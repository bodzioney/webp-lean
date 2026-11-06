import WebP.Spec.Container
/-!
# Canvas assembly from frames (RFC 9649 §2.7.1.1, §2.7.2)

Canvases are RGBA byte arrays (4 bytes per pixel, row-major). Every operation is defined
pointwise over the canvas, mirroring the RFC's description.

Choices left to the application by the RFC:
* the background color ("ANIM.background_color or application-defined color"): we use
  transparent black `(0,0,0,0)` for the initial canvas and for disposal, as libwebp's
  `WebPAnimDecoder` does; the ANIM value is reported but not used;
* blending is done in the stored (sRGB) space, not in linear space (the RFC's SHOULD is not
  followed by any known implementation);
* the result of the blending formula is rounded to the nearest integer (halves up).
-/
namespace WebP.Spec.Anim

/-- `round(n / d)`, halves rounded up. -/
def roundDiv (n d : Nat) : Nat := (2 * n + d) / (2 * d)

/-- §2.7.1.1: `blend.A = src.A + dst.A * (1 - src.A / 255)`. -/
def blendAlpha (sA dA : Nat) : Nat := roundDiv (255 * sA + dA * (255 - sA)) 255

/-- §2.7.1.1: `blend.RGB = (src.RGB * src.A + dst.RGB * dst.A * (1 - src.A / 255)) / blend.A`,
and `0` if `blend.A = 0`. Multiplying numerator and denominator by 255 makes both integers. -/
def blendColor (sC sA dC dA : Nat) : Nat :=
  let den := 255 * sA + dA * (255 - sA)
  if den = 0 then 0 else roundDiv (255 * sC * sA + dC * dA * (255 - sA)) den

/-- Whether canvas pixel `(x, y)` lies in the frame rectangle. -/
def inRect (f : FrameInfo) (x y : Nat) : Bool :=
  f.x ≤ x && x < f.x + f.width && f.y ≤ y && y < f.y + f.height

/-- Render frame `f` with decoded RGBA pixels `img` onto `canvas` (width `W`) using its
blending method (§2.7.1.1 "Blending method"). -/
def renderFrame (W : Nat) (canvas : ByteArray) (f : FrameInfo) (img : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := canvas.size) fun k =>
    let p := k.val / 4
    let c := k.val % 4
    let x := p % W
    let y := p / W
    if inRect f x y then
      let q := (y - f.y) * f.width + (x - f.x)
      let s := fun ch => byte img (4 * q + ch)
      let t := fun ch => byte canvas (4 * p + ch)
      if f.blend then
        (if c = 3 then blendAlpha (s 3) (t 3) else blendColor (s c) (s 3) (t c) (t 3)).toUInt8
      else (s c).toUInt8
    else canvas[k]⟩

/-- §2.7.1.1 "Dispose to the background color": fill the frame rectangle with the background
color (transparent black, see above). -/
def disposeFrame (W : Nat) (canvas : ByteArray) (f : FrameInfo) : ByteArray :=
  ⟨Array.ofFn (n := canvas.size) fun k =>
    let p := k.val / 4
    if inRect f (p % W) (p / W) then 0 else canvas[k]⟩

/-- §2.7.2: the canvas shown after each frame, for one loop iteration. "Before rendering each
frame, the previous frame's Disposal method is applied." -/
def compose (W H : Nat) (frames : List (FrameInfo × ByteArray)) : List ByteArray :=
  go ⟨Array.replicate (W * H * 4) 0⟩ none frames
where
  go (canvas : ByteArray) (prev : Option FrameInfo) :
      List (FrameInfo × ByteArray) → List ByteArray
    | [] => []
    | (f, img) :: rest =>
      let disposed := match prev with
        | some p => if p.dispose then disposeFrame W canvas p else canvas
        | none => canvas
      let shown := renderFrame W disposed f img
      shown :: go shown (some f) rest

end WebP.Spec.Anim
