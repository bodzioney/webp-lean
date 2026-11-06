import WebP.Spec.Bits
/-!
# The 'ALPH' chunk (RFC 9649 §2.7.1.2)

Header byte `|Rsv(2)|P(2)|F(2)|C(2)|` (MSB first): reserved bits and the preprocessing hint are
ignored ("Readers MUST ignore this field", "Decoders are not required to use this
information"); compression `C` is 0 (raw) or 1 (lossless); filtering `F` selects the predictor.

The reconstructed alpha plane is defined *declaratively* here, pixel by pixel, by the equations
of §2.7.1.2 (`alpha = (predictor + X) % 256`, with predictors over already reconstructed
neighbors). `WebP.Alpha.unfilter` computes it in place in one pass; `WebP.Proofs.Alpha` proves
they agree.
-/
namespace WebP.Spec.Alpha

/-- §2.7.1.2 `clip(v)`. -/
def clip (v : Int) : Nat := if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- §2.7.1.2 Figure 11 predictor for pixel `i = y * w + x` of filtering method `m`, where
`get j` is the reconstructed alpha of pixel `j` (only pixels before `i` are consulted).
`A` = left, `B` = above, `C` = above-left. -/
def predictor (m w : Nat) (get : Nat → Nat) (i : Nat) : Nat :=
  let x := i % w
  let y := i / w
  if x = 0 ∧ y = 0 then 0                 -- "the top-left value at location (0, 0) uses 0"
  else if m = 0 then 0                     -- Method 0: predictor = 0
  else if m = 1 then                       -- Method 1: predictor = A
    if x = 0 then get (i - w) else get (i - 1)   -- left-most column: pixel above
  else if m = 2 then                       -- Method 2: predictor = B
    if y = 0 then get (i - 1) else get (i - w)   -- top row: pixel on the left
  else                                     -- Method 3: predictor = clip(A + B - C)
    if x = 0 then get (i - w)
    else if y = 0 then get (i - 1)
    else clip ((get (i - 1) : Int) + get (i - w) - get (i - w - 1))

/-- The reconstructed alpha value of pixel `i`: `alpha = (predictor + X) % 256`. -/
def value (m w : Nat) (raw : ByteArray) (i : Nat) : Nat :=
  (predictor m w (fun j => if j < i then value m w raw j else 0) i + byte raw i) % 256
termination_by i

/-- The reconstructed `w × h` alpha plane. -/
def unfilter (m w h : Nat) (raw : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := w * h) fun i => (value m w raw i.val).toUInt8⟩

/-- Decoding of an 'ALPH' payload for a `w × h` frame, given a decoder for headerless lossless
image streams (§2.7.1.2 "Lossless format compression": "image-stream ... of implicit
dimensions width x height", alpha taken "from the green channel"). Raw data "consists of a byte
sequence of length = width * height". -/
def decodeWith (unfilt : Nat → Nat → Nat → ByteArray → ByteArray)
    (lossless : ByteArray → Nat → Nat → Except String (Array UInt32))
    (payload : ByteArray) (w h : Nat) : Except String ByteArray := do
  if payload.size < 1 then throw "empty ALPH chunk"
  let hdr := byte payload 0
  let compression := hdr % 4
  let filtering := hdr / 4 % 4
  let data := payload.extract 1 payload.size
  let raw ←
    if compression = 0 then
      if data.size = w * h then pure data else throw "raw alpha size mismatch"
    else if compression = 1 then do
      let px ← lossless data w h
      pure ⟨px.map fun (p : UInt32) => (p >>> 8).toUInt8⟩
    else throw "invalid alpha compression method"
  return unfilt filtering w h raw

end WebP.Spec.Alpha
