import WebP.Basic
import WebP.Spec.Container
import WebP.Spec.Lossless
import WebP.Spec.Alpha
import WebP.Spec.Anim
import WebP.Spec.VP8
/-!
# Semantics of a WebP file (RFC 9649)

`Spec.Decodes vp8 d out`: the file `d` is well formed (`Spec.Demux`) and its frames, decoded
and assembled as in RFC 9649, are `out`.

The semantics is stated parametrically in a function `vp8` decoding a 'VP8 ' payload to an
RGBA image, and instantiated with the concrete lossy semantics `Spec.lossy`: the RFC 6386
reference decoder (`Spec.VP8.decode`, a transcription of RFC 6386 §20) followed by the
application-chosen Y'CbCr → RGB conversion that RFC 9649 §2.5 leaves open (`Frame.toRGBA`,
libwebp's default fancy upsampling). Everything else (container, lossless bitstream, alpha,
animation) is specified here.

The shape of the definitions: `decodeLayout` is written once over a record of `Components`;
the specification instantiates it with the reference components, the decoder with the
optimized ones, and `WebP.Proofs.Decode` shows the two records are equal.
-/
namespace WebP.Spec

open WebP

/-- **The lossy semantics** of a 'VP8 ' chunk payload: RFC 6386 key-frame decoding
(`Spec.VP8.decode`), then **[interp]** the application-chosen Y'CbCr 4:2:0 → RGB conversion of
RFC 9649 §2.5 ("SHOULD use Rec. 601"; the exact method is left to the application): libwebp's
default fancy upsampling and fixed-point Rec. 601 conversion (`WebP.VP8.Frame.toRGBA`),
alpha = 255. -/
def lossy (d : ByteArray) : Except String RGBAImage :=
  (Spec.VP8.decode d).map fun f => ⟨f.width, f.height, f.toRGBA⟩

/-- Components a WebP decoder is built from. -/
structure Components where
  /-- 'VP8 ' payload to RGBA (alpha 255). -/
  vp8 : ByteArray → Except String RGBAImage
  /-- 'VP8L' payload (§3). -/
  vp8l : ByteArray → Except String VP8L.Image
  /-- Headerless lossless stream of given dimensions (§2.7.1.2). -/
  vp8lStream : ByteArray → Nat → Nat → Except String (Array UInt32)
  /-- Alpha unfiltering (§2.7.1.2): method, width, height, filtered plane. -/
  unfilter : Nat → Nat → Nat → ByteArray → ByteArray

/-- The reference components, given a VP8 decoder. -/
def specComponents (vp8 : ByteArray → Except String RGBAImage) : Components :=
  ⟨vp8, VP8L.decode, VP8L.decodeStream, Alpha.unfilter⟩

/-- Result of decoding: canvas size, flags, and the canvas after each frame. -/
structure Output where
  width : Nat
  height : Nat
  animated : Bool
  hasAlpha : Bool
  lossy : Bool
  loopCount : Nat
  background : Nat
  /-- `(duration in ms, RGBA canvas)` per frame; a still image is one frame of duration 0. -/
  frames : List (Nat × ByteArray)

/-- §3.2 ARGB pixels to RGBA bytes. -/
def argbToRGBA (px : Array UInt32) : ByteArray :=
  ⟨Array.ofFn (n := px.size * 4) fun k =>
    let p := px.getD (k.val / 4) 0
    match k.val % 4 with
    | 0 => (p >>> 16).toUInt8
    | 1 => (p >>> 8).toUInt8
    | 2 => p.toUInt8
    | _ => (p >>> 24).toUInt8⟩

/-- Replace the alpha channel of an RGBA buffer by an alpha plane. -/
def setAlpha (rgba alpha : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := rgba.size) fun k =>
    if k.val % 4 = 3 then (byte alpha (k.val / 4)).toUInt8 else rgba[k]⟩

def payload (d : ByteArray) (c : Chunk) : ByteArray := d.extract c.off (c.off + c.size)

/-- Decode the image data of one frame (§2.7.1.2, §2.7.1.3): a 'VP8L' bitstream carries its
own alpha (an 'ALPH' chunk next to it is ignored: "A frame containing a 'VP8L' Chunk SHOULD
NOT contain this chunk"); a 'VP8 ' bitstream takes its alpha from 'ALPH' if present. -/
def decodeImage (C : Components) (d : ByteArray) (alph : Option Chunk) (bits : Chunk) :
    Except String RGBAImage := do
  if bits.tag = VP8L then
    let img ← C.vp8l (payload d bits)
    return ⟨img.width, img.height, argbToRGBA img.pixels⟩
  else
    let img ← C.vp8 (payload d bits)
    match alph with
    | none => return img
    | some a =>
      let plane ← Alpha.decodeWith C.unfilter C.vp8lStream (payload d a) img.width img.height
      return ⟨img.width, img.height, setAlpha img.data plane⟩

/-- Decode all frames of an animation, checking that each bitstream has the frame's size. -/
def decodeFrames (C : Components) (d : ByteArray) :
    List FrameInfo → Except String (List (FrameInfo × ByteArray))
  | [] => .ok []
  | f :: fs => do
    let img ← decodeImage C d f.alph f.bits
    if img.width ≠ f.width ∨ img.height ≠ f.height then
      throw "frame bitstream size differs from ANMF size"
    let rest ← decodeFrames C d fs
    return (f, img.data) :: rest

def isLossyFrame (f : FrameInfo) : Bool := f.bits.tag == VP8

/-- Decode a demuxed file. -/
def decodeLayout (C : Components) (d : ByteArray) : Layout → Except String Output
  | .still vp8x alph bits => do
    let img ← decodeImage C d alph bits
    let hasAlpha ← match vp8x with
      | none =>
        -- §2.6 / §3.4 `alpha_is_used` hint for simple lossless files.
        if bits.tag = VP8L then do
          let (_, _, a) ← VP8L.readHeaderOnly (payload d bits); pure a
        else pure false
      | some x =>
        -- §2.5 / §2.7: the bitstream size "is assumed to be the width and height of the canvas".
        if img.width ≠ x.canvasWidth ∨ img.height ≠ x.canvasHeight then
          throw "bitstream size differs from canvas size"
        else pure x.alpha
    return ⟨img.width, img.height, false, hasAlpha, bits.tag == VP8, 0, 0,
      [(0, img.data)]⟩
  | .animated x bg loops frames => do
    let decoded ← decodeFrames C d frames
    let canvases := Anim.compose x.canvasWidth x.canvasHeight decoded
    return ⟨x.canvasWidth, x.canvasHeight, true, x.alpha, frames.any isLossyFrame, loops, bg,
      (frames.map (·.duration)).zip canvases⟩

/-- **The semantics of WebP files.** -/
def Decodes (vp8 : ByteArray → Except String RGBAImage) (d : ByteArray) (out : Output) : Prop :=
  ∃ L, Demux d L ∧ decodeLayout (specComponents vp8) d L = .ok out

end WebP.Spec
