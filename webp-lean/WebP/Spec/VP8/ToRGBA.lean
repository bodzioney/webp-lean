import WebP.Spec.VP8.Frame
/-!
# Y'CbCr 4:2:0 → RGBA conversion (the application-chosen conversion of RFC 9649 §2.5)

RFC 6386 defines the decoded frame as Y'CbCr 4:2:0 planes; RFC 9649 §2.5 says the conversion
to RGB SHOULD follow Rec. 601 but leaves the exact method (chroma upsampling, rounding) to the
application. **[interp]** Our chosen conversion is libwebp's default (`WebPDecodeRGBA`): "fancy" upsampling
(src/dsp/upsampling.c `UPSAMPLE_FUNC`, driven by src/dec/io_dec.c `EmitFancyRGB`) and the
14-bit fixed-point conversion of src/dsp/yuv.h (`VP8YUVToR/G/B`).
The packed two-channel arithmetic of libwebp is equivalent to the per-channel formulas
below (no carries cross the 16-bit lanes, and the masked/shifted lanes are exact).
-/
namespace WebP.VP8

/-- Bounds-checked plane read (`0` out of range). -/
@[inline] def rdPlane (a : ByteArray) (i : Nat) : Nat := if h : i < a.size then a[i].toNat else 0

/-- Bounds-checked byte write of a `Nat` truncated to 8 bits (no-op out of range). -/
@[inline] def wrPlane (a : ByteArray) (i : Nat) (v : Nat) : ByteArray :=
  if h : i < a.size then a.set i v.toUInt8 h else a

@[inline] def mulHi (v c : Nat) : Nat := (v * c) >>> 8

/-- `VP8Clip8` applied to `pos - neg` (YUV_FIX2 = 6). -/
@[inline] def clip8 (pos neg : Nat) : Nat :=
  if pos < neg then 0 else
  let t := pos - neg
  if t < 16384 then t >>> 6 else 255

@[inline] def yuvToR (y v : Nat) : Nat := clip8 (mulHi y 19077 + mulHi v 26149) 14234
@[inline] def yuvToG (y u v : Nat) : Nat := clip8 (mulHi y 19077 + 8708) (mulHi u 6419 + mulHi v 13320)
@[inline] def yuvToB (y u : Nat) : Nat := clip8 (mulHi y 19077 + mulHi u 33050) 17685

@[inline] def putRGBA (out : ByteArray) (i : Nat) (y u v : Nat) : ByteArray :=
  let o := 4 * i
  let out := wrPlane out o (yuvToR y v)
  let out := wrPlane out (o + 1) (yuvToG y u v)
  let out := wrPlane out (o + 2) (yuvToB y u)
  wrPlane out (o + 3) 255

/-- One call of libwebp's `UpsampleRgbaLinePair_C`.
`topY`/`botY`: luma row indices (`botY = none` for a single line), `tu`/`cu`: chroma row
indices of the "top" and "current" chroma rows. -/
def upsampleLinePair (f : Frame) (out : ByteArray) (topY : Nat) (botY : Option Nat)
    (tu cu : Nat) : ByteArray := Id.run do
  let len := f.width
  let uvW := (f.width + 1) / 2
  let U (r x : Nat) : Nat := rdPlane f.u (r * uvW + x)
  let V (r x : Nat) : Nat := rdPlane f.v (r * uvW + x)
  let Y (r x : Nat) : Nat := rdPlane f.y (r * len + x)
  let mut out := out
  let lastPair := (len - 1) >>> 1
  let mut tlU := U tu 0; let mut tlV := V tu 0
  let mut lU := U cu 0; let mut lV := V cu 0
  out := putRGBA out (topY * len) (Y topY 0) ((3 * tlU + lU + 2) >>> 2) ((3 * tlV + lV + 2) >>> 2)
  if let some by' := botY then
    out := putRGBA out (by' * len) (Y by' 0) ((3 * lU + tlU + 2) >>> 2) ((3 * lV + tlV + 2) >>> 2)
  for x in [1:lastPair + 1] do
    let tU := U tu x; let tV := V tu x
    let cU := U cu x; let cV := V cu x
    let avgU := tlU + tU + lU + cU + 8
    let avgV := tlV + tV + lV + cV + 8
    let d12U := (avgU + 2 * (tU + lU)) >>> 3
    let d12V := (avgV + 2 * (tV + lV)) >>> 3
    let d03U := (avgU + 2 * (tlU + cU)) >>> 3
    let d03V := (avgV + 2 * (tlV + cV)) >>> 3
    out := putRGBA out (topY * len + 2 * x - 1) (Y topY (2 * x - 1)) ((d12U + tlU) >>> 1) ((d12V + tlV) >>> 1)
    out := putRGBA out (topY * len + 2 * x) (Y topY (2 * x)) ((d03U + tU) >>> 1) ((d03V + tV) >>> 1)
    if let some by' := botY then
      out := putRGBA out (by' * len + 2 * x - 1) (Y by' (2 * x - 1)) ((d03U + lU) >>> 1) ((d03V + lV) >>> 1)
      out := putRGBA out (by' * len + 2 * x) (Y by' (2 * x)) ((d12U + cU) >>> 1) ((d12V + cV) >>> 1)
    tlU := tU; tlV := tV; lU := cU; lV := cV
  if len % 2 == 0 then
    out := putRGBA out (topY * len + len - 1) (Y topY (len - 1)) ((3 * tlU + lU + 2) >>> 2) ((3 * tlV + lV + 2) >>> 2)
    if let some by' := botY then
      out := putRGBA out (by' * len + len - 1) (Y by' (len - 1)) ((3 * lU + tlU + 2) >>> 2) ((3 * lV + tlV + 2) >>> 2)
  return out

/-- YUV420 → RGBA (alpha = 255), bit-exact with libwebp's default fancy upsampling.
Global row schedule of `EmitFancyRGB`: row 0 alone (chroma row 0 twice); then pairs
`(2k-1, 2k)` using chroma rows `(k-1, k)`; for even heights the last row alone with the
last chroma row twice. -/
def Frame.toRGBA (f : Frame) : ByteArray := Id.run do
  let mut out := ByteArray.mk (Array.replicate (4 * f.width * f.height) 0)
  if f.width == 0 || f.height == 0 then return out
  out := upsampleLinePair f out 0 none 0 0
  -- pairs (2k-1, 2k) for all k ≥ 1 with 2k < height
  for k in [1:(f.height + 1) / 2] do
    out := upsampleLinePair f out (2 * k - 1) (some (2 * k)) (k - 1) k
  if f.height % 2 == 0 then
    let last := f.height / 2 - 1
    out := upsampleLinePair f out (f.height - 1) none last last
  return out

end WebP.VP8
