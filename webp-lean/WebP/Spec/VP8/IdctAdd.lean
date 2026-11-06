import WebP.Spec.VP8.Tokens
/-!
# Inverse transforms (RFC 6386 §14.3, §14.4; reference source §20.8 `idct_add.c`)

`vp8_dixie_walsh` and `vp8_dixie_idct_add`, with their C integer semantics: intermediate
results computed in `int` and stored in `short` arrays are truncated to 16 bits (`toShort`),
`>>` on negative `int`s is an arithmetic shift (**[interp]** implementation-defined in C;
arithmetic on every compiler the reference decoder is built with), and pixels are clamped
with `CLAMP_255` and stored as `unsigned char`.

Image planes are `ByteArray`s addressed by a pointer (an index) and a stride, exactly like the
reference code's `unsigned char *` arithmetic.
-/
namespace WebP.Spec.VP8

/-- Read the `unsigned char` at index `i` of a plane (as an `int`). -/
@[inline] def px (b : ByteArray) (i : Nat) : Int := (byteAt b i).toNat

/-- Store an `unsigned char` (the value is in `[0, 255]` at every call site). -/
@[inline] def setPx (b : ByteArray) (i : Nat) (v : Int) : ByteArray :=
  if h : i < b.size then b.set i v.toNat.toUInt8 h else b

/-- `CLAMP_255(x)` (dixie.h). -/
@[inline] def clamp255 (x : Int) : Int := if x < 0 then 0 else if x > 255 then 255 else x

/-- `vp8_dixie_walsh(input, output)`: inverse Walsh–Hadamard transform of the Y2 block
(§14.3). `input` is `coeffs[off, off + 16)`; returns `output[16]`. -/
def walsh (coeffs : Array Int) (off : Nat) : Array Int := Id.run do
  let ip (k : Nat) : Int := coeffs.getD (off + k) 0
  let mut op : Array Int := Array.replicate 16 0
  for i in [0:4] do
    let a1 := ip (i + 0) + ip (i + 12)
    let b1 := ip (i + 4) + ip (i + 8)
    let c1 := ip (i + 4) - ip (i + 8)
    let d1 := ip (i + 0) - ip (i + 12)
    op := op.setIfInBounds (i + 0) (toShort (a1 + b1))
    op := op.setIfInBounds (i + 4) (toShort (c1 + d1))
    op := op.setIfInBounds (i + 8) (toShort (a1 - b1))
    op := op.setIfInBounds (i + 12) (toShort (d1 - c1))
  for i in [0:4] do
    let ip (k : Nat) : Int := op.getD (4 * i + k) 0
    let a1 := ip 0 + ip 3
    let b1 := ip 1 + ip 2
    let c1 := ip 1 - ip 2
    let d1 := ip 0 - ip 3
    let a2 := a1 + b1
    let b2 := c1 + d1
    let c2 := a1 - b1
    let d2 := d1 - c1
    op := op.setIfInBounds (4 * i + 0) (toShort ((a2 + 3) >>> 3))
    op := op.setIfInBounds (4 * i + 1) (toShort ((b2 + 3) >>> 3))
    op := op.setIfInBounds (4 * i + 2) (toShort ((c2 + 3) >>> 3))
    op := op.setIfInBounds (4 * i + 3) (toShort ((d2 + 3) >>> 3))
  return op

/-- `cospi8sqrt2minus1` -/
def cospi8sqrt2minus1 : Int := 20091
/-- `sinpi8sqrt2` -/
def sinpi8sqrt2 : Int := 35468

/-- `idct_columns(input, output)`: first (vertical) pass of the inverse DCT (§14.4), on
`coeffs[off, off + 16)`, results stored in `short tmp[16]`. -/
def idctColumns (coeffs : Array Int) (off : Nat) : Array Int := Id.run do
  let mut op : Array Int := Array.replicate 16 0
  for i in [0:4] do
    let ip (k : Nat) : Int := coeffs.getD (off + i + k) 0
    let a1 := ip 0 + ip 8
    let b1 := ip 0 - ip 8
    let temp1 := (ip 4 * sinpi8sqrt2) >>> 16
    let temp2 := ip 12 + ((ip 12 * cospi8sqrt2minus1) >>> 16)
    let c1 := temp1 - temp2
    let temp1 := ip 4 + ((ip 4 * cospi8sqrt2minus1) >>> 16)
    let temp2 := (ip 12 * sinpi8sqrt2) >>> 16
    let d1 := temp1 + temp2
    op := op.setIfInBounds (i + 4 * 0) (toShort (a1 + d1))
    op := op.setIfInBounds (i + 4 * 3) (toShort (a1 - d1))
    op := op.setIfInBounds (i + 4 * 1) (toShort (b1 + c1))
    op := op.setIfInBounds (i + 4 * 2) (toShort (b1 - c1))
  return op

/-- `vp8_dixie_idct_add(recon, predict, stride, coeffs)` with `recon = predict = p`: add the
inverse DCT of `coeffs[off, off + 16)` to the 4×4 prediction at `p` (§14.4, §14.5). -/
def idctAdd (b : ByteArray) (p stride : Nat) (coeffs : Array Int) (off : Nat) : ByteArray :=
  Id.run do
  let tmp := idctColumns coeffs off
  let mut b := b
  for i in [0:4] do
    let c (k : Nat) : Int := tmp.getD (4 * i + k) 0
    let a1 := c 0 + c 2
    let b1 := c 0 - c 2
    let temp1 := (c 1 * sinpi8sqrt2) >>> 16
    let temp2 := c 3 + ((c 3 * cospi8sqrt2minus1) >>> 16)
    let c1 := temp1 - temp2
    let temp1 := c 1 + ((c 1 * cospi8sqrt2minus1) >>> 16)
    let temp2 := (c 3 * sinpi8sqrt2) >>> 16
    let d1 := temp1 + temp2
    let r := p + i * stride
    b := setPx b (r + 0) (clamp255 (px b (r + 0) + ((a1 + d1 + 4) >>> 3)))
    b := setPx b (r + 3) (clamp255 (px b (r + 3) + ((a1 - d1 + 4) >>> 3)))
    b := setPx b (r + 1) (clamp255 (px b (r + 1) + ((b1 + c1 + 4) >>> 3)))
    b := setPx b (r + 2) (clamp255 (px b (r + 2) + ((b1 - c1 + 4) >>> 3)))
  return b

end WebP.Spec.VP8
