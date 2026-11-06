import WebP.VP8Libwebp.BoolDecoder
/-!
# VP8 reconstruction primitives (RFC 6386 §12 intra prediction, §14.3–§14.4 inverse transforms)

Literal ports of libwebp src/dsp/dec.c (C reference versions; the SIMD versions are
bit-exact with these). All functions operate on a scratch "work buffer" with stride
`BPS = 32`, exactly like libwebp's `yuv_b`, so that the border conventions (127 above
the frame, 129 left of the frame, replicated top-right samples) are reproduced exactly.
-/
namespace WebP.VP8Libwebp

def BPS : Nat := 32

/-- Clamp to `[0,255]`. -/
@[inline] def clip255 (v : Int) : Nat := if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- Wrap an integer to `int16_t` (two's complement truncation, as C assignment does). -/
@[inline] def wrap16 (v : Int) : Int :=
  let m := v % 65536            -- Int.emod: result in [0, 65536)
  if m ≥ 32768 then m - 65536 else m

/-- Arithmetic (flooring) right shift of an `Int`. -/
@[inline] def asr (v : Int) (s : Nat) : Int := v >>> s

/-! ## Intra predictors (RFC 6386 §12.2, §12.3) -/

/-- Read `wb[d + dx + dy*BPS]` with signed offsets. -/
@[inline] def px (wb : ByteArray) (d : Nat) (dx dy : Int) : Nat :=
  rd wb ((d : Int) + dx + dy * 32).toNat

@[inline] def setPx (wb : ByteArray) (d : Nat) (dx dy : Int) (v : Nat) : ByteArray :=
  wrN wb ((d : Int) + dx + dy * 32).toNat v

@[inline] def fill (wb : ByteArray) (d : Nat) (w h : Nat) (v : Nat) : ByteArray := Id.run do
  let mut wb := wb
  for y in [0:h] do
    for x in [0:w] do
      wb := wrN wb (d + x + y * 32) v
  return wb

/-- TrueMotion predictor of size `n` (TM4/TM8uv/TM16). -/
def trueMotion (wb : ByteArray) (d : Nat) (n : Nat) : ByteArray := Id.run do
  let mut wb := wb
  let tl : Int := px wb d (-1) (-1)
  for y in [0:n] do
    let l : Int := px wb d (-1) y
    for x in [0:n] do
      let t : Int := px wb d x (-1)
      wb := wrN wb (d + x + y * 32) (clip255 (t + l - tl))
  return wb

def ve (wb : ByteArray) (d n : Nat) : ByteArray := Id.run do
  let mut wb := wb
  for y in [0:n] do
    for x in [0:n] do
      wb := wrN wb (d + x + y * 32) (px wb d x (-1))
  return wb

def he (wb : ByteArray) (d n : Nat) : ByteArray := Id.run do
  let mut wb := wb
  for y in [0:n] do
    let l := px wb d (-1) y
    for x in [0:n] do
      wb := wrN wb (d + x + y * 32) l
  return wb

/-- DC prediction for 16x16 / 8x8 blocks with variants for missing edges. -/
def dcPred (wb : ByteArray) (d n : Nat) (useTop useLeft : Bool) : ByteArray := Id.run do
  let shift := if n == 16 then 4 else 3   -- log2 n
  let mut s := 0
  if useTop then
    for i in [0:n] do s := s + px wb d i (-1)
  if useLeft then
    for i in [0:n] do s := s + px wb d (-1) i
  let v :=
    if useTop && useLeft then (s + n) >>> (shift + 1)
    else if useTop || useLeft then (s + (n >>> 1)) >>> shift
    else 0x80
  return fill wb d n n v

/-- Luma 16x16 / chroma 8x8 predictors indexed as libwebp's `VP8PredLuma16` / `VP8PredChroma8`:
0 DC, 1 TM, 2 VE, 3 HE, 4 DC-no-top, 5 DC-no-left, 6 DC-no-top-left. -/
def predBlock (wb : ByteArray) (d n : Nat) (mode : Nat) : ByteArray :=
  match mode with
  | 0 => dcPred wb d n true true
  | 1 => trueMotion wb d n
  | 2 => ve wb d n
  | 3 => he wb d n
  | 4 => dcPred wb d n false true
  | 5 => dcPred wb d n true false
  | _ => dcPred wb d n false false

@[inline] def avg3 (a b c : Nat) : Nat := (a + 2 * b + c + 2) >>> 2
@[inline] def avg2 (a b : Nat) : Nat := (a + b + 1) >>> 1

/-- 4x4 luma sub-block predictors (`VP8PredLuma4`), RFC 6386 §12.3.
Modes: 0 DC, 1 TM, 2 VE, 3 HE, 4 RD, 5 VR, 6 LD, 7 VL, 8 HD, 9 HU. -/
def pred4 (wb : ByteArray) (d : Nat) (mode : Nat) : ByteArray :=
  let I := px wb d (-1) 0; let J := px wb d (-1) 1; let K := px wb d (-1) 2; let L := px wb d (-1) 3
  let X := px wb d (-1) (-1)
  let A := px wb d 0 (-1); let B := px wb d 1 (-1); let C := px wb d 2 (-1); let D := px wb d 3 (-1)
  let E := px wb d 4 (-1); let F := px wb d 5 (-1); let G := px wb d 6 (-1); let H := px wb d 7 (-1)
  -- set a 4x4 block from a function of (x, y)
  let put (f : Nat → Nat → Nat) : ByteArray := Id.run do
    let mut wb := wb
    for y in [0:4] do
      for x in [0:4] do
        wb := wrN wb (d + x + y * 32) (f x y)
    return wb
  match mode with
  | 0 =>
    let dc := (A + B + C + D + I + J + K + L + 4) >>> 3
    put fun _ _ => dc
  | 1 => trueMotion wb d 4
  | 2 =>
    let v0 := avg3 X A B; let v1 := avg3 A B C; let v2 := avg3 B C D; let v3 := avg3 C D E
    put fun x _ => match x with | 0 => v0 | 1 => v1 | 2 => v2 | _ => v3
  | 3 =>
    let r0 := avg3 X I J; let r1 := avg3 I J K; let r2 := avg3 J K L; let r3 := avg3 K L L
    put fun _ y => match y with | 0 => r0 | 1 => r1 | 2 => r2 | _ => r3
  | 4 => -- RD: depends on x - y
    put fun x y =>
      match (3 + x) - y with  -- (x - y) + 3 in [0, 6]
      | 0 => avg3 J K L
      | 1 => avg3 I J K
      | 2 => avg3 X I J
      | 3 => avg3 A X I
      | 4 => avg3 B A X
      | 5 => avg3 C B A
      | _ => avg3 D C B
  | 5 => -- VR
    put fun x y =>
      match x, y with
      | 0, 0 => avg2 X A | 1, 2 => avg2 X A
      | 1, 0 => avg2 A B | 2, 2 => avg2 A B
      | 2, 0 => avg2 B C | 3, 2 => avg2 B C
      | 3, 0 => avg2 C D
      | 0, 3 => avg3 K J I
      | 0, 2 => avg3 J I X
      | 0, 1 => avg3 I X A | 1, 3 => avg3 I X A
      | 1, 1 => avg3 X A B | 2, 3 => avg3 X A B
      | 2, 1 => avg3 A B C | 3, 3 => avg3 A B C
      | _, _ => avg3 B C D   -- (3,1)
  | 6 => -- LD: depends on x + y
    put fun x y =>
      match x + y with
      | 0 => avg3 A B C
      | 1 => avg3 B C D
      | 2 => avg3 C D E
      | 3 => avg3 D E F
      | 4 => avg3 E F G
      | 5 => avg3 F G H
      | _ => avg3 G H H
  | 7 => -- VL
    put fun x y =>
      match x, y with
      | 0, 0 => avg2 A B
      | 1, 0 => avg2 B C | 0, 2 => avg2 B C
      | 2, 0 => avg2 C D | 1, 2 => avg2 C D
      | 3, 0 => avg2 D E | 2, 2 => avg2 D E
      | 0, 1 => avg3 A B C
      | 1, 1 => avg3 B C D | 0, 3 => avg3 B C D
      | 2, 1 => avg3 C D E | 1, 3 => avg3 C D E
      | 3, 1 => avg3 D E F | 2, 3 => avg3 D E F
      | 3, 2 => avg3 E F G
      | _, _ => avg3 F G H   -- (3,3)
  | 8 => -- HD
    put fun x y =>
      match x, y with
      | 0, 0 => avg2 I X | 2, 1 => avg2 I X
      | 0, 1 => avg2 J I | 2, 2 => avg2 J I
      | 0, 2 => avg2 K J | 2, 3 => avg2 K J
      | 0, 3 => avg2 L K
      | 3, 0 => avg3 A B C
      | 2, 0 => avg3 X A B
      | 1, 0 => avg3 I X A | 3, 1 => avg3 I X A
      | 1, 1 => avg3 J I X | 3, 2 => avg3 J I X
      | 1, 2 => avg3 K J I | 3, 3 => avg3 K J I
      | _, _ => avg3 L K J   -- (1,3)
  | _ => -- 9: HU
    put fun x y =>
      match x, y with
      | 0, 0 => avg2 I J
      | 2, 0 => avg2 J K | 0, 1 => avg2 J K
      | 2, 1 => avg2 K L | 0, 2 => avg2 K L
      | 1, 0 => avg3 I J K
      | 3, 0 => avg3 J K L | 1, 1 => avg3 J K L
      | 3, 1 => avg3 K L L | 1, 2 => avg3 K L L
      | _, _ => L

/-! ## Inverse transforms (RFC 6386 §14.3, §14.4; libwebp `TransformOne_C` etc.) -/

@[inline] def mul1 (a : Int) : Int := asr (a * 20091) 16 + a
@[inline] def mul2 (a : Int) : Int := asr (a * 35468) 16

/-- `STORE(x, y, v)`: `dst = clip(dst + (v >> 3))`. -/
@[inline] def store (wb : ByteArray) (d x y : Nat) (v : Int) : ByteArray :=
  let i := d + x + y * 32
  wrN wb i (clip255 ((rd wb i : Int) + asr v 3))

/-- `_mm_mulhi_epi16`: high 16 bits of the signed 32-bit product. -/
@[inline] def mulhi16 (x k : Int) : Int := asr (x * k) 16

/-- Full 4x4 inverse DCT of `c[base..base+16)` added to the prediction at `d`, with the
exact arithmetic of libwebp's x86 `Transform_SSE2` (used by default on x86-64): every
intermediate sum is wrapped to `int16` and the constants are applied via
`x + mulhi(x, k - 65536)`. On well-formed streams (coefficients within the ranges noted in
libwebp's C code) this equals `transformOneC`; on corrupted streams with huge coefficients
the two differ, and libwebp's actual output is the SSE2 one. -/
def transformOne (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray := Id.run do
  let w := wrap16
  let k1 : Int := 20091
  let k2 : Int := -30068
  let inp (k : Nat) : Int := c.getD (base + k) 0
  let mut tmp : Array Int := Array.replicate 16 0
  for i in [0:4] do
    let x0 := inp i; let x1 := inp (4 + i); let x2 := inp (8 + i); let x3 := inp (12 + i)
    let a := w (x0 + x2)
    let b := w (x0 - x2)
    let cc := w (w (x1 - x3) + w (mulhi16 x1 k2 - mulhi16 x3 k1))
    let dd := w (w (x1 + x3) + w (mulhi16 x1 k1 + mulhi16 x3 k2))
    tmp := tmp.setIfInBounds (4*i) (w (a + dd))
    tmp := tmp.setIfInBounds (4*i + 1) (w (b + cc))
    tmp := tmp.setIfInBounds (4*i + 2) (w (b - cc))
    tmp := tmp.setIfInBounds (4*i + 3) (w (a - dd))
  let mut wb := wb
  for i in [0:4] do
    let t (k : Nat) : Int := tmp.getD (i + k) 0
    let dc := w (t 0 + 4)
    let a := w (dc + t 8)
    let b := w (dc - t 8)
    let cc := w (w (t 4 - t 12) + w (mulhi16 (t 4) k2 - mulhi16 (t 12) k1))
    let dd := w (w (t 4 + t 12) + w (mulhi16 (t 4) k1 + mulhi16 (t 12) k2))
    wb := store wb d 0 i (w (a + dd))
    wb := store wb d 1 i (w (b + cc))
    wb := store wb d 2 i (w (b - cc))
    wb := store wb d 3 i (w (a - dd))
  return wb

/-- libwebp's portable C `TransformOne_C` (32-bit intermediates). Kept for reference;
equal to `transformOne` on well-formed streams. -/
def transformOneC (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray := Id.run do
  let inp (k : Nat) : Int := c.getD (base + k) 0
  let mut tmp : Array Int := Array.replicate 16 0
  for i in [0:4] do
    let a := inp i + inp (8 + i)
    let b := inp i - inp (8 + i)
    let cc := mul2 (inp (4 + i)) - mul1 (inp (12 + i))
    let dd := mul1 (inp (4 + i)) + mul2 (inp (12 + i))
    tmp := tmp.setIfInBounds (4*i) (a + dd)
    tmp := tmp.setIfInBounds (4*i + 1) (b + cc)
    tmp := tmp.setIfInBounds (4*i + 2) (b - cc)
    tmp := tmp.setIfInBounds (4*i + 3) (a - dd)
  let mut wb := wb
  for i in [0:4] do
    let t (k : Nat) : Int := tmp.getD (i + k) 0
    let dc := t 0 + 4
    let a := dc + t 8
    let b := dc - t 8
    let cc := mul2 (t 4) - mul1 (t 12)
    let dd := mul1 (t 4) + mul2 (t 12)
    wb := store wb d 0 i (a + dd)
    wb := store wb d 1 i (b + cc)
    wb := store wb d 2 i (b - cc)
    wb := store wb d 3 i (a - dd)
  return wb

/-- `TransformAC3_C`: only coefficients 0, 1, 4 non-zero. -/
def transformAC3 (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray := Id.run do
  let inp (k : Nat) : Int := c.getD (base + k) 0
  let a := inp 0 + 4
  let c4 := mul2 (inp 4); let d4 := mul1 (inp 4)
  let c1 := mul2 (inp 1); let d1 := mul1 (inp 1)
  let mut wb := wb
  let rows : Array Int := #[a + d4, a + c4, a - c4, a - d4]
  for y in [0:4] do
    let dc := rows.getD y 0
    wb := store wb d 0 y (dc + d1)
    wb := store wb d 1 y (dc + c1)
    wb := store wb d 2 y (dc - c1)
    wb := store wb d 3 y (dc - d1)
  return wb

/-- `TransformDC_C`: DC-only block. -/
def transformDC (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray := Id.run do
  let dc := c.getD base 0 + 4
  let mut wb := wb
  for j in [0:4] do
    for i in [0:4] do
      wb := store wb d i j dc
  return wb

/-- `DoTransform`: choose transform from the 2-bit non-zero code. -/
@[inline] def doTransform (code : Nat) (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray :=
  match code with
  | 3 => transformOne wb c base d
  | 2 => transformAC3 wb c base d
  | 1 => transformDC wb c base d
  | _ => wb

/-- `DoUVTransform` for one 8x8 chroma block (4 sub-blocks at `base`). -/
def doUVTransform (bits : Nat) (wb : ByteArray) (c : Array Int) (base d : Nat) : ByteArray :=
  if bits &&& 0xff != 0 then
    if bits &&& 0xaa != 0 then
      let wb := transformOne wb c base d
      let wb := transformOne wb c (base + 16) (d + 4)
      let wb := transformOne wb c (base + 32) (d + 4 * 32)
      transformOne wb c (base + 48) (d + 4 * 32 + 4)
    else
      let wb := if c.getD base 0 != 0 then transformDC wb c base d else wb
      let wb := if c.getD (base + 16) 0 != 0 then transformDC wb c (base + 16) (d + 4) else wb
      let wb := if c.getD (base + 32) 0 != 0 then transformDC wb c (base + 32) (d + 4 * 32) else wb
      if c.getD (base + 48) 0 != 0 then transformDC wb c (base + 48) (d + 4 * 32 + 4) else wb
  else wb

/-- Inverse Walsh-Hadamard transform (RFC 6386 §14.3, `TransformWHT_C`): `dc[0..16)` →
coefficient 0 of each of the 16 luma blocks in `out` (block `k` at `out[16k]`),
with `int16_t` truncation of the results. -/
def transformWHT (dc : Array Int) (out : Array Int) : Array Int := Id.run do
  let inp (k : Nat) : Int := dc.getD k 0
  let mut tmp : Array Int := Array.replicate 16 0
  for i in [0:4] do
    let a0 := inp i + inp (12 + i)
    let a1 := inp (4 + i) + inp (8 + i)
    let a2 := inp (4 + i) - inp (8 + i)
    let a3 := inp i - inp (12 + i)
    tmp := tmp.setIfInBounds i (a0 + a1)
    tmp := tmp.setIfInBounds (8 + i) (a0 - a1)
    tmp := tmp.setIfInBounds (4 + i) (a3 + a2)
    tmp := tmp.setIfInBounds (12 + i) (a3 - a2)
  let mut out := out
  for i in [0:4] do
    let t (k : Nat) : Int := tmp.getD (k + i * 4) 0
    let dc := t 0 + 3
    let a0 := dc + t 3
    let a1 := t 1 + t 2
    let a2 := t 1 - t 2
    let a3 := dc - t 3
    let o := 64 * i
    out := out.setIfInBounds o (wrap16 (asr (a0 + a1) 3))
    out := out.setIfInBounds (o + 16) (wrap16 (asr (a3 + a2) 3))
    out := out.setIfInBounds (o + 32) (wrap16 (asr (a0 - a1) 3))
    out := out.setIfInBounds (o + 48) (wrap16 (asr (a3 - a2) 3))
  return out

end WebP.VP8Libwebp
