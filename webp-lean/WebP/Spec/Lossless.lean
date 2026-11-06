import WebP.Spec.Prefix
/-!
# The WebP lossless bitstream (RFC 9649 §3), as an executable specification

This file is a direct transcription of RFC 9649 §3 ("Specification for WebP Lossless
Bitstream"). It is written against an abstract pair of primitives `Prims`:

* `readBits` — the RFC's `ReadBits(n)`;
* `build`    — turning a list of code lengths into a prefix code (§3.7.2.1).

`Spec.VP8L.specPrims` instantiates them with the reference definitions of
`WebP.Spec.Bits` / `WebP.Spec.Prefix`, giving the specification `Spec.VP8L.decode`.
The production decoder (`WebP.VP8L.decode`) instantiates them with optimized primitives
(word-at-a-time bit extraction, table-driven prefix decoding); `WebP.Proofs.Lossless`
proves the two instantiations equal, hence the decoder equals the specification.

Points where the RFC is not explicit and we follow libwebp (the reference implementation
the RFC text is derived from) are marked **[interp]**.
-/
namespace WebP.Spec.VP8L

open WebP.Spec

/-- The two primitive operations the lossless format is defined in terms of. -/
structure Prims where
  /-- `ReadBits(n)` at a bit position: value and new position. -/
  readBits : ByteArray → Nat → Nat → Except String (Nat × Nat)
  /-- Build a prefix code from code lengths (§3.7.2.1). -/
  build : ByteArray → Array Nat → Except String Code

/-- The reference primitives. -/
def specPrims : Prims := ⟨Spec.readBits, Prefix.build⟩

/-- Decoding monad: the state is the current bit position. -/
abbrev M := StateT Nat (Except String)

/-! ## Pixels (§3.2: alpha in bits 31..24, red 23..16, green 15..8, blue 7..0) -/

@[inline] def chA (p : UInt32) : UInt32 := (p >>> 24) &&& 0xff
@[inline] def chR (p : UInt32) : UInt32 := (p >>> 16) &&& 0xff
@[inline] def chG (p : UInt32) : UInt32 := (p >>> 8) &&& 0xff
@[inline] def chB (p : UInt32) : UInt32 := p &&& 0xff
@[inline] def argb (a r g b : UInt32) : UInt32 :=
  ((a &&& 0xff) <<< 24) ||| ((r &&& 0xff) <<< 16) ||| ((g &&& 0xff) <<< 8) ||| (b &&& 0xff)

/-- Channel-wise addition modulo 256. -/
@[inline] def addPixels (a b : UInt32) : UInt32 :=
  argb (chA a + chA b) (chR a + chR b) (chG a + chG b) (chB a + chB b)

/-- `DIV_ROUND_UP(size, 1 << bits)` (§3.5.1). -/
def subSampleSize (size bits : Nat) : Nat := (size + 2 ^ bits - 1) / 2 ^ bits

/-! ## Transforms (§3.5) -/

/-- §3.5.1 `Average2`, per component. -/
def average2 (a b : UInt32) : UInt32 :=
  argb ((chA a + chA b) / 2) ((chR a + chR b) / 2) ((chG a + chG b) / 2) ((chB a + chB b) / 2)

/-- §3.5.1 `Select`. -/
def select (L T TL : UInt32) : UInt32 :=
  let i (c : UInt32) : Int := c.toNat
  let pA := i (chA L) + i (chA T) - i (chA TL)
  let pR := i (chR L) + i (chR T) - i (chR TL)
  let pG := i (chG L) + i (chG T) - i (chG TL)
  let pB := i (chB L) + i (chB T) - i (chB TL)
  let pL := (pA - i (chA L)).natAbs + (pR - i (chR L)).natAbs +
            (pG - i (chG L)).natAbs + (pB - i (chB L)).natAbs
  let pT := (pA - i (chA T)).natAbs + (pR - i (chR T)).natAbs +
            (pG - i (chG T)).natAbs + (pB - i (chB T)).natAbs
  if pL < pT then L else T

/-- §3.5.1 `Clamp`. -/
def clamp (a : Int) : UInt32 := if a < 0 then 0 else if a > 255 then 255 else a.toNat.toUInt32

/-- §3.5.1 `ClampAddSubtractFull`, per component. -/
def clampAddSubtractFull (a b c : UInt32) : UInt32 :=
  let f (x y z : UInt32) : UInt32 := clamp ((x.toNat : Int) + y.toNat - z.toNat)
  argb (f (chA a) (chA b) (chA c)) (f (chR a) (chR b) (chR c))
       (f (chG a) (chG b) (chG c)) (f (chB a) (chB b) (chB c))

/-- §3.5.1 `ClampAddSubtractHalf`, per component. The RFC's `(a - b) / 2` is C integer
division, which truncates toward zero (`Int.tdiv`). -/
def clampAddSubtractHalf (a b : UInt32) : UInt32 :=
  let f (x y : UInt32) : UInt32 :=
    clamp ((x.toNat : Int) + Int.tdiv ((x.toNat : Int) - y.toNat) 2)
  argb (f (chA a) (chA b)) (f (chR a) (chR b)) (f (chG a) (chG b)) (f (chB a) (chB b))

/-- §3.5.1 Table 2: prediction modes. **[interp]** The mode is the green component of the
predictor-image pixel; the RFC defines modes `0..13` only. Like libwebp we use the low
four bits of green and treat the undefined modes 14 and 15 like mode 0. -/
def predict (mode : Nat) (L T TR TL : UInt32) : UInt32 :=
  match mode with
  | 1 => L
  | 2 => T
  | 3 => TR
  | 4 => TL
  | 5 => average2 (average2 L TR) T
  | 6 => average2 L TL
  | 7 => average2 L T
  | 8 => average2 TL T
  | 9 => average2 T TR
  | 10 => average2 (average2 L TL) (average2 T TR)
  | 11 => select L T TL
  | 12 => clampAddSubtractFull L T TL
  | 13 => clampAddSubtractHalf (average2 L T) TL
  | _ => 0xff000000

/-- §3.5.1 inverse predictor transform on a `w × h` image. Border rules: the top-left pixel
is predicted by `0xff000000`, the rest of the top row by L, the leftmost column by T. For the
rightmost column, TR is "the leftmost pixel on the same row as the current pixel", which is
exactly the pixel at scan-line index `i - w + 1`. -/
def inversePredictor (w h bits : Nat) (sub : Array UInt32) (img : Array UInt32) :
    Array UInt32 := Id.run do
  let tw := subSampleSize w bits
  let mut out := img
  for y in [0:h] do
    for x in [0:w] do
      let i := y * w + x
      let pred :=
        if y = 0 then (if x = 0 then 0xff000000 else out.getD (i - 1) 0)
        else if x = 0 then out.getD (i - w) 0
        else
          let mode := (chG (sub.getD ((y / 2 ^ bits) * tw + x / 2 ^ bits) 0)).toNat % 16
          predict mode (out.getD (i - 1) 0) (out.getD (i - w) 0)
            (out.getD (i - w + 1) 0) (out.getD (i - w - 1) 0)
      out := out.setIfInBounds i (addPixels (out.getD i 0) pred)
  return out

/-- Interpret a `uint8` as an `int8` (two's complement), §3.5.2. -/
def toInt8 (v : UInt32) : Int := if v.toNat ≥ 128 then (v.toNat : Int) - 256 else v.toNat

/-- §3.5.2 `ColorTransformDelta(t, c) = (t * c) >> 5` on signed 8-bit values; only the low 8
bits of the result are used. `>>` of a negative `int` is an arithmetic shift, i.e. floor
division by 32 (`Int.ediv` by a positive divisor). -/
def colorTransformDelta (t c : UInt32) : Int := Int.ediv (toInt8 t * toInt8 c) 32

/-- §3.5.2 `InverseTransform` for one pixel. The color transform element is stored in the
sub-resolution image as: red = `red_to_blue`, green = `green_to_blue`, blue = `green_to_red`. -/
def inverseColorPixel (cte p : UInt32) : UInt32 :=
  let g2r := chB cte
  let g2b := chG cte
  let r2b := chR cte
  let green := chG p
  let tmpRed : Int := (chR p).toNat + colorTransformDelta g2r green
  let newRed : UInt32 := (Int.emod tmpRed 256).toNat.toUInt32
  let tmpBlue : Int := (chB p).toNat + colorTransformDelta g2b green +
    colorTransformDelta r2b newRed
  let newBlue : UInt32 := (Int.emod tmpBlue 256).toNat.toUInt32
  argb (chA p) newRed green newBlue

/-- §3.5.2 inverse color transform on a `w × h` image. -/
def inverseColor (w h bits : Nat) (sub : Array UInt32) (img : Array UInt32) :
    Array UInt32 := Id.run do
  let tw := subSampleSize w bits
  let mut out := img
  for y in [0:h] do
    for x in [0:w] do
      let i := y * w + x
      let cte := sub.getD ((y / 2 ^ bits) * tw + x / 2 ^ bits) 0
      out := out.setIfInBounds i (inverseColorPixel cte (out.getD i 0))
  return out

/-- §3.5.3 `AddGreenToBlueAndRed`. -/
def addGreenPixel (p : UInt32) : UInt32 :=
  argb (chA p) (chR p + chG p) (chG p) (chB p + chG p)

/-- §3.5.3 inverse subtract-green transform. -/
def inverseSubtractGreen (img : Array UInt32) : Array UInt32 := img.map addGreenPixel

/-- §3.5.4 Table 3: color table size to `width_bits`. -/
def widthBits (colorTableSize : Nat) : Nat :=
  if colorTableSize ≤ 2 then 3 else if colorTableSize ≤ 4 then 2
  else if colorTableSize ≤ 16 then 1 else 0

/-- §3.5.4 inverse color indexing transform, producing a `w × h` image from the
(possibly pixel-bundled) index image of width `subSampleSize w bits`. "If the index is equal
to or larger than color_table_size, the argb color value should be set to 0x00000000". -/
def inverseColorIndexing (w h bits : Nat) (palette : Array UInt32) (img : Array UInt32) :
    Array UInt32 := Id.run do
  let bw := subSampleSize w bits
  let bitsPerPixel := 8 / 2 ^ bits
  let mut out := Array.replicate (w * h) (0 : UInt32)
  for y in [0:h] do
    for x in [0:w] do
      let packed := (chG (img.getD (y * bw + x / 2 ^ bits) 0)).toNat
      let idx := packed / 2 ^ ((x % 2 ^ bits) * bitsPerPixel) % 2 ^ bitsPerPixel
      out := out.setIfInBounds (y * w + x) (palette.getD idx 0)
  return out

/-- §3.5.4: "every final color in the color table can be obtained by adding the previous color
component values by each ARGB component separately". -/
def deltaDecodePalette (raw : Array UInt32) : Array UInt32 := Id.run do
  let mut out := raw
  for i in [1:raw.size] do
    out := out.setIfInBounds i (addPixels (out.getD i 0) (out.getD (i - 1) 0))
  return out

/-- A transform as read from the bitstream, with the image width at the time it was read. -/
inductive Transform where
  | predictor (w bits : Nat) (sub : Array UInt32)
  | color (w bits : Nat) (sub : Array UInt32)
  | subtractGreen
  | colorIndexing (w bits : Nat) (palette : Array UInt32)

def Transform.inverse (h : Nat) : Transform → Array UInt32 → Array UInt32
  | .predictor w bits sub, img => inversePredictor w h bits sub img
  | .color w bits sub, img => inverseColor w h bits sub img
  | .subtractGreen, img => inverseSubtractGreen img
  | .colorIndexing w bits pal, img => inverseColorIndexing w h bits pal img

/-- §3.5: "The inverse transforms are applied in the reverse order that they are read from the
bitstream, that is, last one first." (`ts` is in bitstream order.) -/
def applyInverseTransforms (h : Nat) (ts : List Transform) (img : Array UInt32) :
    Array UInt32 :=
  ts.foldr (fun t acc => t.inverse h acc) img

/-! ## LZ77 (§3.6.2.2) and color cache (§3.6.2.3) -/

/-- §3.6.2.2.1 Figure 20: distance code to neighboring pixel offset `(xi, yi)`. -/
def distanceMap : Array (Int × Int) := #[
  (0, 1),  (1, 0),  (1, 1),  (-1, 1), (0, 2),  (2, 0),  (1, 2),
  (-1, 2), (2, 1),  (-2, 1), (2, 2),  (-2, 2), (0, 3),  (3, 0),
  (1, 3),  (-1, 3), (3, 1),  (-3, 1), (2, 3),  (-2, 3), (3, 2),
  (-3, 2), (0, 4),  (4, 0),  (1, 4),  (-1, 4), (4, 1),  (-4, 1),
  (3, 3),  (-3, 3), (2, 4),  (-2, 4), (4, 2),  (-4, 2), (0, 5),
  (3, 4),  (-3, 4), (4, 3),  (-4, 3), (5, 0),  (1, 5),  (-1, 5),
  (5, 1),  (-5, 1), (2, 5),  (-2, 5), (5, 2),  (-5, 2), (4, 4),
  (-4, 4), (3, 5),  (-3, 5), (5, 3),  (-5, 3), (0, 6),  (6, 0),
  (1, 6),  (-1, 6), (6, 1),  (-6, 1), (2, 6),  (-2, 6), (6, 2),
  (-6, 2), (4, 5),  (-4, 5), (5, 4),  (-5, 4), (3, 6),  (-3, 6),
  (6, 3),  (-6, 3), (0, 7),  (7, 0),  (1, 7),  (-1, 7), (5, 5),
  (-5, 5), (7, 1),  (-7, 1), (4, 6),  (-4, 6), (6, 4),  (-6, 4),
  (2, 7),  (-2, 7), (7, 2),  (-7, 2), (3, 7),  (-3, 7), (7, 3),
  (-7, 3), (5, 6),  (-5, 6), (6, 5),  (-6, 5), (8, 0),  (4, 7),
  (-4, 7), (7, 4),  (-7, 4), (8, 1),  (8, 2),  (6, 6),  (-6, 6),
  (8, 3),  (5, 7),  (-5, 7), (7, 5),  (-7, 5), (8, 4),  (6, 7),
  (-6, 7), (7, 6),  (-7, 6), (8, 5),  (7, 7),  (-7, 7), (8, 6),
  (8, 7)]

/-- §3.6.2.2.1: distance code to scan-line distance for an image of width `w`. -/
def planeCodeToDistance (w code : Nat) : Nat :=
  if code > 120 then code - 120 else
  let (xi, yi) := distanceMap.getD (code - 1) (0, 0)
  let dist := xi + yi * (w : Int)
  if dist < 1 then 1 else dist.toNat

/-- §3.6.2.3 color cache size for `color_cache_code_bits` (0 = no cache). -/
def cacheSize (bits : Nat) : Nat := if bits = 0 then 0 else 2 ^ bits

/-- §3.6.2.3: index of color `c` in a cache with `bits` bits:
`(0x1e35a7bd * color) >> (32 - color_cache_code_bits)` in 32-bit unsigned arithmetic. -/
def cacheIndex (bits : Nat) (c : UInt32) : Nat :=
  ((0x1e35a7bd * c) >>> (32 - bits).toUInt32).toNat

/-- Insert a color in the cache ("Only one lookup is done in a color cache; there is no
conflict resolution"). No-op without a cache. -/
def cacheInsert (bits : Nat) (cache : Array UInt32) (c : UInt32) : Array UInt32 :=
  if bits = 0 then cache else cache.setIfInBounds (cacheIndex bits c) c

/-! ## Reading with the primitives -/

section Decoder
variable (P : Prims) (d : ByteArray)

@[inline] def rb (n : Nat) : M Nat := fun pos => P.readBits d pos n
@[inline] def readSym (c : Code) : M Nat := fun pos => c.decode pos
@[inline] def buildCode (lens : Array Nat) : M Code := fun pos =>
  match P.build d lens with
  | .ok c => .ok (c, pos)
  | .error e => .error e

/-- §3.6.2.2: value of a (length or distance) prefix code, minus one. -/
def prefixValueMinusOne (prefixCode : Nat) : M Nat :=
  if prefixCode < 4 then pure prefixCode
  else do
    let extraBits := (prefixCode - 2) / 2
    let offset := (2 + prefixCode % 2) * 2 ^ extraBits
    return offset + (← rb P d extraBits)

/-- §3.7.2.1.2: `kCodeLengthCodeOrder`. -/
def kCodeLengthCodeOrder : Array Nat :=
  #[17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- §3.7.2.1.2: reading code lengths with the code-length code. `maxSym` counts the remaining
code-length *codes* that may be read — **[interp]** "used to read up to max_symbol code
lengths": like libwebp, each code (literal or repeat code 16/17/18) counts as one.
Code 16 repeats `prevLen` (initially 8). A repeat that would overflow the alphabet is an
error. -/
def readCodeLengths (clCode : Code) (numSymbols : Nat) (maxSym prevLen : Nat)
    (lens : Array Nat) : M (Array Nat) := do
  if hlt : lens.size < numSymbols then
    if maxSym = 0 then return lens
    else
      let c ← readSym clCode
      if c < 16 then
        readCodeLengths clCode numSymbols (maxSym - 1) (if c = 0 then prevLen else c)
          (lens.push c)
      else if c = 16 then
        let rep := (← rb P d 2) + 3
        if lens.size + rep > numSymbols then throw "code length repeat overflows alphabet"
        readCodeLengths clCode numSymbols (maxSym - 1) prevLen
          (lens ++ Array.replicate rep prevLen)
      else if c = 17 then
        let rep := (← rb P d 3) + 3
        if lens.size + rep > numSymbols then throw "code length repeat overflows alphabet"
        readCodeLengths clCode numSymbols (maxSym - 1) prevLen
          (lens ++ Array.replicate rep 0)
      else
        let rep := (← rb P d 7) + 11
        if lens.size + rep > numSymbols then throw "code length repeat overflows alphabet"
        readCodeLengths clCode numSymbols (maxSym - 1) prevLen
          (lens ++ Array.replicate rep 0)
  else return lens
termination_by numSymbols - lens.size
decreasing_by all_goals (simp only [Array.size_push, Array.size_append, Array.size_replicate]; omega)

/-- §3.7.2.1: read one prefix code for an alphabet of `alphabetSize` symbols. -/
def readPrefixCode (alphabetSize : Nat) : M Code := do
  if (← rb P d 1) = 1 then
    -- §3.7.2.1.1 simple code length code.
    let numSymbols := (← rb P d 1) + 1
    let isFirst8Bits ← rb P d 1
    let symbol0 ← rb P d (1 + 7 * isFirst8Bits)
    -- [interp] symbols ≥ alphabetSize are dropped: "a prefix code for each symbol type ... is
    -- formed using their respective alphabet sizes" (libwebp behaves the same way).
    let mut lens := (Array.replicate alphabetSize 0).setIfInBounds symbol0 1
    if numSymbols = 2 then
      let symbol1 ← rb P d 8
      lens := lens.setIfInBounds symbol1 1
    buildCode P d lens
  else
    -- §3.7.2.1.2 normal code length code.
    let numCodeLengths := 4 + (← rb P d 4)
    let mut clLens := Array.replicate 19 0
    for i in [0:numCodeLengths] do
      clLens := clLens.setIfInBounds (kCodeLengthCodeOrder.getD i 0) (← rb P d 3)
    let clCode ← buildCode P d clLens
    let maxSymbol ←
      if (← rb P d 1) = 0 then pure alphabetSize
      else do
        let lengthNBits := 2 + 2 * (← rb P d 3)
        pure (2 + (← rb P d lengthNBits))
    if maxSymbol > alphabetSize then throw "max_symbol larger than alphabet"
    let lens ← readCodeLengths P d clCode alphabetSize maxSymbol 8 #[]
    buildCode P d (lens ++ Array.replicate (alphabetSize - lens.size) 0)

/-- §3.7.2: a prefix code group (green+length+cache, red, blue, alpha, distance). -/
structure Group where
  green : Code
  red : Code
  blue : Code
  alpha : Code
  dist : Code

/-- §3.7.2.1 / §3.7.2.3: alphabet sizes; the green alphabet is `256 + 24 + color_cache_size`. -/
def readGroup (cacheBits : Nat) : M Group := do
  let g ← readPrefixCode P d (256 + 24 + cacheSize cacheBits)
  let r ← readPrefixCode P d 256
  let b ← readPrefixCode P d 256
  let a ← readPrefixCode P d 256
  let dist ← readPrefixCode P d 40
  return ⟨g, r, b, a, dist⟩

/-- Read `n` prefix code groups. -/
def readGroups (cacheBits : Nat) : Nat → Array Group → M (Array Group)
  | 0, acc => pure acc
  | n + 1, acc => do readGroups cacheBits n (acc.push (← readGroup P d cacheBits))

/-- §3.6.2.3: `color-cache-info`. "The range of allowed values for color_cache_code_bits is
[1..11]. Compliant decoders MUST indicate a corrupted bitstream for other values." -/
def readColorCacheInfo : M Nat := do
  if (← rb P d 1) = 1 then
    let bits ← rb P d 4
    if bits < 1 ∨ bits > 11 then throw "invalid color cache size"
    return bits
  else return 0

/-- Entropy image used to select prefix code groups (§3.7.2.2): `(prefix_bits, width, image)`. -/
structure MetaInfo where
  bits : Nat
  width : Nat
  image : Array UInt32

/-- §3.7.2.2.2: the prefix code group index of pixel `(x, y)`. -/
def groupIndex (m : Option MetaInfo) (x y : Nat) : Nat :=
  match m with
  | none => 0
  | some m => ((m.image.getD ((y / 2 ^ m.bits) * m.width + x / 2 ^ m.bits) 0) >>> 8).toNat % 65536

/-- §3.6.2.2 "Copy L pixels (in scan-line order) from the sequence of pixels starting at the
current position minus D pixels", inserting every copied pixel in the color cache. -/
def copyPixels (cacheBits dist : Nat) :
    Nat → Nat → Array UInt32 → Array UInt32 → Array UInt32 × Array UInt32
  | 0, _, px, cache => (px, cache)
  | n + 1, i, px, cache =>
    let p := px.getD (i - dist) 0
    copyPixels cacheBits dist n (i + 1) (px.setIfInBounds i p) (cacheInsert cacheBits cache p)

/-- §3.7.2.3 "Decoding Entropy-Coded Image Data": decode the `w × h` pixels. The end of image
is implicit (§3.8). **[interp]** A backward reference whose distance reaches before the first
pixel or whose length runs past the last pixel is invalid. -/
def decodePixels (w h cacheBits : Nat) (groups : Array Group) (mi : Option MetaInfo)
    (i : Nat) (px cache : Array UInt32) : M (Array UInt32) := do
  if _hi : i < w * h then
    let x := i % w
    let y := i / w
    let some g := groups[groupIndex mi x y]? | throw "prefix code group out of range"
    let s ← readSym g.green
    if s < 256 then
      -- §3.6.2.1 literal: green, then red, blue, alpha.
      let r ← readSym g.red
      let b ← readSym g.blue
      let a ← readSym g.alpha
      let p := argb a.toUInt32 r.toUInt32 s.toUInt32 b.toUInt32
      decodePixels w h cacheBits groups mi (i + 1) (px.setIfInBounds i p)
        (cacheInsert cacheBits cache p)
    else if s < 256 + 24 then
      -- §3.6.2.2 backward reference.
      let lenM1 ← prefixValueMinusOne P d (s - 256)
      let distSym ← readSym g.dist
      let distCode := (← prefixValueMinusOne P d distSym) + 1
      let dist := planeCodeToDistance w distCode
      if dist > i then throw "backward reference before start of image"
      if i + (lenM1 + 1) > w * h then throw "backward reference past end of image"
      let (px', cache') := copyPixels cacheBits dist (lenM1 + 1) i px cache
      decodePixels w h cacheBits groups mi (i + lenM1 + 1) px' cache'
    else
      -- §3.6.2.3 color cache code.
      let p := cache.getD (s - (256 + 24)) 0
      decodePixels w h cacheBits groups mi (i + 1) (px.setIfInBounds i p)
        (cacheInsert cacheBits cache p)
  else return px
termination_by w * h - i
decreasing_by all_goals omega

/-- §3.8.3 `data = prefix-codes lz77-coded-image`, given the color cache and mi info. -/
def decodeData (w h cacheBits : Nat) (mi : Option MetaInfo) (numGroups : Nat) :
    M (Array UInt32) := do
  let groups ← readGroups P d cacheBits numGroups #[]
  decodePixels P d w h cacheBits groups mi 0 (Array.replicate (w * h) 0)
    (Array.replicate (cacheSize cacheBits) 0)

/-- §3.8.3 `entropy-coded-image = color-cache-info data` (sub-resolution images: no
transforms, no mi prefix codes, a single prefix code group). -/
def decodeEntropyCodedImage (w h : Nat) : M (Array UInt32) := do
  let cacheBits ← readColorCacheInfo P d
  decodeData P d w h cacheBits none 1

/-- §3.8.3 `spatially-coded-image = color-cache-info mi-prefix data`. -/
def decodeSpatiallyCodedImage (w h : Nat) : M (Array UInt32) := do
  let cacheBits ← readColorCacheInfo P d
  if (← rb P d 1) = 1 then
    -- §3.7.2.2.1 entropy image.
    let prefixBits := (← rb P d 3) + 2
    let pw := subSampleSize w prefixBits
    let ph := subSampleSize h prefixBits
    let ent ← decodeEntropyCodedImage P d pw ph
    -- §3.7.2.2.2 `num_prefix_groups = max(entropy image) + 1`.
    let numGroups := ent.foldl (fun (m : Nat) (p : UInt32) => max m ((p >>> 8).toNat % 65536)) 0 + 1
    decodeData P d w h cacheBits (some ⟨prefixBits, pw, ent⟩) numGroups
  else
    decodeData P d w h cacheBits none 1

/-- §3.5 / §3.8.2 `optional-transform`: read transforms, returning them in bitstream order and
the final (possibly pixel-bundled) image width. "Each transform is allowed to be used only
once." At most four transforms can be read, so 5 iterations of fuel suffice. -/
def readTransforms (h : Nat) : Nat → List Nat → Nat → List Transform → M (List Transform × Nat)
  | 0, _, w, acc => pure (acc, w)
  | fuel + 1, seen, w, acc => do
    if (← rb P d 1) = 0 then return (acc, w)
    let ty ← rb P d 2
    if ty ∈ seen then throw "transform used twice"
    match ty with
    | 0 =>
      let bits := (← rb P d 3) + 2
      let sub ← decodeEntropyCodedImage P d (subSampleSize w bits) (subSampleSize h bits)
      readTransforms h fuel (ty :: seen) w (acc ++ [.predictor w bits sub])
    | 1 =>
      let bits := (← rb P d 3) + 2
      let sub ← decodeEntropyCodedImage P d (subSampleSize w bits) (subSampleSize h bits)
      readTransforms h fuel (ty :: seen) w (acc ++ [.color w bits sub])
    | 2 => readTransforms h fuel (ty :: seen) w (acc ++ [.subtractGreen])
    | _ =>
      let colorTableSize := (← rb P d 8) + 1
      let bits := widthBits colorTableSize
      let raw ← decodeEntropyCodedImage P d colorTableSize 1
      readTransforms h fuel (ty :: seen) (subSampleSize w bits)
        (acc ++ [.colorIndexing w bits (deltaDecodePalette raw)])

/-- §3.8.1 `image-stream = optional-transform spatially-coded-image`, for a `w × h` image;
returns the final ARGB pixels. -/
def decodeImageStream (w h : Nat) : M (Array UInt32) := do
  let (ts, xsize) ← readTransforms P d h 5 [] w []
  let img ← decodeSpatiallyCodedImage P d xsize h
  return applyInverseTransforms h ts img

/-- §3.4 header: signature `0x2f`, 14-bit width-1, 14-bit height-1, `alpha_is_used`, 3-bit
version that "MUST be set to 0. Any other value MUST be treated as an error." -/
def readHeader : M (Nat × Nat × Bool) := do
  if (← rb P d 8) ≠ 0x2f then throw "bad VP8L signature"
  let w := (← rb P d 14) + 1
  let h := (← rb P d 14) + 1
  let alphaIsUsed := (← rb P d 1) = 1
  if (← rb P d 3) ≠ 0 then throw "bad VP8L version"
  return (w, h, alphaIsUsed)

end Decoder

/-- A decoded lossless image. -/
structure Image where
  width : Nat
  height : Nat
  /-- `alpha_is_used` header hint (§3.4; "SHOULD NOT impact decoding"). -/
  alphaHint : Bool
  pixels : Array UInt32

/-- Decode the payload of a 'VP8L' chunk (§2.6, §3) with primitives `P`. -/
def decodeWith (P : Prims) (d : ByteArray) : Except String Image :=
  (do
    let (w, h, a) ← readHeader P d
    let px ← decodeImageStream P d w h
    return ⟨w, h, a, px⟩ : M Image).run' 0

/-- Decode a headerless image stream of implicit dimensions `w × h` (used by 'ALPH', §2.7.1.2). -/
def decodeStreamWith (P : Prims) (d : ByteArray) (w h : Nat) : Except String (Array UInt32) :=
  (decodeImageStream P d w h).run' 0

/-- **The specification** of the lossless bitstream. -/
def decode (d : ByteArray) : Except String Image := decodeWith specPrims d

/-- **The specification** of headerless lossless image streams (ALPH). -/
def decodeStream (d : ByteArray) (w h : Nat) : Except String (Array UInt32) :=
  decodeStreamWith specPrims d w h

/-- Only the header (§3.4), used to learn the dimensions without decoding. -/
def readHeaderOnly (d : ByteArray) : Except String (Nat × Nat × Bool) :=
  (readHeader specPrims d).run' 0

end WebP.Spec.VP8L
