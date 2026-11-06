/-!
# VP8 boolean entropy decoder (RFC 6386 §7)

This is a port of libwebp's `VP8BitReader` (src/utils/bit_reader*). libwebp keeps
`range - 1` in `range` and pre-loads up to 56 bits; we load one byte at a time.
Both variants consume exactly the same bits and set `eof` at exactly the same moment:
`eof` becomes true the first time a bit is requested while fewer than 8 unread bits
(the 8-bit decoding window) remain *and* the buffer is exhausted. libwebp then shifts
in 8 zero bits once, and afterwards stops shifting (`bits = 0`), which we replicate.

libwebp-specific behaviour reproduced here (RFC 6386 is silent):
* `init` fails if the first byte of a non-empty partition is `0xff`
  (libwebp `VP8InitBitReader` returns 0 because RFC 6386 §7.2 requires `value < range`).
* Every `eof` causes the frame decode to fail (checked per macroblock / per mode row
  by the caller), so values decoded after `eof` never influence a successful output.
-/
namespace WebP.VP8Libwebp

/-- Bounds-checked byte read, `0` when out of range (never panics). -/
@[inline] def rdByte (a : ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0

/-- Bounds-checked byte read as `Nat`. -/
@[inline] def rd (a : ByteArray) (i : Nat) : Nat := (rdByte a i).toNat

/-- Bounds-checked byte write (no-op when out of range). -/
@[inline] def wr (a : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < a.size then a.set i v h else a

/-- Write a `Nat` (truncated to 8 bits). -/
@[inline] def wrN (a : ByteArray) (i : Nat) (v : Nat) : ByteArray := wr a i v.toUInt8

/-- `floor (log2 n)` for `1 ≤ n < 256`; returns 0 for 0. -/
@[inline] def log2Floor8 (n : Nat) : Nat :=
  if n ≥ 128 then 7 else if n ≥ 64 then 6 else if n ≥ 32 then 5 else if n ≥ 16 then 4
  else if n ≥ 8 then 3 else if n ≥ 4 then 2 else if n ≥ 2 then 1 else 0

/-- Boolean decoder state. -/
structure BoolDec where
  data  : ByteArray
  /-- next byte to load -/
  pos   : Nat
  /-- end of this partition (exclusive) -/
  stop  : Nat
  /-- buffered bits; the decoding window is `value >>> bits` -/
  value : Nat
  /-- `range - 1`, in `[127, 254]` while not at eof -/
  range : Nat
  /-- number of buffered bits beyond the 8-bit window (may be negative) -/
  bits  : Int
  eof   : Bool

namespace BoolDec

/-- Load one more byte (libwebp `VP8LoadNewBytes`/`VP8LoadFinalBytes`). -/
@[inline] def load (br : BoolDec) : BoolDec :=
  if br.pos < br.stop then
    { br with value := (br.value <<< 8) ||| rd br.data br.pos, pos := br.pos + 1, bits := br.bits + 8 }
  else if !br.eof then
    { br with value := br.value <<< 8, bits := br.bits + 8, eof := true }
  else
    { br with bits := 0 }

/-- Create a decoder over `data[start, start+size)`. Returns `none` when libwebp's
`VP8InitBitReader` would fail (first byte `0xff`). -/
def init (data : ByteArray) (start size : Nat) : Option BoolDec :=
  let br : BoolDec := { data, pos := start, stop := start + size, value := 0, range := 254,
                        bits := -8, eof := false }
  let br := br.load
  if (br.value >>> br.bits.toNat) ≤ br.range then some br else none

/-- Decode one bool with probability `prob/256` of being 0 (libwebp `VP8GetBit`). -/
@[inline] def getBit (br : BoolDec) (prob : Nat) : Bool × BoolDec :=
  let br := if br.bits < 0 then br.load else br
  let range := br.range
  let pos := br.bits.toNat
  let split := (range * prob) >>> 8
  let v := br.value >>> pos
  if v > split then
    let r := range - split
    let shift := 7 - log2Floor8 r
    (true, { br with value := br.value - ((split + 1) <<< pos),
                     range := (r <<< shift) - 1, bits := br.bits - shift })
  else
    let r := split + 1
    let shift := 7 - log2Floor8 r
    (false, { br with range := (r <<< shift) - 1, bits := br.bits - shift })

/-- `VP8GetValue`: `n` bits, most significant first, each with probability 128. -/
def getValue (br : BoolDec) (n : Nat) : Nat × BoolDec := Id.run do
  let mut br := br
  let mut v := 0
  for _ in [0:n] do
    let (b, br') := br.getBit 0x80
    br := br'
    v := (v <<< 1) ||| (if b then 1 else 0)
  return (v, br)

/-- `VP8Get`: a single flag. -/
@[inline] def getFlag (br : BoolDec) : Bool × BoolDec := br.getBit 0x80

/-- `VP8GetSignedValue`: magnitude of `n` bits followed by a sign flag. -/
def getSignedValue (br : BoolDec) (n : Nat) : Int × BoolDec :=
  let (v, br) := br.getValue n
  let (s, br) := br.getFlag
  (if s then -(v : Int) else (v : Int), br)

/-- `VP8GetSigned`: returns `±v` using one probability-1/2 bool (libwebp's branchless
variant, replicated exactly including its range update). -/
@[inline] def getSigned (br : BoolDec) (v : Nat) : Int × BoolDec :=
  let br := if br.bits < 0 then br.load else br
  let pos := br.bits.toNat
  let split := br.range >>> 1
  let w := br.value >>> pos
  if w > split then
    (-(v : Int), { br with bits := br.bits - 1, range := (br.range - 1) ||| 1,
                           value := br.value - ((split + 1) <<< pos) })
  else
    ((v : Int), { br with bits := br.bits - 1, range := br.range ||| 1 })

end BoolDec
end WebP.VP8Libwebp
