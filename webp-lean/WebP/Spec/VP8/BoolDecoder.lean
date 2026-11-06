/-!
# The boolean entropy decoder (RFC 6386 §7, reference source §20.2 `bool_decoder.h`)

A literal transcription of the reference decoder's `struct bool_decoder`, `init_bool_decoder`,
`bool_get`, `bool_get_bit`, `bool_get_uint`, `bool_get_int`, `bool_maybe_get_int` and
`bool_read_tree`.

C types are modelled exactly: `range` and `value` are `unsigned int` (32 bits, so `value <<= 1`
wraps modulo 2³²; **[interp]** `unsigned int` is taken to be 32 bits wide, as on every platform the
reference decoder is built for); the input pointer is an index `pos` into the buffer, and
`input_len` is the number of bytes left. As in the reference code, reading past the end of a
partition is *not* an error: no more bytes are shifted in (i.e. zeros are read).

The rest of the decoder is written against an abstract `Prims` record holding `bool_get`, so that
the shipped decoder can use an optimized implementation (`WebP.VP8.fastBoolGet`, proven equal
to `boolGet` in `WebP.Proofs.VP8Bool`).
-/
namespace WebP.Spec.VP8

/-- `buf[i]`, or `0` out of bounds (all reads of the reference decoder are in bounds; the default
only makes the function total). -/
@[inline] def byteAt (buf : ByteArray) (i : Nat) : UInt8 :=
  if h : i < buf.size then buf[i] else 0

/-- `struct bool_decoder` (§20.2). -/
structure BoolDecoder where
  /-- the buffer `input` points into -/
  input : ByteArray
  /-- `input`: index of the next compressed data byte -/
  pos : Nat
  /-- `input_len`: number of bytes left -/
  inputLen : Nat
  /-- `range`: identical to the encoder's range -/
  range : UInt32
  /-- `value`: contains at least 8 significant bits -/
  value : UInt32
  /-- `bit_count`: number of bits shifted out of `value`, at most 7 -/
  bitCount : Nat

/-- `init_bool_decoder(d, start_partition, sz)` for the partition `buf[start, start + sz)`. -/
def initBoolDecoder (buf : ByteArray) (start sz : Nat) : BoolDecoder :=
  if sz ≥ 2 then
    { input := buf, pos := start + 2, inputLen := sz - 2, range := 255, bitCount := 0,
      value := ((byteAt buf start).toUInt32 <<< 8) ||| (byteAt buf (start + 1)).toUInt32 }
  else
    -- `input = NULL`, `input_len = 0`
    { input := buf, pos := 0, inputLen := 0, range := 255, bitCount := 0, value := 0 }

/-- One iteration of the normalization loop of `bool_get`:
```
d->value <<= 1; d->range <<= 1;
if (++d->bit_count == 8) { d->bit_count = 0;
  if (d->input_len) { d->value |= *d->input++; d->input_len--; } }
``` -/
def shiftOnce (d : BoolDecoder) : BoolDecoder :=
  let d := { d with value := d.value <<< 1, range := d.range <<< 1, bitCount := d.bitCount + 1 }
  if d.bitCount = 8 then
    let d := { d with bitCount := 0 }
    if d.inputLen ≠ 0 then
      { d with value := d.value ||| (byteAt d.input d.pos).toUInt32, pos := d.pos + 1,
               inputLen := d.inputLen - 1 }
    else d
  else d

/-- `while (d->range < 128) { ... }`, with fuel. After the decision of `bool_get` the range is at
least 1, so the loop body runs at most 7 times: the fuel `8` used by `boolGet` never runs out. -/
def normalize : Nat → BoolDecoder → BoolDecoder
  | 0, d => d
  | n + 1, d => if d.range < 128 then normalize n (shiftOnce d) else d

/-- `bool_get(d, probability)` (§7.3, §20.2): decode one bool whose probability of being `0` is
`probability / 256`. -/
def boolGet (d : BoolDecoder) (probability : Nat) : Bool × BoolDecoder :=
  let split : UInt32 := (1 : UInt32) + (((d.range - 1) * UInt32.ofNat probability) >>> 8)
  let SPLIT : UInt32 := split <<< 8
  if d.value ≥ SPLIT then
    -- encoded a one
    (true, normalize 8 { d with range := d.range - split, value := d.value - SPLIT })
  else
    -- encoded a zero
    (false, normalize 8 { d with range := split })

/-- The primitive operations the decoder is written against. -/
structure Prims where
  /-- `bool_get` -/
  boolGet : BoolDecoder → Nat → Bool × BoolDecoder

/-- The reference primitives. -/
def specPrims : Prims := ⟨boolGet⟩

/-- A computation reading from a boolean decoder. -/
abbrev BoolM := StateM BoolDecoder

section
variable (P : Prims)

/-- `bool_get(bool, probability)` as a `BoolM` action. -/
@[inline] def get (probability : Nat) : BoolM Bool := fun d => P.boolGet d probability

/-- `bool_get_bit`: a bool with probability 1/2. -/
@[inline] def getBit : BoolM Bool := get P 128

/-- `bool_get_uint(br, bits)`: `bits` bits, most significant first. -/
def getUint (bits : Nat) : BoolM Nat := do
  let mut z := 0
  for k in [0:bits] do
    let bit := bits - 1 - k
    let b ← getBit P
    z := z ||| (b.toNat <<< bit)
  return z

/-- `bool_get_int(br, bits)`: magnitude (`bits` bits), then a sign bit. -/
def getInt (bits : Nat) : BoolM Int := do
  let z ← getUint P bits
  let s ← getBit P
  return if s then -(z : Int) else (z : Int)

/-- `bool_maybe_get_int(br, bits)`: a flag, then (if set) `bool_get_int(br, bits)`. -/
def maybeGetInt (bits : Nat) : BoolM Int := do
  if ← getBit P then getInt P bits else return 0

/-- `bool_read_tree(bool, t, p)` (§8.1): `while ((i = t[i + bool_get(bool, p[i>>1])]) > 0);
return -i;` — the probabilities are `probs[pOff + i/2]`. Leaves are stored negated
(`-0 = 0` is a leaf too). The fuel `t.size` is never exhausted for the RFC's trees, whose
internal links always point forward. -/
def readTree (t : Array Int) (probs : Array Nat) (pOff : Nat) : BoolM Nat :=
  go t.size 0
where
  go : Nat → Nat → BoolM Nat
    | 0, _ => return 0
    | fuel + 1, i => do
      let b ← get P (probs.getD (pOff + (i >>> 1)) 0)
      let j := t.getD (i + b.toNat) 0
      if j > 0 then go fuel j.toNat else return (-j).toNat

end
end WebP.Spec.VP8
