import WebP.Spec.VP8.BoolDecoder
/-!
# Optimized boolean decoder

`fastBoolGet` computes the same function as the reference `bool_get` (`Spec.VP8.boolGet`), but
renormalizes with a single shift instead of the bit-at-a-time `while (range < 128)` loop: the
shift amount `k` is the number of leading zeros of the 8-bit range, and the (at most one) byte
that the loop would shift in when `bit_count` reaches 8 is OR-ed in at its final position.
States violating the decoder's invariant (`bit_count < 8`, `range ≠ 0` after the decision) —
which never occur — fall back to the reference loop, so the two functions are equal on *all*
states (`WebP.Proofs.VP8Bool.fastBoolGet_eq`).
-/
namespace WebP.VP8

open WebP.Spec.VP8

/-- Number of left shifts bringing `r ∈ [1, 127]` into `[128, 255]` (`7 - ⌊log₂ r⌋`). -/
@[inline] def normShift (r : Nat) : Nat :=
  if r ≥ 64 then 1 else if r ≥ 32 then 2 else if r ≥ 16 then 3 else if r ≥ 8 then 4
  else if r ≥ 4 then 5 else if r ≥ 2 then 6 else 7

/-- `k` iterations of the normalization loop at once (valid when `bit_count < 8`, `k ≤ 7`):
`value` and `range` are shifted by `k`, and if `bit_count` passes 8 the next input byte is
OR-ed in at the position it would have reached. -/
@[inline] def shiftBy (d : BoolDecoder) (k : Nat) : BoolDecoder :=
  let bc := d.bitCount + k
  if bc ≥ 8 then
    if d.inputLen ≠ 0 then
      { d with range := d.range <<< k.toUInt32,
               value := (d.value <<< k.toUInt32) ||| ((byteAt d.input d.pos).toUInt32 <<< (bc - 8).toUInt32),
               bitCount := bc - 8, pos := d.pos + 1, inputLen := d.inputLen - 1 }
    else
      { d with range := d.range <<< k.toUInt32, value := d.value <<< k.toUInt32, bitCount := bc - 8 }
  else
    { d with range := d.range <<< k.toUInt32, value := d.value <<< k.toUInt32, bitCount := bc }

/-- Renormalize after the decision: nothing to do if `range ≥ 128`, one shift if the invariant
holds, the reference loop otherwise. -/
@[inline] def renorm (d : BoolDecoder) (range value : UInt32) : BoolDecoder :=
  if range ≥ 128 then { d with range, value }
  else if range ≠ 0 ∧ d.bitCount < 8 then shiftBy { d with range, value } (normShift range.toNat)
  else normalize 8 { d with range, value }

/-- `bool_get`, renormalizing with one shift. -/
def fastBoolGet (d : BoolDecoder) (probability : Nat) : Bool × BoolDecoder :=
  let split : UInt32 := (1 : UInt32) + (((d.range - 1) * UInt32.ofNat probability) >>> 8)
  let SPLIT : UInt32 := split <<< 8
  if d.value ≥ SPLIT then (true, renorm d (d.range - split) (d.value - SPLIT))
  else (false, renorm d split d.value)

/-- The optimized primitives. -/
def fastPrims : Prims := ⟨fastBoolGet⟩

end WebP.VP8
