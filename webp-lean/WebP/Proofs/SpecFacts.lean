import WebP.Spec.Lossless
import Std.Tactic.BVDecide
/-!
# Sanity checks of the formal specification against statements of RFC 9649

These theorems do not concern the decoder; they check that the formal definitions say what
the RFC text says, increasing confidence in the transcription.
-/
namespace WebP.Proofs

open WebP.Spec WebP.Spec.VP8L

/-- §3.2: "`b = ReadBits(2);` is equivalent with `b = ReadBits(1); b |= ReadBits(1) << 1;`",
in general: reading `a + b` bits equals reading `a` bits, then `b` bits shifted left by `a`. -/
theorem readBitsVal_add (d : ByteArray) (pos a b : Nat) :
    readBitsVal d pos (a + b) = readBitsVal d pos a + 2 ^ a * readBitsVal d (pos + a) b := by
  induction a generalizing pos with
  | zero => simp [readBitsVal]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [readBitsVal]
    rw [ih (pos + 1), show pos + 1 + a = pos + (a + 1) by omega, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_assoc]
    congr 2
    rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

/-- The RFC's literal example. -/
theorem readBits2 (d : ByteArray) (pos : Nat) :
    readBitsVal d pos 2 = readBitsVal d pos 1 ||| (readBitsVal d (pos + 1) 1 <<< 1) := by
  have h1 : readBitsVal d pos 1 = bit d pos := by simp [readBitsVal]
  have h2 : readBitsVal d (pos + 1) 1 = bit d (pos + 1) := by simp [readBitsVal]
  have hb : ∀ i, bit d i < 2 := fun i => Nat.mod_lt _ (by decide)
  simp only [readBitsVal, Nat.add_zero, Nat.mul_zero, Nat.shiftLeft_eq]
  have := hb pos; have := hb (pos + 1)
  generalize bit d pos = x at *
  generalize bit d (pos + 1) = y at *
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
  rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

/-- A `ReadBits(n)` value fits in `n` bits. -/
theorem readBitsVal_lt (d : ByteArray) (pos n : Nat) : readBitsVal d pos n < 2 ^ n := by
  induction n generalizing pos with
  | zero => simp [readBitsVal]
  | succ n ih =>
    simp only [readBitsVal, Nat.pow_succ]
    have := ih (pos + 1)
    have : bit d pos < 2 := Nat.mod_lt _ (by decide)
    omega

/-- §3.5.3: adding green back undoes subtracting it ("the decoder needs to add the green value
to both the red and blue values"). -/
theorem addGreen_subtractGreen (a r g b : UInt32) (ha : a < 256) (hr : r < 256) (hg : g < 256)
    (hb : b < 256) :
    addGreenPixel (argb a (r - g) g (b - g)) = argb a r g b := by
  unfold addGreenPixel argb chA chR chG chB
  bv_decide

/-- §3.6.2.2.1: "the distance code 1 indicates an offset of (0, 1) ... the pixel above the
current pixel"; "the distance code 3 indicates the top-left pixel"; there are 120 codes. -/
theorem distanceMap_facts (w : Nat) (hw : 2 ≤ w) :
    planeCodeToDistance w 1 = w ∧ planeCodeToDistance w 2 = 1 ∧
    planeCodeToDistance w 3 = w + 1 ∧ distanceMap.size = 120 := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> simp [planeCodeToDistance, distanceMap] <;> (try split) <;> omega

/-- §3.6.2.2.1: distance codes larger than 120 denote the scan-line distance offset by 120. -/
theorem planeCodeToDistance_large (w c : Nat) (h : 120 < c) :
    planeCodeToDistance w c = c - 120 := by
  simp [planeCodeToDistance, h]

end WebP.Proofs
