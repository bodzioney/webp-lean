import WebP.VP8.BoolDecoder
/-!
# The one-shift boolean decoder equals the reference `bool_get`

Main result: `fastBoolGet_eq : VP8.fastBoolGet = Spec.VP8.boolGet` (equality of functions on
*all* decoder states and probabilities).

The key lemma `normalize_eq_shiftBy`: if exactly `k` doublings bring the range into
`[128, 256)` and `bit_count < 8`, then the reference loop (`normalize`) computes the closed form
`shiftBy d k`. It is proved by induction on `k`, peeling off one iteration of the loop
(`shiftOnce`) and using that shifts compose (`shl_shl`) and distribute over `|||`.
-/
namespace WebP.Proofs.VP8Bool

open WebP.Spec.VP8 WebP.VP8

/-- Shifts compose (no shift amount reaches 32). -/
theorem shl_shl (x : UInt32) (a b : Nat) (h : a + b < 32) :
    (x <<< a.toUInt32) <<< b.toUInt32 = x <<< (a + b).toUInt32 := by
  apply UInt32.toNat_inj.mp
  have ha : a.toUInt32.toNat = a := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have hb : b.toUInt32.toNat = b := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have hab : (a + b).toUInt32.toNat = a + b := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  simp only [UInt32.toNat_shiftLeft, ha, hb, hab, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : a < 32), Nat.mod_eq_of_lt (by omega : b < 32),
    Nat.mod_eq_of_lt (by omega : a + b < 32), Nat.mod_mul_mod, Nat.pow_add, Nat.mul_assoc]

theorem one_toUInt32 : (1 : Nat).toUInt32 = (1 : UInt32) := rfl

theorem zero_toUInt32 : (0 : Nat).toUInt32 = (0 : UInt32) := rfl

/-- Shifting by one doubles a value below `2³¹`. -/
theorem toNat_shl_one (x : UInt32) (h : x.toNat < 2 ^ 31) : (x <<< 1).toNat = x.toNat * 2 := by
  rw [UInt32.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  have : (1 : UInt32).toNat % 32 = 1 := rfl
  rw [this, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]

/-- `shiftBy d 0 = d` (when `bit_count < 8`). -/
theorem shiftBy_zero (d : BoolDecoder) (hbc : d.bitCount < 8) : shiftBy d 0 = d := by
  rcases d with ⟨input, pos, len, range, value, bc⟩
  simp only at hbc
  have : ¬ bc ≥ 8 := by omega
  simp only [shiftBy, Nat.add_zero, this, ite_false, zero_toUInt32, UInt32.shiftLeft_zero]

theorem shiftOnce_range (d : BoolDecoder) : (shiftOnce d).range = d.range <<< 1 := by
  rcases d with ⟨input, pos, len, range, value, bc⟩
  simp only [shiftOnce]
  split <;> (try split) <;> rfl

theorem shiftOnce_bitCount (d : BoolDecoder) (h : d.bitCount < 8) : (shiftOnce d).bitCount < 8 := by
  rcases d with ⟨input, pos, len, range, value, bc⟩
  simp only at h
  simp only [shiftOnce]
  split
  · split <;> simp
  · rename_i h'; simp only at h' ⊢; omega

/-- One loop iteration followed by `k` shifts at once is `k + 1` shifts at once. -/
theorem shiftBy_shiftOnce (d : BoolDecoder) (k : Nat) (hk : k + 1 ≤ 7) (hbc : d.bitCount < 8) :
    shiftBy (shiftOnce d) k = shiftBy d (k + 1) := by
  rcases d with ⟨input, pos, len, range, value, bc⟩
  simp only at hbc
  by_cases h7 : bc + 1 = 8
  · -- the iteration shifts in a byte (if any is left)
    have hbc7 : bc = 7 := by omega
    subst hbc7
    by_cases hl : len ≠ 0
    · simp only [shiftOnce, shiftBy, hl, ite_true, Nat.reduceAdd, ne_eq, not_false_eq_true]
      have h1 : ¬ 0 + k ≥ 8 := by omega
      have h2 : 7 + (k + 1) ≥ 8 := by omega
      simp only [h1, h2, ite_false, ite_true, BoolDecoder.mk.injEq, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← one_toUInt32, shl_shl _ _ _ (by omega), Nat.add_comm 1 k]
      · rw [UInt32.shiftLeft_or, ← one_toUInt32, shl_shl _ _ _ (by omega), Nat.add_comm 1 k,
          show 7 + (k + 1) - 8 = k by omega]
      · omega
    · have hl0 : len = 0 := by omega
      subst hl0
      simp only [shiftOnce, shiftBy, ite_true, ne_eq, not_true_eq_false, ite_false,
        Nat.reduceAdd]
      have h1 : ¬ 0 + k ≥ 8 := by omega
      have h2 : 7 + (k + 1) ≥ 8 := by omega
      simp only [h1, h2, ite_false, ite_true, BoolDecoder.mk.injEq, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← one_toUInt32, shl_shl _ _ _ (by omega), Nat.add_comm 1 k]
      · rw [← one_toUInt32, shl_shl _ _ _ (by omega), Nat.add_comm 1 k]
      · omega
  · -- no byte boundary in this iteration
    simp only [shiftOnce, shiftBy, h7, ite_false]
    rw [show bc + 1 + k = bc + (k + 1) by omega, ← one_toUInt32,
      shl_shl range 1 k (by omega), shl_shl value 1 k (by omega), Nat.add_comm 1 k]

/-- **The reference normalization loop is a single shift by `k`**, if exactly `k` doublings
bring the range into `[128, 256)`. -/
theorem normalize_eq_shiftBy : ∀ (k n : Nat) (d : BoolDecoder), k ≤ 7 → k ≤ n →
    d.bitCount < 8 → 128 ≤ d.range.toNat * 2 ^ k → d.range.toNat * 2 ^ k < 256 →
    (k = 0 ∨ d.range.toNat * 2 ^ (k - 1) < 128) →
    normalize n d = shiftBy d k := by
  intro k
  induction k with
  | zero =>
    intro n d _ _ hbc hlo _ _
    rw [shiftBy_zero d hbc]
    have hr : ¬ d.range < 128 := by
      rw [UInt32.lt_iff_toNat_lt]; simp only [Nat.pow_zero, Nat.mul_one] at hlo
      exact Nat.not_lt.mpr (by simpa using hlo)
    cases n with
    | zero => rfl
    | succ n => simp only [normalize, hr, ite_false]
  | succ k ih =>
    intro n d hk hn hbc hlo hhi hexact
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hexact' : d.range.toNat * 2 ^ k < 128 := by
      rcases hexact with h | h
      · omega
      · simpa using h
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hr128 : d.range.toNat < 128 := by
      have : d.range.toNat ≤ d.range.toNat * 2 ^ k := Nat.le_mul_of_pos_right _ hpos
      omega
    have hr : d.range < 128 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hr128
    simp only [normalize, hr, ite_true]
    -- the state after one iteration
    have hrange : (shiftOnce d).range.toNat = d.range.toNat * 2 := by
      rw [shiftOnce_range, toNat_shl_one _ (by omega)]
    have hbc' : (shiftOnce d).bitCount < 8 := shiftOnce_bitCount d hbc
    rw [ih n (shiftOnce d) (by omega) (by omega) hbc'
      (by rw [hrange, Nat.mul_assoc, ← Nat.pow_succ']; exact hlo)
      (by rw [hrange, Nat.mul_assoc, ← Nat.pow_succ']; exact hhi)
      (by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exact Or.inl h0
        · right
          rw [hrange, Nat.mul_assoc, ← Nat.pow_succ', Nat.succ_eq_add_one,
            show k - 1 + 1 = k by omega]
          exact hexact')]
    exact shiftBy_shiftOnce d k (by omega) hbc

/-- `normShift r` is exactly the number of doublings needed, for `1 ≤ r < 128`. -/
theorem normShift_spec : ∀ r < 128, 0 < r →
    normShift r ≤ 7 ∧ 128 ≤ r * 2 ^ normShift r ∧ r * 2 ^ normShift r < 256 ∧
    (normShift r = 0 ∨ r * 2 ^ (normShift r - 1) < 128) := by
  decide

/-- `renorm` is the reference normalization loop. -/
theorem renorm_eq (d : BoolDecoder) (range value : UInt32) :
    renorm d range value = normalize 8 { d with range, value } := by
  unfold renorm
  split
  · rename_i h
    have h' := UInt32.le_iff_toNat_le.mp (show (128 : UInt32) ≤ range from h)
    have hr : ¬ range < 128 := by
      rw [UInt32.lt_iff_toNat_lt]
      exact Nat.not_lt.mpr (by simpa using h')
    simp only [normalize, hr, ite_false]
  · rename_i hge
    split
    · rename_i h
      obtain ⟨hne, hbc⟩ := h
      have hlt : range.toNat < 128 := by
        have : ¬ (128 : UInt32) ≤ range := hge
        rw [UInt32.le_iff_toNat_le] at this; simp at this; omega
      have hpos : 0 < range.toNat := by
        rcases Nat.eq_zero_or_pos range.toNat with h0 | h0
        · exact absurd (UInt32.toNat_inj.mp (by simpa using h0)) hne
        · exact h0
      obtain ⟨h1, h2, h3, h4⟩ := normShift_spec range.toNat hlt hpos
      exact (normalize_eq_shiftBy (normShift range.toNat) 8 { d with range, value } h1
        (by omega) hbc h2 h3 h4).symm
    · rfl

/-- **The one-shift boolean decoder is the reference `bool_get`.** -/
theorem fastBoolGet_eq : fastBoolGet = boolGet := by
  funext d p
  simp only [fastBoolGet, boolGet, renorm_eq]

/-- The optimized primitives are the reference primitives. -/
theorem fastPrims_eq : fastPrims = specPrims := by
  unfold fastPrims specPrims
  rw [fastBoolGet_eq]

end WebP.Proofs.VP8Bool
