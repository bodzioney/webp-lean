import WebP.VP8L.Fast
/-!
# The word-at-a-time bit reader equals `ReadBits`

Main results:
* `bit_le4`: bit `j` of the 32-bit little-endian word at byte `pos / 8`, shifted by `pos % 8`,
  is stream bit `pos + j` (for `pos % 8 + j < 32`).
* `fastReadBits_eq`: `VP8L.fastReadBits = Spec.readBits`.
-/
namespace WebP.Proofs

open WebP.Spec

/-- Splitting off the lowest bit of a truncated value. -/
theorem mod_two_pow_succ (y n : Nat) : y % 2 ^ (n + 1) = y % 2 + 2 * (y / 2 % 2 ^ n) := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]

/-- If stream bits `pos, pos+1, ...` are bits `s, s+1, ...` of `x`, then `ReadBits(n)` is the
corresponding bit field of `x`. -/
theorem readBitsVal_eq_field (d : ByteArray) (x : Nat) :
    ∀ n pos s, (∀ j < n, bit d (pos + j) = x / 2 ^ (s + j) % 2) →
      readBitsVal d pos n = x / 2 ^ s % 2 ^ n := by
  intro n
  induction n with
  | zero => intro pos s _; simp [readBitsVal, Nat.mod_one]
  | succ n ih =>
    intro pos s h
    have h0 := h 0 (by omega)
    have ih' := ih (pos + 1) (s + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rw [show pos + 1 + j = pos + (j + 1) by omega, show s + 1 + j = s + (j + 1) by omega]
      exact this)
    simp only [readBitsVal, Nat.add_zero] at h0 ⊢
    rw [ih', h0, mod_two_pow_succ, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- Bits of a little-endian multi-byte integer. -/
theorem le_bit (d : ByteArray) :
    ∀ m k t, t < 8 * m → le d k m / 2 ^ t % 2 = byte d (k + t / 8) / 2 ^ (t % 8) % 2 := by
  intro m
  induction m with
  | zero => intro k t ht; omega
  | succ m ih =>
    intro k t ht
    simp only [le]
    have hb : byte d k < 256 := by
      unfold byte; split
      · exact UInt8.toNat_lt _
      · omega
    by_cases h8 : t < 8
    · -- low byte
      have h256 : (256 : Nat) = 2 ^ t * 2 ^ (8 - t) := by
        have : t + (8 - t) = 8 := by omega
        rw [← Nat.pow_add, this]
      have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
      rw [h256, Nat.mul_assoc, Nat.add_mul_div_left _ _ hpos]
      have : 2 ^ (8 - t) = 2 * 2 ^ (8 - t - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [this, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · -- higher bytes
      have ht' : t - 8 < 8 * m := by omega
      have e1 : 2 ^ t = 256 * 2 ^ (t - 8) := by
        rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_add]; congr 1; omega
      have e2 : (byte d k + 256 * le d (k + 1) m) / 256 = le d (k + 1) m := by
        rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]
      rw [e1, ← Nat.div_div_eq_div_mul, e2, ih (k + 1) (t - 8) ht']
      congr 3 <;> omega

/-- Bit `j` of the shifted 32-bit window is stream bit `pos + j`. -/
theorem bit_le4 (d : ByteArray) (pos j : Nat) (hj : pos % 8 + j < 32) :
    le d (pos / 8) 4 / 2 ^ (pos % 8 + j) % 2 = bit d (pos + j) := by
  rw [le_bit d 4 _ _ (by omega)]
  unfold bit
  congr 3 <;> omega

/-- The window extraction used by the fast reader is `ReadBits`. -/
theorem window_eq_readBitsVal (d : ByteArray) (pos n : Nat) (hn : n ≤ 25) :
    (le d (pos / 8) 4 >>> (pos % 8)) % 2 ^ n = readBitsVal d pos n := by
  rw [Nat.shiftRight_eq_div_pow]
  symm
  apply readBitsVal_eq_field
  intro j hj
  rw [bit_le4 d pos j (by omega)]

/-- Truncating above bit `j` does not change bit `j`. -/
theorem mod_pow_div_pow_mod_two (y tb j : Nat) (hj : j < tb) :
    y % 2 ^ tb / 2 ^ j % 2 = y / 2 ^ j % 2 := by
  conv => rhs; rw [← Nat.mod_add_div y (2 ^ tb)]
  have e : 2 ^ tb = 2 ^ j * (2 * 2 ^ (tb - j - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

/-- Bit `j` of the `tb`-bit peeked window (as used by `Table.decode`) is stream bit `pos + j`. -/
theorem peek_bit (d : ByteArray) (pos tb j : Nat) (htb : tb ≤ 25) (hj : j < tb) :
    (le d (pos / 8) 4 >>> (pos % 8)) % 2 ^ tb / 2 ^ j % 2 = bit d (pos + j) := by
  rw [Nat.shiftRight_eq_div_pow, mod_pow_div_pow_mod_two _ _ _ hj, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, bit_le4 d pos j (by omega)]

/-- **The optimized bit reader is `ReadBits`.** -/
theorem fastReadBits_eq : VP8L.fastReadBits = Spec.readBits := by
  funext d pos n
  unfold VP8L.fastReadBits Spec.readBits
  split
  · split
    · rw [window_eq_readBitsVal d pos n (by omega)]
    · rfl
  · rfl

end WebP.Proofs
