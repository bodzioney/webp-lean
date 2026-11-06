import WebP.Alpha
/-!
# In-place alpha unfiltering equals the declarative definition

`unfilter_eq : WebP.Alpha.unfilter = Spec.Alpha.unfilter`: the one-pass in-place
reconstruction computes exactly the pixel-wise equations of RFC 9649 §2.7.1.2.
-/
namespace WebP.Proofs

open WebP.Spec WebP.Spec.Alpha

theorem byte_mk (a : Array UInt8) (j : Nat) : byte ⟨a⟩ j = (a.getD j 0).toNat := by
  unfold byte
  simp only [ByteArray.size]
  split
  · rename_i h; simp; rfl
  · rename_i h; simp

theorem byte_lt (d : ByteArray) (j : Nat) : byte d j < 256 := by
  unfold byte; split
  · exact UInt8.toNat_lt _
  · omega

/-- The predictor only looks at pixels before `i`. -/
theorem predictor_congr (m w i : Nat) (g1 g2 : Nat → Nat) (h : ∀ j < i, g1 j = g2 j) :
    predictor m w g1 i = predictor m w g2 i := by
  have e1 : i % w ≠ 0 → g1 (i - 1) = g2 (i - 1) := by
    intro hx; apply h
    have : i ≠ 0 := by intro h0; simp [h0] at hx
    omega
  have hwi : i / w ≠ 0 → 0 < w ∧ w ≤ i := by
    intro hy
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · simp [h0] at hy
    · refine ⟨h0, ?_⟩
      rcases Nat.lt_or_ge i w with hlt | hge
      · simp [Nat.div_eq_of_lt hlt] at hy
      · exact hge
  have e2 : i / w ≠ 0 → g1 (i - w) = g2 (i - w) := by
    intro hy; have := hwi hy; apply h; omega
  have e3 : i / w ≠ 0 → g1 (i - w - 1) = g2 (i - w - 1) := by
    intro hy; have := hwi hy; apply h; omega
  unfold predictor
  dsimp only
  by_cases hx0 : i % w = 0 <;> by_cases hy0 : i / w = 0
  · simp [hx0, hy0]
  · simp [hx0, hy0, e2 hy0]
  · simp [hx0, hy0, e1 hx0]
  · simp [hx0, hy0, e1 hx0, e2 hy0, e3 hy0]

theorem value_eq (m w : Nat) (raw : ByteArray) (i : Nat) :
    value m w raw i =
      (predictor m w (fun j => if j < i then value m w raw j else 0) i + byte raw i) % 256 := by
  rw [value]

theorem byte_set (out : ByteArray) (i j : Nat) (x : UInt8) (hi : i < out.size) :
    byte (out.set! i x) j = if j = i then x.toNat else byte out j := by
  obtain ⟨a⟩ := out
  simp only [ByteArray.set!, byte_mk, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  have hi' : i < a.size := hi
  by_cases hji : j = i
  · subst hji; simp [hi']
  · simp [Ne.symm hji, hji]

theorem size_set (out : ByteArray) (i : Nat) (x : UInt8) : (out.set! i x).size = out.size := by
  obtain ⟨a⟩ := out
  simp [ByteArray.set!, ByteArray.size]

/-- Loop invariant: after processing pixels `< i`, they hold their reconstructed values. -/
theorem unfilterLoop_spec (m w : Nat) (raw : ByteArray) :
    ∀ n i (out : ByteArray), out.size = i + n →
      (∀ j < i, byte out j = value m w raw j) →
      (WebP.Alpha.unfilterLoop m w raw n i out).size = i + n ∧
      ∀ j < i + n, byte (WebP.Alpha.unfilterLoop m w raw n i out) j = value m w raw j := by
  intro n
  induction n with
  | zero =>
    intro i out hs hdone
    simp only [WebP.Alpha.unfilterLoop, Nat.add_zero]
    exact ⟨by omega, hdone⟩
  | succ n ih =>
    intro i out hs hdone
    simp only [WebP.Alpha.unfilterLoop]
    have hv : (predictor m w (fun j => byte out j) i + byte raw i) % 256 = value m w raw i := by
      rw [value_eq]
      congr 2
      apply predictor_congr
      intro j hj; simp [hj, hdone j hj]
    have hvlt : value m w raw i < 256 := by rw [← hv]; exact Nat.mod_lt _ (by decide)
    rw [hv]
    have hi : i < out.size := by omega
    have key := ih (i + 1) (out.set! i (value m w raw i).toUInt8)
      (by rw [size_set]; omega)
      (by
        intro j hj
        rw [byte_set _ _ _ _ hi]
        by_cases hji : j = i
        · subst hji; simp [Nat.mod_eq_of_lt hvlt]
        · simp [hji]; exact hdone j (by omega))
    exact ⟨by have := key.1; omega, fun j hj => key.2 j (by omega)⟩

/-- **In-place alpha unfiltering computes the declarative alpha plane.** -/
theorem unfilter_eq : WebP.Alpha.unfilter = Spec.Alpha.unfilter := by
  funext m w h raw
  unfold WebP.Alpha.unfilter Spec.Alpha.unfilter
  have := unfilterLoop_spec m w raw (w * h) 0
    ⟨Array.ofFn (n := w * h) fun i => (byte raw i.val).toUInt8⟩ (by simp [ByteArray.size])
    (fun j hj => by omega)
  simp only [Nat.zero_add] at this
  obtain ⟨hs, hv⟩ := this
  generalize WebP.Alpha.unfilterLoop m w raw (w * h) 0 _ = r at hs hv ⊢
  obtain ⟨a⟩ := r
  apply ByteArray.ext
  apply Array.ext
  · simpa [ByteArray.size] using hs
  · intro j h1 h2
    have := hv j (by simpa using h2)
    rw [byte_mk] at this
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
      at this
    simp only [Array.getElem_ofFn]
    rw [← this]; simp

end WebP.Proofs
