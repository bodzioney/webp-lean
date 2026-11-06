import WebP.Proofs.Bits
/-!
# Table-driven canonical prefix decoding equals the specification

Main result: `fastBuild_eq : VP8L.fastBuild = Spec.Prefix.build`.

Structure of the proof:
* `puff_eq_find`: the bit-by-bit canonical decoder `puff` on the data stream returns exactly the
  unique symbol whose canonical codeword matches the stream (`Spec.Prefix.matchesAt`), i.e. the
  result of the specification's `find?` (no Kraft inequality is needed: canonical codes are
  always prefix-free, `matches_unique`).
* `puff_local`: `puff` only depends on the bits it consumes; the lookup table is `puff` run on
  every `tableBits`-bit pattern, and the peeked window agrees with the stream (`peek_bit`), so
  a table hit equals `puff` on the stream (`decode_eq_puff`).
-/
namespace WebP.Proofs

open WebP.Spec WebP.VP8L

/-! ## Filters of `List.range` -/

section FilterRange
variable (p : Nat → Bool)

theorem fr_succ (n : Nat) :
    (List.range (n + 1)).filter p = (List.range n).filter p ++ (if p n then [n] else []) := by
  rw [List.range_succ, List.filter_append]; cases h : p n <;> simp [h]

theorem fr_len_mono {m n : Nat} (h : m ≤ n) :
    ((List.range m).filter p).length ≤ ((List.range n).filter p).length := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; simp
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · have := ih (by omega)
      rw [fr_succ]; simp only [List.length_append]; omega
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

theorem fr_len_lt {s n : Nat} (hs : s < n) (hp : p s = true) :
    ((List.range s).filter p).length < ((List.range n).filter p).length := by
  have h1 := fr_len_mono p (show s + 1 ≤ n by omega)
  rw [fr_succ] at h1; simp [hp] at h1; omega

theorem fr_getElem_rank {s n : Nat} (hs : s < n) (hp : p s = true) :
    ((List.range n).filter p)[((List.range s).filter p).length]? = some s := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [fr_succ]
    rcases Nat.lt_or_ge s n with h | h
    · rw [List.getElem?_append_left (fr_len_lt p h hp)]; exact ih h
    · have : s = n := by omega
      subst this; simp [hp]

theorem fr_rank_of_getElem {n k s : Nat} (h : ((List.range n).filter p)[k]? = some s) :
    p s = true ∧ s < n ∧ ((List.range s).filter p).length = k := by
  induction n generalizing k with
  | zero => simp at h
  | succ n ih =>
    rw [fr_succ] at h
    by_cases hk : k < ((List.range n).filter p).length
    · rw [List.getElem?_append_left hk] at h
      obtain ⟨a, b, c⟩ := ih h; exact ⟨a, by omega, c⟩
    · rw [List.getElem?_append_right (by omega)] at h
      by_cases hpn : p n = true
      · rw [ite_eq_left hpn] at h
        rw [List.getElem?_singleton] at h
        split at h
        · cases h; exact ⟨hpn, by omega, by omega⟩
        · cases h
      · rw [ite_eq_right hpn] at h; simp at h

end FilterRange

/-! ## Symbol counts and ranks -/

/-- Number of symbols `< s` with code length `l`. -/
def rank (lens : Array Nat) (l s : Nat) : Nat :=
  ((List.range s).filter (fun t => lens.getD t 0 == l)).length

theorem getD_eq (lens : Array Nat) (s : Nat) (hs : s < lens.size) : lens.getD s 0 = lens[s] := by
  simp [Array.getD_eq_getD_getElem?, hs]

theorem lt_of_getD_ne (lens : Array Nat) (s : Nat) (h : lens.getD s 0 ≠ 0) : s < lens.size := by
  rcases Nat.lt_or_ge s lens.size with h' | h'
  · exact h'
  · exfalso; apply h; simp [Array.getD_eq_getD_getElem?, h']

theorem count_take_eq (lens : Array Nat) (l : Nat) :
    ∀ s, s ≤ lens.size → (lens.toList.take s).count l = rank lens l s := by
  intro s
  induction s with
  | zero => intro _; simp [rank]
  | succ s ih =>
    intro hs
    unfold rank at ih ⊢
    rw [List.take_add_one, List.count_append, ih (by omega), fr_succ, List.length_append]
    have h1 : lens.toList[s]? = some lens[s] := by simp
    rw [h1, getD_eq lens s (by omega)]
    cases h : lens[s] == l <;> simp [h, List.count_cons]

theorem count_eq_rank (lens : Array Nat) (l : Nat) : Prefix.count lens l = rank lens l lens.size := by
  unfold Prefix.count
  rw [← count_take_eq lens l lens.size (Nat.le_refl _), List.take_of_length_le (by simp)]

theorem codeword_eq (lens : Array Nat) (s : Nat) (hs : s < lens.size) :
    Prefix.codeword lens s = Prefix.firstCode lens (lens.getD s 0) + rank lens (lens.getD s 0) s := by
  unfold Prefix.codeword
  simp only
  rw [count_take_eq lens _ s (by omega)]

/-! ## Stream prefixes and first codewords -/

theorem bit_lt_two (d : ByteArray) (i : Nat) : bit d i < 2 := Nat.mod_lt _ (by decide)

theorem bitsMSB_succ (d : ByteArray) (pos n : Nat) :
    Prefix.bitsMSB d pos (n + 1) = Prefix.bitsMSB d pos n * 2 + bit d (pos + n) := rfl

theorem bitsMSB_prefix (d : ByteArray) (pos l : Nat) :
    ∀ k, Prefix.bitsMSB d pos (l + k) / 2 ^ k = Prefix.bitsMSB d pos l
  | 0 => by simp
  | k + 1 => by
    rw [show l + (k + 1) = (l + k) + 1 by omega, bitsMSB_succ, Nat.pow_succ,
      Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
    have hb := bit_lt_two d (pos + (l + k))
    rw [show (Prefix.bitsMSB d pos (l + k) * 2 + bit d (pos + (l + k))) / 2 =
      Prefix.bitsMSB d pos (l + k) by omega]
    exact bitsMSB_prefix d pos l k

theorem firstCode_succ (lens : Array Nat) (l : Nat) (hl : 1 ≤ l) :
    Prefix.firstCode lens (l + 1) = (Prefix.firstCode lens l + Prefix.count lens l) * 2 := by
  rw [Prefix.firstCode, ite_eq_right (by omega)]

theorem firstCode_double (lens : Array Nat) (m : Nat) :
    Prefix.firstCode lens m * 2 ≤ Prefix.firstCode lens (m + 1) := by
  rw [Prefix.firstCode]; exact Nat.mul_le_mul_right 2 (Nat.le_add_right _ _)

theorem firstCode_ge (lens : Array Nat) (l1 : Nat) (h1 : 1 ≤ l1) :
    ∀ k, (Prefix.firstCode lens l1 + Prefix.count lens l1) * 2 ^ (k + 1) ≤
      Prefix.firstCode lens (l1 + 1 + k)
  | 0 => by rw [firstCode_succ lens l1 h1]; simp
  | k + 1 => by
    have ih := firstCode_ge lens l1 h1 k
    have hd := firstCode_double lens (l1 + 1 + k)
    rw [show l1 + 1 + (k + 1) = l1 + 1 + k + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_right 2 ih) hd

/-! ## Canonical codes are prefix-free -/

theorem matches_iff (d : ByteArray) (lens : Array Nat) (pos s : Nat) :
    Prefix.matchesAt d lens pos s = true ↔
      lens.getD s 0 ≠ 0 ∧ pos + lens.getD s 0 ≤ 8 * d.size ∧
      Prefix.bitsMSB d pos (lens.getD s 0) = Prefix.codeword lens s := by
  simp [Prefix.matchesAt, and_assoc]

theorem rank_lt_count (lens : Array Nat) (s : Nat) (hs : s < lens.size) :
    rank lens (lens.getD s 0) s < Prefix.count lens (lens.getD s 0) := by
  rw [count_eq_rank]; exact fr_len_lt _ hs (by simp)

theorem rank_strict (lens : Array Nat) (l s1 s2 : Nat) (h : s1 < s2) (h1 : lens.getD s1 0 = l) :
    rank lens l s1 < rank lens l s2 := fr_len_lt _ h (by simp [h1])

theorem no_match_longer (d : ByteArray) (lens : Array Nat) (pos s1 s2 : Nat)
    (h1 : Prefix.matchesAt d lens pos s1 = true) (h2 : Prefix.matchesAt d lens pos s2 = true)
    (hlt : lens.getD s1 0 < lens.getD s2 0) : False := by
  rw [matches_iff] at h1 h2
  obtain ⟨a1, -, c1⟩ := h1
  obtain ⟨-, -, c2⟩ := h2
  have hs1 := lt_of_getD_ne lens s1 a1
  have hs2 := lt_of_getD_ne lens s2 (by omega)
  rw [codeword_eq lens s1 hs1] at c1
  rw [codeword_eq lens s2 hs2] at c2
  have hr := rank_lt_count lens s1 hs1
  generalize lens.getD s1 0 = l1 at *
  generalize lens.getD s2 0 = l2 at *
  have hge := firstCode_ge lens l1 (by omega) (l2 - l1 - 1)
  rw [show l1 + 1 + (l2 - l1 - 1) = l2 by omega, show l2 - l1 - 1 + 1 = l2 - l1 by omega] at hge
  have hpre := bitsMSB_prefix d pos l1 (l2 - l1)
  rw [show l1 + (l2 - l1) = l2 by omega, c2, c1] at hpre
  have hp : 0 < 2 ^ (l2 - l1) := Nat.two_pow_pos _
  have : Prefix.firstCode lens l1 + Prefix.count lens l1 ≤
      (Prefix.firstCode lens l2 + rank lens l2 s2) / 2 ^ (l2 - l1) := by
    rw [Nat.le_div_iff_mul_le hp]; omega
  omega

theorem matches_unique (d : ByteArray) (lens : Array Nat) (pos s1 s2 : Nat)
    (h1 : Prefix.matchesAt d lens pos s1 = true) (h2 : Prefix.matchesAt d lens pos s2 = true) :
    s1 = s2 := by
  rcases Nat.lt_trichotomy (lens.getD s1 0) (lens.getD s2 0) with hl | hl | hl
  · exact (no_match_longer d lens pos s1 s2 h1 h2 hl).elim
  · have h1' := h1; have h2' := h2
    rw [matches_iff] at h1' h2'
    have hs1 := lt_of_getD_ne lens s1 h1'.1
    have hs2 := lt_of_getD_ne lens s2 h2'.1
    have e1 := h1'.2.2; have e2 := h2'.2.2
    rw [codeword_eq lens s1 hs1] at e1
    rw [codeword_eq lens s2 hs2] at e2
    rw [hl] at e1
    rcases Nat.lt_trichotomy s1 s2 with h | h | h
    · have := rank_strict lens _ s1 s2 h hl; omega
    · exact h
    · have := rank_strict lens _ s2 s1 h rfl; omega
  · exact (no_match_longer d lens pos s2 s1 h2 h1 hl).elim

/-! ## `puff` -/

theorem go_props (src : Nat → Option Nat) (byLen : Array (Array Nat)) :
    ∀ k len code first s l, 16 - len ≤ k → puff.go src byLen len code first = some (s, l) →
      len ≤ l ∧ l ≤ 15 ∧ ∃ b, src (l - 1) = some b := by
  intro k
  induction k with
  | zero =>
    intro len code first s l hk h
    rw [puff.go, ite_eq_right (by omega)] at h; cases h
  | succ k ih =>
    intro len code first s l hk h
    rw [puff.go] at h
    split at h
    · cases hb : src (len - 1) with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h
        split at h
        · cases h; exact ⟨Nat.le_refl _, by omega, b, hb⟩
        · have := ih _ _ _ _ _ (by omega) h; exact ⟨by omega, this.2⟩
    · cases h

theorem go_local (byLen : Array (Array Nat)) (src1 src2 : Nat → Option Nat) :
    ∀ k len code first s l, 16 - len ≤ k → 1 ≤ len →
      puff.go src1 byLen len code first = some (s, l) → (∀ j < l, src1 j = src2 j) →
      puff.go src2 byLen len code first = some (s, l) := by
  intro k
  induction k with
  | zero =>
    intro len code first s l hk _ h
    rw [puff.go, ite_eq_right (by omega)] at h; cases h
  | succ k ih =>
    intro len code first s l hk h1 h hag
    have hp := go_props src1 byLen _ _ _ _ _ _ (Nat.le_refl _) h
    rw [puff.go] at h ⊢
    split at h
    · rename_i h15
      rw [ite_eq_left h15, ← hag (len - 1) (by omega)]
      cases hb : src1 (len - 1) with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h ⊢
        split at h
        · rename_i hlt; rw [ite_eq_left hlt]; exact h
        · rename_i hlt; rw [ite_eq_right hlt]; exact ih _ _ _ _ _ (by omega) (by omega) h hag
    · cases h

theorem puff_local (byLen : Array (Array Nat)) (src1 src2 : Nat → Option Nat) (s l : Nat)
    (h : puff src1 byLen = some (s, l)) (hag : ∀ j < l, src1 j = src2 j) :
    puff src2 byLen = some (s, l) :=
  go_local byLen src1 src2 16 1 0 0 s l (by omega) (Nat.le_refl _) h hag

theorem puff_props (src : Nat → Option Nat) (byLen : Array (Array Nat)) (s l : Nat)
    (h : puff src byLen = some (s, l)) : 1 ≤ l ∧ l ≤ 15 ∧ ∃ b, src (l - 1) = some b :=
  go_props src byLen 16 1 0 0 s l (by omega) h

theorem symbolsByLen_getD (lens : Array Nat) (l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ 15) :
    (symbolsByLen lens).getD l #[] =
      ((List.range lens.size).filter (fun s => lens.getD s 0 == l)).toArray := by
  simp [symbolsByLen, Array.getD_eq_getD_getElem?, show l < 16 by omega, show l ≠ 0 by omega]

/-- The stream source, described by its values. -/
def IsDataSrc (d : ByteArray) (pos : Nat) (src : Nat → Option Nat) : Prop :=
  ∀ j, src j = if pos + j < 8 * d.size then some (bit d (pos + j)) else none

/-- The by-length symbol lists, described by their values. -/
def IsByLen (lens : Array Nat) (byLen : Array (Array Nat)) : Prop :=
  ∀ l, 1 ≤ l → l ≤ 15 →
    byLen.getD l #[] = ((List.range lens.size).filter (fun s => lens.getD s 0 == l)).toArray

theorem go_sound (d : ByteArray) (lens : Array Nat) (pos : Nat) (src : Nat → Option Nat)
    (byLen : Array (Array Nat)) (hsrc : IsDataSrc d pos src) (hby : IsByLen lens byLen) :
    ∀ k len code first s l, 16 - len ≤ k → 1 ≤ len →
      code = 2 * Prefix.bitsMSB d pos (len - 1) → first = Prefix.firstCode lens len →
      first ≤ code →
      puff.go src byLen len code first = some (s, l) →
      Prefix.matchesAt d lens pos s = true ∧ lens.getD s 0 = l := by
  intro k
  induction k with
  | zero =>
    intro len code first s l hk _ _ _ _ h
    rw [puff.go, ite_eq_right (by omega)] at h; cases h
  | succ k ih =>
    intro len code first s l hk h1 hc hf hfc h
    rw [puff.go] at h
    split at h
    · rename_i h15
      by_cases hin : pos + (len - 1) < 8 * d.size
      · have hs : src (len - 1) = some (bit d (pos + (len - 1))) := by rw [hsrc, ite_eq_left hin]
        simp only [hs] at h
        rw [hby len h1 h15] at h
        have hB : Prefix.bitsMSB d pos len =
            Prefix.bitsMSB d pos (len - 1) * 2 + bit d (pos + (len - 1)) := by
          rw [← bitsMSB_succ]; congr 1; omega
        have hsz : ((List.range lens.size).filter (fun s => lens.getD s 0 == len)).length =
            Prefix.count lens len := by rw [count_eq_rank]; rfl
        simp only [List.size_toArray] at h
        split at h
        · rename_i hlt
          cases h
          generalize hk' : code + bit d (pos + (len - 1)) - first = kk at *
          have hkl : kk < ((List.range lens.size).filter (fun s => lens.getD s 0 == len)).length := by
            omega
          obtain ⟨s0, hs0⟩ : ∃ s0, ((List.range lens.size).filter
              (fun s => lens.getD s 0 == len))[kk]? = some s0 :=
            ⟨_, List.getElem?_eq_getElem hkl⟩
          have hget : ((List.range lens.size).filter
              (fun s => lens.getD s 0 == len)).toArray.getD kk 0 = s0 := by
            rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, hs0]; rfl
          rw [hget]
          obtain ⟨hp, hlt0, hr⟩ := fr_rank_of_getElem _ hs0
          have hL : lens.getD s0 0 = len := by simpa using hp
          refine ⟨?_, hL⟩
          rw [matches_iff, hL, codeword_eq lens s0 hlt0, hL]
          refine ⟨by omega, by omega, ?_⟩
          unfold rank; rw [hr, hB]; omega
        · rename_i hge
          refine ih (len + 1) _ _ s l (by omega) (by omega) ?_ ?_ ?_ h
          · rw [show len + 1 - 1 = len by omega, hB]; omega
          · rw [firstCode_succ lens len h1, hsz, hf]
          · omega
      · have hs : src (len - 1) = none := by rw [hsrc, ite_eq_right hin]
        simp [hs] at h
    · cases h

theorem go_complete (d : ByteArray) (lens : Array Nat) (pos : Nat) (src : Nat → Option Nat)
    (byLen : Array (Array Nat)) (hsrc : IsDataSrc d pos src) (hby : IsByLen lens byLen)
    (s : Nat) (hm : Prefix.matchesAt d lens pos s = true) (h15 : lens.getD s 0 ≤ 15) :
    ∀ k len code first, 16 - len ≤ k → 1 ≤ len → len ≤ lens.getD s 0 →
      code = 2 * Prefix.bitsMSB d pos (len - 1) → first = Prefix.firstCode lens len →
      first ≤ code → (puff.go src byLen len code first).isSome = true := by
  have hm' := (matches_iff d lens pos s).mp hm
  have hs := lt_of_getD_ne lens s hm'.1
  intro k
  induction k with
  | zero => intro len code first hk _ hl; omega
  | succ k ih =>
    intro len code first hk h1 hl hc hf hfc
    rw [puff.go, ite_eq_left (by omega)]
    have hin : pos + (len - 1) < 8 * d.size := by omega
    have hsrc' : src (len - 1) = some (bit d (pos + (len - 1))) := by rw [hsrc, ite_eq_left hin]
    simp only [hsrc']
    rw [hby len h1 (by omega)]
    simp only [List.size_toArray]
    have hB : Prefix.bitsMSB d pos len =
        Prefix.bitsMSB d pos (len - 1) * 2 + bit d (pos + (len - 1)) := by
      rw [← bitsMSB_succ]; congr 1; omega
    have hsz : ((List.range lens.size).filter (fun s => lens.getD s 0 == len)).length =
        Prefix.count lens len := by rw [count_eq_rank]; rfl
    split
    · rfl
    · rename_i hge
      by_cases heq : len = lens.getD s 0
      · exfalso
        have e := hm'.2.2
        rw [codeword_eq lens s hs, ← heq] at e
        have hr := rank_lt_count lens s hs
        rw [← heq] at hr
        omega
      · refine ih (len + 1) _ _ (by omega) (by omega) (by omega) ?_ ?_ ?_
        · rw [show len + 1 - 1 = len by omega, hB]; omega
        · rw [firstCode_succ lens len h1, hsz, hf]
        · omega

theorem puff_sound (d : ByteArray) (lens : Array Nat) (pos : Nat) (src : Nat → Option Nat)
    (byLen : Array (Array Nat)) (hsrc : IsDataSrc d pos src) (hby : IsByLen lens byLen)
    (s l : Nat) (h : puff src byLen = some (s, l)) :
    Prefix.matchesAt d lens pos s = true ∧ lens.getD s 0 = l :=
  go_sound d lens pos src byLen hsrc hby 16 1 0 0 s l (by omega) (Nat.le_refl _)
    (by simp [Prefix.bitsMSB]) (by simp [Prefix.firstCode]) (Nat.le_refl _) h

/-- **`puff` on the stream is the specification's search** (for code lengths ≤ 15). -/
theorem puff_eq_find (d : ByteArray) (lens : Array Nat) (pos : Nat) (src : Nat → Option Nat)
    (byLen : Array (Array Nat)) (hsrc : IsDataSrc d pos src) (hby : IsByLen lens byLen)
    (h15 : ∀ s, lens.getD s 0 ≤ 15) :
    puff src byLen = ((List.range lens.size).find? (Prefix.matchesAt d lens pos)).map
      (fun s => (s, lens.getD s 0)) := by
  cases hf : (List.range lens.size).find? (Prefix.matchesAt d lens pos) with
  | some s =>
    have hm := List.find?_some hf
    have hm' := (matches_iff d lens pos s).mp hm
    have hc := go_complete d lens pos src byLen hsrc hby s hm (h15 s) 16 1 0 0 (by omega)
      (Nat.le_refl _) (by omega) (by simp [Prefix.bitsMSB]) (by simp [Prefix.firstCode])
      (Nat.le_refl _)
    cases hp : puff src byLen with
    | none =>
      have e : puff src byLen = puff.go src byLen 1 0 0 := rfl
      rw [← e, hp] at hc; cases hc
    | some p =>
      obtain ⟨s', l'⟩ := p
      obtain ⟨hm2, hl⟩ := puff_sound d lens pos src byLen hsrc hby s' l' hp
      have := matches_unique d lens pos s' s hm2 hm
      subst this; subst hl; rfl
  | none =>
    cases hp : puff src byLen with
    | none => rfl
    | some p =>
      obtain ⟨s', l'⟩ := p
      obtain ⟨hm2, _⟩ := puff_sound d lens pos src byLen hsrc hby s' l' hp
      have hlt := lt_of_getD_ne lens s' ((matches_iff d lens pos s').mp hm2).1
      exact absurd hm2 (List.find?_eq_none.mp hf s' (List.mem_range.mpr hlt))

/-! ## The lookup table -/

/-- **A table lookup agrees with `puff` on the stream.** -/
theorem decode_eq_puff (lens : Array Nat) (d : ByteArray) (pos : Nat) :
    (mkTable lens).decode d pos =
      match puff (dataSrc d pos) (symbolsByLen lens) with
      | some (s, l) => .ok (s, pos + l)
      | none => .error Prefix.symErr := by
  unfold Table.decode mkTable
  simp only
  generalize htb : min 8 (lens.foldl max 0) = tb
  have htb8 : tb ≤ 8 := htb ▸ Nat.min_le_left _ _
  generalize hpk : le d (pos / 8) 4 >>> (pos % 8) % 2 ^ tb = peek
  have hpeek : peek < 2 ^ tb := hpk ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hpeek, Option.getD_some]
  cases hp : puff (patternSrc tb peek) (symbolsByLen lens) with
  | none =>
    simp only; rw [ite_eq_right (by simp)]
    cases puff (dataSrc d pos) (symbolsByLen lens) <;> rfl
  | some p =>
    obtain ⟨s, l⟩ := p
    simp only
    obtain ⟨hl1, hl15, b, hb⟩ := puff_props _ _ s l hp
    have hltb : l - 1 < tb := by
      unfold patternSrc at hb; split at hb
      · assumption
      · cases hb
    have e1 : (s * 16 + l) % 16 = l := by omega
    have e2 : (s * 16 + l) / 16 = s := by omega
    rw [e1, e2]
    by_cases hc : pos + l ≤ 8 * d.size
    · rw [ite_eq_left ⟨by omega, hc⟩, puff_local _ (patternSrc tb peek) (dataSrc d pos) s l hp ?_]
      intro j hj
      unfold patternSrc dataSrc
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ← hpk, peek_bit d pos tb j (by omega) (by omega)]
    · rw [ite_eq_right (by omega)]
      cases puff (dataSrc d pos) (symbolsByLen lens) <;> rfl

/-! ## Main theorem -/

theorem lens_le_15 (lens : Array Nat) (h : ¬ (lens.any (· > Prefix.maxLen)) = true) :
    ∀ s, lens.getD s 0 ≤ 15 := by
  intro s
  rcases Nat.lt_or_ge s lens.size with hs | hs
  · rw [getD_eq lens s hs]
    rcases Nat.lt_or_ge 15 lens[s] with h' | h'
    · exact absurd (Array.any_eq_true.mpr ⟨s, hs, by simp [Prefix.maxLen]; omega⟩) h
    · exact h'
  · simp [Array.getD_eq_getD_getElem?, hs]

/-- **The table-driven prefix code builder equals the specification's.** -/
theorem fastBuild_eq : VP8L.fastBuild = Spec.Prefix.build := by
  funext d lens
  unfold fastBuild Prefix.build
  by_cases hany : lens.any (· > Prefix.maxLen) = true
  · rw [ite_eq_left hany, ite_eq_left hany]
  · rw [ite_eq_right hany, ite_eq_right hany]
    have h15 := lens_le_15 lens hany
    generalize Prefix.coded lens = cl
    rcases cl with _ | ⟨a, _ | ⟨b, r⟩⟩
    · rfl
    · rfl
    · simp only
      by_cases hk : Prefix.kraft lens = 2 ^ Prefix.maxLen
      · rw [ite_eq_left hk, ite_eq_left hk]
        congr 2
        funext pos
        rw [decode_eq_puff, puff_eq_find d lens pos (dataSrc d pos) (symbolsByLen lens)
          (fun _ => rfl) (fun l h1 h2 => symbolsByLen_getD lens l h1 h2) h15]
        cases (List.range lens.size).find? (Prefix.matchesAt d lens pos) <;> rfl
      · rw [ite_eq_right hk, ite_eq_right hk]

end WebP.Proofs