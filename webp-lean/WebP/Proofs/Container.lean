import WebP.Container.Demux
/-!
# The demuxer implements the container grammar

`demux_iff : Container.demux d = .ok L ↔ Spec.Demux d L` — soundness and completeness of the
executable demuxer `WebP.Container.demux` with respect to the relational grammar
`WebP.Spec.Demux` (RFC 9649 §2).
-/
namespace WebP.Proofs

open WebP.Spec WebP.Container

/-! ## FourCC values -/

theorem VP8X_val : VP8X = 1480085590 := by decide
theorem ICCP_val : ICCP = 1346585417 := by decide
theorem ANIM_val : ANIM = 1296649793 := by decide
theorem ANMF_val : ANMF = 1179471425 := by decide
theorem ALPH_val : ALPH = 1213221953 := by decide
theorem VP8_val : VP8 = 540561494 := by decide
theorem VP8L_val : VP8L = 1278758998 := by decide

theorem isBitstream_iff (t : Nat) : isBitstream t = true ↔ t = VP8 ∨ t = VP8L := by
  simp [isBitstream]

theorem ne_of_isBitstream {t : Nat} (h : isBitstream t = true) :
    t ≠ VP8X ∧ t ≠ ICCP ∧ t ≠ ANIM ∧ t ≠ ALPH := by
  rw [isBitstream_iff] at h
  rw [VP8X_val, ICCP_val, ANIM_val, ALPH_val]
  rcases h with h | h <;> rw [h] <;> decide

/-! ## Chunk sequences -/

theorem _root_.WebP.Spec.ChunkSeq.le {d : ByteArray} {p stop : Nat} {cs : List Chunk}
    (h : ChunkSeq d p stop cs) : p ≤ stop := by
  induction h <;> omega

theorem parseChunks_iff (d : ByteArray) (p stop : Nat) (cs : List Chunk) :
    parseChunks d p stop = .ok cs ↔ ChunkSeq d p stop cs := by
  rw [parseChunks]
  by_cases h1 : p = stop
  · subst h1
    simp only [↓reduceIte]
    constructor
    · intro h; cases h; exact .nil _
    · intro h
      cases h with
      | nil => rfl
      | cons _ _ _ h' => have := h'.le; omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : stop < p + 8
    · simp only [h2, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro h
        cases h with
        | nil => exact absurd rfl h1
        | cons _ _ _ h' => have := h'.le; omega
    · simp only [h2, ↓reduceIte]
      by_cases h3 : stop < p + 8 + u32 d (p + 4) + u32 d (p + 4) % 2
      · simp only [h3, ↓reduceIte]
        constructor
        · intro h; cases h
        · intro h
          cases h with
          | nil => exact absurd rfl h1
          | cons _ _ _ h' => have := h'.le; omega
      · simp only [h3, ↓reduceIte]
        have ih := parseChunks_iff d (p + 8 + u32 d (p + 4) + u32 d (p + 4) % 2) stop
        constructor
        · intro h
          split at h
          · rename_i cs' heq
            cases h
            exact .cons _ _ _ ((ih cs').1 heq)
          · cases h
        · intro h
          cases h with
          | nil => exact absurd rfl h1
          | cons _ _ cs' h' => rw [(ih cs').2 h']
termination_by stop - p

theorem _root_.WebP.Spec.ChunkSeq.det {d : ByteArray} {p stop : Nat} {cs cs' : List Chunk}
    (h : ChunkSeq d p stop cs) (h' : ChunkSeq d p stop cs') : cs = cs' := by
  have a := (parseChunks_iff d p stop cs).2 h
  have b := (parseChunks_iff d p stop cs').2 h'
  rw [a] at b; cases b; rfl

/-! ## RIFF header -/

theorem parseRiff_iff (d : ByteArray) (cs : List Chunk) :
    parseRiff d = .ok cs ↔ RiffFile d cs := by
  unfold parseRiff
  dsimp only
  constructor
  · intro h
    split at h
    · rename_i hc
      split at h
      · rename_i hs
        exact ⟨hc.2.1, hc.2.2, hs.1, hs.2, (parseChunks_iff _ _ _ _).1 h⟩
      · cases h
    · cases h
  · intro h
    have hle := h.chunks.le
    have hf := h.fits
    have c1 : 12 ≤ d.size ∧ u32 d 0 = RIFF ∧ u32 d 8 = WEBP := ⟨by omega, h.riff, h.webp⟩
    have c2 : u32 d 4 ≤ 2 ^ 32 - 10 ∧ 8 + u32 d 4 ≤ d.size := ⟨h.sizeMax, h.fits⟩
    simp only [c1, c2, and_self, ↓reduceIte]
    exact (parseChunks_iff _ _ _ _).2 h.chunks

theorem _root_.WebP.Spec.RiffFile.det {d : ByteArray} {cs cs' : List Chunk}
    (h : RiffFile d cs) (h' : RiffFile d cs') : cs = cs' := h.chunks.det h'.chunks

/-! ## Frame data and frames -/

theorem frameData_iff (core : List Chunk) (a : Option Chunk) (b : Chunk) :
    frameData core = .ok (a, b) ↔ FrameData core a b := by
  unfold FrameData
  match core with
  | [] => cases a <;> simp [frameData]
  | [x] =>
    by_cases hx : isBitstream x.tag = true
    · cases a <;> simp [frameData, hx] <;> grind
    · cases a <;> simp [frameData, hx] <;> grind
  | [x, y] =>
    by_cases hx : x.tag = ALPH ∧ isBitstream y.tag = true
    · cases a <;> simp [frameData, hx] <;> grind
    · cases a <;> simp [frameData, hx] <;> grind
  | x :: y :: z :: t =>
    cases a <;> simp [frameData]

theorem parseFrame_iff (d : ByteArray) (c : Chunk) (f : FrameInfo) :
    parseFrame d c = .ok f ↔ FrameChunk d c f := by
  unfold parseFrame FrameChunk
  constructor
  · intro h
    split at h
    · rename_i hc
      split at h
      · rename_i sub hsub
        split at h
        · rename_i hall
          split at h
          · rename_i alph bits hfd
            cases h
            refine ⟨hc.1, hc.2, sub, (parseChunks_iff _ _ _ _).1 hsub, hall, ?_, rfl⟩
            exact (frameData_iff _ _ _).1 hfd
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨ht, hs, sub, hseq, hall, hfd, hf⟩
    simp only [ht, hs, and_self, ↓reduceIte, (parseChunks_iff _ _ _ _).2 hseq, hall,
      (frameData_iff _ _ _).2 hfd]
    rw [← hf]

theorem parseFrames_iff (d : ByteArray) :
    ∀ (cs : List Chunk) (fs : List FrameInfo), parseFrames d cs = .ok fs ↔ Frames d cs fs
  | [], fs => by
    simp only [parseFrames]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | c :: cs, fs => by
    simp only [parseFrames]
    constructor
    · intro h
      cases hf : parseFrame d c <;> cases hfs : parseFrames d cs <;> simp [hf, hfs] at h
      subst h
      exact .cons _ _ _ _ ((parseFrame_iff _ _ _).1 hf) ((parseFrames_iff d cs _).1 hfs)
    · intro h
      cases h with
      | cons _ f _ fs' hc hr =>
        rw [(parseFrame_iff _ _ _).2 hc, (parseFrames_iff d cs fs').2 hr]

/-! ## List splitting -/

/-- Predicate used by the demuxer to skip leading 'ICCP' chunks. -/
abbrev isIccp (c : Chunk) : Bool := decide (c.tag = ICCP)

theorem mem_takeWhile {p : Chunk → Bool} :
    ∀ {l : List Chunk} {c : Chunk}, c ∈ l.takeWhile p → p c = true
  | [], _, h => by simp at h
  | x :: xs, c, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.1 h with rfl | h
      · exact hx
      · exact mem_takeWhile h
    · simp at h

theorem dropWhile_iccp (iccps rest : List Chunk) (h : ∀ c ∈ iccps, c.tag = ICCP)
    (hr : ∀ a ∈ rest.head?, a.tag ≠ ICCP) :
    (iccps ++ rest).dropWhile isIccp = rest := by
  induction iccps with
  | nil =>
    cases rest with
    | nil => rfl
    | cons a r =>
      have : a.tag ≠ ICCP := hr a (by simp)
      simp [this]
  | cons x xs ih =>
    have hx : x.tag = ICCP := h x (by simp)
    simp only [List.cons_append, List.dropWhile, isIccp, hx, decide_true]
    exact ih (fun c hc => h c (by simp [hc]))

/-! ## Extended format -/

theorem parseExtended_sound (d : ByteArray) (x : Chunk) (rest : List Chunk) (L : Layout)
    (hR : RiffFile d (x :: rest)) (hx : x.tag = VP8X) (h : parseExtended d x rest = .ok L) :
    Demux d L := by
  unfold parseExtended at h
  dsimp only at h
  split at h
  · cases h
  rename_i hsz
  split at h
  · cases h
  rename_i hcanvas
  have hcanvas' : canvasOk (vp8xInfo d x) := by unfold canvasOk; omega
  have hsz' : 10 ≤ x.size := by omega
  -- the decomposition F = takeWhile ++ dropWhile
  have hsplit := (List.takeWhile_append_dropWhile (p := isIccp) (l := rest.filter isRecon)).symm
  have hicc : ∀ c ∈ (rest.filter isRecon).takeWhile isIccp, c.tag = ICCP := by
    intro c hc; have := mem_takeWhile hc; simpa [isIccp] using this
  split at h
  · rename_i hanim
    split at h
    · rename_i a anmfs hcore
      split at h
      · rename_i hcond
        split at h
        · rename_i frames hfr
          split at h
          · rename_i hall
            cases h
            rw [hcore] at hsplit
            refine Demux.animated x rest _ a anmfs frames hR hx hsz' hcanvas' hanim hsplit hicc
              hcond.1 hcond.2.1 hcond.2.2 ((parseFrames_iff _ _ _).1 hfr) ?_
            intro f hf
            have := List.all_eq_true.1 hall f hf
            simpa using this
          · cases h
        · cases h
      · cases h
    · cases h
  · rename_i hanim
    have hanim' : (vp8xInfo d x).animation = false := by simpa using hanim
    have hsplit' := (List.takeWhile_append_dropWhile (p := isIccp)
      (l := rest.filter isStillRecon)).symm
    have hicc' : ∀ c ∈ (rest.filter isStillRecon).takeWhile isIccp, c.tag = ICCP := by
      intro c hc; have := mem_takeWhile hc; simpa [isIccp] using this
    split at h
    · rename_i alph bits hfd
      cases h
      have hfd' := (frameData_iff _ _ _).1 hfd
      refine Demux.still x rest _ alph bits hR hx hsz' hcanvas' hanim' ?_ hicc'
        ⟨rfl, hfd'.2⟩
      conv => lhs; rw [hsplit']
      rw [hfd'.1, List.append_assoc]
    · cases h

theorem parseExtended_still (d : ByteArray) (x : Chunk) (rest iccps : List Chunk)
    (alph : Option Chunk) (bits : Chunk)
    (hsz : 10 ≤ x.size) (hc : canvasOk (vp8xInfo d x))
    (hanim : (vp8xInfo d x).animation = false)
    (hF : rest.filter isStillRecon = iccps ++ alph.toList ++ [bits])
    (hicc : ∀ c ∈ iccps, c.tag = ICCP)
    (hfd : FrameData (alph.toList ++ [bits]) alph bits) :
    parseExtended d x rest = .ok (.still (some (vp8xInfo d x)) alph bits) := by
  have hb := ne_of_isBitstream hfd.2.2
  have hal : ∀ a ∈ alph, a.tag = ALPH := hfd.2.1
  have tagne : ICCP ≠ ALPH := by rw [ICCP_val, ALPH_val]; decide
  have hdrop : (rest.filter isStillRecon).dropWhile isIccp = alph.toList ++ [bits] := by
    rw [hF, List.append_assoc]
    apply dropWhile_iccp _ _ hicc
    match alph with
    | none => intro a ha; simp at ha; subst ha; exact hb.2.1
    | some a' => intro a ha; simp at ha; subst ha; rw [hal a' (by simp)]; exact tagne.symm
  unfold parseExtended
  have n1 : ¬ x.size < 10 := by omega
  have n2 : ¬ (vp8xInfo d x).canvasWidth * (vp8xInfo d x).canvasHeight > 2 ^ 32 - 1 := by
    unfold canvasOk at hc; omega
  simp only [n1, n2, hanim, Bool.false_eq_true, ↓reduceIte]
  rw [hdrop, (frameData_iff _ _ _).2 hfd]

theorem parseExtended_animated (d : ByteArray) (x : Chunk) (rest iccps : List Chunk) (a : Chunk)
    (anmfs : List Chunk) (frames : List FrameInfo)
    (hsz : 10 ≤ x.size) (hc : canvasOk (vp8xInfo d x))
    (hanim : (vp8xInfo d x).animation = true)
    (hF : rest.filter isRecon = iccps ++ a :: anmfs)
    (hicc : ∀ c ∈ iccps, c.tag = ICCP) (ha : a.tag = ANIM) (has : 6 ≤ a.size)
    (hne : anmfs ≠ []) (hfr : Frames d anmfs frames)
    (hin : ∀ f ∈ frames, frameInCanvas (vp8xInfo d x) f) :
    parseExtended d x rest =
      .ok (.animated (vp8xInfo d x) (u32 d a.off) (u16 d (a.off + 4)) frames) := by
  have hdrop : (rest.filter isRecon).dropWhile isIccp = a :: anmfs := by
    rw [hF]
    apply dropWhile_iccp _ _ hicc
    intro b hb
    simp at hb; subst hb; rw [ha, ICCP_val, ANIM_val]; decide
  unfold parseExtended
  have n1 : ¬ x.size < 10 := by omega
  have n2 : ¬ (vp8xInfo d x).canvasWidth * (vp8xInfo d x).canvasHeight > 2 ^ 32 - 1 := by
    unfold canvasOk at hc; omega
  have hall : (frames.all fun f => decide (frameInCanvas (vp8xInfo d x) f)) = true :=
    List.all_eq_true.2 (fun f hf => by simpa using hin f hf)
  simp only [n1, n2, hanim, ↓reduceIte]
  rw [hdrop]
  simp only [ha, has, ne_eq, hne, not_false_eq_true, and_self, ↓reduceIte,
    (parseFrames_iff _ _ _).2 hfr, hall]

/-! ## Main theorem -/

theorem demux_iff (d : ByteArray) (L : Layout) : demux d = .ok L ↔ Demux d L := by
  constructor
  · intro h
    unfold demux at h
    split at h
    · rename_i c rest hR
      have hR' := (parseRiff_iff _ _).1 hR
      split at h
      · rename_i hx
        exact parseExtended_sound d c rest L hR' hx h
      · split at h
        · rename_i hb
          cases h
          exact Demux.simple c rest hR' hb.1 hb.2
        · cases h
    · cases h
    · cases h
  · intro h
    cases h with
    | simple c rest hR hb hf =>
      unfold demux
      rw [(parseRiff_iff _ _).2 hR]
      have n := (ne_of_isBitstream hb).1
      simp only [n, hb, hf, and_self, ↓reduceIte]
    | still x rest iccps alph bits hR hx hsz hc hanim hF hicc hfd =>
      unfold demux
      rw [(parseRiff_iff _ _).2 hR]
      simp only [hx, ↓reduceIte]
      exact parseExtended_still d x rest iccps alph bits hsz hc hanim hF hicc hfd
    | animated x rest iccps a anmfs frames hR hx hsz hc hanim hF hicc ha has hne hfr hin =>
      unfold demux
      rw [(parseRiff_iff _ _).2 hR]
      simp only [hx, ↓reduceIte]
      exact parseExtended_animated d x rest iccps a anmfs frames hsz hc hanim hF hicc ha has hne
        hfr hin

end WebP.Proofs
