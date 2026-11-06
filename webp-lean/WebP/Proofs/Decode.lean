import WebP.Proofs.Lossless
import WebP.Proofs.Alpha
import WebP.Proofs.Container
import WebP.FFI
import WebP.Proofs.VP8
/-!
# End-to-end: the decoder implements the WebP semantics

* `decodeWith_iff`: for any VP8 decoder `vp8`,
  `WebP.decodeWith vp8 d = .ok out ↔ Spec.Decodes vp8 d out`.
* `decode_iff`: the same for `WebP.decode`, whose lossy part is `WebP.vp8Decode`.
* `decodes_unique`: the semantics is functional (a file has at most one meaning).
* `ffi_sound` / `ffi_complete`: the entry point used by the fuzzer returns exactly the
  specified result, except that it may refuse (status 2) inputs beyond its resource limit.
* With the lossy decoder proven equal to the RFC 6386 semantics (`vp8Decode_eq`), all of these
  hold for the concrete semantics `Spec.Decodes Spec.lossy`: `decode_iff'`, `decodes_unique'`,
  `ffi_sound'`, `ffi_complete'`, `ffi_invalid'`.
-/
namespace WebP.Proofs

open WebP WebP.Spec

theorem implComponents_eq (vp8 : ByteArray → Except String RGBAImage) :
    implComponents vp8 = specComponents vp8 := by
  unfold implComponents specComponents
  rw [vp8l_decode_eq, vp8l_decodeStream_eq, unfilter_eq]

/-- **The decoder computes exactly the specified semantics** (relative to the VP8 decoder). -/
theorem decodeWith_iff (vp8 : ByteArray → Except String RGBAImage) (d : ByteArray)
    (out : Output) : WebP.decodeWith vp8 d = .ok out ↔ Spec.Decodes vp8 d out := by
  unfold WebP.decodeWith Spec.Decodes
  rw [implComponents_eq]
  constructor
  · intro h
    cases hL : Container.demux d with
    | error e => simp [hL, bind, Except.bind] at h
    | ok L =>
      simp only [hL, bind, Except.bind] at h
      exact ⟨L, (demux_iff d L).mp hL, h⟩
  · rintro ⟨L, hD, hL⟩
    rw [(demux_iff d L).mpr hD]
    simpa [bind, Except.bind] using hL

/-- **`WebP.decode` computes exactly the specified semantics.** -/
theorem decode_iff (d : ByteArray) (out : Output) :
    WebP.decode d = .ok out ↔ Spec.Decodes vp8Decode d out :=
  decodeWith_iff vp8Decode d out

/-- A well-formed file has a unique layout and a unique meaning. -/
theorem demux_unique (d : ByteArray) (L L' : Layout) (h : Demux d L) (h' : Demux d L') :
    L = L' := by
  have := (demux_iff d L).mpr h
  rw [(demux_iff d L').mpr h'] at this
  cases this; rfl

theorem decodes_unique (vp8 : ByteArray → Except String RGBAImage) (d : ByteArray)
    (o o' : Output) (h : Spec.Decodes vp8 d o) (h' : Spec.Decodes vp8 d o') : o = o' := by
  have e := (decodeWith_iff vp8 d o).mpr h
  rw [(decodeWith_iff vp8 d o').mpr h'] at e
  cases e; rfl

/-- What the fuzzer gets back as "ok" is the specified decoding of the file. -/
theorem ffi_sound (d : ByteArray) (maxPixels : Nat) (o : Output) :
    FFI.decodeChecked d maxPixels = .ok o → Spec.Decodes vp8Decode d o := by
  intro h
  unfold FFI.decodeChecked at h
  cases hL : Container.demux d with
  | error e => simp [hL] at h
  | ok L =>
    simp only [hL] at h
    split at h
    · simp at h
    · rw [implComponents_eq] at h
      split at h
      · rename_i o' ho; cases h; exact ⟨L, (demux_iff d L).mp hL, ho⟩
      · simp at h

/-- Within the resource limit, every file with a meaning is decoded to it, and every file
without one is reported invalid (status 1). -/
theorem ffi_complete (d : ByteArray) (maxPixels : Nat) (o : Output) (L : Layout)
    (hD : Demux d L) (hlim : FFI.withinLimits d L maxPixels = true)
    (h : decodeLayout (specComponents vp8Decode) d L = .ok o) :
    FFI.decodeChecked d maxPixels = .ok o := by
  unfold FFI.decodeChecked
  rw [(demux_iff d L).mpr hD]
  simp only [hlim, Bool.not_true]
  rw [implComponents_eq, h]
  rfl

theorem ffi_invalid (d : ByteArray) (maxPixels : Nat) (msg : String) :
    FFI.decodeChecked d maxPixels = .error (1, msg) → ¬ ∃ o, Spec.Decodes vp8Decode d o := by
  intro h ⟨o, L, hD, hL⟩
  unfold FFI.decodeChecked at h
  rw [(demux_iff d L).mpr hD] at h
  simp only at h
  split at h
  · simp at h
  · rw [implComponents_eq, hL] at h; simp at h

/-! ## The concrete semantics: lossy = RFC 6386 reference decoder + chosen YUV→RGB -/

/-- **`WebP.decode` computes exactly the WebP semantics, with the lossy bitstream decoded as
specified by RFC 6386** (and converted to RGBA with the chosen §2.5 conversion). -/
theorem decode_iff' (d : ByteArray) (out : Output) :
    WebP.decode d = .ok out ↔ Spec.Decodes Spec.lossy d out := by
  rw [← vp8Decode_eq]; exact decode_iff d out

theorem decodes_unique' (d : ByteArray) (o o' : Output) (h : Spec.Decodes Spec.lossy d o)
    (h' : Spec.Decodes Spec.lossy d o') : o = o' :=
  decodes_unique Spec.lossy d o o' h h'

/-- What the fuzzer gets back as "ok" is the specified decoding of the file. -/
theorem ffi_sound' (d : ByteArray) (maxPixels : Nat) (o : Output) :
    FFI.decodeChecked d maxPixels = .ok o → Spec.Decodes Spec.lossy d o := by
  rw [← vp8Decode_eq]; exact ffi_sound d maxPixels o

/-- Within the resource limit, every file with a meaning is decoded to it. -/
theorem ffi_complete' (d : ByteArray) (maxPixels : Nat) (o : Output) (L : Layout)
    (hD : Demux d L) (hlim : FFI.withinLimits d L maxPixels = true)
    (h : decodeLayout (specComponents Spec.lossy) d L = .ok o) :
    FFI.decodeChecked d maxPixels = .ok o := by
  rw [← vp8Decode_eq] at h; exact ffi_complete d maxPixels o L hD hlim h

/-- Files reported invalid (status 1) have no meaning. -/
theorem ffi_invalid' (d : ByteArray) (maxPixels : Nat) (msg : String) :
    FFI.decodeChecked d maxPixels = .error (1, msg) → ¬ ∃ o, Spec.Decodes Spec.lossy d o := by
  rw [← vp8Decode_eq]; exact ffi_invalid d maxPixels msg

end WebP.Proofs
