import WebP.Proofs.Prefix
/-!
# The lossless decoder equals the specification

`VP8L.decode = Spec.VP8L.decode` and `VP8L.decodeStream = Spec.VP8L.decodeStream`: both are
the same transcription of RFC 9649 §3 (`Spec.VP8L.decodeWith`) instantiated with primitives
that are proven equal (`fastReadBits_eq`, `fastBuild_eq`).
-/
namespace WebP.Proofs

theorem fastPrims_eq : VP8L.fastPrims = Spec.VP8L.specPrims := by
  unfold VP8L.fastPrims Spec.VP8L.specPrims
  rw [fastReadBits_eq, fastBuild_eq]

/-- **The lossless decoder is the RFC 9649 §3 specification.** -/
theorem vp8l_decode_eq : VP8L.decode = Spec.VP8L.decode := by
  funext d
  unfold VP8L.decode Spec.VP8L.decode
  rw [fastPrims_eq]

theorem vp8l_decodeStream_eq : VP8L.decodeStream = Spec.VP8L.decodeStream := by
  funext d w h
  unfold VP8L.decodeStream Spec.VP8L.decodeStream
  rw [fastPrims_eq]

end WebP.Proofs
