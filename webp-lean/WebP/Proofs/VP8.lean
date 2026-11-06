import WebP.Proofs.VP8Bool
import WebP.Decode
/-!
# The lossy decoder equals the RFC 6386 reference decoder

* `decodeFrame_eq : VP8.decodeFrame = Spec.VP8.decode` — the shipped VP8 decoder is the
  transcription of the RFC 6386 reference decoder (`Spec.VP8.decodeWith`) instantiated with the
  optimized primitives, which are proven equal to the reference ones (`fastPrims_eq`).
* `vp8Decode_eq : WebP.vp8Decode = Spec.lossy` — and so is the lossy part of `WebP.decode`.
-/
namespace WebP.Proofs

open WebP

/-- **The shipped VP8 decoder is the RFC 6386 reference decoder.** -/
theorem decodeFrame_eq : VP8.decodeFrame = Spec.VP8.decode := by
  funext d
  unfold VP8.decodeFrame Spec.VP8.decode
  rw [VP8Bool.fastPrims_eq]

/-- **The lossy decoder of `WebP.decode` is the lossy semantics.** -/
theorem vp8Decode_eq : vp8Decode = Spec.lossy := by
  funext d
  unfold vp8Decode Spec.lossy
  rw [decodeFrame_eq]

end WebP.Proofs
