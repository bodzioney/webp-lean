import WebP.Spec.VP8
import WebP.VP8.BoolDecoder
/-!
# VP8 lossy decoder — public API (see DESIGN.md "VP8 (lossy) Lean API")

* `WebP.VP8.Frame`          — decoded Y'CbCr 4:2:0 planes (cropped to the visible size).
* `WebP.VP8.readHeader`     — frame header only: `(width, height)` (RFC 6386 §9.1,
                              `vp8_parse_frame_header`).
* `WebP.VP8.decodeFrame`    — full key frame decode of a 'VP8 ' chunk payload: the RFC 6386
                              reference decoder (`Spec.VP8.decodeWith`) instantiated with the
                              optimized primitives `fastPrims`. `WebP.Proofs.VP8.decodeFrame_eq`
                              proves `decodeFrame = Spec.VP8.decode`.
* `WebP.VP8.Frame.toRGBA`   — the application-chosen Y'CbCr → RGBA conversion (libwebp-exact fancy
                              upsampling, alpha = 255).
-/
namespace WebP.VP8

/-- Parse the frame header (`vp8_parse_frame_header` checks) and return `(width, height)`.
Only used as a size probe (resource limits); `decodeFrame` does all the checks. -/
def readHeader (data : ByteArray) : Except String (Nat × Nat) := do
  let h ← Spec.VP8.parseFrameHeader data data.size
  return (h.w, h.h)

/-- Full key frame decode of a 'VP8 ' chunk payload (`data` = exactly the payload). -/
def decodeFrame (data : ByteArray) : Except String Frame := Spec.VP8.decodeWith fastPrims data

end WebP.VP8
