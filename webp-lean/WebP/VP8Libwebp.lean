import WebP.VP8Libwebp.Decode
import WebP.Spec.VP8.ToRGBA
/-!
# libwebp-mimic VP8 decoder (differential model of libwebp; not the shipped decoder)

A port of libwebp's VP8 decoder, bit-exact with libwebp including its behaviour on corrupted
streams (partition-size clamping, end-of-data errors, SSE2-style 16-bit-wrapping IDCT). The
shipped decoder is `WebP.VP8.decodeFrame` (RFC 6386 reference decoder, proven); this one is
used by `vp8-check ... libwebp` as a model of libwebp.

* `WebP.VP8Libwebp.readHeader`     — frame header only: `(width, height)` (libwebp `VP8GetInfo`).
* `WebP.VP8Libwebp.decodeFrame`    — full key frame decode of a 'VP8 ' chunk payload.
* `WebP.VP8Libwebp.decodeFrameExt` — same, with libwebp's "data extends past the chunk" convention.
-/
namespace WebP.VP8Libwebp

open WebP.VP8 (Frame)

/-- Parse and validate the VP8 frame header (libwebp `VP8GetInfo` checks with
`chunk_size = data.size`) and return `(width, height)`. -/
def readHeader (data : ByteArray) : Except String (Nat × Nat) := do
  let t ← parseFrameTag data data.size
  return (t.width, t.height)

/-- Full key frame decode of a 'VP8 ' chunk payload (`data` = exactly the payload). -/
def decodeFrame (data : ByteArray) : Except String Frame := decodeFrameExt data data.size

end WebP.VP8Libwebp
