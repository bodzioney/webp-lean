/-!
# A decoded VP8 frame

Shared by the RFC 6386 specification (`WebP.Spec.VP8.decode`), the shipped decoder
(`WebP.VP8.decodeFrame`) and the libwebp model (`WebP.VP8Libwebp.decodeFrame`).
-/
namespace WebP.VP8

/-- A decoded VP8 frame: Y'CbCr 4:2:0 planes cropped to the visible size. -/
structure Frame where
  width  : Nat
  height : Nat
  /-- luma plane, stride `width`, `height` rows -/
  y : ByteArray
  /-- chroma planes, stride `(width+1)/2`, `(height+1)/2` rows -/
  u : ByteArray
  v : ByteArray

end WebP.VP8
