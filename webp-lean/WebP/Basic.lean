/-!
# Shared basic types for the WebP decoder.
-/
namespace WebP

/-- An 8-bit RGBA image in row-major order, 4 bytes per pixel (R, G, B, A). -/
structure RGBAImage where
  width  : Nat
  height : Nat
  data   : ByteArray

end WebP
