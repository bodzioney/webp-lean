import WebP.Spec.Decode
import WebP.Container.Demux
import WebP.VP8L.Fast
import WebP.Alpha
import WebP.VP8
/-!
# The WebP decoder

`WebP.decode` = demuxer + optimized components. `WebP.Proofs.Decode` proves that it computes
exactly the semantics `Spec.Decodes` (relative to the VP8 decoder used), and
`WebP.Proofs.VP8` that its lossy decoder `vp8Decode` is the lossy semantics `Spec.lossy`.
-/
namespace WebP

/-- 'VP8 ' payload to RGBA, with the lossy decoder of `WebP.VP8` (proven equal to the RFC 6386
reference decoder) and the chosen Y'CbCr → RGBA conversion `Frame.toRGBA`. -/
def vp8Decode (d : ByteArray) : Except String RGBAImage :=
  (VP8.decodeFrame d).map fun f => ⟨f.width, f.height, f.toRGBA⟩

/-- The optimized components, parametric in the VP8 decoder. -/
def implComponents (vp8 : ByteArray → Except String RGBAImage) : Spec.Components :=
  ⟨vp8, VP8L.decode, VP8L.decodeStream, Alpha.unfilter⟩

/-- **The decoder**, parametric in the VP8 decoder. -/
def decodeWith (vp8 : ByteArray → Except String RGBAImage) (d : ByteArray) :
    Except String Spec.Output := do
  let L ← Container.demux d
  Spec.decodeLayout (implComponents vp8) d L

/-- **The decoder.** -/
def decode (d : ByteArray) : Except String Spec.Output := decodeWith vp8Decode d

end WebP
