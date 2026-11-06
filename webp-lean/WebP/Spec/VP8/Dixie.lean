import WebP.Spec.VP8.LoopFilter
import WebP.Spec.VP8.Frame
/-!
# Decoding a key frame (RFC 6386 §19, §20.4 `dixie.c`: `vp8_dixie_decode_frame`, `decode_frame`)

The decoding of one VP8 frame by the reference decoder, from a fresh decoder context
(`calloc` + `vp8_dixie_decode_init`), restricted to the frames a WebP 'VP8 ' chunk can carry:

* **[interp]** The frame must be a key frame: a WebP file holds a single frame and no reference
  frames exist (RFC 9649 §2.5: "a VP8 key frame"). The reference decoder would go on and
  inter-predict from reference frames that do not exist.
* **[interp]** The frame must have `show_frame = 1`: an invisible frame has nothing to display.
  (libwebp rejects it too.)

* **[interp]** An error aborts the decoding. The reference code calls `setjmp` in
  `vp8_dixie_decode_frame` but never sets `ctx->error.setjmp`, so taken literally
  `vpx_internal_error` records the error and *returns*, and `decode_frame` carries on with an
  inconsistent state (e.g. reading partition sizes past the end of the data after "Truncated
  packet"): undefined behaviour, observed as heap-buffer-overflows/crashes under AddressSanitizer
  on ~19% of corrupted streams (`build/dixie/examples/rfc_literal_no_setjmp`). We follow the
  evident intent and libvpx (which sets the flag around its `setjmp`): every
  `vpx_internal_error` rejects the frame.

Everything else is the reference decoder's behaviour: its checks (`vp8_parse_frame_header`,
"Experimental bitstreams not supported", non-zero color space / clamping type bits rejected as
"Reserved bits not supported", the token-partition size checks), its processing order (for each
macroblock row: modes, tokens, prediction + reconstruction, then the loop filter of the previous
row; finally the loop filter of the last row), and its handling of truncated partitions (the
boolean decoder reads zeros past the end of a partition; this is not an error).

The output is the visible area of the frame buffer: the Y plane (`w × h`) and the U and V planes
(`⌈w/2⌉ × ⌈h/2⌉`).
-/
namespace WebP.Spec.VP8

open WebP.VP8 (Frame)

/-- Run a `BoolM` computation on a decoder state. -/
@[inline] def runB {α : Type} (x : BoolM α) (d : BoolDecoder) : α × BoolDecoder := x d

/-- The headers of a key frame, parsed from the first partition. -/
structure Headers where
  hdr : FrameHdr
  seg : SegmentHdr
  lf : LoopFilterHdr
  parts : Partitions
  quant : QuantHdr
  ent : EntropyHdr
  /-- the state of the first-partition decoder after the headers -/
  bool : BoolDecoder

/-- `decode_frame` up to (and including) `decode_entropy_header`. -/
def decodeHeaders (P : Prims) (data : ByteArray) : Except String Headers := do
  let sz := data.size
  let hdr ← parseFrameHeader data sz
  if hdr.isExperimental then throw "VP8: unsupported bitstream (experimental bitstreams not supported)"
  if !hdr.isKeyframe then throw "VP8: not a key frame"
  if !hdr.isShown then throw "VP8: frame not shown (show_frame = 0)"
  -- data += FRAME_HEADER_SZ + KEYFRAME_HEADER_SZ; sz -= …
  let off := 3 + 7
  let sz := sz - 10
  -- Start the bitreader for the header/entropy partition
  let bool := initBoolDecoder data off hdr.part0Sz
  -- the color space and clamping type bits (§9.2)
  let (reserved, bool) := runB (getUint P 2) bool
  if reserved ≠ 0 then throw "VP8: unsupported bitstream (reserved bits not supported)"
  let (seg, bool) := runB (decodeSegmentationHeader P) bool
  let (lf, bool) := runB (decodeLoopfilterHeader P) bool
  -- decode_and_init_token_partitions(ctx, bool, data + part0_sz, sz - part0_sz, …)
  let (np, bool) := runB (getUint P 2) bool
  let parts ← tokenPartitions data (1 <<< np) (off + hdr.part0Sz) (sz - hdr.part0Sz)
  let (quant, bool) := runB (decodeQuantizerHeader P) bool
  let (_refreshEntropy, bool) := runB (decodeReferenceHeader P) bool
  let (ent, bool) := runB (decodeEntropyHeader P) bool
  return { hdr, seg, lf, parts, quant, ent, bool }

/-- The macroblock-row loop of `decode_frame`: returns the frame buffer. -/
def decodeRows (P : Prims) (data : ByteArray) (H : Headers) (mbCols mbRows : Nat) : Img :=
  Id.run do
  let g := Geom.ofMbs mbCols
  let dqf := dequantInit H.seg H.quant
  let numParts := H.parts.size
  let ⟨y0, u0, v0⟩ := Img.alloc mbCols mbRows
  let mut y := y0
  let mut u := u0
  let mut v := v0
  let mut bool := H.bool
  let dummy := initBoolDecoder data 0 0
  let mut tokenBools : Array BoolDecoder := H.parts.map fun (o, s) => initBoolDecoder data o s
  -- `mb_info` of the row above (the zero border row for row 0) / of the previous row
  let mut above : Array MbInfo := Array.replicate mbCols MbInfo.zero
  -- reset_above_context (row 0)
  let mut aboveCtx : TokenCtx := Array.replicate (9 * mbCols) 0
  let mut partition := 0
  for row in [0:mbRows] do
    let (mbi, b) := runB (modemvProcessRow P H.seg H.ent above mbCols) bool
    bool := b
    let tb := tokenBools.getD partition dummy
    tokenBools := tokenBools.setIfInBounds partition dummy
    let ((coeffs, mbi, ac), tb) := runB (tokensProcessRow P H.ent.coeffProbs dqf mbi aboveCtx) tb
    tokenBools := tokenBools.setIfInBounds partition tb
    aboveCtx := ac
    let ⟨y1, u1, v1⟩ := predictProcessRow g y u v row mbi coeffs
    y := y1; u := u1; v := v1
    if H.lf.level ≠ 0 ∧ row ≠ 0 then
      let ⟨y2, u2, v2⟩ := loopfilterProcessRow g y u v H.seg H.lf (row - 1) above
      y := y2; u := u2; v := v2
    above := mbi
    partition := partition + 1
    if partition = numParts then partition := 0
  if H.lf.level ≠ 0 then
    let ⟨y2, u2, v2⟩ := loopfilterProcessRow g y u v H.seg H.lf (mbRows - 1) above
    y := y2; u := u2; v := v2
  return ⟨y, u, v⟩

/-- `n × rows` bytes of a plane starting at `origin`, rows `stride` apart. -/
def cropPlane (b : ByteArray) (origin stride n rows : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (n * rows)
  for j in [0:rows] do
    let s := origin + j * stride
    out := out ++ b.extract s (s + n)
  return out

/-- **Decoding of a 'VP8 ' chunk payload** by the RFC 6386 reference decoder, written over the
primitives `P`. -/
def decodeWith (P : Prims) (data : ByteArray) : Except String Frame := do
  let H ← decodeHeaders P data
  let w := H.hdr.w
  let h := H.hdr.h
  let mbCols := (w + 15) / 16
  let mbRows := (h + 15) / 16
  let img := decodeRows P data H mbCols mbRows
  let g := Geom.ofMbs mbCols
  let uvW := (w + 1) / 2
  let uvH := (h + 1) / 2
  return { width := w, height := h,
           y := cropPlane img.y g.yOrigin g.stride w h,
           u := cropPlane img.u g.uvOrigin g.uvStride uvW uvH,
           v := cropPlane img.v g.uvOrigin g.uvStride uvW uvH }

/-- **The RFC 6386 VP8 key-frame decoding of a 'VP8 ' chunk payload** (the specification). -/
def decode (data : ByteArray) : Except String Frame := decodeWith specPrims data

end WebP.Spec.VP8
