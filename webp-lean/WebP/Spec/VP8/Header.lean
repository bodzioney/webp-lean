import WebP.Spec.VP8.BoolDecoder
import WebP.Spec.VP8.Tables
/-!
# Frame header parsing (RFC 6386 §9, §19.1–§19.2; reference source §20.4 `dixie.c`)

Transcription of `vp8_parse_frame_header`, `decode_segmentation_header`,
`decode_loopfilter_header`, `decode_and_init_token_partitions`, `decode_quantizer_header`,
`decode_reference_header`, `decode_entropy_header` and `dequant_init`, specialised to a key
frame decoded with a fresh (zero-initialised, then `vp8_dixie_decode_init`) decoder context:
* every `memset(hdr, 0, …)` done for key frames, and the `calloc`'d context, give zero defaults;
* the "previous" quantizer index used by `decode_quantizer_header` is `0`;
* the dequantization cache `dequant_factors[i].quant_idx` starts at `-1` with all factors `0`
  (`dequant_global_init`; the factors are zero because the context is zero-initialised).
-/
namespace WebP.Spec.VP8

/-- `struct vp8_frame_hdr` (§9.1, §19.1). -/
structure FrameHdr where
  isKeyframe : Bool
  isExperimental : Bool
  version : Nat
  isShown : Bool
  /-- size of the first partition, in bytes -/
  part0Sz : Nat
  w : Nat
  h : Nat
  scaleW : Nat
  scaleH : Nat

/-- `vp8_parse_frame_header(data, sz, hdr)`: the 3-byte frame tag and, for key frames, the start
code and the dimensions. -/
def parseFrameHeader (data : ByteArray) (sz : Nat) : Except String FrameHdr := do
  if sz < 10 then throw "VP8: corrupt frame (fewer than 10 bytes)"
  let b (i : Nat) : Nat := (byteAt data i).toNat
  -- "The frame header is defined as a three-byte little endian value"
  let raw := b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16)
  let isKeyframe := (raw &&& 1) = 0
  let version := (raw >>> 1) &&& 3
  let isExperimental := (raw >>> 3) &&& 1 = 1
  let isShown := (raw >>> 4) &&& 1 = 1
  let part0Sz := (raw >>> 5) &&& 0x7ffff
  if sz ≤ part0Sz + (if isKeyframe then 10 else 3) then
    throw "VP8: corrupt frame (first partition does not fit)"
  if isKeyframe then
    if b 3 ≠ 0x9d ∨ b 4 ≠ 0x01 ∨ b 5 ≠ 0x2a then
      throw "VP8: unsupported bitstream (bad start code)"
    -- **[interp]** `data[9] << 24` overflows `int` when `data[9] ≥ 128` (undefined in C); it is
    -- read as the intended unsigned bit pattern (only bits 30–31 = scale_h depend on it).
    let raw := b 6 ||| (b 7 <<< 8) ||| (b 8 <<< 16) ||| (b 9 <<< 24)
    let w := raw &&& 0x3fff
    let h := (raw >>> 16) &&& 0x3fff
    if w = 0 ∨ h = 0 then throw "VP8: unsupported bitstream (zero width or height)"
    return { isKeyframe, isExperimental, version, isShown, part0Sz, w, h,
             scaleW := (raw >>> 14) &&& 3, scaleH := (raw >>> 30) &&& 3 }
  else
    return { isKeyframe, isExperimental, version, isShown, part0Sz,
             w := 0, h := 0, scaleW := 0, scaleH := 0 }

/-- `struct vp8_segment_hdr` (§9.3). -/
structure SegmentHdr where
  enabled : Bool
  updateData : Bool
  updateMap : Bool
  /-- `abs`: 0 = deltas, 1 = absolute values -/
  abs : Bool
  treeProbs : Array Nat
  lfLevel : Array Int
  quantIdx : Array Int

/-- `struct vp8_loopfilter_hdr` (§9.6). -/
structure LoopFilterHdr where
  useSimple : Bool
  level : Nat
  sharpness : Nat
  deltaEnabled : Bool
  refDelta : Array Int
  modeDelta : Array Int

/-- `struct vp8_quant_hdr` (§9.6). -/
structure QuantHdr where
  qIndex : Nat
  deltaUpdate : Bool
  y1DcDeltaQ : Int
  y2DcDeltaQ : Int
  y2AcDeltaQ : Int
  uvDcDeltaQ : Int
  uvAcDeltaQ : Int

/-- `struct vp8_entropy_hdr`, key frame part (§9.9–§9.11, §13.4). -/
structure EntropyHdr where
  /-- `coeff_probs[4][8][3][11]`, flattened -/
  coeffProbs : Array Nat
  coeffSkipEnabled : Bool
  coeffSkipProb : Nat

section
variable (P : Prims)

/-- `decode_segmentation_header` for a key frame (§9.3, §19.2). -/
def decodeSegmentationHeader : BoolM SegmentHdr := do
  -- key frame: memset(hdr, 0, sizeof(*hdr))
  let mut hdr : SegmentHdr :=
    { enabled := false, updateData := false, updateMap := false, abs := false,
      treeProbs := #[0, 0, 0], lfLevel := #[0, 0, 0, 0], quantIdx := #[0, 0, 0, 0] }
  let enabled ← getBit P
  hdr := { hdr with enabled }
  if enabled then
    let updateMap ← getBit P
    let updateData ← getBit P
    hdr := { hdr with updateMap, updateData }
    if updateData then
      let abs ← getBit P
      let mut quantIdx : Array Int := #[]
      for _ in [0:4] do quantIdx := quantIdx.push (← maybeGetInt P 7)
      let mut lfLevel : Array Int := #[]
      for _ in [0:4] do lfLevel := lfLevel.push (← maybeGetInt P 6)
      hdr := { hdr with abs, quantIdx, lfLevel }
    if updateMap then
      let mut treeProbs : Array Nat := #[]
      for _ in [0:3] do
        treeProbs := treeProbs.push (← if ← getBit P then getUint P 8 else pure 255)
      hdr := { hdr with treeProbs }
  else
    hdr := { hdr with updateMap := false, updateData := false }
  return hdr

/-- `decode_loopfilter_header` for a key frame (§9.6). -/
def decodeLoopfilterHeader : BoolM LoopFilterHdr := do
  -- key frame: memset(hdr, 0, sizeof(*hdr))
  let useSimple ← getBit P
  let level ← getUint P 6
  let sharpness ← getUint P 3
  let deltaEnabled ← getBit P
  let mut refDelta : Array Int := #[0, 0, 0, 0]
  let mut modeDelta : Array Int := #[0, 0, 0, 0]
  -- `if (hdr->delta_enabled && bool_get_bit(bool))`
  if deltaEnabled then
    if ← getBit P then
      refDelta := #[]
      for _ in [0:4] do refDelta := refDelta.push (← maybeGetInt P 6)
      modeDelta := #[]
      for _ in [0:4] do modeDelta := modeDelta.push (← maybeGetInt P 6)
  return { useSimple, level, sharpness, deltaEnabled, refDelta, modeDelta }

/-- `decode_quantizer_header` (§9.6) with `last_q = 0` (fresh context). -/
def decodeQuantizerHeader : BoolM QuantHdr := do
  let lastQ := 0
  let qIndex ← getUint P 7
  let y1DcDeltaQ ← maybeGetInt P 4
  let y2DcDeltaQ ← maybeGetInt P 4
  let y2AcDeltaQ ← maybeGetInt P 4
  let uvDcDeltaQ ← maybeGetInt P 4
  let uvAcDeltaQ ← maybeGetInt P 4
  -- `update = last_q != q_index; update |= (delta = …)` for each of the five deltas
  let deltaUpdate := lastQ ≠ qIndex ∨ y1DcDeltaQ ≠ 0 ∨ y2DcDeltaQ ≠ 0 ∨ y2AcDeltaQ ≠ 0 ∨
    uvDcDeltaQ ≠ 0 ∨ uvAcDeltaQ ≠ 0
  return { qIndex, deltaUpdate, y1DcDeltaQ, y2DcDeltaQ, y2AcDeltaQ, uvDcDeltaQ, uvAcDeltaQ }

/-- `decode_reference_header` for a key frame (§9.7, §9.8): the only bit read is
`refresh_entropy_probs`, which is returned. (`refresh_gf = refresh_arf = refresh_last = 1`,
`copy_gf = copy_arf = 0`, `sign_bias = 0` are not read on key frames.) -/
def decodeReferenceHeader : BoolM Bool := getBit P

/-- `decode_entropy_header` for a key frame (§9.9, §9.11, §13.4), starting from the default
coefficient probabilities `k_default_coeff_probs` (copied for every key frame in
`decode_frame`). -/
def decodeEntropyHeader : BoolM EntropyHdr := do
  let mut coeffProbs := Tables.kDefaultCoeffProbs
  -- for i < BLOCK_TYPES, j < COEFF_BANDS, k < PREV_COEFF_CONTEXTS, l < ENTROPY_NODES
  for n in [0:4 * 8 * 3 * 11] do
    if ← get P (Tables.kCoeffEntropyUpdateProbs.getD n 0) then
      coeffProbs := coeffProbs.setIfInBounds n (← getUint P 8)
  let coeffSkipEnabled ← getBit P
  -- `coeff_skip_prob` keeps its zero-initialised value when not enabled
  let coeffSkipProb ← if coeffSkipEnabled then getUint P 8 else pure 0
  return { coeffProbs, coeffSkipEnabled, coeffSkipProb }

end

/-- The data partitions (§9.5): `(offset, size)` of each token partition in the frame buffer. -/
abbrev Partitions := Array (Nat × Nat)

/-- `decode_and_init_token_partitions`, after `partitions = 1 << bool_get_uint(bool, 2)` has been
read: `off` is the offset of the partition sizes (right after the first partition) and `sz` the
number of bytes from there to the end of the frame. -/
def tokenPartitions (data : ByteArray) (numPartitions off sz : Nat) :
    Except String Partitions := do
  if sz < 3 * (numPartitions - 1) then
    throw "VP8: corrupt frame (truncated packet found parsing partition lengths)"
  let mut sz := sz - 3 * (numPartitions - 1)
  let mut sizes : Array Nat := #[]
  for i in [0:numPartitions] do
    let psz :=
      if i < numPartitions - 1 then
        let p := off + 3 * i
        ((byteAt data (p + 2)).toNat <<< 16) ||| ((byteAt data (p + 1)).toNat <<< 8) |||
          (byteAt data p).toNat
      else sz
    if sz < psz then throw s!"VP8: corrupt frame (truncated partition {i})"
    sz := sz - psz
    sizes := sizes.push psz
  -- the partitions follow the 3-byte sizes, in order
  let mut start := off + 3 * (numPartitions - 1)
  let mut parts : Partitions := #[]
  for psz in sizes do
    parts := parts.push (start, psz)
    start := start + psz
  return parts

/-! ## Dequantization factors (§9.6, §14.1; `dequant_init`) -/

/-- `clamp_q` -/
def clampQ (q : Int) : Nat := if q < 0 then 0 else if q > 127 then 127 else q.toNat

/-- `dc_q` -/
def dcQ (q : Int) : Int := Tables.dcQLookup.getD (clampQ q) 0
/-- `ac_q` -/
def acQ (q : Int) : Int := Tables.acQLookup.getD (clampQ q) 0

/-- `struct dequant_factors`: `factor[TOKEN_BLOCK_Y1 = 0 | TOKEN_BLOCK_UV = 1 |
TOKEN_BLOCK_Y2 = 2][DC = 0 | AC = 1]`, flattened to `factor[2 * type + i]`. -/
structure DequantFactors where
  quantIdx : Int
  factor : Array Int

/-- C `/` on `int` (truncating division). -/
@[inline] def cdiv (a b : Int) : Int := a.tdiv b

/-- `dequant_init(factors, seg, quant_hdr)`, starting from the fresh-context cache
(`quant_idx = -1`, factors zero). **Note** (a property of the reference decoder, transcribed
as is): a segment whose quantizer index `q` is `-1` keeps all-zero factors unless one of the
quantizer deltas is non-zero or `q_index ≠ 0` (`delta_update`). -/
def dequantInit (seg : SegmentHdr) (quant : QuantHdr) : Array DequantFactors := Id.run do
  let mut out : Array DequantFactors := #[]
  for i in [0:4] do
    -- dequant_global_init + zero-initialised context
    let mut dqf : DequantFactors := { quantIdx := -1, factor := #[0, 0, 0, 0, 0, 0] }
    if i < (if seg.enabled then 4 else 1) then
      let mut q : Int := quant.qIndex
      if seg.enabled then
        q := if !seg.abs then q + seg.quantIdx.getD i 0 else seg.quantIdx.getD i 0
      if dqf.quantIdx ≠ q ∨ quant.deltaUpdate then
        let y1dc := dcQ (q + quant.y1DcDeltaQ)
        let y1ac := acQ q
        let uvdc := dcQ (q + quant.uvDcDeltaQ)
        let uvac := acQ (q + quant.uvAcDeltaQ)
        let y2dc := dcQ (q + quant.y2DcDeltaQ) * 2
        let y2ac := cdiv (acQ (q + quant.y2AcDeltaQ) * 155) 100
        let y2ac := if y2ac < 8 then 8 else y2ac
        let uvdc := if uvdc > 132 then 132 else uvdc
        dqf := { quantIdx := q, factor := #[y1dc, y1ac, uvdc, uvac, y2dc, y2ac] }
    out := out.push dqf
  return out

end WebP.Spec.VP8
