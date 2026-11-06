import WebP.Spec.VP8.Predict
/-!
# Loop filter (RFC 6386 §15; reference source §20.6 `dixie_loopfilter.c`)

Transcription of `dixie_loopfilter.c`: the per-pixel filters (`filter_common`,
`filter_mb_edge`, thresholds), the edge loops, `calculate_filter_parameters` (key frame:
`ref_frame = CURRENT_FRAME`, the only mode delta that applies is `mode_delta[0]` for `B_PRED`),
`filter_row_normal`, `filter_row_simple` and `vp8_dixie_loopfilter_process_row`.

A pixel position `s` addresses `q0`, the first pixel after the edge; `step` is the distance
between pixels across the edge (`1` for a vertical edge, the stride for a horizontal one). C
`int` arithmetic on promoted `unsigned char`s is done in `Int`; `>>` is an arithmetic shift.
-/
namespace WebP.Spec.VP8

/-- `ABS` -/
@[inline] def iabs (x : Int) : Int := if x ≥ 0 then x else -x

/-- `saturate_int8` -/
@[inline] def saturateInt8 (x : Int) : Int := if x < -128 then -128 else if x > 127 then 127 else x

/-- `saturate_uint8` -/
@[inline] def saturateUint8 (x : Int) : Int := if x < 0 then 0 else if x > 255 then 255 else x

/-- `p3 … q3` around the edge at `s`. -/
@[inline] def p3 (b : ByteArray) (s step : Nat) : Int := px b (s - 4 * step)
@[inline] def p2 (b : ByteArray) (s step : Nat) : Int := px b (s - 3 * step)
@[inline] def p1 (b : ByteArray) (s step : Nat) : Int := px b (s - 2 * step)
@[inline] def p0 (b : ByteArray) (s step : Nat) : Int := px b (s - step)
@[inline] def q0 (b : ByteArray) (s _step : Nat) : Int := px b s
@[inline] def q1 (b : ByteArray) (s step : Nat) : Int := px b (s + step)
@[inline] def q2 (b : ByteArray) (s step : Nat) : Int := px b (s + 2 * step)
@[inline] def q3 (b : ByteArray) (s step : Nat) : Int := px b (s + 3 * step)

/-- `high_edge_variance` -/
def highEdgeVariance (b : ByteArray) (s step : Nat) (hevThreshold : Int) : Bool :=
  iabs (p1 b s step - p0 b s step) > hevThreshold ∨ iabs (q1 b s step - q0 b s step) > hevThreshold

/-- `simple_threshold` -/
def simpleThreshold (b : ByteArray) (s step : Nat) (filterLimit : Int) : Bool :=
  iabs (p0 b s step - q0 b s step) * 2 + (iabs (p1 b s step - q1 b s step) >>> 1) ≤ filterLimit

/-- `normal_threshold` -/
def normalThreshold (b : ByteArray) (s step : Nat) (E I : Int) : Bool :=
  simpleThreshold b s step (2 * E + I)
    ∧ iabs (p3 b s step - p2 b s step) ≤ I ∧ iabs (p2 b s step - p1 b s step) ≤ I
    ∧ iabs (p1 b s step - p0 b s step) ≤ I ∧ iabs (q3 b s step - q2 b s step) ≤ I
    ∧ iabs (q2 b s step - q1 b s step) ≤ I ∧ iabs (q1 b s step - q0 b s step) ≤ I

/-- `filter_common(pixels, stride, use_outer_taps)` -/
def filterCommon (b : ByteArray) (s step : Nat) (useOuterTaps : Bool) : ByteArray := Id.run do
  let P1 := p1 b s step; let P0 := p0 b s step; let Q0 := q0 b s step; let Q1 := q1 b s step
  let mut a0 := 3 * (Q0 - P0)
  if useOuterTaps then a0 := a0 + saturateInt8 (P1 - Q1)
  let a := saturateInt8 a0
  let f1 := (if a + 4 > 127 then 127 else a + 4) >>> 3
  let f2 := (if a + 3 > 127 then 127 else a + 3) >>> 3
  let mut b := setPx b (s - step) (saturateUint8 (P0 + f2))
  b := setPx b s (saturateUint8 (Q0 - f1))
  if !useOuterTaps then
    -- "This handles the case of subblock_filter() (from the bitstream guide)"
    let a' := (f1 + 1) >>> 1
    b := setPx b (s - 2 * step) (saturateUint8 (P1 + a'))
    b := setPx b (s + step) (saturateUint8 (Q1 - a'))
  return b

/-- `filter_mb_edge(pixels, stride)` -/
def filterMbEdge (b : ByteArray) (s step : Nat) : ByteArray :=
  let P2 := p2 b s step; let P1 := p1 b s step; let P0 := p0 b s step
  let Q0 := q0 b s step; let Q1 := q1 b s step; let Q2 := q2 b s step
  let w := saturateInt8 (saturateInt8 (P1 - Q1) + 3 * (Q0 - P0))
  let a := (27 * w + 63) >>> 7
  let b := setPx b (s - step) (saturateUint8 (P0 + a))
  let b := setPx b s (saturateUint8 (Q0 - a))
  let a := (18 * w + 63) >>> 7
  let b := setPx b (s - 2 * step) (saturateUint8 (P1 + a))
  let b := setPx b (s + step) (saturateUint8 (Q1 - a))
  let a := (9 * w + 63) >>> 7
  let b := setPx b (s - 3 * step) (saturateUint8 (P2 + a))
  setPx b (s + 2 * step) (saturateUint8 (Q2 - a))

/-- `filter_mb_v_edge` (`across = 1`, `along = stride`) and `filter_mb_h_edge`
(`across = stride`, `along = 1`): `8 * size` pixels along the edge starting at `src`. -/
def filterMbEdgeLoop (b : ByteArray) (src across along : Nat) (edgeLimit interiorLimit hevThreshold : Int)
    (size : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8 * size] do
    let s := src + i * along
    if normalThreshold b s across edgeLimit interiorLimit then
      if highEdgeVariance b s across hevThreshold then
        b := filterCommon b s across true
      else
        b := filterMbEdge b s across
  return b

/-- `filter_subblock_v_edge` / `filter_subblock_h_edge`. -/
def filterSubblockEdgeLoop (b : ByteArray) (src across along : Nat)
    (edgeLimit interiorLimit hevThreshold : Int) (size : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8 * size] do
    let s := src + i * along
    if normalThreshold b s across edgeLimit interiorLimit then
      b := filterCommon b s across (highEdgeVariance b s across hevThreshold)
  return b

/-- `filter_v_edge_simple` / `filter_h_edge_simple`: 16 pixels along the edge. -/
def filterSimpleEdgeLoop (b : ByteArray) (src across along : Nat) (filterLimit : Int) :
    ByteArray := Id.run do
  let mut b := b
  for i in [0:16] do
    let s := src + i * along
    if simpleThreshold b s across filterLimit then
      b := filterCommon b s across true
  return b

/-- Filter parameters of a macroblock: `(edge_limit, interior_limit, hev_threshold)`. -/
structure FilterParams where
  edgeLimit : Int
  interiorLimit : Int
  hevThreshold : Int

/-- `calculate_filter_parameters(ctx, mbi, …)` for a key frame. -/
def calculateFilterParameters (seg : SegmentHdr) (lf : LoopFilterHdr) (mbi : MbInfo) :
    FilterParams := Id.run do
  -- "Reference code/spec seems to conflate filter_level and edge_limit"
  let mut filterLevel : Int := lf.level
  if seg.enabled then
    if !seg.abs then filterLevel := filterLevel + seg.lfLevel.getD mbi.segmentId 0
    else filterLevel := seg.lfLevel.getD mbi.segmentId 0
  if filterLevel > 63 then filterLevel := 63
  else if filterLevel < 0 then filterLevel := 0
  if lf.deltaEnabled then
    -- ref_frame == CURRENT_FRAME (intra)
    filterLevel := filterLevel + lf.refDelta.getD 0 0
    if mbi.yMode = B_PRED then filterLevel := filterLevel + lf.modeDelta.getD 0 0
  if filterLevel > 63 then filterLevel := 63
  else if filterLevel < 0 then filterLevel := 0
  let mut interiorLimit := filterLevel
  if lf.sharpness ≠ 0 then
    interiorLimit := interiorLimit >>> (if lf.sharpness > 4 then 2 else 1)
    if interiorLimit > 9 - (lf.sharpness : Int) then interiorLimit := 9 - (lf.sharpness : Int)
  if interiorLimit < 1 then interiorLimit := 1
  let mut hevThreshold : Int := if filterLevel ≥ 15 then 1 else 0
  if filterLevel ≥ 40 then hevThreshold := hevThreshold + 1
  -- `filter_level >= 20 && !is_keyframe`: not on key frames
  return { edgeLimit := filterLevel, interiorLimit, hevThreshold }

/-- `filter_row_normal(ctx, row, 0, mb_cols)` -/
def filterRowNormal (g : Geom) (y u v : ByteArray) (seg : SegmentHdr) (lf : LoopFilterHdr)
    (row : Nat) (mbi : Array MbInfo) : Img := Id.run do
  let stride := g.stride
  let uvStride := g.uvStride
  let mut y := y
  let mut u := u
  let mut v := v
  for h : col in [0:mbi.size] do
    let m := mbi[col]
    let py := g.yOrigin + (stride * row + col) * 16
    let pu := g.uvOrigin + (uvStride * row + col) * 8
    let fp := calculateFilterParameters seg lf m
    let E := fp.edgeLimit; let I := fp.interiorLimit; let H := fp.hevThreshold
    if E ≠ 0 then
      if col ≠ 0 then
        y := filterMbEdgeLoop y py 1 stride (E + 2) I H 2
        u := filterMbEdgeLoop u pu 1 uvStride (E + 2) I H 1
        v := filterMbEdgeLoop v pu 1 uvStride (E + 2) I H 1
      -- "This conditional is actually dependent on the number of coefficients decoded, not
      -- the skip flag as coded in the bitstream."
      if m.eobMask ≠ 0 ∨ m.yMode = B_PRED then
        y := filterSubblockEdgeLoop y (py + 4) 1 stride E I H 2
        y := filterSubblockEdgeLoop y (py + 8) 1 stride E I H 2
        y := filterSubblockEdgeLoop y (py + 12) 1 stride E I H 2
        u := filterSubblockEdgeLoop u (pu + 4) 1 uvStride E I H 1
        v := filterSubblockEdgeLoop v (pu + 4) 1 uvStride E I H 1
      if row ≠ 0 then
        y := filterMbEdgeLoop y py stride 1 (E + 2) I H 2
        u := filterMbEdgeLoop u pu uvStride 1 (E + 2) I H 1
        v := filterMbEdgeLoop v pu uvStride 1 (E + 2) I H 1
      if m.eobMask ≠ 0 ∨ m.yMode = B_PRED then
        y := filterSubblockEdgeLoop y (py + 4 * stride) stride 1 E I H 2
        y := filterSubblockEdgeLoop y (py + 8 * stride) stride 1 E I H 2
        y := filterSubblockEdgeLoop y (py + 12 * stride) stride 1 E I H 2
        u := filterSubblockEdgeLoop u (pu + 4 * uvStride) uvStride 1 E I H 1
        v := filterSubblockEdgeLoop v (pu + 4 * uvStride) uvStride 1 E I H 1
  return ⟨y, u, v⟩

/-- `filter_row_simple(ctx, row, 0, mb_cols)` (luma only). -/
def filterRowSimple (g : Geom) (y : ByteArray) (seg : SegmentHdr) (lf : LoopFilterHdr)
    (row : Nat) (mbi : Array MbInfo) : ByteArray := Id.run do
  let stride := g.stride
  let mut y := y
  for h : col in [0:mbi.size] do
    let m := mbi[col]
    let py := g.yOrigin + (stride * row + col) * 16
    let fp := calculateFilterParameters seg lf m
    let E := fp.edgeLimit; let I := fp.interiorLimit
    if E ≠ 0 then
      let filterSubblocks := m.eobMask ≠ 0 ∨ m.yMode = B_PRED
      let mbLimit := (E + 2) * 2 + I
      let bLimit := E * 2 + I
      if col ≠ 0 then y := filterSimpleEdgeLoop y py 1 stride mbLimit
      if filterSubblocks then
        y := filterSimpleEdgeLoop y (py + 4) 1 stride bLimit
        y := filterSimpleEdgeLoop y (py + 8) 1 stride bLimit
        y := filterSimpleEdgeLoop y (py + 12) 1 stride bLimit
      if row ≠ 0 then y := filterSimpleEdgeLoop y py stride 1 mbLimit
      if filterSubblocks then
        y := filterSimpleEdgeLoop y (py + 4 * stride) stride 1 bLimit
        y := filterSimpleEdgeLoop y (py + 8 * stride) stride 1 bLimit
        y := filterSimpleEdgeLoop y (py + 12 * stride) stride 1 bLimit
  return y

/-- `vp8_dixie_loopfilter_process_row(ctx, row, 0, mb_cols)` -/
def loopfilterProcessRow (g : Geom) (y u v : ByteArray) (seg : SegmentHdr)
    (lf : LoopFilterHdr) (row : Nat) (mbi : Array MbInfo) : Img :=
  if lf.useSimple then ⟨filterRowSimple g y seg lf row mbi, u, v⟩
  else filterRowNormal g y u v seg lf row mbi

end WebP.Spec.VP8
