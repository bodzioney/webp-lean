import WebP.Spec.VP8.IdctAdd
/-!
# Intra prediction and reconstruction (RFC 6386 §12, §14.5; reference source §20.14 `predict.c`)

Transcription of the intra-prediction part of `predict.c`: the predictors `predict_*_nxn` and
`predict_*_4x4`, `copy_down`, `b_pred`, `fixup_dc_coeffs`, `predict_intra_luma`,
`predict_intra_chroma`, `fixup_left`, `fixup_above` and `vp8_dixie_predict_process_row`
(key frames: every macroblock is intra coded).

The reference decoder predicts directly into the frame buffer, which has a border of
`BORDER_PIXELS = 16` pixels around the (macroblock-aligned) luma plane and 8 around the chroma
planes (`vpx_img_alloc` + `vpx_img_set_rect(img, 16, 16, w, h)`). The out-of-frame pixels used by
the predictors (127 above the frame, 129 left of it, and the DC-mode edge cases) are written into
that border by `fixup_left` / `fixup_above` just before a macroblock is predicted, and the four
pixels above and to the right of the last macroblock of a row are made by replicating the last
pixel (end of `vp8_dixie_predict_process_row`). Every pixel the predictors read has been
written before, so the initial content of the buffer is irrelevant (we start from zeros).

A plane is a `ByteArray` with a stride; positions are indices ("pointers") into it.
-/
namespace WebP.Spec.VP8

/-- `BORDER_PIXELS` -/
def BORDER_PIXELS : Nat := 16

/-- Geometry of the frame buffer (`ctx->ref_frames[CURRENT_FRAME]->img`). -/
structure Geom where
  /-- `stride[PLANE_Y]` -/
  stride : Nat
  /-- `stride[PLANE_U] = stride[PLANE_V]` -/
  uvStride : Nat
  /-- index of the first visible luma pixel (`planes[PLANE_Y]`) -/
  yOrigin : Nat
  /-- index of the first visible chroma pixel (`planes[PLANE_U]`, `planes[PLANE_V]`) -/
  uvOrigin : Nat

/-- The three planes of the frame buffer. -/
structure Img where
  y : ByteArray
  u : ByteArray
  v : ByteArray

/-- A zero-filled byte buffer. -/
def zeros (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push 0
  return b

/-- The frame buffer `vp8_dixie_predict_init` allocates for an `mbCols × mbRows` frame:
`vpx_img_alloc(img, IMG_FMT_I420, w, h, 16)` with `w = mb_cols * 16 + 2 * BORDER_PIXELS`,
`h = mb_rows * 16 + 2 * BORDER_PIXELS` (planar I420: luma stride `w`, which is already a multiple
of 16, chroma stride `w / 2`, chroma height `h / 2`), then `vpx_img_set_rect(img, 16, 16, …)`
(the chroma origin is at `(8, 8)`). -/
def Geom.ofMbs (mbCols : Nat) : Geom :=
  let stride := mbCols * 16 + 2 * BORDER_PIXELS
  let uvStride := stride / 2
  { stride, uvStride,
    yOrigin := BORDER_PIXELS + BORDER_PIXELS * stride,
    uvOrigin := BORDER_PIXELS / 2 + BORDER_PIXELS / 2 * uvStride }

/-- The (zero-filled) planes of the frame buffer. -/
def Img.alloc (mbCols mbRows : Nat) : Img :=
  let g := Geom.ofMbs mbCols
  let h := mbRows * 16 + 2 * BORDER_PIXELS
  { y := zeros (h * g.stride), u := zeros (h / 2 * g.uvStride), v := zeros (h / 2 * g.uvStride) }

/-! ## Predictors (§12.2, §12.3). `p` points at the top-left pixel of the block. -/

/-- `predict_h_nxn` -/
def predictHNxn (b : ByteArray) (p stride n : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:n] do
    let l := px b (p - 1 + i * stride)
    for j in [0:n] do
      b := setPx b (p + i * stride + j) l
  return b

/-- `predict_v_nxn` -/
def predictVNxn (b : ByteArray) (p stride n : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:n] do
    for j in [0:n] do
      b := setPx b (p + i * stride + j) (px b (p - stride + j))
  return b

/-- `predict_tm_nxn` -/
def predictTmNxn (b : ByteArray) (p stride n : Nat) : ByteArray := Id.run do
  let above := p - stride
  let pp := px b (above - 1)
  let mut b := b
  for j in [0:n] do
    let row := p + j * stride
    let l := px b (row - 1)
    for i in [0:n] do
      b := setPx b (row + i) (clamp255 (l + px b (above + i) - pp))
  return b

/-- `predict_dc_nxn` -/
def predictDcNxn (b : ByteArray) (p stride n : Nat) : ByteArray := Id.run do
  let mut sum : Int := 0
  for i in [0:n] do
    sum := sum + px b (p - 1 + i * stride) + px b (p - stride + i)
  let dc :=
    if n = 16 then (sum + 16) >>> 5
    else if n = 8 then (sum + 8) >>> 4
    else if n = 4 then (sum + 4) >>> 3
    else sum
  let mut b := b
  for i in [0:n] do
    for j in [0:n] do
      b := setPx b (p + i * stride + j) dc
  return b

/-- The pixels around a 4×4 sub-block at `p`: `above[-1..7]` at indices `0..8` and
`left[0], left[stride], left[2*stride], left[3*stride]` at indices `9..12`. -/
def edges4x4 (b : ByteArray) (p stride : Nat) : Array Int :=
  let a := p - stride - 1
  let l := p - 1
  #[px b a, px b (a + 1), px b (a + 2), px b (a + 3), px b (a + 4), px b (a + 5), px b (a + 6),
    px b (a + 7), px b (a + 8),
    px b l, px b (l + stride), px b (l + 2 * stride), px b (l + 3 * stride)]

/-- Write the 4×4 block `vals` (row-major) at `p`. -/
def put4x4 (b : ByteArray) (p stride : Nat) (vals : Array Int) : ByteArray := Id.run do
  let mut b := b
  for r in [0:4] do
    for c in [0:4] do
      b := setPx b (p + r * stride + c) (vals.getD (4 * r + c) 0)
  return b

/-- The values of the 4×4 sub-block predictors `predict_{ve,he,ld,rd,vr,vl,hd,hu}_4x4`
(row-major), from the surrounding pixels `e = edges4x4 …`. The pixels above (`above[-1..7]`)
and to the left (`left[0..3*stride]`) are outside the block, so the reference code's
interleaving of reads and writes does not matter. -/
def predict4x4Vals (e : Array Int) (mode : Nat) : Array Int :=
  let A (k : Int) : Int := e.getD (k + 1).toNat 0   -- above[k], k ∈ [-1, 7]
  let L (k : Nat) : Int := e.getD (9 + k) 0          -- left[k * stride], k ∈ [0, 3]
  let avg3 (x y z : Int) : Int := (x + 2 * y + z + 2) >>> 2
  let avg2 (x y : Int) : Int := (x + y + 1) >>> 1
  match mode with
  | 2 => -- B_VE_PRED: predict[j] = (above[j-1] + 2 * above[j] + above[j+1] + 2) >> 2, all rows
    let v0 := avg3 (A (-1)) (A 0) (A 1)
    let v1 := avg3 (A 0) (A 1) (A 2)
    let v2 := avg3 (A 1) (A 2) (A 3)
    let v3 := avg3 (A 2) (A 3) (A 4)
    #[v0, v1, v2, v3, v0, v1, v2, v3, v0, v1, v2, v3, v0, v1, v2, v3]
  | 3 => -- B_HE_PRED (left[-stride] = above[-1])
    let r0 := avg3 (A (-1)) (L 0) (L 1)
    let r1 := avg3 (L 0) (L 1) (L 2)
    let r2 := avg3 (L 1) (L 2) (L 3)
    let r3 := avg3 (L 2) (L 3) (L 3)   -- (left[-stride] + 2 * left[0] + left[0] + 2) >> 2
    #[r0, r0, r0, r0, r1, r1, r1, r1, r2, r2, r2, r2, r3, r3, r3, r3]
  | 4 => -- B_LD_PRED
    let pred0 := avg3 (A 0) (A 1) (A 2)
    let pred1 := avg3 (A 1) (A 2) (A 3)
    let pred2 := avg3 (A 2) (A 3) (A 4)
    let pred3 := avg3 (A 3) (A 4) (A 5)
    let pred4 := avg3 (A 4) (A 5) (A 6)
    let pred5 := avg3 (A 5) (A 6) (A 7)
    let pred6 := avg3 (A 6) (A 7) (A 7)
    #[pred0, pred1, pred2, pred3,
      pred1, pred2, pred3, pred4,
      pred2, pred3, pred4, pred5,
      pred3, pred4, pred5, pred6]
  | 5 => -- B_RD_PRED
    let pred0 := avg3 (L 0) (A (-1)) (A 0)
    let pred1 := avg3 (A (-1)) (A 0) (A 1)
    let pred2 := avg3 (A 0) (A 1) (A 2)
    let pred3 := avg3 (A 1) (A 2) (A 3)
    let pred4 := avg3 (L 1) (L 0) (A (-1))
    let pred5 := avg3 (L 2) (L 1) (L 0)
    let pred6 := avg3 (L 3) (L 2) (L 1)
    #[pred0, pred1, pred2, pred3,
      pred4, pred0, pred1, pred2,
      pred5, pred4, pred0, pred1,
      pred6, pred5, pred4, pred0]
  | 6 => -- B_VR_PRED
    let pred0 := avg2 (A (-1)) (A 0)
    let pred1 := avg2 (A 0) (A 1)
    let pred2 := avg2 (A 1) (A 2)
    let pred3 := avg2 (A 2) (A 3)
    let pred4 := avg3 (L 0) (A (-1)) (A 0)
    let pred5 := avg3 (A (-1)) (A 0) (A 1)
    let pred6 := avg3 (A 0) (A 1) (A 2)
    let pred7 := avg3 (A 1) (A 2) (A 3)
    let pred8 := avg3 (L 1) (L 0) (A (-1))
    let pred9 := avg3 (L 2) (L 1) (L 0)
    #[pred0, pred1, pred2, pred3,
      pred4, pred5, pred6, pred7,
      pred8, pred0, pred1, pred2,
      pred9, pred4, pred5, pred6]
  | 7 => -- B_VL_PRED
    let pred0 := avg2 (A 0) (A 1)
    let pred1 := avg2 (A 1) (A 2)
    let pred2 := avg2 (A 2) (A 3)
    let pred3 := avg2 (A 3) (A 4)
    let pred4 := avg3 (A 0) (A 1) (A 2)
    let pred5 := avg3 (A 1) (A 2) (A 3)
    let pred6 := avg3 (A 2) (A 3) (A 4)
    let pred7 := avg3 (A 3) (A 4) (A 5)
    let pred8 := avg3 (A 4) (A 5) (A 6)
    let pred9 := avg3 (A 5) (A 6) (A 7)
    #[pred0, pred1, pred2, pred3,
      pred4, pred5, pred6, pred7,
      pred1, pred2, pred3, pred8,
      pred5, pred6, pred7, pred9]
  | 8 => -- B_HD_PRED
    let pred0 := avg2 (L 0) (A (-1))
    let pred1 := avg3 (L 0) (A (-1)) (A 0)
    let pred2 := avg3 (A (-1)) (A 0) (A 1)
    let pred3 := avg3 (A 0) (A 1) (A 2)
    let pred4 := avg2 (L 1) (L 0)
    let pred5 := avg3 (L 1) (L 0) (A (-1))
    let pred6 := avg2 (L 2) (L 1)
    let pred7 := avg3 (L 2) (L 1) (L 0)
    let pred8 := avg2 (L 3) (L 2)
    let pred9 := avg3 (L 3) (L 2) (L 1)
    #[pred0, pred1, pred2, pred3,
      pred4, pred5, pred0, pred1,
      pred6, pred7, pred4, pred5,
      pred8, pred9, pred6, pred7]
  | _ => -- 9: B_HU_PRED
    let pred0 := avg2 (L 0) (L 1)
    let pred1 := avg3 (L 0) (L 1) (L 2)
    let pred2 := avg2 (L 1) (L 2)
    let pred3 := avg3 (L 1) (L 2) (L 3)
    let pred4 := avg2 (L 2) (L 3)
    let pred5 := avg3 (L 2) (L 3) (L 3)
    let pred6 := L 3
    #[pred0, pred1, pred2, pred3,
      pred2, pred3, pred4, pred5,
      pred4, pred5, pred6, pred6,
      pred6, pred6, pred6, pred6]

/-- The 4×4 sub-block predictors other than `B_DC_PRED` / `B_TM_PRED` (modes 2–9). -/
def predict4x4 (b : ByteArray) (p stride mode : Nat) : ByteArray :=
  let vals := predict4x4Vals (edges4x4 b p stride) mode
  put4x4 b p stride vals

/-- `copy_down(recon, stride)`: copy the four pixels above-right of sub-block 3 to the
above-right of sub-blocks 7, 11 and 15 (i.e. into rows 3, 7 and 11, columns 16–19). -/
def copyDown (b : ByteArray) (p stride : Nat) : ByteArray := Id.run do
  let src := p + 16 - stride
  let mut b := b
  for k in [1:4] do
    for i in [0:4] do
      b := setPx b (src + 4 * k * stride + i) (px b (src + i))
  return b

/-- `b_pred(predict, stride, mbi, coeffs)`: predict and reconstruct the 16 sub-blocks in
raster order. -/
def bPred (b : ByteArray) (p stride : Nat) (modes : Array Nat) (coeffs : Array Int) :
    ByteArray := Id.run do
  let mut b := copyDown b p stride
  for i in [0:16] do
    let bp := p + (i / 4) * 4 * stride + (i &&& 3) * 4
    let mode := modes.getD i 0
    b := if mode = B_DC_PRED then predictDcNxn b bp stride 4
      else if mode = B_TM_PRED then predictTmNxn b bp stride 4
      else predict4x4 b bp stride mode
    b := idctAdd b bp stride coeffs (16 * i)
  return b

/-- `fixup_dc_coeffs(mbi, coeffs)`: the inverse WHT of the Y2 block (block 24) gives the DC
coefficients of the 16 luma blocks. -/
def fixupDcCoeffs (coeffs : Array Int) : Array Int := Id.run do
  let y2 := walsh coeffs (24 * 16)
  let mut coeffs := coeffs
  for i in [0:16] do
    coeffs := coeffs.setIfInBounds (i * 16) (y2.getD i 0)
  return coeffs

/-- `predict_intra_luma(predict, stride, mbi, coeffs)`. -/
def predictIntraLuma (b : ByteArray) (p stride : Nat) (mbi : MbInfo) (coeffs : Array Int) :
    ByteArray := Id.run do
  if mbi.yMode = B_PRED then return bPred b p stride mbi.modes coeffs
  let mut b :=
    if mbi.yMode = DC_PRED then predictDcNxn b p stride 16
    else if mbi.yMode = V_PRED then predictVNxn b p stride 16
    else if mbi.yMode = H_PRED then predictHNxn b p stride 16
    else if mbi.yMode = TM_PRED then predictTmNxn b p stride 16
    else b
  let coeffs := fixupDcCoeffs coeffs
  for i in [0:16] do
    b := idctAdd b (p + (i / 4) * 4 * stride + (i % 4) * 4) stride coeffs (16 * i)
  return b

/-- One chroma plane of `predict_intra_chroma`: blocks `first … first + 3` of `coeffs`. -/
def predictIntraChromaPlane (b : ByteArray) (p stride : Nat) (uvMode : Nat) (coeffs : Array Int)
    (first : Nat) : ByteArray := Id.run do
  let mut b :=
    if uvMode = DC_PRED then predictDcNxn b p stride 8
    else if uvMode = V_PRED then predictVNxn b p stride 8
    else if uvMode = H_PRED then predictHNxn b p stride 8
    else if uvMode = TM_PRED then predictTmNxn b p stride 8
    else b
  for i in [0:4] do
    b := idctAdd b (p + (i / 2) * 4 * stride + (i % 2) * 4) stride coeffs (16 * (first + i))
  return b

/-- `fixup_left(predict, width, stride, row, mode)`: the column left of the frame is 129,
except for `DC_PRED` below the first row, where it is a copy of the row above (so that the
DC predictor averages the above row only). -/
def fixupLeft (b : ByteArray) (p width stride row mode : Nat) : ByteArray := Id.run do
  let mut b := b
  if mode = DC_PRED ∧ row ≠ 0 then
    for i in [0:width] do
      b := setPx b (p - 1 + i * stride) (px b (p - stride + i))
  else
    -- also the pixel above-left ("in case the above MB was DC_PRED")
    b := setPx b (p - 1 - stride) 129
    for i in [0:width] do
      b := setPx b (p - 1 + i * stride) 129
  return b

/-- `fixup_above(predict, width, stride, col, mode)`: the row above the frame is 127, except
for `DC_PRED` right of the first column, where it is a copy of the left column; the four pixels
above-right are 127. -/
def fixupAbove (b : ByteArray) (p width stride col mode : Nat) : ByteArray := Id.run do
  let above := p - stride
  let mut b := b
  if mode = DC_PRED ∧ col ≠ 0 then
    for i in [0:width] do
      b := setPx b (above + i) (px b (p - 1 + i * stride))
  else
    -- memset(above - 1, 127, width + 1)
    for i in [0:width + 1] do
      b := setPx b (above - 1 + i) 127
  -- memset(above + width, 127, 4): for above-right subblock modes
  for i in [0:4] do
    b := setPx b (above + width + i) 127
  return b

/-- `vp8_dixie_predict_process_row(ctx, row, 0, mb_cols)` for a key frame: predict and
reconstruct one macroblock row into the frame buffer. `coeffs[col]` are the coefficients of the
macroblocks of the row (`tokens[row & (partitions - 1)].coeffs`). -/
def predictProcessRow (g : Geom) (y u v : ByteArray) (row : Nat) (mbi : Array MbInfo)
    (coeffs : Array (Array Int)) : Img := Id.run do
  let stride := g.stride
  let uvStride := g.uvStride
  let mut y := y
  let mut u := u
  let mut v := v
  let py0 := g.yOrigin + stride * row * 16
  let puv0 := g.uvOrigin + uvStride * row * 8
  -- Fix up the out-of-frame pixels (start_col == 0)
  let m0 := mbi.getD 0 MbInfo.zero
  y := fixupLeft y py0 16 stride row m0.yMode
  u := fixupLeft u puv0 8 uvStride row m0.uvMode
  v := fixupLeft v puv0 8 uvStride row m0.uvMode
  if row = 0 then y := setPx y (py0 - stride - 1) 127
  for h : col in [0:mbi.size] do
    let m := mbi[col]
    let py := py0 + 16 * col
    let puv := puv0 + 8 * col
    if row = 0 then
      y := fixupAbove y py 16 stride col m.yMode
      u := fixupAbove u puv 8 uvStride col m.uvMode
      v := fixupAbove v puv 8 uvStride col m.uvMode
    -- y_mode <= B_PRED: always the case on key frames
    let c := coeffs.getD col #[]
    y := predictIntraLuma y py stride m c
    u := predictIntraChromaPlane u puv uvStride m.uvMode c 16
    v := predictIntraChromaPlane v puv uvStride m.uvMode c 20
  -- "Extend the last row by four pixels for intra-prediction. This will be propagated later by
  -- copy_down." (img.y now points just right of the last macroblock).
  -- `*(uint32_t *)extend = 0x01010101 * pixel`: **[interp]** the `int` product overflows (formally
  -- undefined) when `pixel ≥ 128`; it is read as the intended four copies of the pixel.
  let pe := py0 + 16 * mbi.size + 15 * stride
  let val := px y (pe - 1)
  for i in [0:4] do
    y := setPx y (pe + i) val
  return ⟨y, u, v⟩

end WebP.Spec.VP8
