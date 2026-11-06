import WebP.VP8Libwebp.Header
import WebP.VP8Libwebp.Dsp
import WebP.VP8Libwebp.LoopFilter
import WebP.Spec.VP8.Frame
/-!
# VP8 key frame decoding, libwebp-mimic model (RFC 6386 §11 modes, §13 tokens, §14 reconstruction, §15 filter)

This is NOT the shipped decoder (that is `WebP.VP8.decodeFrame`, proven equal to the RFC 6386
reference decoder `WebP.Spec.VP8.decode`). It is kept as a differential model of libwebp.

Structure follows libwebp `VP8GetHeaders` + `ParseFrame` + `ReconstructRow` + `DoFilter`.

libwebp behaviours reproduced (RFC 6386 is silent or differs):
* The last token partition must be non-empty (`ParsePartitions`); partition sizes larger
  than the remaining data are clamped; a partition whose first byte is `0xff` is rejected.
* Any read past the end of partition 0 or of a token partition (`eof`) fails the decode
  (checked after each macroblock row of modes and after each macroblock of tokens).
* `color_space` and `clamping_type` bits are read and ignored (output is always clamped).
* The `update_proba`/refresh_entropy bit is read and ignored (single key frame).
* Intra prediction uses *unfiltered* neighbours; the loop filter runs afterwards in
  macroblock raster order over the whole (macroblock-padded) frame.
* Coefficients are stored as `int16_t` (products wrap), as in libwebp.
* No dithering (libwebp default `dithering_strength = 0`); horizontal/vertical scale bits
  of the frame header are ignored.
-/
namespace WebP.VP8Libwebp

open WebP.VP8 (Frame)

/-- Zig-zag scan order (RFC 6386 §13.2). -/
def kZigzag : Array Nat := #[0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15]

/-- Offsets of the 16 luma sub-blocks inside the work buffer (`kScan`). -/
def kScan : Array Nat := #[0, 4, 8, 12, 128, 132, 136, 140, 256, 260, 264, 268, 384, 388, 392, 396]

/-- Work buffer layout (libwebp `yuv_b`, stride `BPS = 32`). -/
def Y_OFF : Nat := 32 + 8
def U_OFF : Nat := Y_OFF + 32 * 16 + 32
def V_OFF : Nat := U_OFF + 16
def YUV_SIZE : Nat := 32 * 17 + 32 * 9

/-- Per-macroblock intra mode info. -/
structure MBModes where
  segment : Nat
  skip    : Bool
  isI4    : Bool
  imodes  : Array Nat   -- 16 sub-block modes (i4) or `[ymode]`
  uvmode  : Nat

/-- Parse the intra modes of one macroblock (`ParseIntraMode`, RFC 6386 §11.2–§11.4).
`top` holds 4 sub-block modes per macroblock column, `left` the 4 left modes. -/
def parseIntraMode (br : BoolDec) (seg : SegmentHeader) (useSkip : Bool) (skipP : Nat)
    (top : Array Nat) (left : Array Nat) (mbx : Nat) :
    MBModes × Array Nat × Array Nat × BoolDec := Id.run do
  let mut br := br
  let mut segment := 0
  if seg.updateMap then
    let (b0, b) := br.getBit (seg.segProbs.getD 0 255); br := b
    if !b0 then
      let (b1, b) := br.getBit (seg.segProbs.getD 1 255); br := b
      segment := if b1 then 1 else 0
    else
      let (b1, b) := br.getBit (seg.segProbs.getD 2 255); br := b
      segment := if b1 then 3 else 2
  let mut skip := false
  if useSkip then
    let (s, b) := br.getBit skipP; br := b; skip := s
  let (notI4, b) := br.getBit 145; br := b
  let mut top := top
  let mut left := left
  if notI4 then
    let (b1, b) := br.getBit 156; br := b
    let mut ymode := 0
    if b1 then
      let (b2, b) := br.getBit 128; br := b
      ymode := if b2 then 1 else 3     -- TM_PRED : H_PRED
    else
      let (b2, b) := br.getBit 163; br := b
      ymode := if b2 then 2 else 0     -- V_PRED : DC_PRED
    for i in [0:4] do
      top := top.setIfInBounds (4 * mbx + i) ymode
      left := left.setIfInBounds i ymode
    let (uv, br') := parseUV br
    return ({ segment, skip, isI4 := false, imodes := #[ymode], uvmode := uv }, top, left, br')
  else
    let mut modes : Array Nat := Array.replicate 16 0
    for y in [0:4] do
      let mut ymode := left.getD y 0
      for x in [0:4] do
        let pb := (top.getD (4 * mbx + x) 0 * 10 + ymode) * 9
        let prob (k : Nat) : Nat := rd Tables.bModesProba (pb + k)
        -- hardcoded tree of libwebp (identical to RFC 6386 §11.2 bmode_tree)
        let (c0, b) := br.getBit (prob 0); br := b
        if !c0 then ymode := 0
        else
          let (c1, b) := br.getBit (prob 1); br := b
          if !c1 then ymode := 1
          else
            let (c2, b) := br.getBit (prob 2); br := b
            if !c2 then ymode := 2
            else
              let (c3, b) := br.getBit (prob 3); br := b
              if !c3 then
                let (c4, b) := br.getBit (prob 4); br := b
                if !c4 then ymode := 3
                else
                  let (c5, b) := br.getBit (prob 5); br := b
                  ymode := if !c5 then 4 else 5
              else
                let (c6, b) := br.getBit (prob 6); br := b
                if !c6 then ymode := 6
                else
                  let (c7, b) := br.getBit (prob 7); br := b
                  if !c7 then ymode := 7
                  else
                    let (c8, b) := br.getBit (prob 8); br := b
                    ymode := if !c8 then 8 else 9
        top := top.setIfInBounds (4 * mbx + x) ymode
      for x in [0:4] do
        modes := modes.setIfInBounds (4 * y + x) (top.getD (4 * mbx + x) 0)
      left := left.setIfInBounds y ymode
    let (uv, br') := parseUV br
    return ({ segment, skip, isI4 := true, imodes := modes, uvmode := uv }, top, left, br')
where
  parseUV (br : BoolDec) : Nat × BoolDec :=
    let (u0, br) := br.getBit 142
    if !u0 then (0, br) else
    let (u1, br) := br.getBit 114
    if !u1 then (2, br) else
    let (u2, br) := br.getBit 183
    (if u2 then 1 else 3, br)

/-- `GetLargeValue` (RFC 6386 §13.2 dct_cat tokens). `p` = base index of the 11 probas. -/
def getLargeValue (br : BoolDec) (probas : ByteArray) (p : Nat) : Nat × BoolDec := Id.run do
  let pr (k : Nat) : Nat := rd probas (p + k)
  let mut br := br
  let (b3, b) := br.getBit (pr 3); br := b
  if !b3 then
    let (b4, b) := br.getBit (pr 4); br := b
    if !b4 then return (2, br)
    let (b5, b) := br.getBit (pr 5); br := b
    return (3 + (if b5 then 1 else 0), br)
  let (b6, b) := br.getBit (pr 6); br := b
  if !b6 then
    let (b7, b) := br.getBit (pr 7); br := b
    if !b7 then
      let (x, b) := br.getBit 159; br := b
      return (5 + (if x then 1 else 0), br)
    let (x1, b) := br.getBit 165; br := b
    let (x2, b) := br.getBit 145; br := b
    return (7 + 2 * (if x1 then 1 else 0) + (if x2 then 1 else 0), br)
  let (bit1, b) := br.getBit (pr 8); br := b
  let (bit0, b) := br.getBit (pr (9 + (if bit1 then 1 else 0))); br := b
  let cat := 2 * (if bit1 then 1 else 0) + (if bit0 then 1 else 0)
  let tab : Array Nat := match cat with
    | 0 => #[173, 148, 140]
    | 1 => #[176, 155, 140, 135]
    | 2 => #[180, 157, 141, 134, 130]
    | _ => #[254, 254, 243, 230, 196, 177, 153, 140, 133, 130, 129]
  let mut v := 0
  for t in tab do
    let (x, b) := br.getBit t; br := b
    v := v + v + (if x then 1 else 0)
  return (v + 3 + (8 <<< cat), br)

/-- Base index of the 11 probabilities for type `t`, coefficient position `n`, context `ctx`. -/
@[inline] def probIdx (t n ctx : Nat) : Nat := t * 264 + kBands.getD n 0 * 33 + ctx * 11

/-- `GetCoeffs` (RFC 6386 §13): decode one 4x4 block's tokens starting at position `n0`,
dequantize (`dq0` for position 0, `dq1` otherwise) into `out[base + zigzag n]`.
Returns the index after the last non-zero coefficient (or 16). -/
def getCoeffs (br : BoolDec) (probas : ByteArray) (t ctx : Nat) (dq0 dq1 : Int) (n0 : Nat)
    (out : Array Int) (base : Nat) : Nat × BoolDec × Array Int := Id.run do
  let mut br := br
  let mut out := out
  let mut n := n0
  let mut p := probIdx t n ctx
  while n < 16 do
    let (b0, b) := br.getBit (rd probas p); br := b
    if !b0 then return (n, br, out)
    -- run of zero coefficients
    let mut zero := true
    while zero do
      let (b1, b) := br.getBit (rd probas (p + 1)); br := b
      if b1 then zero := false
      else
        n := n + 1
        p := probIdx t n 0
        if n == 16 then return (16, br, out)
    -- non-zero coefficient at position n
    let (b2, b) := br.getBit (rd probas (p + 2)); br := b
    let mut v := 1
    if !b2 then
      p := probIdx t (n + 1) 1
    else
      let (lv, b) := getLargeValue br probas p; br := b
      v := lv
      p := probIdx t (n + 1) 2
    let (s, b) := br.getSigned v; br := b
    let dq := if n > 0 then dq1 else dq0
    out := out.setIfInBounds (base + kZigzag.getD n 0) (wrap16 (s * dq))
    n := n + 1
  return (16, br, out)

/-- `NzCodeBits`. -/
@[inline] def nzCodeBits (nzCoeffs : Nat) (nz : Nat) (dcNz : Bool) : Nat :=
  (nzCoeffs <<< 2) ||| (if nz > 3 then 3 else if nz > 1 then 2 else if dcNz then 1 else 0)

/-- Result of residual parsing for one macroblock. -/
structure Residuals where
  coeffs   : Array Int   -- 384 = 16 Y + 4 U + 4 V blocks of 16
  nonZeroY : Nat
  nonZeroUV : Nat

/-- `ParseResiduals` (RFC 6386 §13.3 contexts). `tnz/tnzDc` are the top context of this
macroblock column, `lnz/lnzDc` the left context. Returns updated contexts. -/
def parseResiduals (br : BoolDec) (probas : ByteArray) (q : QuantMatrix) (isI4 : Bool)
    (tnz0 tnzDc lnz0 lnzDc : Nat) :
    Residuals × (Nat × Nat × Nat × Nat) × BoolDec := Id.run do
  let mut br := br
  let mut dst : Array Int := Array.replicate 384 0
  let mut tnzDc := tnzDc
  let mut lnzDc := lnzDc
  let mut first := 0
  let mut acType := 3
  if !isI4 then
    let dc0 : Array Int := Array.replicate 16 0
    let ctx := tnzDc + lnzDc
    let (nz, b, dc) := getCoeffs br probas 1 ctx q.y2.1 q.y2.2 0 dc0 0; br := b
    let f := if nz > 0 then 1 else 0
    tnzDc := f; lnzDc := f
    if nz > 1 then
      dst := transformWHT dc dst
    else
      let d := asr (dc.getD 0 0 + 3) 3
      for i in [0:16] do dst := dst.setIfInBounds (16 * i) d
    first := 1
    acType := 0
  let mut tnz := tnz0 &&& 0x0f
  let mut lnz := lnz0 &&& 0x0f
  let mut nonZeroY := 0
  for y in [0:4] do
    let mut l := lnz &&& 1
    let mut nzCoeffs := 0
    for x in [0:4] do
      let ctx := l + (tnz &&& 1)
      let base := 16 * (4 * y + x)
      let (nz, b, d) := getCoeffs br probas acType ctx q.y1.1 q.y1.2 first dst base; br := b
      dst := d
      l := if nz > first then 1 else 0
      tnz := ((tnz >>> 1) ||| (l <<< 7)) &&& 0xff
      nzCoeffs := nzCodeBits nzCoeffs nz (dst.getD base 0 != 0)
    tnz := tnz >>> 4
    lnz := ((lnz >>> 1) ||| (l <<< 7)) &&& 0xff
    nonZeroY := ((nonZeroY <<< 8) ||| nzCoeffs) &&& 0xffffffff
  let mut outTnz := tnz
  let mut outLnz := lnz >>> 4
  let mut nonZeroUV := 0
  for ch in [0:2] do
    let chs := 2 * ch   -- libwebp's ch = 0, 2
    let mut nzCoeffs := 0
    let mut tz := (tnz0 >>> (4 + chs)) &&& 0xff
    let mut lz := (lnz0 >>> (4 + chs)) &&& 0xff
    for y in [0:2] do
      let mut l := lz &&& 1
      for x in [0:2] do
        let ctx := l + (tz &&& 1)
        let base := 256 + 64 * ch + 16 * (2 * y + x)
        let (nz, b, d) := getCoeffs br probas 2 ctx q.uv.1 q.uv.2 0 dst base; br := b
        dst := d
        l := if nz > 0 then 1 else 0
        tz := ((tz >>> 1) ||| (l <<< 3)) &&& 0xff
        nzCoeffs := nzCodeBits nzCoeffs nz (dst.getD base 0 != 0)
      tz := tz >>> 2
      lz := ((lz >>> 1) ||| (l <<< 5)) &&& 0xff
    nonZeroUV := nonZeroUV ||| (nzCoeffs <<< (4 * chs))
    outTnz := outTnz ||| ((tz <<< 4) <<< chs)
    outLnz := outLnz ||| ((lz &&& 0xf0) <<< chs)
  return ({ coeffs := dst, nonZeroY, nonZeroUV },
          (outTnz &&& 0xff, tnzDc, outLnz &&& 0xff, lnzDc), br)

/-- `CheckMode`: DC prediction variants at frame borders. -/
@[inline] def checkMode (mbx mby mode : Nat) : Nat :=
  if mode == 0 then
    if mbx == 0 then (if mby == 0 then 6 else 5) else (if mby == 0 then 4 else 0)
  else mode

/-- Copy `n` bytes inside the work buffer. -/
@[inline] def copyWithin (wb : ByteArray) (src dst n : Nat) : ByteArray := Id.run do
  let mut wb := wb
  for i in [0:n] do wb := wr wb (dst + i) (rdByte wb (src + i))
  return wb

/-- Reconstruct one macroblock into the work buffer (`ReconstructRow` body for one `mb_x`).
`topY/topU/topV` hold the unfiltered bottom rows of the previous macroblock row
(16 / 8 / 8 bytes per column). -/
def reconstructMB (wb : ByteArray) (m : MBModes) (r : Residuals) (mbx mby mbw : Nat)
    (topY topU topV : ByteArray) : ByteArray := Id.run do
  let mut wb := wb
  if mbx > 0 then
    for jj in [0:17] do
      let rowY := Y_OFF + jj * 32 - 32   -- j = jj - 1 in [-1, 15]
      wb := copyWithin wb (rowY + 12) (rowY - 4) 4
    for jj in [0:9] do
      let rowU := U_OFF + jj * 32 - 32
      let rowV := V_OFF + jj * 32 - 32
      wb := copyWithin wb (rowU + 4) (rowU - 4) 4
      wb := copyWithin wb (rowV + 4) (rowV - 4) 4
  if mby > 0 then
    for i in [0:16] do wb := wr wb (Y_OFF - 32 + i) (rdByte topY (16 * mbx + i))
    for i in [0:8] do
      wb := wr wb (U_OFF - 32 + i) (rdByte topU (8 * mbx + i))
      wb := wr wb (V_OFF - 32 + i) (rdByte topV (8 * mbx + i))
  let c := r.coeffs
  if m.isI4 then
    let tr := Y_OFF - 32 + 16
    if mby > 0 then
      if mbx + 1 ≥ mbw then
        let v := rdByte topY (16 * mbx + 15)
        for i in [0:4] do wb := wr wb (tr + i) v
      else
        for i in [0:4] do wb := wr wb (tr + i) (rdByte topY (16 * (mbx + 1) + i))
    for k in [1:4] do
      for i in [0:4] do wb := wr wb (tr + 128 * k + i) (rdByte wb (tr + i))
    let mut bits := r.nonZeroY
    for n in [0:16] do
      let d := Y_OFF + kScan.getD n 0
      wb := pred4 wb d (m.imodes.getD n 0)
      wb := doTransform ((bits >>> 30) &&& 3) wb c (16 * n) d
      bits := (bits <<< 2) &&& 0xffffffff
  else
    let mode := checkMode mbx mby (m.imodes.getD 0 0)
    wb := predBlock wb Y_OFF 16 mode
    let mut bits := r.nonZeroY
    if bits != 0 then
      for n in [0:16] do
        wb := doTransform ((bits >>> 30) &&& 3) wb c (16 * n) (Y_OFF + kScan.getD n 0)
        bits := (bits <<< 2) &&& 0xffffffff
  let uvMode := checkMode mbx mby m.uvmode
  wb := predBlock wb U_OFF 8 uvMode
  wb := predBlock wb V_OFF 8 uvMode
  wb := doUVTransform r.nonZeroUV wb c 256 U_OFF
  wb := doUVTransform (r.nonZeroUV >>> 8) wb c 320 V_OFF
  return wb

/-- Read `n` bytes starting at `off` (zero-padded if out of range). -/
def sliceBytes (a : ByteArray) (off n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do out := out.push (rdByte a (off + i))
  return out

/-- Decode a VP8 key frame.

`data` is the VP8 bitstream. `chunkSize` is the size declared by the 'VP8 ' chunk
header (used only for libwebp's `partition_length < chunk_size` check). Note that libwebp's
simple decoding API (`WebPDecode*`) hands the VP8 decoder *all bytes from the start of the
VP8 payload to the end of the input buffer*, so the last partition may extend past the
chunk; to mimic that, pass the longer buffer as `data` and the chunk size as `chunkSize`. -/
def decodeFrameExt (data : ByteArray) (chunkSize : Nat) : Except String Frame := do
  let tag ← parseFrameTag data chunkSize
  let width := tag.width
  let height := tag.height
  let bufSize := data.size - 10
  if tag.partitionLength > bufSize then throw "VP8: bad partition length"
  let some br0 := BoolDec.init data 10 tag.partitionLength
    | throw "VP8: cannot initialize bitreader"
  let mut br := br0
  -- color space / clamping type (read and ignored)
  let (_, b) := br.getFlag; br := b
  let (_, b) := br.getFlag; br := b
  let (seg, b) := parseSegmentHeader br; br := b
  if br.eof then throw "VP8: cannot parse segment header"
  let (fh, b) := parseFilterHeader br; br := b
  if br.eof then throw "VP8: cannot parse filter header"
  -- partitions
  let (np, b) := br.getValue 2; br := b
  let lastPart := (1 <<< np) - 1
  let partStart0 := 10 + tag.partitionLength
  let size := data.size - partStart0
  if size < 3 * lastPart then throw "VP8: cannot parse partitions"
  let mut partStart := partStart0 + 3 * lastPart
  let mut sizeLeft := size - 3 * lastPart
  let mut parts : Array BoolDec := #[]
  for pIdx in [0:lastPart] do
    let psize0 := le24 data (partStart0 + 3 * pIdx)
    let psize := if psize0 > sizeLeft then sizeLeft else psize0
    let some pb := BoolDec.init data partStart psize | throw "VP8: cannot parse partitions"
    parts := parts.push pb
    partStart := partStart + psize
    sizeLeft := sizeLeft - psize
  let some pl := BoolDec.init data partStart sizeLeft | throw "VP8: cannot parse partitions"
  parts := parts.push pl
  if sizeLeft == 0 then throw "VP8: cannot parse partitions (not enough data)"
  let (dqm, b) := parseQuant br seg; br := b
  let (_, b) := br.getFlag; br := b   -- update_proba: ignored
  let ((probas, useSkip, skipP), b) := parseProba br; br := b
  -- filter strengths (PrecomputeFilterStrengths)
  let filterType := if fh.level == 0 then 0 else if fh.simple then 1 else 2
  let mut fstr : Array FInfo := #[]   -- index 2*s + i4x4
  for s in [0:4] do
    for i4 in [0:2] do
      let mut baseLevel : Int := fh.level
      if seg.useSegment then
        baseLevel := seg.filterStrength.getD s 0 + (if seg.absoluteDelta then 0 else (fh.level : Int))
      let mut level := baseLevel
      if fh.useLfDelta then
        level := level + fh.refLfDelta.getD 0 0
        if i4 == 1 then level := level + fh.modeLfDelta.getD 0 0
      let lv : Nat := (if level < 0 then 0 else if level > 63 then 63 else level).toNat
      if lv > 0 then
        let mut ilevel := lv
        if fh.sharpness > 0 then
          ilevel := if fh.sharpness > 4 then ilevel >>> 2 else ilevel >>> 1
          if ilevel > 9 - fh.sharpness then ilevel := 9 - fh.sharpness
        if ilevel < 1 then ilevel := 1
        fstr := fstr.push { limit := 2 * lv + ilevel, ilevel,
                            inner := i4 == 1, hevThresh := if lv ≥ 40 then 2 else if lv ≥ 15 then 1 else 0 }
      else
        fstr := fstr.push { limit := 0, ilevel := 0, inner := i4 == 1, hevThresh := 0 }
  -- frame buffers (macroblock padded)
  let mbw := (width + 15) >>> 4
  let mbh := (height + 15) >>> 4
  let yStride := 16 * mbw
  let uvStride := 8 * mbw
  let mut yPlane := ByteArray.mk (Array.replicate (yStride * 16 * mbh) 0)
  let mut uPlane := ByteArray.mk (Array.replicate (uvStride * 8 * mbh) 0)
  let mut vPlane := ByteArray.mk (Array.replicate (uvStride * 8 * mbh) 0)
  let mut finfos : Array FInfo := Array.emptyWithCapacity (mbw * mbh)
  let mut topY := ByteArray.mk (Array.replicate (16 * mbw) 0)
  let mut topU := ByteArray.mk (Array.replicate (8 * mbw) 0)
  let mut topV := ByteArray.mk (Array.replicate (8 * mbw) 0)
  let mut intraT : Array Nat := Array.replicate (4 * mbw) 0
  let mut nzTop : Array Nat := Array.replicate mbw 0
  let mut nzDcTop : Array Nat := Array.replicate mbw 0
  let mut wb := ByteArray.mk (Array.replicate YUV_SIZE 0)
  let numPartsMinusOne := lastPart
  for mby in [0:mbh] do
    -- intra modes for the whole row (partition 0)
    let mut intraL : Array Nat := #[0, 0, 0, 0]
    let mut rowModes : Array MBModes := Array.emptyWithCapacity mbw
    for mbx in [0:mbw] do
      let (m, t, l, b) := parseIntraMode br seg useSkip skipP intraT intraL mbx
      br := b; intraT := t; intraL := l
      rowModes := rowModes.push m
    if br.eof then throw "VP8: premature end-of-partition0 encountered"
    let pidx := mby &&& numPartsMinusOne
    let mut tbr := parts.getD pidx br0
    -- left contexts
    let mut lnz := 0
    let mut lnzDc := 0
    -- ReconstructRow prologue: left borders and top border
    for j in [0:16] do wb := wrN wb (Y_OFF + j * 32 - 1) 129
    for j in [0:8] do
      wb := wrN wb (U_OFF + j * 32 - 1) 129
      wb := wrN wb (V_OFF + j * 32 - 1) 129
    if mby > 0 then
      wb := wrN wb (Y_OFF - 33) 129
      wb := wrN wb (U_OFF - 33) 129
      wb := wrN wb (V_OFF - 33) 129
    else
      for i in [0:21] do wb := wrN wb (Y_OFF - 33 + i) 127
      for i in [0:9] do
        wb := wrN wb (U_OFF - 33 + i) 127
        wb := wrN wb (V_OFF - 33 + i) 127
    for mbx in [0:mbw] do
      let m := rowModes.getD mbx { segment := 0, skip := false, isI4 := false, imodes := #[0], uvmode := 0 }
      let skip := useSkip && m.skip
      let mut res : Residuals := { coeffs := #[], nonZeroY := 0, nonZeroUV := 0 }
      let mut allZero := skip
      if !skip then
        let q := dqm.getD m.segment (dqm.getD 0 { y1 := (0,0), y2 := (0,0), uv := (0,0) })
        let (r, (tn, tdc, ln, ldc), b) :=
          parseResiduals tbr probas q m.isI4 (nzTop.getD mbx 0) (nzDcTop.getD mbx 0) lnz lnzDc
        tbr := b
        res := r
        nzTop := nzTop.setIfInBounds mbx tn
        nzDcTop := nzDcTop.setIfInBounds mbx tdc
        lnz := ln; lnzDc := ldc
        allZero := r.nonZeroY == 0 && r.nonZeroUV == 0
      else
        nzTop := nzTop.setIfInBounds mbx 0
        lnz := 0
        if !m.isI4 then
          nzDcTop := nzDcTop.setIfInBounds mbx 0
          lnzDc := 0
      if filterType > 0 then
        let f := fstr.getD (2 * m.segment + (if m.isI4 then 1 else 0)) { limit := 0, ilevel := 0, inner := false, hevThresh := 0 }
        finfos := finfos.push { f with inner := f.inner || !allZero }
      if tbr.eof then throw "VP8: premature end-of-file encountered"
      -- reconstruction
      wb := reconstructMB wb m res mbx mby mbw topY topU topV
      if mby + 1 < mbh then
        for i in [0:16] do topY := wr topY (16 * mbx + i) (rdByte wb (Y_OFF + 15 * 32 + i))
        for i in [0:8] do
          topU := wr topU (8 * mbx + i) (rdByte wb (U_OFF + 7 * 32 + i))
          topV := wr topV (8 * mbx + i) (rdByte wb (V_OFF + 7 * 32 + i))
      -- copy to frame
      for j in [0:16] do
        for i in [0:16] do
          yPlane := wr yPlane ((mby * 16 + j) * yStride + mbx * 16 + i) (rdByte wb (Y_OFF + j * 32 + i))
      for j in [0:8] do
        for i in [0:8] do
          uPlane := wr uPlane ((mby * 8 + j) * uvStride + mbx * 8 + i) (rdByte wb (U_OFF + j * 32 + i))
          vPlane := wr vPlane ((mby * 8 + j) * uvStride + mbx * 8 + i) (rdByte wb (V_OFF + j * 32 + i))
    parts := parts.setIfInBounds pidx tbr
  -- loop filter (in macroblock raster order)
  if filterType > 0 then
    for mby in [0:mbh] do
      for mbx in [0:mbw] do
        let f := finfos.getD (mby * mbw + mbx) { limit := 0, ilevel := 0, inner := false, hevThresh := 0 }
        let (y', u', v') := doFilterMB yPlane uPlane vPlane yStride uvStride filterType f mbx mby
        yPlane := y'; uPlane := u'; vPlane := v'
  -- crop
  let uvW := (width + 1) / 2
  let uvH := (height + 1) / 2
  let mut yOut := ByteArray.emptyWithCapacity (width * height)
  for j in [0:height] do
    for i in [0:width] do yOut := yOut.push (rdByte yPlane (j * yStride + i))
  let mut uOut := ByteArray.emptyWithCapacity (uvW * uvH)
  let mut vOut := ByteArray.emptyWithCapacity (uvW * uvH)
  for j in [0:uvH] do
    for i in [0:uvW] do
      uOut := uOut.push (rdByte uPlane (j * uvStride + i))
      vOut := vOut.push (rdByte vPlane (j * uvStride + i))
  return { width, height, y := yOut, u := uOut, v := vOut }

end WebP.VP8Libwebp
