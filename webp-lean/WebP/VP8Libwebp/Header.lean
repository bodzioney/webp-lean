import WebP.VP8Libwebp.BoolDecoder
import WebP.VP8Libwebp.Tables
/-!
# VP8 frame header parsing (RFC 6386 §9, §19.1–§19.2)

Port of libwebp `VP8GetInfo` / `VP8GetHeaders` / `ParseSegmentHeader` /
`ParseFilterHeader` / `ParsePartitions` / `VP8ParseQuant` / `VP8ParseProba`.
-/
namespace WebP.VP8Libwebp

/-- Little-endian 24-bit read. -/
def le24 (a : ByteArray) (i : Nat) : Nat := rd a i ||| (rd a (i+1) <<< 8) ||| (rd a (i+2) <<< 16)

/-- Uncompressed data chunk of a key frame (RFC 6386 §9.1). -/
structure FrameTag where
  keyFrame        : Bool
  profile         : Nat
  showFrame       : Bool
  partitionLength : Nat
  width           : Nat
  xscale          : Nat
  height          : Nat
  yscale          : Nat

/-- Parse and validate the 10-byte frame tag + key frame start code + dimensions.
Reproduces libwebp `VP8GetInfo(data, data_size, chunkSize)` checks:
non-keyframes, profile > 3, invisible frames, `partition_length ≥ chunkSize`
and zero dimensions are rejected. -/
def parseFrameTag (data : ByteArray) (chunkSize : Nat) : Except String FrameTag := do
  if data.size < 10 then throw "VP8: not enough data for frame header"
  if !(rd data 3 == 0x9d && rd data 4 == 0x01 && rd data 5 == 0x2a) then
    throw "VP8: bad start code"
  let bits := rd data 0 ||| (rd data 1 <<< 8) ||| (rd data 2 <<< 16)
  let keyFrame := bits &&& 1 == 0
  let profile := (bits >>> 1) &&& 7
  let showFrame := (bits >>> 4) &&& 1 == 1
  let partitionLength := bits >>> 5
  let w := (rd data 6 ||| (rd data 7 <<< 8)) &&& 0x3fff
  let h := (rd data 8 ||| (rd data 9 <<< 8)) &&& 0x3fff
  if !keyFrame then throw "VP8: not a key frame"
  if profile > 3 then throw "VP8: unknown profile"
  if !showFrame then throw "VP8: frame not displayable"
  if partitionLength ≥ chunkSize then throw "VP8: inconsistent partition length"
  if w == 0 || h == 0 then throw "VP8: zero dimension"
  return { keyFrame, profile, showFrame, partitionLength, width := w, xscale := rd data 7 >>> 6,
           height := h, yscale := rd data 9 >>> 6 }

/-- Segment header (RFC 6386 §9.3). -/
structure SegmentHeader where
  useSegment    : Bool := false
  updateMap     : Bool := false
  absoluteDelta : Bool := true
  quantizer     : Array Int := #[0, 0, 0, 0]
  filterStrength : Array Int := #[0, 0, 0, 0]
  /-- segment-id tree probabilities (default 255) -/
  segProbs      : Array Nat := #[255, 255, 255]

/-- `ParseSegmentHeader`. -/
def parseSegmentHeader (br : BoolDec) : SegmentHeader × BoolDec := Id.run do
  let mut br := br
  let mut hdr : SegmentHeader := {}
  let (use, br1) := br.getFlag; br := br1
  if use then
    let (upd, br2) := br.getFlag; br := br2
    hdr := { hdr with useSegment := true, updateMap := upd }
    let (updData, br3) := br.getFlag; br := br3
    if updData then
      let (abs, br4) := br.getFlag; br := br4
      hdr := { hdr with absoluteDelta := abs }
      let mut q : Array Int := #[]
      for _ in [0:4] do
        let (f, b) := br.getFlag; br := b
        if f then
          let (v, b) := br.getSignedValue 7; br := b; q := q.push v
        else q := q.push 0
      let mut fs : Array Int := #[]
      for _ in [0:4] do
        let (f, b) := br.getFlag; br := b
        if f then
          let (v, b) := br.getSignedValue 6; br := b; fs := fs.push v
        else fs := fs.push 0
      hdr := { hdr with quantizer := q, filterStrength := fs }
    if upd then
      let mut ps : Array Nat := #[]
      for _ in [0:3] do
        let (f, b) := br.getFlag; br := b
        if f then
          let (v, b) := br.getValue 8; br := b; ps := ps.push v
        else ps := ps.push 255
      hdr := { hdr with segProbs := ps }
  return (hdr, br)

/-- Loop filter header (RFC 6386 §9.6). -/
structure FilterHeader where
  simple     : Bool
  level      : Nat
  sharpness  : Nat
  useLfDelta : Bool
  refLfDelta : Array Int
  modeLfDelta : Array Int

/-- `ParseFilterHeader`. Deltas default to 0 (fresh decoder). -/
def parseFilterHeader (br : BoolDec) : FilterHeader × BoolDec := Id.run do
  let mut br := br
  let (simple, b) := br.getFlag; br := b
  let (level, b) := br.getValue 6; br := b
  let (sharpness, b) := br.getValue 3; br := b
  let (useLfDelta, b) := br.getFlag; br := b
  let mut ref : Array Int := #[0, 0, 0, 0]
  let mut mode : Array Int := #[0, 0, 0, 0]
  if useLfDelta then
    let (upd, b) := br.getFlag; br := b
    if upd then
      for i in [0:4] do
        let (f, b) := br.getFlag; br := b
        if f then
          let (v, b) := br.getSignedValue 6; br := b; ref := ref.setIfInBounds i v
      for i in [0:4] do
        let (f, b) := br.getFlag; br := b
        if f then
          let (v, b) := br.getSignedValue 6; br := b; mode := mode.setIfInBounds i v
  return ({ simple, level, sharpness, useLfDelta, refLfDelta := ref, modeLfDelta := mode }, br)

/-- Dequantization factors of one segment: `(y1dc, y1ac, y2dc, y2ac, uvdc, uvac)`. -/
structure QuantMatrix where
  y1 : Int × Int
  y2 : Int × Int
  uv : Int × Int

@[inline] private def clipQ (v : Int) (m : Int) : Nat := (if v < 0 then 0 else if v > m then m else v).toNat

/-- `VP8ParseQuant` (RFC 6386 §9.6, §14.1 with libwebp's y2/uv adjustments). -/
def parseQuant (br : BoolDec) (seg : SegmentHeader) : Array QuantMatrix × BoolDec := Id.run do
  let mut br := br
  let (q0, b) := br.getValue 7; br := b
  let mut d : Array Int := #[]
  for _ in [0:5] do
    let (f, b) := br.getFlag; br := b
    if f then
      let (v, b) := br.getSignedValue 4; br := b; d := d.push v
    else d := d.push 0
  let dqy1dc := d.getD 0 0; let dqy2dc := d.getD 1 0; let dqy2ac := d.getD 2 0
  let dquvdc := d.getD 3 0; let dquvac := d.getD 4 0
  let mk (q : Int) : QuantMatrix :=
    let dc := Tables.dcTable; let ac := Tables.acTable
    let y2ac0 := (ac.getD (clipQ (q + dqy2ac) 127) 0 * 101581) >>> 16
    { y1 := ((dc.getD (clipQ (q + dqy1dc) 127) 0 : Int), (ac.getD (clipQ q 127) 0 : Int))
      y2 := ((dc.getD (clipQ (q + dqy2dc) 127) 0 * 2 : Int), ((if y2ac0 < 8 then 8 else y2ac0 : Nat) : Int))
      uv := ((dc.getD (clipQ (q + dquvdc) 117) 0 : Int), (ac.getD (clipQ (q + dquvac) 127) 0 : Int)) }
  let mut out : Array QuantMatrix := #[]
  for i in [0:4] do
    if seg.useSegment then
      let q := seg.quantizer.getD i 0 + (if seg.absoluteDelta then 0 else (q0 : Int))
      out := out.push (mk q)
    else
      out := out.push (mk q0)
  return (out, br)

/-- Band index for coefficient position `n` (0..16, 16 is a sentinel). -/
def kBands : Array Nat := #[0, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 0]

/-- `VP8ParseProba`: coefficient probabilities (RFC 6386 §13.4) and skip probability.
Result: (probas [t][b][c][p] flattened, useSkipProba, skipP). -/
def parseProba (br : BoolDec) : (ByteArray × Bool × Nat) × BoolDec := Id.run do
  let mut br := br
  let mut probas := ByteArray.mk (Array.replicate 1056 0)
  for i in [0:1056] do
    let (f, b) := br.getBit (rd Tables.coeffsUpdateProba i); br := b
    if f then
      let (v, b) := br.getValue 8; br := b
      probas := wrN probas i v
    else
      probas := wr probas i (rdByte Tables.coeffsProba0 i)
  let (useSkip, b) := br.getFlag; br := b
  let mut skipP := 0
  if useSkip then
    let (v, b) := br.getValue 8; br := b; skipP := v
  return ((probas, useSkip, skipP), br)

end WebP.VP8Libwebp
