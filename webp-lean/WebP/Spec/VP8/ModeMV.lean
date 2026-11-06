import WebP.Spec.VP8.Header
/-!
# Macroblock modes (RFC 6386 §10, §11, §19.3; reference source §20.11 `modemv.c`)

Key-frame part of `vp8_dixie_modemv_process_row`: `read_segment_id`, `decode_kf_mb_mode`,
`above_block_mode`, `left_block_mode`.

The reference decoder keeps `struct mb_info` for every macroblock plus a border column on the
left and a border row above, all `calloc`'d (so the border entries have `y_mode = DC_PRED`, and
the sub-block modes of macroblocks that are not `B_PRED` are `0` = `B_DC_PRED`).
-/
namespace WebP.Spec.VP8

/-- Luma / chroma prediction modes (`enum prediction_mode`, §20.5). -/
def DC_PRED : Nat := 0
def V_PRED : Nat := 1
def H_PRED : Nat := 2
def TM_PRED : Nat := 3
def B_PRED : Nat := 4

/-- Sub-block modes. -/
def B_DC_PRED : Nat := 0
def B_TM_PRED : Nat := 1
def B_VE_PRED : Nat := 2
def B_HE_PRED : Nat := 3
def B_LD_PRED : Nat := 4
def B_RD_PRED : Nat := 5
def B_VR_PRED : Nat := 6
def B_VL_PRED : Nat := 7
def B_HD_PRED : Nat := 8
def B_HU_PRED : Nat := 9

/-- The key-frame fields of `struct mb_info`. -/
structure MbInfo where
  yMode : Nat
  uvMode : Nat
  segmentId : Nat
  skipCoeff : Bool
  /-- `split.modes[16]` -/
  modes : Array Nat
  /-- `eob_mask`, set by the token decoder (`vp8_dixie_tokens_process_row`) -/
  eobMask : Nat

/-- A `calloc`'d `mb_info` (used for the border, and the initial state of every entry). -/
def MbInfo.zero : MbInfo :=
  { yMode := 0, uvMode := 0, segmentId := 0, skipCoeff := false,
    modes := Array.replicate 16 0, eobMask := 0 }

instance : Inhabited MbInfo := ⟨MbInfo.zero⟩

/-- `above_block_mode(this, above, b)`. -/
def aboveBlockMode (thisModes : Array Nat) (above : MbInfo) (b : Nat) : Nat :=
  if b < 4 then
    match above.yMode with
    | 0 => B_DC_PRED      -- DC_PRED
    | 1 => B_VE_PRED      -- V_PRED
    | 2 => B_HE_PRED      -- H_PRED
    | 3 => B_TM_PRED      -- TM_PRED
    | 4 => above.modes.getD (b + 12) 0   -- B_PRED
    | _ => 0              -- `assert(0)`: unreachable on key frames
  else thisModes.getD (b - 4) 0

/-- `left_block_mode(this, left, b)`. -/
def leftBlockMode (thisModes : Array Nat) (left : MbInfo) (b : Nat) : Nat :=
  if b &&& 3 = 0 then
    match left.yMode with
    | 0 => B_DC_PRED
    | 1 => B_VE_PRED
    | 2 => B_HE_PRED
    | 3 => B_TM_PRED
    | 4 => left.modes.getD (b + 3) 0
    | _ => 0
  else thisModes.getD (b - 1) 0

section
variable (P : Prims)

/-- `read_segment_id` (§10, §19.3). -/
def readSegmentId (seg : SegmentHdr) : BoolM Nat := do
  if ← get P (seg.treeProbs.getD 0 0) then
    return 2 + (← get P (seg.treeProbs.getD 2 0)).toNat
  else
    return (← get P (seg.treeProbs.getD 1 0)).toNat

/-- `decode_kf_mb_mode(this, left, above, bool)` (§11.2–§11.4). `prev` holds the fields of the
`mb_info` entry before decoding (its `split.modes` survive when the mode is not `B_PRED`). -/
def decodeKfMbMode (prev left above : MbInfo) : BoolM MbInfo := do
  let yMode ← readTree P Tables.kfYModeTree Tables.kfYModeProbs 0
  let mut modes := prev.modes
  if yMode = B_PRED then
    for i in [0:16] do
      let a := aboveBlockMode modes above i
      let l := leftBlockMode modes left i
      let b ← readTree P Tables.bModeTree Tables.kfBModeProbs ((a * 10 + l) * 9)
      modes := modes.setIfInBounds i b
  let uvMode ← readTree P Tables.uvModeTree Tables.kfUvModeProbs 0
  return { prev with yMode, uvMode, modes }

/-- Key-frame part of `vp8_dixie_modemv_process_row(ctx, bool, row, 0, mb_cols)`: decode the
modes of one macroblock row, given the row above (`above`, the border row for row 0).
Every entry starts as `MbInfo.zero` (fresh, `calloc`'d context). -/
def modemvProcessRow (seg : SegmentHdr) (ent : EntropyHdr) (above : Array MbInfo)
    (mbCols : Nat) : BoolM (Array MbInfo) := do
  let mut row : Array MbInfo := Array.emptyWithCapacity mbCols
  -- `this - 1` for column 0 is the (zero) border entry
  let mut left := MbInfo.zero
  for col in [0:mbCols] do
    let mut this := MbInfo.zero
    if seg.updateMap then
      this := { this with segmentId := ← readSegmentId P seg }
    if ent.coeffSkipEnabled then
      this := { this with skipCoeff := ← get P ent.coeffSkipProb }
    -- key frame
    if !seg.updateMap then this := { this with segmentId := 0 }
    this ← decodeKfMbMode P this left (above.getD col MbInfo.zero)
    row := row.push this
    left := this
  return row

end
end WebP.Spec.VP8
