import WebP.Spec.VP8.ModeMV
/-!
# DCT/WHT coefficient tokens (RFC 6386 §13; reference source §20.16 `tokens.c`)

Transcription of `decode_mb_tokens` (whose `goto`-based control flow becomes the recursive
`blockTokens`), `reset_mb_context` and `vp8_dixie_tokens_process_row`.

C semantics kept: coefficients are stored in `short` (the dequantized value `v * dqf`, computed
in `int`, is truncated to 16 bits — **[interp]** two's complement truncation, the behaviour of
every C compiler the reference decoder is built with); `eob_mask` is an `int` whose bit 31 is set
with `t << 31` (**[interp]** formally undefined in C for `t = 1`; the mask is only ever tested for
being non-zero, so we read it as setting bit 31).
-/
namespace WebP.Spec.VP8

/-- Truncation to `short` (two's complement). -/
@[inline] def toShort (v : Int) : Int :=
  let m := v % 65536
  if m ≥ 32768 then m - 65536 else m

/-- `token_entropy_ctx_t`: 4 Y, 2 U, 2 V and 1 Y2 "has non-zero data" flags. -/
abbrev TokenCtx := Array Nat

/-- Node indices of the token tree (`EOB_CONTEXT_NODE` … `CAT_FIVE_CONTEXT_NODE`). -/
def EOB_CONTEXT_NODE : Nat := 0
def ZERO_CONTEXT_NODE : Nat := 1
def ONE_CONTEXT_NODE : Nat := 2
def LOW_VAL_CONTEXT_NODE : Nat := 3
def TWO_CONTEXT_NODE : Nat := 4
def THREE_CONTEXT_NODE : Nat := 5
def HIGH_LOW_CONTEXT_NODE : Nat := 6
def CAT_ONE_CONTEXT_NODE : Nat := 7
def CAT_THREEFOUR_CONTEXT_NODE : Nat := 8
def CAT_THREE_CONTEXT_NODE : Nat := 9
def CAT_FIVE_CONTEXT_NODE : Nat := 10

/-- `ENTROPY_NODES` -/
def ENTROPY_NODES : Nat := 11

/-- Token numbers of the value categories (`DCT_VAL_CATEGORY1` … `6`). -/
def DCT_VAL_CATEGORY1 : Nat := 5
def DCT_VAL_CATEGORY6 : Nat := 10

/-- `(block, type)` in decoding order for macroblocks with a Y2 block. -/
def blocksWithY2 : Array (Nat × Nat) :=
  #[(24, 1)] ++ (Array.range 16).map (·, 0) ++ (Array.range' 16 8).map (·, 2)

/-- `(block, type)` in decoding order for `B_PRED` macroblocks. -/
def blocksNoY2 : Array (Nat × Nat) :=
  (Array.range 16).map (·, 3) ++ (Array.range' 16 8).map (·, 2)

section
variable (P : Prims)

/-- The extra bits of `DCT_VAL_CATEGORYt`: `val = extrabits[t].min_val`, then
`DECODE_EXTRABIT_AND_ADJUST_VAL(t, b)` for `b = extrabits[t].length` down to `0`, i.e.
`val += bool_get(bool, extrabits[t].probs[b]) << b`. -/
def extraBits (t : Nat) : BoolM Int := do
  let len := (Tables.extrabitsLength.getD t 0).toNat
  let mut val : Int := Tables.extrabitsMinVal.getD t 0
  for k in [0:len + 1] do
    let b := len - k
    let bit ← get P (Tables.extrabitsProbs.getD (12 * t + b) 0)
    val := val + ((bit.toNat <<< b : Nat) : Int)
  return val

/-- The value of a non-zero token, after `prob[ZERO_CONTEXT_NODE]` decoded as non-zero
(labels `CHECK_0_` … `ONE_CONTEXT_NODE_0_` of `decode_mb_tokens`). Returns the absolute value
and whether it was a `ONE_TOKEN` (which selects context 1 instead of 2 for the next token). -/
def tokenValue (probs : Array Nat) (prob : Nat) : BoolM (Int × Bool) := do
  let p (n : Nat) : Nat := probs.getD (prob + n) 0
  if !(← get P (p ONE_CONTEXT_NODE)) then return (1, true)
  if !(← get P (p LOW_VAL_CONTEXT_NODE)) then
    -- LOW_VAL_CONTEXT_NODE_0_
    if !(← get P (p TWO_CONTEXT_NODE)) then return (2, false)
    if !(← get P (p THREE_CONTEXT_NODE)) then return (3, false)
    return (4, false)
  if !(← get P (p HIGH_LOW_CONTEXT_NODE)) then
    -- HIGH_LOW_CONTEXT_NODE_0_
    if !(← get P (p CAT_ONE_CONTEXT_NODE)) then
      return (← extraBits P DCT_VAL_CATEGORY1, false)      -- CAT_ONE_CONTEXT_NODE_0_
    return (← extraBits P (DCT_VAL_CATEGORY1 + 1), false)   -- DCT_VAL_CATEGORY2
  if !(← get P (p CAT_THREEFOUR_CONTEXT_NODE)) then
    -- CAT_THREEFOUR_CONTEXT_NODE_0_
    if !(← get P (p CAT_THREE_CONTEXT_NODE)) then
      return (← extraBits P (DCT_VAL_CATEGORY1 + 2), false) -- DCT_VAL_CATEGORY3
    return (← extraBits P (DCT_VAL_CATEGORY1 + 3), false)   -- DCT_VAL_CATEGORY4
  if !(← get P (p CAT_FIVE_CONTEXT_NODE)) then
    return (← extraBits P (DCT_VAL_CATEGORY1 + 4), false)   -- DCT_VAL_CATEGORY5
  return (← extraBits P DCT_VAL_CATEGORY6, false)

/-- The tokens of one block, from label `DO_WHILE` (`atCheck0 = false`) or `CHECK_0_`
(`atCheck0 = true`) to `BLOCK_FINISHED`. `c` is the coefficient index, `prob` the offset of the
current probabilities in `probs` (`prob` already includes `bands_x[c]`), `typeProbs` the offset
of `probs[type]`, `dqf` the dequantization factors `(dc, ac)` of the block, and the block's
coefficients are `tokens[base, base + 16)`. Returns the final `c`. Every step increases `c` and
the block finishes at `c = 15` at the latest, so the fuel `17` suffices. -/
def blockTokens (probs : Array Nat) (typeProbs : Nat) (dqf : Int × Int) (base : Nat) :
    Nat → Nat → Nat → Bool → Array Int → BoolM (Nat × Array Int)
  | 0, c, _, _, tokens => return (c, tokens)
  | fuel + 1, c, prob, atCheck0, tokens => do
    -- DO_WHILE: DECODE_AND_BRANCH_IF_ZERO(prob[EOB_CONTEXT_NODE], BLOCK_FINISHED)
    if !atCheck0 then
      if !(← get P (probs.getD (prob + EOB_CONTEXT_NODE) 0)) then return (c, tokens)
    -- CHECK_0_: DECODE_AND_LOOP_IF_ZERO(prob[ZERO_CONTEXT_NODE], CHECK_0_)
    if !(← get P (probs.getD (prob + ZERO_CONTEXT_NODE) 0)) then
      if c < 15 then
        return ← blockTokens probs typeProbs dqf base fuel (c + 1)
          (typeProbs + Tables.bandsX.getD (c + 1) 0) true tokens
      else return (c, tokens)  -- "for malformed input"
    let (val, isOne) ← tokenValue P probs prob
    -- DECODE_AND_APPLYSIGN(val): v = (bool_get_bit(bool) ? -val : val) * dqf[!!c]
    let sign ← getBit P
    let v := (if sign then -val else val) * (if c = 0 then dqf.1 else dqf.2)
    -- prob = type_probs + ENTROPY_NODES * (isOne ? 1 : 2)
    let prob := typeProbs + ENTROPY_NODES * (if isOne then 1 else 2)
    if c < 15 then
      let tokens := tokens.setIfInBounds (base + Tables.zigzag.getD c 0) (toShort v)
      blockTokens probs typeProbs dqf base fuel (c + 1)
        (prob + Tables.bandsX.getD (c + 1) 0) false tokens
    else
      return (c, tokens.setIfInBounds (base + Tables.zigzag.getD 15 0) (toShort v))

/-- `decode_mb_tokens(bool, left, above, tokens, mode, probs, factor)` for a key frame:
decode the coefficients of one macroblock into a fresh (`memset` 0) array of 25 × 16 `short`s
(blocks 0–15 Y, 16–19 U, 20–23 V, 24 Y2). `above` is the whole above-context array, this
macroblock's entry being `above[aOff, aOff + 9)`. Returns the coefficients, `eob_mask`, and the
updated contexts. -/
def decodeMbTokens (left above : TokenCtx) (aOff : Nat) (mode : Nat) (probs : Array Nat)
    (factor : Array Int) : BoolM (Array Int × Nat × TokenCtx × TokenCtx) := do
  let mut tokens : Array Int := Array.replicate (25 * 16) 0
  let mut left := left
  let mut above := above
  let mut eobMask : Nat := 0
  -- The block sequence: with a Y2 block (mode != B_PRED): block 24 (type 1), blocks 0–15
  -- (type 0), blocks 16–23 (type 2); otherwise blocks 0–15 (type 3), blocks 16–23 (type 2).
  let blocks := if mode ≠ B_PRED then blocksWithY2 else blocksNoY2
  for (i, type) in blocks do
    -- dqf = factor[TOKEN_BLOCK_Y2 | TOKEN_BLOCK_Y1 | TOKEN_BLOCK_UV]
    let ft := if type = 1 then 2 else if type = 2 then 1 else 0
    let dqf := (factor.getD (2 * ft) 0, factor.getD (2 * ft + 1) 0)
    let typeProbs := type * (8 * 3 * ENTROPY_NODES)
    -- BLOCK_LOOP
    let li := Tables.leftContextIndex.getD i 0
    let ai := aOff + Tables.aboveContextIndex.getD i 0
    let t := left.getD li 0 + above.getD ai 0
    let c0 := if type = 0 then 1 else 0   -- `c = !type`
    let prob := typeProbs + t * ENTROPY_NODES + Tables.bandsX.getD c0 0
    let (c, tks) ← blockTokens P probs typeProbs dqf (16 * i) 17 c0 prob false tokens
    tokens := tks
    -- BLOCK_FINISHED
    if c > 1 then eobMask := eobMask ||| (1 <<< i)
    let nz := if c ≠ c0 then 1 else 0
    if nz = 1 then eobMask := eobMask ||| (1 <<< 31)
    left := left.setIfInBounds li nz
    above := above.setIfInBounds ai nz
  return (tokens, eobMask, left, above)

/-- `reset_mb_context(left, above, mode)`: used for macroblocks with `skip_coeff` set; the Y2
context is preserved by `B_PRED` macroblocks (which have no Y2 block). -/
def resetMbContext (left above : TokenCtx) (aOff : Nat) (mode : Nat) : TokenCtx × TokenCtx :=
  Id.run do
    let mut left := left
    let mut above := above
    for k in [0:8] do
      left := left.setIfInBounds k 0
      above := above.setIfInBounds (aOff + k) 0
    if mode ≠ B_PRED then
      left := left.setIfInBounds 8 0
      above := above.setIfInBounds (aOff + 8) 0
    return (left, above)

/-- `vp8_dixie_tokens_process_row(ctx, partition, row, 0, mb_cols)`: decode the coefficients of
a macroblock row from its token partition. `left` is reset at the start of the row; `above`
(9 entries per column) is reset by the caller before row 0. Returns, per macroblock, its 400
coefficients, the row's `mb_info` with `eob_mask` set, and the new above context. -/
def tokensProcessRow (probs : Array Nat) (dqf : Array DequantFactors) (mbi : Array MbInfo)
    (above : TokenCtx) : BoolM (Array (Array Int) × Array MbInfo × TokenCtx) := do
  let mut left : TokenCtx := Array.replicate 9 0   -- reset_row_context
  let mut above := above
  let mut coeffs : Array (Array Int) := Array.emptyWithCapacity mbi.size
  let mut out : Array MbInfo := Array.emptyWithCapacity mbi.size
  for h : col in [0:mbi.size] do
    let m := mbi[col]
    if m.skipCoeff then
      let (l, a) := resetMbContext left above (9 * col) m.yMode
      left := l; above := a
      coeffs := coeffs.push (Array.replicate (25 * 16) 0)
      out := out.push { m with eobMask := 0 }
    else
      let factor := (dqf.getD m.segmentId { quantIdx := 0, factor := #[] }).factor
      let (tks, eob, l, a) ← decodeMbTokens P left above (9 * col) m.yMode probs factor
      left := l; above := a
      coeffs := coeffs.push tks
      out := out.push { m with eobMask := eob }
  return (coeffs, out, above)

end
end WebP.Spec.VP8
