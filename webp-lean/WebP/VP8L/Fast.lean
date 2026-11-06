import WebP.Spec.Lossless
/-!
# Optimized primitives for the lossless decoder

* `fastReadBits`: extracts up to 25 bits with one 32-bit little-endian load and a shift,
  instead of bit-by-bit.
* `fastBuild`: canonical prefix decoding with (1) a lookup table indexed by the next
  `tableBits ≤ 8` stream bits and (2) a fallback that walks the code lengths one bit at a time
  (the classic `puff` algorithm of zlib), instead of searching all codewords.

`WebP.Proofs.Lossless` proves `fastPrims = Spec.VP8L.specPrims`, hence
`WebP.VP8L.decode = Spec.VP8L.decode`.
-/
namespace WebP.VP8L

open WebP.Spec

/-- `ReadBits(n)`: one 32-bit load + shift for `n ≤ 25`, reference definition otherwise. -/
def fastReadBits (d : ByteArray) (pos n : Nat) : Except String (Nat × Nat) :=
  if pos + n ≤ 8 * d.size then
    if n ≤ 25 then .ok ((le d (pos / 8) 4 >>> (pos % 8)) % 2 ^ n, pos + n)
    else .ok (readBitsVal d pos n, pos + n)
  else .error eofMsg

/-- Canonical prefix decoding one bit at a time (zlib's `puff`). `src j` is the `j`-th next bit
of the stream (`none` past the end); `byLen[l]` lists the symbols of code length `l` in
increasing order. Invariant at length `len`: `code` is twice the value of the first `len - 1`
bits, `first` is the first canonical codeword of length `len`. Returns `(symbol, length)`. -/
def puff (src : Nat → Option Nat) (byLen : Array (Array Nat)) : Option (Nat × Nat) :=
  go 1 0 0
where
  go (len code first : Nat) : Option (Nat × Nat) :=
    if len ≤ 15 then
      match src (len - 1) with
      | none => none
      | some b =>
        let code := code + b
        let syms := byLen.getD len #[]
        if code < first + syms.size then some (syms.getD (code - first) 0, len)
        else go (len + 1) (code * 2) ((first + syms.size) * 2)
    else none
  termination_by 16 - len

/-- Symbols of each code length, in increasing symbol order. -/
def symbolsByLen (lens : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 16) fun l =>
    if l.val = 0 then #[] else ((List.range lens.size).filter (fun s => lens.getD s 0 == l.val)).toArray

/-- The `tb` bits of `i`, least significant first, as a bit source. -/
def patternSrc (tb i : Nat) : Nat → Option Nat :=
  fun j => if j < tb then some (i / 2 ^ j % 2) else none

/-- The stream bits from position `pos` on, as a bit source. -/
def dataSrc (d : ByteArray) (pos : Nat) : Nat → Option Nat :=
  fun j => if pos + j < 8 * d.size then some (bit d (pos + j)) else none

/-- A prefix decoding table. `lut[i]` is `sym * 16 + len` when the `tableBits` bits `i` start with
a whole codeword of length `len`, and `0` otherwise. -/
structure Table where
  byLen : Array (Array Nat)
  tableBits : Nat
  lut : Array Nat

def mkTable (lens : Array Nat) : Table :=
  let byLen := symbolsByLen lens
  let maxLen := lens.foldl max 0
  let tb := min 8 maxLen
  let lut := Array.ofFn (n := 2 ^ tb) fun i =>
    match puff (patternSrc tb i.val) byLen with
    | some (s, len) => s * 16 + len
    | none => 0
  ⟨byLen, tb, lut⟩

/-- Decode one symbol at bit position `pos`. -/
def Table.decode (t : Table) (d : ByteArray) (pos : Nat) : Except String (Nat × Nat) :=
  let peek := (le d (pos / 8) 4 >>> (pos % 8)) % 2 ^ t.tableBits
  let e := t.lut.getD peek 0
  let len := e % 16
  if len ≠ 0 ∧ pos + len ≤ 8 * d.size then .ok (e / 16, pos + len)
  else
    match puff (dataSrc d pos) t.byLen with
    | some (s, l) => .ok (s, pos + l)
    | none => .error Prefix.symErr

/-- Building a prefix code: same validity rules as `Spec.Prefix.build`, table-driven decoding. -/
def fastBuild (d : ByteArray) (lens : Array Nat) : Except String Code :=
  if lens.any (· > Prefix.maxLen) then .error Prefix.buildErr else
  match Prefix.coded lens with
  | [] => .error Prefix.buildErr
  | [s] => .ok ⟨fun pos => .ok (s, pos)⟩
  | _ =>
    if Prefix.kraft lens = 2 ^ Prefix.maxLen then
      let t := mkTable lens
      .ok ⟨fun pos => t.decode d pos⟩
    else .error Prefix.buildErr

/-- The optimized primitives. -/
def fastPrims : Spec.VP8L.Prims := ⟨fastReadBits, fastBuild⟩

/-- The lossless decoder ('VP8L' chunk payload). -/
def decode (d : ByteArray) : Except String Spec.VP8L.Image := Spec.VP8L.decodeWith fastPrims d

/-- Headerless lossless image stream of implicit size (ALPH). -/
def decodeStream (d : ByteArray) (w h : Nat) : Except String (Array UInt32) :=
  Spec.VP8L.decodeStreamWith fastPrims d w h

end WebP.VP8L
