import WebP.Spec.Bits
/-!
# Canonical prefix codes (RFC 9649 §3.7)

"Most of the data is coded using a canonical prefix code [Huffman]. Hence, the codes are
transmitted by sending the prefix code lengths, as opposed to the actual prefix codes."

RFC 9649 does not spell out the canonical code assignment; it is the classical one of DEFLATE
(RFC 1951 §3.2.2), which is what libwebp implements:

1. `bl_count[l]` = number of symbols with code length `l`;
2. `next_code[1] = 0`, `next_code[l+1] = (next_code[l] + bl_count[l]) << 1`;
3. symbols of equal length get consecutive codes in increasing symbol order;

and codes are packed starting with their most significant bit (i.e. the first bit read from
the stream is the MSB of the codeword).

Validity (§3.7.2.1): "The described tree must be a complete binary tree. A single leaf node is
considered a complete binary tree". We formalize "complete" as the Kraft equality
`Σ 2^-len = 1`. A code with exactly one used symbol is the single-leaf tree: decoding it
consumes no bits ("even when no bits are consumed when that single leaf node tree is used"),
whatever nonzero length was transmitted for it (libwebp and image-webp agree). A code with no
used symbol at all is not a tree and is rejected (the RFC notes encoders send such "empty"
codes as a single symbol 0).
-/
namespace WebP.Spec

/-- A prefix code, represented by its decoding function: given a bit position, return the
decoded symbol and the position after its codeword. -/
structure Code where
  decode : Nat → Except String (Nat × Nat)

namespace Prefix

/-- Maximum code length (code lengths are coded with the literals `0..15`, §3.7.2.1.2). -/
def maxLen : Nat := 15

/-- `bl_count[l]`: number of symbols with code length `l`. -/
def count (lens : Array Nat) (l : Nat) : Nat := lens.toList.count l

/-- `next_code[l]` of RFC 1951 §3.2.2: the first canonical codeword of length `l`. -/
def firstCode (lens : Array Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => (firstCode lens l + (if l = 0 then 0 else count lens l)) * 2

/-- The canonical codeword of symbol `s` (only meaningful when `lens[s] ≠ 0`). -/
def codeword (lens : Array Nat) (s : Nat) : Nat :=
  let l := lens.getD s 0
  firstCode lens l + (lens.toList.take s).count l

/-- Value of the `n` stream bits starting at `pos`, the first bit being the most significant. -/
def bitsMSB (d : ByteArray) (pos : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bitsMSB d pos n * 2 + bit d (pos + n)

/-- Symbol `s` has a codeword and the stream at `pos` starts with exactly that codeword. -/
def matchesAt (d : ByteArray) (lens : Array Nat) (pos s : Nat) : Bool :=
  let l := lens.getD s 0
  l != 0 && decide (pos + l ≤ 8 * d.size) && bitsMSB d pos l == codeword lens s

/-- Kraft sum scaled by `2^15`: the code is complete iff this equals `2^15`. -/
def kraft (lens : Array Nat) : Nat :=
  lens.foldl (fun acc l => if l = 0 then acc else acc + 2 ^ (maxLen - l)) 0

/-- Symbols that have a codeword, in increasing order. -/
def coded (lens : Array Nat) : List Nat :=
  (List.range lens.size).filter (fun s => lens.getD s 0 != 0)

def buildErr : String := "invalid prefix code"
def symErr : String := "invalid prefix code symbol"

/-- Building the prefix code from its code lengths (§3.7.2.1, last paragraph of §3.7.2.1.2). -/
def build (d : ByteArray) (lens : Array Nat) : Except String Code :=
  if lens.any (· > maxLen) then .error buildErr else
  match coded lens with
  | [] => .error buildErr
  | [s] => .ok ⟨fun pos => .ok (s, pos)⟩
  | _ =>
    if kraft lens = 2 ^ maxLen then
      .ok ⟨fun pos =>
        match (List.range lens.size).find? (matchesAt d lens pos) with
        | some s => .ok (s, pos + lens.getD s 0)
        | none => .error symErr⟩
    else .error buildErr

end Prefix
end WebP.Spec
