/-!
# Bytes, little-endian integers, and the LSB-first bit stream

Formalizes the basic data conventions of RFC 9649:

* §2.2 "uint16 / uint24 / uint32": little-endian unsigned integers; "FourCC": four ASCII
  characters concatenated in little-endian order.
* §3.2: the lossless bit stream. "The bytes are read in the natural order of the stream
  containing them, and bits of each byte are read in least-significant-bit-first order.
  ... `b = ReadBits(2);` is equivalent with `b = ReadBits(1); b |= ReadBits(1) << 1;`"

Everything here is a plain total function on `Nat`; the efficient implementations used by
the decoder are proven equal to these in `WebP.Proofs.Bits`.
-/
namespace WebP.Spec

/-- Byte `i` of `d` as a natural number (`0` when out of range; callers always check ranges). -/
def byte (d : ByteArray) (i : Nat) : Nat :=
  if h : i < d.size then d[i].toNat else 0

/-- Little-endian unsigned integer made of the `n` bytes starting at offset `off`. -/
def le (d : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => byte d off + 256 * le d (off + 1) n

/-- §2.2 uint16. -/
def u16 (d : ByteArray) (off : Nat) : Nat := le d off 2
/-- §2.2 uint24. -/
def u24 (d : ByteArray) (off : Nat) : Nat := le d off 3
/-- §2.2 uint32. -/
def u32 (d : ByteArray) (off : Nat) : Nat := le d off 4

/-- §2.2 FourCC: "a uint32 created by concatenating four ASCII characters in little-endian
order". -/
def fourcc (a b c e : Char) : Nat :=
  a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * e.toNat))

def RIFF : Nat := fourcc 'R' 'I' 'F' 'F'
def WEBP : Nat := fourcc 'W' 'E' 'B' 'P'
def VP8  : Nat := fourcc 'V' 'P' '8' ' '
def VP8L : Nat := fourcc 'V' 'P' '8' 'L'
def VP8X : Nat := fourcc 'V' 'P' '8' 'X'
def ANIM : Nat := fourcc 'A' 'N' 'I' 'M'
def ANMF : Nat := fourcc 'A' 'N' 'M' 'F'
def ALPH : Nat := fourcc 'A' 'L' 'P' 'H'
def ICCP : Nat := fourcc 'I' 'C' 'C' 'P'
def EXIF : Nat := fourcc 'E' 'X' 'I' 'F'
def XMP  : Nat := fourcc 'X' 'M' 'P' ' '

/-- Bit number `i` of the stream `d`: bytes in order, least-significant bit first (§3.2). -/
def bit (d : ByteArray) (i : Nat) : Nat :=
  byte d (i / 8) / 2 ^ (i % 8) % 2

/-- The value of `ReadBits(n)` executed at bit position `pos`: the first bit read is the least
significant bit of the result (§3.2). -/
def readBitsVal (d : ByteArray) (pos : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bit d pos + 2 * readBitsVal d (pos + 1) n

/-- Error raised whenever the decoder needs bits beyond the end of the data. -/
def eofMsg : String := "unexpected end of bitstream"

/-- `ReadBits(n)` at bit position `pos`, returning the value and the new position. Reading past
the end of the data is an error (the stream has exactly `8 * d.size` bits). -/
def readBits (d : ByteArray) (pos n : Nat) : Except String (Nat × Nat) :=
  if pos + n ≤ 8 * d.size then .ok (readBitsVal d pos n, pos + n) else .error eofMsg

end WebP.Spec
