import WebP.Decode
/-!
# FFI entry point used by the differential fuzzer (wire format: ../DESIGN.md)
-/
namespace WebP.FFI

open WebP.Spec

def pushLE (b : ByteArray) (v n : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:n] do b := b.push (v / 256 ^ i % 256).toUInt8
  return b

/-- Dimensions of a bitstream chunk from its header, without decoding it. -/
def bitstreamDims (d : ByteArray) (c : Chunk) : Except String (Nat × Nat) :=
  let p := payload d c
  if c.tag = VP8L then do let (w, h, _) ← VP8L.readHeaderOnly p; pure (w, h)
  else VP8.readHeader p

/-- Resource check (status 2 = skip): every image ≤ `maxPixels`, and the total number of
canvas pixels produced ≤ `4 * maxPixels`. -/
def withinLimits (d : ByteArray) (L : Layout) (maxPixels : Nat) : Bool :=
  match L with
  | .still _ _ bits =>
    match bitstreamDims d bits with
    | .ok (w, h) => w * h ≤ maxPixels
    | .error _ => true   -- the decoder will reject it anyway
  | .animated x _ _ frames =>
    let cp := x.canvasWidth * x.canvasHeight
    cp ≤ maxPixels && frames.length * cp ≤ 4 * maxPixels &&
      frames.all fun f => f.width * f.height ≤ maxPixels

def errorResult (status : UInt8) (msg : String) : ByteArray :=
  (ByteArray.mk #[status]) ++ msg.toUTF8

def serialize (o : Output) : ByteArray := Id.run do
  let mut b := ByteArray.mk #[0]
  b := pushLE b o.width 4
  b := pushLE b o.height 4
  let flags := (if o.animated then 1 else 0) + (if o.hasAlpha then 2 else 0) +
    (if o.lossy then 4 else 0)
  b := b.push flags.toUInt8
  b := pushLE b o.loopCount 2
  b := pushLE b o.background 4
  b := pushLE b o.frames.length 4
  for (dur, canvas) in o.frames do
    b := pushLE b dur 4
    b := b ++ canvas
  return b

/-- Decoding with the resource check: errors carry the FFI status (1 = invalid, 2 = skip). -/
def decodeChecked (data : ByteArray) (maxPixels : Nat) : Except (UInt8 × String) Output :=
  match Container.demux data with
  | .error e => .error (1, e)
  | .ok L =>
    if !withinLimits data L maxPixels then .error (2, "resource limit")
    else match decodeLayout (implComponents vp8Decode) data L with
      | .ok o => .ok o
      | .error e => .error (1, e)

/-- Decode `data`. Takes ownership of `data`. -/
@[export webp_lean_decode_impl]
def decodeFFI (data : ByteArray) (maxPixels : UInt64) : ByteArray :=
  match decodeChecked data maxPixels.toNat with
  | .ok o => serialize o
  | .error (s, e) => errorResult s e

end WebP.FFI
