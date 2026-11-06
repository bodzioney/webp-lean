import WebP.Spec.Bits
/-!
# The WebP container (RFC 9649 §2), as a declarative grammar

`Demux d L` holds when the file `d` is a well-formed WebP file whose reconstruction-relevant
content is `L`. It is a relation, written to mirror the RFC text; `WebP.Container.demux` is an
executable parser and `WebP.Proofs.Container` proves
`demux d = .ok L ↔ Demux d L` (soundness and completeness).

Reading decisions (all MUST-level requirements of §2 are enforced, plus the reader SHOULD of
§2.7 to reject out-of-order reconstruction chunks):

* §2.4: the file size field gives the extent of the chunk list exactly ("the total size of the
  chunks that follow plus 4 bytes for the 'WEBP' FourCC"), is at most `2^32 - 10`, and trailing
  data after it is ignored ("Readers MAY parse such files, ignoring the trailing data").
* §2.3: each chunk is header + payload + one padding byte if the size is odd. The padding
  byte's value is not checked (it only matters for RIFF conformance).
* §2.5/§2.6: a simple file starts with one 'VP8 ' or 'VP8L' chunk. **[interp]** Strictly the
  simple layouts contain nothing else, and §2.7.1.6 only places unknown chunks in extended
  files; but "Readers SHOULD ignore these chunks", and libwebp's own conformance vectors are
  simple files followed by unknown chunks, so further chunks are accepted (and ignored) as long
  as none of them is a reconstruction chunk.
* §2.7: extended files start with 'VP8X' (payload ≥ 10 bytes: "Future specifications may add
  more fields. Unknown fields MUST be ignored."). The chunks needed for reconstruction —
  'VP8X', 'ICCP', 'ANIM', 'ANMF', 'ALPH', 'VP8 ', 'VP8L' — must appear in the order
  `VP8X ICCP* ANIM? (ALPH? bitstream | ANMF+)`; metadata ('EXIF', 'XMP ') and unknown chunks
  "MAY appear out of order", i.e. anywhere after 'VP8X'. Extra 'ICCP' chunks are allowed
  ("readers MAY ignore all except the first one").
* Animation flag set: 'ANIM' (≥ 6 bytes) "MUST appear", followed by at least one 'ANMF'
  ("next chunk in image_data is ANMF MUST be TRUE") and no other image data. Frames must lie
  within the canvas ("VP8X.canvasWidth >= frame_right MUST be TRUE").
* Animation flag clear: 'ANIM' chunks "MUST be ignored" (wherever they are); image data is an
  optional 'ALPH' and one bitstream chunk.
* 'ANMF' payload: 16 header bytes then padded subchunks: at most one 'ALPH' before exactly one
  bitstream chunk ("alpha/bitstream subchunks not found in 'Frame Data' earlier MUST be TRUE"),
  plus unknown chunks, which are ignored. Other *known* chunks (e.g. a nested 'ANMF') are not
  unknown chunks (§2.7.1.6) and make the frame invalid.
* "The product of Canvas Width and Canvas Height MUST be at most 2^32 - 1."
* Reserved bits are ignored ("Readers MUST ignore this field"); the I/E/X/L flags are
  informational and not cross-checked against the chunks present.
-/
namespace WebP.Spec

/-- A chunk: its FourCC, the file offset of its payload, and its payload size. -/
structure Chunk where
  tag : Nat
  off : Nat
  size : Nat
deriving DecidableEq, Repr, Inhabited

/-- §2.3: `[p, stop)` is exactly a sequence of (padded) chunks `cs`. -/
inductive ChunkSeq (d : ByteArray) : Nat → Nat → List Chunk → Prop
  | nil (p : Nat) : ChunkSeq d p p []
  | cons (p stop : Nat) (cs : List Chunk) :
      ChunkSeq d (p + 8 + u32 d (p + 4) + u32 d (p + 4) % 2) stop cs →
      ChunkSeq d p stop (⟨u32 d p, p + 8, u32 d (p + 4)⟩ :: cs)

/-- §2.4 WebP file header, with chunk list `cs`. -/
structure RiffFile (d : ByteArray) (cs : List Chunk) : Prop where
  riff : u32 d 0 = RIFF
  webp : u32 d 8 = WEBP
  sizeMax : u32 d 4 ≤ 2 ^ 32 - 10
  fits : 8 + u32 d 4 ≤ d.size
  chunks : ChunkSeq d 12 (8 + u32 d 4) cs

def isBitstream (tag : Nat) : Bool := tag == VP8 || tag == VP8L

/-- §2.7: chunks "necessary for reconstruction and color correction". -/
def isRecon (c : Chunk) : Bool :=
  c.tag == VP8X || c.tag == ICCP || c.tag == ANIM || c.tag == ANMF || c.tag == ALPH ||
  isBitstream c.tag

/-- Reconstruction chunks of a still image: an 'ANIM' chunk "MUST be ignored" when the
animation flag is not set (§2.7.1.1), wherever it appears. -/
def isStillRecon (c : Chunk) : Bool := isRecon c && c.tag != ANIM

/-- Subchunks of 'ANMF' frame data that are not unknown chunks. -/
def isFrameData (c : Chunk) : Bool := c.tag == ALPH || isBitstream c.tag

/-- FourCCs defined by RFC 9649 §2.7.1. Any other FourCC is an *unknown chunk* (§2.7.1.6). -/
def isKnown (tag : Nat) : Bool :=
  tag == VP8X || tag == ICCP || tag == ANIM || tag == ANMF || tag == ALPH || isBitstream tag ||
  tag == EXIF || tag == XMP

/-- Allowed subchunks of 'ANMF' frame data: "An optional alpha subchunk", "A bitstream
subchunk", "An optional list of unknown chunks" (§2.7.1.1). -/
def frameSubOk (c : Chunk) : Bool := isFrameData c || !isKnown c.tag

/-- Contents of the 'VP8X' chunk (§2.7, Figure 7). -/
structure VP8XInfo where
  flags : Nat
  canvasWidth : Nat
  canvasHeight : Nat
deriving DecidableEq, Repr

def vp8xInfo (d : ByteArray) (c : Chunk) : VP8XInfo :=
  ⟨byte d c.off, u24 d (c.off + 4) + 1, u24 d (c.off + 7) + 1⟩

/-- Flag bits of Figure 7 (MSB-0 numbering: `|Rsv|I|L|E|X|A|R|`). -/
def VP8XInfo.animation (x : VP8XInfo) : Bool := x.flags / 2 % 2 == 1
def VP8XInfo.alpha (x : VP8XInfo) : Bool := x.flags / 16 % 2 == 1

/-- A frame: position/size on the canvas, timing, blending/disposal, and its chunks. -/
structure FrameInfo where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  duration : Nat
  /-- Blending method bit is 0: alpha-blend. -/
  blend : Bool
  /-- Disposal method bit is 1: dispose to background. -/
  dispose : Bool
  alph : Option Chunk
  bits : Chunk
deriving DecidableEq, Repr

/-- §2.7.1.1 'ANMF' header fields (Figure 9). -/
def anmfInfo (d : ByteArray) (c : Chunk) (alph : Option Chunk) (bits : Chunk) : FrameInfo :=
  ⟨2 * u24 d c.off, 2 * u24 d (c.off + 3), u24 d (c.off + 6) + 1, u24 d (c.off + 9) + 1,
   u24 d (c.off + 12), byte d (c.off + 15) / 2 % 2 == 0, byte d (c.off + 15) % 2 == 1,
   alph, bits⟩

/-- Image data of a frame: optional 'ALPH' then one bitstream chunk. -/
def FrameData (core : List Chunk) (alph : Option Chunk) (bits : Chunk) : Prop :=
  core = alph.toList ++ [bits] ∧ (∀ a ∈ alph, a.tag = ALPH) ∧ isBitstream bits.tag = true

/-- §2.7.1.1: chunk `c` is a well-formed 'ANMF' chunk describing frame `f`. -/
def FrameChunk (d : ByteArray) (c : Chunk) (f : FrameInfo) : Prop :=
  c.tag = ANMF ∧ 16 ≤ c.size ∧
  ∃ sub, ChunkSeq d (c.off + 16) (c.off + c.size) sub ∧ sub.all frameSubOk = true ∧
    FrameData (sub.filter isFrameData) f.alph f.bits ∧ f = anmfInfo d c f.alph f.bits

/-- The 'ANMF' chunks `cs` describe the frames `fs`, in order. -/
inductive Frames (d : ByteArray) : List Chunk → List FrameInfo → Prop
  | nil : Frames d [] []
  | cons (c : Chunk) (f : FrameInfo) (cs : List Chunk) (fs : List FrameInfo) :
      FrameChunk d c f → Frames d cs fs → Frames d (c :: cs) (f :: fs)

/-- The reconstruction-relevant content of a file. -/
inductive Layout where
  /-- A still image; `vp8x = none` for the simple formats (§2.5, §2.6). -/
  | still (vp8x : Option VP8XInfo) (alph : Option Chunk) (bits : Chunk)
  /-- An animation (§2.7.1.1): canvas info, ANIM background color and loop count, frames. -/
  | animated (vp8x : VP8XInfo) (background loopCount : Nat) (frames : List FrameInfo)
deriving Repr

/-- Canvas size constraint of §2.7. -/
def canvasOk (x : VP8XInfo) : Prop := x.canvasWidth * x.canvasHeight ≤ 2 ^ 32 - 1

def frameInCanvas (x : VP8XInfo) (f : FrameInfo) : Prop :=
  f.x + f.width ≤ x.canvasWidth ∧ f.y + f.height ≤ x.canvasHeight

instance (x : VP8XInfo) (f : FrameInfo) : Decidable (frameInCanvas x f) := by
  unfold frameInCanvas; infer_instance

/-- **Container specification**: `d` is a well-formed WebP file with content `L`. -/
inductive Demux (d : ByteArray) : Layout → Prop
  /-- §2.5, §2.6 simple formats. -/
  | simple (c : Chunk) (rest : List Chunk) :
      RiffFile d (c :: rest) → isBitstream c.tag = true → rest.filter isRecon = [] →
      Demux d (.still none none c)
  /-- §2.7 extended format, still image. -/
  | still (x : Chunk) (rest iccps : List Chunk) (alph : Option Chunk) (bits : Chunk) :
      RiffFile d (x :: rest) → x.tag = VP8X → 10 ≤ x.size →
      canvasOk (vp8xInfo d x) → (vp8xInfo d x).animation = false →
      rest.filter isStillRecon = iccps ++ alph.toList ++ [bits] →
      (∀ c ∈ iccps, c.tag = ICCP) →
      FrameData (alph.toList ++ [bits]) alph bits →
      Demux d (.still (some (vp8xInfo d x)) alph bits)
  /-- §2.7 extended format, animation (§2.7.1.1, §2.7.2). -/
  | animated (x : Chunk) (rest iccps : List Chunk) (a : Chunk) (anmfs : List Chunk)
      (frames : List FrameInfo) :
      RiffFile d (x :: rest) → x.tag = VP8X → 10 ≤ x.size →
      canvasOk (vp8xInfo d x) → (vp8xInfo d x).animation = true →
      rest.filter isRecon = iccps ++ a :: anmfs →
      (∀ c ∈ iccps, c.tag = ICCP) → a.tag = ANIM → 6 ≤ a.size → anmfs ≠ [] →
      Frames d anmfs frames →
      (∀ f ∈ frames, frameInCanvas (vp8xInfo d x) f) →
      Demux d (.animated (vp8xInfo d x) (u32 d a.off) (u16 d (a.off + 4)) frames)

end WebP.Spec
