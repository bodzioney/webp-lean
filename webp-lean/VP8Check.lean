import WebP.VP8
import WebP.VP8Libwebp
/-!
`vp8-check <in> <pam|yuv|frame|bench|hdr> [out|-] [impl|spec|libwebp]`

Finds the first 'VP8 ' chunk of a RIFF/WEBP file (top level or inside the first ANMF; a file
that is not RIFF/WEBP is taken to be a raw VP8 payload) and decodes it with one of the Lean VP8
decoders:

* `impl` (default) — `WebP.VP8.decodeFrame`, the shipped decoder (proven equal to `spec`);
* `spec`           — `WebP.Spec.VP8.decode`, the RFC 6386 reference decoder transcription;
* `libwebp`        — `WebP.VP8Libwebp`, the libwebp-mimic model. As libwebp's simple API does,
                     it is given all bytes from the VP8 payload to the end of the file.

`impl`/`spec` are given exactly the chunk payload. Modes: `pam` / `yuv` write dwebp-compatible
output (`dwebp -pam` / `dwebp -yuv`); `frame` writes `u32 LE width, u32 LE height, Y, U, V`
(planes cropped, chroma `⌈w/2⌉ × ⌈h/2⌉`); `bench` decodes 5 times and prints the time;
`hdr` prints the dimensions. Exit code 0 = decoded, 1 = rejected.
-/
open WebP.VP8

def rdB (a : ByteArray) (i : Nat) : Nat := if h : i < a.size then a[i].toNat else 0

def le32 (a : ByteArray) (i : Nat) : Nat :=
  rdB a i ||| (rdB a (i+1) <<< 8) ||| (rdB a (i+2) <<< 16) ||| (rdB a (i+3) <<< 24)

def isTag (a : ByteArray) (i : Nat) (t : String) : Bool :=
  let b := t.toUTF8
  rdB a i == rdB b 0 && rdB a (i+1) == rdB b 1 && rdB a (i+2) == rdB b 2 && rdB a (i+3) == rdB b 3

/-- Locate the 'VP8 ' chunk: returns (payload offset, chunk size). -/
def findVP8 (a : ByteArray) (pos stop : Nat) (fuel : Nat := a.size) : Option (Nat × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if pos + 8 > stop then none
    else
      let sz := le32 a (pos + 4)
      if isTag a pos "VP8 " then some (pos + 8, sz)
      else if isTag a pos "ANMF" then findVP8 a (pos + 24) (min stop (pos + 8 + sz)) fuel
      else findVP8 a (pos + 8 + sz + sz % 2) stop fuel

def pushLE32 (b : ByteArray) (v : Nat) : ByteArray :=
  (((b.push (v % 256).toUInt8).push (v / 256 % 256).toUInt8).push (v / 65536 % 256).toUInt8).push
    (v / 16777216 % 256).toUInt8

def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, mode] => run inp mode none "impl"
  | [inp, mode, out] => run inp mode (if out == "-" then none else some out) "impl"
  | [inp, mode, out, dec] => run inp mode (if out == "-" then none else some out) dec
  | _ => IO.eprintln "usage: vp8-check <in> <pam|yuv|frame|bench|hdr> [out|-] [impl|spec|libwebp]"; return 2
where
  run (inp mode : String) (out : Option String) (dec : String) : IO UInt32 := do
    let data ← IO.FS.readBinFile inp
    let isRiff := isTag data 0 "RIFF" && isTag data 8 "WEBP"
    let (off, sz) ← if isRiff then
        match findVP8 data 12 data.size with
        | some r => pure r
        | none => IO.eprintln "no VP8 chunk"; return 3
      else pure (0, data.size)
    let payload := data.extract off (off + sz)
    if mode == "hdr" then
      match readHeader payload with
      | .ok (w, h) => IO.println s!"{w}x{h}"; return 0
      | .error e => IO.eprintln e; return 1
    let decodeOnce : Unit → Except String Frame := fun _ =>
      match dec with
      | "spec" => WebP.Spec.VP8.decode payload
      | "libwebp" => WebP.VP8Libwebp.decodeFrameExt (data.extract off data.size) sz
      | _ => decodeFrame payload
    let n := if mode == "bench" then 5 else 1
    let mut res : Except String Frame := .error "none"
    let t0 ← IO.monoMsNow
    for i in [0:n] do
      res := decodeOnce ()
      -- keep the loop from being optimized into a single call
      if i == n then IO.println ""
    match res with
    | .error e => IO.eprintln s!"decode error: {e}"; return 1
    | .ok f =>
      if mode == "bench" then
        let t1 ← IO.monoMsNow
        let rgba := f.toRGBA
        let t2 ← IO.monoMsNow
        IO.println s!"{dec} {f.width}x{f.height} {(t1 - t0) / n} ms/decode, toRGBA {t2 - t1} ms ({rgba.size})"
        return 0
      let bytes :=
        if mode == "yuv" then f.y ++ f.u ++ f.v
        else if mode == "frame" then pushLE32 (pushLE32 .empty f.width) f.height ++ f.y ++ f.u ++ f.v
        else
          let hdr := s!"P7\nWIDTH {f.width}\nHEIGHT {f.height}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n"
          hdr.toUTF8 ++ f.toRGBA
      match out with
      | some o => IO.FS.writeBinFile o bytes
      | none => (← IO.getStdout).write bytes
      return 0
