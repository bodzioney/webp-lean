import WebP
open WebP WebP.Spec

def writePAM (path : String) (w h : Nat) (rgba : ByteArray) : IO Unit := do
  let hdr := s!"P7\nWIDTH {w}\nHEIGHT {h}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n"
  IO.FS.writeBinFile path (hdr.toUTF8 ++ rgba)

def usage : String :=
  "usage: webp-lean decode <in.webp> <out-prefix>   (writes <out-prefix>.pam or <out-prefix>.<n>.pam)\n" ++
  "       webp-lean info <in.webp>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", inp, out] =>
    let d ← IO.FS.readBinFile inp
    match WebP.decode d with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok o =>
      match o.frames with
      | [(_, c)] => if !o.animated then writePAM (out ++ ".pam") o.width o.height c
                    else writePAM (out ++ ".0.pam") o.width o.height c
      | fs => for ((_, c), i) in fs.zipIdx do writePAM s!"{out}.{i}.pam" o.width o.height c
      pure 0
  | ["info", inp] =>
    let d ← IO.FS.readBinFile inp
    match Container.demux d with
    | .error e => IO.println s!"demux error: {e}"; pure 1
    | .ok L => IO.println (repr L); pure 0
  | _ => IO.eprintln usage; pure 2
