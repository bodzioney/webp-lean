import WebP.Spec.Alpha
/-!
# Alpha unfiltering, in place (one pass in scan order)

Proven equal to the declarative `Spec.Alpha.unfilter` in `WebP.Proofs.Alpha`.
-/
namespace WebP.Alpha

open WebP.Spec

/-- Reconstruct the alpha plane in place: when pixel `i` is processed, entries `< i` already
hold reconstructed values and entry `i` still holds the filtered value. -/
def unfilterLoop (m w : Nat) (raw : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | n + 1, i, out =>
    let v := (Spec.Alpha.predictor m w (fun j => byte out j) i + byte raw i) % 256
    unfilterLoop m w raw n (i + 1) (out.set! i v.toUInt8)

def unfilter (m w h : Nat) (raw : ByteArray) : ByteArray :=
  unfilterLoop m w raw (w * h) 0 ⟨Array.ofFn (n := w * h) fun i => (byte raw i.val).toUInt8⟩

end WebP.Alpha
