import WebP.Spec.VP8.Frame
import WebP.Spec.VP8.Tables
import WebP.Spec.VP8.BoolDecoder
import WebP.Spec.VP8.Header
import WebP.Spec.VP8.ModeMV
import WebP.Spec.VP8.Tokens
import WebP.Spec.VP8.IdctAdd
import WebP.Spec.VP8.Predict
import WebP.Spec.VP8.LoopFilter
import WebP.Spec.VP8.Dixie
import WebP.Spec.VP8.ToRGBA
/-!
# RFC 6386 (VP8) key-frame decoding: the specification

RFC 6386 §1: "the bitstream is defined by the reference source code and not this narrative".
`WebP.Spec.VP8.decode` is a transcription of that reference decoder ("dixie", RFC 6386 §20),
restricted to decoding a single key frame from a fresh decoder context, as carried by a WebP
'VP8 ' chunk. The module structure follows the reference decoder's files:

| module | reference source |
|---|---|
| `Tables`      | `dequant_data.h`, `vp8_prob_data.h`, `modemv_data.h`, tables of `tokens.c` (generated from the RFC text) |
| `BoolDecoder` | `bool_decoder.h` (§7) |
| `Header`      | header parsing in `dixie.c` (§9, §19.2) |
| `ModeMV`      | `modemv.c`, key-frame part (§11) |
| `Tokens`      | `tokens.c` (§13) |
| `IdctAdd`     | `idct_add.c` (§14.3, §14.4) |
| `Predict`     | `predict.c`, intra part (§12) |
| `LoopFilter`  | `dixie_loopfilter.c` (§15) |
| `Dixie`       | `decode_frame` in `dixie.c` |

`Frame.toRGBA` (`ToRGBA`) is not part of RFC 6386: it is the application-chosen Y'CbCr → RGB
conversion RFC 9649 §2.5 leaves open.

All points where a reading of the C code had to be chosen (C implementation-defined behaviour)
or where the WebP context restricts the bitstream are marked **[interp]**.
-/
