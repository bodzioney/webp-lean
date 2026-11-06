# WebP (RFC 9649) in Lean: formal spec, verified decoder, differential fuzzer

```
rfc/rfc9649.txt      the specification (WebP)
rfc/rfc6386.txt      the VP8 specification (its §20 reference decoder "dixie" defines the bitstream)
webp-lean/           Lean 4 (v4.35.0, core only, no Mathlib)
  WebP/Spec/*        formal specification of RFC 9649
  WebP/Spec/VP8/*    formal specification of RFC 6386 key-frame decoding (transcription of dixie)
  WebP/Container/*   demuxer            ┐
  WebP/VP8L/Fast     lossless decoder   │ the decoder
  WebP/Alpha         alpha unfiltering  │
  WebP/VP8, VP8/*    lossy (VP8) decoder┘ (= Spec.VP8 with a proven one-shift boolean decoder)
  WebP/VP8Libwebp/*  old libwebp-mimic VP8 decoder (differential model of libwebp; not shipped)
  WebP/Decode, FFI   top level + C entry point for the fuzzer
  WebP/Proofs/*      proofs: decoder = spec
build/dixie/         RFC 6386 reference decoder extracted from the RFC text, driver, validation
fuzz/                differential fuzzer: Lean vs libwebp (2 APIs) vs image-webp  (see fuzz/README.md)
libwebp/ image-webp/ reference implementations (git checkouts)
build/libwebp-tools  cwebp/dwebp/img2webp/webpmux/webpinfo
DESIGN.md            Lean <-> fuzzer wire format
```

Build and check everything: `cd webp-lean && lake build` (all proofs are checked as part of the
build; there is no `sorry`, `axiom` or `native_decide`; every decoder theorem depends only on
Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound` — the one sanity lemma
`addGreen_subtractGreen` uses `bv_decide`, i.e. a checked SAT certificate). CLI: `webp-lean decode in.webp out`
(writes PAM), `webp-lean info in.webp` (prints the demuxed layout).

## The specification (`WebP/Spec`)

| file | RFC 9649 | style |
|---|---|---|
| `Bits.lean` | §2.2 uint16/24/32, FourCC; §3.2 `ReadBits` (LSB-first) | functions |
| `Container.lean` | §2.3–§2.7 RIFF chunks, simple/extended layouts, VP8X/ANIM/ANMF, chunk order | **relational grammar** `Demux d L` |
| `Prefix.lean` | §3.7 canonical prefix codes (RFC 1951 assignment), validity, decoding = "the symbol whose codeword is a prefix of the stream" | functions |
| `Lossless.lean` | §3.4–§3.8 header, 4 transforms, LZ77 + distance map, color cache, meta prefix codes, code-length codes | transcription over abstract `ReadBits`/`build` |
| `Alpha.lean` | §2.7.1.2 ALPH header, raw/lossless alpha, filters | **pixel-wise recursive equations** |
| `Anim.lean` | §2.7.1.1, §2.7.2 canvas assembly, blending formula, disposal | pointwise canvas functions |
| `VP8/*.lean` | RFC 6386 key-frame decoding (see below) | transcription of the reference decoder over abstract `Prims` |
| `VP8/ToRGBA.lean` | §2.5 Y'CbCr → RGB, application-chosen (libwebp's fancy upsampling) | functions |
| `Decode.lean` | ties it together: `Spec.Decodes vp8 d out`; `Spec.lossy` | relation |

The 'VP8 ' bitstream is defined by RFC 6386, which RFC 9649 references but does not contain.
`Spec.Decodes` is stated parametrically in the VP8 decoder (`vp8 : ByteArray → Except String
RGBAImage`) and instantiated with **`Spec.lossy`** = `Spec.VP8.decode` + `Frame.toRGBA`.

### RFC 6386 (`WebP/Spec/VP8`)

RFC 6386 §1: "the bitstream is defined by the reference source code and not this narrative".
`Spec.VP8.decode : ByteArray → Except String WebP.VP8.Frame` is a transcription of that reference
decoder (dixie, RFC §20), restricted to one key frame decoded from a fresh decoder context, with
the module structure of dixie's files: `BoolDecoder` (bool_decoder.h), `Header` (dixie.c header
parsing, `dequant_init`), `ModeMV` (modemv.c), `Tokens` (tokens.c), `IdctAdd` (idct_add.c),
`Predict` (predict.c, with dixie's bordered frame buffer and `fixup_left/above`), `LoopFilter`
(dixie_loopfilter.c), `Dixie` (`decode_frame`: per MB row modes, tokens, prediction, loop filter
of the previous row). C semantics are kept (`unsigned int` wrap-around of the bool decoder
value, `short` truncation of coefficients / IDCT and WHT intermediates, arithmetic `>>`), as
are dixie's checks and behaviours (reads past the end of a partition give zeros; non-zero color
space / clamping bits rejected; `sz <= part0_sz + 10`; "Truncated partition"; the dequantizer
cache quirk for a segment with `q = -1`; loop-filter level clamped before and after the deltas).
Tables (`Tables.lean`) are generated from the RFC's C sources by `build/dixie/gen_lean_tables.py`.
**[interp]** choices: non-key frames and `show_frame = 0` frames are rejected (WebP context);
every `vpx_internal_error` aborts decoding (the RFC code never sets `error.setjmp`, so literally
it would continue with corrupt state — undefined behaviour; libvpx sets it);
`data[9] << 24` and `0x01010101 * pixel` (signed-overflow UB) read as the intended bit patterns;
`unsigned int` is 32 bits; `short` stores truncate (two's complement); `>>` of negative `int` is
arithmetic; `t << 31` in `eob_mask` (formally UB) sets bit 31; the YUV → RGB conversion.

Validation against the reference decoder compiled from the RFC text (`build/dixie`, see its
README): the Lean spec, the shipped decoder and dixie agree exactly (accept/reject and planes)
on all valid test vectors and generated files, and on >10,000 corrupted streams.

Every place where the RFC is ambiguous and a reading had to be chosen is marked **[interp]** in
the source (e.g. predictor modes 14/15, single-symbol prefix codes of any length, how
`max_symbol` counts, copies past the image end, simple files followed by unknown chunks).
Application-defined choices: transparent-black background, sRGB-space blending rounded half up.

## What is proven (`WebP/Proofs`)

* `Proofs.Bits.fastReadBits_eq : VP8L.fastReadBits = Spec.readBits` — 32-bit-window bit extraction is `ReadBits`.
* `Proofs.Prefix.fastBuild_eq : VP8L.fastBuild = Spec.Prefix.build` — table + bit-by-bit canonical decoding equals codeword search.
* `Proofs.Lossless.vp8l_decode_eq : VP8L.decode = Spec.VP8L.decode` (and for headerless ALPH streams).
* `Proofs.Alpha.unfilter_eq : Alpha.unfilter = Spec.Alpha.unfilter` — in-place one-pass unfiltering equals the declarative equations.
* `Proofs.Container.demux_iff : Container.demux d = .ok L ↔ Spec.Demux d L` — demuxer sound and complete for the grammar.
* `Proofs.VP8Bool.fastBoolGet_eq : VP8.fastBoolGet = Spec.VP8.boolGet` — the boolean decoder that
  renormalizes with one shift equals dixie's bit-at-a-time `bool_get` on all states.
* `Proofs.decodeFrame_eq : VP8.decodeFrame = Spec.VP8.decode` and
  `Proofs.vp8Decode_eq : WebP.vp8Decode = Spec.lossy` — the lossy decoder is RFC 6386.
* `Proofs.Decode.decodeWith_iff : WebP.decodeWith vp8 d = .ok out ↔ Spec.Decodes vp8 d out` (any `vp8`),
  `decode_iff` for the shipped decoder, `decodes_unique` (the semantics is a function),
  and for the exact function the fuzzer calls: `ffi_sound`, `ffi_complete` (within its resource limit), `ffi_invalid`.
* The same with the concrete lossy semantics: `decode_iff' : WebP.decode d = .ok out ↔
  Spec.Decodes Spec.lossy d out`, `decodes_unique'`, `ffi_sound'`, `ffi_complete'`, `ffi_invalid'`.
* `Proofs.SpecFacts`: sanity checks of the spec against RFC sentences (`ReadBits(2)` example, distance codes, subtract-green inverse).

The lossy decoder is now proven equal to the RFC 6386 transcription. What remains trusted: that
the transcription is faithful to dixie (validated differentially, see `build/dixie`), and the
application-chosen YUV → RGB conversion. RFC 6386 and libwebp agree on valid streams but differ
on corrupted ones (libwebp fails at the end of a partition, ignores color space/clamping bits,
clamps oversized partitions, uses SIMD 16-bit IDCT arithmetic, …): see `build/dixie/README.md`.
`vp8-check <in> <pam|yuv|frame|bench|hdr> [out|-] [impl|spec|libwebp]` runs any of the three
Lean VP8 decoders (`libwebp` = the old libwebp-mimic model in `WebP/VP8Libwebp`).

## Differential fuzzing

See `fuzz/README.md`. Summary of findings is in `FINDINGS.md`.
