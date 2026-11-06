# Differential fuzzing findings

Oracles: the Lean decoder (spec-proven), libwebp `WebPDecode` (simple API), libwebp
`WebPAnimDecoder` (demux path), image-webp 0.2.4. Paths are relative to `fuzz/`.
Every cited example input is in `fuzz/repro/`. The full triage directories (`fuzz/findings-triaged/`,
`fuzz/findings-vp8spec/`, hundreds of MB) are local campaign output and not committed;
`webp-diff-run --summary <file>` reproduces any entry.

Campaign: 32 workers × 25 min, 2.16M execs, ~1.4k exec/s (the Lean decoder is the
bottleneck, ~9 ms/input). Corpus 1,526 seeds → 6,922. 31% of mutants remain decodable by
libwebp; the structure-aware VP8L generator yields 79% decodable streams.

## Bugs in the reference implementations

| # | Implementation | Finding | Example |
|---|---|---|---|
| 1 | image-webp | **Panics** (index out of bounds) in `lossy/yuv.rs:90/147/286` and `decoder.rs:852`: the animated ALPH+VP8 frame path never checks the VP8 bitstream size against the ANMF frame size | `repro/image-webp-panic/020ebf0d….webp` |
| 2 | image-webp | **Allocates 2–9 GB** despite its memory limit: a VP8X chunk shorter than 10 bytes makes it read the canvas size from the following bytes | `repro/image-webp-oom/oom-0a70…` |
| 3 | image-webp | Lossless: drops alpha when the VP8L `alpha_is_used` hint is 0 (RFC 9649 §3.4: the hint "SHOULD NOT impact decoding") | `repro/image-webp-lossless-alpha-hint/008103ec….webp` |
| 4 | image-webp | Lossless: out-of-range palette index decodes to opaque black; RFC 9649 §3.5.4 says transparent black `0x00000000` | `../corpus-src/libwebp-test-data/bad_palette_index.webp` |
| 5 | libwebp demux / `WebPAnimDecoder` | A known chunk (e.g. a nested ANMF) inside ANMF frame data is played as extra frames (16 frames from a file with 14 ANMF chunks). RFC 9649 §2.7.1.6: only *unknown* chunks may follow the bitstream in a frame | `repro/nested-anmf/0f53f2e0….webp` |
| 6 | libwebp `WebPAnimDecoder` | Accepts a frame whose bitstream size differs from the ANMF frame size | `repro/libwebp-anim-frame-size-mismatch/0dc62095….webp` |
| 7 | libwebp (internal inconsistency) | VP8X alpha flag 0 + an ALPH chunk: `WebPDecode` applies (or fails on) the alpha, `WebPAnimDecoder` silently ignores it | `repro/libwebp-alpha-flag-inconsistency/078e12b1….webp` |
| 8 | libwebp (internal inconsistency) | An ALPH lossless stream rejected by libwebp's own VP8L decoder (and by Lean and image-webp) is accepted by libwebp's alpha-plane path | `repro/libwebp-alph-lenient/9bebfef3…` |
| 9 | libwebp simple API | Reads past the end of the 'VP8 '/'VP8L' chunk (into following chunks and the padding byte); decoding succeeds only because of bytes outside the chunk. Not a memory-safety issue: reads stay within the caller's buffer (`webp_dec.c:493`); all 19 files, cut at every byte and decoded from exactly-sized heap buffers via `WebPDecodeRGBA` and `WebPIUpdate` under ASan+UBSan, are clean. It is a parser differential (pixels/acceptance depend on bytes of following chunks) | `repro/libwebp-reads-past-chunk/1a4dcdaf….webp` |
| 10 | libwebp, image-webp | **RFC violation:** reject ALPH chunks with nonzero reserved bits or preprocessing ∈ {2,3}; RFC 9649 §2.7.1.2: "Readers MUST ignore this field" | `repro/alph-reserved-bits/5920053f….webp` |
| 11 | libwebp, image-webp | **RFC violation:** reject a VP8X payload longer than 10 bytes; RFC 9649 §2.7: "Future specifications may add more fields. Unknown fields MUST be ignored." | `repro/vp8x-oversized/1e744a25….webp` |
| 12 | libwebp `WebPAnimDecoder` | **Skips alpha-blending based on the VP8L `alpha_is_used` hint.** `IsKeyFrame` (`anim_decode.c:208`) treats a full-canvas frame with `!has_alpha` as a key frame and draws it unblended; for VP8L frames `has_alpha` is the header hint, which RFC 9649 §3.4 says "SHOULD NOT impact decoding". A frame with translucent pixels but hint 0 is composited wrongly (alpha 206 instead of 246 in the example). Setting the hint bit makes libwebp match Lean exactly. Explains all 26 lossless-animation alpha mismatches of campaign 2 | `repro/libwebp-anim-alpha-hint/02cffeaf….webp` (+ `-alpha_is_used-set` variant) |

## Campaign 2 (after replacing the VP8 decoder with the RFC 6386-proven one)

32 workers × 30 min (incl. ~10 min single-process corpus replay), 2.0M execs, 0 crashes/OOMs/
timeouts, findings in `fuzz/findings-vp8spec/`. Every VP8 payload (2,732 distinct, top-level and
inside ANMF) from findings involving Lean was re-decoded by the RFC 6386 reference decoder:
Lean and dixie agree on all of them (2,327 identical decodes, 405 identical rejections). So
every Lean-vs-libwebp lossy difference is a libwebp-vs-RFC 6386 divergence (section below).
Lossless still images: no Lean-vs-libwebp difference. Lossless animations: 26 alpha
mismatches = finding 12; the remaining ones are blend rounding compounded over many frames at
very low alpha (RFC formula vs libwebp's integer approximation). No new Lean issue was found.

## Lean-side issues found by the fuzzer (fixed)

* Nested known chunks inside ANMF were ignored instead of rejected (spec reading too lenient) — fixed in spec + demuxer + proof.
* An ANIM chunk after the image data of a still image was rejected; RFC 9649 §2.7.1.1 says it "MUST be ignored" when the animation flag is clear — fixed in spec + demuxer + proof.
* VP8 lossy stills: 16 corrupted streams where the earlier (libwebp-modelled, unverified) VP8
  decoder differed from libwebp (`repro/lean-vp8-pixels/`), plus end-of-partition and
  `color_space` handling differences. That decoder has been replaced by one proven equal to a
  formalization of RFC 6386's normative reference decoder — see the RFC 6386 section below.
  All 16 now decode identically under the RFC 6386 reference decoder, the Lean spec and the
  Lean decoder; their old mismatch was libwebp's SSE2 vs portable-C IDCT overflow behaviour.

## Expected differences (strict reading of RFC 9649 by Lean)

| Class | Lean | Others |
|---|---|---|
| Simple-format file followed by another reconstruction chunk (e.g. VP8 then ALPH) | reject (out of order) | accept |
| ICCP after the image data ("MUST appear before the image data") | reject | libwebp accepts |
| Raw ALPH of size ≠ width×height ("length = width * height") | reject | libwebp accepts ≥ |
| Animated: blending | exact RFC formula, rounded | integer approximations (differences ≤ 2 seen, only in translucent pixels; fully transparent pixels keep RGB in libwebp's keyframe path) |

No discrepancy was found between Lean and libwebp on lossless images, on alpha planes, or on
the composited pixels of opaque/non-blended animation frames (other than findings 5–6).

## libwebp vs RFC 6386 (VP8 lossy)

RFC 6386 §1: "The bitstream is defined by the reference source code" (dixie, §20). Dixie was
extracted from the RFC text and compiled (`build/dixie/`); the Lean spec/decoder match it
exactly (accept/reject and Y/U/V planes) on 564 valid, 10,241 corrupted, 80 crafted and 625
fuzzer/mutation streams. On valid encoder output dixie, libwebp (SSE2 and `-noasm`) and Lean
all agree. On the 10,241 corrupted streams libwebp deviates from RFC 6386 on 3,140
(examples in `build/dixie/examples/`, reports in `build/dixie/reports/`):

| # | Divergence | Files |
|---|---|---|
| 1 | Token partition exhausted: RFC bool decoder reads zeros; libwebp "Premature end-of-file" | 1305 |
| 2 | First partition exhausted: libwebp "end-of-partition0" / "cannot parse segment/filter header" | 1589 |
| 3 | libwebp rejects a token partition starting with 0xFF even if never read | 206 |
| 4 | libwebp rejects an empty last partition (also when every macroblock is skipped) | — |
| 5 | color_space/clamping_type ≠ 0: RFC reference rejects ("Reserved bits not supported"), libwebp ignores | 17 |
| 6 | Segmentation enabled with no segment data: RFC uses delta mode, libwebp absolute mode → different pixels | — |
| 7 | Loop-filter level: RFC clamps before and after deltas, libwebp only after | — |
| 8 | Segment quantizer index −1 without update: RFC's dequant cache zeroes all factors | crafted |
| 9 | IDCT/WHT overflow: RFC stores the first pass in `short`; libwebp C uses `int`, SSE2 wraps every op at 16 bits | 20 pixel diffs |
| 10 | libwebp disagrees with itself (SSE2 vs `-noasm`) on overflowing coefficients | 11 of the 20 |

Also found in the RFC itself: a typo in the attached `tokens.c` (`short coeffs` → `short *coeffs`)
that prevents it from compiling, and the code never sets `error.setjmp`, so read literally it keeps
decoding after an error on corrupt state (1,941 of the 10,241 corrupted files crash under ASan).
The Lean spec aborts on every `vpx_internal_error`, as libvpx does (marked `[interp]`), along with
three integer-overflow undefined behaviours UBSan reports (`tokens.c:283`, `predict.c:1382`,
`dixie.c:511`), which are given their intended meaning.
