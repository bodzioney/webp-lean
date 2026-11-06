# webp-diff: differential fuzzer for WebP decoders

Compares four decoders on every input:

| oracle         | what                                                                 |
|----------------|----------------------------------------------------------------------|
| `lean`         | the Lean decoder (`../webp-lean`), via FFI (`csrc/lean_shim.c`)       |
| `libwebp`      | libwebp `WebPDecode` → RGBA (still images; animated → skipped)        |
| `libwebp-anim` | libwebp `WebPAnimDecoder` (demux path), every composited frame         |
| `image-webp`   | `../image-webp` (Rust), default options, RGB normalized to RGBA       |

All outcomes are normalized to `Ok{width,height,frames:[(duration,rgba)],..} | Err(msg) | Skip(reason)`.
Inputs whose declared canvas/frame/bitstream size exceeds `WEBP_DIFF_MAX_PIXELS` (default 2^22) or
whose frames×canvas exceeds `WEBP_DIFF_MAX_TOTAL` (2^24) are skipped by all oracles (cheap header
probe in `src/probe.rs`); the Lean decoder also receives the limit (`maxPixels`).
Lean status 2 (resource limit) is a `Skip`; the old stub message `not implemented` is also a `Skip`.
The VP8X canvas is probed from the 10 bytes after the VP8X header even if the chunk is declared
shorter (image-webp reads it from there and would otherwise allocate GBs).

## Layout

```
fuzz/
  Cargo.toml, build.rs      webp-diff library + CLIs; build.rs links libwebp + Lean (see below)
  csrc/libwebp_shim.c       C ABI over WebPDecode / WebPAnimDecoder
  csrc/lean_shim.c          Lean runtime init + webp_lean_decode_impl wrapper (panic => exit)
  src/oracles.rs            the four oracles, Lean wire-format parser (../DESIGN.md)
  src/compare.rs            comparator, signatures, findings recording, WEBP_DIFF_ABORT
  src/probe.rs              header probe / resource limits
  src/riff.rs               tolerant RIFF chunk tree (exact round-trip)
  src/mutate.rs             format-aware mutator + crossover
  src/vp8l_gen.rs           structure-aware random VP8L / ALPH bitstream generator
  src/bin/webp-diff-run.rs  triage CLI
  src/bin/webp-diff-mutate.rs  offline mutator / generator / validity stats
  fuzz/fuzz_targets/diff.rs cargo-fuzz target (fuzz_target! + fuzz_mutator! + fuzz_crossover!)
  scripts/build-libwebp.sh  builds build/libwebp-fuzz/{asan,cov,plain}
  scripts/gen-corpus.sh     builds corpus/diff (scripts/make_sources.py makes PAM/PPM sources)
  scripts/run-fuzz.sh       runs a campaign (fork mode)
  webp.dict, lsan.supp
  corpus/diff/              seed corpus;  findings/<signature>/  discrepancy inputs + reports
  artifacts/diff/           crashes / timeouts from libFuzzer
```

## Build

```sh
scripts/build-libwebp.sh            # asan, cov, plain variants of libwebp (static, clang)
(cd ../webp-lean && lake build)     # emits .lake/build/ir/**/*.c that build.rs compiles
cargo build --release               # CLIs (plain variant)
cargo fuzz build diff               # ASan fuzz target   (or: cargo fuzz build -s none diff)
```

Linking details (build.rs):
* libwebp variant is picked from RUSTFLAGS (`asan` if `-Zsanitizer=address`, `cov` if sancov,
  else `plain`), or forced with `WEBP_DIFF_VARIANT`.
* Lean: by default the Lean-emitted C (`webp-lean/.lake/build/ir/WebP*.c`) is compiled here with
  `-fsanitize=fuzzer-no-link`, so libFuzzer also gets coverage from the Lean decoder.
  `WEBP_DIFF_LEAN_MODE=staticlib` links `libwebp_WebP.a` (from `lake build WebP:static`) instead.
  Re-run `lake build` before `cargo` after changing Lean code (build.rs tracks the .c files).
* The Lean runtime is `libleanshared.so` (rpath set). It bundles its own libc++ and exports LLVM
  libunwind's `_Unwind_*`; `lean_shim.c` references `_Unwind_RaiseException` so libgcc_s is
  ordered first and Rust panics keep unwinding correctly.
* A Lean `panic!` exits the process (`lean_set_exit_on_panic`) => libFuzzer records a crash.
  `WEBP_DIFF_LEAN_PANIC_OK=1` disables that.

## Run

```sh
scripts/run-fuzz.sh asan 16                     # ASan, 16 fork workers
scripts/run-fuzz.sh none 32 -max_total_time=3600 # coverage-only build, ~4x faster
# equivalent raw invocation:
cargo fuzz run diff corpus/diff -- -dict=webp.dict -max_len=65536 -timeout=30 \
    -rss_limit_mb=4096 -fork=16 -ignore_crashes=1 -ignore_timeouts=1 -ignore_ooms=1
```
(For ASan runs export `LSAN_OPTIONS=suppressions=$PWD/lsan.supp` — the Lean runtime leaks a few
GMP blocks at init; `run-fuzz.sh` does this.) Logs: `logs/fuzz/`.

Environment knobs:

| var | default | meaning |
|-----|---------|---------|
| `WEBP_DIFF_ABORT` | (none) | comma-separated signature prefixes (or `all`) that abort ⇒ libFuzzer saves a crash, e.g. `pixels-lossless,accept-reject` |
| `WEBP_DIFF_FINDINGS` | `fuzz/findings` | where discrepancy inputs go (`off` to disable) |
| `WEBP_DIFF_CAP` | 25 | max stored inputs per signature |
| `WEBP_DIFF_SOFT_PANIC` | (none) | oracles (`image-webp`, `all`, ...) whose panics become a `crash:<oracle>` finding instead of a crash — use once a panic is known so it doesn't dominate the campaign |
| `WEBP_DIFF_DISABLE` | (none) | oracles to skip, e.g. `image-webp` |
| `WEBP_DIFF_LOSSY_TOL` | 0 | per-channel tolerance for image-webp on lossy images |
| `WEBP_DIFF_ANIM_TOL` | 1 | per-channel tolerance, image-webp vs libwebp-anim on animations (blend rounding) |
| `WEBP_DIFF_LEAN_ANIM_TOL` | 2 | per-channel tolerance for pairs with Lean on animations (Lean blends with the exact RFC formula, rounded half-up) |
| `WEBP_DIFF_MAX_PIXELS` / `WEBP_DIFF_MAX_TOTAL` | 2^22 / 2^24 | resource limits |

## Signatures

* `crash:<oracle>` — oracle panicked (soft-panic mode / triage CLI only).
* `accept-reject:ok=<oracles>:err=<oracles>` — some decoders accept, others reject.
* `dims:<a>-vs-<b>`, `frames-count:..`, `durations:..`, `loop-count:..`.
* `pixels-{lossless|lossy}[-anim]:<a>-vs-<b>[:alpha-only]` — pixel mismatch beyond tolerance
  (lossy = any `VP8 ` chunk in the file). `:alpha-only` = RGB identical, only alpha differs.
  Still images: exact (image-webp lossy: `WEBP_DIFF_LOSSY_TOL`).
  Animations: pixels with alpha 0 in both outputs compare equal regardless of RGB (libwebp's
  keyframe shortcut keeps RGB of transparent pixels; the RFC blend formula zeroes it); other
  pixels use the tolerances above; the max deviation seen within tolerance for Lean pairs is
  printed by `webp-diff-run --summary`.
* `pixels-*-anim:<a>-vs-<b>:hard` — mismatch inside the rectangle of a frame drawn with
  blending method 1 (no blend): must be exact, so this is a real bug, not rounding.
* `libwebp-reads-past-bitstream-chunk:<original signature>` — a lean/libwebp disagreement on a
  still image that disappears when libwebp is given only the bytes up to the end of the `VP8 `
  chunk (libwebp's simple API lets the VP8 decoder read past the chunk into following bytes;
  Lean decodes exactly the chunk payload).

* `pixels-*-anim:<a>-vs-<b>:translucent` — beyond-tolerance animation pixels, none of which is
  opaque in both outputs: blend-rounding amplification at low alpha (libwebp's 8-bit blend
  approximation compounds across frames). Untagged anim mismatches involve opaque pixels.
* `known:<class>[+<class>]:<signature>` — a discrepancy involving Lean in a file that matches a
  triaged class (header-level classifier `compare::known_classes`, also printed as
  `known classes:` by `webp-diff-run`):
  * `vp8x-oversized` — VP8X payload > 10 bytes; RFC: unknown fields MUST be ignored. Lean accepts, libwebp/image-webp reject (they are too strict).
  * `alph-reserved-or-preproc` — ALPH reserved bits != 0 or preprocessing ∈ {2,3}; RFC: MUST ignore. Lean accepts, libwebp & image-webp reject.
  * `simple-extra-recon-chunk` — simple file (no VP8X) followed by ALPH/VP8/VP8L/VP8X/ANIM/ANMF/ICCP; Lean rejects by the grammar.
  * `simple-trailing-data` — simple file with other bytes after the bitstream chunk inside the RIFF size; Lean rejects.
  * `anmf-known-subchunk` — a known non-frame chunk (e.g. nested ANMF) inside ANMF frame data; Lean rejects; libwebp's WebPAnimDecoder plays nested ANMFs as extra frames (libwebp demux bug).
  * `still-stray-anim` — VP8X without animation flag but with an ANIM chunk after the image; RFC says ANIM "MUST be ignored", Lean rejects it as out-of-order.
  * `iccp-after-image` — ICCP after the image data; Lean rejects (order), libwebp accepts.
  * `alph-raw-size` — raw ALPH whose size != width*height; Lean rejects, libwebp accepts >= w*h.

Known oracle notes: libwebp is built with SIMD (SSE2/SSE4.1) enabled, which the Lean VP8 decoder
matches; a no-SIMD libwebp may legitimately differ on corrupted streams (C vs SSE2 IDCT overflow).

Each finding is `findings/<signature>/<sha1>.webp` + `<sha1>.txt` (the triage report).

## Triage

```sh
./target/release/webp-diff-run findings/<sig>/<sha1>.webp      # per-oracle outcome + diffs
./target/release/webp-diff-run --quiet --summary corpus/diff   # histogram over a directory
./target/release/webp-diff-run --dump out/ file.webp            # raw RGBA per oracle/frame
scripts/triage-all.sh OUT corpus/diff findings artifacts/diff  # re-triage with current rules
./target/release/webp-diff-mutate in.webp out.webp --seed 7     # one mutation, offline
./target/release/webp-diff-mutate --stats some_dir --iters 20   # mutant validity rate
./target/release/webp-diff-mutate --gen out_dir --count 100     # generated VP8L/animated files
../build/libwebp-tools/webpinfo -diag file.webp                 # libwebp's chunk view
cargo fuzz tmin diff artifacts/diff/crash-...                   # minimize a crash
```

## Mutator (src/mutate.rs)

Parses into a RIFF chunk tree (ANMF = 16-byte header + sub-chunks; unparseable bytes kept), then
applies 1–5 of: delete / duplicate / swap / move chunks (top level or inside an ANMF); insert
ICCP/EXIF/XMP/ANIM/ALPH/VP8X/VP8L/ANMF/unknown chunks; change FourCC; truncate payloads;
field edits (VP8X flags & canvas, ANIM bg/loop, ANMF x/y/w/h/duration/blend/dispose, ALPH
header bits, VP8L signature/dims/alpha/version, VP8 keyframe/version/show/partition size/start
code/dims/scale); libFuzzer byte mutation of one payload; LSB-first bit flips in VP8L/ALPH
streams (biased to the header/prefix-code area); regenerate a VP8L or ALPH payload with the
generator; "make consistent" (flags, canvas, frame dims, ANIM presence); promote simple →
extended (+ALPH) and still → animated. Then sizes are fixed up (15/16) or left stale (1/16), and
rarely the file is truncated. Crossover splices chunks/frames between two inputs.
20% of mutations are plain libFuzzer mutations.

The generator (src/vp8l_gen.rs) emits random but mostly valid VP8L streams: random dims, a random
subset/order of the four transforms (predictor modes incl. 14/15, color indexing with 1–256
colors ⇒ pixel bundling), color cache 1–11 bits, meta prefix codes with an entropy image,
simple and normal code-length codes (random complete trees ≤15 bits, run-length symbols
16/17/18, optional `max_symbol`), and literal / backward-reference (with the 120-entry distance
map) / color-cache pixels. It simulates decoding to keep group indices, distances and lengths in
range. In 1/8 of streams ("evil") it injects specific invalidities (incomplete/over-subscribed
codes, bad cache bits, out-of-range backrefs, `max_symbol` overflow, duplicate transform, bad
version/signature, truncation).

## Repro sets (fuzz/repro/)

* `lean-vp8-pixels/` — VP8-only still images (the VP8 chunk isolated from fuzzer findings) where
  Lean's pixels differ from libwebp (`dwebp` and all libwebp builds agree with each other).
* `lean-vp8-eof/` — VP8 stills Lean decodes but libwebp rejects (NOT_ENOUGH_DATA /
  BITSTREAM_ERROR): end-of-partition handling differs.
* `lean-vp8-colorspace/` — Lean rejects VP8 `color_space = 1` ("reserved"); libwebp ignores it.
* `libwebp-alph-lenient/` — lossless ALPH stream that libwebp's alpha path accepts but libwebp's
  own VP8L decoder (stream re-wrapped as VP8L), Lean and image-webp reject.
