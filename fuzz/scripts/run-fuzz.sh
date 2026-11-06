#!/usr/bin/env bash
# Run the differential fuzzer.
# Usage: scripts/run-fuzz.sh [asan|none] [JOBS] [extra libFuzzer args...]
# Uses libFuzzer fork mode: crashes/timeouts/OOMs are saved to artifacts/ and fuzzing continues.
#   asan (default): ASan + LSan; none: coverage only (faster, uses build/libwebp-fuzz/cov).
# Findings go to fuzz/findings/<signature>/ (see README); crashes to fuzz/artifacts/diff/.
set -euo pipefail
FZ=/var/data/diff-fuzz/webp/fuzz
cd "$FZ"
SAN=${1:-asan}; shift || true
JOBS=${1:-8}; shift || true
export LSAN_OPTIONS="suppressions=$FZ/lsan.supp:print_suppressions=0"
export ASAN_OPTIONS="${ASAN_OPTIONS:-detect_leaks=1:allocator_may_return_null=1}"
export WEBP_DIFF_FINDINGS=${WEBP_DIFF_FINDINGS:-$FZ/findings}
mkdir -p logs/fuzz artifacts/diff corpus/diff
cargo fuzz build -s "$SAN" diff > logs/fuzz/build-$SAN.log 2>&1
BIN=$FZ/fuzz/target/x86_64-unknown-linux-gnu/release/diff
cd logs/fuzz
exec "$BIN" -dict="$FZ/webp.dict" -max_len=65536 -timeout=30 -rss_limit_mb=4096 \
  -artifact_prefix="$FZ/artifacts/diff/" -fork="$JOBS" -ignore_crashes=1 -ignore_timeouts=1 -ignore_ooms=1 \
  "$@" "$FZ/corpus/diff"
