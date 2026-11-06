#!/usr/bin/env bash
# Re-triage inputs with the *current* comparator (signatures change as rules evolve).
# Usage: scripts/triage-all.sh OUT_DIR INPUT_DIRS...
# Writes OUT_DIR/<signature>/ (cap 3 each), OUT_DIR/summary.txt and OUT_DIR/examples.txt.
set -euo pipefail
FZ=/var/data/diff-fuzz/webp/fuzz
OUT=$1; shift
mkdir -p "$OUT"
cargo build --release --manifest-path "$FZ/Cargo.toml" > "$OUT/build.log" 2>&1
WEBP_DIFF_FINDINGS="$OUT" WEBP_DIFF_CAP=3 "$FZ/target/release/webp-diff-run" --quiet --summary --record "$@" \
  > "$OUT/full.log" 2>/dev/null
sed -n '/== [0-9]* files/,$p' "$OUT/full.log" > "$OUT/summary.txt"
for d in "$OUT"/*/; do
  f=$(ls "$d"*.webp 2>/dev/null | head -1)
  [ -n "$f" ] && echo "$(basename "$d")  $f"
done > "$OUT/examples.txt"
cat "$OUT/summary.txt"
