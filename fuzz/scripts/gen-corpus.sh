#!/usr/bin/env bash
# Builds the seed corpus for the `diff` fuzz target into fuzz/corpus/diff.
# Sources: libwebp-test-data, image-webp test images, and files generated with libwebp tools
# from small synthetic images (scripts/make_sources.py). Large files (> MAX bytes) are dropped.
set -uo pipefail
ROOT=/var/data/diff-fuzz/webp
T=$ROOT/build/libwebp-tools
FZ=$ROOT/fuzz
SRC=$FZ/corpus-gen/src
GEN=$FZ/corpus-gen/out
OUT=$FZ/corpus/diff
MAX=${MAX:-65536}
mkdir -p "$SRC" "$GEN" "$OUT"
python3 -I "$FZ/scripts/make_sources.py" "$SRC"

[ -d "$ROOT/corpus-src/libwebp-test-data" ] || git clone --depth 1 https://chromium.googlesource.com/webm/libwebp-test-data "$ROOT/corpus-src/libwebp-test-data"

enc() { # enc <out-name> <src> <cwebp args...>
  local name=$1 src=$2; shift 2
  "$T/cwebp" -quiet "$@" "$src" -o "$GEN/$name.webp" 2>/dev/null || true
}
i=0
for s in "$SRC"/*; do
  b=$(basename "${s%.*}")
  i=$((i+1))
  # lossless, all effort levels spread across sources
  enc "$b.ll.z$((i % 10))" "$s" -lossless -z $((i % 10))
  enc "$b.ll.exact" "$s" -lossless -exact -m $((i % 7))
  [ $((i % 3)) = 0 ] && enc "$b.nl$((i % 5 * 20))" "$s" -near_lossless $((i % 5 * 20))
  # lossy
  enc "$b.q$((i * 17 % 101))" "$s" -q $((i * 17 % 101)) -m $((i % 7))
  [ $((i % 2)) = 0 ] && enc "$b.lossy.seg" "$s" -q 60 -segments $((1 + i % 4)) -sns $((i * 13 % 101)) -f $((i * 7 % 101)) -sharpness $((i % 8))
  [ $((i % 4)) = 1 ] && enc "$b.sharpyuv" "$s" -q 80 -sharp_yuv
  [ $((i % 5)) = 2 ] && enc "$b.preset" "$s" -preset $(echo photo drawing icon text picture | cut -d' ' -f$((1 + i % 5))) -q 50
  [ $((i % 6)) = 3 ] && enc "$b.pass" "$s" -pass 3 -size 300 -af
  case $s in *.pam)
    for f in none fast best; do
      for am in 0 1; do
        enc "$b.alpha.$f.m$am" "$s" -q 70 -alpha_filter $f -alpha_method $am -alpha_q $((i * 31 % 101))
      done
    done
    enc "$b.noalpha" "$s" -q 70 -noalpha
    enc "$b.alpha.exact" "$s" -q 70 -exact
    ;;
  esac
done

# metadata via webpmux
printf 'fake-icc-profile' > "$GEN/x.icc"; printf 'Exif\0\0MM\0*' > "$GEN/x.exif"; printf '<x:xmpmeta/>' > "$GEN/x.xmp"
n=0
for f in "$GEN"/*_8x8*.webp "$GEN"/*_3x5*.webp; do
  [ -f "$f" ] || continue
  n=$((n+1))
  case $((n % 4)) in
    0) "$T/webpmux" -set icc "$GEN/x.icc" "$f" -o "${f%.webp}.icc.webp" 2>/dev/null ;;
    1) "$T/webpmux" -set exif "$GEN/x.exif" "$f" -o "${f%.webp}.exif.webp" 2>/dev/null ;;
    2) "$T/webpmux" -set xmp "$GEN/x.xmp" "$f" -o "${f%.webp}.xmp.webp" 2>/dev/null ;;
    3) "$T/webpmux" -set icc "$GEN/x.icc" "$f" -o "$GEN/tmp.webp" 2>/dev/null && \
       "$T/webpmux" -set xmp "$GEN/x.xmp" "$GEN/tmp.webp" -o "${f%.webp}.iccxmp.webp" 2>/dev/null ;;
  esac
done
rm -f "$GEN/tmp.webp"

# animations with img2webp (same-size frames)
for sz in 8x8 16x16 13x17 33x33 1x1 3x5; do
  fr=( $(ls "$SRC"/*_"$sz".* 2>/dev/null | head -6) )
  [ ${#fr[@]} -ge 2 ] || continue
  "$T/img2webp" -loop 3 -lossless -d 50 "${fr[0]}" -lossy -q 40 -d 70 "${fr[1]}" ${fr[2]:+-d 0 "${fr[2]}"} -o "$GEN/anim.mixed1.$sz.webp" 2>/dev/null
  "$T/img2webp" -mixed -kmin 1 -kmax 2 "${fr[@]}" -o "$GEN/anim.mixed.$sz.webp" 2>/dev/null
  "$T/img2webp" -lossy -q 30 -kmax 0 "${fr[@]}" -o "$GEN/anim.lossy.$sz.webp" 2>/dev/null
  "$T/img2webp" -lossless -min_size "${fr[@]}" -o "$GEN/anim.minsize.$sz.webp" 2>/dev/null
  "$T/img2webp" -lossless -exact -kmin 3 -kmax 5 -loop 1 "${fr[@]}" "${fr[@]}" -o "$GEN/anim.kf.$sz.webp" 2>/dev/null
done

# animations with explicit offsets / dispose / blend via webpmux -frame
frames=( $(ls "$GEN"/*_8x8.ll.* "$GEN"/*_3x5.ll.* "$GEN"/*_8x8.alpha.*m1.webp "$GEN"/*_13x17.q* 2>/dev/null | head -12) )
k=0
for a in "${frames[@]}"; do
  b=${frames[$(( (k + 3) % ${#frames[@]} ))]}
  c=${frames[$(( (k + 5) % ${#frames[@]} ))]}
  k=$((k+1))
  d1=$((k % 2)); d2=$(((k / 2) % 2))
  bl1=$([ $((k % 3)) = 0 ] && echo -b || echo +b)
  bl2=$([ $((k % 4)) = 1 ] && echo -b || echo +b)
  "$T/webpmux" -frame "$a" +80+0+0+$d1$bl1 -frame "$b" +40+$((k % 3 * 2))+$((k % 4 * 2))+$d2$bl2 \
      -frame "$c" +0+2+2+0+b -loop $((k % 3)) -bgcolor $((k * 37 % 256)),$((k * 91 % 256)),20,$((k * 53 % 256)) \
      -o "$GEN/mux.anim.$k.webp" 2>/dev/null
done

# Optional extra: generated VP8L (structure-aware generator), if the CLI is built.
if [ -x "$FZ/target/release/webp-diff-mutate" ]; then
  "$FZ/target/release/webp-diff-mutate" --gen "$GEN" --count 150 --seed 42
fi

# collect
find "$GEN" "$ROOT/corpus-src/libwebp-test-data" "$ROOT/image-webp/tests/images" -name '*.webp' -size -${MAX}c -print0 |
  while IFS= read -r -d '' f; do
    h=$(sha1sum "$f" | cut -c1-40)
    cp "$f" "$OUT/$h"
  done
echo "corpus: $(ls "$OUT" | wc -l) files, $(du -sh "$OUT" | cut -f1)"
