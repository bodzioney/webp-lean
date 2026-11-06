#!/usr/bin/env bash
# Build static libwebp (webp, webpdemux, sharpyuv) for the differential fuzzer.
# Usage: build-libwebp.sh [asan|cov|plain|all]
#   asan  : -fsanitize=fuzzer-no-link,address  (for `cargo fuzz run diff`, default sanitizer)
#   cov   : -fsanitize=fuzzer-no-link          (for `cargo fuzz run -s none diff`, faster)
#   plain : no instrumentation                 (for the webp-diff-run / webp-diff-mutate CLIs)
# Output: /var/data/diff-fuzz/webp/build/libwebp-fuzz/<variant>/{libwebp.a,libwebpdemux.a,libsharpyuv.a}
set -euo pipefail
ROOT=/var/data/diff-fuzz/webp
SRC=$ROOT/libwebp
OUT=$ROOT/build/libwebp-fuzz
variants=("${@:-all}")
[[ "${variants[0]}" == all ]] && variants=(asan cov plain)
for v in "${variants[@]}"; do
  case $v in
    asan)  flags="-g -O1 -fno-omit-frame-pointer -fsanitize=fuzzer-no-link,address" ;;
    cov)   flags="-g -O2 -fsanitize=fuzzer-no-link" ;;
    plain) flags="-g -O2" ;;
    *) echo "unknown variant $v" >&2; exit 1 ;;
  esac
  bdir=$OUT/$v/build
  mkdir -p "$bdir"
  echo "== libwebp variant $v ($flags)"
  cmake -S "$SRC" -B "$bdir" -DCMAKE_BUILD_TYPE=None -DCMAKE_C_COMPILER=clang \
    -DCMAKE_C_FLAGS="$flags -fPIC" -DBUILD_SHARED_LIBS=OFF -DWEBP_USE_THREAD=OFF \
    -DWEBP_BUILD_ANIM_UTILS=OFF -DWEBP_BUILD_CWEBP=OFF -DWEBP_BUILD_DWEBP=OFF \
    -DWEBP_BUILD_GIF2WEBP=OFF -DWEBP_BUILD_IMG2WEBP=OFF -DWEBP_BUILD_VWEBP=OFF \
    -DWEBP_BUILD_WEBPINFO=OFF -DWEBP_BUILD_WEBPMUX=OFF -DWEBP_BUILD_EXTRAS=OFF \
    -DWEBP_BUILD_LIBWEBPMUX=OFF > "$OUT/$v.cmake.log" 2>&1
  cmake --build "$bdir" -j"$(nproc)" --target webp webpdemux sharpyuv > "$OUT/$v.build.log" 2>&1
  for l in webp webpdemux sharpyuv; do
    cp "$(find "$bdir" -name "lib$l.a" | head -1)" "$OUT/$v/"
  done
  ls -la "$OUT/$v"/*.a
done
