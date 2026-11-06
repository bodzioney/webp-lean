#!/bin/sh
# Build the RFC 6386 reference decoder driver (dixie_dec) and sanitizer builds.
#   ./build.sh            -> dixie_dec, dixie_dec_asan, dixie_dec_iconv
# src/ is the verbatim RFC extraction (extract_dixie.py); gen/ is a copy with
# compat/rfc_errata.sed applied; compat/ holds the shim headers (see README.md).
set -eu
cd "$(dirname "$0")"
CC=${CC:-clang}

rm -rf gen && mkdir gen
cp src/*.c src/*.h gen/
sed -f compat/rfc_errata.sed src/tokens.c > gen/tokens.c
grep -q '^    short             \*coeffs = tokens->coeffs' gen/tokens.c ||
    { echo "errata fix for tokens.c did not apply" >&2; exit 1; }

SRCS="gen/dixie.c gen/dixie_loopfilter.c gen/idct_add.c gen/modemv.c gen/predict.c gen/tokens.c gen/vpx_image.c dixie_dec.c"
CFLAGS="-std=gnu99 -g -Igen -Icompat -Wall -Wno-unused-function -Wno-unused-variable"

$CC $CFLAGS -O1 -o dixie_dec $SRCS
$CC $CFLAGS -O1 -fno-omit-frame-pointer -fsanitize=address,undefined \
    -o dixie_dec_asan $SRCS
# informational only: implicit integer truncation / sign changes (expected in
# a codec, e.g. int -> short / unsigned char stores)
$CC $CFLAGS -O1 -fno-omit-frame-pointer \
    -fsanitize=undefined,implicit-conversion -o dixie_dec_iconv $SRCS
echo "built: dixie_dec dixie_dec_asan dixie_dec_iconv"

# helper tools linked against the libwebp build in ../libwebp-tools
LW=../libwebp-tools
if [ -f $LW/libwebp.a ]; then
    $CC -O2 -I../../libwebp/src -o tools/vp8enc tools/vp8enc.c \
        $LW/libwebp.a $LW/libsharpyuv.a -lm -lpthread
    $CC -O1 -g -I../../libwebp -I../../libwebp/src -o tools/vp8err tools/vp8err.c \
        $LW/libwebp.a $LW/libsharpyuv.a -lm -lpthread
    echo "built: tools/vp8enc tools/vp8err"
fi
