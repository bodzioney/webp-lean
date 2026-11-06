/* compat shim: vpx_image.c includes "vpx/vpx_image.h" (libvpx tree layout);
 * the RFC ships vpx_image.h at the top level. */
#include "../../gen/vpx_image.h"   /* build.sh copies src/ to gen/ */
/* RFC 6386 vpx_image.h spells this enumerator VPX_IMGFMT_RGB555 (typo carried
 * over from libvpx of that era) while vpx_image.c uses VPX_IMG_FMT_RGB555. */
#ifndef VPX_IMG_FMT_RGB555
#define VPX_IMG_FMT_RGB555 VPX_IMGFMT_RGB555
#endif
