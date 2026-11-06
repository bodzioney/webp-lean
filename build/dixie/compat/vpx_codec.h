/* compat shim: minimal replacement for libvpx's vpx/vpx_codec.h (and the
 * encoder types from vpx_encoder.h) which RFC 6386 section 20 does not include,
 * but which vpx_decoder.h / vpx_codec_internal.h reference.
 * Only type declarations; none of these are used by the dixie decode path
 * except vpx_codec_err_t (whose enumerator values follow libvpx). */
#ifndef VPX_CODEC_H
#define VPX_CODEC_H
#include "vpx_integer.h"
#include "vpx_image.h"

/* libvpx defines DEPRECATED as a deprecation attribute; used by vpx_decoder_compat.h */
#ifndef DEPRECATED
#define DEPRECATED
#endif

#define VPX_CODEC_ABI_VERSION (2 + VPX_IMAGE_ABI_VERSION)

typedef enum {
    VPX_CODEC_OK,
    VPX_CODEC_ERROR,
    VPX_CODEC_MEM_ERROR,
    VPX_CODEC_ABI_MISMATCH,
    VPX_CODEC_INCAPABLE,
    VPX_CODEC_UNSUP_BITSTREAM,
    VPX_CODEC_UNSUP_FEATURE,
    VPX_CODEC_CORRUPT_FRAME,
    VPX_CODEC_INVALID_PARAM,
    VPX_CODEC_LIST_END
} vpx_codec_err_t;

typedef long vpx_codec_caps_t;
#define VPX_CODEC_CAP_DECODER 0x1
#define VPX_CODEC_CAP_ENCODER 0x2
#define VPX_CODEC_CAP_XMA     0x4

typedef long vpx_codec_flags_t;
#define VPX_CODEC_USE_XMA 0x00000001

typedef const struct vpx_codec_iface vpx_codec_iface_t;
typedef struct vpx_codec_priv vpx_codec_priv_t;
typedef const void *vpx_codec_iter_t;

typedef struct vpx_codec_ctx {
    const char              *name;
    vpx_codec_iface_t       *iface;
    vpx_codec_err_t          err;
    const char              *err_detail;
    vpx_codec_flags_t        init_flags;
    union {
        struct vpx_codec_dec_cfg *dec;
        struct vpx_codec_enc_cfg *enc;
        void                     *raw;
    } config;
    vpx_codec_priv_t        *priv;
} vpx_codec_ctx_t;

typedef struct vpx_codec_mmap {
    unsigned int   id;
    unsigned long  sz;
    unsigned int   align;
    unsigned int   flags;
    void          *base;
    void         (*dtor)(struct vpx_codec_mmap *map);
    void          *priv;
} vpx_codec_mmap_t;

/* --- encoder-side types (vpx_encoder.h), declared only so that
 *     vpx_codec_internal.h compiles --- */
typedef int64_t vpx_codec_pts_t;
typedef long vpx_enc_frame_flags_t;
typedef struct vpx_fixed_buf { void *buf; size_t sz; } vpx_fixed_buf_t;
typedef struct vpx_codec_enc_cfg { unsigned int g_usage; } vpx_codec_enc_cfg_t;
typedef struct vpx_codec_cx_pkt { int kind; vpx_fixed_buf_t raw; } vpx_codec_cx_pkt_t;

#endif
