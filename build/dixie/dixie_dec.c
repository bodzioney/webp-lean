/*
 * dixie_dec: decode ONE VP8 key frame with the RFC 6386 section 20 reference
 * decoder ("dixie") and dump the planes.
 *
 *   dixie_dec <input> <output>
 *
 * Input: if the file starts with "RIFF????WEBP", the payload of the first
 * 'VP8 ' chunk (top-level chunks from offset 12; ANMF chunks are descended
 * into, their sub-chunks start at ANMF payload offset + 16), clamped to the
 * end of the file.  Otherwise the whole file is the raw VP8 payload.
 *
 * Output (on success, exit 0):
 *   u32 LE width, u32 LE height,
 *   Y  (w*h bytes, row-major),
 *   U  (((w+1)/2) * ((h+1)/2) bytes), V (same).
 * On error: "error: <code> <detail>" on stderr, no output file, exit 1.
 *
 * Environment:
 *   DIXIE_DUMP=1       print the parsed frame headers to stderr.
 *   DIXIE_NO_SETJMP=1  do NOT set ctx->error.setjmp (RFC-literal behaviour:
 *                      the RFC code never sets it, so vpx_internal_error()
 *                      only records the error and decoding continues).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>

#include "dixie.h"

static const char *err_name(vpx_codec_err_t e)
{
    switch (e) {
    case VPX_CODEC_OK: return "VPX_CODEC_OK";
    case VPX_CODEC_ERROR: return "VPX_CODEC_ERROR";
    case VPX_CODEC_MEM_ERROR: return "VPX_CODEC_MEM_ERROR";
    case VPX_CODEC_ABI_MISMATCH: return "VPX_CODEC_ABI_MISMATCH";
    case VPX_CODEC_INCAPABLE: return "VPX_CODEC_INCAPABLE";
    case VPX_CODEC_UNSUP_BITSTREAM: return "VPX_CODEC_UNSUP_BITSTREAM";
    case VPX_CODEC_UNSUP_FEATURE: return "VPX_CODEC_UNSUP_FEATURE";
    case VPX_CODEC_CORRUPT_FRAME: return "VPX_CODEC_CORRUPT_FRAME";
    case VPX_CODEC_INVALID_PARAM: return "VPX_CODEC_INVALID_PARAM";
    default: return "VPX_CODEC_?";
    }
}

static const char *out_path;

static int fail(const char *code, const char *detail)
{
    fprintf(stderr, "error: %s %s\n", code, detail ? detail : "");
    if (out_path)
        unlink(out_path);
    return 1;
}

static uint32_t rd32(const unsigned char *p)
{
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

/* Search chunks in [off, end) for the first 'VP8 ' chunk (DFS into ANMF). */
static int find_vp8(const unsigned char *d, uint64_t off, uint64_t end,
                    uint64_t *poff, uint64_t *psz)
{
    while (off + 8 <= end) {
        uint64_t sz = rd32(d + off + 4);
        uint64_t pay = off + 8;
        if (!memcmp(d + off, "VP8 ", 4)) {
            *poff = pay;
            *psz = (pay + sz <= end) ? sz : end - pay;
            return 1;
        }
        if (!memcmp(d + off, "ANMF", 4)) {
            uint64_t sub_end = pay + sz < end ? pay + sz : end;
            if (find_vp8(d, pay + 16, sub_end, poff, psz))
                return 1;
        }
        off = pay + sz + (sz & 1);
    }
    return 0;
}

static int write_plane(FILE *f, const unsigned char *p, int stride,
                       unsigned w, unsigned h)
{
    unsigned y;
    for (y = 0; y < h; y++)
        if (fwrite(p + (ptrdiff_t)y * stride, 1, w, f) != w)
            return -1;
    return 0;
}

static void dump_hdrs(const struct vp8_decoder_ctx *c)
{
    unsigned i;
    const struct vp8_frame_hdr *f = &c->frame_hdr;
    fprintf(stderr, "frame: key=%u ver=%u exp=%u shown=%u part0_sz=%u w=%u h=%u "
            "scale=%u,%u mb=%ux%u\n", f->is_keyframe, f->version,
            f->is_experimental, f->is_shown, f->part0_sz, f->kf.w, f->kf.h,
            f->kf.scale_w, f->kf.scale_h, c->mb_cols, c->mb_rows);
    fprintf(stderr, "segment: enabled=%u update_map=%u update_data=%u abs=%u "
            "quant=[%d %d %d %d] lf=[%d %d %d %d] probs=[%u %u %u]\n",
            c->segment_hdr.enabled, c->segment_hdr.update_map,
            c->segment_hdr.update_data, c->segment_hdr.abs,
            c->segment_hdr.quant_idx[0], c->segment_hdr.quant_idx[1],
            c->segment_hdr.quant_idx[2], c->segment_hdr.quant_idx[3],
            c->segment_hdr.lf_level[0], c->segment_hdr.lf_level[1],
            c->segment_hdr.lf_level[2], c->segment_hdr.lf_level[3],
            c->segment_hdr.tree_probs[0], c->segment_hdr.tree_probs[1],
            c->segment_hdr.tree_probs[2]);
    fprintf(stderr, "loopfilter: simple=%u level=%u sharpness=%u delta_enabled=%u "
            "ref=[%d %d %d %d] mode=[%d %d %d %d]\n",
            c->loopfilter_hdr.use_simple, c->loopfilter_hdr.level,
            c->loopfilter_hdr.sharpness, c->loopfilter_hdr.delta_enabled,
            c->loopfilter_hdr.ref_delta[0], c->loopfilter_hdr.ref_delta[1],
            c->loopfilter_hdr.ref_delta[2], c->loopfilter_hdr.ref_delta[3],
            c->loopfilter_hdr.mode_delta[0], c->loopfilter_hdr.mode_delta[1],
            c->loopfilter_hdr.mode_delta[2], c->loopfilter_hdr.mode_delta[3]);
    fprintf(stderr, "tokens: partitions=%u sizes=[", c->token_hdr.partitions);
    for (i = 0; i < c->token_hdr.partitions && i < MAX_PARTITIONS; i++)
        fprintf(stderr, "%s%u", i ? " " : "", c->token_hdr.partition_sz[i]);
    fprintf(stderr, "]\n");
    fprintf(stderr, "quant: q=%u y1dc=%d y2dc=%d y2ac=%d uvdc=%d uvac=%d\n",
            c->quant_hdr.q_index, c->quant_hdr.y1_dc_delta_q,
            c->quant_hdr.y2_dc_delta_q, c->quant_hdr.y2_ac_delta_q,
            c->quant_hdr.uv_dc_delta_q, c->quant_hdr.uv_ac_delta_q);
    fprintf(stderr, "entropy: skip_enabled=%u skip_prob=%u refresh_entropy=%u\n",
            c->entropy_hdr.coeff_skip_enabled, c->entropy_hdr.coeff_skip_prob,
            c->reference_hdr.refresh_entropy);
    for (i = 0; i < MAX_MB_SEGMENTS; i++)
        fprintf(stderr, "dequant[%u]: idx=%d y1=%d,%d uv=%d,%d y2=%d,%d\n", i,
                c->dequant_factors[i].quant_idx,
                c->dequant_factors[i].factor[0][0], c->dequant_factors[i].factor[0][1],
                c->dequant_factors[i].factor[1][0], c->dequant_factors[i].factor[1][1],
                c->dequant_factors[i].factor[2][0], c->dequant_factors[i].factor[2][1]);
}

int main(int argc, char **argv)
{
    FILE *f;
    unsigned char *buf = NULL;
    long n;
    const unsigned char *data;
    uint64_t size;
    struct vp8_decoder_ctx *ctx;
    vpx_codec_err_t err;

    if (argc != 3) {
        fprintf(stderr, "usage: %s <input> <output>\n", argv[0]);
        return 2;
    }
    out_path = argv[2];

    f = fopen(argv[1], "rb");
    if (!f)
        return fail("io", "cannot open input");
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    buf = malloc(n > 0 ? n : 1);
    if (!buf || (n > 0 && fread(buf, 1, n, f) != (size_t)n))
        return fail("io", "cannot read input");
    fclose(f);

    data = buf;
    size = (uint64_t)n;
    if (n >= 12 && !memcmp(buf, "RIFF", 4) && !memcmp(buf + 8, "WEBP", 4)) {
        uint64_t off, sz;
        if (!find_vp8(buf, 12, (uint64_t)n, &off, &sz)) {
            free(buf);
            return fail("driver", "no VP8 chunk in RIFF/WEBP container");
        }
        data = buf + off;
        size = sz;
    }

    /* WebP-level checks mirroring the Lean spec's [interp] choices. */
    if (size >= 1 && (data[0] & 1) != 0) {
        free(buf);
        return fail("driver", "not a key frame");
    }
    if (size >= 1 && ((data[0] >> 4) & 1) == 0) {
        free(buf);
        return fail("driver", "frame not shown");
    }

    ctx = calloc(1, sizeof *ctx);
    if (!ctx)
        return fail("io", "out of memory");
    vp8_dixie_decode_init(ctx);
    {
        const char *e = getenv("DIXIE_NO_SETJMP");
        /* The RFC code calls setjmp() in vp8_dixie_decode_frame but never sets
         * error.setjmp, so vpx_internal_error() would not longjmp.  libvpx
         * sets this flag around its setjmp; we do the same. */
        ctx->error.setjmp = !(e && *e == '1');
    }
    err = vp8_dixie_decode_frame(ctx, data, (unsigned int)size);
    if (getenv("DIXIE_DUMP"))
        dump_hdrs(ctx);
    if (err != VPX_CODEC_OK) {
        char detail[160];
        snprintf(detail, sizeof detail, "%s", ctx->error.has_detail ?
                 ctx->error.detail : "");
        vp8_dixie_decode_destroy(ctx);
        free(ctx);
        free(buf);
        {
            char code[64];
            snprintf(code, sizeof code, "%d:%s", (int)err, err_name(err));
            return fail(code, detail);
        }
    }

    {
        vpx_image_t *img = &ctx->ref_frames[CURRENT_FRAME]->img;
        unsigned w = ctx->frame_hdr.kf.w, h = ctx->frame_hdr.kf.h;
        unsigned cw = (w + 1) / 2, ch = (h + 1) / 2;
        unsigned char hdr[8];
        for (int k = 0; k < 4; k++) {
            hdr[k] = (unsigned char)((w >> (8 * k)) & 0xff);
            hdr[4 + k] = (unsigned char)((h >> (8 * k)) & 0xff);
        }
        f = fopen(out_path, "wb");
        if (!f)
            return fail("io", "cannot open output");
        if (fwrite(hdr, 1, 8, f) != 8 ||
            write_plane(f, img->planes[PLANE_Y], img->stride[PLANE_Y], w, h) ||
            write_plane(f, img->planes[PLANE_U], img->stride[PLANE_U], cw, ch) ||
            write_plane(f, img->planes[PLANE_V], img->stride[PLANE_V], cw, ch)) {
            fclose(f);
            return fail("io", "cannot write output");
        }
        if (fclose(f))
            return fail("io", "cannot write output");
    }
    vp8_dixie_decode_destroy(ctx);
    free(ctx);
    free(buf);
    return 0;
}
