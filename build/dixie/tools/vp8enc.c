/* vp8enc: encode a binary PPM (P6) with libwebp's lossy encoder, exposing the
 * WebPConfig fields cwebp does not (notably `partitions`, i.e. 1/2/4/8 token
 * partitions).
 *   vp8enc in.ppm out.webp key=value ...
 * keys: q m partitions segments sns f sharpness strong af pass pre
 *       partition_limit sharp_yuv
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/encode.h"

static int writer(const uint8_t *d, size_t n, const WebPPicture *p)
{
    return fwrite(d, 1, n, (FILE *)p->custom_ptr) == n;
}

static int read_ppm(const char *path, int *w, int *h, unsigned char **rgb)
{
    FILE *f = fopen(path, "rb");
    int maxv, c;
    if (!f || fscanf(f, "P6 %d %d %d", w, h, &maxv) != 3 || maxv != 255)
        return 0;
    c = fgetc(f);               /* single whitespace */
    (void)c;
    *rgb = malloc((size_t)*w * *h * 3);
    if (fread(*rgb, 3, (size_t)*w * *h, f) != (size_t)*w * *h)
        return 0;
    fclose(f);
    return 1;
}

int main(int argc, char **argv)
{
    WebPConfig cfg;
    WebPPicture pic;
    int w, h, i;
    unsigned char *rgb;
    FILE *out;
    if (argc < 3) { fprintf(stderr, "usage\n"); return 2; }
    if (!read_ppm(argv[1], &w, &h, &rgb)) { fprintf(stderr, "bad ppm\n"); return 1; }
    WebPConfigInit(&cfg);
    for (i = 3; i < argc; i++) {
        char *eq = strchr(argv[i], '=');
        float v;
        if (!eq) return 2;
        *eq = 0; v = atof(eq + 1);
        if (!strcmp(argv[i], "q")) cfg.quality = v;
        else if (!strcmp(argv[i], "m")) cfg.method = (int)v;
        else if (!strcmp(argv[i], "partitions")) cfg.partitions = (int)v;
        else if (!strcmp(argv[i], "segments")) cfg.segments = (int)v;
        else if (!strcmp(argv[i], "sns")) cfg.sns_strength = (int)v;
        else if (!strcmp(argv[i], "f")) cfg.filter_strength = (int)v;
        else if (!strcmp(argv[i], "sharpness")) cfg.filter_sharpness = (int)v;
        else if (!strcmp(argv[i], "strong")) cfg.filter_type = (int)v;
        else if (!strcmp(argv[i], "af")) cfg.autofilter = (int)v;
        else if (!strcmp(argv[i], "pass")) cfg.pass = (int)v;
        else if (!strcmp(argv[i], "pre")) cfg.preprocessing = (int)v;
        else if (!strcmp(argv[i], "partition_limit")) cfg.partition_limit = (int)v;
        else if (!strcmp(argv[i], "sharp_yuv")) cfg.use_sharp_yuv = (int)v;
        else { fprintf(stderr, "unknown key %s\n", argv[i]); return 2; }
    }
    if (!WebPValidateConfig(&cfg)) { fprintf(stderr, "bad config\n"); return 1; }
    WebPPictureInit(&pic);
    pic.width = w; pic.height = h;
    if (!WebPPictureImportRGB(&pic, rgb, w * 3)) return 1;
    out = fopen(argv[2], "wb");
    pic.writer = writer; pic.custom_ptr = out;
    if (!WebPEncode(&cfg, &pic)) { fprintf(stderr, "encode err %d\n", pic.error_code); return 1; }
    fclose(out);
    WebPPictureFree(&pic);
    free(rgb);
    return 0;
}
