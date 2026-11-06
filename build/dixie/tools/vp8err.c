/* vp8err: run libwebp's internal VP8 decoder (VP8GetHeaders + VP8Decode) on a
 * payload with data_size = exactly the payload (no RIFF layer), and print the
 * status + libwebp's internal error message.  Input conventions as dixie_dec
 * (RIFF/WEBP -> first 'VP8 ' chunk payload, else raw).  Diagnostic tool only.
 *   vp8err <file>    -> "ok WxH" or "error <status> <message>", exit 0/1 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "src/dec/vp8_dec.h"

static int put(const VP8Io *io) { (void)io; return 1; }

static unsigned rd32(const unsigned char *p)
{ return p[0] | p[1] << 8 | p[2] << 16 | (unsigned)p[3] << 24; }

static int find_vp8(const unsigned char *d, size_t off, size_t end, size_t *po, size_t *ps)
{
    while (off + 8 <= end) {
        size_t sz = rd32(d + off + 4), pay = off + 8;
        if (!memcmp(d + off, "VP8 ", 4)) { *po = pay; *ps = pay + sz <= end ? sz : end - pay; return 1; }
        if (!memcmp(d + off, "ANMF", 4) && find_vp8(d, pay + 16, pay + sz < end ? pay + sz : end, po, ps)) return 1;
        off = pay + sz + (sz & 1);
    }
    return 0;
}

int main(int argc, char **argv)
{
    FILE *f = fopen(argv[1], "rb");
    long n; unsigned char *buf, *data; size_t size;
    VP8Decoder *dec; VP8Io io;
    if (!f) return 2;
    fseek(f, 0, SEEK_END); n = ftell(f); fseek(f, 0, SEEK_SET);
    buf = malloc(n + 1);
    if (fread(buf, 1, n, f) != (size_t)n) return 2;
    data = buf; size = n;
    if (n >= 12 && !memcmp(buf, "RIFF", 4) && !memcmp(buf + 8, "WEBP", 4)) {
        size_t o, s;
        if (!find_vp8(buf, 12, n, &o, &s)) { printf("error - no VP8 chunk\n"); return 1; }
        data = buf + o; size = s;
    }
    /* copy into an exact-size buffer so ASan-built variants catch overreads */
    { unsigned char *c = malloc(size ? size : 1); memcpy(c, data, size); data = c; }
    dec = VP8New();
    if (!VP8InitIo(&io)) return 2;
    io.data = data; io.data_size = size; io.put = put;
    if (!VP8GetHeaders(dec, &io) || !VP8Decode(dec, &io)) {
        printf("error %d %s\n", VP8Status(dec), VP8StatusMessage(dec));
        return 1;
    }
    printf("ok %dx%d\n", io.width, io.height);
    VP8Delete(dec);
    return 0;
}
