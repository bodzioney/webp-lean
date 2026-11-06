// Thin C ABI over libwebp's decode + anim-decode APIs (hides inline ABI-version wrappers).
#include <stdlib.h>
#include <string.h>
#include "webp/decode.h"
#include "webp/demux.h"

// Still-image decode via the simple/advanced decoding API.
// Returns VP8StatusCode; on success *out is malloc'ed by libwebp (free with shim_free).
int shim_webp_decode_rgba(const uint8_t* data, size_t size, int* w, int* h,
                          int* has_alpha, int* has_anim, int* format,
                          uint8_t** out) {
  WebPDecoderConfig config;
  *out = NULL;
  if (!WebPInitDecoderConfig(&config)) return -1;
  VP8StatusCode st = WebPGetFeatures(data, size, &config.input);
  *w = config.input.width;
  *h = config.input.height;
  *has_alpha = config.input.has_alpha;
  *has_anim = config.input.has_animation;
  *format = config.input.format;
  if (st != VP8_STATUS_OK) return (int)st;
  config.output.colorspace = MODE_RGBA;
  config.options.use_threads = 0;
  st = WebPDecode(data, size, &config);
  if (st != VP8_STATUS_OK) {
    WebPFreeDecBuffer(&config.output);
    return (int)st;
  }
  *w = config.output.width;
  *h = config.output.height;
  // Copy into a tightly packed buffer.
  size_t stride = (size_t)config.output.u.RGBA.stride;
  size_t row = (size_t)config.output.width * 4;
  uint8_t* buf = (uint8_t*)malloc(row * (size_t)config.output.height + 1);
  for (int y = 0; y < config.output.height; ++y)
    memcpy(buf + row * y, config.output.u.RGBA.rgba + stride * y, row);
  WebPFreeDecBuffer(&config.output);
  *out = buf;
  return 0;
}

void shim_free(void* p) { free(p); }

typedef struct {
  WebPAnimDecoder* dec;
  WebPData data;
} ShimAnim;

void* shim_anim_new(const uint8_t* data, size_t size) {
  WebPAnimDecoderOptions opts;
  if (!WebPAnimDecoderOptionsInit(&opts)) return NULL;
  opts.color_mode = MODE_RGBA;
  opts.use_threads = 0;
  ShimAnim* a = (ShimAnim*)calloc(1, sizeof(ShimAnim));
  a->data.bytes = data;
  a->data.size = size;
  a->dec = WebPAnimDecoderNew(&a->data, &opts);
  if (a->dec == NULL) { free(a); return NULL; }
  return a;
}

int shim_anim_info(void* h, uint32_t* cw, uint32_t* ch, uint32_t* loop,
                   uint32_t* bg, uint32_t* nframes) {
  WebPAnimInfo info;
  if (!WebPAnimDecoderGetInfo(((ShimAnim*)h)->dec, &info)) return 0;
  *cw = info.canvas_width; *ch = info.canvas_height; *loop = info.loop_count;
  *bg = info.bgcolor; *nframes = info.frame_count;
  return 1;
}

int shim_anim_has_more(void* h) { return WebPAnimDecoderHasMoreFrames(((ShimAnim*)h)->dec); }

// Returns 1 on success; *buf points into decoder-owned memory (canvas_w*canvas_h*4).
int shim_anim_next(void* h, uint8_t** buf, int* timestamp) {
  return WebPAnimDecoderGetNext(((ShimAnim*)h)->dec, buf, timestamp);
}

void shim_anim_delete(void* h) {
  if (!h) return;
  WebPAnimDecoderDelete(((ShimAnim*)h)->dec);
  free(h);
}
