// Initializes the Lean runtime once and wraps the exported Lean decoder (see ../../DESIGN.md).
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern lean_object* webp_lean_decode_impl(lean_object* data, uint64_t max_pixels);
extern lean_object* initialize_webp_WebP(uint8_t builtin);
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);

static int g_lean_initialized = 0;

void webp_lean_init(void) {
  if (g_lean_initialized) return;
  lean_initialize_runtime_module();
  lean_set_panic_messages(true);
  // A Lean `panic!` (e.g. out-of-bounds `get!`) is a decoder bug: make it fatal.
  if (getenv("WEBP_DIFF_LEAN_PANIC_OK") == NULL) lean_set_exit_on_panic(true);
  lean_object* res = initialize_webp_WebP(1);
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    abort();
  }
  lean_io_mark_end_initialization();
  g_lean_initialized = 1;
}

// Decodes `data`; result bytes (wire format of DESIGN.md) are malloc'ed into *out.
size_t webp_lean_decode(const uint8_t* data, size_t len, uint64_t max_pixels, uint8_t** out) {
  webp_lean_init();
  lean_object* ba = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(ba), data, len);
  lean_object* r = webp_lean_decode_impl(ba, max_pixels);  // consumes ba
  size_t n = lean_sarray_size(r);
  uint8_t* buf = (uint8_t*)malloc(n ? n : 1);
  if (n) memcpy(buf, lean_sarray_cptr(r), n);
  lean_dec(r);
  *out = buf;
  return n;
}

void webp_lean_free(void* p) { free(p); }

// libleanshared.so exports its bundled LLVM libunwind. Referencing the unwinder here (this
// archive is linked before -lgcc_s and -lleanshared) makes the linker record libgcc_s as
// DT_NEEDED *before* libleanshared, so Rust panics keep using the system unwinder.
extern int _Unwind_RaiseException(void*);
__attribute__((used)) void* webp_diff_force_gcc_s_first = (void*)&_Unwind_RaiseException;
