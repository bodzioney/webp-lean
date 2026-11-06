//! The decoders under test, all normalized to [`Outcome`].
use crate::probe::Probe;
use std::fmt;
use std::io::Cursor;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Oracle {
    Lean,
    Libwebp,
    LibwebpAnim,
    ImageWebp,
}

impl Oracle {
    pub const ALL: [Oracle; 4] =
        [Oracle::Lean, Oracle::Libwebp, Oracle::LibwebpAnim, Oracle::ImageWebp];
    pub fn name(self) -> &'static str {
        match self {
            Oracle::Lean => "lean",
            Oracle::Libwebp => "libwebp",
            Oracle::LibwebpAnim => "libwebp-anim",
            Oracle::ImageWebp => "image-webp",
        }
    }
}

impl fmt::Display for Oracle {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Frame {
    /// Display duration in ms (0 for still images).
    pub duration: u32,
    /// Full canvas, RGBA, row-major.
    pub rgba: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Decoded {
    pub width: u32,
    pub height: u32,
    pub frames: Vec<Frame>,
    pub animated: bool,
    pub has_alpha: bool,
    pub loop_count: Option<u32>,
    pub bgcolor: Option<u32>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Ok(Decoded),
    Err(String),
    Skip(String),
}

impl Outcome {
    pub fn summary(&self) -> String {
        match self {
            Outcome::Ok(d) => format!(
                "OK {}x{} frames={} animated={} alpha={} loop={:?} bg={:?} durations={:?}",
                d.width,
                d.height,
                d.frames.len(),
                d.animated,
                d.has_alpha,
                d.loop_count,
                d.bgcolor.map(|c| format!("{c:08x}")),
                d.frames.iter().map(|f| f.duration).take(16).collect::<Vec<_>>()
            ),
            Outcome::Err(e) => format!("ERR {e}"),
            Outcome::Skip(s) => format!("SKIP {s}"),
        }
    }
}

// ---------------------------------------------------------------- FFI declarations
extern "C" {
    fn webp_lean_decode(data: *const u8, len: usize, max_pixels: u64, out: *mut *mut u8) -> usize;
    fn webp_lean_free(p: *mut u8);

    fn shim_webp_decode_rgba(
        data: *const u8,
        size: usize,
        w: *mut i32,
        h: *mut i32,
        has_alpha: *mut i32,
        has_anim: *mut i32,
        format: *mut i32,
        out: *mut *mut u8,
    ) -> i32;
    fn shim_free(p: *mut u8);
    fn shim_anim_new(data: *const u8, size: usize) -> *mut std::ffi::c_void;
    fn shim_anim_info(
        h: *mut std::ffi::c_void,
        cw: *mut u32,
        ch: *mut u32,
        lp: *mut u32,
        bg: *mut u32,
        n: *mut u32,
    ) -> i32;
    fn shim_anim_has_more(h: *mut std::ffi::c_void) -> i32;
    fn shim_anim_next(h: *mut std::ffi::c_void, buf: *mut *mut u8, ts: *mut i32) -> i32;
    fn shim_anim_delete(h: *mut std::ffi::c_void);
}

fn vp8_status_name(s: i32) -> &'static str {
    match s {
        0 => "OK",
        1 => "OUT_OF_MEMORY",
        2 => "INVALID_PARAM",
        3 => "BITSTREAM_ERROR",
        4 => "UNSUPPORTED_FEATURE",
        5 => "SUSPENDED",
        6 => "USER_ABORT",
        7 => "NOT_ENOUGH_DATA",
        _ => "?",
    }
}

// ---------------------------------------------------------------- Lean
/// Prefix of the error message for an oracle that panicked (offline runs only).
pub const PANIC_PREFIX: &str = "PANIC: ";

pub const LEAN_STUB_MSG: &str = "not implemented";

/// Raw Lean result bytes (see DESIGN.md wire format).
pub fn lean_raw(data: &[u8], max_pixels: u64) -> Vec<u8> {
    unsafe {
        let mut out: *mut u8 = std::ptr::null_mut();
        let n = webp_lean_decode(data.as_ptr(), data.len(), max_pixels, &mut out);
        let v = std::slice::from_raw_parts(out, n).to_vec();
        webp_lean_free(out);
        v
    }
}

struct Rd<'a>(&'a [u8], usize);
impl Rd<'_> {
    fn take(&mut self, n: usize) -> &[u8] {
        let s = self.0.get(self.1..self.1 + n).unwrap_or_else(|| {
            panic!("Lean FFI result truncated: want {n} bytes at {} of {}", self.1, self.0.len())
        });
        self.1 += n;
        s
    }
    fn u8(&mut self) -> u8 {
        self.take(1)[0]
    }
    fn u16(&mut self) -> u16 {
        let b = self.take(2);
        u16::from_le_bytes([b[0], b[1]])
    }
    fn u32(&mut self) -> u32 {
        let b = self.take(4);
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }
}

/// Parses the Lean wire format. Panics on malformed output (that is a Lean-side bug).
pub fn parse_lean(raw: &[u8]) -> Outcome {
    assert!(!raw.is_empty(), "Lean FFI returned empty result");
    let msg = || String::from_utf8_lossy(&raw[1..]).into_owned();
    match raw[0] {
        0 => {}
        1 if msg() == LEAN_STUB_MSG => return Outcome::Skip("lean stub".into()),
        1 => return Outcome::Err(msg()),
        2 => return Outcome::Skip(format!("lean resource limit: {}", msg())),
        s => panic!("Lean FFI returned unknown status {s}"),
    }
    let mut r = Rd(raw, 1);
    let width = r.u32();
    let height = r.u32();
    let flags = r.u8();
    let loop_count = r.u16() as u32;
    let bg = r.u32();
    let n = r.u32() as usize;
    let fsize = width as usize * height as usize * 4;
    let mut frames = Vec::with_capacity(n.min(4096));
    for _ in 0..n {
        let duration = r.u32();
        frames.push(Frame { duration, rgba: r.take(fsize).to_vec() });
    }
    assert_eq!(r.1, raw.len(), "Lean FFI result has trailing bytes");
    let animated = flags & 1 != 0;
    Outcome::Ok(Decoded {
        width,
        height,
        frames,
        animated,
        has_alpha: flags & 2 != 0,
        loop_count: animated.then_some(loop_count),
        bgcolor: animated.then_some(bg),
    })
}

pub fn run_lean(data: &[u8]) -> Outcome {
    parse_lean(&lean_raw(data, crate::probe::max_pixels_limit()))
}

// ---------------------------------------------------------------- libwebp
pub fn run_libwebp(data: &[u8]) -> Outcome {
    unsafe {
        let (mut w, mut h, mut a, mut anim, mut fmt) = (0, 0, 0, 0, 0);
        let mut out: *mut u8 = std::ptr::null_mut();
        let st = shim_webp_decode_rgba(
            data.as_ptr(),
            data.len(),
            &mut w,
            &mut h,
            &mut a,
            &mut anim,
            &mut fmt,
            &mut out,
        );
        if st != 0 {
            if anim != 0 && st == 4 {
                return Outcome::Skip("animated (simple API unsupported)".into());
            }
            return Outcome::Err(format!("VP8StatusCode {} ({})", st, vp8_status_name(st)));
        }
        let n = w as usize * h as usize * 4;
        let rgba = std::slice::from_raw_parts(out, n).to_vec();
        shim_free(out);
        Outcome::Ok(Decoded {
            width: w as u32,
            height: h as u32,
            frames: vec![Frame { duration: 0, rgba }],
            animated: false,
            has_alpha: a != 0,
            loop_count: None,
            bgcolor: None,
        })
    }
}

pub fn run_libwebp_anim(data: &[u8], probe: &Probe) -> Outcome {
    unsafe {
        let h = shim_anim_new(data.as_ptr(), data.len());
        if h.is_null() {
            return Outcome::Err("WebPAnimDecoderNew failed".into());
        }
        let (mut cw, mut ch, mut lp, mut bg, mut n) = (0, 0, 0, 0, 0);
        if shim_anim_info(h, &mut cw, &mut ch, &mut lp, &mut bg, &mut n) == 0 {
            shim_anim_delete(h);
            return Outcome::Err("WebPAnimDecoderGetInfo failed".into());
        }
        let fsize = cw as usize * ch as usize * 4;
        let mut frames = Vec::new();
        let mut prev_ts = 0;
        while shim_anim_has_more(h) != 0 {
            let mut buf: *mut u8 = std::ptr::null_mut();
            let mut ts = 0;
            if shim_anim_next(h, &mut buf, &mut ts) == 0 {
                shim_anim_delete(h);
                return Outcome::Err(format!("WebPAnimDecoderGetNext failed at frame {}", frames.len()));
            }
            frames.push(Frame {
                duration: (ts - prev_ts) as u32,
                rgba: std::slice::from_raw_parts(buf, fsize).to_vec(),
            });
            prev_ts = ts;
        }
        shim_anim_delete(h);
        let animated = probe.animated;
        if !animated {
            for f in &mut frames {
                f.duration = 0;
            }
        }
        Outcome::Ok(Decoded {
            width: cw,
            height: ch,
            frames,
            animated,
            has_alpha: probe.vp8x_flags & 0x10 != 0 || probe.has_alph || probe.has_vp8l,
            loop_count: animated.then_some(lp),
            bgcolor: animated.then_some(bg),
        })
    }
}

// ---------------------------------------------------------------- image-webp
fn to_rgba(buf: Vec<u8>, has_alpha: bool) -> Vec<u8> {
    if has_alpha {
        return buf;
    }
    let mut out = Vec::with_capacity(buf.len() / 3 * 4);
    for px in buf.chunks_exact(3) {
        out.extend_from_slice(&[px[0], px[1], px[2], 255]);
    }
    out
}

fn image_webp_inner(data: &[u8]) -> Result<Decoded, String> {
    use image_webp::{LoopCount, WebPDecoder};
    let mut d = WebPDecoder::new(Cursor::new(data)).map_err(|e| format!("new: {e}"))?;
    d.set_memory_limit(1 << 28);
    let (w, h) = d.dimensions();
    let has_alpha = d.has_alpha();
    let animated = d.is_animated();
    let size = d.output_buffer_size().ok_or("output_buffer_size overflow")?;
    let mut frames = Vec::new();
    if animated {
        let n = d.num_frames();
        for i in 0..n {
            let mut buf = vec![0u8; size];
            let dur = d.read_frame(&mut buf).map_err(|e| format!("read_frame {i}: {e}"))?;
            frames.push(Frame { duration: dur, rgba: to_rgba(buf, has_alpha) });
        }
    } else {
        let mut buf = vec![0u8; size];
        d.read_image(&mut buf).map_err(|e| format!("read_image: {e}"))?;
        frames.push(Frame { duration: 0, rgba: to_rgba(buf, has_alpha) });
    }
    let loop_count = animated.then(|| match d.loop_count() {
        LoopCount::Forever => 0,
        LoopCount::Times(n) => n.get() as u32,
    });
    let bgcolor = if animated {
        d.background_color_hint().map(u32::from_le_bytes)
    } else {
        None
    };
    Ok(Decoded { width: w, height: h, frames, animated, has_alpha, loop_count, bgcolor })
}

pub fn run_image_webp(data: &[u8]) -> Outcome {
    match image_webp_inner(data) {
        Ok(d) => Outcome::Ok(d),
        Err(e) => Outcome::Err(e),
    }
}

/// Runs every oracle (or skips all if the probe says the input is too large).
pub fn run_all(data: &[u8], probe: &Probe) -> Vec<(Oracle, Outcome)> {
    if let Some(reason) = &probe.skip {
        return Oracle::ALL.iter().map(|&o| (o, Outcome::Skip(reason.clone()))).collect();
    }
    let disabled = std::env::var("WEBP_DIFF_DISABLE").unwrap_or_default();
    Oracle::ALL
        .iter()
        .map(|&o| {
            if disabled.split(',').any(|d| d == o.name()) {
                return (o, Outcome::Skip("disabled".into()));
            }
            // In the fuzzer libfuzzer-sys's panic hook aborts before unwinding, so panics stay
            // fatal there; offline (webp-diff-run) they become a `PANIC:` error + signature.
            let soft = std::env::var("WEBP_DIFF_SOFT_PANIC")
                .map(|v| v == "all" || v.split(',').any(|x| x == o.name()))
                .unwrap_or(false);
            // Soft-panic oracles: silence the (aborting) libFuzzer hook while this oracle runs.
            let prev_hook = soft.then(|| {
                let h = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                h
            });
            let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match o {
                Oracle::Lean => run_lean(data),
                Oracle::Libwebp => run_libwebp(data),
                Oracle::LibwebpAnim => run_libwebp_anim(data, probe),
                Oracle::ImageWebp => run_image_webp(data),
            }))
            .unwrap_or_else(|e| {
                let msg = e
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                Outcome::Err(format!("{PANIC_PREFIX}{msg}"))
            });
            if let Some(h) = prev_hook {
                std::panic::set_hook(h);
            }
            (o, out)
        })
        .collect()
}
