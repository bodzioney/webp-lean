//! Pairwise comparison of oracle outcomes and discrepancy signatures.
//!
//! Environment knobs:
//! * `WEBP_DIFF_ABORT`     comma-separated signature prefixes (or `all`) that abort the process
//!                         (so libFuzzer stores a crash file). Default: none.
//! * `WEBP_DIFF_FINDINGS`  findings directory (default `<crate>/findings`); `off` disables.
//! * `WEBP_DIFF_CAP`       max files stored per signature (default 25).
//! * `WEBP_DIFF_LOSSY_TOL` per-channel tolerance for image-webp on lossy images (default 0).
//! * `WEBP_DIFF_ANIM_TOL`  per-channel tolerance for image-webp on animations (default 1,
//!                         image-webp rounds alpha-blending differently from libwebp).
use crate::oracles::{Decoded, Oracle, Outcome};
use crate::probe::Probe;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::Mutex;

#[derive(Clone, Debug)]
pub struct Discrepancy {
    pub signature: String,
    pub detail: String,
}

#[derive(Clone, Debug)]
pub struct Report {
    /// Known discrepancy classes detected from headers (see `known_classes`).
    pub known: Vec<&'static str>,
    pub probe: Probe,
    pub outcomes: Vec<(Oracle, Outcome)>,
    pub discrepancies: Vec<Discrepancy>,
}

fn env_u32(k: &str, d: u32) -> u32 {
    std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d)
}

#[derive(Default, Debug)]
struct PixDiff {
    differing: usize,
    max: u8,
    alpha_only: bool,
    first: Option<(usize, u32, u32)>,
}

fn pixel_diff(a: &[u8], b: &[u8], w: u32, tol: u8, frame: usize, acc: &mut PixDiff) {
    for (i, (pa, pb)) in a.chunks_exact(4).zip(b.chunks_exact(4)).enumerate() {
        let mut bad = false;
        let mut rgb_bad = false;
        for c in 0..4 {
            let d = pa[c].abs_diff(pb[c]);
            if d > tol {
                bad = true;
                if c < 3 {
                    rgb_bad = true;
                }
                acc.max = acc.max.max(d);
            }
        }
        if bad {
            if acc.differing == 0 {
                acc.alpha_only = true;
                let (x, y) = ((i as u32) % w.max(1), (i as u32) / w.max(1));
                acc.first = Some((frame, x, y));
            }
            if rgb_bad {
                acc.alpha_only = false;
            }
            acc.differing += 1;
        }
    }
}

fn compare_pair(
    probe: &Probe,
    a: Oracle,
    da: &Decoded,
    b: Oracle,
    db: &Decoded,
    out: &mut Vec<Discrepancy>,
) {
    let pair = format!("{a}-vs-{b}");
    if (da.width, da.height) != (db.width, db.height) {
        out.push(Discrepancy {
            signature: format!("dims:{pair}"),
            detail: format!("{a}: {}x{}, {b}: {}x{}", da.width, da.height, db.width, db.height),
        });
        return;
    }
    if da.frames.len() != db.frames.len() {
        out.push(Discrepancy {
            signature: format!("frames-count:{pair}"),
            detail: format!("{a}: {}, {b}: {}", da.frames.len(), db.frames.len()),
        });
    }
    let animated = da.animated || db.animated || probe.animated;
    if animated {
        let d1: Vec<u32> = da.frames.iter().map(|f| f.duration).collect();
        let d2: Vec<u32> = db.frames.iter().map(|f| f.duration).collect();
        let n = d1.len().min(d2.len());
        if d1[..n] != d2[..n] {
            out.push(Discrepancy {
                signature: format!("durations:{pair}"),
                detail: format!("{a}: {d1:?}\n{b}: {d2:?}"),
            });
        }
        if da.loop_count.is_some() && db.loop_count.is_some() && da.loop_count != db.loop_count {
            out.push(Discrepancy {
                signature: format!("loop-count:{pair}"),
                detail: format!("{a}: {:?}, {b}: {:?}", da.loop_count, db.loop_count),
            });
        }
    }
    let involves_iw = a == Oracle::ImageWebp || b == Oracle::ImageWebp;
    let involves_lean = a == Oracle::Lean || b == Oracle::Lean;
    let kind = if probe.has_vp8 { "lossy" } else { "lossless" };
    if animated {
        anim_pixels(probe, a, da, b, db, involves_lean, involves_iw, kind, &pair, out);
        return;
    }
    let mut tol = 0u32;
    if involves_iw && probe.has_vp8 {
        tol = tol.max(env_u32("WEBP_DIFF_LOSSY_TOL", 0));
    }
    let mut pd = PixDiff::default();
    for (i, (fa, fb)) in da.frames.iter().zip(db.frames.iter()).enumerate() {
        pixel_diff(&fa.rgba, &fb.rgba, da.width, tol.min(255) as u8, i, &mut pd);
    }
    if pd.differing > 0 {
        let ao = if pd.alpha_only { ":alpha-only" } else { "" };
        let (fr, x, y) = pd.first.unwrap();
        let idx = (y as usize * da.width as usize + x as usize) * 4;
        let pa = &da.frames[fr].rgba[idx..idx + 4];
        let pb = &db.frames[fr].rgba[idx..idx + 4];
        out.push(Discrepancy {
            signature: format!("pixels-{kind}:{pair}{ao}"),
            detail: format!(
                "{} differing pixels (tol {tol}), max channel diff {}, first at frame {fr} ({x},{y}): {a}={pa:?} {b}={pb:?}",
                pd.differing, pd.max
            ),
        });
    }
}

/// Largest per-channel deviation seen *within tolerance* on animations for pairs involving
/// Lean (process-wide; reported by webp-diff-run --summary).
pub static LEAN_ANIM_MAX_DEV: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Animated canvases: pixels with alpha 0 on both sides are equal regardless of RGB (blend
/// formula vs libwebp's keyframe shortcut); inside the rectangle of a frame that is drawn
/// without blending, pixels must match exactly (`:hard`); elsewhere a per-channel tolerance
/// applies (blend rounding): `WEBP_DIFF_LEAN_ANIM_TOL` (default 2) for pairs with Lean,
/// `WEBP_DIFF_ANIM_TOL` (default 1) for image-webp vs libwebp-anim, 0 otherwise.
#[allow(clippy::too_many_arguments)]
fn anim_pixels(
    probe: &Probe,
    a: Oracle,
    da: &Decoded,
    b: Oracle,
    db: &Decoded,
    involves_lean: bool,
    involves_iw: bool,
    kind: &str,
    pair: &str,
    out: &mut Vec<Discrepancy>,
) {
    let mut tol = if involves_lean {
        env_u32("WEBP_DIFF_LEAN_ANIM_TOL", 2)
    } else if involves_iw {
        env_u32("WEBP_DIFF_ANIM_TOL", 1)
    } else {
        0
    };
    if involves_iw && probe.has_vp8 {
        tol = tol.max(env_u32("WEBP_DIFF_LOSSY_TOL", 0));
    }
    let w = da.width as usize;
    let (mut hard, mut soft, mut max_in, mut max_out) = (0usize, 0usize, 0u8, 0u8);
    let mut first_hard: Option<(usize, usize)> = None;
    let mut first_soft: Option<(usize, usize)> = None;
    let mut soft_alpha_only = true;
    let mut soft_opaque = 0usize;
    for (fi, (fa, fb)) in da.frames.iter().zip(db.frames.iter()).enumerate() {
        let rect = probe.frames.get(fi).filter(|f| f.no_blend);
        for (i, (pa, pb)) in fa.rgba.chunks_exact(4).zip(fb.rgba.chunks_exact(4)).enumerate() {
            if pa == pb || (pa[3] == 0 && pb[3] == 0) {
                continue;
            }
            let d = (0..4).map(|c| pa[c].abs_diff(pb[c])).max().unwrap();
            let (x, y) = ((i % w.max(1)) as u32, (i / w.max(1)) as u32);
            let in_hard = rect.is_some_and(|r| x >= r.x && y >= r.y && x - r.x < r.w && y - r.y < r.h);
            if in_hard {
                hard += 1;
                first_hard.get_or_insert((fi, i));
            } else if d as u32 > tol {
                soft += 1;
                max_out = max_out.max(d);
                first_soft.get_or_insert((fi, i));
                if (0..3).any(|c| pa[c] != pb[c]) {
                    soft_alpha_only = false;
                }
                if pa[3] == 255 && pb[3] == 255 {
                    soft_opaque += 1;
                }
            } else {
                max_in = max_in.max(d);
            }
        }
    }
    if involves_lean {
        LEAN_ANIM_MAX_DEV.fetch_max(max_in, std::sync::atomic::Ordering::Relaxed);
    }
    let px = |fi: usize, i: usize| {
        let pa = &da.frames[fi].rgba[i * 4..i * 4 + 4];
        let pb = &db.frames[fi].rgba[i * 4..i * 4 + 4];
        format!("frame {fi} ({},{}): {a}={pa:?} {b}={pb:?}", i % w.max(1), i / w.max(1))
    };
    if let Some((fi, i)) = first_hard {
        out.push(Discrepancy {
            signature: format!("pixels-{kind}-anim:{pair}:hard"),
            detail: format!("{hard} differing pixels inside no-blend frame rects (exact required); first at {}", px(fi, i)),
        });
    }
    if let Some((fi, i)) = first_soft {
        // `:translucent`: no beyond-tolerance pixel is opaque in both outputs, i.e. this is
        // blend-rounding amplification at low alpha (libwebp's 8-bit approximation compounds
        // across frames), not a decoding difference.
        let ao = if soft_alpha_only {
            ":alpha-only"
        } else if soft_opaque == 0 {
            ":translucent"
        } else {
            ""
        };
        out.push(Discrepancy {
            signature: format!("pixels-{kind}-anim:{pair}{ao}"),
            detail: format!(
                "{soft} pixels beyond tol {tol} ({soft_opaque} opaque in both; max diff {max_out}; max within tol {max_in}); first at {}",
                px(fi, i)
            ),
        });
    }
}

/// libwebp's simple API lets the VP8 decoder read past the end of the 'VP8 ' chunk into the
/// following bytes, while Lean decodes exactly the chunk payload. Re-run libwebp on a copy
/// that ends at the VP8 payload (RIFF size patched); if that reproduces Lean's outcome, the
/// lean/libwebp discrepancy is attributed to this known behavior.
fn libwebp_strict_matches_lean(data: &[u8], probe: &Probe, lean: &Outcome) -> bool {
    let Some((_, end)) = probe.vp8_payload else { return false };
    if end > data.len() || end < 12 {
        return false;
    }
    let mut v = data[..end].to_vec();
    let rs = ((end - 8) as u32).to_le_bytes();
    v[4..8].copy_from_slice(&rs);
    // Only VP8-decoder-level Lean errors qualify (container-level rejections are other classes).
    if let Outcome::Err(m) = lean {
        if !m.starts_with("VP8") && !probe.bitstream_is_last {
            return false;
        }
    }
    let strict = crate::oracles::run_libwebp(&v);
    match (lean, &strict) {
        (Outcome::Err(_), Outcome::Err(_)) => true,
        (Outcome::Ok(l), Outcome::Ok(s)) => l.width == s.width && l.height == s.height && l.frames == s.frames,
        _ => false,
    }
}

pub fn compare(data: &[u8], probe: &Probe, outcomes: Vec<(Oracle, Outcome)>) -> Report {
    let mut ds = Vec::new();
    for (o, r) in &outcomes {
        if let Outcome::Err(m) = r {
            if let Some(msg) = m.strip_prefix(crate::oracles::PANIC_PREFIX) {
                ds.push(Discrepancy { signature: format!("crash:{o}"), detail: msg.to_string() });
            }
        }
    }
    let oks: Vec<(Oracle, &Decoded)> = outcomes
        .iter()
        .filter_map(|(o, r)| if let Outcome::Ok(d) = r { Some((*o, d)) } else { None })
        .collect();
    let errs: Vec<Oracle> = outcomes
        .iter()
        .filter_map(|(o, r)| matches!(r, Outcome::Err(_)).then_some(*o))
        .collect();
    if !oks.is_empty() && !errs.is_empty() {
        let ok_names: Vec<&str> = oks.iter().map(|(o, _)| o.name()).collect();
        let err_names: Vec<&str> = errs.iter().map(|o| o.name()).collect();
        let mut detail = String::new();
        for (o, r) in &outcomes {
            let _ = writeln!(detail, "{o}: {}", r.summary());
        }
        ds.push(Discrepancy {
            signature: format!("accept-reject:ok={}:err={}", ok_names.join(","), err_names.join(",")),
            detail,
        });
    }
    for i in 0..oks.len() {
        for j in i + 1..oks.len() {
            compare_pair(probe, oks[i].0, oks[i].1, oks[j].0, oks[j].1, &mut ds);
        }
    }
    // Attribute lean/libwebp lossy-still discrepancies caused by libwebp reading past the chunk.
    let get = |o: Oracle| outcomes.iter().find(|(x, _)| *x == o).map(|(_, r)| r);
    if !probe.animated {
        if let (Some(lean), Some(lw)) = (get(Oracle::Lean), get(Oracle::Libwebp)) {
            let touches = |sig: &str| {
                (sig.starts_with("accept-reject") && matches!((lean, lw), (Outcome::Err(_), Outcome::Ok(_)) | (Outcome::Ok(_), Outcome::Err(_))))
                    || sig.contains("lean-vs-libwebp:")
                    || sig.ends_with("lean-vs-libwebp")
            };
            if ds.iter().any(|d| touches(&d.signature)) && libwebp_strict_matches_lean(data, probe, lean) {
                for d in ds.iter_mut().filter(|d| touches(&d.signature)) {
                    d.signature = format!("libwebp-reads-past-bitstream-chunk:{}", d.signature);
                }
            }
        }
    }
    // Label discrepancies involving Lean that belong to already-triaged classes.
    let known = known_classes(data);
    if !known.is_empty() {
        let tag = known.join("+");
        for d in ds.iter_mut().filter(|d| d.signature.contains("lean") && !d.signature.starts_with("libwebp-reads-past")) {
            d.signature = format!("known:{tag}:{}", d.signature);
        }
    }
    Report { known, probe: probe.clone(), outcomes, discrepancies: ds }
}

/// Header-level classifier for triaged discrepancy classes (RFC 9649 references):
/// * `vp8x-oversized`: VP8X payload > 10 bytes. §2.7: "Unknown fields MUST be ignored" — Lean
///   accepts; libwebp / image-webp reject.
/// * `alph-reserved-or-preproc`: ALPH header with reserved bits != 0 or preprocessing in {2,3}.
///   §2.7.1.2: reserved MUST be ignored, preprocessing is informative — Lean accepts; libwebp
///   and image-webp reject.
/// * `simple-extra-recon-chunk`: simple format (first chunk VP8/VP8L) followed by another
///   reconstruction chunk (ALPH/VP8/VP8L/VP8X/ANIM/ANMF/ICCP) — Lean rejects by the grammar.
/// * `still-stray-anim`: VP8X without the animation flag but with an ANIM chunk (after the
///   image data). §2.7.1.1 says ANIM "MUST be ignored" then; Lean rejects it as an
///   out-of-order reconstruction chunk (§2.7 "SHOULD fail"); libwebp/image-webp accept.
/// * `iccp-after-image`: ICCP after the image data — Lean rejects (order, §2.7.1.4 "MUST appear
///   before the image data"); libwebp's simple API accepts.
/// * `alph-raw-size`: uncompressed ALPH whose size != width*height (§2.7.1.2: "length =
///   width * height") — Lean rejects; libwebp accepts any size >= width*height.
/// * `simple-trailing-data`: simple-format file with bytes after the VP8/VP8L chunk inside the
///   RIFF size — Lean rejects (grammar); libwebp ignores them.
/// * `anmf-known-subchunk`: an ANMF whose frame data contains a known non-frame chunk (e.g. a
///   nested ANMF) — Lean rejects (§2.7.1.6: not an unknown chunk); libwebp's WebPAnimDecoder
///   plays nested ANMFs as extra frames.
pub fn known_classes(data: &[u8]) -> Vec<&'static str> {
    use crate::riff;
    let mut v = Vec::new();
    let Some(f) = riff::WebPFile::parse(data) else { return v };
    if f.chunks.first().is_some_and(|c| c.fourcc == riff::VP8X && c.payload.len() > 10) {
        v.push("vp8x-oversized");
    }
    let mut alph_bad = false;
    let mut nested = false;
    for c in &f.chunks {
        let subs: Vec<&riff::Chunk> = match &c.anmf {
            Some(a) => {
                nested |= a.chunks.iter().any(|s| {
                    matches!(s.fourcc, riff::ANMF | riff::ANIM | riff::VP8X | riff::ICCP | riff::EXIF | riff::XMP)
                });
                a.chunks.iter().collect()
            }
            None => vec![c],
        };
        for s in subs {
            if s.fourcc == riff::ALPH {
                if let Some(&h) = s.payload.first() {
                    alph_bad |= h & 0xc0 != 0 || (h >> 4) & 3 >= 2;
                }
            }
        }
    }
    if alph_bad {
        v.push("alph-reserved-or-preproc");
    }
    if f.chunks.first().is_some_and(|c| c.fourcc == riff::VP8 || c.fourcc == riff::VP8L)
        && f.chunks[1..].iter().any(|c| {
            matches!(c.fourcc, riff::ALPH | riff::VP8 | riff::VP8L | riff::VP8X | riff::ANIM | riff::ANMF | riff::ICCP)
        })
    {
        v.push("simple-extra-recon-chunk");
    }
    if nested {
        v.push("anmf-known-subchunk");
    }
    // Raw ALPH whose size != width*height of the frame's VP8 bitstream.
    let raw_alph_bad = |list: &[riff::Chunk]| {
        let dims = list.iter().find_map(crate::probe::bitstream_dims);
        list.iter().any(|c| {
            c.fourcc == riff::ALPH
                && c.payload.first().is_some_and(|h| h & 3 == 0)
                && dims.is_some_and(|(w, h)| c.payload.len() - 1 != (w * h) as usize)
        })
    };
    if raw_alph_bad(&f.chunks) || f.chunks.iter().any(|c| c.anmf.as_ref().is_some_and(|a| raw_alph_bad(&a.chunks))) {
        v.push("alph-raw-size");
    }
    // Simple format with extra bytes after the bitstream chunk inside the RIFF payload.
    if f.chunks.first().is_some_and(|c| c.fourcc == riff::VP8 || c.fourcc == riff::VP8L) {
        let c = &f.chunks[0];
        let end = 12 + 8 + c.payload.len() + (c.payload.len() & 1);
        if (f.riff_size as usize + 8).min(data.len()) > end {
            v.push("simple-trailing-data");
        }
    }
    if let Some(x) = f.chunks.first().filter(|c| c.fourcc == riff::VP8X) {
        let anim_flag = x.payload.first().is_some_and(|b| b & 2 != 0);
        if !anim_flag && f.chunks.iter().any(|c| c.fourcc == riff::ANIM) {
            v.push("still-stray-anim");
        }
        if let Some(first_img) = f.chunks.iter().position(|c| matches!(c.fourcc, riff::ALPH | riff::VP8 | riff::VP8L | riff::ANMF)) {
            if f.chunks[first_img..].iter().any(|c| c.fourcc == riff::ICCP) {
                v.push("iccp-after-image");
            }
        }
    }
    v
}

impl Report {
    pub fn signatures(&self) -> Vec<&str> {
        self.discrepancies.iter().map(|d| d.signature.as_str()).collect()
    }

    pub fn render(&self) -> String {
        let mut s = String::new();
        let p = &self.probe;
        if !self.known.is_empty() {
            let _ = writeln!(s, "known classes: {}", self.known.join(", "));
        }
        let _ = writeln!(
            s,
            "probe: first={:?} canvas={:?} animated={} anmf={} vp8={} vp8l={} alph={} skip={:?}",
            p.first.map(|f| String::from_utf8_lossy(&f).into_owned()),
            p.canvas,
            p.animated,
            p.num_anmf,
            p.has_vp8,
            p.has_vp8l,
            p.has_alph,
            p.skip
        );
        for (o, r) in &self.outcomes {
            let _ = writeln!(s, "  {:<13} {}", o.name(), r.summary());
        }
        if self.discrepancies.is_empty() {
            let _ = writeln!(s, "  => agree");
        }
        for d in &self.discrepancies {
            let _ = writeln!(s, "  !! {}", d.signature);
            for l in d.detail.lines() {
                let _ = writeln!(s, "       {l}");
            }
        }
        s
    }
}

fn sanitize(sig: &str) -> String {
    sig.chars().map(|c| if c.is_ascii_alphanumeric() || "-_=,.".contains(c) { c } else { '_' }).collect()
}

static COUNTS: Mutex<Option<HashMap<String, usize>>> = Mutex::new(None);

/// Records findings and aborts for signatures selected by `WEBP_DIFF_ABORT`.
pub fn handle(data: &[u8], report: &Report) {
    if report.discrepancies.is_empty() {
        return;
    }
    let abort = std::env::var("WEBP_DIFF_ABORT").unwrap_or_default();
    let dir = std::env::var("WEBP_DIFF_FINDINGS")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/findings").to_string());
    if dir != "off" {
        let cap = env_u32("WEBP_DIFF_CAP", 25) as usize;
        let mut guard = COUNTS.lock().unwrap();
        let counts = guard.get_or_insert_with(HashMap::new);
        let hash = sha1_smol::Sha1::from(data).digest().to_string();
        for d in &report.discrepancies {
            let sd = format!("{dir}/{}", sanitize(&d.signature));
            let c = counts.entry(d.signature.clone()).or_insert_with(|| {
                std::fs::read_dir(&sd).map(|r| r.count() / 2).unwrap_or(0)
            });
            if *c >= cap {
                continue;
            }
            *c += 1;
            let _ = std::fs::create_dir_all(&sd);
            let _ = std::fs::write(format!("{sd}/{hash}.webp"), data);
            let _ = std::fs::write(format!("{sd}/{hash}.txt"), report.render());
        }
    }
    if !abort.is_empty() {
        for d in &report.discrepancies {
            if abort == "all" || abort.split(',').any(|p| !p.is_empty() && d.signature.starts_with(p)) {
                eprintln!("{}", report.render());
                panic!("WEBP_DIFF_ABORT: discrepancy {}", d.signature);
            }
        }
    }
}
