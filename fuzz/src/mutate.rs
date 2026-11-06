//! Format-aware mutator for WebP files.
//!
//! Works on the [`WebPFile`] chunk tree: chunk-level edits, field-level edits of every
//! header defined in RFC 9649, payload byte/bit mutations, generative VP8L/ALPH payloads
//! (see [`crate::vp8l_gen`]), "make consistent" repairs, and promotion of simple files to
//! extended/animated ones. Sizes are re-derived on serialization with high probability.
use crate::bits;
use crate::probe::bitstream_dims;
use crate::riff::{self, Chunk, WebPFile};
use crate::rng::Rng;
use crate::vp8l_gen;

/// Byte-level mutation callback: mutate `buf` in place, keeping `buf.len() <= max_len`.
/// In the fuzzer this is libFuzzer's `fuzzer_mutate`; offline it is [`simple_byte_mutate`].
pub type ByteMut<'a> = &'a mut dyn FnMut(&mut Vec<u8>, usize, &mut Rng);

/// Fallback byte mutator (used by the offline CLI and unit tests).
pub fn simple_byte_mutate(buf: &mut Vec<u8>, max_len: usize, rng: &mut Rng) {
    match rng.below(6) {
        0 if !buf.is_empty() => {
            let i = rng.below(buf.len());
            buf[i] ^= 1 << rng.below(8);
        }
        1 if !buf.is_empty() => {
            let i = rng.below(buf.len());
            buf[i] = rng.u32() as u8;
        }
        2 if buf.len() < max_len => {
            let i = rng.below(buf.len() + 1);
            buf.insert(i, rng.u32() as u8);
        }
        3 if !buf.is_empty() => {
            let i = rng.below(buf.len());
            let n = rng.range(1, (buf.len() - i).min(16));
            buf.drain(i..i + n);
        }
        4 if buf.len() >= 4 => {
            let i = rng.below(buf.len() - 3);
            let v = rng.interesting(32).to_le_bytes();
            buf[i..i + 4].copy_from_slice(&v);
        }
        _ if !buf.is_empty() => {
            let i = rng.below(buf.len());
            buf[i] = buf[i].wrapping_add(rng.range(1, 3) as u8).wrapping_sub(2);
        }
        _ => buf.push(rng.u32() as u8),
    }
    buf.truncate(max_len);
}

const UNKNOWN_FOURCCS: [&[u8; 4]; 10] =
    [b"JUNK", b"LIST", b"vp8l", b"VP8l", b"ALPh", b"RIFF", b"WEBP", b"\0\0\0\0", b"XYZW", b"FRGM"];

fn le24(b: &[u8], i: usize) -> u32 {
    if i + 3 > b.len() {
        return 0;
    }
    b[i] as u32 | (b[i + 1] as u32) << 8 | (b[i + 2] as u32) << 16
}

fn put24(b: &mut [u8], i: usize, v: u32) {
    if i + 3 <= b.len() {
        b[i] = v as u8;
        b[i + 1] = (v >> 8) as u8;
        b[i + 2] = (v >> 16) as u8;
    }
}

/// Dims of the first VP8/VP8L bitstream in a chunk list.
fn dims_in(chunks: &[Chunk]) -> Option<(u32, u32)> {
    chunks.iter().find_map(|c| match &c.anmf {
        Some(a) => dims_in(&a.chunks),
        None => bitstream_dims(c),
    })
}

fn vp8x_payload(flags: u8, w: u32, h: u32) -> Vec<u8> {
    let mut p = vec![flags, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    put24(&mut p, 4, w.saturating_sub(1));
    put24(&mut p, 7, h.saturating_sub(1));
    p
}

fn anmf_header(x: u32, y: u32, w: u32, h: u32, dur: u32, flags: u8) -> Vec<u8> {
    let mut p = vec![0u8; 16];
    put24(&mut p, 0, x / 2);
    put24(&mut p, 3, y / 2);
    put24(&mut p, 6, w.saturating_sub(1));
    put24(&mut p, 9, h.saturating_sub(1));
    put24(&mut p, 12, dur);
    p[15] = flags;
    p
}

fn anmf_chunk(header: Vec<u8>, subs: Vec<Chunk>) -> Chunk {
    let mut c = Chunk::new(riff::ANMF, header);
    c.anmf.as_mut().unwrap().chunks = subs;
    c.flatten(true);
    c.declared = c.payload.len() as u32;
    c
}

fn random_meta(rng: &mut Rng, max: usize) -> Vec<u8> {
    let n = rng.below(max + 1);
    rng.bytes(n)
}

/// A brand-new random file (used when the input is not RIFF at all, and as an insert source).
pub fn synthesize(rng: &mut Rng) -> WebPFile {
    let (w, h) = (rng.range(1, 24), rng.range(1, 24));
    let vp8l = Chunk::new(riff::VP8L, vp8l_gen::gen_vp8l(rng, Some((w, h))));
    match rng.below(4) {
        0 => WebPFile::new(vec![vp8l]),
        1 => WebPFile::new(vec![
            Chunk::new(riff::VP8X, vp8x_payload(0x10, w as u32, h as u32)),
            vp8l,
        ]),
        _ => {
            let n = rng.range(1, 4);
            let (cw, ch) = (w as u32 + 2 * rng.below(4) as u32, h as u32 + 2 * rng.below(4) as u32);
            let mut chunks = vec![
                Chunk::new(riff::VP8X, vp8x_payload(0x12, cw, ch)),
                Chunk::new(riff::ANIM, {
                    let mut p = rng.bytes(4);
                    p.extend_from_slice(&(rng.below(3) as u16).to_le_bytes());
                    p
                }),
            ];
            for _ in 0..n {
                let (fw, fh) = (rng.range(1, w), rng.range(1, h));
                let x = 2 * rng.below(((cw - fw as u32) / 2 + 1) as usize) as u32;
                let y = 2 * rng.below(((ch - fh as u32) / 2 + 1) as usize) as u32;
                let sub = Chunk::new(riff::VP8L, vp8l_gen::gen_vp8l(rng, Some((fw, fh))));
                let hdr = anmf_header(x, y, fw as u32, fh as u32, rng.below(200) as u32, rng.below(4) as u8);
                chunks.push(anmf_chunk(hdr, vec![sub]));
            }
            WebPFile::new(chunks)
        }
    }
}

/// Makes flags / canvas / frame headers agree with the actual content.
fn make_consistent(f: &mut WebPFile, rng: &mut Rng) {
    let has = |f: &WebPFile, cc: [u8; 4]| f.chunks.iter().any(|c| c.fourcc == cc);
    let mut alpha = false;
    for c in &f.chunks {
        let subs: Vec<&Chunk> = match &c.anmf {
            Some(a) => a.chunks.iter().collect(),
            None => vec![c],
        };
        alpha |= subs.iter().any(|s| s.fourcc == riff::ALPH || s.fourcc == riff::VP8L);
    }
    let anim = has(f, riff::ANMF);
    let iccp = has(f, riff::ICCP);
    let exif = has(f, riff::EXIF);
    let xmp = has(f, riff::XMP);
    // Fix ANMF frame dims to their bitstreams.
    let mut cw = 0;
    let mut ch = 0;
    for c in f.chunks.iter_mut() {
        if let Some(a) = &mut c.anmf {
            if let Some((w, h)) = dims_in(&a.chunks) {
                if a.header.len() == 16 {
                    put24(&mut a.header, 6, w.saturating_sub(1));
                    put24(&mut a.header, 9, h.saturating_sub(1));
                    cw = cw.max(le24(&a.header, 0) * 2 + w);
                    ch = ch.max(le24(&a.header, 3) * 2 + h);
                }
            }
        }
    }
    if !anim {
        if let Some((w, h)) = dims_in(&f.chunks) {
            cw = w;
            ch = h;
        }
    }
    if let Some(c) = f.chunks.iter_mut().find(|c| c.fourcc == riff::VP8X) {
        if c.payload.len() < 10 {
            c.payload.resize(10, 0);
        }
        let mut flags = 0u8;
        if iccp {
            flags |= 0x20;
        }
        if alpha {
            flags |= 0x10;
        }
        if exif {
            flags |= 0x08;
        }
        if xmp {
            flags |= 0x04;
        }
        if anim {
            flags |= 0x02;
        }
        c.payload[0] = flags;
        if cw > 0 && ch > 0 {
            put24(&mut c.payload, 4, cw - 1);
            put24(&mut c.payload, 7, ch - 1);
        }
    } else if (anim || alpha && f.chunks.iter().any(|c| c.fourcc == riff::ALPH) || iccp || exif || xmp)
        && rng.chance(3, 4)
    {
        let flags = (iccp as u8) << 5 | (alpha as u8) << 4 | (exif as u8) << 3 | (xmp as u8) << 2 | (anim as u8) << 1;
        f.chunks.insert(0, Chunk::new(riff::VP8X, vp8x_payload(flags, cw.max(1), ch.max(1))));
    }
    if anim && !has(f, riff::ANIM) {
        let pos = f.chunks.iter().position(|c| c.fourcc == riff::ANMF).unwrap_or(0);
        f.chunks.insert(pos, Chunk::new(riff::ANIM, vec![0, 0, 0, 0, 0, 0]));
    }
}

/// Number of top-level chunk-list "containers": the file itself plus each ANMF.
fn pick_list<'f>(f: &'f mut WebPFile, rng: &mut Rng) -> &'f mut Vec<Chunk> {
    let anmfs: Vec<usize> =
        (0..f.chunks.len()).filter(|&i| f.chunks[i].anmf.is_some()).collect();
    if !anmfs.is_empty() && rng.chance(1, 3) {
        let i = *rng.pick(&anmfs);
        &mut f.chunks[i].anmf.as_mut().unwrap().chunks
    } else {
        &mut f.chunks
    }
}

fn frame_dims_for(f: &WebPFile, path: (usize, Option<usize>)) -> (usize, usize) {
    let d = match path.1 {
        Some(_) => dims_in(&f.chunks[path.0].anmf.as_ref().unwrap().chunks),
        None => dims_in(&f.chunks),
    };
    let (w, h) = d.unwrap_or((8, 8));
    ((w as usize).clamp(1, 256), (h as usize).clamp(1, 256))
}

fn new_chunk(f: &WebPFile, rng: &mut Rng) -> Chunk {
    let (w, h) = dims_in(&f.chunks).map(|(w, h)| (w.clamp(1, 256) as usize, h.clamp(1, 256) as usize)).unwrap_or((8, 8));
    match rng.below(10) {
        0 => Chunk::new(riff::ICCP, random_meta(rng, 64)),
        1 => Chunk::new(riff::EXIF, random_meta(rng, 64)),
        2 => Chunk::new(riff::XMP, random_meta(rng, 64)),
        3 => {
            let n = if rng.chance(7, 8) { 6 } else { rng.below(10) };
            Chunk::new(riff::ANIM, rng.bytes(n))
        }
        4 => Chunk::new(riff::ALPH, if rng.bool() { vp8l_gen::gen_alph(rng, w, h) } else { vp8l_gen::gen_alph_raw(rng, w, h) }),
        5 => {
            let d = if rng.bool() { Some((w, h)) } else { None };
            Chunk::new(riff::VP8L, vp8l_gen::gen_vp8l(rng, d))
        }
        6 => Chunk::new(riff::VP8X, vp8x_payload(rng.u32() as u8, w as u32, h as u32)),
        7 => {
            let sub = Chunk::new(riff::VP8L, vp8l_gen::gen_vp8l(rng, Some((w.min(16), h.min(16)))));
            let hdr = anmf_header(0, 0, w.min(16) as u32, h.min(16) as u32, rng.below(100) as u32, rng.below(4) as u8);
            anmf_chunk(hdr, vec![sub])
        }
        _ => {
            let fc = if rng.chance(1, 2) { **rng.pick(&UNKNOWN_FOURCCS) } else {
                let b = rng.bytes(4);
                [b[0], b[1], b[2], b[3]]
            };
            Chunk::new(fc, random_meta(rng, 32))
        }
    }
}

/// Field-level mutation of a known chunk header.
fn mutate_fields(c: &mut Chunk, rng: &mut Rng) {
    match c.fourcc {
        riff::VP8X if c.payload.len() >= 10 => match rng.below(4) {
            0 => c.payload[0] ^= 1 << rng.below(8),
            1 => c.payload[0] = rng.u32() as u8,
            2 => put24(&mut c.payload, 4, rng.interesting(24)),
            _ => put24(&mut c.payload, 7, rng.interesting(24)),
        },
        riff::ANIM if c.payload.len() >= 6 => {
            if rng.bool() {
                let v = rng.u32().to_le_bytes();
                c.payload[..4].copy_from_slice(&v);
            } else {
                let v = (rng.interesting(16) as u16).to_le_bytes();
                c.payload[4..6].copy_from_slice(&v);
            }
        }
        riff::ANMF if c.anmf.is_some() => {
            let a = c.anmf.as_mut().unwrap();
            if a.header.len() < 16 {
                a.header.resize(16, 0);
            }
            match rng.below(7) {
                0 => put24(&mut a.header, 0, rng.interesting(24)),
                1 => put24(&mut a.header, 3, rng.interesting(24)),
                2 => {
                    let v = le24(&a.header, 6);
                    put24(&mut a.header, 6, if rng.bool() { v.wrapping_add(rng.range(0, 2) as u32).wrapping_sub(1) } else { rng.interesting(24) });
                }
                3 => {
                    let v = le24(&a.header, 9);
                    put24(&mut a.header, 9, if rng.bool() { v.wrapping_add(rng.range(0, 2) as u32).wrapping_sub(1) } else { rng.interesting(24) });
                }
                4 => put24(&mut a.header, 12, rng.interesting(24)),
                5 => a.header[15] ^= 1 << rng.below(2),
                _ => a.header[15] = rng.u32() as u8,
            }
        }
        riff::ALPH if !c.payload.is_empty() => match rng.below(4) {
            0 => c.payload[0] ^= 0x03,                         // compression
            1 => c.payload[0] ^= (1 + rng.below(3) as u8) << 2, // filter
            2 => c.payload[0] ^= (1 + rng.below(3) as u8) << 4, // preprocessing
            _ => c.payload[0] ^= 0xc0,                          // reserved
        },
        riff::VP8L if c.payload.len() >= 5 => match rng.below(5) {
            0 => bits::set_bits(&mut c.payload[1..], 0, 14, rng.interesting(14)),
            1 => bits::set_bits(&mut c.payload[1..], 14, 14, rng.interesting(14)),
            2 => bits::flip_bit(&mut c.payload[1..], 28),
            3 => bits::set_bits(&mut c.payload[1..], 29, 3, rng.below(8) as u32),
            _ => c.payload[0] = if rng.bool() { 0x2f } else { rng.u32() as u8 },
        },
        riff::VP8 if c.payload.len() >= 10 => match rng.below(7) {
            0 => c.payload[0] ^= 1,                        // keyframe bit
            1 => c.payload[0] ^= (1 + rng.below(7) as u8) << 1, // version
            2 => c.payload[0] ^= 0x10,                     // show_frame
            3 => {
                // first partition size (19 bits)
                let v = rng.interesting(19);
                let t = (c.payload[0] as u32 & 0x1f) | v << 5;
                c.payload[0] = t as u8;
                c.payload[1] = (t >> 8) as u8;
                c.payload[2] = (t >> 16) as u8;
            }
            4 => {
                let i = 3 + rng.below(3);
                c.payload[i] ^= 1 << rng.below(8); // start code
            }
            5 => {
                let i = if rng.bool() { 6 } else { 8 };
                let v = rng.interesting(14) as u16 | (c.payload[i + 1] as u16 & 0xc0) << 8;
                c.payload[i..i + 2].copy_from_slice(&v.to_le_bytes());
            }
            _ => {
                let i = if rng.bool() { 7 } else { 9 };
                c.payload[i] ^= 0x40 << rng.below(2); // scale bits
            }
        },
        _ => {
            if !c.payload.is_empty() {
                let i = rng.below(c.payload.len());
                c.payload[i] = rng.u32() as u8;
            }
        }
    }
}

/// One structural mutation step. Returns false if it could not be applied.
fn step(f: &mut WebPFile, rng: &mut Rng, bm: ByteMut, max_size: usize) -> bool {
    let paths = f.all_paths();
    match rng.below(20) {
        // ---- chunk-level
        0 => {
            let l = pick_list(f, rng);
            if l.is_empty() {
                return false;
            }
            let i = rng.below(l.len());
            l.remove(i);
        }
        1 => {
            let l = pick_list(f, rng);
            if l.is_empty() {
                return false;
            }
            let i = rng.below(l.len());
            let c = l[i].clone();
            let j = rng.below(l.len() + 1);
            l.insert(j, c);
        }
        2 => {
            let l = pick_list(f, rng);
            if l.len() < 2 {
                return false;
            }
            let (i, j) = (rng.below(l.len()), rng.below(l.len()));
            l.swap(i, j);
        }
        3 => {
            let l = pick_list(f, rng);
            if l.is_empty() {
                return false;
            }
            let c = l.remove(rng.below(l.len()));
            let j = rng.below(l.len() + 1);
            l.insert(j, c);
        }
        4 | 5 => {
            let c = new_chunk(f, rng);
            let l = pick_list(f, rng);
            let j = rng.below(l.len() + 1);
            l.insert(j, c);
        }
        6 => {
            if paths.is_empty() {
                return false;
            }
            let p = *rng.pick(&paths);
            let c = f.get_mut(p);
            c.flatten(true);
            c.fourcc = if rng.chance(3, 4) { *rng.pick(&riff::KNOWN) } else { **rng.pick(&UNKNOWN_FOURCCS) };
            c.reparse();
        }
        7 => {
            if paths.is_empty() {
                return false;
            }
            let p = *rng.pick(&paths);
            let c = f.get_mut(p);
            c.flatten(true);
            let n = rng.below(c.payload.len() + 1);
            c.payload.truncate(n);
            c.reparse();
        }
        // ---- field-level
        8..=10 => {
            if paths.is_empty() {
                return false;
            }
            let p = *rng.pick(&paths);
            mutate_fields(f.get_mut(p), rng);
        }
        // ---- payload bytes (libFuzzer's mutator on one payload)
        11 | 12 => {
            let cands: Vec<_> = paths.iter().copied().filter(|&p| f.get(p).anmf.is_none()).collect();
            if cands.is_empty() {
                return false;
            }
            let p = *rng.pick(&cands);
            let c = f.get_mut(p);
            let max = (c.payload.len() + 64).min(max_size);
            bm(&mut c.payload, max, rng);
        }
        // ---- LSB-first bit flips in lossless streams
        13 => {
            let cands: Vec<_> = paths
                .iter()
                .copied()
                .filter(|&p| {
                    let c = f.get(p);
                    (c.fourcc == riff::VP8L && c.payload.len() > 5) || (c.fourcc == riff::ALPH && c.payload.len() > 1)
                })
                .collect();
            if cands.is_empty() {
                return false;
            }
            let p = *rng.pick(&cands);
            let c = f.get_mut(p);
            let start = if c.fourcc == riff::VP8L { 8 + 32 } else { 8 };
            let nbits = c.payload.len() * 8;
            for _ in 0..rng.range(1, 4) {
                // Bias towards the front, where transforms and prefix codes live.
                let span = if rng.chance(2, 3) { (nbits - start).min(256) } else { nbits - start };
                let b = start + rng.below(span.max(1));
                bits::flip_bit(&mut c.payload, b);
            }
        }
        // ---- generative
        14 | 15 => {
            let cands: Vec<_> = paths
                .iter()
                .copied()
                .filter(|&p| matches!(f.get(p).fourcc, riff::VP8L | riff::ALPH))
                .collect();
            if cands.is_empty() {
                let c = Chunk::new(riff::VP8L, vp8l_gen::gen_vp8l(rng, None));
                f.chunks.push(c);
                return true;
            }
            let p = *rng.pick(&cands);
            let (w, h) = frame_dims_for(f, p);
            let c = f.get_mut(p);
            if c.fourcc == riff::VP8L {
                let keep = c.payload.len() >= 5 && rng.chance(3, 4);
                let dims = bitstream_dims(c).filter(|_| keep).map(|(w, h)| (w as usize, h as usize));
                let dims = dims.filter(|&(w, h)| w * h <= 65536);
                c.payload = vp8l_gen::gen_vp8l(rng, dims);
            } else {
                c.payload = if rng.chance(3, 4) { vp8l_gen::gen_alph(rng, w, h) } else { vp8l_gen::gen_alph_raw(rng, w, h) };
            }
        }
        16 => make_consistent(f, rng),
        // ---- promotions
        17 => {
            // simple -> extended (+ optional ALPH for lossy)
            if f.chunks.first().map(|c| c.fourcc) == Some(riff::VP8X) {
                return false;
            }
            let (w, h) = dims_in(&f.chunks).unwrap_or((1, 1));
            if f.chunks.first().map(|c| c.fourcc) == Some(riff::VP8) && rng.bool() {
                let a = if rng.bool() { vp8l_gen::gen_alph(rng, w as usize, h as usize) } else { vp8l_gen::gen_alph_raw(rng, w as usize, h as usize) };
                f.chunks.insert(0, Chunk::new(riff::ALPH, a));
            }
            f.chunks.insert(0, Chunk::new(riff::VP8X, vp8x_payload(0, w, h)));
            make_consistent(f, rng);
        }
        18 => {
            // still -> animated: wrap frame chunks into 1..3 ANMF frames
            if f.chunks.iter().any(|c| c.fourcc == riff::ANMF) {
                return false;
            }
            let frame: Vec<Chunk> = f
                .chunks
                .iter()
                .filter(|c| matches!(c.fourcc, riff::ALPH | riff::VP8 | riff::VP8L))
                .cloned()
                .collect();
            let Some((w, h)) = dims_in(&frame) else { return false };
            f.chunks.retain(|c| !matches!(c.fourcc, riff::ALPH | riff::VP8 | riff::VP8L | riff::VP8X));
            let (cw, ch) = (w + 2 * rng.below(3) as u32, h + 2 * rng.below(3) as u32);
            let mut anim = rng.bytes(4);
            anim.extend_from_slice(&(rng.below(3) as u16).to_le_bytes());
            let mut new = vec![Chunk::new(riff::VP8X, vp8x_payload(0x12, cw, ch)), Chunk::new(riff::ANIM, anim)];
            for _ in 0..rng.range(1, 3) {
                let x = 2 * rng.below(((cw - w) / 2 + 1) as usize) as u32;
                let y = 2 * rng.below(((ch - h) / 2 + 1) as usize) as u32;
                let hdr = anmf_header(x, y, w, h, rng.below(300) as u32, rng.below(4) as u8);
                new.push(anmf_chunk(hdr, frame.clone()));
            }
            new.append(&mut f.chunks);
            f.chunks = new;
        }
        _ => {
            // RIFF header fields
            match rng.below(4) {
                0 => f.riff_size = rng.interesting(32),
                1 => f.form[rng.below(4)] ^= 0x20,
                2 => {
                    let n = rng.range(1, 16);
                    f.trailing.extend(rng.bytes(n))
                }
                _ => f.trailing.clear(),
            }
        }
    }
    true
}

/// Mutates `data`; deterministic for a given `seed` and byte mutator.
pub fn mutate(data: &[u8], max_size: usize, seed: u64, bm: ByteMut) -> Vec<u8> {
    let mut rng = Rng::new(seed);
    let mut f = match WebPFile::parse(data) {
        Some(f) if f.riff == riff::RIFF || rng.chance(1, 2) => f,
        _ => {
            if rng.chance(1, 2) {
                let mut v = data.to_vec();
                bm(&mut v, max_size, &mut rng);
                return v;
            }
            synthesize(&mut rng)
        }
    };
    let n = match rng.below(8) {
        0..=4 => 1,
        5 | 6 => 2,
        _ => rng.range(3, 6),
    };
    let mut applied = 0;
    for _ in 0..n * 4 {
        if step(&mut f, &mut rng, &mut *bm, max_size) {
            applied += 1;
            if applied >= n {
                break;
            }
        }
    }
    if rng.chance(1, 10) {
        make_consistent(&mut f, &mut rng);
    }
    let fixup = !rng.chance(1, 16);
    let mut out = f.serialize(fixup);
    if rng.chance(1, 50) && !out.is_empty() {
        let cut = rng.below(out.len());
        out.truncate(cut);
    }
    out.truncate(max_size);
    out
}

/// Crossover: splice chunks (top-level or frames) from `b` into `a`.
pub fn crossover(a: &[u8], b: &[u8], max_size: usize, seed: u64) -> Vec<u8> {
    let mut rng = Rng::new(seed);
    let (Some(mut fa), Some(fb)) = (WebPFile::parse(a), WebPFile::parse(b)) else {
        let cut_a = rng.below(a.len() + 1);
        let cut_b = rng.below(b.len() + 1);
        let mut v = a[..cut_a].to_vec();
        v.extend_from_slice(&b[cut_b..]);
        v.truncate(max_size);
        return v;
    };
    let pb = fb.all_paths();
    if pb.is_empty() {
        return a[..a.len().min(max_size)].to_vec();
    }
    match rng.below(3) {
        0 => {
            // replace one chunk of a with one from b (same FourCC preferred)
            let src = fb.get(*rng.pick(&pb)).clone();
            let pa = fa.all_paths();
            let same: Vec<_> = pa.iter().copied().filter(|&p| fa.get(p).fourcc == src.fourcc).collect();
            if let Some(&p) = same.first().filter(|_| rng.chance(3, 4)) {
                *fa.get_mut(p) = src;
            } else {
                let j = rng.below(fa.chunks.len() + 1);
                fa.chunks.insert(j, src);
            }
        }
        1 => {
            // append all of b's frames
            for c in fb.chunks.iter().filter(|c| c.fourcc == riff::ANMF) {
                fa.chunks.push(c.clone());
            }
            if !fb.chunks.iter().any(|c| c.fourcc == riff::ANMF) {
                let src = fb.get(*rng.pick(&pb)).clone();
                fa.chunks.push(src);
            }
        }
        _ => {
            // a's header chunks + b's tail
            let i = rng.below(fa.chunks.len() + 1);
            let j = rng.below(fb.chunks.len() + 1);
            fa.chunks.truncate(i);
            fa.chunks.extend_from_slice(&fb.chunks[j..]);
        }
    }
    if rng.chance(1, 3) {
        make_consistent(&mut fa, &mut rng);
    }
    let mut out = fa.serialize(!rng.chance(1, 16));
    out.truncate(max_size);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mutate_is_deterministic_and_bounded() {
        let mut r = Rng::new(3);
        let seed_file = synthesize(&mut r).serialize(true);
        for s in 0..500u64 {
            let a = mutate(&seed_file, 4096, s, &mut simple_byte_mutate);
            let b = mutate(&seed_file, 4096, s, &mut simple_byte_mutate);
            assert_eq!(a, b);
            assert!(a.len() <= 4096);
        }
    }
}
