//! Cheap header probe: what kind of file is this, how big would decoding be?
//! Used to enforce one shared resource limit for all oracles and to pick the comparison mode.
use crate::riff::{self, Chunk, WebPFile};

#[derive(Clone, Debug, Default)]
pub struct Probe {
    /// First chunk FourCC after the RIFF header (VP8 / VP8L / VP8X / other).
    pub first: Option<[u8; 4]>,
    pub canvas: Option<(u32, u32)>,
    /// VP8X animation flag.
    pub animated: bool,
    pub vp8x_flags: u8,
    pub num_anmf: usize,
    /// Any 'VP8 ' bitstream anywhere -> lossy comparison rules.
    pub has_vp8: bool,
    pub has_vp8l: bool,
    pub has_alph: bool,
    /// Largest pixel count of any declared canvas/frame/bitstream dimension.
    pub max_pixels: u64,
    /// Reason to skip decoding entirely (resource limit).
    pub skip: Option<String>,
    /// Top-level ANMF frame headers, in order.
    pub frames: Vec<FrameInfo>,
    /// Byte range of the payload of the first top-level 'VP8 '/'VP8L' chunk (if any).
    pub vp8_payload: Option<(usize, usize)>,
    /// That chunk is the last chunk inside the RIFF payload.
    pub bitstream_is_last: bool,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct FrameInfo {
    pub x: u32,
    pub y: u32,
    pub w: u32,
    pub h: u32,
    /// Blending method bit: true = do not blend (overwrite).
    pub no_blend: bool,
    pub dispose: bool,
}

pub fn max_pixels_limit() -> u64 {
    std::env::var("WEBP_DIFF_MAX_PIXELS").ok().and_then(|s| s.parse().ok()).unwrap_or(1 << 22)
}

pub fn max_total_limit() -> u64 {
    std::env::var("WEBP_DIFF_MAX_TOTAL").ok().and_then(|s| s.parse().ok()).unwrap_or(1 << 24)
}

fn le24(b: &[u8]) -> u32 {
    b[0] as u32 | (b[1] as u32) << 8 | (b[2] as u32) << 16
}

/// Dimensions declared by a VP8 / VP8L payload header, if parseable.
pub fn bitstream_dims(c: &Chunk) -> Option<(u32, u32)> {
    let p = &c.payload;
    if c.fourcc == riff::VP8 && p.len() >= 10 {
        let w = u16::from_le_bytes([p[6], p[7]]) as u32 & 0x3fff;
        let h = u16::from_le_bytes([p[8], p[9]]) as u32 & 0x3fff;
        Some((w, h))
    } else if c.fourcc == riff::VP8L && p.len() >= 5 {
        let v = u32::from_le_bytes([p[1], p[2], p[3], p[4]]);
        Some(((v & 0x3fff) + 1, ((v >> 14) & 0x3fff) + 1))
    } else {
        None
    }
}

pub fn probe(data: &[u8]) -> Probe {
    let mut pr = Probe::default();
    let Some(f) = WebPFile::parse(data) else { return pr };
    // Also look at chunks hidden behind a too-small RIFF size: decoders differ in how far they read.
    pr.first = f.chunks.first().map(|c| c.fourcc);
    let note = |pr: &mut Probe, w: u32, h: u32| {
        pr.max_pixels = pr.max_pixels.max(w as u64 * h as u64);
    };
    for (i, c) in f.chunks.iter().enumerate() {
        match c.fourcc {
            riff::VP8X if c.payload.len() >= 10 => {
                if i == 0 {
                    pr.vp8x_flags = c.payload[0];
                    pr.animated = c.payload[0] & 0x02 != 0;
                }
                let w = le24(&c.payload[4..7]) + 1;
                let h = le24(&c.payload[7..10]) + 1;
                if i == 0 {
                    pr.canvas = Some((w, h));
                }
                note(&mut pr, w, h);
            }
            riff::ANMF => {
                pr.num_anmf += 1;
                if c.payload.len() >= 16 {
                    let w = le24(&c.payload[6..9]) + 1;
                    let h = le24(&c.payload[9..12]) + 1;
                    note(&mut pr, w, h);
                    pr.frames.push(FrameInfo {
                        x: le24(&c.payload[0..3]) * 2,
                        y: le24(&c.payload[3..6]) * 2,
                        w,
                        h,
                        no_blend: c.payload[15] & 2 != 0,
                        dispose: c.payload[15] & 1 != 0,
                    });
                }
            }
            _ => {}
        }
        let subs: Vec<&Chunk> = match &c.anmf {
            Some(a) => a.chunks.iter().collect(),
            None => vec![c],
        };
        for s in subs {
            match s.fourcc {
                riff::VP8 => pr.has_vp8 = true,
                riff::VP8L => pr.has_vp8l = true,
                riff::ALPH => pr.has_alph = true,
                _ => {}
            }
            if let Some((w, h)) = bitstream_dims(s) {
                if i == 0 && pr.canvas.is_none() {
                    pr.canvas = Some((w, h));
                }
                note(&mut pr, w, h);
            }
        }
    }
    {
        let mut off = 12usize;
        for c in &f.chunks {
            let start = off + 8;
            let is_bs = c.fourcc == riff::VP8 || c.fourcc == riff::VP8L;
            off = start + c.payload.len() + c.pad.is_some() as usize;
            if is_bs && pr.vp8_payload.is_none() {
                pr.vp8_payload = Some((start, start + c.payload.len()));
                pr.bitstream_is_last = off + 8 > (f.riff_size as usize).saturating_add(8);
            }
        }
    }
    // Decoders read the VP8X canvas from the 10 bytes after the chunk header even when the
    // declared chunk size is smaller, so probe the raw bytes too.
    if data.len() >= 30 && &data[12..16] == b"VP8X" {
        let w = le24(&data[24..27]) + 1;
        let h = le24(&data[27..30]) + 1;
        pr.canvas.get_or_insert((w, h));
        note(&mut pr, w, h);
    }
    let lim = max_pixels_limit();
    let canvas_px = pr.canvas.map(|(w, h)| w as u64 * h as u64).unwrap_or(0);
    if pr.max_pixels > lim {
        pr.skip = Some(format!("pixels {} > limit {}", pr.max_pixels, lim));
    } else if canvas_px * (pr.num_anmf.max(1) as u64) > max_total_limit() {
        pr.skip = Some(format!("frames*pixels {} > limit", canvas_px * pr.num_anmf as u64));
    }
    pr
}
