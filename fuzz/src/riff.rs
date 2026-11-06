//! Tolerant RIFF/WebP chunk-tree model used by the mutator (RFC 9649 §2.3, §2.7).
//!
//! Parsing never fails once the 12-byte header is present: truncated chunks keep whatever
//! bytes exist, and unparseable tails are kept verbatim so `serialize(parse(x), false) == x`.

pub const RIFF: [u8; 4] = *b"RIFF";
pub const WEBP: [u8; 4] = *b"WEBP";
pub const VP8: [u8; 4] = *b"VP8 ";
pub const VP8L: [u8; 4] = *b"VP8L";
pub const VP8X: [u8; 4] = *b"VP8X";
pub const ANIM: [u8; 4] = *b"ANIM";
pub const ANMF: [u8; 4] = *b"ANMF";
pub const ALPH: [u8; 4] = *b"ALPH";
pub const ICCP: [u8; 4] = *b"ICCP";
pub const EXIF: [u8; 4] = *b"EXIF";
pub const XMP: [u8; 4] = *b"XMP ";
pub const KNOWN: [[u8; 4]; 9] = [VP8, VP8L, VP8X, ANIM, ANMF, ALPH, ICCP, EXIF, XMP];

#[derive(Clone, Debug, PartialEq)]
pub struct Chunk {
    pub fourcc: [u8; 4],
    /// Size as declared in the file (used when serializing without fix-ups).
    pub declared: u32,
    /// Payload bytes (for ANMF: unused, see `anmf`).
    pub payload: Vec<u8>,
    /// Parsed ANMF contents.
    pub anmf: Option<Anmf>,
    /// Original padding byte (odd-sized complete chunks), kept for exact round-trips.
    pub pad: Option<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Anmf {
    /// 16-byte frame header (may be shorter if truncated).
    pub header: Vec<u8>,
    pub chunks: Vec<Chunk>,
    pub trailing: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct WebPFile {
    pub riff: [u8; 4],
    pub riff_size: u32,
    pub form: [u8; 4],
    pub chunks: Vec<Chunk>,
    /// Bytes that could not be parsed as chunks (garbage / data after the RIFF payload).
    pub trailing: Vec<u8>,
}

fn le32(b: &[u8]) -> u32 {
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

/// Parses a chunk sequence. Returns (chunks, unparsed tail).
pub fn parse_chunks(mut data: &[u8], depth: u32) -> (Vec<Chunk>, Vec<u8>) {
    let mut chunks = Vec::new();
    while data.len() >= 8 {
        let fourcc = [data[0], data[1], data[2], data[3]];
        let declared = le32(&data[4..8]);
        let avail = data.len() - 8;
        let take = (declared as usize).min(avail);
        let payload = data[8..8 + take].to_vec();
        let mut consumed = 8 + take;
        let mut pad = None;
        if take == declared as usize && declared % 2 == 1 && consumed < data.len() {
            pad = Some(data[consumed]);
            consumed += 1; // padding byte
        }
        let anmf = if fourcc == ANMF && depth == 0 {
            let hl = payload.len().min(16);
            let (sub, trailing) = parse_chunks(&payload[hl..], depth + 1);
            Some(Anmf { header: payload[..hl].to_vec(), chunks: sub, trailing })
        } else {
            None
        };
        chunks.push(Chunk { fourcc, declared, payload, anmf, pad });
        data = &data[consumed..];
    }
    (chunks, data.to_vec())
}

impl WebPFile {
    pub fn parse(data: &[u8]) -> Option<WebPFile> {
        if data.len() < 12 {
            return None;
        }
        let riff = [data[0], data[1], data[2], data[3]];
        let riff_size = le32(&data[4..8]);
        let form = [data[8], data[9], data[10], data[11]];
        let (chunks, trailing) = parse_chunks(&data[12..], 0);
        Some(WebPFile { riff, riff_size, form, chunks, trailing })
    }

    pub fn new(chunks: Vec<Chunk>) -> WebPFile {
        WebPFile { riff: RIFF, riff_size: 0, form: WEBP, chunks, trailing: Vec::new() }
    }

    /// Serializes. With `fixup`, all sizes (RIFF + chunks) are recomputed and odd payloads
    /// padded; without it, the declared sizes are written verbatim.
    pub fn serialize(&self, fixup: bool) -> Vec<u8> {
        let mut body = Vec::new();
        body.extend_from_slice(&self.form);
        write_chunks(&mut body, &self.chunks, fixup);
        let trailing_in_riff = !fixup;
        if trailing_in_riff {
            body.extend_from_slice(&self.trailing);
        }
        let mut out = Vec::with_capacity(body.len() + 8);
        out.extend_from_slice(&self.riff);
        let size = if fixup { body.len() as u32 } else { self.riff_size };
        out.extend_from_slice(&size.to_le_bytes());
        out.extend_from_slice(&body);
        if !trailing_in_riff {
            out.extend_from_slice(&self.trailing);
        }
        out
    }

    /// Iterates over all chunks including ANMF sub-chunks: (path, chunk).
    pub fn all_paths(&self) -> Vec<(usize, Option<usize>)> {
        let mut v = Vec::new();
        for (i, c) in self.chunks.iter().enumerate() {
            v.push((i, None));
            if let Some(a) = &c.anmf {
                for j in 0..a.chunks.len() {
                    v.push((i, Some(j)));
                }
            }
        }
        v
    }

    pub fn get_mut(&mut self, p: (usize, Option<usize>)) -> &mut Chunk {
        match p.1 {
            None => &mut self.chunks[p.0],
            Some(j) => &mut self.chunks[p.0].anmf.as_mut().unwrap().chunks[j],
        }
    }

    pub fn get(&self, p: (usize, Option<usize>)) -> &Chunk {
        match p.1 {
            None => &self.chunks[p.0],
            Some(j) => &self.chunks[p.0].anmf.as_ref().unwrap().chunks[j],
        }
    }
}

impl Chunk {
    pub fn new(fourcc: [u8; 4], payload: Vec<u8>) -> Chunk {
        let anmf = if fourcc == ANMF {
            let hl = payload.len().min(16);
            let (sub, trailing) = parse_chunks(&payload[hl..], 1);
            Some(Anmf { header: payload[..hl].to_vec(), chunks: sub, trailing })
        } else {
            None
        };
        Chunk { fourcc, declared: payload.len() as u32, payload, anmf, pad: None }
    }

    /// Payload bytes as they would be serialized (with fix-ups inside ANMF).
    pub fn body(&self, fixup: bool) -> Vec<u8> {
        match &self.anmf {
            Some(a) => {
                let mut b = a.header.clone();
                write_chunks(&mut b, &a.chunks, fixup);
                b.extend_from_slice(&a.trailing);
                b
            }
            None => self.payload.clone(),
        }
    }

    /// Re-derives `anmf` from `payload` (after raw payload mutation of an ANMF chunk).
    pub fn reparse(&mut self) {
        if self.fourcc == ANMF {
            let c = Chunk::new(ANMF, self.payload.clone());
            self.anmf = c.anmf;
        } else {
            self.anmf = None;
        }
    }

    /// Makes `payload` reflect `anmf` (before raw payload mutation of an ANMF chunk).
    pub fn flatten(&mut self, fixup: bool) {
        if self.anmf.is_some() {
            self.payload = self.body(fixup);
        }
    }
}

pub fn write_chunks(out: &mut Vec<u8>, chunks: &[Chunk], fixup: bool) {
    for c in chunks {
        let body = c.body(fixup);
        out.extend_from_slice(&c.fourcc);
        let size = if fixup { body.len() as u32 } else { c.declared };
        out.extend_from_slice(&size.to_le_bytes());
        out.extend_from_slice(&body);
        if fixup {
            if body.len() % 2 == 1 {
                out.push(0);
            }
        } else if let Some(p) = c.pad {
            out.push(p);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn roundtrip_garbage() {
        let mut d = b"RIFF\x20\0\0\0WEBPVP8L\x05\0\0\0\x2f\0\0\0\0\0junkX".to_vec();
        let f = WebPFile::parse(&d).unwrap();
        assert_eq!(f.serialize(false), d);
        d.truncate(20);
        let f = WebPFile::parse(&d).unwrap();
        assert_eq!(f.serialize(false), d);
    }
}
