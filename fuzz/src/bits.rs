//! LSB-first bit reader/writer as used by VP8L (RFC 9649 §3.2).
pub struct BitWriter {
    pub buf: Vec<u8>,
    acc: u64,
    n: u32,
}

impl Default for BitWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl BitWriter {
    pub fn new() -> Self {
        BitWriter { buf: Vec::new(), acc: 0, n: 0 }
    }
    /// Writes the low `n` bits of `v`, least significant first (ReadBits(n) order).
    pub fn put(&mut self, v: u32, n: u32) {
        debug_assert!(n <= 32);
        if n == 0 {
            return;
        }
        let v = if n == 32 { v as u64 } else { (v as u64) & ((1u64 << n) - 1) };
        self.acc |= v << self.n;
        self.n += n;
        while self.n >= 8 {
            self.buf.push(self.acc as u8);
            self.acc >>= 8;
            self.n -= 8;
        }
    }
    /// Writes a prefix codeword (`len` bits, MSB of the code first, as in DEFLATE).
    pub fn put_code(&mut self, code: u32, len: u32) {
        for i in (0..len).rev() {
            self.put((code >> i) & 1, 1);
        }
    }
    pub fn bit_len(&self) -> usize {
        self.buf.len() * 8 + self.n as usize
    }
    pub fn finish(mut self) -> Vec<u8> {
        if self.n > 0 {
            self.buf.push(self.acc as u8);
        }
        self.buf
    }
}

pub struct BitReader<'a> {
    data: &'a [u8],
    pub pos: usize,
}

impl<'a> BitReader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        BitReader { data, pos: 0 }
    }
    pub fn read(&mut self, n: u32) -> Option<u32> {
        let mut v = 0u32;
        for i in 0..n {
            let byte = *self.data.get(self.pos / 8)?;
            v |= (((byte >> (self.pos % 8)) & 1) as u32) << i;
            self.pos += 1;
        }
        Some(v)
    }
}

/// Flips bit `bit` (LSB-first numbering) of `data`.
pub fn flip_bit(data: &mut [u8], bit: usize) {
    if bit / 8 < data.len() {
        data[bit / 8] ^= 1 << (bit % 8);
    }
}

/// Overwrites `n` bits starting at LSB-first bit position `pos` with `v`.
pub fn set_bits(data: &mut [u8], pos: usize, n: u32, v: u32) {
    for i in 0..n as usize {
        let b = pos + i;
        if b / 8 >= data.len() {
            return;
        }
        let m = 1u8 << (b % 8);
        if (v >> i) & 1 == 1 {
            data[b / 8] |= m;
        } else {
            data[b / 8] &= !m;
        }
    }
}
