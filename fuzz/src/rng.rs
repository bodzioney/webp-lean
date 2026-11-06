//! Small deterministic PRNG (SplitMix64) so mutations are reproducible from a seed.
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }
    /// Uniform in [0, n) (n > 0; returns 0 for n == 0).
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }
    /// Uniform in [lo, hi] inclusive.
    pub fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }
    /// True with probability num/den.
    pub fn chance(&mut self, num: u32, den: u32) -> bool {
        (self.u32() % den) < num
    }
    pub fn bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.u32() as u8).collect()
    }
    /// "Interesting" integer near boundaries for a field of `bits` bits.
    pub fn interesting(&mut self, bits: u32) -> u32 {
        let max = if bits >= 32 { u32::MAX } else { (1u32 << bits) - 1 };
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => max,
            3 => max.wrapping_sub(1),
            4 => self.u32() & max,
            5 => (1u32 << self.below(bits as usize)) & max,
            6 => self.range(0, 64) as u32 & max,
            _ => ((1u32 << self.below(bits as usize)).wrapping_sub(1)) & max,
        }
    }
}
