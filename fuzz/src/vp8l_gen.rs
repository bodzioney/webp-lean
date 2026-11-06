//! Structure-aware random VP8L bitstream generator (RFC 9649 §3).
//!
//! Instead of encoding a real image, it emits a random but (mostly) *valid* symbol stream:
//! random transforms, color cache, meta prefix codes with an entropy image, random complete
//! canonical prefix codes (simple and normal code-length codes with run-length symbols
//! 16/17/18, optional `max_symbol`), and literal / backward-reference / color-cache pixels.
//! It simulates decoding (pixel values, color cache) so that entropy-image group indices,
//! backward-reference distances and lengths stay in range. With `evil` set it occasionally
//! injects a specific invalidity. Fully deterministic from the [`Rng`] state.
use crate::bits::BitWriter;
use crate::rng::Rng;

const CODE_LENGTH_ORDER: [usize; 19] =
    [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

/// RFC 9649 Figure 20.
const DIST_MAP: [(i32, i32); 120] = [
    (0, 1), (1, 0), (1, 1), (-1, 1), (0, 2), (2, 0), (1, 2), (-1, 2), (2, 1), (-2, 1), (2, 2),
    (-2, 2), (0, 3), (3, 0), (1, 3), (-1, 3), (3, 1), (-3, 1), (2, 3), (-2, 3), (3, 2), (-3, 2),
    (0, 4), (4, 0), (1, 4), (-1, 4), (4, 1), (-4, 1), (3, 3), (-3, 3), (2, 4), (-2, 4), (4, 2),
    (-4, 2), (0, 5), (3, 4), (-3, 4), (4, 3), (-4, 3), (5, 0), (1, 5), (-1, 5), (5, 1), (-5, 1),
    (2, 5), (-2, 5), (5, 2), (-5, 2), (4, 4), (-4, 4), (3, 5), (-3, 5), (5, 3), (-5, 3), (0, 6),
    (6, 0), (1, 6), (-1, 6), (6, 1), (-6, 1), (2, 6), (-2, 6), (6, 2), (-6, 2), (4, 5), (-4, 5),
    (5, 4), (-5, 4), (3, 6), (-3, 6), (6, 3), (-6, 3), (0, 7), (7, 0), (1, 7), (-1, 7), (5, 5),
    (-5, 5), (7, 1), (-7, 1), (4, 6), (-4, 6), (6, 4), (-6, 4), (2, 7), (-2, 7), (7, 2), (-7, 2),
    (3, 7), (-3, 7), (7, 3), (-7, 3), (5, 6), (-5, 6), (6, 5), (-6, 5), (8, 0), (4, 7), (-4, 7),
    (7, 4), (-7, 4), (8, 1), (8, 2), (6, 6), (-6, 6), (8, 3), (5, 7), (-5, 7), (7, 5), (-7, 5),
    (8, 4), (6, 7), (-6, 7), (7, 6), (-7, 6), (8, 5), (7, 7), (-7, 7), (8, 6), (8, 7),
];

fn div_round_up(a: usize, b: usize) -> usize {
    a.div_ceil(b)
}

/// Prefix-coded value -> (value base, number of extra bits) (RFC 9649 §3.6.2.2).
fn prefix_value(code: usize) -> (usize, u32) {
    if code < 4 {
        (code + 1, 0)
    } else {
        let extra = ((code - 2) >> 1) as u32;
        let offset = (2 + (code & 1)) << extra;
        (offset + 1, extra)
    }
}

/// Distance code -> scan-line distance (RFC 9649 §3.6.2.2.1).
fn distance(code: usize, xsize: usize) -> usize {
    if code > 120 {
        code - 120
    } else {
        let (xi, yi) = DIST_MAP[code - 1];
        let d = xi as i64 + yi as i64 * xsize as i64;
        if d < 1 {
            1
        } else {
            d as usize
        }
    }
}

/// A canonical prefix code over an alphabet.
#[derive(Clone, Debug)]
struct Code {
    lens: Vec<u8>,
    codes: Vec<u32>,
    /// Symbols with nonzero length.
    syms: Vec<usize>,
}

impl Code {
    fn from_lens(lens: Vec<u8>) -> Code {
        let mut bl_count = [0u32; 16];
        for &l in &lens {
            if l > 0 {
                bl_count[l as usize] += 1;
            }
        }
        let mut next2 = [0u32; 16];
        let mut code = 0u32;
        for bits in 1..16 {
            code = (code + bl_count[bits - 1]) << 1;
            next2[bits] = code;
        }
        let mut codes = vec![0u32; lens.len()];
        let mut syms = Vec::new();
        for (s, &l) in lens.iter().enumerate() {
            if l > 0 {
                codes[s] = next2[l as usize];
                next2[l as usize] += 1;
                syms.push(s);
            }
        }
        Code { lens, codes, syms }
    }

    fn write(&self, bw: &mut BitWriter, sym: usize) {
        if self.syms.len() <= 1 {
            return; // single-leaf tree: zero bits
        }
        bw.put_code(self.codes[sym], self.lens[sym] as u32);
    }
}

/// Random complete binary tree with `n` leaves and depth <= maxd; returns leaf depths.
fn random_depths(rng: &mut Rng, n: usize, maxd: u8) -> Vec<u8> {
    if n <= 1 {
        return vec![1];
    }
    let mut leaves = vec![0u8];
    while leaves.len() < n {
        let cands: Vec<usize> = (0..leaves.len()).filter(|&i| leaves[i] < maxd).collect();
        if cands.is_empty() {
            break;
        }
        // Prefer splitting shallow leaves sometimes (balanced), else uniform (skewed trees).
        let i = if rng.chance(1, 3) {
            *cands.iter().min_by_key(|&&i| leaves[i]).unwrap()
        } else {
            *rng.pick(&cands)
        };
        leaves[i] += 1;
        let d = leaves[i];
        leaves.push(d);
    }
    for i in (1..leaves.len()).rev() {
        let j = rng.below(i + 1);
        leaves.swap(i, j);
    }
    leaves
}

/// Restriction on literal symbol values for a sub-image role.
#[derive(Clone, Copy)]
struct Hint {
    green: usize,
    red: usize,
    blue: usize,
    alpha: usize,
}

const FULL: Hint = Hint { green: 256, red: 256, blue: 256, alpha: 256 };

struct Group {
    green: Code,
    red: Code,
    blue: Code,
    alpha: Code,
    dist: Code,
}

pub struct Gen<'a> {
    rng: &'a mut Rng,
    bw: BitWriter,
    /// Inject invalidities occasionally.
    evil: bool,
    /// Budget of symbols to keep generation fast.
    budget: usize,
}

impl<'a> Gen<'a> {
    fn new(rng: &'a mut Rng) -> Self {
        let evil = rng.chance(1, 8);
        Gen { rng, bw: BitWriter::new(), evil, budget: 200_000 }
    }

    fn oops(&mut self, num: u32, den: u32) -> bool {
        self.evil && self.rng.chance(num, den)
    }

    fn pick_symbols(&mut self, alphabet: usize, lit_max: usize, extra: &[usize]) -> Vec<usize> {
        // How many symbols: mostly few, sometimes many.
        let n = match self.rng.below(10) {
            0..=2 => 1,
            3..=5 => self.rng.range(2, 4),
            6..=8 => self.rng.range(2, 16),
            _ => self.rng.range(2, 128),
        };
        let mut set: Vec<usize> = Vec::new();
        let lit_max = lit_max.min(alphabet).max(1);
        for _ in 0..n * 2 {
            if set.len() >= n {
                break;
            }
            let s = if !extra.is_empty() && self.rng.chance(1, 3) {
                *self.rng.pick(extra)
            } else if self.rng.chance(1, 2) {
                self.rng.below(lit_max.min(8))
            } else {
                self.rng.below(lit_max)
            };
            if s < alphabet && !set.contains(&s) {
                set.push(s);
            }
        }
        if set.is_empty() {
            set.push(0);
        }
        set.sort();
        set
    }

    /// Writes a prefix code for `syms` (chosen symbol set) over `alphabet`; returns the code.
    fn write_code(&mut self, alphabet: usize, syms: &[usize]) -> Code {
        let n = syms.len();
        let depths = random_depths(self.rng, n, 15);
        let mut lens = vec![0u8; alphabet];
        for (i, &s) in syms.iter().enumerate() {
            lens[s] = depths.get(i).copied().unwrap_or(15);
        }
        // Optionally break completeness.
        if self.oops(1, 6) {
            if n >= 2 && self.rng.bool() {
                lens[syms[0]] = 0; // incomplete tree
            } else {
                let s = self.rng.below(alphabet);
                lens[s] = self.rng.range(1, 15) as u8; // likely over-subscribed
            }
        }
        let simple_ok = n <= 2 && syms.iter().all(|&s| s < 256) && depths.iter().all(|&d| d == 1);
        if simple_ok && self.rng.chance(2, 3) {
            self.bw.put(1, 1);
            self.bw.put((n - 1) as u32, 1);
            let s0 = syms[0];
            let first8 = s0 >= 2 || self.rng.bool();
            self.bw.put(first8 as u32, 1);
            self.bw.put(s0 as u32, if first8 { 8 } else { 1 });
            if n == 2 {
                self.bw.put(syms[1] as u32, 8);
            }
            return Code::from_lens(lens);
        }
        if self.oops(1, 10) {
            // Simple code with an out-of-alphabet or duplicate symbol.
            self.bw.put(1, 1);
            self.bw.put(1, 1);
            self.bw.put(1, 1);
            let s = self.rng.below(256) as u32;
            self.bw.put(s, 8);
            self.bw.put(if self.rng.bool() { s } else { 255 }, 8);
            let mut l = vec![0u8; alphabet];
            for x in [s as usize, 255] {
                if x < alphabet {
                    l[x] = 1;
                }
            }
            return Code::from_lens(l);
        }
        self.bw.put(0, 1);
        self.write_normal_lengths(alphabet, &lens);
        Code::from_lens(lens)
    }

    /// Normal code-length code (RFC 9649 §3.7.2.1.2).
    fn write_normal_lengths(&mut self, alphabet: usize, lens: &[u8]) {
        let last = lens.iter().rposition(|&l| l != 0).map(|p| p + 1).unwrap_or(1);
        // Tokenize lens[0..last].
        let mut toks: Vec<(usize, u32, u32)> = Vec::new(); // (symbol, extra value, extra bits)
        let mut i = 0;
        let mut prev_nonzero = 8u8;
        while i < last {
            let l = lens[i];
            let mut run = 1;
            while i + run < last && lens[i + run] == l {
                run += 1;
            }
            if l == 0 && run >= 3 && self.rng.chance(4, 5) {
                let r = if run >= 11 && self.rng.chance(3, 4) { run.min(138) } else { run.min(10) };
                if r >= 11 {
                    toks.push((18, (r - 11) as u32, 7));
                } else {
                    toks.push((17, (r - 3) as u32, 3));
                }
                i += r;
                continue;
            }
            if l != 0 && l == prev_nonzero && run >= 3 && self.rng.chance(4, 5) {
                let r = run.min(6);
                toks.push((16, (r - 3) as u32, 2));
                i += r;
                continue;
            }
            toks.push((l as usize, 0, 0));
            if l != 0 {
                prev_nonzero = l;
            }
            i += 1;
        }
        // Either use max_symbol (= number of tokens) or pad zeros to the full alphabet.
        let use_max = toks.len() >= 2 && (last < alphabet) && self.rng.chance(1, 2);
        if !use_max {
            let mut rem = alphabet - last;
            while rem > 0 {
                if rem >= 11 && self.rng.chance(3, 4) {
                    let r = rem.min(138);
                    toks.push((18, (r - 11) as u32, 7));
                    rem -= r;
                } else if rem >= 3 && self.rng.chance(3, 4) {
                    let r = rem.min(10);
                    toks.push((17, (r - 3) as u32, 3));
                    rem -= r;
                } else {
                    toks.push((0, 0, 0));
                    rem -= 1;
                }
            }
            if self.oops(1, 8) {
                toks.push((18, self.rng.below(128) as u32, 7)); // overruns the alphabet
            }
        }
        // Code-length code over the used token symbols.
        let mut used: Vec<usize> = toks.iter().map(|t| t.0).collect();
        used.sort();
        used.dedup();
        let depths = random_depths(self.rng, used.len(), 7);
        let mut cl = vec![0u8; 19];
        for (k, &s) in used.iter().enumerate() {
            cl[s] = depths[k];
        }
        let mut num = CODE_LENGTH_ORDER.iter().rposition(|&s| cl[s] != 0).unwrap_or(0) + 1;
        num = num.max(4);
        if self.rng.chance(1, 4) {
            num = self.rng.range(num, 19);
        }
        self.bw.put((num - 4) as u32, 4);
        for &s in &CODE_LENGTH_ORDER[..num] {
            self.bw.put(cl[s] as u32, 3);
        }
        let clc = Code::from_lens(cl);
        if use_max {
            self.bw.put(1, 1);
            let mut max_symbol = toks.len();
            if self.oops(1, 6) {
                max_symbol = self.rng.range(2, alphabet + 50);
            }
            let need = 2 + 2 * self.rng.range(0, 7) as u32;
            // smallest legal length_nbits >= what's needed, randomized upward.
            let mut k = 0u32;
            while (max_symbol - 2) >= (1usize << (2 + 2 * k)) {
                k += 1;
            }
            let nbits = (2 + 2 * k).max(need.min(16)).min(16);
            self.bw.put((nbits - 2) / 2, 3);
            self.bw.put((max_symbol - 2) as u32, nbits);
        } else {
            self.bw.put(0, 1);
        }
        for (s, v, nb) in toks {
            clc.write(&mut self.bw, s);
            self.bw.put(v, nb);
        }
    }

    fn write_group(&mut self, cache_size: usize, hint: Hint) -> Group {
        let galpha = 256 + 24 + cache_size;
        let mut extra: Vec<usize> = Vec::new();
        if self.rng.chance(2, 3) {
            for _ in 0..self.rng.range(1, 4) {
                let m = if self.rng.bool() { 8 } else { 24 };
                extra.push(256 + self.rng.below(m));
            }
        }
        if cache_size > 0 {
            for _ in 0..self.rng.range(1, 4) {
                extra.push(280 + self.rng.below(cache_size));
            }
        }
        let mut gs = self.pick_symbols(galpha, hint.green, &extra);
        if !gs.iter().any(|&s| s < 256) && !self.oops(1, 2) {
            gs.push(self.rng.below(hint.green.max(1)));
            gs.sort();
            gs.dedup();
        }
        let green = self.write_code(galpha, &gs);
        let rs = self.pick_symbols(256, hint.red, &[]);
        let red = self.write_code(256, &rs);
        let bs = self.pick_symbols(256, hint.blue, &[]);
        let blue = self.write_code(256, &bs);
        let a_extra = [255usize];
        let as_ = self.pick_symbols(256, hint.alpha, if hint.alpha == 256 { &a_extra } else { &[] });
        let alpha = self.write_code(256, &as_);
        let ds_extra: Vec<usize> = (0..8).collect();
        let ds = self.pick_symbols(40, 40, &ds_extra);
        let dist = self.write_code(40, &ds);
        Group { green, red, blue, alpha, dist }
    }

    fn cache_bits(&mut self) -> u32 {
        if self.rng.chance(1, 2) {
            self.bw.put(0, 1);
            return 0;
        }
        self.bw.put(1, 1);
        let b = if self.oops(1, 4) {
            *self.rng.pick(&[0u32, 12, 13, 15])
        } else {
            self.rng.range(1, 11) as u32
        };
        self.bw.put(b, 4);
        if (1..=11).contains(&b) {
            b
        } else {
            0
        }
    }

    /// Entropy-coded image (sub-images: no meta codes) or spatially coded image (main).
    /// Returns decoded pixels (simulation) or None if generation got stuck.
    fn image(&mut self, w: usize, h: usize, main: bool, hint: Hint) -> Option<Vec<u32>> {
        let cbits = self.cache_bits();
        let csize = if cbits > 0 { 1usize << cbits } else { 0 };
        let mut meta: Option<(usize, usize, Vec<u32>)> = None;
        let mut ngroups = 1;
        if main {
            if self.rng.chance(1, 3) {
                self.bw.put(1, 1);
                let pb = self.rng.range(2, 9);
                self.bw.put((pb - 2) as u32, 3);
                let ew = div_round_up(w, 1 << pb);
                let eh = div_round_up(h, 1 << pb);
                let g = self.rng.range(1, 6);
                let ehint = Hint { green: g, red: if self.oops(1, 10) { 2 } else { 1 }, blue: 256, alpha: 256 };
                let ent = self.image(ew, eh, false, ehint)?;
                ngroups = ent.iter().map(|p| ((p >> 8) & 0xffff) as usize).max().unwrap_or(0) + 1;
                if ngroups > 600 {
                    return None;
                }
                meta = Some((pb, ew, ent));
            } else {
                self.bw.put(0, 1);
            }
        }
        let groups: Vec<Group> = (0..ngroups).map(|_| self.write_group(csize, hint)).collect();
        let total = w * h;
        let mut px: Vec<u32> = Vec::with_capacity(total);
        let mut cache = vec![0u32; csize];
        let insert = |cache: &mut Vec<u32>, p: u32| {
            if cbits > 0 {
                let k = (0x1e35a7bdu32.wrapping_mul(p) >> (32 - cbits)) as usize;
                cache[k] = p;
            }
        };
        while px.len() < total {
            if self.budget == 0 {
                return None;
            }
            self.budget -= 1;
            let pos = px.len();
            let (x, y) = (pos % w, pos / w);
            let gi = match &meta {
                Some((pb, ew, ent)) => ((ent[(y >> pb) * ew + (x >> pb)] >> 8) & 0xffff) as usize,
                None => 0,
            };
            let g = &groups[gi];
            if [&g.green, &g.red, &g.blue, &g.alpha, &g.dist].iter().any(|c| c.syms.is_empty()) {
                return None; // an (invalid) empty code: the stream is broken anyway
            }
            let gsyms = g.green.syms.clone();
            let mut done = false;
            for _attempt in 0..6 {
                let s = *self.rng.pick(&gsyms);
                if s < 256 {
                    let r = *self.rng.pick(&g.red.syms);
                    let b = *self.rng.pick(&g.blue.syms);
                    let a = *self.rng.pick(&g.alpha.syms);
                    g.green.write(&mut self.bw, s);
                    g.red.write(&mut self.bw, r);
                    g.blue.write(&mut self.bw, b);
                    g.alpha.write(&mut self.bw, a);
                    let p = (a as u32) << 24 | (r as u32) << 16 | (s as u32) << 8 | b as u32;
                    px.push(p);
                    insert(&mut cache, p);
                    done = true;
                    break;
                } else if s < 280 {
                    let (lbase, lbits) = prefix_value(s - 256);
                    let lextra = self.rng.below(1 << lbits);
                    let len = lbase + lextra;
                    let dsym = *self.rng.pick(&g.dist.syms);
                    let (dbase, dbits) = prefix_value(dsym);
                    let dextra = if dbits > 0 { self.rng.below(1usize << dbits.min(20)) } else { 0 };
                    let dcode = dbase + dextra;
                    let dist = distance(dcode, w);
                    let ok = dist <= pos && pos + len <= total;
                    if !ok && !self.oops(1, 20) {
                        continue;
                    }
                    g.green.write(&mut self.bw, s);
                    self.bw.put(lextra as u32, lbits);
                    g.dist.write(&mut self.bw, dsym);
                    self.bw.put(dextra as u32, dbits);
                    if !ok {
                        return None; // stream is now invalid; stop here
                    }
                    for k in 0..len {
                        let p = px[pos + k - dist];
                        px.push(p);
                        insert(&mut cache, p);
                    }
                    done = true;
                    break;
                } else {
                    let idx = s - 280;
                    g.green.write(&mut self.bw, s);
                    let p = cache[idx];
                    px.push(p);
                    insert(&mut cache, p);
                    done = true;
                    break;
                }
            }
            if !done {
                // Fall back to any literal; if the code has none, we are stuck.
                let lit = gsyms.iter().copied().find(|&s| s < 256)?;
                let r = g.red.syms[0];
                let b = g.blue.syms[0];
                let a = g.alpha.syms[0];
                g.green.write(&mut self.bw, lit);
                g.red.write(&mut self.bw, r);
                g.blue.write(&mut self.bw, b);
                g.alpha.write(&mut self.bw, a);
                let p = (a as u32) << 24 | (r as u32) << 16 | (lit as u32) << 8 | b as u32;
                px.push(p);
                insert(&mut cache, p);
            }
        }
        Some(px)
    }

    /// Image stream = transforms + spatially coded image (RFC 9649 §3.8.1 `image-stream`).
    fn image_stream(&mut self, w: usize, h: usize) {
        let mut xsize = w;
        let mut types: Vec<u32> = vec![0, 1, 2, 3];
        for i in (1..types.len()).rev() {
            let j = self.rng.below(i + 1);
            types.swap(i, j);
        }
        let n = match self.rng.below(6) {
            0 | 1 => 0,
            2 => 1,
            3 => 2,
            4 => 3,
            _ => 4,
        };
        let mut chosen: Vec<u32> = types[..n].to_vec();
        if self.oops(1, 8) && !chosen.is_empty() {
            let d = chosen[0];
            chosen.push(d); // transform used twice
        }
        for t in chosen {
            self.bw.put(1, 1);
            self.bw.put(t, 2);
            match t {
                0 | 1 => {
                    let bits = self.rng.range(2, 9);
                    self.bw.put((bits - 2) as u32, 3);
                    let sw = div_round_up(xsize, 1 << bits);
                    let sh = div_round_up(h, 1 << bits);
                    let hint = if t == 0 {
                        Hint { green: if self.rng.chance(1, 10) { 16 } else { 14 }, ..FULL }
                    } else {
                        FULL
                    };
                    if self.image(sw, sh, false, hint).is_none() {
                        return;
                    }
                }
                2 => {}
                _ => {
                    let size = match self.rng.below(4) {
                        0 => self.rng.range(1, 2),
                        1 => self.rng.range(3, 4),
                        2 => self.rng.range(5, 16),
                        _ => self.rng.range(17, 256),
                    };
                    self.bw.put((size - 1) as u32, 8);
                    if self.image(size, 1, false, FULL).is_none() {
                        return;
                    }
                    let wb = match size {
                        1..=2 => 3,
                        3..=4 => 2,
                        5..=16 => 1,
                        _ => 0,
                    };
                    xsize = div_round_up(xsize, 1 << wb);
                }
            }
        }
        self.bw.put(0, 1);
        // Main image: literal ranges biased so color-indexed images use valid indices.
        let _ = self.image(xsize, h, true, FULL);
    }

    fn finish(mut self) -> Vec<u8> {
        let mut out = std::mem::take(&mut self.bw).finish();
        if self.oops(1, 4) && !out.is_empty() {
            let cut = self.rng.below(out.len());
            out.truncate(cut);
        }
        if self.rng.chance(1, 16) {
            let n = self.rng.below(8);
            out.extend(self.rng.bytes(n));
        }
        out
    }
}

fn random_dims(rng: &mut Rng) -> (usize, usize) {
    let mut d = || match rng.below(10) {
        0..=5 => rng.range(1, 16),
        6..=8 => rng.range(1, 64),
        _ => rng.range(1, 300),
    };
    let (w, h) = (d(), d());
    if w * h > 65536 {
        (w, 65536 / w)
    } else {
        (w, h)
    }
}

/// Full 'VP8L' chunk payload: signature, header and image stream.
pub fn gen_vp8l(rng: &mut Rng, dims: Option<(usize, usize)>) -> Vec<u8> {
    let (w, h) = dims.unwrap_or_else(|| random_dims(rng));
    let mut g = Gen::new(rng);
    let sig = if g.oops(1, 10) { 0x2e } else { 0x2f };
    g.bw.put(sig, 8);
    g.bw.put((w - 1) as u32, 14);
    g.bw.put((h - 1) as u32, 14);
    let alpha = g.rng.bool() as u32;
    g.bw.put(alpha, 1);
    let version = if g.oops(1, 10) { g.rng.range(1, 7) as u32 } else { 0 };
    g.bw.put(version, 3);
    g.image_stream(w, h);
    g.finish()
}

/// 'ALPH' chunk payload with lossless compression for a `w`x`h` frame.
pub fn gen_alph(rng: &mut Rng, w: usize, h: usize) -> Vec<u8> {
    let filter = rng.below(4) as u8;
    let pre = if rng.chance(1, 4) { 1 } else { 0 };
    let mut g = Gen::new(rng);
    let method = if g.oops(1, 6) { 2 + g.rng.below(2) as u8 } else { 1 };
    let mut hdr = method | filter << 2 | pre << 4;
    if g.oops(1, 6) {
        hdr |= 0xc0;
    }
    g.image_stream(w, h);
    let mut out = vec![hdr];
    out.extend(g.finish());
    out
}

/// Raw (uncompressed) ALPH payload.
pub fn gen_alph_raw(rng: &mut Rng, w: usize, h: usize) -> Vec<u8> {
    let filter = rng.below(4) as u8;
    let mut out = vec![filter << 2];
    let mut n = w * h;
    if rng.chance(1, 8) {
        n = rng.below(n + 2);
    }
    out.extend(rng.bytes(n));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_codes() {
        let c = Code::from_lens(vec![2, 1, 3, 3]);
        assert_eq!(c.codes, vec![0b10, 0b0, 0b110, 0b111]);
    }
    #[test]
    fn depths_complete() {
        let mut r = Rng::new(1);
        for n in 1..300 {
            let d = random_depths(&mut r, n, 15);
            assert_eq!(d.len(), n);
            if n > 1 {
                let kraft: f64 = d.iter().map(|&x| 0.5f64.powi(x as i32)).sum();
                assert!((kraft - 1.0).abs() < 1e-9);
            }
        }
    }
    #[test]
    fn deterministic() {
        let a = gen_vp8l(&mut Rng::new(7), None);
        let b = gen_vp8l(&mut Rng::new(7), None);
        assert_eq!(a, b);
    }
}
