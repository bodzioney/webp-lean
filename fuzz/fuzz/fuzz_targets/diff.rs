#![no_main]
//! Differential fuzz target: Lean vs libwebp (simple + anim) vs image-webp,
//! with the format-aware mutator from webp_diff::mutate.
use libfuzzer_sys::{fuzz_crossover, fuzz_mutator, fuzz_target, fuzzer_mutate};
use webp_diff::rng::Rng;

fuzz_target!(|data: &[u8]| {
    let report = webp_diff::check(data);
    webp_diff::compare::handle(data, &report);
});

/// libFuzzer's byte-level mutator on a Vec (used for chunk payloads).
fn lf_mutate(buf: &mut Vec<u8>, max_len: usize, _rng: &mut Rng) {
    let len = buf.len();
    let max_len = max_len.max(len);
    buf.resize(max_len, 0);
    let n = fuzzer_mutate(buf, len, max_len);
    buf.truncate(n);
}

fuzz_mutator!(|data: &mut [u8], size: usize, max_size: usize, seed: u32| {
    let mut rng = Rng::new(seed as u64);
    // Keep a share of plain libFuzzer mutations for diversity.
    if rng.chance(1, 5) {
        return fuzzer_mutate(data, size, max_size);
    }
    let out = webp_diff::mutate::mutate(&data[..size], max_size, seed as u64, &mut lf_mutate);
    let n = out.len().min(max_size);
    data[..n].copy_from_slice(&out[..n]);
    n
});

fuzz_crossover!(|data1: &[u8], data2: &[u8], out: &mut [u8], seed: u32| {
    let v = webp_diff::mutate::crossover(data1, data2, out.len(), seed as u64);
    let n = v.len().min(out.len());
    out[..n].copy_from_slice(&v[..n]);
    n
});
