//! Differential testing of WebP decoders.
//!
//! * [`oracles`]: Lean (FFI), libwebp (simple + anim/demux), image-webp; normalized outcomes.
//! * [`compare`]: pairwise comparison, discrepancy signatures, findings recording.
//! * [`riff`] / [`mutate`] / [`vp8l_gen`]: the format-aware mutator.
pub mod bits;
pub mod compare;
pub mod mutate;
pub mod oracles;
pub mod probe;
pub mod riff;
pub mod rng;
pub mod vp8l_gen;

/// Runs all oracles on `data` and compares them (the body of the fuzz target).
pub fn check(data: &[u8]) -> compare::Report {
    let probe = probe::probe(data);
    let outcomes = oracles::run_all(data, &probe);
    compare::compare(data, &probe, outcomes)
}
