//! Offline mutator driver.
//!   webp-diff-mutate <in> <out> [--seed N] [--max-size N] [--crossover other.webp]
//!   webp-diff-mutate --stats <dir> [--iters N]   (validity rate of mutants under libwebp)
//!   webp-diff-mutate --gen <out-dir> [--count N] (write N generated VP8L files)
use webp_diff::mutate::{crossover, mutate, simple_byte_mutate};
use webp_diff::rng::Rng;

fn arg<T: std::str::FromStr>(args: &[String], name: &str, d: T) -> T {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let seed: u64 = arg(&args, "--seed", 1);
    let max: usize = arg(&args, "--max-size", 1 << 20);
    if args.first().map(|s| s.as_str()) == Some("--gen") {
        let dir = &args[1];
        std::fs::create_dir_all(dir).unwrap();
        let n: u64 = arg(&args, "--count", 100);
        for i in 0..n {
            let mut r = Rng::new(seed.wrapping_mul(1_000_003).wrapping_add(i));
            let f = webp_diff::mutate::synthesize(&mut r).serialize(true);
            std::fs::write(format!("{dir}/gen-{seed}-{i}.webp"), f).unwrap();
        }
        return;
    }
    if args.first().map(|s| s.as_str()) == Some("--stats") {
        let dir = &args[1];
        let iters: u64 = arg(&args, "--iters", 20);
        let mut files: Vec<_> = std::fs::read_dir(dir).unwrap().flatten().map(|e| e.path()).collect();
        files.sort();
        let (mut total, mut ok, mut ok_any, mut seed_ok) = (0u64, 0u64, 0u64, 0u64);
        let mut sigs = std::collections::BTreeMap::<String, u64>::new();
        for (fi, f) in files.iter().enumerate() {
            let data = std::fs::read(f).unwrap();
            if matches!(webp_diff::oracles::run_libwebp_anim(&data, &webp_diff::probe::probe(&data)), webp_diff::oracles::Outcome::Ok(_)) {
                seed_ok += 1;
            }
            for it in 0..iters {
                let m = mutate(&data, 1 << 16, (fi as u64) << 20 | it, &mut simple_byte_mutate);
                let rep = webp_diff::check(&m);
                if std::env::var("WEBP_DIFF_FINDINGS").map(|v| v != "off").unwrap_or(false) {
                    webp_diff::compare::handle(&m, &rep);
                }
                total += 1;
                let lw = rep.outcomes.iter().any(|(o, r)| *o == webp_diff::oracles::Oracle::LibwebpAnim && matches!(r, webp_diff::oracles::Outcome::Ok(_)));
                let any = rep.outcomes.iter().any(|(_, r)| matches!(r, webp_diff::oracles::Outcome::Ok(_)));
                ok += lw as u64;
                ok_any += any as u64;
                for s in rep.signatures() {
                    *sigs.entry(s.to_string()).or_default() += 1;
                }
            }
        }
        println!("seeds: {} (libwebp-anim ok: {seed_ok})", files.len());
        println!("mutants: {total}; libwebp-anim decodes: {ok} ({:.1}%); any oracle decodes: {ok_any} ({:.1}%)",
            100.0 * ok as f64 / total as f64, 100.0 * ok_any as f64 / total as f64);
        for (k, v) in sigs {
            println!("  {v:6}  {k}");
        }
        return;
    }
    let input = std::fs::read(&args[0]).expect("read input");
    let out = if let Some(i) = args.iter().position(|a| a == "--crossover") {
        let other = std::fs::read(&args[i + 1]).expect("read crossover input");
        crossover(&input, &other, max, seed)
    } else {
        let mut bm = |b: &mut Vec<u8>, m: usize, r: &mut Rng| simple_byte_mutate(b, m, r);
        mutate(&input, max, seed, &mut bm)
    };
    std::fs::write(&args[1], out).expect("write output");
}
