//! Triage: run all oracles on each file and print outcomes + discrepancy signatures.
//! Usage: webp-diff-run [--quiet] [--summary] [--record] <files or dirs...>
//!   --quiet    only print files with discrepancies
//!   --summary  print a signature histogram at the end
//!   --record   store findings like the fuzzer does (WEBP_DIFF_FINDINGS etc.)
//!   --dump DIR write raw RGBA frames of each oracle to DIR/<oracle>.<frame>.rgba
use std::collections::BTreeMap;
use std::path::PathBuf;

fn collect(p: PathBuf, out: &mut Vec<PathBuf>) {
    if p.is_dir() {
        let mut v: Vec<_> = std::fs::read_dir(&p).unwrap().flatten().map(|e| e.path()).collect();
        v.sort();
        for e in v {
            collect(e, out);
        }
    } else {
        out.push(p);
    }
}

fn main() {
    let mut quiet = false;
    let mut summary = false;
    let mut record = false;
    let mut dump: Option<String> = None;
    let mut next_is_dump = false;
    let mut files = Vec::new();
    for a in std::env::args().skip(1) {
        if next_is_dump {
            dump = Some(a);
            next_is_dump = false;
            continue;
        }
        match a.as_str() {
            "--dump" => next_is_dump = true,
            "--quiet" | "-q" => quiet = true,
            "--summary" | "-s" => summary = true,
            "--record" => record = true,
            _ => collect(PathBuf::from(a), &mut files),
        }
    }
    let mut hist: BTreeMap<String, usize> = BTreeMap::new();
    let mut status: BTreeMap<String, usize> = BTreeMap::new();
    for f in &files {
        let data = match std::fs::read(f) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("{}: {e}", f.display());
                continue;
            }
        };
        let rep = match std::panic::catch_unwind(|| webp_diff::check(&data)) {
            Ok(r) => r,
            Err(_) => {
                println!("== {}\n  !! PANIC in an oracle", f.display());
                *hist.entry("PANIC".into()).or_default() += 1;
                continue;
            }
        };
        for (o, r) in &rep.outcomes {
            let k = match r {
                webp_diff::oracles::Outcome::Ok(_) => "ok",
                webp_diff::oracles::Outcome::Err(_) => "err",
                webp_diff::oracles::Outcome::Skip(_) => "skip",
            };
            *status.entry(format!("{o}:{k}")).or_default() += 1;
        }
        for s in rep.signatures() {
            *hist.entry(s.to_string()).or_default() += 1;
        }
        if let Some(d) = &dump {
            // Raw RGBA of every frame of every successful oracle: <d>/<oracle>.<frame>.rgba
            let _ = std::fs::create_dir_all(d);
            for (o, r) in &rep.outcomes {
                if let webp_diff::oracles::Outcome::Ok(dec) = r {
                    for (i, fr) in dec.frames.iter().enumerate() {
                        let _ = std::fs::write(format!("{d}/{o}.{i}.rgba"), &fr.rgba);
                    }
                }
            }
        }
        if record {
            webp_diff::compare::handle(&data, &rep);
        }
        if !quiet || !rep.discrepancies.is_empty() {
            println!("== {} ({} bytes)", f.display(), data.len());
            print!("{}", rep.render());
        }
    }
    if summary {
        println!("\n== {} files; oracle status:", files.len());
        for (k, v) in &status {
            println!("  {v:6}  {k}");
        }
        println!(
            "== max per-channel deviation within tolerance (animations, Lean pairs): {}",
            webp_diff::compare::LEAN_ANIM_MAX_DEV.load(std::sync::atomic::Ordering::Relaxed)
        );
        println!("== signatures:");
        for (k, v) in &hist {
            println!("  {v:6}  {k}");
        }
    }
}
