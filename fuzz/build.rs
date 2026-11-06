//! Links the three oracles' native parts:
//! * libwebp static libs from build/libwebp-fuzz/<variant> (see scripts/build-libwebp.sh),
//! * the Lean decoder: by default the C files Lean emitted in webp-lean/.lake/build/ir are
//!   compiled here (so they get the same sanitizer-coverage instrumentation as libwebp and
//!   libFuzzer gets feedback from the Lean decoder too); `WEBP_DIFF_LEAN_MODE=staticlib`
//!   links webp-lean/.lake/build/lib/libwebp_WebP.a instead,
//! * the Lean runtime (libleanshared.so, which bundles its own libc++) dynamically.
//!
//! Variant selection: `WEBP_DIFF_VARIANT=asan|cov|plain`, otherwise inferred from RUSTFLAGS
//! (cargo-fuzz passes -Zsanitizer=address and/or -Cpasses=sancov-module).

use std::path::{Path, PathBuf};
use std::process::Command;

const ROOT: &str = "/var/data/diff-fuzz/webp";

fn collect_c(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect_c(&p, out);
        } else if p.extension().is_some_and(|x| x == "c") {
            out.push(p);
        }
    }
}

fn main() {
    for v in [
        "WEBP_DIFF_VARIANT",
        "WEBP_DIFF_LEAN_MODE",
        "WEBP_DIFF_LEAN_PREFIX",
        "CARGO_ENCODED_RUSTFLAGS",
    ] {
        println!("cargo:rerun-if-env-changed={v}");
    }
    let rustflags = std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    let variant = std::env::var("WEBP_DIFF_VARIANT").unwrap_or_else(|_| {
        if rustflags.contains("sanitizer=address") {
            "asan".into()
        } else if rustflags.contains("sancov") || rustflags.contains("sanitizer-coverage") {
            "cov".into()
        } else {
            "plain".into()
        }
    });
    let instrument: &[&str] = match variant.as_str() {
        "asan" => &["-fsanitize=fuzzer-no-link,address", "-fno-omit-frame-pointer"],
        "cov" => &["-fsanitize=fuzzer-no-link"],
        _ => &[],
    };

    // ---- libwebp ----
    let libwebp_dir = format!("{ROOT}/build/libwebp-fuzz/{variant}");
    assert!(
        Path::new(&format!("{libwebp_dir}/libwebp.a")).exists(),
        "missing {libwebp_dir}/libwebp.a: run scripts/build-libwebp.sh {variant}"
    );
    for l in ["webpdemux", "webp", "sharpyuv"] {
        println!("cargo:rerun-if-changed={libwebp_dir}/lib{l}.a");
    }
    let mut shim = cc::Build::new();
    shim.compiler("clang")
        .file("csrc/libwebp_shim.c")
        .include(format!("{ROOT}/libwebp/src"))
        .opt_level(2)
        .warnings(false);
    for f in instrument {
        shim.flag(f);
    }
    shim.compile("libwebp_shim");
    println!("cargo:rustc-link-search=native={libwebp_dir}");
    println!("cargo:rustc-link-lib=static=webpdemux");
    println!("cargo:rustc-link-lib=static=webp");
    println!("cargo:rustc-link-lib=static=sharpyuv");
    println!("cargo:rerun-if-changed=csrc/libwebp_shim.c");
    println!("cargo:rerun-if-changed=csrc/lean_shim.c");

    // ---- Lean ----
    let lean_proj = format!("{ROOT}/webp-lean");
    let prefix = std::env::var("WEBP_DIFF_LEAN_PREFIX").unwrap_or_else(|_| {
        let out = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(&lean_proj)
            .output()
            .expect("run `lean --print-prefix`");
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    });
    let lean_include = format!("{prefix}/include");
    let lean_libdir = format!("{prefix}/lib/lean");

    let mut ls = cc::Build::new();
    ls.compiler("clang")
        .file("csrc/lean_shim.c")
        .include(&lean_include)
        .opt_level(2)
        .warnings(false);
    ls.compile("lean_shim");

    let mode = std::env::var("WEBP_DIFF_LEAN_MODE").unwrap_or_else(|_| "ir".into());
    if mode == "staticlib" {
        let dir = format!("{lean_proj}/.lake/build/lib");
        println!("cargo:rerun-if-changed={dir}/libwebp_WebP.a");
        println!("cargo:rustc-link-search=native={dir}");
        println!("cargo:rustc-link-lib=static=webp_WebP");
    } else {
        let ir = PathBuf::from(format!("{lean_proj}/.lake/build/ir"));
        println!("cargo:rerun-if-changed={}", ir.display());
        let mut files = Vec::new();
        collect_c(&ir.join("WebP"), &mut files);
        files.push(ir.join("WebP.c"));
        files.sort();
        for f in &files {
            println!("cargo:rerun-if-changed={}", f.display());
        }
        // Lean's own flags (`leanc --print-cflags`) minus -fvisibility=hidden (we link statically).
        let mut b = cc::Build::new();
        b.compiler("clang")
            .include(&lean_include)
            .opt_level(3)
            .define("NDEBUG", None)
            .flag("-fstack-clash-protection")
            .flag("-ffp-contract=off")
            .flag("-fwrapv")
            .flag("-Wno-unused-parameter")
            .flag("-Wno-unused-label")
            .flag("-Wno-unused-but-set-variable")
            .warnings(false);
        // Coverage only (no ASan) for Lean code: Lean memory safety comes from the runtime,
        // and its RC-managed heap is not ASan-instrumented anyway.
        if variant != "plain" {
            b.flag("-fsanitize=fuzzer-no-link");
        }
        b.files(&files);
        b.compile("webp_lean_ir");
    }
    println!("cargo:rustc-link-search=native={lean_libdir}");
    // libleanshared.so exports its bundled LLVM libunwind (_Unwind_*). Make libgcc_s come
    // first in DT_NEEDED order so Rust panics/unwinding keep using the system unwinder.
    println!("cargo:rustc-link-lib=dylib=gcc_s");
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{lean_libdir}");
    println!("cargo:rustc-env=WEBP_DIFF_VARIANT={variant}");
}
