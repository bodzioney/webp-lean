// The Lean runtime is linked dynamically (libleanshared.so); rustc-link-arg does not
// propagate from the webp-diff library, so the fuzz binary sets its own rpath here.
fn main() {
    let dir = std::env::var("WEBP_DIFF_LEAN_LIBDIR").ok().unwrap_or_else(|| {
        let out = std::process::Command::new("lean")
            .arg("--print-prefix")
            .current_dir("/var/data/diff-fuzz/webp/webp-lean")
            .output()
            .expect("run lean --print-prefix");
        format!("{}/lib/lean", String::from_utf8(out.stdout).unwrap().trim())
    });
    println!("cargo:rustc-link-arg=-Wl,-rpath,{dir}");
    println!("cargo:rerun-if-env-changed=WEBP_DIFF_LEAN_LIBDIR");
}
