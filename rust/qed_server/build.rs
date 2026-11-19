use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/lean_bridge.c");
    println!("cargo:rerun-if-env-changed=LEAN_INCLUDE_DIR");

    let inc_dir = env::var("LEAN_INCLUDE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let out = Command::new("lean")
                .arg("--print-prefix")
                .output()
                .expect("LEAN_INCLUDE_DIR unset and `lean --print-prefix` failed");
            assert!(out.status.success(), "`lean --print-prefix` exited non-zero");
            PathBuf::from(String::from_utf8(out.stdout).unwrap().trim()).join("include")
        });

    cc::Build::new()
        .file("src/lean_bridge.c")
        .include(inc_dir)
        .opt_level(3)
        .pic(true)
        .flag_if_supported("-Wall")
        .flag_if_supported("-Wextra")
        .compile("qed_lean_bridge");
}
