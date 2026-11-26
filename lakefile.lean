import Lake
open Lake DSL

package qed where

extern_lib libqed_server pkg := do
  let libFile := pkg.staticLibDir / nameToStaticLib "qed_server"
  let crateDir := pkg.dir / "rust" / "qed_server"
  let srcJobs := Job.collectArray #[
    ← inputTextFile (crateDir / "Cargo.toml"),
    ← inputTextFile (crateDir / "Cargo.lock"),
    ← inputTextFile (crateDir / "build.rs"),
    ← inputTextFile (crateDir / "src" / "lean_bridge.c"),
    ← inputTextFile (crateDir / "src" / "lib.rs"),
    ← inputTextFile (crateDir / "src" / "lean_ffi.rs"),
    ← inputTextFile (crateDir / "src" / "crypto.rs"),
    ← inputTextFile (crateDir / "src" / "gzip.rs"),
    ← inputTextFile (crateDir / "src" / "outbound.rs"),
    ← inputTextFile (crateDir / "src" / "server.rs"),
    ← inputTextFile (crateDir / "src" / "sqlite.rs"),
    ← inputTextFile (crateDir / "src" / "watch.rs")
  ]
  buildFileAfterDep libFile srcJobs fun _ => do
    let incDir ← getLeanIncludeDir
    proc {
      cmd := "cargo"
      args := #["build", "--release", "--manifest-path", (crateDir / "Cargo.toml").toString]
      env := #[("LEAN_INCLUDE_DIR", some incDir.toString)]
    }
    createParentDirs libFile
    let built := crateDir / "target" / "release" / nameToStaticLib "qed_server"
    IO.FS.writeBinFile libFile (← IO.FS.readBinFile built)

@[default_target]
lean_lib Qed where

lean_lib QedServer where
  roots := #[`Qed.Server.Net, `Qed.Server.Http, `Qed.Server.Prim,
    `Qed.Server.Db.HttpSql, `Qed.Server.Db.PgWire, `Qed.Auth.Oidc, `Qed.Server.Native,
    `Qed.Cloud.Protocol, `Qed.Cloud.Executor]
  moreLinkArgs := #["-pthread"]

lean_lib QedProofs where
  roots := #[`Qed.Proofs.DomArena, `Qed.Proofs.ViewPatch, `Qed.Proofs.KeyedReconcile, `Qed.Proofs.Hydration]

lean_lib JsProofs where
  roots := #[`Js.Proofs]

lean_lib Js where
  roots := #[`Js.Backend, `Js.VerifyEnv]

lean_exe qedjs where
  root := `Js.Main
  supportInterpreter := true

lean_lib Examples where
  globs := #[.submodules `Examples]

lean_lib QedTests where
  globs := #[.submodules `QedTests]

lean_lib Bench where
  globs := #[.submodules `Bench]

lean_lib Cli where
  globs := #[.submodules `Cli]

lean_exe qed where
  root := `Cli
  moreLinkArgs := #["-pthread"]

lean_exe qedtest where
  root := `QedTests.Runner
  moreLinkArgs := #["-pthread"]

lean_exe bench where
  root := `Bench.Pipeline
