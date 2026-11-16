import Lake
open Lake DSL

package qed where

target qed_server_o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "qed_server.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "qed_server.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-O3", "-fPIC", "-Wall", "-Wextra", "-Wno-unused-parameter"] "cc" getLeanTrace

@[default_target]
lean_lib Qed where

@[default_target]
lean_lib QedServer where
  roots := #[`Qed.Server.Prim, `Qed.Server.Native]
  moreLinkObjs := #[qed_server_o]
  moreLinkArgs := #["-pthread", "-lssl", "-lcrypto"]

@[default_target]
lean_lib QedProofs where
  roots := #[`Qed.Proofs.DomEquiv]

@[default_target]
lean_lib JsProofs where
  roots := #[`Js.Proofs]

lean_lib Js where

lean_exe qedjs where
  root := `Js.Main
  supportInterpreter := true

lean_lib Examples where
  globs := #[.submodules `Examples]

lean_exe counter where
  root := `Examples.Native

lean_lib Cli where
  globs := #[.submodules `Cli]

lean_exe qed where
  root := `Cli

lean_exe bench where
  root := `Examples.Bench.Pipeline

lean_exe users_ssr where
  root := `Examples.UsersSSR

lean_exe template_ssr where
  root := `Examples.TemplateSSR
