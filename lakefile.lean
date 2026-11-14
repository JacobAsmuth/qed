import Lake
open Lake DSL

package qed where

@[default_target]
lean_lib Qed where

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
