import Cli.Common
import Cli.Verify
import Cli.Build
import Cli.Test
import Cli.Scaffold

open Qed.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["dev"]                                    => cmdDev
  | ["build"]                                  => cmdBuild (prod := true)
  | ["build", "--sourcemap"]                   => cmdBuild (prod := true) (sourceMap := true)
  | ["build", "--dev"]                         => cmdBuild (prod := false)
  | ["build", "--dev", "--sourcemap"]          => cmdBuild (prod := false) (sourceMap := true)
  | ["build", "--dev", "--no-verify"]          => cmdBuild (prod := false) (skipVerify := true)
  | ["build", "--dev", "--no-verify", "--sourcemap"] => cmdBuild (prod := false) (skipVerify := true) (sourceMap := true)
  | ["start"] | ["preview"]             => cmdStart
  | "serve" :: rest                     => cmdServe rest
  | "manifest" :: rest                  => cmdManifest rest
  | "dev-auth" :: rest                  => cmdDevAuth rest
  | ["test"]                            => cmdTest
  | ["check"]                           => cmdCheck
  | ["clean"]                           => cmdClean
  | ["doctor"]                          => cmdDoctor
  | ["new", dir]                        => cmdNew dir
  | ["new"]                             => IO.eprintln "missing project directory: usage: qed new <dir>"; return 1
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | _ => IO.eprintln s!"unknown command: {" ".intercalate args}"; let _ ← usage; return 1
