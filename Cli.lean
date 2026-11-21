import Cli.Common
import Cli.Verify
import Cli.Build
import Cli.Test
import Cli.Scaffold

open Qed.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["dev"]                             => cmdDev
  | ["build"]                           => cmdBuild (prod := true)
  | ["build", "--dev"]                  => cmdBuild (prod := false)
  | ["build", "--dev", "--no-verify"]   => cmdBuild (prod := false) (skipVerify := true)
  | ["start"] | ["preview"]             => cmdStart
  | "serve" :: rest                     => cmdServe rest
  | ["test"]                            => cmdTest
  | ["check"]                           => cmdCheck
  | ["clean"]                           => cmdClean
  | ["doctor"]                          => cmdDoctor
  | ["new", dir]                        => cmdNew dir
  | ["new"]                             => IO.eprintln "missing project directory: usage: qed new <dir>"; return 1
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | _ => IO.eprintln s!"unknown command: {" ".intercalate args}"; let _ ← usage; return 1
