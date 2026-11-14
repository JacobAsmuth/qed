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
  | ["test"]                            => cmdTest
  | ["check"]                           => cmdCheck
  | ["clean"]                           => cmdClean
  | ["doctor"]                          => cmdDoctor
  | ["new", dir]                        => cmdNew dir
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | _ => IO.eprintln s!"unknown command: {" ".intercalate args}"; usage
