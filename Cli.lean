import Cli.Common
import Cli.Verify
import Cli.Build
import Cli.Cloud
import Cli.Deploy
import Cli.Scaffold

open Qed.Cli in
def main (args : List String) : IO UInt32 := do
  let unknown : IO UInt32 := do IO.eprintln s!"unknown command: {" ".intercalate args}"; discard usage; return 1
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | ["dev"]        => cmdDev
  | ["start"] | ["preview"] => cmdStart
  | ["test"]       => cmdTest
  | ["check"]      => cmdCheck
  | ["clean"]      => cmdClean
  | ["doctor"]     => cmdDoctor
  | ["new", dir]   => cmdNew dir
  | ["new"]        => IO.eprintln "missing project directory: usage: qed new <dir>"; return 1
  | cmd :: rest =>
      if let some act := cloudCmds.lookup cmd then runExceptCmd (act rest)
      else match cmd with
        | "build" =>
            let (dev, noVerify) := (rest.contains "--dev", rest.contains "--no-verify")
            if rest.all (["--dev", "--no-verify", "--sourcemap"].contains ·) && (!noVerify || dev) then
              cmdBuild (prod := !dev) (skipVerify := noVerify) (sourceMap := rest.contains "--sourcemap")
            else unknown
        | "serve"     => cmdServe rest
        | "manifest"  => cmdManifest rest
        | "deploy"    => cmdDeploy rest
        | "dev-auth"  => cmdDevAuth rest
        | "stage-sdk" => cmdStageSdk rest
        | _           => unknown
