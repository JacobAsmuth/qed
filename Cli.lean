import Cli.Common
import Cli.Verify
import Cli.Build
import Cli.Cloud
import Cli.Deploy
import Cli.Test
import Cli.Scaffold

open Qed.Cli in
def main (args : List String) : IO UInt32 := do
  let unknown : IO UInt32 := do IO.eprintln s!"unknown command: {" ".intercalate args}"; discard usage; return 1
  match args with
  | ["dev"]        => cmdDev
  | "build" :: flags =>
      let (dev, noVerify) := (flags.contains "--dev", flags.contains "--no-verify")
      if flags.all (["--dev", "--no-verify", "--sourcemap"].contains ·) && (!noVerify || dev) then
        cmdBuild (prod := !dev) (skipVerify := noVerify) (sourceMap := flags.contains "--sourcemap")
      else unknown
  | ["start"] | ["preview"] => cmdStart
  | "serve" :: rest         => cmdServe rest
  | "manifest" :: rest      => cmdManifest rest
  | "login" :: rest         => cmdLogin rest
  | "logout" :: rest        => cmdLogout rest
  | "whoami" :: rest        => cmdWhoami rest
  | "status" :: rest        => cmdStatus rest
  | "logs" :: rest          => cmdLogs rest
  | "cancel" :: rest        => cmdCancel rest
  | "secrets" :: rest       => cmdSecrets rest
  | "rollback" :: rest      => cmdRollback rest
  | "deploy" :: rest        => cmdDeploy rest
  | "dev-auth" :: rest      => cmdDevAuth rest
  | "stage-sdk" :: rest     => cmdStageSdk rest
  | ["test"]                => cmdTest
  | ["check"]               => cmdCheck
  | ["clean"]               => cmdClean
  | ["doctor"]              => cmdDoctor
  | ["new", dir]            => cmdNew dir
  | ["new"]                 => IO.eprintln "missing project directory: usage: qed new <dir>"; return 1
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | _                       => unknown
