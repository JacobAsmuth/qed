import Cli.Verify

open System (FilePath)

namespace Qed.Cli

def cmdTest : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  step "building native test runner"
  if (← shLakeBuild #["build", "qedtest"]) != 0 then
    IO.eprintln (red "✗ failed to build native test runner")
    return 1
  step "running tests"
  let some lp ← lakeEnvLeanPath | return 1
  sh ((FilePath.mk ".lake" / "build" / "bin" / "qedtest").toString) #[] #[
    ("QED_SKIP_VERIFY", some "1"),
    ("QED_PREBUILT", some "1"),
    ("LEAN_PATH", some lp)
  ]

end Qed.Cli
