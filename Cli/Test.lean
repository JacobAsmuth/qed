import Cli.Build

namespace Qed.Cli

def cmdTest : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  step "running tests"
  let some lp ← lakeEnvLeanPath | return 1
  sh "node" #["test/harness.mjs"] #[
    ("QED_SKIP_VERIFY", some "1"),
    ("QED_PREBUILT", some "1"),
    ("LEAN_PATH", some lp)
  ]

end Qed.Cli
