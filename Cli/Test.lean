import Cli.Build

open System (FilePath)

namespace Qed.Cli

private def testSuites : Array String := #[
  "cli_scaffold_test.mjs", "dom_equivalence_test.mjs", "chat_test.mjs", "signup_test.mjs",
  "booking_test.mjs", "todo_test.mjs", "users_test.mjs", "local_test.mjs", "effects_test.mjs",
  "template_test.mjs", "ssr_test.mjs", "ssr_dynamic_test.mjs", "ssr_template_test.mjs",
  "bookshelf_test.mjs", "bookshelf_ssr_test.mjs", "socket_test.mjs", "live_test.mjs",
  "js_gate_test.mjs", "js_driver_browser_test.mjs", "svg_test.mjs"
]

def cmdTest : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  step "running tests"
  let mut ran := 0
  let mut failed := 0
  for file in testSuites do
    let path := FilePath.mk "test" / file
    if (← path.pathExists) then
      ran := ran + 1
      if (← sh "node" #[s!"test/{file}"] #[("QED_SKIP_VERIFY", some "1")]) != 0 then
        failed := failed + 1
  if failed == 0 then
    IO.println (green s!"✓ {ran}/{ran} test suites passed")
    return 0
  else
    IO.eprintln (red s!"✗ {failed}/{ran} test suite(s) failed")
    return 1

end Qed.Cli
