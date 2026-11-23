import Tests.Native.CliScaffold
import Tests.Native.Database
import Tests.Native.FullstackRpc
import Tests.Native.WebSocket
import Tests.Native.VerificationAndJobs
import Tests.Native.AuthAndDeploy

def main : IO UInt32 := do
  let suites : Array (String × IO Bool) := #[
    ("cli-scaffold",          Tests.Native.CliScaffold.run),
    ("fullstack-rpc",         Tests.Native.FullstackRpc.run),
    ("database",              Tests.Native.Database.run),
    ("websockets",            Tests.Native.WebSocket.run),
    ("verification-and-jobs", Tests.Native.VerificationAndJobs.run),
    ("auth-and-deploy",       Tests.Native.AuthAndDeploy.run)
  ]
  -- Run all independent native suites concurrently.
  let tasks ← suites.mapM fun (name, fn) => return (name, ← IO.asTask (prio := .dedicated) fn)
  let mut failed := 0
  for (name, t) in tasks do
    match ← IO.wait t with
    | .ok true  => pure ()
    | .ok false => failed := failed + 1
    | .error e  => IO.eprintln s!"  ✗ {name}: exception: {e}"; failed := failed + 1
  if failed == 0 then
    IO.println s!"\x1b[32m✓ {suites.size}/{suites.size} test suites passed\x1b[0m"; return 0
  IO.eprintln s!"\x1b[31m✗ {failed}/{suites.size} test suite(s) failed\x1b[0m"; return 1
