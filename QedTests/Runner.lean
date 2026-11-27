import QedTests.Native.CliScaffold
import QedTests.Native.Database
import QedTests.Native.FullstackRpc
import QedTests.Native.WebSocket
import QedTests.Native.VerificationAndJobs
import QedTests.Native.AuthAndDeploy
import QedTests.Native.CloudDeploy

def main (args : List String) : IO UInt32 := do
  let allSuites : Array (String × IO Bool) := #[
    ("cli-scaffold", QedTests.Native.CliScaffold.run), ("fullstack-rpc", QedTests.Native.FullstackRpc.run),
    ("database", QedTests.Native.Database.run), ("websockets", QedTests.Native.WebSocket.run),
    ("verification-and-jobs", QedTests.Native.VerificationAndJobs.run),
    ("auth-and-deploy", QedTests.Native.AuthAndDeploy.run), ("cloud-deploy", QedTests.Native.CloudDeploy.run)]
  let suites := if args.isEmpty then allSuites else allSuites.filter fun (nm, _) => args.contains nm
  let tasks ← suites.mapM fun (name, fn) => return (name, ← IO.asTask (prio := .dedicated) fn)
  let mut failed := 0
  for (name, t) in tasks do
    match ← IO.wait t with
    | .ok true  => pure ()
    | .ok false => failed := failed + 1
    | .error e  => IO.eprintln s!"  ✗ {name}: exception: {e}"; failed := failed + 1
  if failed == 0 then IO.println s!"\x1b[32m✓ {suites.size}/{suites.size} test suites passed\x1b[0m"; return 0
  IO.eprintln s!"\x1b[31m✗ {failed}/{suites.size} test suite(s) failed\x1b[0m"; return 1
