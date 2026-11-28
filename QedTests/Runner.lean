import Std.Sync.Mutex
import QedTests.Native.CliScaffold
import QedTests.Native.Database
import QedTests.Native.FullstackRpc
import QedTests.Native.WebSocket
import QedTests.Native.VerificationAndJobs
import QedTests.Native.AuthAndDeploy
import QedTests.Native.CloudDeploy

def main (args : List String) : IO UInt32 := do
  -- Longest-first order so bounded worker pools start heavy suites immediately.
  let allSuites : Array (String × IO Bool) := #[
    ("cli-scaffold", QedTests.Native.CliScaffold.run),
    ("database", QedTests.Native.Database.run),
    ("cloud-deploy", QedTests.Native.CloudDeploy.run),
    ("fullstack-rpc", QedTests.Native.FullstackRpc.run),
    ("websockets", QedTests.Native.WebSocket.run),
    ("auth-and-deploy", QedTests.Native.AuthAndDeploy.run),
    ("verification-and-jobs", QedTests.Native.VerificationAndJobs.run)]
  let suites := if args.isEmpty then allSuites else allSuites.filter fun (nm, _) => args.contains nm
  let defaultJobs := if System.Platform.isOSX then 2 else 4
  let envJobs := ((← IO.getEnv "QED_TEST_JOBS").bind String.toNat?).getD defaultJobs
  let nWorkers := max 1 (min (max 1 envJobs) suites.size)
  let nextIdx ← Std.Mutex.new (0 : Nat)
  let failedCnt ← Std.Mutex.new (0 : Nat)
  let rec workerLoop : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
        let idx ← nextIdx.atomically do
          let i ← get; set (i + 1); pure i
        if h : idx < suites.size then
          let (name, fn) := suites[idx]
          try
            if !(← fn) then failedCnt.atomically (modify (· + 1))
          catch e =>
            IO.eprintln s!"  ✗ {name}: exception: {e}"
            (← IO.getStderr).flush
            failedCnt.atomically (modify (· + 1))
          workerLoop fuel
  let workers ← (Array.range nWorkers).mapM fun _ =>
    IO.asTask (prio := .dedicated) (workerLoop suites.size)
  for w in workers do
    if let .error e ← IO.wait w then
      IO.eprintln s!"  ✗ worker exception: {e}"; (← IO.getStderr).flush
      failedCnt.atomically (modify (· + 1))
  let failed ← failedCnt.atomically get
  if failed == 0 then
    IO.println s!"\x1b[32m✓ {suites.size}/{suites.size} test suites passed\x1b[0m"
    (← IO.getStdout).flush
    return 0
  IO.eprintln s!"\x1b[31m✗ {failed}/{suites.size} test suite(s) failed\x1b[0m"
  (← IO.getStderr).flush
  return 1
