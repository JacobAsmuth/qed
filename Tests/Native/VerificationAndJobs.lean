import Qed
import Qed.Server.Native
import Tests.Native.Harness

open Qed
open Qed.Server

namespace Tests.Native.VerificationAndJobs

server JobRunnerDemo:
  state ticks : Nat = 0
  state resets : Nat = 0

  invariant bounded: ticks <= 50
  invariant mono: resets >= old(resets)

  def getTicks() -> Nat:
    return ticks

  every 15ms heartbeat:
    if ticks < 50:
      ticks += 1

  every 40ms markReset:
    atomic:
      resets += 1

def run : IO Bool := do
  let c ← mkChecker "verification-and-jobs"

  -- 1. Base64 round-trip across empty, 1/2/3-byte, all 256 byte values, and 64 KiB binary buffer
  let empty := ByteArray.empty
  c.checkEq "base64 empty encode" (Base64.encode empty) ""
  c.checkEq "base64 empty decode" (Base64.decode "") (.ok empty)

  for n in [1, 2, 3, 4, 5, 17, 256] do
    let bs := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i % 256))
    let enc := Base64.encode bs
    c.checkEq s!"base64 round-trip ({n} bytes)" (Base64.decode enc) (.ok bs)

  let big := ByteArray.mk ((List.range 65536).toArray.map fun i => UInt8.ofNat ((i * 37 + 13) % 256))
  let bigEnc := Base64.encode big
  c.check "base64 64KiB encoded length" (bigEnc.length == ((65536 + 2) / 3) * 4)
  c.checkEq "base64 64KiB round-trip" (Base64.decode bigEnc) (.ok big)

  c.check "base64 rejects invalid length" (match Base64.decode "abc" with | .error _ => true | .ok _ => false)
  c.check "base64 rejects invalid char" (match Base64.decode "ab!d" with | .error _ => true | .ok _ => false)

  -- 2. FileBytes JSON + Base64 decoding
  let sampleBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0xFF]
  let sampleJson := Json.render (.obj [
    ("name", .str "icon.png"),
    ("mime", .str "image/png"),
    ("size", .num ⟨10, 0⟩),
    ("base64", .str (Base64.encode sampleBytes))
  ])
  c.expectOk "FileBytes.decode ok" (FileBytes.decode sampleJson) fun fb => do
    c.checkEq "FileBytes.name" fb.name "icon.png"
    c.checkEq "FileBytes.mime" fb.mime "image/png"
    c.checkEq "FileBytes.size" fb.size 10
    c.checkEq "FileBytes.bytes" fb.bytes sampleBytes

  c.check "FileBytes.decode propagates host error"
    (match FileBytes.decode "{\"error\":\"file too large (200 bytes; max 100)\"}" with
     | .error msg => msg.contains "file too large"
     | .ok _ => false)

  -- 3. Verified background server jobs execution on Prim.StateBox via `runServerJobs`
  let box ← Prim.mkStateBox JobRunnerDemo.initState
  let srvInst : MonadServer IO := Qed.Server.Native.mkNativeServerInst none
  let atomicInst : MonadAtomic JobRunnerDemo.State IO := Qed.Server.Native.withStateBox box
  let ioJobs := JobRunnerDemo.jobs.map (·.toIoJob srvInst atomicInst)
  c.checkEq "JobRunnerDemo job count" ioJobs.size 2

  let stopFlag ← IO.mkRef false
  let tasks ← Qed.Server.runServerJobs ioJobs (stopFlag? := some stopFlag) (maxTicks := 5)
  -- Wait for bounded job tasks (5 ticks at 15ms and 40ms ≈ 200ms)
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => c.check "job task exited cleanly" false (toString e)

  let finalState ← Prim.atomicRead box id
  c.checkEq "heartbeat job ran 5 ticks" finalState.ticks 5
  c.checkEq "markReset atomic job ran 5 ticks" finalState.resets 5
  c.check "final state preserves bounded invariant" (finalState.ticks ≤ 50)

  -- 4. Stop flag halts long-running background job early
  let box2 ← Prim.mkStateBox JobRunnerDemo.initState
  let atomicInst2 : MonadAtomic JobRunnerDemo.State IO := Qed.Server.Native.withStateBox box2
  let ioJobs2 := JobRunnerDemo.jobs.map (·.toIoJob srvInst atomicInst2)
  let stopFlag2 ← IO.mkRef false
  let tasks2 ← Qed.Server.spawnServerJobs ioJobs2 (stopFlag? := some stopFlag2) (maxTicks := 1000)
  IO.sleep 60
  stopFlag2.set true
  for t in tasks2 do
    discard <| IO.wait t
  let stoppedState ← Prim.atomicRead box2 id
  c.check "background job ticked before stopFlag" (stoppedState.ticks ≥ 1 && stoppedState.ticks < 50)

  c.finish

end Tests.Native.VerificationAndJobs
