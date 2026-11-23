import Qed
import Qed.Server.Native
import Tests.Native.Harness
open Qed Qed.Server

namespace Tests.Native.VerificationAndJobs
server JobRunnerDemo:
  state ticks  : Nat = 0
  state resets : Nat = 0
  invariant bounded: ticks <= 50
  invariant mono: resets >= old(resets)
  def getTicks() -> Nat: return ticks
  every 15ms heartbeat: if ticks < 50: ticks += 1
  every 40ms markReset: atomic: resets += 1

def run : IO Bool := do
  let c ← mkChecker "verification-and-jobs"
  c.checkEq "base64 empty encode" (Base64.encode ByteArray.empty) ""; c.checkEq "base64 empty decode" (Base64.decode "") (.ok ByteArray.empty)
  for n in [1, 2, 3, 256] do
    let bs := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i % 256))
    c.checkEq s!"base64 round-trip ({n} bytes)" (Base64.decode (Base64.encode bs)) (.ok bs)
  let big := ByteArray.mk ((List.range 65536).toArray.map fun i => UInt8.ofNat ((i * 37 + 13) % 256)); let bigEnc := Base64.encode big
  c.check "base64 64KiB encoded length" (bigEnc.length == ((65536 + 2) / 3) * 4); c.checkEq "base64 64KiB round-trip" (Base64.decode bigEnc) (.ok big)
  for (lbl, bad) in [("invalid length", "abc"), ("invalid char", "ab!d")] do c.check s!"base64 rejects {lbl}" (!(Base64.decode bad).isOk)
  let sampleBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0xFF]
  c.expectOk "FileBytes.decode ok" (FileBytes.decode (Json.render (.obj [("name", .str "icon.png"), ("mime", .str "image/png"), ("size", .num ⟨10, 0⟩), ("base64", .str (Base64.encode sampleBytes))]))) fun fb =>
    c.checkEq "FileBytes fields match" (fb.name, fb.mime, fb.size, fb.bytes) ("icon.png", "image/png", 10, sampleBytes)
  c.checkErrContains "FileBytes.decode propagates host error" (FileBytes.decode "{\"error\":\"file too large (200 bytes; max 100)\"}") "file too large"
  let srvInst : MonadServer IO := Qed.Server.Native.mkNativeServerInst none
  let mkJobs := do let box ← Prim.mkStateBox JobRunnerDemo.initState; return (box, JobRunnerDemo.jobs.map (·.toIoJob srvInst (Qed.Server.Native.withStateBox box)), ← IO.mkRef false)
  let (box, ioJobs, stopFlag) ← mkJobs; c.checkEq "JobRunnerDemo job count" ioJobs.size 2
  for t in ← Qed.Server.runServerJobs ioJobs (stopFlag? := some stopFlag) (maxTicks := 5) do if let .error e ← IO.wait t then c.check "job task exited cleanly" false (toString e)
  let st1 ← Prim.atomicRead box id; c.checkEq "heartbeat & markReset ran 5 ticks" (st1.ticks, st1.resets) (5, 5); c.check "final state preserves bounded invariant" (st1.ticks ≤ 50)
  let (box2, ioJobs2, stopFlag2) ← mkJobs; let tasks2 ← Qed.Server.spawnServerJobs ioJobs2 (stopFlag? := some stopFlag2) (maxTicks := 1000)
  IO.sleep 60; stopFlag2.set true; for t in tasks2 do discard <| IO.wait t
  let st2 ← Prim.atomicRead box2 id; c.check "background job ticked before stopFlag" (st2.ticks ≥ 1 && st2.ticks < 50)
  c.finish

end Tests.Native.VerificationAndJobs
