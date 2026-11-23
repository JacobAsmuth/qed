import Qed.Server.Core

namespace Qed.Server

/-! ## Verified Scheduled / Background Server Jobs -/

inductive DurationUnit where
  | ms | s | m | h
deriving Inhabited, DecidableEq, Repr

def durationToMs (n : Nat) : DurationUnit → Nat
  | .ms => n
  | .s  => n * 1000
  | .m  => n * 60000
  | .h  => n * 3600000

/-- Shared metadata for periodic background server jobs. -/
structure JobMeta where
  name        : String
  intervalMs  : Nat
  intervalPos : 0 < intervalMs

/-- Runtime descriptor (erasing `Inv`) for a stateful periodic server job. -/
structure ServerJob (σ : Type) extends JobMeta where
  runM : {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
           m (Except ApiError Unit)

/-- A verified periodic background server job on stateful server `σ`, carrying both
    a compile-time positive-interval proof and a kernel-checked multi-core invariant
    preservation proof (`ProgPreservesInv Inv`). -/
structure VerifiedJob (σ : Type) (Inv : σ → Prop) extends ServerJob σ where
  preserves : ProgPreservesInv Inv (runM (m := ThreadProg σ))

/-- Runtime descriptor for a stateless periodic server job. -/
structure StatelessJob extends JobMeta where
  runM : {m : Type → Type} → [Monad m] → [MonadServer m] → m (Except ApiError Unit)

def StatelessJob.toUnitJob (j : StatelessJob) : ServerJob Unit :=
  { j.toJobMeta with runM := fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @j.runM m _ _ }

/-! ### Linearizability & Composition Lemmas for Verified Jobs -/

/-- Spawning any `VerifiedJob` into a multi-core server execution is a sound `MultiCoreStep`,
    so `concurrent_schedule_preserves_inv` guarantees `Inv` across all interleavings of
    HTTP RPC requests and background jobs. -/
theorem verifiedJob_spawn_step {σ : Type} {Inv : σ → Prop}
    (j : VerifiedJob σ Inv) (s : σ) (ts : List (ThreadProg σ (Except ApiError Unit))) :
    MultiCoreStep Inv ⟨s, ts⟩ ⟨s, j.runM (m := ThreadProg σ) :: ts⟩ :=
  .spawn s ts (j.runM (m := ThreadProg σ)) j.preserves

theorem progPreservesInv_of_pureStep {σ α : Type} {Inv : σ → Prop}
    (step : σ → σ × α) (h : ∀ s, Inv s → Inv (step s).1) :
    ProgPreservesInv Inv (MonadAtomic.runAtomic (m := ThreadProg σ) step) :=
  progPreservesStepRel_runAtomic step h

theorem progPreservesInv_of_pureStepRead {σ α : Type} {Inv : σ → Prop}
    (f : σ → α) :
    ProgPreservesInv Inv (MonadAtomic.runAtomicRead (m := ThreadProg σ) f) :=
  progPreservesStepRel_runAtomicRead f (fun _ hs => hs)

theorem progPreservesInv_of_pureStepEmit {σ α : Type} {Inv : σ → Prop}
    (step : σ → σ × (α × List WsEmit)) (h : ∀ s, Inv s → Inv (step s).1) :
    ProgPreservesInv Inv
      (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= fun p =>
        flushWsEmits (m := ThreadProg σ) p.2 >>= fun _ => Pure.pure p.1) :=
  progPreservesStepRel_bind (progPreservesStepRel_runAtomic step h) fun p =>
    progPreservesStepRel_bind (ProgSpec.of_noAtomic (noAtomic_flushWsEmits p.2)) (fun _ => .pure p.1)

theorem progPreservesInv_of_pureStepReadEmit {σ α : Type} {Inv : σ → Prop}
    (f : σ → α × List WsEmit) :
    ProgPreservesInv Inv
      (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= fun p =>
        flushWsEmits (m := ThreadProg σ) p.2 >>= fun _ => Pure.pure p.1) :=
  progPreservesStepRel_bind (progPreservesStepRel_runAtomicRead f (fun _ hs => hs)) fun p =>
    progPreservesStepRel_bind (ProgSpec.of_noAtomic (noAtomic_flushWsEmits p.2)) (fun _ => .pure p.1)

theorem progPreservesInv_readEnv_default {σ α : Type} {Inv : σ → Prop}
    (osKey defVal : String) (k : String → ThreadProg σ α)
    (hk : ∀ v, ProgPreservesInv Inv (k v)) :
    ProgPreservesInv Inv
      (MonadServer.readEnv (m := ThreadProg σ) osKey >>= fun opt => k (opt.getD defVal)) :=
  safeIO_bind_preservesStepRel _ (fun opt => hk (opt.getD defVal))

theorem progPreservesInv_readEnv_required {σ α : Type} {Inv : σ → Prop}
    (osKey missingMsg : String) (k : String → ThreadProg σ (Except ApiError α))
    (hk : ∀ v, ProgPreservesInv Inv (k v)) :
    ProgPreservesInv Inv
      (MonadServer.readEnv (m := ThreadProg σ) osKey >>= fun opt =>
        match opt with
        | some v => k v
        | none   => Pure.pure (Except.error (ApiError.internal missingMsg))) :=
  safeIO_bind_preservesStepRel _ fun
    | some v => hk v
    | none   => .pure _

/-! ### Native Background Job Runner (Total, Tail-Recursive, Non-Blocking) -/

/-- Type-erased `IO` job unit executed by the native server background scheduler. -/
structure IoJob extends JobMeta where
  runOnce : IO (Except ApiError Unit)

def ServerJob.toIoJob {σ : Type} (srvInst : MonadServer IO) (atomicInst : MonadAtomic σ IO)
    (j : ServerJob σ) : IoJob :=
  { j.toJobMeta with runOnce := @j.runM IO _ srvInst atomicInst }

def StatelessJob.toIoJob (srvInst : MonadServer IO) (j : StatelessJob) : IoJob :=
  { j.toJobMeta with runOnce := @j.runM IO _ srvInst }

/-- Default tick budget for background server jobs (1 trillion ticks ≈ 31.7 years at 1ms). -/
def defaultMaxJobTicks : Nat := 1000000000000

/-- Total, tail-recursive periodic job loop (compiles to O(1) stack with zero `partial`/`while`).
    Stops early if `stopFlag?` becomes `true`. -/
def runJobLoop (name : String) (intervalMs : UInt32)
    (runOnce : IO (Except ApiError Unit))
    (stopFlag? : Option (IO.Ref Bool) := none) : Nat → IO Unit
  | 0 => pure ()
  | fuel + 1 => do
      if let some flag := stopFlag? then
        if ← flag.get then return ()
      IO.sleep intervalMs
      if let some flag := stopFlag? then
        if ← flag.get then return ()
      match ← runOnce with
      | .ok ()  => pure ()
      | .error e => IO.eprintln s!"[qed job `{name}`] error: {e.message}"
      runJobLoop name intervalMs runOnce stopFlag? fuel

/-- Spawns all registered periodic server jobs on dedicated background tasks without
    blocking HTTP/RPC worker threads. -/
def spawnServerJobs (jobs : Array IoJob)
    (stopFlag? : Option (IO.Ref Bool) := none)
    (maxTicks : Nat := defaultMaxJobTicks) :
    IO (Array (Task (Except IO.Error Unit))) := do
  jobs.mapM fun job => do
    let delayMs : UInt32 := (min job.intervalMs 2147483647).toUInt32
    IO.asTask (prio := .dedicated) (runJobLoop job.name delayMs job.runOnce stopFlag? maxTicks)

/-- Convenience alias for `spawnServerJobs`. -/
abbrev runServerJobs := @spawnServerJobs

end Qed.Server
