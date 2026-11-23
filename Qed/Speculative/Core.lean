import Qed.Runtime.AppCore

namespace Qed

class SpecEq (α : Type) where
  eq : α → α → Bool
  eq_of_true : ∀ {a b : α}, eq a b = true → a = b
  eq_refl : ∀ (a : α), eq a a = true

@[inline] instance {α : Type} [DecidableEq α] : SpecEq α := ⟨fun a b => decide (a = b), of_decide_eq_true, fun _ => decide_eq_true rfl⟩
@[inline] instance (priority := low) {α : Type} [BEq α] [LawfulBEq α] : SpecEq α := ⟨(· == ·), eq_of_beq, beq_self_eq_true⟩

inductive SpecEntry (Msg : Type) where
  | regular (msg : Msg) | pending (txId : Nat) (msg : Msg) | resolved (msg : Msg)

structure SpecState (State Msg : Type) where
  visible   : State
  confirmed : State
  nextTxId  : Nat := 0
  log       : List (SpecEntry Msg) := []

namespace SpecState
@[inline] def pure {State Msg : Type} (s : State) : SpecState State Msg := ⟨s, s, 0, []⟩
@[simp] theorem pure_visible {State Msg : Type} (s : State) : (SpecState.pure (Msg := Msg) s).visible = s := rfl
@[simp] theorem pure_confirmed {State Msg : Type} (s : State) : (SpecState.pure (Msg := Msg) s).confirmed = s := rfl
@[simp] theorem pure_log {State Msg : Type} (s : State) : (SpecState.pure (Msg := Msg) s).log = [] := rfl
end SpecState

inductive SpecAction (Msg : Type) where
  | normal
  | dispatch (preMsg? : Option Msg) (preCmd : Cmd Msg) (specMsg : Msg) (rpcCmd : Nat → Cmd Msg)
  | resolve (txId : Nat) (hit : Bool) (replMsgs : List Msg) (confirmOnHit : List Msg)

namespace SpecEngine
section
variable {State Msg : Type}

@[inline] def entryMsg : SpecEntry Msg → Msg | .regular m | .pending _ m | .resolved m => m
@[inline] def replayEntry (step : State → Msg → State) (s : State) (e : SpecEntry Msg) : State := step s (entryMsg e)

def drainConfirmed (step : State → Msg → State) (conf : State) : List (SpecEntry Msg) → State × List (SpecEntry Msg)
  | .regular m :: rest | .resolved m :: rest => drainConfirmed step (step conf m) rest
  | rest => (conf, rest)

def runMsgs (upd : State → Msg → State × Cmd Msg) (s : State) : List Msg → State × List (Cmd Msg)
  | [] => (s, [])
  | m :: ms => let (s1, c1) := upd s m; let (s2, cs) := runMsgs upd s1 ms; (s2, c1 :: cs)

def replacePending (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) (sCur : State) :
    List (SpecEntry Msg) → List (SpecEntry Msg) × List (Cmd Msg) × Bool
  | [] => ([], [], false)
  | .pending id m :: rest =>
      if id == txId then (replMsgs.map SpecEntry.resolved ++ rest, (runMsgs upd sCur replMsgs).2, true)
      else let (r', cs, ok) := replacePending upd txId replMsgs (upd sCur m).1 rest; (.pending id m :: r', cs, ok)
  | e :: rest =>
      let (r', cs, ok) := replacePending upd txId replMsgs (replayEntry (fun s m => (upd s m).1) sCur e) rest
      (e :: r', cs, ok)

def mkBatchCmd : List (Cmd Msg) → Cmd Msg | [] => .none | [c] => c | cs => .batch cs

def resolveReplace (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) (st : SpecState State Msg) :
    SpecState State Msg × Cmd Msg :=
  let stepOnly := fun s m => (upd s m).1
  let (newLog, cmds, found) := replacePending upd txId replMsgs st.confirmed st.log
  if !found then (st, .none)
  else
    let (conf', log') := drainConfirmed stepOnly st.confirmed newLog
    ({ st with visible := log'.foldl (replayEntry stepOnly) conf', confirmed := conf', log := log' }, mkBatchCmd cmds)

@[inline] def appendNonPending (st : SpecState State Msg) (vis' : State) (entry : SpecEntry Msg) : SpecState State Msg :=
  if st.log.isEmpty then { st with visible := vis', confirmed := vis', log := [] }
  else { st with visible := vis', log := st.log ++ [entry] }

@[inline] def appendPending (stepOnly : State → Msg → State) (st : SpecState State Msg) (specMsg : Msg) : SpecState State Msg :=
  ⟨stepOnly st.visible specMsg, st.confirmed, st.nextTxId + 1, st.log ++ [.pending st.nextTxId specMsg]⟩

@[inline] def resolveHeadHit (upd : State → Msg → State × Cmd Msg) (st : SpecState State Msg) (m0 : Msg)
    (tail : List (SpecEntry Msg)) (confirmOnHit : List Msg) : SpecState State Msg × Cmd Msg :=
  let stepOnly := fun s m => (upd s m).1; let conf1 := stepOnly st.confirmed m0
  if confirmOnHit.isEmpty then
    let (conf2, log2) := drainConfirmed stepOnly conf1 tail
    ({ st with confirmed := conf2, log := log2 }, .none)
  else
    let (conf2, cmds) := runMsgs upd conf1 confirmOnHit
    let (conf3, log3) := drainConfirmed stepOnly conf2 tail
    ({ st with visible := log3.foldl (replayEntry stepOnly) conf3, confirmed := conf3, log := log3 }, mkBatchCmd cmds)

def step (upd : State → Msg → State × Cmd Msg) (classify : State → Msg → SpecAction Msg) (st : SpecState State Msg) (msg : Msg) :
    SpecState State Msg × Cmd Msg :=
  match classify st.visible msg with
  | .normal => let (vis', cmd) := upd st.visible msg; (appendNonPending st vis' (.regular msg), cmd)
  | .dispatch preMsg? preCmd specMsg rpcCmd =>
      let (st1, cPre) := match preMsg? with
        | none => (st, preCmd)
        | some pm => let (v1, c1) := upd st.visible pm; (appendNonPending st v1 (.resolved pm), .batch [preCmd, c1])
      (appendPending (fun s m => (upd s m).1) st1 specMsg, .batch [cPre, rpcCmd st.nextTxId])
  | .resolve txId hit replMsgs confirmOnHit =>
      match st.log with
      | .pending id0 m0 :: tail => if hit && id0 == txId then resolveHeadHit upd st m0 tail confirmOnHit else resolveReplace upd txId replMsgs st
      | _ => resolveReplace upd txId replMsgs st

end
end SpecEngine

namespace Internal
def App.withSpeculative {State Msg : Type} (classify : State → Msg → SpecAction Msg) (app : App State Msg) : App (SpecState State Msg) Msg :=
  App.liftModel SpecState.pure SpecState.visible (fun _ => rfl) (SpecEngine.step app.update classify) app
end Internal

end Qed
