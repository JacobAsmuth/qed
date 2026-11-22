import Qed.Runtime.AppCore

namespace Qed

/-! ## Lawful Structural Equality (`SpecEq`) Supporting `DecidableEq` & `LawfulBEq` -/

/-- Sound equality check for comparing a server's actual response against a client's prediction.
    The `eq_of_true` law guarantees that a prediction hit (`eq actual pred = true`) implies
    true mathematical equality `actual = pred`, ruling out silent missed rollbacks from buggy `BEq` instances. -/
class SpecEq (α : Type) where
  eq : α → α → Bool
  eq_of_true : ∀ {a b : α}, eq a b = true → a = b
  eq_refl : ∀ (a : α), eq a a = true

@[inline] instance {α : Type} [DecidableEq α] : SpecEq α where
  eq a b := decide (a = b)
  eq_of_true h := of_decide_eq_true h
  eq_refl _ := decide_eq_true rfl

@[inline] instance (priority := low) {α : Type} [BEq α] [LawfulBEq α] : SpecEq α where
  eq a b := a == b
  eq_of_true h := eq_of_beq h
  eq_refl a := beq_self_eq_true a

/-! ## Client-Side Prediction & Transactional Rollback (`SpecEntry`, `SpecState`, `SpecEngine`) -/

/-- An entry in the client's ephemeral speculative journal while one or more predicted RPCs are in flight. -/
inductive SpecEntry (Msg : Type) where
  | regular  (msg : Msg)
  | pending  (txId : Nat) (msg : Msg)
  | resolved (msg : Msg)

/-- Wrapper model separating the immediately rendered `visible` state from the `confirmed` base state.
    When `log` is empty (no predictions in flight), `visible = confirmed` with zero replay overhead. -/
structure SpecState (State Msg : Type) where
  visible   : State
  confirmed : State
  nextTxId  : Nat := 0
  log       : List (SpecEntry Msg) := []

namespace SpecState

@[inline] def pure {State Msg : Type} (s : State) : SpecState State Msg :=
  { visible := s, confirmed := s, nextTxId := 0, log := [] }

@[simp] theorem pure_visible {State Msg : Type} (s : State) :
    (SpecState.pure (Msg := Msg) s).visible = s := rfl

@[simp] theorem pure_confirmed {State Msg : Type} (s : State) :
    (SpecState.pure (Msg := Msg) s).confirmed = s := rfl

@[simp] theorem pure_log {State Msg : Type} (s : State) :
    (SpecState.pure (Msg := Msg) s).log = [] := rfl

end SpecState

/-- Classification of an incoming `Msg` for speculative execution. -/
inductive SpecAction (Msg : Type) where
  | normal
  | dispatch (preMsg? : Option Msg) (preCmd : Cmd Msg) (specMsg : Msg) (rpcCmd : Nat → Cmd Msg)
  | resolve (txId : Nat) (hit : Bool) (replMsgs : List Msg) (confirmOnHit : List Msg)

namespace SpecEngine

@[inline] def entryMsg {Msg : Type} : SpecEntry Msg → Msg
  | .regular m | .pending _ m | .resolved m => m

@[inline] def replayEntry {State Msg : Type} (step : State → Msg → State) (s : State)
    (e : SpecEntry Msg) : State :=
  step s (entryMsg e)

/-- Advances `confirmed` past all leading `.regular` and `.resolved` entries until the first `.pending` entry. -/
def drainConfirmed {State Msg : Type} (step : State → Msg → State)
    (conf : State) : List (SpecEntry Msg) → State × List (SpecEntry Msg)
  | .regular m :: rest  => drainConfirmed step (step conf m) rest
  | .resolved m :: rest => drainConfirmed step (step conf m) rest
  | rest                => (conf, rest)

/-- Runs a list of messages sequentially, collecting their emitted commands once. -/
def runMsgs {State Msg : Type} (upd : State → Msg → State × Cmd Msg)
    (s : State) : List Msg → State × List (Cmd Msg)
  | []      => (s, [])
  | m :: ms =>
      let (s1, c1) := upd s m
      let (s2, cs) := runMsgs upd s1 ms
      (s2, c1 :: cs)

/-- Replaces `.pending txId _` in `log` with `replMsgs.map .resolved`, running `replMsgs`
    at `txId`'s chronological state `sCur` to collect their one-shot commands. -/
def replacePending {State Msg : Type} (upd : State → Msg → State × Cmd Msg)
    (txId : Nat) (replMsgs : List Msg) (sCur : State) :
    List (SpecEntry Msg) → List (SpecEntry Msg) × List (Cmd Msg) × Bool
  | [] => ([], [], false)
  | .pending id m :: rest =>
      if id == txId then
        let (_, cmds) := runMsgs upd sCur replMsgs
        (replMsgs.map SpecEntry.resolved ++ rest, cmds, true)
      else
        let (rest', cmds, found) := replacePending upd txId replMsgs (upd sCur m).1 rest
        (.pending id m :: rest', cmds, found)
  | e :: rest =>
      let (rest', cmds, found) :=
        replacePending upd txId replMsgs (replayEntry (fun s m => (upd s m).1) sCur e) rest
      (e :: rest', cmds, found)

def mkBatchCmd {Msg : Type} : List (Cmd Msg) → Cmd Msg
  | []  => .none
  | [c] => c
  | cs  => .batch cs

def resolveReplace {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (txId : Nat) (replMsgs : List Msg) (st : SpecState State Msg) :
    SpecState State Msg × Cmd Msg :=
  let stepOnly := fun s m => (upd s m).1
  let (newLog, cmds, found) := replacePending upd txId replMsgs st.confirmed st.log
  if !found then (st, .none)
  else
    let (conf', log') := drainConfirmed stepOnly st.confirmed newLog
    let vis' := log'.foldl (replayEntry stepOnly) conf'
    ({ st with visible := vis', confirmed := conf', log := log' }, mkBatchCmd cmds)

@[inline] def appendNonPending {State Msg : Type} (st : SpecState State Msg)
    (vis' : State) (entry : SpecEntry Msg) : SpecState State Msg :=
  if st.log.isEmpty then { st with visible := vis', confirmed := vis', log := [] }
  else { st with visible := vis', log := st.log ++ [entry] }

@[inline] def appendPending {State Msg : Type} (stepOnly : State → Msg → State)
    (st : SpecState State Msg) (specMsg : Msg) : SpecState State Msg :=
  { visible := stepOnly st.visible specMsg, confirmed := st.confirmed,
    nextTxId := st.nextTxId + 1, log := st.log ++ [SpecEntry.pending st.nextTxId specMsg] }

@[inline] def resolveHeadHit {State Msg : Type} (upd : State → Msg → State × Cmd Msg)
    (st : SpecState State Msg) (m0 : Msg) (tail : List (SpecEntry Msg))
    (confirmOnHit : List Msg) : SpecState State Msg × Cmd Msg :=
  let stepOnly := fun s m => (upd s m).1
  let conf1 := stepOnly st.confirmed m0
  if confirmOnHit.isEmpty then
    let (conf2, log2) := drainConfirmed stepOnly conf1 tail
    ({ st with confirmed := conf2, log := log2 }, .none)
  else
    let (conf2, cmds) := runMsgs upd conf1 confirmOnHit
    let (conf3, log3) := drainConfirmed stepOnly conf2 tail
    ({ st with visible := log3.foldl (replayEntry stepOnly) conf3, confirmed := conf3, log := log3 }, mkBatchCmd cmds)

/-- Single step of the speculative state machine wrapping `upd : State → Msg → State × Cmd Msg`. -/
def step {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg) : SpecState State Msg × Cmd Msg :=
  let stepOnly := fun s m => (upd s m).1
  match classify st.visible msg with
  | .normal =>
      let (vis', cmd) := upd st.visible msg
      (appendNonPending st vis' (.regular msg), cmd)
  | .dispatch preMsg? preCmd specMsg rpcCmd =>
      let (st1, cPre) :=
        match preMsg? with
        | none => (st, preCmd)
        | some pm =>
            let (v1, c1) := upd st.visible pm
            (appendNonPending st v1 (.resolved pm), Cmd.batch [preCmd, c1])
      (appendPending stepOnly st1 specMsg, Cmd.batch [cPre, rpcCmd st.nextTxId])
  | .resolve txId hit replMsgs confirmOnHit =>
      match st.log with
      | .pending id0 m0 :: tail =>
          if hit && id0 == txId then resolveHeadHit upd st m0 tail confirmOnHit
          else resolveReplace upd txId replMsgs st
      | _ => resolveReplace upd txId replMsgs st

end SpecEngine

namespace Internal

/-- Wraps a verified `App State Msg` with client-side prediction and transactional rollback. -/
def App.withSpeculative {State Msg : Type}
    (classify : State → Msg → SpecAction Msg)
    (app : App State Msg) : App (SpecState State Msg) Msg :=
  App.liftModel SpecState.pure SpecState.visible (fun _ => rfl)
    (SpecEngine.step app.update classify) app

end Internal

end Qed
