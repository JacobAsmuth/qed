import Qed.Verify.Core
import Qed.Runtime.Cmd

namespace Qed
section
variable {State Msg Out : Type} [InvTarget Out State]

class InvOut (Out : Type) (Ev : outParam Type) where projOut : Out → Option Ev
instance {S E : Type} : InvOut (S × Option E) E := ⟨Prod.snd⟩
instance {S E C : Type} : InvOut (S × Option E × C) E := ⟨fun r => r.2.1⟩
class InvCmd (Out : Type) (Msg : outParam Type) where projCmd : Out → Cmd Msg
instance {S M : Type} : InvCmd (S × Cmd M) M := ⟨Prod.snd⟩
instance {S E M : Type} : InvCmd (S × Option E × Cmd M) M := ⟨fun r => r.2.2⟩

def optSat {α : Type} (o : Option α) (P : α → Prop) : Prop := match o with | some a => P a | none => False
instance {α : Type} (o : Option α) (P : α → Prop) [∀ a, Decidable (P a)] : Decidable (optSat o P) :=
  match o with | some a => inferInstanceAs (Decidable (P a)) | none => isFalse id

def runTrace (update : State → Msg → Out) : State → List Msg → State
  | s, [] => s | s, m :: ms => runTrace update (InvTarget.proj (update s m)) ms
@[simp] theorem runTrace_nil (update : State → Msg → Out) (s : State) : runTrace update s [] = s := rfl
@[simp] theorem runTrace_cons (update : State → Msg → Out) (s : State) (m : Msg) (ms : List Msg) :
    runTrace update s (m :: ms) = runTrace update (InvTarget.proj (update s m)) ms := rfl

def runTraceEmits {Ev : Type} [InvOut Out Ev] (update : State → Msg → Out) : State → List Msg → State × List Ev
  | s, [] => (s, [])
  | s, m :: ms => let r := update s m; let (s', es) := runTraceEmits update (InvTarget.proj r) ms; (s', match InvOut.projOut r with | some e => e :: es | none => es)

inductive TraceStep (Msg : Type) where
  | msg (m : Msg) | rpcReply (urlSuffix : String) (resp : Except String ByteArray)

private def extractPendingRpc {M : Type} (c : Cmd M) : List (String × (Except String ByteArray → M)) :=
  (Cmd.flatten c).filterMap fun | .requestBytes _ url _ cb => some (url, cb) | _ => none

private def popMatchingRpc {M : Type} (sfx : String) :
    List (String × (Except String ByteArray → M)) → Option ((Except String ByteArray → M) × List (String × (Except String ByteArray → M)))
  | [] => none
  | (u, cb) :: rest => if Qed.Str.endsWith u sfx then some (cb, rest) else (popMatchingRpc sfx rest).map fun (f, r') => (f, (u, cb) :: r')

private def runTraceAsyncCore {Ev : Type} [InvCmd Out Msg] (getOut : Out → Option Ev) (update : State → Msg → Out)
    (s : State) (outs : List Ev) (pending : List (String × (Except String ByteArray → Msg))) :
    List (TraceStep Msg) → Option (State × List Ev)
  | [] => some (s, outs.reverse)
  | step :: rest =>
      let advance (m : Msg) (p' : List (String × (Except String ByteArray → Msg))) :=
        let r := update s m; let outs' := match getOut r with | some o => o :: outs | none => outs
        runTraceAsyncCore getOut update (InvTarget.proj r) outs' (p' ++ extractPendingRpc (InvCmd.projCmd r)) rest
      match step with
      | .msg m => advance m pending
      | .rpcReply sfx resp => match popMatchingRpc sfx pending with | none => none | some (cb, p') => advance (cb resp) p'

def runTraceAsync [InvCmd Out Msg] (update : State → Msg → Out) (init : State) (steps : List (TraceStep Msg)) : Option State :=
  (runTraceAsyncCore (Ev := Unit) (fun _ => none) update init [] [] steps).map Prod.fst
def runTraceAsyncEmits {Ev : Type} [InvOut Out Ev] [InvCmd Out Msg] (update : State → Msg → Out) (init : State) (steps : List (TraceStep Msg)) : Option (State × List Ev) :=
  runTraceAsyncCore InvOut.projOut update init [] [] steps

def Reachable (update : State → Msg → Out) (init : State) (target : State → Prop) : Prop := ∃ trace : List Msg, target (runTrace update init trace)
theorem reachable_of_trace (update : State → Msg → Out) (init : State) (target : State → Prop) (trace : List Msg) (h : target (runTrace update init trace)) : Reachable update init target := ⟨trace, h⟩
theorem inv_holds_on_runTrace {update : State → Msg → Out} {init : State} {Inv : State → Prop}
    (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) : ∀ trace, Inv (runTrace update init trace)
  | [] => hinit | m :: ms => inv_holds_on_runTrace (hstep init m hinit) hstep ms
theorem inv_nonvacuous_of_reachable {update : State → Msg → Out} {init : State} {Inv target : State → Prop}
    (hreach : Reachable update init target) (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) :
    ∃ s, Inv s ∧ target s := let ⟨tr, ht⟩ := hreach; ⟨runTrace update init tr, inv_holds_on_runTrace hinit hstep tr, ht⟩
end

private def reachBaseSimpNames : Array Lean.Name :=
  #[``Qed.runTrace, ``Qed.runTrace_nil, ``Qed.runTrace_cons, ``Qed.runTraceEmits, ``Qed.optSat,
    ``Qed.InvTarget.proj_id, ``Qed.InvTarget.proj_fst, ``Qed.InvOut.projOut, ``Qed.InvCmd.projCmd,
    ``Qed.Lang.QedVal.val_id] ++ Qed.Verify.Core.dictSimpNames
private def reachBoolSimpNames : Array Lean.Name := Qed.Verify.Core.boolSimpNames ++ #[``decide_eq_false_iff_not]

private partial def extractHeadIdent? (stx : Lean.Syntax) : Option Lean.Syntax :=
  if stx.isIdent then some stx
  else if stx.getKind == ``Lean.Parser.Term.paren then extractHeadIdent? (stx.getArg 1)
  else if stx.getKind == ``Lean.Parser.Term.app then extractHeadIdent? (stx.getArg 0)
  else none

section ReachabilityTactic
open Lean Meta Elab Tactic Qed.Verify.Core

@[noinline] private def runReachPass (allDynNames unfoldDyn : Array Name) (projSt? : Option SimpTheorems) : TacticM Unit := do
  if let g :: rest ← getGoals then
    let closedRfl ← if projSt?.isNone then tryReflGoal g else pure false
    if closedRfl then setGoals rest
    else
      let baseCtx ← mkDynamicSimpCtx unfoldDyn (some ("reachBase", reachBaseSimpNames)) (withEqns := false)
      let g2? ← match projSt? with
        | some st => simpGoalOnly g (← Simp.mkContext baseCtx.config (baseCtx.simpTheorems.push st) baseCtx.congrTheorems)
        | none => match ← simpGoalOnly g baseCtx (dsimpOnly := true) with | none => pure none | some g1 => simpGoalOnly g1 baseCtx
      let g3? ← match g2? with
        | none => pure none
        | some g2 => if ← tryCloseBasic g2 (reducibleOnly := true) then pure none else if projSt?.isSome then pure (some g2) else trySimpAll g2 (← mkSimpCtxWithBase) #[← Meta.Simp.getSimprocs]
      setGoals (match g3? with | none => rest | some g' => g' :: rest)
  if !(← getGoals).isEmpty then
    let (bCtx, _) ← mkCachedSimpCtx "reachBool" reachBoolSimpNames; let dCtx ← mkEmptyDsimpCtx
    let splitSimp : TacticM Unit := do setGoals (← splitTargetsRec 16 (← (← getGoals).filterMapM (simpGoalAllHyps · bCtx)) (some dCtx))
    splitSimp; if !(← getGoals).isEmpty && projSt?.isNone then runUnfoldPresent #[] allDynNames; splitSimp
    let closeLeaf (g : MVarId) : MetaM Bool := do if ← tryCloseBasic g then pure true else tryCloseGroundKernel g (check := true)
    forEachGoal fun g => do
      if ← closeLeaf g then setGoals []; return
      let some g' ← trySimpAll g (← mkSimpCtxWithBase) #[← Meta.Simp.getSimprocs] | setGoals []; return
      if ← closeLeaf g' then setGoals [] else setGoals [g']; discard <| tryTac (requireClosed := true) (Qed.Lang.runPQTactic `(tactic| qedAutoClose))

@[noinline] private def runDischargeReachable (upd initT : Term) (nm : Ident) (labelLit : StrLit) : TacticM Unit := withFreshHeartbeatsT do
  if let g0 :: _ ← getGoals then
    if (← g0.withContext (Lean.instantiateMVars (← g0.getType))).getUsedConstants.contains ``Qed.optSat then
      if ← tryCloseGroundKernel g0 (check := true) then replaceMainGoal []; return
  let dynNames ← foldlMeta #[upd, initT] #[] fun acc raw =>
    match extractHeadIdent? raw.raw with
    | none => pure acc
    | some idStx => return (← resolveCompUpdateUnfolds idStx).foldl (fun a n => if a.contains n then a else a.push n) acc
  try
    let solvedFast ← match ← getGoals with
      | g0 :: _ => match ← buildFastReconThms? g0 (dynNames.filter (·.getString! == "_reconcileHoisted")) with
          | some projSt => tryRestoreM false id (do runReachPass dynNames (dynNames.filter (·.getString! != "_reconcileHoisted")) (some projSt); return (← getGoals).isEmpty)
          | none => pure false
      | [] => pure false
    unless solvedFast do runReachPass dynNames dynNames none
  catch _ => pure ()
  let lbl := labelLit.getString
  Qed.Diag.throwUnsolvedGoals m!"Example `{nm.getId}` failed to prove `{lbl}`:"
    m!"\n\nHint: Verify the action sequence reaches a state satisfying `{lbl}` (or strengthen the `where` preconditions for parametric examples)." (ref? := some nm)

elab "qedDischargeReachable" upd:term:max initT:term:max nm:ident labelLit:str : tactic => runDischargeReachable upd initT nm labelLit
end ReachabilityTactic
end Qed
