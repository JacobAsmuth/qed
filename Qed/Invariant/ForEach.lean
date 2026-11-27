import Qed.Component.Core
import Qed.Verify.Core
import Qed.Invariant.View

namespace Qed
open Lean Elab Tactic Qed.Verify.Core

theorem Html.liftA11yWithKey {α β msg : Type} {P : ∀ {m : Type}, Html m → Bool} {PL : ∀ {m : Type}, List (Html m) → Bool}
    (hML : ∀ {γ m : Type} (g : γ → Html m) (l : List γ), PL (l.map g) = true ↔ ∀ x ∈ l, P (g x) = true)
    (hCan : ∀ {m : Type} (h : Html m), P h.canonical = P h) (hMap : ∀ {γ δ : Type} (f : γ → δ) (h : Html γ), P (h.map f) = P h)
    {k : α → String} {f : α → β → msg} {v : α → Html β} {l : List α} (hc : ∀ c : α, P (v c) = true) :
    PL (l.map fun c => withKey (k c) ((v c).map (f c))) = true :=
  (hML _ _).2 fun c _ => by rw [← hCan, Html.canonical_withKey, hCan, hMap]; exact hc c

theorem Html.liftA11yPlain {α β msg : Type} {P : ∀ {m : Type}, Html m → Bool} {PL : ∀ {m : Type}, List (Html m) → Bool}
    (hML : ∀ {γ m : Type} (g : γ → Html m) (l : List γ), PL (l.map g) = true ↔ ∀ x ∈ l, P (g x) = true)
    (hMap : ∀ {γ δ : Type} (f : γ → δ) (h : Html γ), P (h.map f) = P h)
    {f : α → β → msg} {v : α → Html β} {l : List α} (hc : ∀ c : α, P (v c) = true) :
    PL (l.map fun c => (v c).map (f c)) = true :=
  (hML _ _).2 fun c _ => (hMap (f c) (v c)).trans (hc c)

def extractViewInvPred (childStyled : Ident) : Term.TermElabM Term := do
  Meta.forallTelescope (← getConstInfo (← realizeGlobalConstNoOverload childStyled)).type fun _ body => do
    let some lhs := body.eq?.map (·.2.1) | throwErrorAt childStyled "`{childStyled}` doesn't look like a `… holds_in …` invariant, so its predicate can't be inferred, write it explicitly (`<pred> for_each … using {childStyled}`)."
    PrettyPrinter.delab lhs.appFn!

private inductive FeOp where | exactH | direct (lem : Name) | elem (lem : Name) | map | mod | updateKeyed
private def feOpTable : List (Name × FeOp) := [
  (``Array.filter, .direct ``Qed.ForEach.forall_filter), (``Array.sortBy, .direct ``Qed.ForEach.forall_sortBy),
  (``Array.pop, .direct ``Qed.ForEach.forall_pop), (``Array.reverse, .direct ``Qed.ForEach.forall_reverse),
  (``Array.extract, .direct ``Qed.ForEach.forall_extract), (``Array.eraseIdx, .direct ``Qed.ForEach.forall_eraseIdx),
  (``Array.eraseIdxIfInBounds, .direct ``Qed.ForEach.forall_eraseIdxIfInBounds), (``Array.swap, .direct ``Qed.ForEach.forall_swap),
  (``Array.swapIfInBounds, .direct ``Qed.ForEach.forall_swapIfInBounds), (``Array.push, .elem ``Qed.ForEach.forall_push),
  (``Array.set, .elem ``Qed.ForEach.forall_set), (``Array.setIfInBounds, .elem ``Qed.ForEach.forall_setIfInBounds),
  (``HAppend.hAppend, .elem ``Qed.ForEach.forall_append), (``Array.append, .elem ``Qed.ForEach.forall_append),
  (``Array.map, .map), (``Array.modify, .mod)]
private def feFallbackOps : List FeOp :=
  [.exactH] ++ feOpTable.filterMap (fun | (_, .direct l) => some (.direct l) | _ => none) ++
  [.updateKeyed, .map, .mod] ++ (feOpTable.filterMap fun | (_, .elem l) => some (.elem l) | _ => none).take 4

@[noinline] private def tryCloseForEachSub (dCtx predCtx : Meta.Simp.Context) (isPredIdent : Bool) (g : MVarId) : TacticM Bool := do
  let some g1 ← simpGoalAllHyps g dCtx (dsimpOnly := true) | return true
  let some g2 ← simpGoalAllHyps g1 predCtx | return true
  if ← tryCloseBasic g2 then return true
  let baseCtx ← mkSimpCtxWithBase
  if !isPredIdent then match ← simpGoalOnly g2 baseCtx with | none => return true | some g3 => if ← tryCloseBasic g3 then return true
  let some g3 ← trySimpAll g2 baseCtx | return true
  if ← tryCloseBasic g3 then return true
  setGoals [g3]; tryTac (requireClosed := true) `(tactic| qedAutoClose)

@[noinline] private def closeWithH (hFv : FVarId) (gh : MVarId) : MetaM Bool := do
  if ← gh.assumptionCore then return true
  tryRestoreM false id (gh.withContext do return (← gh.apply (mkFVar hFv)).isEmpty)

@[noinline] private def applyFeOpCore (g : MVarId) (hFv : FVarId) (hcExprs : List Expr) (closeSub : MVarId → TacticM Bool) : FeOp → TacticM (Option (List MVarId))
  | .exactH => return if ← closeWithH hFv g then some [] else none
  | .direct lem => do
      let [gh] ← g.applyConst lem | return none
      return if ← closeWithH hFv gh then some [] else none
  | .elem lem => do
      let gh :: rest ← g.applyConst lem | return none
      if !(← closeWithH hFv gh) then return none
      some <$> rest.filterM fun sg => return !(← closeSub sg)
  | .map => do
      let [g1] ← g.applyConst ``Qed.ForEach.forall_map | return none
      let (fvs, g2) ← g1.introN 2
      let pf ← g2.withContext (Meta.mkAppM' (mkFVar hFv) #[mkFVar fvs[0]!, mkFVar fvs[1]!])
      let (_, g3) ← (← g2.assert `hP (← g2.withContext (Meta.inferType pf)) pf).intro1P
      return some (if ← closeSub g3 then [] else [g3])
  | .mod => do
      let [gh, g1] ← g.applyConst ``Qed.ForEach.forall_modify | return none
      if !(← closeWithH hFv gh) then return none
      let (_, g2) ← g1.introN 3; return some (if ← closeSub g2 then [] else [g2])
  | .updateKeyed => do
      let [ghc, gh] ← g.applyConst ``Qed.ForEach.updateKeyed_forall | return none
      if !(← closeWithH hFv gh) then return none
      let ok : Bool ← (hcExprs.anyM fun hc => tryRestoreM false id (ghc.withContext do return (← ghc.apply hc).isEmpty) : MetaM Bool)
      return if ok then some [] else none

@[noinline] private def tryFeOp (g : MVarId) (hFv : FVarId) (hcExprs : List Expr) (closeSub : MVarId → TacticM Bool) (op : FeOp) : TacticM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome (applyFeOpCore g hFv hcExprs closeSub op)

@[noinline] private def runForEachLift (upd childInv : Ident) (pred : Term) : TacticM Unit := withFreshHeartbeatsT do
  let predNm? ← if pred.raw.isIdent then try some <$> realizeGlobalConstNoOverload pred catch _ => pure none else pure none
  let predCtx ← mkDynamicSimpCtx (match predNm? with | some p => #[p, ``Qed.Lang.QedVal.val_id] | none => #[``Qed.Lang.QedVal.val_id]) none
  let dCtx ← mkEmptyDsimpCtx
  let updCtx ← mkDynamicSimpCtx ((← resolveCompUpdateUnfolds upd.raw) ++ #[``InvTarget.proj_id, ``InvTarget.proj_fst]) none (withEqns := false)
  let childExpr ← Term.elabTerm childInv none
  let hcExprs := match ← try some <$> Meta.mkAppM ``And.right #[childExpr] catch _ => pure none with | some r => [childExpr, r] | none => [childExpr]
  let (fvs, g1) ← (← getMainGoal).introN 2 [`m, `msg]
  let closeSub := tryCloseForEachSub dCtx predCtx pred.raw.isIdent
  let rec tryOps (g : MVarId) (hFv : FVarId) : List FeOp → TacticM (List MVarId) | [] => pure [g] | op :: r => do match ← tryFeOp g hFv hcExprs closeSub op with | some rem => pure rem | none => tryOps g hFv r
  setGoals ((← g1.cases fvs[1]!).toList.map (·.mvarId))
  forEachGoal fun g => withFreshHeartbeatsT do
    let (hFv, g0) ← g.intro `h
    let some g1 ← simpGoalOnly g0 updCtx | setGoals []; return
    let fast? ← g1.withContext do
      let some collRaw := extractForEachColl? (← instantiateMVars (← g1.getType)) | return none
      match (Qed.stripLetE 16 collRaw).getAppFn.constName? with
      | none => return some .exactH
      | some nm => return some (if nm == ``Qed.Component.updateKeyed || nm.getString! == "updateKeyed" then .updateKeyed else (feOpTable.find? (·.1 == nm)).map (·.2) |>.getD .exactH)
    setGoals (← tryOps g1 hFv (match fast? with | some op => op :: feFallbackOps | none => feFallbackOps))

@[noinline] private def runDischargeForEach (upd childInv nm : Ident) (pred : Term) : TacticM Unit := withFreshHeartbeatsT do
  runForEachLift upd childInv pred; let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let predStr := (pred.raw.reprint.getD "the contract").trimmed
    Qed.Diag.throwUnsolvedGoals m!"Invariant `{nm.getId}` failed to lift `{predStr}` across `{upd.getId}`:"
      m!"\n\nHint: Ensure newly inserted elements satisfy `{predStr}`, or prove only the remaining branch:\n  invariant {nm.getId} : {predStr} for_each … using {childInv.getId} := by\n    forEachLift {upd.getId} {childInv.getId} {predStr}\n    case {← goals[0]!.getTag} => …"
      (ref? := some nm) (goals? := some goals)
      (formatGoal? := some fun g => g.withContext do
        let ty ← instantiateMVars (← g.getType); let s ← Qed.Diag.ppQedExpr ty ["m"]
        let why := if s.contains "qsort" then "uses `Array.qsort` (no membership lemma); switch to Qed's verified `sortBy` so it lifts automatically."
          else if s.contains " ++ " then "appends elements (`++`) not known to satisfy the contract; validate them first or prove this case."
          else if ty.isForall then "transforms the collection with an unverified operation; add a lemma or prove this case." else "inserts an element not known to satisfy the contract."
        return some s!"  • {Qed.Diag.formatCaseTag (← g.getTag)}: {why}\n    must satisfy:  {s}")

elab "forEachLift " upd:ident childInv:ident pred:term : tactic => runForEachLift upd childInv pred
elab "qedDischargeForEach" upd:ident childInv:ident nm:ident pred:term : tactic => runDischargeForEach upd childInv nm pred

private def a11yForEachLiftPairs : List (Name × Name × Name) := [
  (``Qed.Html.imgsHaveAltList_mapList, ``Qed.Html.imgsHaveAlt_map, ``Qed.Html.imgsHaveAlt_canonical),
  (``Qed.Html.buttonsAccessibleList_mapList, ``Qed.Html.buttonsAccessible_map, ``Qed.Html.buttonsAccessible_canonical),
  (``Qed.Html.validAriaRolesList_mapList, ``Qed.Html.validAriaRoles_map, ``Qed.Html.validAriaRoles_canonical),
  (``Qed.Html.labelsAssociatedList_mapList, ``Qed.Html.labelsAssociated_map, ``Qed.Html.labelsAssociated_canonical),
  (``Qed.Html.htmlHasLangList_mapList, ``Qed.Html.htmlHasLang_map, ``Qed.Html.htmlHasLang_canonical)]
private def mapSimpNames : Array Name := #[``Qed.attrRole_map, ``Qed.attrClasses_map, ``Qed.hasOneClass]
private def attrSimpNames : Array Name := #[``Qed.attrRole, ``Qed.attrValue, ``Qed.attrClasses, ``Qed.hasOneClass, ``beq_self_eq_true, ``eq_self] ++ boolConstSimpNames

@[noinline] private def applyWithMVars (g : MVarId) (tgt : Expr) (c : Name) (vals : List (Nat × Expr)) (subIdx? : Option Nat := none) : MetaM (Option (Option MVarId)) :=
  tryRestoreM none Option.isSome do
    let fn ← Meta.mkConstWithFreshMVarLevels c; let (mvs, _, _) ← Meta.forallMetaTelescope (← Meta.inferType fn)
    if !(← vals.allM fun (i, v) => Meta.isDefEq mvs[i]! v) then return none
    let pf := mkAppN fn mvs
    if ← Meta.isDefEq (← Meta.inferType pf) tgt then g.assign pf; return some (subIdx?.map fun i => mvs[i]!.mvarId!)
    return none

@[noinline] private def tryLiftChildElem (mapCtx fullMapCtx : Meta.Simp.Context) (childExpr : Expr) (cFv : FVarId) (g : MVarId) : MetaM Bool :=
  tryRestoreM false id <| g.withContext do
    let some (some g1) ← applyWithMVars g (← instantiateMVars (← g.getType)) ``Qed.everyElement_through_map [(7, ← Meta.mkAppM' childExpr #[mkFVar cFv])] (some 6) | return false
    let (_, g2) ← g1.introN 2
    match ← simpGoalOnly g2 mapCtx with | none => return true | some g3 => return (← simpGoalOnly g3 fullMapCtx).isNone

@[noinline] private def liftOneStyleGoal (mapCtx fullMapCtx everyCtx attrCtx fullAttrCtx : Meta.Simp.Context) (childExpr : Expr) (g : MVarId) : MetaM Bool := do
  let closedEvery ← tryRestoreM false id do
    let [g1] ← g.applyConst ``Qed.everyElementL_mapList_of | return false
    let (cfvs, g2) ← g1.introN 2; let cFv := cfvs[0]!
    if ← tryLiftChildElem mapCtx fullMapCtx childExpr cFv g2 then return true
    match ← simpGoalOnly g2 everyCtx with
    | none => return true
    | some g3 => (← splitGoalAnds g3).allM fun sg => do
        if ← tryLiftChildElem mapCtx fullMapCtx childExpr cFv sg then return true
        match ← simpGoalOnly sg attrCtx with
        | none => return true
        | some sg1 => if ← tryReflGoal sg1 then return true else if (← simpGoalOnly sg1 fullAttrCtx).isNone then return true else tryReflGoal sg1
  if closedEvery then return true
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  a11yForEachLiftPairs.anyM fun (ml, m, can) => g.withContext do
    if (← applyWithMVars g tgt ``Qed.Html.liftA11yWithKey [(5, mkConst ml), (6, mkConst can), (7, mkConst m), (12, childExpr)]).isSome then return true
    return (← applyWithMVars g tgt ``Qed.Html.liftA11yPlain [(5, mkConst ml), (6, mkConst m), (10, childExpr)]).isSome

@[noinline] private def runForEachStyleLift (view childStyled : Ident) : TacticM Unit := do
  let (mapCtx, _) ← mkCachedSimpCtx "feMap" mapSimpNames; let fullMapCtx ← mkSimpCtxWithBase mapSimpNames (cacheKey? := some "feMapFull")
  let (everyCtx, _) ← mkCachedSimpCtx "feEvery" #[``Qed.everyElement, ``Qed.everyElementL, ``Bool.and_eq_true]
  let (attrCtx, _) ← mkCachedSimpCtx "feAttr" attrSimpNames; let fullAttrCtx ← mkSimpCtxWithBase #[``Qed.attrRole, ``Qed.attrClasses, ``Qed.hasOneClass] (cacheKey? := some "feAttrFull")
  let childExpr ← Term.elabTerm childStyled none; let (_, g1) ← (← getMainGoal).intro `m; setGoals [g1]; runStyleReduce view
  forEachGoal fun g => do if ← liftOneStyleGoal mapCtx fullMapCtx everyCtx attrCtx fullAttrCtx childExpr g then setGoals []

@[noinline] private def runDischargeStyledForEach (view field childStyled nm : Ident) (pred : Term) : TacticM Unit := withFreshHeartbeatsT do
  runForEachStyleLift view childStyled; let predStr := (pred.raw.reprint.getD "the rule").trimmed
  Qed.Diag.throwUnsolvedGoals m!"Styling invariant `{nm.getId}` failed to lift `{predStr}` over `{field.getId}` in `{view.getId}`:"
    m!"\n\nHint: Finish the remaining branch with `forEachStyleLift`:\n  invariant {nm.getId} : {predStr} for_each {field.getId} using {childStyled.getId} := by\n    forEachStyleLift {view.getId} {childStyled.getId}\n    …"
    (ref? := some nm) (formatGoal? := some fun g => g.withContext do
      let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
      let why := if s.contains "everyElementL" then s!"child list didn't match `{childStyled.getId}`: check that both use the same role and styles." else "an element outside the collection wasn't covered: check if the parent view also renders that role."
      return some s!"  • {why}\n    must satisfy:  {s}")

elab "forEachStyleLift " view:ident childStyled:ident : tactic => runForEachStyleLift view childStyled
elab "qedDischargeStyledForEach" view:ident field:ident childStyled:ident nm:ident pred:term : tactic => runDischargeStyledForEach view field childStyled nm pred
end Qed
