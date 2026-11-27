import Qed.Invariant.Predicates
import Qed.Runtime.Verify

namespace Qed
open Lean Elab Tactic Qed.Verify.Core

@[noinline] private def runUnfoldViewHelpers : TacticM Unit :=
  qedUnfoldHelperLoop 6 fun env n =>
    if !qedIsHelper env n || (n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf)) then return false
    else return (← getProjectionFnInfo? n).isNone

@[noinline] private def generalizeAndCases (g : MVarId) (e : Expr) : MetaM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome <| g.withContext do
    if e.isFVar then return some ((← g.cases e.fvarId!).toList.map (·.mvarId))
    let (fvs, g1) ← g.generalize #[{ expr := e, xName? := some `_qed_enum_x }]
    match fvs[0]? with | some fv => return some ((← g1.cases fv).toList.map (·.mvarId)) | none => return none

@[noinline] private def runCloseExhaustiveEnum (g : MVarId) : MetaM Bool := do
  let lhsList ← g.withContext <| collectLCtxDecls fun d => do
    let inner := match ← instantiateMVars d.type with | .app (.const ``Not _) t => t | t => t
    return match inner with
      | .app (.app (.app (.const ``Eq _) _) (.app (.app (.app (.app (.const ``BEq.beq _) _) _) lhs) _)) _
      | .app (.app (.app (.const ``Eq _) _) lhs) _ => some lhs | _ => none
  lhsList.toList.anyM fun lhs => tryRestoreM false id do
    let some sub ← generalizeAndCases g lhs | return false
    sub.allM fun sg => do
      if ← sg.contradictionCore {} then return true
      if ← tryDirectDecide sg then return true
      match ← trySimpAll sg (← mkSimpCtxWithBase) with | none => return true | some sg' => tryDirectDecide sg'

private partial def findFiniteEnumExpr (env : Environment) (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars then return none
  if !e.isConst && !(e.getAppFn.constName?.any env.isConstructor) then
    let ty ← Meta.inferType e
    if let .const nm _ := ty.getAppFn then
      if nm != ``Unit && nm != ``PUnit && (e.isFVar || nm != ``Bool) then
        if let some k := nullaryEnumCtorCount? env ty then if 2 ≤ k && k ≤ 8 then return some e
  match e with
  | .app f a => (← findFiniteEnumExpr env a).elim (findFiniteEnumExpr env f) (pure ∘ some)
  | .letE _ _ v b _ => (← findFiniteEnumExpr env v).elim (if !b.hasLooseBVars then findFiniteEnumExpr env b else pure none) (pure ∘ some)
  | _ => return none

private def evalGroundBoolGoal (g : MVarId) (tgt : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  if let some (_, lhs, rhs) := tgt.eq? then
    if rhs.isConstOf ``Bool.true then
      let v ← try Meta.whnf lhs catch _ => pure lhs
      if v.isConstOf ``Bool.true then g.assign (← Meta.mkEqRefl (mkConst ``Bool.true)); return some []
      if v.isConstOf ``Bool.false then
        let gf ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
        g.assign (mkApp2 (mkConst ``False.elim [Level.zero]) tgt gf); return some [gf.mvarId!]
      return none
  if ← tryReflGoal g then return some [] else return none

@[noinline] private def evalGroundGoals (chk : Std.HashSet MVarId) (prog : Bool) (acc : List MVarId) :
    List MVarId → MetaM (List MVarId × Std.HashSet MVarId × Bool)
  | [] => pure (acc.reverse, chk, prog)
  | g :: rest => do
      let tgt ← g.withContext do instantiateMVars (← g.getType)
      if !tgt.isFalse && !tgt.hasFVar && !chk.contains g then
        match ← evalGroundBoolGoal g tgt with
        | some gs' => evalGroundGoals (chk.insert g) true (gs'.reverse ++ acc) rest
        | none => evalGroundGoals (chk.insert g) prog (g :: acc) rest
      else evalGroundGoals chk prog (g :: acc) rest

@[noinline] private def runSplitFiniteEnums : TacticM Unit := do
  let splitOne (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    if tgt.isFalse then return none
    match ← findFiniteEnumExpr (← getEnv) tgt with | some e => generalizeAndCases g e | none => pure none
  let rec rounds (chk : Std.HashSet MVarId) : Nat → TacticM (Std.HashSet MVarId)
    | 0 => pure chk
    | n + 1 => do
        if (← getGoals).isEmpty then return chk
        let (gs, chk', prog0) ← evalGroundGoals chk false [] (← getGoals)
        let (next, prog) ← (gs.foldlM (init := ([], prog0)) fun (acc, p) g => do
          match ← splitOne g with | some gs' => pure (gs'.reverse ++ acc, true) | none => pure (g :: acc, p) : MetaM _)
        setGoals next.reverse; if prog then rounds chk' n else pure chk'
  let chk ← rounds {} 2
  setGoals (← evalGroundGoals chk false [] (← getGoals)).1

@[noinline] private def splitTargetsRec : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do match ← trySplitTarget g with | some sub => splitTargetsRec fuel (sub ++ rest) | none => return g :: (← splitTargetsRec fuel rest)

private def a11yReduceNames : Array Name := #[
  ``Qed.Html.fold, ``Qed.Html.foldList, ``Qed.Html.a11yValid, ``Qed.Html.imgsHaveAlt, ``Qed.Html.imgsHaveAltList,
  ``Qed.Html.buttonsAccessible, ``Qed.Html.buttonsAccessibleList, ``Qed.Html.elemHasAccessibleName, ``Qed.Html.hasAccessibleNameChild,
  ``Qed.Html.hasAccessibleNameChildren, ``Qed.Html.validAriaRoles, ``Qed.Html.validAriaRolesList, ``Qed.attrsValidAriaRoles,
  ``Qed.Html.labelsAssociated, ``Qed.Html.labelsAssociatedList, ``Qed.Html.containsFormControl, ``Qed.Html.containsFormControlList,
  ``Qed.isFormControlTag, ``Qed.Html.noDuplicateIds, ``Qed.Html.collectIds, ``Qed.Html.collectIdsList, ``Qed.Html.headingsOrdered,
  ``Qed.Html.collectHeadings, ``Qed.Html.collectHeadingsList, ``Qed.Html.htmlHasLang, ``Qed.Html.htmlHasLangList,
  ``Qed.attrValue, ``Qed.hasAttr, ``Qed.hasNonBlankAttr]

private def styleLeafCoreNames : Array Name := #[``Qed.everyElement, ``Qed.everyElementL, ``Qed.attrClasses, ``Qed.attrRole, ``Qed.hasOneClass]
private def styleReduceCoreNames : Array Name := #[
  ``Qed.roleHasOneOf, ``Qed.tagHasOneOf, ``Qed.roleHas, ``Qed.roleHasOnly, ``Qed.roleLacks, ``Qed.tagLacks, ``Qed.roleHasAll, ``Qed.tagHas,
  ``Qed.noConflictingStyles, ``Qed.hasRole, ``Qed.hasTag, ``Qed.both, ``Qed.either, ``Qed.exactlyOne, ``Qed.allRolesOff, ``Qed.exactlyOneOf,
  ``Qed.exactlyOneOf.go] ++ styleLeafCoreNames ++ a11yReduceNames ++ #[
  ``Qed.Html.imgsHaveAlt_map, ``Qed.Html.buttonsAccessible_map, ``Qed.Html.validAriaRoles_map, ``Qed.Html.labelsAssociated_map,
  ``Qed.Html.noDuplicateIds_map, ``Qed.Html.headingsOrdered_map, ``Qed.Html.htmlHasLang_map, ``Qed.Html.a11yValid_map,
  ``Qed.Html.map, ``Qed.Html.mapChildren, ``Qed.Html.mapAttrs, ``Qed.Html.mapAttrsList, ``Qed.Attr.map, ``Qed.Lang.QedVal.val_id,
  ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list, ``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list,
  ``Qed.Lang.QedMem.mem_string, ``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string]
private def styleReduceOptNames : Array Name := Qed.viewCoreUnfolds ++ #[
  `Qed.View.mapScope, `Qed.View.mapScopeEach, `Qed.VAttr.mapScope, `Qed.View.memo,
  `Qed.Attr.empty, `Qed.Html.ofOption, `Qed.toString_string, `Qed.withKey, `Qed.ToHref.toHref] ++ Qed.qedForEachHelperNames ++ Qed.qedHtmlHelperNames
private def styleLeafFastNames : Array Name := styleLeafCoreNames ++ boolConstSimpNames ++ #[
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.false_eq_true, ``List.all_cons, ``List.all_nil, ``List.any_cons, ``List.any_nil, ``beq_self_eq_true, ``eq_self, ``decide_true, ``decide_false]

private def isUnprovableFalseGoal (g : MVarId) : MetaM Bool := g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let isFalseEq := tgt.isFalse || match tgt.eq? with | some (_, l, r) => l.consumeMData.isConstOf ``Bool.false && r.consumeMData.isConstOf ``Bool.true | none => false
  if !isFalseEq then return false
  return (← findLCtxDecl? fun d => do if ← isPropSafe d.type then pure (some ()) else pure none).isNone

@[noinline] private def runStyleLeafClose (g : MVarId) : MetaM (List MVarId) := do
  if ← tryReflGoal g then return []
  let some g1 ← trySimpAll g (← mkCachedSimpCtx "styleLeafFast" styleLeafFastNames).1 | return []
  if ← tryReflGoal g1 then return []
  if ← isUnprovableFalseGoal g1 then return [g1]
  let some g2 ← trySimpAll g1 (← mkSimpCtxWithBase (styleLeafCoreNames ++ a11yReduceNames) (cacheKey? := some "styleLeafFull")) #[← Meta.Simp.getSimprocs] | return []
  if ← tryDirectDecide g2 then return []
  if ← tryDirectOmega g2 then return []
  if ← runCloseExhaustiveEnum g2 then return []
  return [g2]

@[noinline] private def reduceOneStyleGoal (g1 : MVarId) : TacticM Unit := do
  if (← g1.withContext (instantiateMVars (← g1.getType))).isFalse then return
  runUnfoldViewHelpers
  if let [g] ← getGoals then
    if ← tryReflGoal g then setGoals []; return
    if ← tryRestoreM false id ((do (← splitTargetsRec 32 [g]).allM tryReflGoal) : MetaM Bool) then setGoals []; return
  if let g :: rest ← getGoals then
    try
      let env ← getEnv; let used ← collectGoalConsts g false
      let ctx ← mkDynamicSimpCtx (styleReduceOptNames.filter fun n => env.contains n && used.contains n) (some ("styleReduceCore", styleReduceCoreNames)) (withEqns := false)
      setGoals (match ← simpGoalOnly g ctx with | none => rest | some g' => g' :: rest)
    catch _ => pure ()
  if !(← getGoals).isEmpty then setGoals (← ((← splitTargetsRec 32 (← getGoals)).mapM runStyleLeafClose : MetaM _)).flatten

@[noinline] def runStyleReduce (view : Ident) : TacticM Unit := do
  let viewCtx? ← try some <$> mkDynamicSimpCtx #[← realizeGlobalConstNoOverload view] none (withEqns := false) catch _ => pure none
  runSplitFiniteEnums
  forEachGoal fun g0 => do
    if (← g0.withContext (instantiateMVars (← g0.getType))).isFalse then return
    if let some vCtx := viewCtx? then
      match ← simpGoalOnly g0 vCtx with | none => setGoals []; return | some g1 => setGoals [g1]
    runSplitFiniteEnums; forEachGoal reduceOneStyleGoal

@[noinline] private def hasSub (s sub : String) : Bool := s.contains sub

private def a11yDiagTable : Array (String × String) := #[
  ("imgsHaveAlt", "An `<img>` element in `{v}` is missing an `alt` attribute. Add `alt=\"...\"` (or `alt=\"\"` for decorative images)."),
  ("buttonsAccessible", "A `<button>` or `<a>` element in `{v}` has no accessible name in some branch. Provide non-empty text, `aria-label`, `aria-labelledby`, `title`, or a child `<img>` with non-empty `alt`."),
  ("validAriaRoles", "An element in `{v}` has an unrecognized WAI-ARIA `role` attribute. Use a valid WAI-ARIA 1.2 role name."),
  ("labelsAssociated", "A `<label>` element in `{v}` neither has a non-empty `for` attribute nor wraps a form control (`<input>`, `<select>`, `<textarea>`)."),
  ("noDuplicateIds", "Two elements in `{v}` share the same `id` attribute in some branch. Ensure every non-empty `id` is unique."),
  ("headingsOrdered", "Headings in `{v}` skip a level (e.g. `<h1>` directly to `<h3>`). Use sequential heading levels."),
  ("htmlHasLang", "An `<html>` element in `{v}` is missing a non-empty `lang` attribute (e.g. `<html lang=\"en\">`)."),
  ("a11yValid", "An accessibility check failed in `{v}` (check `<img alt>`, `<button>`/`<a>` accessible names, WAI-ARIA `role`, `<label>` association, unique `id`s, heading order, and `<html lang>`).")]

private def diagnoseStyling (predStr : String) (vName : Name) : String × String :=
  match a11yDiagTable.find? (fun (k, _) => hasSub predStr k) with
  | some (_, tmpl) => ("Accessibility invariant", tmpl.replace "{v}" vName.toString)
  | none => ("Styling invariant",
      if hasSub predStr "roleLacks" || hasSub predStr "tagLacks" then s!"A matching element in `{vName}` carries a forbidden style class in some branch. Remove that style from the matching element or guard it so it cannot apply there."
      else if hasSub predStr "exactlyOne" then s!"In some branch of `{vName}`, either none or more than one of the listed roles carries the active style, a role is missing the inactive style, or one of the roles is not rendered."
      else if (hasSub predStr "hasRole" || hasSub predStr "hasTag") && !(hasSub predStr "roleHas" || hasSub predStr "tagHas") then s!"No element with the required `role`/tag is rendered in some branch of `{vName}`. Check every conditional branch of `{vName}`."
      else s!"Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `{vName}`.")

@[noinline] private def runDischargeStyling (view nm : Ident) (predLit : StrLit) : TacticM Unit := do
  let (_, g1) ← (← getMainGoal).intro `m
  let g2 ← if (← g1.withContext (Meta.whnf (← g1.getType))).isForall then pure (← g1.intro `_qed_h_assume).2 else pure g1
  let g3? ← g2.withContext do
    if let some c ← findLCtxDecl? fun d => do if d.userName == `_qed_h_assume then return (← instantiateMVars d.type).getAppFn.constName? else return none then
      simpGoalAllHyps g2 (← mkDynamicSimpCtx #[c] none (withEqns := false))
    else pure (some g2)
  setGoals <| ← match g3? with
    | none => pure []
    | some g3 => g3.withContext do
        let tgt ← instantiateMVars (← g3.getType)
        if let some (_, lhs, _) := tgt.eq? then
          let (fn, args) := (lhs.getAppFn, lhs.getAppArgs)
          if (fn.isConstOf ``Qed.roleHasOneOf || fn.isConstOf ``Qed.tagHasOneOf) && args.size == 4 then
            let gHas ← Meta.mkFreshExprSyntheticOpaqueMVar (← Meta.mkEq (← Meta.mkAppM (if fn.isConstOf ``Qed.roleHasOneOf then ``Qed.hasRole else ``Qed.hasTag) #[args[1]!, args[3]!]) (mkConst ``Bool.true))
            let gMain ← Meta.mkFreshExprSyntheticOpaqueMVar tgt; g3.assign gMain; return [gHas.mvarId!, gMain.mvarId!]
        return [g3]
  withOptions (fun o => maxRecDepth.set o (max (maxRecDepth.get o) 16384)) do forEachGoal fun _ => withFreshHeartbeatsT (runStyleReduce view)
  let predStr := predLit.getString; let (label, diagnosis) := diagnoseStyling predStr view.getId
  Qed.Diag.throwUnsolvedGoals m!"{label} `{nm.getId}` failed in `{view.getId}`:\n  • `{predStr}` does not hold in every state"
    m!"\n\nHint: {diagnosis}" (ref? := some nm)
    (formatGoal? := some fun g => g.withContext do
      let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
      return if s == "False" || s == "false = true" then none else some s!"  • view must satisfy:  {s}")

elab "qedStyleReduce " view:ident : tactic => runStyleReduce view
elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic => withFreshHeartbeatsT (runDischargeStyling view nm predLit)
syntax (name := invariantView) "invariant " ident " : " qedExpr,+ " holds_in " ident (" assuming " qedExpr)? (" := " term)? : command

section InvariantViewElab
open Lean Elab Command
@[noinline] private def elabInvariantViewCmd (name view : Ident) (rawPreds : Array (TSyntax `qedExpr))
    (assumeE : Option (TSyntax `qedExpr)) (pf : Option Term) : CommandElabM Unit := do
  let p :: ps := (← rawPreds.toList.mapM fun p => liftMacroM (Qed.Lang.lowerSimpleQedExpr .val p.raw)) | throwErrorAt name "empty view invariant"
  let predStr := String.intercalate ", " (rawPreds.toList.map fun p => (p.raw.reprint.getD "this rule").trimmed)
  let assumeP? ← match assumeE with
    | none => pure none
    | some a =>
        let uA := Qed.Lang.unwrapParens1 a.raw
        let aT ← liftMacroM (Qed.Lang.lowerSimpleQedExpr (if uA.getKind == ``Qed.Lang.qedLam1 || uA.getKind == ``Qed.Lang.qedLamN then .propInv else .val) a.raw)
        some <$> if aT.raw.isIdent then try liftTermElabM (extractInvPred ⟨aT.raw⟩) catch _ => pure aT else pure aT
  let cmd ← liftMacroM <| Qed.Lang.runPureQuot do
    let pred ← ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
    let prop ← match assumeP? with
      | some P => `(∀ m, ($P) m → ($pred) ($view m) = true) | none => `(∀ m, ($pred) ($view m) = true)
    match pf with
    | some pfT => `(theorem $name:ident : $prop := $pfT)
    | none => `(set_option linter.unusedSimpArgs false in theorem $name:ident : $prop := by qedDischargeStyling $view $name $(Syntax.mkStrLit predStr))
  elabCommand cmd

elab_rules : command
  | `(invariant $name:ident : $preds:qedExpr,* holds_in $view:ident $[assuming $assumeE:qedExpr]? $[ := $pf:term]?) =>
    elabInvariantViewCmd name view preds.getElems assumeE pf
end InvariantViewElab
end Qed
