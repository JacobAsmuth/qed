import Qed.Invariant.Predicates
import Qed.Runtime.Verify

namespace Qed

open Lean Elab Tactic Qed.Verify.Core

private def runUnfoldViewHelpers : TacticM Unit :=
  qedUnfoldHelperLoop 6 fun env n =>
    if !qedIsHelper env n || (n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf)) then return false
    else return (← getProjectionFnInfo? n).isNone

private def runCloseExhaustiveEnum : TacticM Unit := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let inner := match ← instantiateMVars d.type with | .app (.const ``Not _) t => t | t => t
    let lhs? : Option Expr := match inner with
      | .app (.app (.app (.const ``Eq _) _) (.app (.app (.app (.app (.const ``BEq.beq _) _) _) lhs) _)) _
      | .app (.app (.app (.const ``Eq _) _) lhs) _ => some lhs
      | _ => none
    if let some lhs := lhs? then
      if ← tryTac (requireClosed := true) (do `(tactic| (generalize $(← PrettyPrinter.delab lhs):term = _qed_enum_x at *; cases _qed_enum_x <;> (simp_all; try decide)))) then return

private def isSmallNullaryEnum (env : Environment) (ty : Expr) (allowBool : Bool := false) : Bool :=
  match ty.getAppFn with
  | .const nm _ =>
      if nm == ``Unit || nm == ``PUnit || (!allowBool && nm == ``Bool) then false
      else match env.find? nm with
        | some (.inductInfo iv) => iv.numParams == 0 && iv.numIndices == 0 && 2 ≤ iv.ctors.length && iv.ctors.length ≤ 8 &&
            iv.ctors.all fun c => match env.find? c with | some (.ctorInfo ci) => ci.numFields == 0 | _ => false
        | _ => false
  | _ => false

private partial def findFiniteEnumExpr (env : Environment) (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars then return none
  if !e.isConst && !(e.getAppFn.constName?.any env.isConstructor) then
    if isSmallNullaryEnum env (← Meta.inferType e) e.isFVar then return some e
  match e with
  | .app f a => (← findFiniteEnumExpr env a).elim (findFiniteEnumExpr env f) (pure ∘ some)
  | .letE _ _ v b _ => (← findFiniteEnumExpr env v).elim (if !b.hasLooseBVars then findFiniteEnumExpr env b else pure none) (pure ∘ some)
  | _ => return none

private def evalGroundBoolGoal (g : MVarId) (tgt : Expr) : TacticM (Option (List MVarId)) := g.withContext do
  if let some (_, lhs, rhs) := tgt.eq? then
    if rhs.isConstOf ``Bool.true then
      let v ← try Meta.whnf lhs catch _ => pure lhs
      if v.isConstOf ``Bool.true then g.assign (← Meta.mkEqRefl (mkConst ``Bool.true)); return some []
      if v.isConstOf ``Bool.false then
        let gf ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
        g.assign (mkApp2 (mkConst ``False.elim [Level.zero]) tgt gf); return some [gf.mvarId!]
      return none
  if ← tryReflGoal g then return some []
  return none

private def runSplitFiniteEnums : TacticM Unit := do
  let mut checked : Std.HashSet MVarId := {}
  let evalGroundPass (gs : List MVarId) (chk : Std.HashSet MVarId) : TacticM (List MVarId × Std.HashSet MVarId × Bool) := do
    let mut chk := chk; let mut prog := false; let mut out := []
    for g in gs do
      let tgt ← g.withContext do instantiateMVars (← g.getType)
      if !tgt.isFalse && !tgt.hasFVar && !chk.contains g then
        chk := chk.insert g
        if let some gs' ← evalGroundBoolGoal g tgt then prog := true; out := out ++ gs'; continue
      out := out ++ [g]
    return (out, chk, prog)
  for _ in [0:2] do
    if (← getGoals).isEmpty then return
    let (gs, chk', prog0) ← evalGroundPass (← getGoals) checked
    checked := chk'; let mut prog := prog0; let mut next := []
    for g in gs do
      let tgt ← g.withContext do instantiateMVars (← g.getType)
      let splitRes? ← if tgt.isFalse then pure none else g.withContext do
        let some e ← findFiniteEnumExpr (← getEnv) tgt | return none
        try
          if e.isFVar then return some ((← g.cases e.fvarId!).toList.map (·.mvarId))
          setGoals [g]; evalTactic (← `(tactic| (generalize $(← PrettyPrinter.delab e):term = _qed_enum_x at *; cases _qed_enum_x)))
          return some (← getGoals)
        catch _ => return none
      match splitRes? with | some gs' => prog := true; next := next ++ gs' | none => next := next ++ [g]
    setGoals next; if !prog then break
  setGoals (← evalGroundPass (← getGoals) checked).1

private def a11yReduceNames : Array Name := #[
  ``Qed.Html.a11yValid, ``Qed.Html.imgsHaveAlt, ``Qed.Html.imgsHaveAltList, ``Qed.Html.buttonsAccessible, ``Qed.Html.buttonsAccessibleList,
  ``Qed.Html.elemHasAccessibleName, ``Qed.Html.hasAccessibleNameChild, ``Qed.Html.hasAccessibleNameChildren, ``Qed.Html.validAriaRoles,
  ``Qed.Html.validAriaRolesList, ``Qed.attrsValidAriaRoles, ``Qed.Html.labelsAssociated, ``Qed.Html.labelsAssociatedList,
  ``Qed.Html.containsFormControl, ``Qed.Html.containsFormControlList, ``Qed.isFormControlTag, ``Qed.Html.noDuplicateIds,
  ``Qed.Html.collectIds, ``Qed.Html.collectIdsList, ``Qed.Html.headingsOrdered, ``Qed.Html.collectHeadings, ``Qed.Html.collectHeadingsList,
  ``Qed.Html.htmlHasLang, ``Qed.Html.htmlHasLangList, ``Qed.attrValue, ``Qed.hasAttr, ``Qed.hasNonBlankAttr]

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
  for d in (← getLCtx) do if !d.isImplementationDetail then if ← Meta.isProp d.type then return false
  return true

private def runStyleLeafClose (g : MVarId) : TacticM (List MVarId) := do
  if ← tryReflGoal g then return []
  let some g1 ← trySimpAll g (← mkCachedSimpCtx "styleLeafFast" styleLeafFastNames).1 | return []
  if ← tryReflGoal g1 then return []
  if ← isUnprovableFalseGoal g1 then return [g1]
  let some g2 ← trySimpAll g1 (← mkSimpCtxWithBase (styleLeafCoreNames ++ a11yReduceNames) (cacheKey? := some "styleLeafFull")) #[← Meta.Simp.getSimprocs] | return []
  if ← tryDirectDecide g2 then return []
  if ← tryDirectOmega g2 then return []
  setGoals [g2]; try runCloseExhaustiveEnum catch _ => pure ()
  (← getGoals).filterM fun g3 => return !(← tryDirectDecide g3)

private def runStyleReduce (view : Ident) : TacticM Unit := do
  runSplitFiniteEnums
  forEachGoal fun g0 => do
    if (← g0.withContext (instantiateMVars (← g0.getType))).isFalse then return
    discard <| tryTac `(tactic| simp only [$view:ident]); runSplitFiniteEnums
    forEachGoal fun g1 => do
      if (← g1.withContext (instantiateMVars (← g1.getType))).isFalse then return
      runUnfoldViewHelpers; discard <| tryTac `(tactic| first | rfl | ((repeat' split); all_goals rfl; done) | skip)
      if (← getGoals).isEmpty then return
      try
        if let g :: rest ← getGoals then
          let env ← getEnv; let used ← collectGoalConsts g false
          let ctx ← mkDynamicSimpCtx (styleReduceOptNames.filter fun n => env.contains n && used.contains n) (some ("styleReduceCore", styleReduceCoreNames)) (withEqns := false)
          setGoals (match ← simpGoalOnly g ctx with | none => rest | some g' => g' :: rest)
      catch _ => pure ()
      if (← getGoals).isEmpty then return
      discard <| tryTac `(tactic| repeat' split)
      setGoals <| (← (← getGoals).mapM runStyleLeafClose).flatten

private def a11yDiagTable : Array (String × (Name → String)) := #[
  ("imgsHaveAlt",       fun v => s!"An `<img>` element in `{v}` is missing an `alt` attribute. Add `alt=\"...\"` (or `alt=\"\"` for decorative images)."),
  ("buttonsAccessible", fun v => s!"A `<button>` or `<a>` element in `{v}` has no accessible name in some branch. Provide non-empty text, `aria-label`, `aria-labelledby`, `title`, or a child `<img>` with non-empty `alt`."),
  ("validAriaRoles",    fun v => s!"An element in `{v}` has an unrecognized WAI-ARIA `role` attribute. Use a valid WAI-ARIA 1.2 role name."),
  ("labelsAssociated",  fun v => s!"A `<label>` element in `{v}` neither has a non-empty `for` attribute nor wraps a form control (`<input>`, `<select>`, `<textarea>`)."),
  ("noDuplicateIds",    fun v => s!"Two elements in `{v}` share the same `id` attribute in some branch. Ensure every non-empty `id` is unique."),
  ("headingsOrdered",   fun v => s!"Headings in `{v}` skip a level (e.g. `<h1>` directly to `<h3>`). Use sequential heading levels."),
  ("htmlHasLang",       fun v => s!"An `<html>` element in `{v}` is missing a non-empty `lang` attribute (e.g. `<html lang=\"en\">`)."),
  ("a11yValid",         fun v => s!"An accessibility check failed in `{v}` (check `<img alt>`, `<button>`/`<a>` accessible names, WAI-ARIA `role`, `<label>` association, unique `id`s, heading order, and `<html lang>`).")]

private def diagnoseStyling (predStr : String) (vName : Name) : String × String :=
  match a11yDiagTable.find? (fun (k, _) => predStr.contains k) with
  | some (_, mk) => ("Accessibility invariant", mk vName)
  | none => ("Styling invariant",
      if predStr.contains "roleLacks" || predStr.contains "tagLacks" then s!"A matching element in `{vName}` carries a forbidden style class in some branch. Remove that style from the matching element or guard it so it cannot apply there."
      else if predStr.contains "exactlyOne" then s!"In some branch of `{vName}`, either none or more than one of the listed roles carries the active style, a role is missing the inactive style, or one of the roles is not rendered."
      else if (predStr.contains "hasRole" || predStr.contains "hasTag") && !(predStr.contains "roleHas" || predStr.contains "tagHas") then s!"No element with the required `role`/tag is rendered in some branch of `{vName}`. Check every conditional branch of `{vName}`."
      else s!"Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `{vName}`.")

private def runDischargeStyling (view nm : Ident) (predLit : StrLit) : TacticM Unit := do
  evalTactic (← `(tactic| (intro m; try intro _qed_h_assume)))
  withMainContext do
    for d in (← getLCtx) do
      if d.userName == `_qed_h_assume then if let .const c _ := (← instantiateMVars d.type).getAppFn then discard <| tryTac `(tactic| simp only [$(mkIdent c):ident] at *)
    if let some (_, lhs, _) := (← instantiateMVars (← getMainTarget)).eq? then
      let (fn, args) := (lhs.getAppFn, lhs.getAppArgs)
      if (fn.isConstOf ``Qed.roleHasOneOf || fn.isConstOf ``Qed.tagHasOneOf) && args.size == 4 then
        let chk := mkIdent (if fn.isConstOf ``Qed.roleHasOneOf then ``Qed.hasRole else ``Qed.hasTag)
        evalTactic (← `(tactic| (suffices $chk $(← PrettyPrinter.delab args[1]!) ($view m) = true ∧ _ from this.2; constructor)))
  withOptions (fun o => maxRecDepth.set o (max (maxRecDepth.get o) 16384)) do forEachGoal fun _ => runStyleReduce view
  let predStr := predLit.getString; let (label, diagnosis) := diagnoseStyling predStr view.getId
  Qed.Diag.throwUnsolvedGoals m!"{label} `{nm.getId}` failed in `{view.getId}`:\n  • `{predStr}` does not hold in every state"
    m!"\n\nHint: {diagnosis}" (ref? := some nm)
    (formatGoal? := some fun g => g.withContext do
      let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
      return if s == "False" || s == "false = true" then none else some s!"  • view must satisfy:  {s}")

elab "qedStyleReduce " view:ident : tactic => runStyleReduce view
elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic => runDischargeStyling view nm predLit

syntax (name := invariantView) "invariant " ident " : " qedExpr,+ " holds_in " ident (" assuming " qedExpr)? (" := " term)? : command

open Lean Elab Command in
elab_rules : command
  | `(invariant $name:ident : $preds:qedExpr,* holds_in $view:ident $[assuming $assumeE:qedExpr]? $[ := $pf:term]?) => do
    let rawPreds := preds.getElems
    let p :: ps := (← rawPreds.mapM fun p => liftMacroM (Qed.Lang.lowerSimpleQedExpr .val p)).toList | throwErrorAt name "empty view invariant"
    let pred ← ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
    let predStr := String.intercalate ", " (rawPreds.toList.map fun p => (p.raw.reprint.getD "this rule").trimmed)
    let prop ← match assumeE with
      | some a =>
          let uA := Qed.Lang.unwrapParens1 a.raw
          let aT ← liftMacroM (Qed.Lang.lowerSimpleQedExpr (if uA.getKind == ``Qed.Lang.qedLam1 || uA.getKind == ``Qed.Lang.qedLamN then .propInv else .val) a)
          let P ← if aT.raw.isIdent then try liftTermElabM (extractInvPred ⟨aT.raw⟩) catch _ => pure aT else pure aT
          `(∀ m, ($P) m → ($pred) ($view m) = true)
      | none => `(∀ m, ($pred) ($view m) = true)
    match pf with
    | some p => elabCommand (← `(theorem $name:ident : $prop := $p))
    | none   => elabCommand (← `(set_option linter.unusedSimpArgs false in theorem $name:ident : $prop := by qedDischargeStyling $view $name $(Syntax.mkStrLit predStr)))

end Qed
