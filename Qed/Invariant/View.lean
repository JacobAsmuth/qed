import Qed.Invariant.Predicates
import Qed.Runtime.Verify

namespace Qed

open Lean Elab Tactic Qed.Verify.Core

private def runUnfoldViewHelpers : TacticM Unit :=
  -- Leave keyed component `.view` intact so `for_each … holds_in` can match the child contract.
  qedUnfoldHelperLoop 6 fun env n =>
    return qedIsHelper env n &&
      !(n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf)) &&
      (← getProjectionFnInfo? n).isNone

private def runCloseExhaustiveEnum : TacticM Unit := withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let inner := match ty with | .app (.const ``Not _) t => t | t => t
    let lhs? := match inner with
      | .app (.app (.app (.const ``Eq _) _) (.app (.app (.app (.app (.const ``BEq.beq _) _) _) lhs) _)) _ => some lhs
      | .app (.app (.app (.const ``Eq _) _) lhs) _ => some lhs
      | _ => none
    if let some lhs := lhs? then
      try
        let lhsStx ← PrettyPrinter.delab lhs
        evalTactic (← `(tactic| (generalize $lhsStx:term = _qed_enum_x at *; cases _qed_enum_x <;> (simp_all; try decide); done)))
        return
      catch _ => pure ()

private def isSmallNullaryEnum (env : Environment) (ty : Expr) (allowBool : Bool := false) : Bool :=
  match ty.getAppFn with
  | .const nm _ =>
    if nm == ``Unit || nm == ``PUnit || (!allowBool && nm == ``Bool) then false
    else match env.find? nm with
    | some (.inductInfo iv) =>
      iv.numParams == 0 && iv.numIndices == 0 && 2 ≤ iv.ctors.length && iv.ctors.length ≤ 8 &&
      iv.ctors.all fun c => match env.find? c with
        | some (.ctorInfo ci) => ci.numFields == 0
        | _ => false
    | _ => false
  | _ => false

private partial def findFiniteEnumExpr (env : Environment) (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars then return none
  if !e.isConst && !(e.getAppFn.constName?.any env.isConstructor) then
    if isSmallNullaryEnum env (← Meta.inferType e) (allowBool := e.isFVar) then
      return some e
  match e with
  | .app f a =>
    if let some r ← findFiniteEnumExpr env a then return some r
    findFiniteEnumExpr env f
  | .letE _ _ v b _ =>
    if let some r ← findFiniteEnumExpr env v then return some r
    if !b.hasLooseBVars then findFiniteEnumExpr env b else return none
  | _ => return none

/-- Evaluates a ground `Bool` equality `lhs = true` ONCE via `Meta.whnf`, closing if `true`
    or replacing the goal with `False` if `false` so subsequent tactics skip immediately. -/
private def evalGroundBoolGoal (g : MVarId) (tgt : Expr) : TacticM (Option (List MVarId)) :=
  g.withContext do
    if let some (_, lhs, rhs) := tgt.eq? then
      if rhs.isConstOf ``Bool.true then
        let v ← try Meta.whnf lhs catch _ => pure lhs
        if v.isConstOf ``Bool.true then
          g.assign (← Meta.mkEqRefl (mkConst ``Bool.true))
          return some []
        if v.isConstOf ``Bool.false then
          let gf ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
          g.assign (mkApp2 (mkConst ``False.elim [Level.zero]) tgt gf)
          return some [gf.mvarId!]
        return none
    try
      setGoals [g]
      evalTactic (← `(tactic| rfl))
      return some (← getGoals)
    catch _ => return none

private def runSplitFiniteEnums : TacticM Unit := do
  let mut checkedGround : Std.HashSet MVarId := {}
  for _ in [0:2] do
    let gs ← getGoals
    if gs.isEmpty then return
    let mut progress := false
    let mut nextGoals : List MVarId := []
    for g in gs do
      let tgt ← g.withContext do instantiateMVars (← g.getType)
      if tgt.isFalse then
        nextGoals := nextGoals ++ [g]
        continue
      if !tgt.hasFVar && !checkedGround.contains g then
        checkedGround := checkedGround.insert g
        if let some gs' ← evalGroundBoolGoal g tgt then
          progress := true
          nextGoals := nextGoals ++ gs'
          continue
      let splitRes? ← g.withContext do
        if let some e ← findFiniteEnumExpr (← getEnv) tgt then
          try
            if e.isFVar then
              return some ((← g.cases e.fvarId!).toList.map (·.mvarId))
            else
              setGoals [g]
              let stx ← PrettyPrinter.delab e
              evalTactic (← `(tactic| (generalize $stx:term = _qed_enum_x at *; cases _qed_enum_x)))
              return some (← getGoals)
          catch _ => pure ()
        return none
      match splitRes? with
      | some gs' => progress := true; nextGoals := nextGoals ++ gs'
      | none     => nextGoals := nextGoals ++ [g]
    setGoals nextGoals
    if !progress then break
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    let tgt ← g.withContext do instantiateMVars (← g.getType)
    if !tgt.isFalse && !tgt.hasFVar && !checkedGround.contains g then
      if let some gs' ← evalGroundBoolGoal g tgt then
        rem := rem ++ gs'
        continue
    rem := rem ++ [g]
  setGoals rem

private def a11yReduceNames : Array Name := #[
  ``Qed.Html.a11yValid, ``Qed.Html.imgsHaveAlt, ``Qed.Html.imgsHaveAltList,
  ``Qed.Html.buttonsAccessible, ``Qed.Html.buttonsAccessibleList,
  ``Qed.Html.elemHasAccessibleName, ``Qed.Html.hasAccessibleNameChild, ``Qed.Html.hasAccessibleNameChildren,
  ``Qed.Html.validAriaRoles, ``Qed.Html.validAriaRolesList, ``Qed.attrsValidAriaRoles,
  ``Qed.Html.labelsAssociated, ``Qed.Html.labelsAssociatedList,
  ``Qed.Html.containsFormControl, ``Qed.Html.containsFormControlList, ``Qed.isFormControlTag,
  ``Qed.Html.noDuplicateIds, ``Qed.Html.collectIds, ``Qed.Html.collectIdsList,
  ``Qed.Html.headingsOrdered, ``Qed.Html.collectHeadings, ``Qed.Html.collectHeadingsList,
  ``Qed.Html.htmlHasLang, ``Qed.Html.htmlHasLangList,
  ``Qed.attrValue, ``Qed.hasAttr, ``Qed.hasNonBlankAttr
]

private def styleLeafCoreNames : Array Name := #[
  ``Qed.everyElement, ``Qed.everyElementL, ``Qed.attrClasses, ``Qed.attrRole, ``Qed.hasOneClass
]

private def styleReduceCoreNames : Array Name := #[
  ``Qed.roleHasOneOf, ``Qed.tagHasOneOf, ``Qed.roleHas, ``Qed.roleHasOnly,
  ``Qed.roleLacks, ``Qed.tagLacks, ``Qed.roleHasAll, ``Qed.tagHas, ``Qed.noConflictingStyles,
  ``Qed.hasRole, ``Qed.hasTag, ``Qed.both, ``Qed.either, ``Qed.exactlyOne,
  ``Qed.allRolesOff, ``Qed.exactlyOneOf, ``Qed.exactlyOneOf.go
] ++ styleLeafCoreNames ++ a11yReduceNames ++ #[
  ``Qed.Html.imgsHaveAlt_map, ``Qed.Html.buttonsAccessible_map, ``Qed.Html.validAriaRoles_map,
  ``Qed.Html.labelsAssociated_map, ``Qed.Html.noDuplicateIds_map, ``Qed.Html.headingsOrdered_map,
  ``Qed.Html.htmlHasLang_map, ``Qed.Html.a11yValid_map,
  ``Qed.Html.map, ``Qed.Html.mapChildren, ``Qed.Attr.map,
  ``Qed.Lang.QedVal.val_id, ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list,
  ``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string,
  ``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string
]

private def styleReduceOptNames : Array Name := #[
  `Qed.View.render, `Qed.View.renderEach, `Qed.View.mapScope, `Qed.View.mapScopeEach,
  `Qed.VAttr.eval, `Qed.VAttr.mapScope, `Qed.View.showIf, `Qed.View.ofHtml,
  `Qed.V.el, `Qed.V.text, `Qed.V.dyn, `Qed.V.ifElse, `Qed.V.showIf, `Qed.V.static, `Qed.V.dynNode,
  `Qed.V.memo, `Qed.V.render_forEach, `Qed.View.isDyn, `Qed.View.memo,
  `Qed.Attr.empty, `Qed.Html.ofOption, `Qed.toString_string, `Qed.withKey, `Qed.ToHref.toHref
] ++ Qed.qedForEachHelperNames ++ Qed.qedHtmlHelperNames

private def styleLeafFastNames : Array Name :=
  styleLeafCoreNames ++ boolConstSimpNames ++ #[
    ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.false_eq_true,
    ``List.all_cons, ``List.all_nil, ``List.any_cons, ``List.any_nil,
    ``beq_self_eq_true, ``eq_self, ``decide_true, ``decide_false
  ]

private def runStyleSimpPass : TacticM Unit := do
  let g :: rest ← getGoals | return
  let env ← getEnv
  let used ← collectGoalConsts g false
  let optPresent := styleReduceOptNames.filter fun n => env.contains n && used.contains n
  let ctx ← mkDynamicSimpCtx optPresent (some ("styleReduceCore", styleReduceCoreNames)) (withEqns := false)
  match ← simpGoalOnly g ctx with
  | none    => setGoals rest
  | some g' => setGoals (g' :: rest)

private def isUnprovableFalseGoal (g : MVarId) : MetaM Bool := g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let isFalseEq := tgt.isFalse || match tgt.eq? with
    | some (_, lhs, rhs) => lhs.consumeMData.isConstOf ``Bool.false && rhs.consumeMData.isConstOf ``Bool.true
    | none => false
  if !isFalseEq then return false
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && (← Meta.isProp decl.type) then return false
  return true

private def runStyleLeafClose (g : MVarId) : TacticM (List MVarId) := do
  let s0 ← saveState
  try g.refl; return [] catch _ => restoreState s0
  let (fastCtx, _) ← mkCachedSimpCtx "styleLeafFast" styleLeafFastNames
  let some g1 ← trySimpAll g fastCtx | return []
  let s1 ← saveState
  try g1.refl; return [] catch _ => restoreState s1
  if ← isUnprovableFalseGoal g1 then return [g1]
  let fullCtx ← mkSimpCtxWithBase (styleLeafCoreNames ++ a11yReduceNames) (cacheKey? := some "styleLeafFull")
  let some g2 ← trySimpAll g1 fullCtx #[← Meta.Simp.getSimprocs] | return []
  if ← tryDirectDecide g2 then return []
  if ← tryDirectOmega g2 then return []
  setGoals [g2]
  try runCloseExhaustiveEnum catch _ => pure ()
  let mut rem : List MVarId := []
  for g3 in (← getGoals) do
    if ← tryDirectDecide g3 then continue
    rem := rem ++ [g3]
  return rem

private def runStyleReduce (view : Ident) : TacticM Unit := do
  runSplitFiniteEnums
  let gs0 ← getGoals
  let mut rem : List MVarId := []
  for g0 in gs0 do
    if (← g0.withContext (instantiateMVars (← g0.getType))).isFalse then
      rem := rem ++ [g0]; continue
    setGoals [g0]
    try evalTactic (← `(tactic| simp only [$view:ident])) catch _ => pure ()
    runSplitFiniteEnums
    for g1 in (← getGoals) do
      if (← g1.withContext (instantiateMVars (← g1.getType))).isFalse then
        rem := rem ++ [g1]; continue
      setGoals [g1]
      runUnfoldViewHelpers
      try evalTactic (← `(tactic| first | rfl | ((repeat' split); all_goals rfl; done) | skip)) catch _ => pure ()
      if (← getGoals).isEmpty then continue
      try runStyleSimpPass catch _ => pure ()
      if (← getGoals).isEmpty then continue
      try evalTactic (← `(tactic| repeat' split)) catch _ => pure ()
      for g2 in (← getGoals) do
        rem := rem ++ (← runStyleLeafClose g2)
  setGoals rem

private def a11yDiagTable : Array (String × (Name → String)) := #[
  ("imgsHaveAlt",       fun v => s!"An `<img>` element in `{v}` is missing an `alt` attribute. Add `alt=\"...\"` (or `alt=\"\"` for decorative images)."),
  ("buttonsAccessible", fun v => s!"A `<button>` or `<a>` element in `{v}` has no accessible name in some branch. Provide non-empty text, `aria-label`, `aria-labelledby`, `title`, or a child `<img>` with non-empty `alt`."),
  ("validAriaRoles",    fun v => s!"An element in `{v}` has an unrecognized WAI-ARIA `role` attribute. Use a valid WAI-ARIA 1.2 role name."),
  ("labelsAssociated",  fun v => s!"A `<label>` element in `{v}` neither has a non-empty `for` attribute nor wraps a form control (`<input>`, `<select>`, `<textarea>`)."),
  ("noDuplicateIds",    fun v => s!"Two elements in `{v}` share the same `id` attribute in some branch. Ensure every non-empty `id` is unique."),
  ("headingsOrdered",   fun v => s!"Headings in `{v}` skip a level (e.g. `<h1>` directly to `<h3>`). Use sequential heading levels."),
  ("htmlHasLang",       fun v => s!"An `<html>` element in `{v}` is missing a non-empty `lang` attribute (e.g. `<html lang=\"en\">`)."),
  ("a11yValid",         fun v => s!"An accessibility check failed in `{v}` (check `<img alt>`, `<button>`/`<a>` accessible names, WAI-ARIA `role`, `<label>` association, unique `id`s, heading order, and `<html lang>`).")
]

private def diagnoseStyling (predStr : String) (vName : Name) : String × String :=
  let label := if a11yDiagTable.any (fun (k, _) => predStr.contains k)
    then "Accessibility invariant" else "Styling invariant"
  let diag := match a11yDiagTable.find? (fun (k, _) => predStr.contains k) with
    | some (_, mk) => mk vName
    | none =>
        if predStr.contains "roleLacks" || predStr.contains "tagLacks" then
          s!"A matching element in `{vName}` carries a forbidden style class in some branch. Remove that style from the matching element or guard it so it cannot apply there."
        else if predStr.contains "exactlyOne" then
          s!"In some branch of `{vName}`, either none or more than one of the listed roles carries the active style, a role is missing the inactive style, or one of the roles is not rendered."
        else if (predStr.contains "hasRole" || predStr.contains "hasTag") &&
                !(predStr.contains "roleHas" || predStr.contains "tagHas") then
          s!"No element with the required `role`/tag is rendered in some branch of `{vName}`. Check every conditional branch of `{vName}`."
        else
          s!"Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `{vName}`."
  (label, diag)

private def runDischargeStyling (view nm : Ident) (predLit : StrLit) : TacticM Unit := do
  evalTactic (← `(tactic| (intro m; try intro _qed_h_assume)))
  withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.userName == `_qed_h_assume then
        if let .const c _ := (← instantiateMVars ldecl.type).getAppFn then
          try evalTactic (← `(tactic| simp only [$(mkIdent c):ident] at *)) catch _ => pure ()
    if let some (_, lhs, _) := (← instantiateMVars (← getMainTarget)).eq? then
      let (fn, args) := (lhs.getAppFn, lhs.getAppArgs)
      if (fn.isConstOf ``Qed.roleHasOneOf || fn.isConstOf ``Qed.tagHasOneOf) && args.size == 4 then
        let chk := mkIdent (if fn.isConstOf ``Qed.roleHasOneOf then ``Qed.hasRole else ``Qed.hasTag)
        evalTactic (← `(tactic| (suffices $chk $(← PrettyPrinter.delab args[1]!) ($view m) = true ∧ _ from this.2; constructor)))
  withOptions (fun o => maxRecDepth.set o (max (maxRecDepth.get o) 16384)) do
    let gs ← getGoals
    let mut rem : List MVarId := []
    for g in gs do
      setGoals [g]
      runStyleReduce view
      rem := rem ++ (← getGoals)
    setGoals rem
  let predStr := predLit.getString
  let vName := view.getId
  let (label, diagnosis) := diagnoseStyling predStr vName
  Qed.Diag.throwUnsolvedGoals
    m!"{label} `{nm.getId}` failed in `{vName}`:\n  • `{predStr}` does not hold in every state"
    m!"\n\nHint: {diagnosis}"
    (ref? := some nm)
    (formatGoal? := some fun g => g.withContext do
      let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
      return if s == "False" || s == "false = true" then none else some s!"  • view must satisfy:  {s}")

elab "qedStyleReduce " view:ident : tactic => runStyleReduce view
elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic =>
  runDischargeStyling view nm predLit

syntax (name := invariantView)
  "invariant " ident " : " qedExpr,+ " holds_in " ident (" assuming " qedExpr)? (" := " term)? : command

open Lean Elab Command in
elab_rules : command
  | `(invariant $name:ident : $preds:qedExpr,* holds_in $view:ident $[assuming $assumeE:qedExpr]? $[ := $pf:term]?) => do
    let rawPreds := preds.getElems
    let loweredPreds ← rawPreds.mapM fun p => liftMacroM (Qed.Lang.lowerSimpleQedExpr .val p)
    let pred ← match loweredPreds.toList with
      | [p] => pure p
      | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
      | [] => throwErrorAt name "empty view invariant"
    let predStr := String.intercalate ", " (rawPreds.toList.map fun p => (p.raw.reprint.getD "this rule").trimmed)
    let prop ← match assumeE with
      | some a =>
          let uA := Qed.Lang.unwrapParens1 a.raw
          let aMode := if uA.getKind == ``Qed.Lang.qedLam1 || uA.getKind == ``Qed.Lang.qedLamN then .propInv else .val
          let aT ← liftMacroM (Qed.Lang.lowerSimpleQedExpr aMode a)
          let P ← if aT.raw.isIdent then try liftTermElabM (extractInvPred ⟨aT.raw⟩) catch _ => pure aT else pure aT
          `(∀ m, ($P) m → ($pred) ($view m) = true)
      | none => `(∀ m, ($pred) ($view m) = true)
    match pf with
    | some p => elabCommand (← `(theorem $name:ident : $prop := $p))
    | none   => elabCommand (← `(
        set_option linter.unusedSimpArgs false in
        theorem $name:ident : $prop := by
          qedDischargeStyling $view $name $(Syntax.mkStrLit predStr)))

end Qed
