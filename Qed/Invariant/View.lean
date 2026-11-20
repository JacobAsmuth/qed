import Qed.Invariant.Predicates
import Qed.Invariant.State

namespace Qed

open Lean Elab Tactic

elab "qedUnfoldViewHelpers" : tactic =>
  -- Leave keyed component `.view` intact so `for_each … holds_in` can match the child contract.
  qedUnfoldHelperLoop 6 fun env n =>
    return qedIsHelper env n &&
      !(n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf)) &&
      (← getProjectionFnInfo? n).isNone

elab "qedCloseExhaustiveEnum" : tactic => withMainContext do
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

elab "qedSplitFiniteEnums" : tactic => do
  for _ in [0:2] do
    let gs ← getGoals
    if gs.isEmpty then return
    let mut progress := false
    let mut nextGoals : List MVarId := []
    for g in gs do
      let res ← g.withContext do
        let tgt ← instantiateMVars (← g.getType)
        if !tgt.hasFVar then
          try
            setGoals [g]
            evalTactic (← `(tactic| rfl))
            return some (← getGoals)
          catch _ => pure ()
        if let some e ← findFiniteEnumExpr (← getEnv) tgt then
          try
            setGoals [g]
            if e.isFVar then
              evalTactic (← `(tactic| cases $(mkIdent (← e.fvarId!.getDecl).userName):ident))
            else
              let stx ← PrettyPrinter.delab e
              evalTactic (← `(tactic| (generalize $stx:term = _qed_enum_x at *; cases _qed_enum_x)))
            return some (← getGoals)
          catch _ => pure ()
        return none
      match res with
      | some gs' => progress := true; nextGoals := nextGoals ++ gs'
      | none     => nextGoals := nextGoals ++ [g]
    setGoals nextGoals
    if !progress then break
  -- Close any newly-ground goals by `rfl` (or immediately reduce false ground Bool goals to `False`).
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    let gs' ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      if !tgt.hasFVar then
        try setGoals [g]; evalTactic (← `(tactic| rfl)); return (← getGoals) catch _ => pure ()
        if let some (_, lhs, rhs) := tgt.eq? then
          if rhs.isConstOf ``Bool.true then
            try
              let lhsStx ← PrettyPrinter.delab lhs
              setGoals [g]
              evalTactic (← `(tactic| (have _qed_gf : $lhsStx = false := rfl; rw [_qed_gf]; simp only [Bool.false_eq_true])))
              return (← getGoals)
            catch _ => pure ()
      return [g]
    rem := rem ++ gs'
  setGoals rem

elab "qedSkipIfFalse" tac:tactic : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isFalse then return
  evalTactic tac

syntax "qedStyleReduce " ident : tactic
macro_rules
  | `(tactic| qedStyleReduce $view:ident) =>
    `(tactic|
      (qedSplitFiniteEnums;
       all_goals qedSkipIfFalse (
         try simp only [$view:ident];
         qedSplitFiniteEnums;
         all_goals qedSkipIfFalse (
           qedUnfoldViewHelpers;
           simp only [Qed.roleHasOneOf, Qed.tagHasOneOf, Qed.roleHas, Qed.roleHasOnly,
             Qed.roleLacks, Qed.tagLacks, Qed.roleHasAll, Qed.tagHas, Qed.noConflictingStyles,
             Qed.hasRole, Qed.hasTag, Qed.both, Qed.either, Qed.exactlyOne,
             Qed.allRolesOff, Qed.exactlyOneOf, Qed.exactlyOneOf.go, Qed.hasOneClass,
             Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
             Qed.View.render, Qed.View.renderEach, Qed.View.mapScope, Qed.View.mapScopeEach,
             Qed.VAttr.eval, Qed.VAttr.mapScope, Qed.View.showIf, Qed.View.ofHtml,
             Qed.V.el, Qed.V.text, Qed.V.dyn, Qed.V.ifElse, Qed.V.showIf, Qed.V.static, Qed.V.dynNode,
             Qed.V.memo, Qed.V.render_forEach, Qed.View.isDyn, Qed.View.memo,
             Qed.ForEachItems.toList_array, Qed.ForEachItems.toList_list, Qed.ForEachItems.toArray, Qed.mapList_eq,
             Qed.text, Qed.lazy, Qed.el, Qed.link, Qed.linkTo,
             Qed.Attr.empty, Qed.Html.ofOption, Qed.toString_string, Qed.withKey,
             Qed.Html.map, Qed.Html.mapChildren, Qed.Attr.map,
             Qed.cls, Qed.attr, Qed.role, Qed.on,
             Qed.onValue, Qed.onClick, Qed.onInput, Qed.onChange, Qed.onCheck, Qed.onKeydown,
             Qed.onKeyup, Qed.onSubmit, Qed.onBlur, Qed.onFocus, Qed.onDoubleClick, Qed.onMouseDown,
             Qed.onMouseUp, Qed.key, Qed.value, Qed.placeholder, Qed.name, Qed.href, Qed.ToHref.toHref,
             Qed.src, Qed.action, Qed.alt, Qed.title, Qed.style, Qed.inlineStyle, Qed.styleVars, Qed.type', Qed.disabled, Qed.required,
             Qed.checked, Qed.readOnly,
             Qed.Lang.QedVal.val_id, Qed.Lang.QedSeqLit.ofList_array, Qed.Lang.QedSeqLit.ofList_list,
             Qed.Lang.QedMem.mem_array, Qed.Lang.QedMem.mem_list, Qed.Lang.QedMem.mem_string,
             Qed.Lang.QedMemProp.memProp_array, Qed.Lang.QedMemProp.memProp_list, Qed.Lang.QedMemProp.memProp_string];
           repeat' split;
           all_goals (first
             | rfl
             | (simp_all only [Qed.everyElement, Qed.everyElementL,
                               Qed.attrClasses, Qed.attrRole, Qed.hasOneClass,
                               Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
                               Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
                               Bool.not_true, Bool.not_false, Bool.and_eq_true, Bool.or_eq_true,
                               Bool.false_eq_true, ite_true, ite_false, dite_true, dite_false,
                               List.all_cons, List.all_nil, List.any_cons, List.any_nil,
                               beq_self_eq_true, eq_self, decide_true, decide_false];
                (try rfl); done)
             | (simp_all [Qed.everyElement, Qed.everyElementL,
                          Qed.attrClasses, Qed.attrRole, Qed.hasOneClass];
                try decide;
                try omega;
                try qedCloseExhaustiveEnum)
             | decide)))))

syntax (name := invariantView)
  "invariant " ident " : " qedExpr,+ " holds_in " ident (" assuming " qedExpr)? (" := " term)? : command

elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic => do
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
    evalTactic (← `(tactic| all_goals qedStyleReduce $view))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut details : Array String := #[]
    for g in goals do
      let line ← g.withContext do
        let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
        pure (if s == "False" || s == "false = true" then "" else s!"  • view must satisfy:  {s}")
      if !line.isEmpty && !details.contains line then
        details := details.push line
    let extraBody := if details.isEmpty then "" else "\n" ++ String.intercalate "\n" details.toList
    let predStr := predLit.getString
    let vName := view.getId
    let diagnosis :=
      if predStr.contains "roleLacks" || predStr.contains "tagLacks" then
        s!"A matching element in `{vName}` carries a forbidden style class in some branch. Remove that style from the matching element or guard it so it cannot apply there."
      else if predStr.contains "exactlyOne" then
        s!"In some branch of `{vName}`, either none or more than one of the listed roles carries the active style, a role is missing the inactive style, or one of the roles is not rendered."
      else if (predStr.contains "hasRole" || predStr.contains "hasTag") &&
              !(predStr.contains "roleHas" || predStr.contains "tagHas") then
        s!"No element with the required `role`/tag is rendered in some branch of `{vName}`. Check every conditional branch of `{vName}`."
      else
        s!"Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `{vName}`."
    throwErrorAt nm m!"Styling invariant `{nm.getId}` failed in `{vName}`:\n  • `{predStr}` does not hold in every state{extraBody}\n\nHint: {diagnosis}"

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
