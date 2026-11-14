import Qed.Invariant.Predicates
import Qed.Invariant.State

namespace Qed

open Lean Elab Tactic

elab "qedUnfoldViewHelpers" : tactic => do
  for _ in [0:6] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    -- Leave keyed component `.view` intact so `for_each … holds_in` can match the child contract.
    let present ← ((← instantiateMVars (← getMainTarget)).getUsedConstants.filter fun n =>
        qedIsHelper env n && !(n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf))).filterM
      fun n => return (← getProjectionFnInfo? n).isNone
    if present.isEmpty then return
    let lemmas ← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    try evalTactic (← `(tactic| simp only [$[$lemmas],*])) catch _ => return

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

syntax "qedStyleReduce " ident : tactic
macro_rules
  | `(tactic| qedStyleReduce $view:ident) =>
    `(tactic|
      (try simp only [$view:ident];
       qedUnfoldViewHelpers;
       simp only [Qed.roleHasOneOf, Qed.tagHasOneOf, Qed.roleHas, Qed.roleHasOnly,
         Qed.hasRole, Qed.hasTag, Qed.both, Qed.either, Qed.exactlyOne,
         Qed.allRolesOff, Qed.exactlyOneOf, Qed.exactlyOneOf.go, Qed.hasOneClass,
         Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
         Qed.View.render, Qed.View.renderEach, Qed.View.mapScope, Qed.View.mapScopeEach,
         Qed.VAttr.eval, Qed.VAttr.mapScope, Qed.View.showIf, Qed.View.ofHtml,
         Qed.V.el, Qed.V.text, Qed.V.dyn, Qed.V.ifElse, Qed.V.showIf, Qed.V.static, Qed.V.dynNode,
         Qed.text, Qed.lazy, Qed.el, Qed.link, Qed.linkTo, Qed.styleSheet, Qed.theme,
         Qed.cls, Qed.attr, Qed.role, Qed.rawHtml, Qed.on,
         Qed.onValue, Qed.onClick, Qed.onInput, Qed.onChange, Qed.onCheck, Qed.onKeydown,
         Qed.onKeyup, Qed.onSubmit, Qed.onBlur, Qed.onFocus, Qed.onDoubleClick, Qed.onMouseDown,
         Qed.onMouseUp, Qed.key, Qed.value, Qed.placeholder, Qed.name, Qed.href, Qed.ToHref.toHref,
         Qed.src, Qed.alt, Qed.title, Qed.style, Qed.type', Qed.disabled, Qed.required,
         Qed.checked, Qed.readOnly];
       repeat' split;
       all_goals (first
         | rfl
         | decide
         | (simp_all [Qed.everyElement, Qed.everyElementL,
                      Qed.attrClasses, Qed.attrRole, Qed.hasOneClass];
            try decide;
            try omega;
            try qedCloseExhaustiveEnum))))

syntax (name := invariantView)
  "invariant " ident " : " term " holds_in " ident (" assuming " term:max)? (" := " term)? : command

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
  evalTactic (← `(tactic| all_goals qedStyleReduce $view))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        let s := (fmt.pretty.replace "✝" "").trimmed
        pure (if s == "False" then m!"" else m!"\n  • the view still has to satisfy:  {s}"))
    throwErrorAt nm m!"styling invariant `{nm.getId}` doesn't hold for every model, \
      `{predLit.getString}` is false for some `{view.getId} m`.{body}\n\nSome element the rule \
      constrains isn't carrying one of the required style classes (or no element with that role/tag \
      is rendered). Check that the `role`/tag it matches exists and gets one of the styles passed \
      to `roleHasOneOf`/`tagHasOneOf` in every branch of `{view.getId}`. If the view is routed \
      through `App.view`/`View.render` rather than a plain `Model → Html`, prove it with:  \
      invariant {nm.getId} : … holds_in {view.getId} := by …"

open Lean Elab Command in
elab_rules : command
  | `(invariant $name:ident : $pred holds_in $view:ident $[assuming $assumeT]? $[ := $pf:term]?) => do
    let predStr := ((pred.raw.reprint).getD "this rule").trimmed
    let prop ← match assumeT with
      | some a =>
          let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
          `(∀ m, ($P) m → ($pred) ($view m) = true)
      | none => `(∀ m, ($pred) ($view m) = true)
    match pf with
    | some p => elabCommand (← `(theorem $name:ident : $prop := $p))
    | none   => elabCommand (← `(
        set_option linter.unusedSimpArgs false in
        theorem $name:ident : $prop := by
          qedDischargeStyling $view $name $(Syntax.mkStrLit predStr)))

end Qed
