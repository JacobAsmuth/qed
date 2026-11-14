import Qed.View.Core
import Lean

namespace Qed

open Lean Meta Elab Tactic

private def strLitVal? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _                => none

private def boolVal? (e : Expr) : MetaM (Option Bool) := do
  let r ← whnf e
  if r.isConstOf ``Bool.true then return some true
  if r.isConstOf ``Bool.false then return some false
  return none

private def tagModeVal? (e : Expr) : MetaM (Option TagMode) := do
  let r ← whnf e
  if r.isConstOf ``TagMode.normal       then return some .normal
  if r.isConstOf ``TagMode.ulOl         then return some .ulOl
  if r.isConstOf ``TagMode.dl           then return some .dl
  if r.isConstOf ``TagMode.table        then return some .table
  if r.isConstOf ``TagMode.colgroup     then return some .colgroup
  if r.isConstOf ``TagMode.tableSection then return some .tableSection
  if r.isConstOf ``TagMode.tableRow     then return some .tableRow
  if r.isConstOf ``TagMode.select       then return some .select
  if r.isConstOf ``TagMode.optgroup     then return some .optgroup
  if r.isConstOf ``TagMode.option       then return some .option
  if r.isConstOf ``TagMode.rawStyle     then return some .rawStyle
  if r.isConstOf ``TagMode.textarea     then return some .textarea
  if r.isConstOf ``TagMode.svg          then return some .svg
  return none

private def htmlCtxVal? (e : Expr) : MetaM (Option HtmlCtx) := do
  if e.hasFVar || e.hasMVar then return none
  let r ← whnf e
  if !r.isAppOfArity ``HtmlCtx.mk 4 then return none
  let args := r.getAppArgs
  let some mode   ← tagModeVal? args[0]! | return none
  let some inP    ← boolVal? args[1]!    | return none
  let some inter  ← boolVal? args[2]!    | return none
  let some inForm ← boolVal? args[3]!    | return none
  return some { mode, inP, interactive := inter, inForm }

private def tagModeExpr : TagMode → Expr
  | .normal       => mkConst ``TagMode.normal
  | .ulOl         => mkConst ``TagMode.ulOl
  | .dl           => mkConst ``TagMode.dl
  | .table        => mkConst ``TagMode.table
  | .colgroup     => mkConst ``TagMode.colgroup
  | .tableSection => mkConst ``TagMode.tableSection
  | .tableRow     => mkConst ``TagMode.tableRow
  | .select       => mkConst ``TagMode.select
  | .optgroup     => mkConst ``TagMode.optgroup
  | .option       => mkConst ``TagMode.option
  | .rawStyle     => mkConst ``TagMode.rawStyle
  | .textarea     => mkConst ``TagMode.textarea
  | .svg          => mkConst ``TagMode.svg

private def htmlCtxExpr (c : HtmlCtx) : Expr :=
  mkApp4 (mkConst ``HtmlCtx.mk) (tagModeExpr c.mode) (toExpr c.inP) (toExpr c.interactive) (toExpr c.inForm)

dsimproc [simp] reduceStepHtmlCtx (stepHtmlCtx _ _) := fun e => do
  let args := e.getAppArgs
  if args.size != 2 then return .continue
  let some tag := strLitVal? args[1]! | return .continue
  let some ctx ← htmlCtxVal? args[0]! | return .continue
  match Qed.stepHtmlCtx ctx tag with
  | some next =>
      return .done (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) (htmlCtxExpr next))
  | none =>
      return .done (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``HtmlCtx))

dsimproc [simp] reduceIsVoidTag (isVoidTag _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.isVoidTag s))

dsimproc [simp] reduceIsSafeAttrName (isSafeAttrName _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.isSafeAttrName s))

dsimproc [simp] reduceIsUrlAttrName (isUrlAttrName _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.isUrlAttrName s))

dsimproc [simp] reduceIsSafeUrl (isSafeUrl _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.isSafeUrl s))

dsimproc [simp] reduceContainsCloseSeq (containsCloseSeq (String.toList _)) := fun e => do
  let some s := strLitVal? e.appArg!.appArg! | return .continue
  return .done (toExpr (Qed.containsCloseSeq s.toList))

dsimproc [simp] reduceTagBlocksDirectSpan (tagBlocksDirectSpan _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.tagBlocksDirectSpan s))

dsimproc [simp] reduceTagBlocksSpanSubtree (tagBlocksSpanSubtree _) := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (Qed.tagBlocksSpanSubtree s))

def qedLooksGenerated (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s =>
       ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion",
        "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg",
        "toJson", "fromJson"].contains s
         || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "inst"
   | _ => false)

def qedIsHelper (env : Environment) (n : Name) : Bool :=
  let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i]! | none => n
  ![`Init, `Std, `Lean, `Qed].contains mod.getRoot
    && (match env.find? n with | some (.defnInfo d) => !d.type.isConstOf ``Qed.Style | _ => false)
    && !qedLooksGenerated n

private def looksGeneratedForView (n : Name) : Bool :=
  qedLooksGenerated n ||
  (match n with
   | .str _ s =>
       ["formView", "keyOf", "update", "updateKeyed", "regs", "reg", "init"].contains s
   | _ => false)

private def mentionsViewType (ty : Expr) : Bool :=
  let ret := ty.getForallBody
  ret.getUsedConstants.any fun c =>
    c == ``Qed.Html || c == ``Qed.View || c == ``Qed.Attr || c == ``Qed.VAttr ||
    c == `Qed.Component

private def isUnfoldableUserDef (env : Environment) (viewOnly : Bool) (n : Name) : MetaM Bool := do
  if !qedIsHelper env n then return false
  if viewOnly && looksGeneratedForView n then return false
  if (← getProjectionFnInfo? n).isSome then return false
  match env.find? n with
  | some (.defnInfo d) =>
      if d.type.isConstOf ``Qed.Token || d.type.isConstOf ``Qed.Url ||
         d.type.isAppOfArity `Qed.Codec 1 || d.type.isConstOf `Qed.LocalDef ||
         d.type.isAppOfArity `Qed.App 2 || d.type.isAppOfArity `Qed.Dehydrate 1 then
        return false
      return !viewOnly || mentionsViewType d.type
  | _ => return false

private def viewFrameworkUnfolds (env : Environment) : Array Name :=
  let core := #[
    ``Html.valid, ``Html.validIn, ``Html.validListIn,
    ``Attr.validKeyValue,
    ``View.render, ``View.renderEach, ``View.renderSig, ``View.renderSigList,
    ``View.showIf, ``View.ofHtml, ``View.hasOpaque, ``View.hasOpaqueList,
    ``View.collectDyn, ``View.collectDynList, ``dynValGets,
    ``VAttr.eval, ``V.el, ``V.text, ``V.dyn, ``V.ifElse, ``V.showIf, ``V.static,
    ``V.dynNode, ``V.memo, ``V.forEach, ``V.bindAttr, ``V.dynAttr,
    ``V.onClick', ``V.onInput', ``V.onCheck', ``SoundMemo.ofLawful,
    ``Qed.text, ``Qed.lazy, ``Qed.el, ``Qed.link, ``Qed.linkTo, ``Qed.theme, ``Qed.styleSheet,
    ``Qed.cls, ``Qed.attr, ``Qed.role, ``Qed.on, ``Qed.onValue, ``Qed.onClick, ``Qed.onInput,
    ``Qed.onChange, ``Qed.onCheck, ``Qed.onKeydown, ``Qed.onKeyup, ``Qed.onSubmit,
    ``Qed.onBlur, ``Qed.onFocus, ``Qed.onDoubleClick, ``Qed.onMouseDown, ``Qed.onMouseUp,
    ``Qed.key, ``Qed.value, ``Qed.placeholder, ``Qed.name, ``Qed.href, ``Qed.src, ``Qed.action,
    ``Qed.alt, ``Qed.title, ``Qed.style, ``Qed.type', ``Qed.disabled, ``Qed.required,
    ``Qed.checked, ``Qed.readOnly
  ]
  let opt := #[
    `Qed.Component.render, `Qed.Component.each,
    `Qed.localMount, `Qed.localMountWith
  ].filter env.contains
  core ++ opt

elab "qedUnfoldForValidHtml" : tactic => do
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let target ← instantiateMVars (← getMainTarget)
    let present ← target.getUsedConstants.filterM (fun n => liftM (isUnfoldableUserDef env true n))
    if present.isEmpty then return
    let lemmas ← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    let ok ← try
        evalTactic (← `(tactic| simp only [$[$lemmas],*]))
        pure true
      catch _ => pure false
    unless ok do return

elab "qedProveValidHtmlCore" : tactic => do
  evalTactic (← `(tactic| intros))
  let env ← getEnv
  let fw ← (viewFrameworkUnfolds env).mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  for _ in [0:6] do
    if (← getGoals).isEmpty then return
    let before ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    evalTactic (← `(tactic| qedUnfoldForValidHtml))
    if (← getGoals).isEmpty then return
    try evalTactic (← `(tactic| simp [$[$fw],*])) catch _ => pure ()
    if (← getGoals).isEmpty then return
    try evalTactic (← `(tactic| (split <;> try simp [$[$fw],*]))) catch _ => pure ()
    if (← getGoals).isEmpty then return
    let after ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    if before == after then break
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic| all_goals (first | rfl | decide))) catch _ => pure ()

elab "qedProveValidHtml" : tactic => do
  evalTactic (← `(tactic| qedProveValidHtmlCore))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut details : MessageData := m!""
    for g in goals do
      details := details ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        pure m!"\n  • unsolved HTML5 / attribute validity obligation: {fmt.pretty.replace "✝" ""}")
    throwError m!"HTML5 / XSS validity check (`Html.valid`) failed for this view.{details}\n\n\
      Common causes:\n\
      • Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<button>`/`<a>`, \
        non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)\n\
      • Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount\n\
      • Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute\n\
      • Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`\n\
      • Unescaped dynamic text inside `<style>` (wrap with `escapeRawText` or `theme`/`styleSheet`)"

elab "qedProveDehydrateView" : tactic => do
  evalTactic (← `(tactic| intro _qed_m))
  -- Fast path: `Dehydrate.full` (`project = id`) and inline record-slice `Dehydrate.fields` close by `rfl`/simp!
  try evalTactic (← `(tactic| rfl)) catch _ => pure ()
  if (← getGoals).isEmpty then return
  let env0 ← getEnv
  let projLemmas := #[
    `Qed.mkApp_template, `Qed.mkRoutedApp_template, `Qed.App.addLocals_template,
    `Qed.App.withDehydrate_template, `Qed.App.withQueries_template,
    `Qed.Dehydrate.full_project, `Qed.Dehydrate.slice_project,
    `Qed.Dehydrate.route_project, `Qed.Dehydrate.fromRoute_project,
    ``View.render, ``View.renderEach, ``VAttr.eval,
    ``V.el, ``V.text, ``V.dyn, ``V.ifElse, ``V.showIf, ``V.static,
    ``V.dynNode, ``V.memo, ``V.forEach, ``View.showIf, ``View.ofHtml
  ].filter env0.contains
  let pL ← projLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  try evalTactic (← `(tactic| (simp only [$[$pL],*]; try rfl))) catch _ => pure ()
  if (← getGoals).isEmpty then return
  for _ in [0:6] do
    if (← getGoals).isEmpty then break
    let env ← getEnv
    let target ← instantiateMVars (← getMainTarget)
    let present ← target.getUsedConstants.filterM (fun n => liftM (isUnfoldableUserDef env false n))
    if present.isEmpty then break
    let uL ← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    let combined := uL ++ pL
    let ok ← try
        evalTactic (← `(tactic| (simp only [$[$combined],*]; try rfl)))
        pure true
      catch _ => pure false
    unless ok do break
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic| (simp; try rfl))) catch _ => pure ()
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut details : MessageData := m!""
    for g in goals do
      details := details ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        pure m!"\n  • view mismatch after rehydration: {fmt.pretty.replace "✝" ""}")
    throwError m!"SSR `dehydrate` slice does not preserve the rendered view: rehydrating a model \
      can render different HTML on the client than SSR rendered on the server.{details}\n\n\
      Include every model field read by the view in `(dehydrate := […])`, use \
      `(dehydrate := Dehydrate.full)`, or supply a proof to `App.withDehydrate`."

end Qed
