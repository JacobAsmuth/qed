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
  match n with
  | .str _ s =>
      if ["_qed_render", "_qed_renderTag", "_qed_mount", "_qed_mountWithOpt"].contains s then false
      else
        n.isInternalDetail ||
        ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion",
         "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg",
         "toJson", "fromJson"].contains s
          || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "inst"
  | _ => n.isInternalDetail

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
    ``V.dynNode, ``V.memo, ``V.render_forEach, ``View.isDyn, ``V.bindAttr, ``V.dynAttr,
    ``V.onClick', ``V.onInput', ``V.onCheck', ``SoundMemo.ofLawful,
    ``Qed.text, ``Qed.lazy, ``Qed.el, ``Qed.link, ``Qed.linkTo, ``Qed.theme,
    ``Qed.cls, ``Qed.attr, ``Qed.role, ``Qed.on, ``Qed.onValue, ``Qed.onClick, ``Qed.onInput,
    ``Qed.onChange, ``Qed.onCheck, ``Qed.onKeydown, ``Qed.onKeyup, ``Qed.onSubmit,
    ``Qed.onBlur, ``Qed.onFocus, ``Qed.onDoubleClick, ``Qed.onMouseDown, ``Qed.onMouseUp,
    ``Qed.key, ``Qed.value, ``Qed.placeholder, ``Qed.name, ``Qed.href, ``Qed.src, ``Qed.action,
    ``Qed.alt, ``Qed.title, ``Qed.style, ``Qed.type', ``Qed.disabled, ``Qed.required,
    ``Qed.checked, ``Qed.readOnly
  ]
  let opt := #[
    `Qed.Component.render,
    `Qed.ForEachItems.toList_array, `Qed.ForEachItems.toList_list, `Qed.ForEachItems.toArray, `Qed.mapList_eq,
    `Qed.localMount, `Qed.localMountWith
  ].filter env.contains
  core ++ opt

private def viewValidSimpExtras (env : Environment) : Array Name :=
  let base := #[
    ``Qed.Url.isSafe, ``Qed.Url.parse?_isSome, ``Qed.containsCloseSeq_escapeRawText, ``Qed.toString_string,
    ``Qed.Attr.valid_cls, ``Qed.Attr.valid_attr, ``Qed.Attr.valid_flag, ``Qed.Attr.valid_key,
    ``Qed.Attr.valid_on, ``Qed.Attr.valid_onValue, ``Qed.Attr.valid_localCell,
    ``Qed.Attr.valid_signalBind, ``Qed.Attr.valid_signalAttr, ``Qed.Attr.valid_empty, ``Qed.Attr.valid_ite,
    ``Qed.Attr.validList_nil, ``Qed.Attr.validList_cons, ``Qed.Attr.validList_append,
    ``Qed.Attr.validList_filter_nonkey, ``Qed.Attr.validList_map_attrMap, ``Qed.Attr.validList_prefixSignal,
    ``Qed.Attr.valid_map, ``Qed.Attr.valid_prefixSignal,
    ``Qed.Attr.isLocalCell_cls, ``Qed.Attr.isLocalCell_attr, ``Qed.Attr.isLocalCell_flag,
    ``Qed.Attr.isLocalCell_key, ``Qed.Attr.isLocalCell_on, ``Qed.Attr.isLocalCell_onValue,
    ``Qed.Attr.isLocalCell_localCell, ``Qed.Attr.isLocalCell_signalBind, ``Qed.Attr.isLocalCell_signalAttr,
    ``Qed.Attr.isLocalCell_empty, ``Qed.Attr.isLocalCell_ite,
    ``Qed.Attr.hasLocalCell_nil, ``Qed.Attr.hasLocalCell_cons, ``Qed.Attr.hasLocalCell_append,
    ``Qed.Attr.hasLocalCell_filter_nonkey, ``Qed.Attr.hasLocalCell_map_attrMap, ``Qed.Attr.hasLocalCell_prefixSignal,
    ``View.renderEach_isEmpty,
    ``Html.mapChildren_isEmpty, ``Qed.Html.prefixSignalsList_isEmpty,
    ``Qed.Html.validIn_map, ``Qed.Html.validListIn_mapChildren,
    ``Qed.Html.validIn_prefixSignals, ``Qed.Html.validListIn_prefixSignalsList,
    ``Qed.Html.validListIn_nil, ``Qed.Html.validListIn_cons, ``Qed.Html.validListIn_append,
    ``Qed.Html.validIn_ite, ``Qed.Html.validListIn_ite, ``Qed.Html.validIn_ofOption,
    ``Qed.Html.validListIn_map, ``Qed.Html.validListIn_toList_map, ``Qed.Html.validIn_withKey,
    ``Qed.List.all_const_true,
    ``Qed.validTextIn_normal, ``Qed.validTextIn_option, ``Qed.validTextIn_textarea,
    ``Qed.validTextIn_svg, ``Qed.validTextIn_rawStyle, ``Qed.validTextIn_empty,
    ``Qed.VAttr.eval_mapScope, ``Qed.View.render_mapScope, ``Qed.View.renderEach_mapScopeEach,
    ``Qed.View.renderEach_map, ``Qed.View.render_ite, ``Qed.View.render_showIf,
    ``Qed.View.collectDyn_showIf, ``Qed.View.renderSig_showIf, ``Qed.View.renderSigList_isEmpty,
    ``Qed.Attr.validList_renderSigAttrs, ``Qed.Attr.hasLocalCell_renderSigAttrs,
    ``Qed.V.render_memo, ``Qed.V.render_forEach,
    ``reduceStepHtmlCtx, ``reduceIsVoidTag, ``reduceIsSafeAttrName, ``reduceIsUrlAttrName,
    ``reduceIsSafeUrl, ``reduceContainsCloseSeq, ``reduceTagBlocksDirectSpan, ``reduceTagBlocksSpanSubtree,
    ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true',
    ``Bool.true_and, ``Bool.and_true, ``Bool.false_and, ``Bool.and_false,
    ``Bool.true_or, ``Bool.or_true, ``Bool.false_or, ``Bool.or_false,
    ``Bool.not_false, ``Bool.not_true,
    ``ite_true, ``ite_false, ``dite_true, ``dite_false, ``if_true, ``if_false,
    ``List.map_cons, ``List.map_nil, ``List.map_append, ``List.map_map,
    ``List.isEmpty_cons, ``List.isEmpty_nil, ``List.isEmpty_map,
    ``List.all_cons, ``List.all_nil, ``List.zipIdx_cons, ``List.zipIdx_nil,
    ``Array.toList_map, ``Array.isEmpty_empty, ``Array.isEmpty_push,
    ``Option.map_some, ``Option.map_none, ``Option.isSome_some, ``Option.isSome_none,
    ``Prod.fst, ``Prod.snd, ``Function.comp_apply, ``id_eq, ``eq_self, ``bne_iff_ne, ``beq_iff_eq
  ]
  let opt := #[
    `Qed.Codec.render_valid_simp, `Qed.Codec.formFieldRow_validListIn,
    `Qed.Attr.valid_localProps, `Qed.Attr.valid_localInit,
    `Qed.Attr.valid_localMount, `Qed.Attr.valid_localMountWith,
    `Qed.Router.isSafeUrl_toURL, `Qed.ToHref.isSafeUrl_toHref
  ].filter env.contains
  base ++ opt

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

private def runHtmlSimpLoop (maxIters : Nat)
    (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (useOnly : Bool) : TacticM Unit := do
  for _ in [0:maxIters] do
    if (← getGoals).isEmpty then return
    let before ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    evalTactic (← `(tactic| qedUnfoldForValidHtml))
    if (← getGoals).isEmpty then return
    let stepTac ← if useOnly then `(tactic| simp only [$[$lemmas],*]) else `(tactic| simp [$[$lemmas],*])
    try evalTactic stepTac catch _ => pure ()
    if (← getGoals).isEmpty then return
    let splitTac ← if useOnly then `(tactic| (split <;> try simp only [$[$lemmas],*]))
      else `(tactic| (split <;> try simp [$[$lemmas],*]))
    try evalTactic splitTac catch _ => pure ()
    if (← getGoals).isEmpty then return
    let after ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    if before == after then break

private abbrev ProveValidM := StateRefT (Array MVarId) MetaM

private def rflBoolTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

private def rflBoolFalse : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)

private def rflSomeHtmlCtx (ctxE : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one])
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
    (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) ctxE)

private def mkBoolEq (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs

private def mkBoolEqTrue (lhs : Expr) : Expr :=
  mkBoolEq lhs (mkConst ``Bool.true)

private def defaultHtmlCtx : HtmlCtx := {}

private def defaultHtmlCtxExpr : Expr := htmlCtxExpr defaultHtmlCtx

private def headConst? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

private def emitValidMVar (goalTy : Expr) : ProveValidM Expr := do
  let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
  modify fun gs => gs.push m.mvarId!
  return m

private def isMatcherOrCases (fn : Name) : MetaM Bool := do
  if (← Meta.isMatcher fn) then return true
  if let .str _ s := fn then
    return s == "casesOn" || s == "recOn"
  return false

private def isSafeKeyLit (k : Expr) : Bool :=
  match strLitVal? k with
  | some ks => Qed.isSafeAttrName ks
  | none    => false

private def isSafeKeyValLit (k v : Expr) : Bool :=
  match strLitVal? k with
  | some ks =>
      Qed.isSafeAttrName ks &&
      (!Qed.isUrlAttrName ks ||
        match strLitVal? v with
        | some vs => Qed.isSafeUrl vs
        | none    => false)
  | none => false

private def isFixedSafeNonCellAttrName (n : Name) : Bool :=
  n == ``Attr.cls || n == ``Qed.cls ||
  n == ``Attr.key || n == ``Qed.key ||
  n == ``Attr.empty || n == ``Attr.signalBind ||
  n == ``Qed.role ||
  n == ``Qed.onClick || n == ``Qed.onInput || n == ``Qed.onChange ||
  n == ``Qed.onCheck || n == ``Qed.onKeydown || n == ``Qed.onKeyup ||
  n == ``Qed.onSubmit || n == ``Qed.onBlur || n == ``Qed.onFocus ||
  n == ``Qed.onDoubleClick || n == ``Qed.onMouseDown || n == ``Qed.onMouseUp ||
  n == ``Qed.value || n == ``Qed.placeholder || n == ``Qed.name ||
  n == ``Qed.alt || n == ``Qed.title || n == ``Qed.style || n == ``Qed.type' ||
  n == ``Qed.disabled || n == ``Qed.required || n == ``Qed.checked || n == ``Qed.readOnly

private def isVAttrOnCheckEval (fn : Name) (args : Array Expr) : Bool :=
  fn == ``VAttr.eval && args.size == 4 &&
    (args[3]!).consumeMData.getAppFn.constName? == some ``V.onCheck'

private def isDefValidAttr (a : Expr) : Bool :=
  let a := a.consumeMData
  let args := a.getAppArgs
  match a.getAppFn.constName? with
  | some fn =>
      if isFixedSafeNonCellAttrName fn || fn == ``Attr.localCell ||
         fn == `Qed.localMount || fn == `Qed.localMountWith || isVAttrOnCheckEval fn args then true
      else if (fn == ``Attr.flag || fn == ``Attr.on || fn == ``Attr.onValue) && args.size >= 3 then
        isSafeKeyLit args[1]!
      else if (fn == ``Attr.attr || fn == ``Attr.signalAttr) && args.size >= 3 then
        isSafeKeyValLit args[args.size - 2]! args[args.size - 1]!
      else if fn == ``Qed.attr && args.size == 5 then
        isSafeKeyValLit args[3]! args[4]!
      else false
  | none => false

private def isDefNonLocalCellAttr (a : Expr) : Bool :=
  let a := a.consumeMData
  let args := a.getAppArgs
  match a.getAppFn.constName? with
  | some fn =>
      isFixedSafeNonCellAttrName fn || isVAttrOnCheckEval fn args ||
      fn == ``Qed.href || fn == ``Qed.src || fn == ``Qed.action ||
      fn == ``Attr.flag || fn == ``Attr.on || fn == ``Attr.onValue ||
      fn == ``Attr.attr || fn == ``Attr.signalAttr || fn == ``Qed.attr
  | none => false

private def evalVAttrExpr (sigmaTy msgTy sExpr va : Expr) : Expr :=
  let va := va.consumeMData
  let args := va.getAppArgs
  if va.isAppOfArity ``VAttr.stat 3 then args[2]!
  else if va.isAppOfArity ``VAttr.bind 3 || va.isAppOfArity ``V.bindAttr 3 then
    (mkApp args[2]! sExpr).headBeta
  else if va.isAppOfArity ``VAttr.dynVal 4 || va.isAppOfArity ``V.dynAttr 4 then
    mkApp3 (mkConst ``Attr.attr) args[1]! args[2]! (mkApp args[3]! sExpr)
  else if va.isAppOfArity ``V.onClick' 3 then
    mkApp3 (mkConst ``Attr.on) args[1]! (toExpr "click") (mkApp args[2]! sExpr)
  else if va.isAppOfArity ``V.onInput' 3 then
    mkApp3 (mkConst ``Attr.onValue) args[1]! (toExpr "input") (mkApp args[2]! sExpr)
  else
    mkApp4 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr va

private def expandVAttrMap (sigmaTy msgTy sExpr : Expr) : Nat → Expr → Expr
  | 0, vattrs =>
      mkAppN (mkConst ``List.map [Level.zero, Level.zero])
        #[mkApp2 (mkConst ``VAttr) sigmaTy msgTy, mkApp (mkConst ``Attr) msgTy,
          mkApp3 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr, vattrs]
  | fuel + 1, vattrs =>
      let vattrs := vattrs.consumeMData.headBeta
      if vattrs.isAppOfArity ``List.nil 1 then
        mkApp (mkConst ``List.nil [Level.zero]) (mkApp (mkConst ``Attr) msgTy)
      else if vattrs.isAppOfArity ``List.cons 3 then
        let args := vattrs.getAppArgs
        mkApp3 (mkConst ``List.cons [Level.zero]) (mkApp (mkConst ``Attr) msgTy)
          (evalVAttrExpr sigmaTy msgTy sExpr args[1]!)
          (expandVAttrMap sigmaTy msgTy sExpr fuel args[2]!)
      else
        mkAppN (mkConst ``List.map [Level.zero, Level.zero])
          #[mkApp2 (mkConst ``VAttr) sigmaTy msgTy, mkApp (mkConst ``Attr) msgTy,
            mkApp3 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr, vattrs]

private def normalizeAttrsExpr (attrs : Expr) : Expr :=
  let attrs := attrs.consumeMData.headBeta
  if attrs.isAppOfArity ``List.map 4 then
    let args := attrs.getAppArgs
    let fn := args[2]!.consumeMData
    if fn.isAppOfArity ``VAttr.eval 3 then
      let fArgs := fn.getAppArgs
      expandVAttrMap fArgs[0]! fArgs[1]! fArgs[2]! 128 args[3]!
    else attrs
  else attrs

private def allAttrList (p : Expr → Bool) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, attrs =>
      let attrs := attrs.consumeMData
      if attrs.isAppOfArity ``List.nil 1 then true
      else if attrs.isAppOfArity ``List.cons 3 then
        let args := attrs.getAppArgs
        p args[1]! && allAttrList p fuel args[2]!
      else false

private def withHypLam (ty : Expr) (k : Expr → ProveValidM Expr) : ProveValidM Expr :=
  withLocalDeclD `_qed_h ty fun h => do
    mkLambdaFVars #[h] (← k h)

private def proveIteBranches (c : Expr) (onT onF : ProveValidM Expr) : ProveValidM (Expr × Expr) :=
  return (← withHypLam c fun _ => onT, ← withHypLam (mkApp (mkConst ``Not) c) fun _ => onF)

private def proveResBranches (α ready loading failed idle : Expr) (k : Expr → ProveValidM Expr) :
    ProveValidM (Array Expr) := do
  let pfIdle ← k idle
  let pfLoad ← k loading
  let pfReady ← withHypLam α fun a => k (mkApp ready a)
  let pfFail ← withHypLam (mkConst ``String) fun e => k (mkApp failed e)
  return #[pfIdle, pfLoad, pfReady, pfFail]

private def proveAttrValid (env : Environment) (msgTy a : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a))
  | fuel + 1 => do
      let a := a.consumeMData.headBeta
      if let .letE _ _ val body _ := a then
        return ← proveAttrValid env msgTy (body.instantiate1 val) fuel
      if isDefValidAttr a then
        return rflBoolTrue
      let args := a.getAppArgs
      let aFn? := a.getAppFn.constName?
      for (ctor, lem) in #[
          (``Qed.href, ``Qed.Attr.valid_href),
          (``Qed.src, ``Qed.Attr.valid_src),
          (``Qed.action, ``Qed.Attr.valid_action)] do
        if a.isAppOfArity ctor 4 then
          return mkApp4 (mkConst lem) args[0]! args[1]! args[2]! args[3]!
      for (ctor, lem) in #[(`Qed.Attr.localProps, `Qed.Attr.valid_localProps_intro),
                           (`Qed.Attr.localInit, `Qed.Attr.valid_localInit_intro)] do
        if aFn? == some ctor && args.size == 5 && env.contains lem then
          let pfInner ← proveAttrValid env msgTy args[3]! fuel
          return mkAppN (mkConst lem) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, pfInner]
      if a.isAppOfArity ``Attr.attr 3 then
        if isSafeKeyLit args[1]! then
          let val := args[2]!.consumeMData
          if val.isAppOfArity ``Qed.ToHref.toHref 3 then
            let tArgs := val.getAppArgs
            return mkAppN (mkConst ``Qed.ToHref.valid_attr)
              #[args[0]!, tArgs[0]!, tArgs[1]!, args[1]!, tArgs[2]!, rflBoolTrue]
      if a.isAppOfArity ``ite 5 then
        let c := args[1]!; let dec := args[2]!; let tBr := args[3]!; let fBr := args[4]!
        let (pfT, pfF) ← proveIteBranches c
          (proveAttrValid env msgTy tBr fuel) (proveAttrValid env msgTy fBr fuel)
        return mkAppN (mkConst ``Qed.Attr.valid_ite_intro) #[msgTy, c, dec, tBr, fBr, pfT, pfF]
      if let some fn := aFn? then
        if (← liftM (isUnfoldableUserDef env true fn)) then
          if let some aUnf ← Meta.unfoldDefinition? a then
            return ← proveAttrValid env msgTy aUnf fuel
      emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a))

private def proveAttrValidList (env : Environment) (msgTy attrs : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))
  | fuel + 1 => do
      let attrs := normalizeAttrsExpr attrs
      if allAttrList isDefValidAttr 128 attrs || attrs.isAppOfArity ``List.nil 1 then
        return rflBoolTrue
      if attrs.isAppOfArity ``List.cons 3 then
        let args := attrs.getAppArgs
        let pfA ← proveAttrValid env msgTy args[1]! fuel
        let pfRest ← proveAttrValidList env msgTy args[2]! fuel
        return mkAppN (mkConst ``Qed.Attr.validList_cons_intro) #[msgTy, args[1]!, args[2]!, pfA, pfRest]
      if attrs.isAppOfArity ``HAppend.hAppend 6 then
        let args := attrs.getAppArgs
        let xs := args[4]!; let ys := args[5]!
        let pfXs ← proveAttrValidList env msgTy xs fuel
        let pfYs ← proveAttrValidList env msgTy ys fuel
        return mkAppN (mkConst ``Qed.Attr.validList_append_intro) #[msgTy, xs, ys, pfXs, pfYs]
      emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))

private def proveAttrIsLocalCellFalse (msgTy a : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let a := a.consumeMData.headBeta
      if isDefNonLocalCellAttr a then
        some rflBoolFalse
      else if a.isAppOfArity ``ite 5 then
        let args := a.getAppArgs
        let c := args[1]!; let dec := args[2]!; let tBr := args[3]!; let fBr := args[4]!
        match proveAttrIsLocalCellFalse msgTy tBr fuel, proveAttrIsLocalCellFalse msgTy fBr fuel with
        | some pT, some pF =>
            let lamT := Expr.lam `_qed_h c pT .default
            let lamF := Expr.lam `_qed_h (mkApp (mkConst ``Not) c) pF .default
            some (mkAppN (mkConst ``Qed.Attr.isLocalCell_ite_eq_false) #[msgTy, c, dec, tBr, fBr, lamT, lamF])
        | _, _ => none
      else none

private def proveAttrHasLocalCellFalse (msgTy attrs : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let attrs := normalizeAttrsExpr attrs
      if allAttrList isDefNonLocalCellAttr 128 attrs || attrs.isAppOfArity ``List.nil 1 then
        some rflBoolFalse
      else if attrs.isAppOfArity ``List.cons 3 then
        let args := attrs.getAppArgs
        match proveAttrIsLocalCellFalse msgTy args[1]! fuel, proveAttrHasLocalCellFalse msgTy args[2]! fuel with
        | some pA, some pRest =>
            some (mkAppN (mkConst ``Qed.Attr.hasLocalCell_cons_eq_false) #[msgTy, args[1]!, args[2]!, pA, pRest])
        | _, _ => none
      else if attrs.isAppOfArity ``HAppend.hAppend 6 then
        let args := attrs.getAppArgs
        let xs := args[4]!; let ys := args[5]!
        match proveAttrHasLocalCellFalse msgTy xs fuel, proveAttrHasLocalCellFalse msgTy ys fuel with
        | some pX, some pY =>
            some (mkAppN (mkConst ``Qed.Attr.hasLocalCell_append_eq_false) #[msgTy, xs, ys, pX, pY])
        | _, _ => none
      else none

private def proveVoidObligation (elemTy tagE kids : Expr) (tagS : String) : ProveValidM Expr := do
  if !Qed.isVoidTag tagS then
    return rflBoolTrue
  if kids.consumeMData.isAppOfArity ``List.nil 1 then
    return mkApp (mkConst ``Bool.or_true) (mkApp (mkConst ``Bool.not) (mkApp (mkConst ``Qed.isVoidTag) tagE))
  let lhs := mkApp2 (mkConst ``Bool.or)
    (mkApp (mkConst ``Bool.not) (mkApp (mkConst ``Qed.isVoidTag) tagE))
    (mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids)
  emitValidMVar (mkBoolEqTrue lhs)

private def proveCellObligation (elemTy msgTy evalAttrs kids : Expr) : ProveValidM Expr := do
  if allAttrList isDefNonLocalCellAttr 128 evalAttrs then
    return rflBoolTrue
  let hasCellE := mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs
  let notCellE := mkApp (mkConst ``Bool.not) hasCellE
  if kids.consumeMData.isAppOfArity ``List.nil 1 then
    return mkApp (mkConst ``Bool.or_true) notCellE
  let isEmptyE := mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids
  if let some pFalse := proveAttrHasLocalCellFalse msgTy evalAttrs 128 then
    return mkApp3 (mkConst ``Qed.Bool.not_false_or) hasCellE isEmptyE pFalse
  emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Bool.or) notCellE isEmptyE))

mutual
  private def proveSplitSubgoal (fuel : Nat) (env : Environment) (goalTy : Expr) : ProveValidM Expr := do
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
        let split? ← try
            m.mvarId!.withContext do Meta.splitTarget? m.mvarId!
          catch _ => pure none
        match split? with
        | some subgoals =>
            for sg in subgoals do
              proveGoalMVar fuel env sg
            instantiateMVars m
        | none =>
            modify fun gs => gs.push m.mvarId!
            return m

  private def proveValidIn (fuel : Nat) (env : Environment) (ctxV : HtmlCtx)
      (ctxE msgTy h : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue (mkApp3 (mkConst ``Html.validIn) msgTy ctxE h)
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let h := h.consumeMData.headBeta
        if let .letE _ _ val body _ := h then
          return ← proveValidIn fuel env ctxV ctxE msgTy (body.instantiate1 val)
        let args := h.getAppArgs
        let hFn? := h.getAppFn.constName?
        if h.isAppOfArity ``Html.text 2 then
          let str := args[1]!
          match ctxV.mode with
          | .normal | .option | .textarea | .svg => return rflBoolTrue
          | .rawStyle =>
              if strLitVal? str == some "" then return rflBoolTrue
              if str.consumeMData.isAppOfArity ``Qed.escapeRawText 1 then
                return mkApp4 (mkConst ``Qed.validTextIn_rawStyle_escape)
                  (toExpr ctxV.inP) (toExpr ctxV.interactive) (toExpr ctxV.inForm) str.consumeMData.appArg!
              if let some s := strLitVal? str then
                if !Qed.containsCloseSeq s.toList then
                  return rflBoolTrue
              return ← emitValidMVar goalTy
          | _ =>
              if strLitVal? str == some "" then return rflBoolTrue
              return ← emitValidMVar goalTy
        if h.isAppOfArity ``Qed.text 4 then
          match ctxV.mode with
          | .normal | .option | .textarea | .svg => return rflBoolTrue
          | _ => pure ()
        if h.isAppOfArity ``Html.element 4 || h.isAppOfArity ``Qed.el 4 then
          let tagE := args[1]!
          let attrs := args[2]!
          let kids := args[3]!
          if let some tagS := strLitVal? tagE then
            match Qed.stepHtmlCtx ctxV tagS with
            | some childCtx =>
                let childCtxE := htmlCtxExpr childCtx
                let hstep := rflSomeHtmlCtx childCtxE
                let hattrs ← proveAttrValidList env msgTy attrs 128
                let htmlTy := mkApp (mkConst ``Html) msgTy
                let hvoid ← proveVoidObligation htmlTy tagE kids tagS
                let hcell ← proveCellObligation htmlTy msgTy attrs kids
                let hkids ← proveValidListIn fuel env childCtx childCtxE msgTy kids
                return mkAppN (mkConst ``Qed.Html.validIn_element_intro)
                  #[msgTy, ctxE, childCtxE, tagE, attrs, kids, hstep, hattrs, hvoid, hcell, hkids]
            | none =>
                return ← emitValidMVar goalTy
          return ← emitValidMVar goalTy
        if h.isAppOfArity ``Qed.withKey 3 then
          let pf ← proveValidIn fuel env ctxV ctxE msgTy args[2]!
          return mkApp4 (mkConst ``Qed.Html.validIn_withKey_intro) msgTy ctxE args[1]! args[2]! |>.app pf
        if h.isAppOfArity ``Html.map 4 then
          let α := args[0]!
          let pf ← proveValidIn fuel env ctxV ctxE α args[3]!
          return mkAppN (mkConst ``Qed.Html.validIn_map_intro) #[α, args[1]!, ctxE, args[2]!, args[3]!, pf]
        if h.isAppOfArity ``Html.prefixSignals 3 then
          let pf ← proveValidIn fuel env ctxV ctxE msgTy args[2]!
          return mkAppN (mkConst ``Qed.Html.validIn_prefixSignals_intro) #[msgTy, ctxE, args[1]!, args[2]!, pf]
        if h.isAppOfArity ``Html.ofOption 2 then
          let opt := args[1]!.consumeMData
          if opt.isAppOfArity ``Option.none 1 then
            return mkApp (mkConst ``Qed.validTextIn_empty) ctxE
          if opt.isAppOfArity ``Option.some 2 then
            return ← proveValidIn fuel env ctxV ctxE msgTy opt.getAppArgs[1]!
          return ← proveSplitSubgoal fuel env goalTy
        if h.isAppOfArity ``View.render 4 then
          return ← proveViewRender fuel env ctxV ctxE args[0]! args[1]! args[2]! args[3]!
        if hFn? == some ``Qed.lazy && args.size == 5 then
          let inner := (mkApp args[3]! args[4]!).headBeta
          return ← proveValidIn fuel env ctxV ctxE msgTy inner
        if hFn? == some ``Qed.link || hFn? == some ``Qed.linkTo || hFn? == some ``Qed.theme then
          if let some hUnf ← Meta.unfoldDefinition? h then
            return ← proveValidIn fuel env ctxV ctxE msgTy hUnf
        if hFn? == some `Qed.Resource.awaitView && args.size == 9 && env.contains `Qed.Resource.validIn_awaitView_intro then
          let pfs ← proveResBranches args[1]! args[5]! args[6]! args[7]! args[8]!
            (proveValidIn fuel env ctxV ctxE msgTy)
          return mkAppN (mkConst `Qed.Resource.validIn_awaitView_intro)
            (#[args[0]!, args[1]!, msgTy, args[3]!, ctxE, args[4]!, args[5]!, args[6]!, args[7]!, args[8]!] ++ pfs)
        if (hFn? == some `Qed.Resource.view || (hFn? == some `Qed.Cached.view && env.contains `Qed.Cached.state)) &&
            args.size == 7 && env.contains `Qed.Resource.validIn_view_intro then
          let r := if hFn? == some `Qed.Cached.view then mkApp2 (mkConst `Qed.Cached.state) args[0]! args[2]! else args[2]!
          let pfs ← proveResBranches args[0]! args[3]! args[4]! args[5]! args[6]!
            (proveValidIn fuel env ctxV ctxE msgTy)
          return mkAppN (mkConst `Qed.Resource.validIn_view_intro)
            (#[args[0]!, msgTy, ctxE, r, args[3]!, args[4]!, args[5]!, args[6]!] ++ pfs)
        if h.isAppOfArity ``ite 5 then
          let c := args[1]!; let dec := args[2]!; let a := args[3]!; let b := args[4]!
          let (pfT, pfF) ← proveIteBranches c
            (proveValidIn fuel env ctxV ctxE msgTy a) (proveValidIn fuel env ctxV ctxE msgTy b)
          return mkAppN (mkConst ``Qed.Html.validIn_ite_intro) #[msgTy, ctxE, c, dec, a, b, pfT, pfF]
        if h.isAppOfArity ``dite 5 then
          let c := args[1]!; let dec := args[2]!; let aLam := args[3]!; let bLam := args[4]!
          let pfT ← withHypLam c fun fv => proveValidIn fuel env ctxV ctxE msgTy (mkApp aLam fv)
          let pfF ← withHypLam (mkApp (mkConst ``Not) c) fun fv => proveValidIn fuel env ctxV ctxE msgTy (mkApp bLam fv)
          return mkAppN (mkConst ``Qed.Html.validIn_dite_intro) #[msgTy, ctxE, c, dec, aLam, bLam, pfT, pfF]
        if let some fn := hFn? then
          if fn.toString.endsWith ".formView" && args.size >= 4 && ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
            let validLemma := fn.getPrefix ++ `formView_validIn
            if env.contains validLemma then
              let splitIdx := args.size - 3
              let lmArgs := args.extract 0 splitIdx ++ #[toExpr ctxV.inForm] ++ args.extract splitIdx args.size
              let pf := mkAppN (mkConst validLemma) lmArgs
              if (← Meta.isTypeCorrect pf) then
                return pf
          if (← isMatcherOrCases fn) then
            return ← proveSplitSubgoal fuel env goalTy
          if (← liftM (isUnfoldableUserDef env true fn)) then
            if let some hUnf ← Meta.unfoldDefinition? h then
              return ← proveValidIn fuel env ctxV ctxE msgTy hUnf
        emitValidMVar goalTy

  private def proveValidListIn (fuel : Nat) (env : Environment) (ctxV : HtmlCtx)
      (ctxE msgTy cs : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue (mkApp3 (mkConst ``Html.validListIn) msgTy ctxE cs)
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let cs := cs.consumeMData.headBeta
        if let .letE _ _ val body _ := cs then
          return ← proveValidListIn fuel env ctxV ctxE msgTy (body.instantiate1 val)
        let args := cs.getAppArgs
        let csFn? := cs.getAppFn.constName?
        if cs.isAppOfArity ``List.nil 1 then
          return mkApp2 (mkConst ``Qed.Html.validListIn_nil) msgTy ctxE
        if cs.isAppOfArity ``List.cons 3 then
          let pfC ← proveValidIn fuel env ctxV ctxE msgTy args[1]!
          let pfCs ← proveValidListIn fuel env ctxV ctxE msgTy args[2]!
          return mkAppN (mkConst ``Qed.Html.validListIn_cons_intro) #[msgTy, ctxE, args[1]!, args[2]!, pfC, pfCs]
        if cs.isAppOfArity ``HAppend.hAppend 6 then
          let xs := args[4]!; let ys := args[5]!
          let pfX ← proveValidListIn fuel env ctxV ctxE msgTy xs
          let pfY ← proveValidListIn fuel env ctxV ctxE msgTy ys
          return mkAppN (mkConst ``Qed.Html.validListIn_append_intro) #[msgTy, ctxE, xs, ys, pfX, pfY]
        if cs.isAppOfArity ``Html.mapChildren 4 then
          let α := args[0]!
          let pf ← proveValidListIn fuel env ctxV ctxE α args[3]!
          return mkAppN (mkConst ``Qed.Html.validListIn_mapChildren_intro) #[α, args[1]!, ctxE, args[2]!, args[3]!, pf]
        if cs.isAppOfArity ``Html.prefixSignalsList 3 then
          let pf ← proveValidListIn fuel env ctxV ctxE msgTy args[2]!
          return mkAppN (mkConst ``Qed.Html.validListIn_prefixSignalsList_intro) #[msgTy, ctxE, args[1]!, args[2]!, pf]
        if cs.isAppOfArity ``View.renderEach 4 then
          return ← proveViewRenderEach fuel env ctxV ctxE args[0]! args[1]! args[2]! args[3]!
        if (csFn? == some `Qed.ForEachItems.toList || csFn? == some ``Qed.mapList) then
          if let some csUnf ← Meta.unfoldDefinition? cs then
            return ← proveValidListIn fuel env ctxV ctxE msgTy csUnf
        if cs.isAppOfArity ``List.map 4 then
          let α := args[0]!; let f := args[2]!; let xs := args[3]!
          let pfF ← withHypLam α fun a => proveValidIn fuel env ctxV ctxE msgTy (mkApp f a)
          return mkAppN (mkConst ``Qed.Html.validListIn_map_intro) #[α, msgTy, ctxE, xs, f, pfF]
        if cs.isAppOfArity ``Array.toList 2 then
          let inner := args[1]!.consumeMData
          if inner.isAppOfArity ``Array.map 4 then
            let mArgs := inner.getAppArgs
            let α := mArgs[0]!; let f := mArgs[2]!; let xs := mArgs[3]!
            let pfF ← withHypLam α fun a => proveValidIn fuel env ctxV ctxE msgTy (mkApp f a)
            return mkAppN (mkConst ``Qed.Html.validListIn_toList_map_intro) #[α, msgTy, ctxE, xs, f, pfF]
        if csFn? == some `Qed.Codec.formFieldRow && args.size == 7 &&
            env.contains `Qed.Codec.formFieldRow_validListIn &&
            ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
          let pfCtrl ← proveValidIn fuel env ctxV ctxE msgTy args[6]!
          return mkAppN (mkConst `Qed.Codec.formFieldRow_validListIn)
            #[msgTy, toExpr ctxV.inForm, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, pfCtrl]
        if cs.isAppOfArity ``ite 5 then
          let c := args[1]!; let dec := args[2]!; let a := args[3]!; let b := args[4]!
          let (pfT, pfF) ← proveIteBranches c
            (proveValidListIn fuel env ctxV ctxE msgTy a) (proveValidListIn fuel env ctxV ctxE msgTy b)
          return mkAppN (mkConst ``Qed.Html.validListIn_ite_intro) #[msgTy, ctxE, c, dec, a, b, pfT, pfF]
        if let some fn := csFn? then
          if (← isMatcherOrCases fn) then
            return ← proveSplitSubgoal fuel env goalTy
          if (← liftM (isUnfoldableUserDef env true fn)) then
            if let some csUnf ← Meta.unfoldDefinition? cs then
              return ← proveValidListIn fuel env ctxV ctxE msgTy csUnf
        emitValidMVar goalTy

  private def proveViewRender (fuel : Nat) (env : Environment) (ctxV : HtmlCtx)
      (ctxE sigmaTy msgTy v sExpr : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue (mkApp3 (mkConst ``Html.validIn) msgTy ctxE
      (mkApp4 (mkConst ``View.render) sigmaTy msgTy v sExpr))
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let v := v.consumeMData.headBeta
        if let .letE _ _ val body _ := v then
          return ← proveViewRender fuel env ctxV ctxE sigmaTy msgTy (body.instantiate1 val) sExpr
        let args := v.getAppArgs
        let vFn? := v.getAppFn.constName?
        if v.isAppOfArity ``View.text 3 || v.isAppOfArity ``V.text 3 then
          return ← proveValidIn fuel env ctxV ctxE msgTy (mkApp2 (mkConst ``Html.text) msgTy args[2]!)
        if v.isAppOfArity ``View.dyn 3 || v.isAppOfArity ``V.dyn 3 then
          return ← proveValidIn fuel env ctxV ctxE msgTy (mkApp2 (mkConst ``Html.text) msgTy (mkApp args[2]! sExpr))
        if v.isAppOfArity ``View.static 3 || v.isAppOfArity ``V.static 3 then
          return ← proveValidIn fuel env ctxV ctxE msgTy args[2]!
        if v.isAppOfArity ``View.dynNode 3 || v.isAppOfArity ``V.dynNode 3 || v.isAppOfArity ``View.ofHtml 3 then
          return ← proveValidIn fuel env ctxV ctxE msgTy (mkApp args[2]! sExpr)
        if v.isAppOfArity ``V.memo 6 then
          return ← proveValidIn fuel env ctxV ctxE msgTy (mkApp args[4]! (mkApp args[5]! sExpr))
        if v.isAppOfArity ``View.memo 3 then
          let sm := args[2]!.consumeMData
          if sm.isAppOfArity ``SoundMemo.ofLawful 6 then
            let smArgs := sm.getAppArgs
            return ← proveValidIn fuel env ctxV ctxE msgTy (mkApp smArgs[4]! (mkApp smArgs[5]! sExpr))
        if v.isAppOfArity ``View.element 5 || v.isAppOfArity ``V.el 5 then
          let tagE := args[2]!; let attrs := args[3]!; let kids := args[4]!
          if let some tagS := strLitVal? tagE then
            match Qed.stepHtmlCtx ctxV tagS with
            | some childCtx =>
                let childCtxE := htmlCtxExpr childCtx
                let hstep := rflSomeHtmlCtx childCtxE
                let evalAttrs := expandVAttrMap sigmaTy msgTy sExpr 128 attrs
                let hattrs ← proveAttrValidList env msgTy evalAttrs 128
                let viewTy := mkApp2 (mkConst ``View) sigmaTy msgTy
                let hvoid ← proveVoidObligation viewTy tagE kids tagS
                let hcell ← proveCellObligation viewTy msgTy evalAttrs kids
                let hkids ← proveViewRenderEach fuel env childCtx childCtxE sigmaTy msgTy kids sExpr
                return mkAppN (mkConst ``View.validIn_render_element_intro)
                  #[sigmaTy, msgTy, ctxE, childCtxE, tagE, attrs, kids, sExpr, hstep, hattrs, hvoid, hcell, hkids]
            | none =>
                return ← emitValidMVar goalTy
          return ← emitValidMVar goalTy
        if v.isAppOfArity ``View.showIf 4 || v.isAppOfArity ``V.showIf 4 then
          let cond := args[2]!; let child := args[3]!
          let pfY ← withHypLam (mkBoolEqTrue (mkApp cond sExpr)) fun _ =>
            proveViewRender fuel env ctxV ctxE sigmaTy msgTy child sExpr
          return mkAppN (mkConst ``View.validIn_render_showIf) #[sigmaTy, msgTy, ctxE, cond, child, sExpr, pfY]
        if v.isAppOfArity ``View.ifElse 5 || v.isAppOfArity ``V.ifElse 5 then
          let cond := args[2]!; let y := args[3]!; let n := args[4]!
          let pfY ← withHypLam (mkBoolEqTrue (mkApp cond sExpr)) fun _ =>
            proveViewRender fuel env ctxV ctxE sigmaTy msgTy y sExpr
          let pfN ← withHypLam (mkBoolEq (mkApp cond sExpr) (mkConst ``Bool.false)) fun _ =>
            proveViewRender fuel env ctxV ctxE sigmaTy msgTy n sExpr
          return mkAppN (mkConst ``View.validIn_render_ifElse) #[sigmaTy, msgTy, ctxE, cond, y, n, sExpr, pfY, pfN]
        if v.isAppOfArity ``V.forEach 9 then
          let alpha := args[2]!; let tagE := args[3]!; let items := args[4]!
          let key := args[5]!; let child := args[6]!; let attrs := args[7]!; let sigPrefix := args[8]!
          if let some tagS := strLitVal? tagE then
            if !Qed.isVoidTag tagS then
              if let some childCtx := Qed.stepHtmlCtx ctxV tagS then
                let childCtxE := htmlCtxExpr childCtx
                let hstep := rflSomeHtmlCtx childCtxE
                let hvoid := rflBoolFalse
                let evalAttrs := expandVAttrMap sigmaTy msgTy sExpr 128 attrs
                let hcell ← do
                  if allAttrList isDefNonLocalCellAttr 128 evalAttrs then
                    pure rflBoolTrue
                  else if let some pFalse := proveAttrHasLocalCellFalse msgTy evalAttrs 128 then
                    Meta.mkAppM ``congrArg #[mkConst ``Bool.not, pFalse]
                  else
                    emitValidMVar (mkBoolEqTrue (mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs)))
                let hattrs ← proveAttrValidList env msgTy evalAttrs 128
                let pfChild ← withHypLam alpha fun a =>
                  proveViewRender fuel env childCtx childCtxE alpha msgTy child a
                let lemTy ← Meta.inferType (mkAppN (mkConst ``V.validIn_render_forEach)
                  #[alpha, sigmaTy, msgTy, ctxE, childCtxE, tagE, items, key, child, attrs, sigPrefix, sExpr,
                    hstep, hvoid, hcell, hattrs, pfChild])
                let hsigTy := lemTy.bindingDomain!
                let hsig ←
                  if (← Meta.isDefEq hsigTy (mkBoolEqTrue (mkConst ``Bool.true))) then
                    pure rflBoolTrue
                  else
                    emitValidMVar hsigTy
                return mkAppN (mkConst ``V.validIn_render_forEach)
                  #[alpha, sigmaTy, msgTy, ctxE, childCtxE, tagE, items, key, child, attrs, sigPrefix, sExpr,
                    hstep, hvoid, hcell, hattrs, pfChild, hsig]
        if v.isAppOfArity ``View.mapScope 5 then
          let σInner := args[1]!; let f := args[3]!; let subV := args[4]!
          let pf ← proveViewRender fuel env ctxV ctxE σInner msgTy subV (mkApp f sExpr)
          return mkAppN (mkConst ``Qed.View.validIn_render_mapScope_intro)
            #[sigmaTy, σInner, msgTy, ctxE, f, subV, sExpr, pf]
        if v.isAppOfArity ``ite 5 then
          let c := args[1]!; let dec := args[2]!; let a := args[3]!; let b := args[4]!
          let (pfT, pfF) ← proveIteBranches c
            (proveViewRender fuel env ctxV ctxE sigmaTy msgTy a sExpr)
            (proveViewRender fuel env ctxV ctxE sigmaTy msgTy b sExpr)
          return mkAppN (mkConst ``Qed.View.validIn_render_ite_intro)
            #[sigmaTy, msgTy, ctxE, c, dec, a, b, sExpr, pfT, pfF]
        if let some fn := vFn? then
          if (← isMatcherOrCases fn) then
            return ← proveSplitSubgoal fuel env goalTy
          if (← liftM (isUnfoldableUserDef env true fn)) then
            if let some vUnf ← Meta.unfoldDefinition? v then
              return ← proveViewRender fuel env ctxV ctxE sigmaTy msgTy vUnf sExpr
        emitValidMVar goalTy

  private def proveViewRenderEach (fuel : Nat) (env : Environment) (ctxV : HtmlCtx)
      (ctxE sigmaTy msgTy vs sExpr : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue (mkApp3 (mkConst ``Html.validListIn) msgTy ctxE
      (mkApp4 (mkConst ``View.renderEach) sigmaTy msgTy vs sExpr))
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let vs := vs.consumeMData.headBeta
        if let .letE _ _ val body _ := vs then
          return ← proveViewRenderEach fuel env ctxV ctxE sigmaTy msgTy (body.instantiate1 val) sExpr
        let args := vs.getAppArgs
        let vsFn? := vs.getAppFn.constName?
        if vs.isAppOfArity ``List.nil 1 then
          return mkAppN (mkConst ``Qed.View.validListIn_renderEach_nil) #[sigmaTy, msgTy, ctxE, sExpr]
        if vs.isAppOfArity ``List.cons 3 then
          let pfK ← proveViewRender fuel env ctxV ctxE sigmaTy msgTy args[1]! sExpr
          let pfKs ← proveViewRenderEach fuel env ctxV ctxE sigmaTy msgTy args[2]! sExpr
          return mkAppN (mkConst ``Qed.View.validListIn_renderEach_cons)
            #[sigmaTy, msgTy, ctxE, args[1]!, args[2]!, sExpr, pfK, pfKs]
        if vs.isAppOfArity ``View.mapScopeEach 5 then
          let σInner := args[1]!; let f := args[3]!; let subVs := args[4]!
          let pf ← proveViewRenderEach fuel env ctxV ctxE σInner msgTy subVs (mkApp f sExpr)
          return mkAppN (mkConst ``Qed.View.validListIn_renderEach_mapScopeEach_intro)
            #[sigmaTy, σInner, msgTy, ctxE, f, subVs, sExpr, pf]
        if vs.isAppOfArity ``List.map 4 then
          let α := args[0]!; let f := args[2]!; let xs := args[3]!
          let pfF ← withHypLam α fun a => proveViewRender fuel env ctxV ctxE sigmaTy msgTy (mkApp f a) sExpr
          return mkAppN (mkConst ``Qed.View.validListIn_renderEach_map_intro)
            #[α, sigmaTy, msgTy, ctxE, xs, f, sExpr, pfF]
        if (vsFn? == some `Qed.ForEachItems.toList || vsFn? == some ``Qed.mapList) then
          if let some vsUnf ← Meta.unfoldDefinition? vs then
            return ← proveViewRenderEach fuel env ctxV ctxE sigmaTy msgTy vsUnf sExpr
        if let some fn := vsFn? then
          if (← isMatcherOrCases fn) then
            return ← proveSplitSubgoal fuel env goalTy
        proveValidListIn fuel env ctxV ctxE msgTy (mkApp4 (mkConst ``View.renderEach) sigmaTy msgTy vs sExpr)

  private def proveGoalMVar (fuel : Nat) (env : Environment) (g : MVarId) : ProveValidM Unit := do
    if (← g.isAssigned) then return
    match fuel with
    | 0 => modify fun gs => gs.push g
    | fuel + 1 =>
        let (_, g') ← g.intros
        g'.withContext do
          let tgt := (← instantiateMVars (← g'.getType)).consumeMData.headBeta
          if !tgt.isAppOfArity ``Eq 3 then
            modify fun gs => gs.push g'
            return
          let lhs := (tgt.getAppArgs[1]!).consumeMData.headBeta
          let rhs := (tgt.getAppArgs[2]!).consumeMData
          if !rhs.isConstOf ``Bool.true then
            modify fun gs => gs.push g'
            return
          let pf? : Option Expr ←
            if lhs.isAppOfArity ``Html.valid 2 then
              let lArgs := lhs.getAppArgs
              some <$> proveValidIn fuel env defaultHtmlCtx defaultHtmlCtxExpr lArgs[0]! lArgs[1]!
            else if lhs.isAppOfArity ``Html.validIn 3 then
              let lArgs := lhs.getAppArgs
              if let some ctxV ← htmlCtxVal? lArgs[1]! then
                some <$> proveValidIn fuel env ctxV lArgs[1]! lArgs[0]! lArgs[2]!
              else pure none
            else if lhs.isAppOfArity ``Html.validListIn 3 then
              let lArgs := lhs.getAppArgs
              if let some ctxV ← htmlCtxVal? lArgs[1]! then
                some <$> proveValidListIn fuel env ctxV lArgs[1]! lArgs[0]! lArgs[2]!
              else pure none
            else pure none
          match pf? with
          | some pf => g'.assign pf
          | none    => modify fun gs => gs.push g'
end

elab "qedProveValidHtmlCore" : tactic => do
  evalTactic (← `(tactic| intros))
  let env ← getEnv
  let goals ← getGoals
  let mut residuals : Array MVarId := #[]
  for g in goals do
    let (_, rem) ← (proveGoalMVar 2048 env g).run #[]
    residuals := residuals ++ rem
  setGoals residuals.toList
  if !(← getGoals).isEmpty then
    let toLemma (n : Name) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    let fw ← (viewFrameworkUnfolds env).mapM toLemma
    let onlySet ← ((viewFrameworkUnfolds env) ++ (viewValidSimpExtras env)).mapM toLemma
    runHtmlSimpLoop 4 onlySet true
    if !(← getGoals).isEmpty then
      runHtmlSimpLoop 2 fw false
    if !(← getGoals).isEmpty then
      try evalTactic (← `(tactic| all_goals (first | rfl | decide | (split <;> simp)))) catch _ => pure ()

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
      • Unescaped dynamic text inside `<style>` (wrap with `escapeRawText` or `theme`)"

private def dehydrateProjLemmas (env0 : Environment) : Array Name :=
  #[
    `Qed.Internal.mkApp_template, `Qed.Internal.mkRoutedApp_template,
    `Qed.Internal.mkApp_dehydrate, `Qed.Internal.mkApp_rehydrate,
    `Qed.Internal.mkRoutedApp_dehydrate, `Qed.Internal.mkRoutedApp_rehydrate,
    `Qed.Internal.App.setUpdate_dehydrate, `Qed.Internal.App.setUpdate_rehydrate,
    `Qed.Internal.App.withDehydrate_template, `Qed.Internal.App.withQueries_template,
    `Qed.Internal.App.withQueries_dehydrate, `Qed.Internal.App.withQueries_rehydrate,
    `Qed.Internal.App.withFullDehydrate, `Qed.Internal.App.withDehydrate_rehydrate_dehydrate,
    `Qed.App.guardRehydrate_template, `Qed.App.guardRehydrate_dehydrate,
    `Qed.Dehydrate.full_project, `Qed.Dehydrate.slice_project, `Qed.Dehydrate.const_project,
    `Qed.InvTarget.proj_id, `Qed.InvTarget.proj_fst
  ].filter env0.contains

private def unfoldDehydrateUsers (maxIters : Nat)
    (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (includeLCtx : Bool) : TacticM Unit := do
  for _ in [0:maxIters] do
    if (← getGoals).isEmpty then break
    let env ← getEnv
    let present ← withMainContext do
      let mut cs := (← instantiateMVars (← getMainTarget)).getUsedConstants
      if includeLCtx then
        for ldecl in (← getLCtx) do
          if !ldecl.isImplementationDetail then
            cs := cs ++ (← instantiateMVars ldecl.type).getUsedConstants
      cs.filterM (fun n => liftM (isUnfoldableUserDef env false n))
    if present.isEmpty then break
    let uL ← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    let combined := uL ++ extraLemmas
    let tac ← if includeLCtx
      then `(tactic| (simp only [$[$combined],*] at *; try rfl))
      else `(tactic| (simp only [$[$combined],*]; try rfl))
    let ok ← try evalTactic tac; pure true catch _ => pure false
    unless ok do break

elab "qedProveDehydrateView" : tactic => do
  evalTactic (← `(tactic| intro _qed_m))
  -- Fast path: `Dehydrate.full` (`project = id`) and inline record-slice `Dehydrate.fields` close by `rfl`/simp!
  try evalTactic (← `(tactic| rfl)) catch _ => pure ()
  if (← getGoals).isEmpty then return
  let env0 ← getEnv
  let viewSimpNames := dehydrateProjLemmas env0 ++ #[
    ``View.render, ``View.renderEach, ``VAttr.eval,
    ``V.el, ``V.text, ``V.dyn, ``V.ifElse, ``V.showIf, ``V.static,
    ``V.dynNode, ``V.memo, ``V.render_forEach, ``View.isDyn, ``View.showIf, ``View.ofHtml
  ].filter env0.contains
  let pL ← viewSimpNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  try evalTactic (← `(tactic| (simp only [$[$pL],*]; try rfl))) catch _ => pure ()
  if (← getGoals).isEmpty then return
  unfoldDehydrateUsers 6 pL false
  if !(← getGoals).isEmpty then
    let onlySet ← (viewSimpNames ++ viewValidSimpExtras env0).mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    try evalTactic (← `(tactic| (simp only [$[$onlySet],*]; try rfl))) catch _ => pure ()
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
      Do not mark model fields read by the view as `ephemeral` (so rehydration preserves the rendered view)."

elab "qedProveDehydrateInv" : tactic => do
  evalTactic (← `(tactic| intro _qed_m _qed_m' _qed_hinv _qed_hre))
  let env0 ← getEnv
  let pL ← (dehydrateProjLemmas env0).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  try evalTactic (← `(tactic| simp only [$[$pL],*] at _qed_hre)) catch _ => pure ()
  try evalTactic (← `(tactic| cases _qed_hre)) catch _ => pure ()
  try evalTactic (← `(tactic| exact _qed_hinv)) catch _ => pure ()
  if (← getGoals).isEmpty then return
  unfoldDehydrateUsers 6 pL true
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic|
      ((repeat' split) <;> first
        | exact _qed_hinv | rfl | decide | omega
        | (simp_all <;> first | exact _qed_hinv | rfl | decide | omega))))
    catch _ => pure ()
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut details : MessageData := m!""
    for g in goals do
      details := details ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        pure m!"\n  • invariant violation after rehydration: {fmt.pretty.replace "✝" ""}")
    throwError m!"SSR `dehydrate` slice can violate the component's state invariant: rehydrating a \
      model resets `ephemeral` or unserializable fields to `init`, which may break the \
      invariant.{details}\n\nDo not mark fields constrained by a state `invariant` as `ephemeral`, \
      or weaken the invariant."

@[simp] theorem ite_bool_eq_true (c : Prop) [Decidable c] {α : Sort _} (a b : α) :
    (if (if c then true else false) = true then a else b) = (if c then a else b) := by
  by_cases hc : c <;> simp [hc]

open Lean Elab Tactic Meta in
elab "qedProveViewEquiv" appId:ident viewId:ident : tactic => do
  let appName ← realizeGlobalConstNoOverloadWithInfo appId
  let viewName ← realizeGlobalConstNoOverloadWithInfo viewId
  let env0 ← getEnv
  let toLemma (n : Name) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  let stage1 := #[
    appName, viewName, `Qed.App.view, `Qed.Internal.App.withFullDehydrate,
    `Qed.Internal.mkApp_template, `Qed.Internal.mkRoutedApp_template,
    `Qed.Internal.App.withDehydrate_template, `Qed.Internal.App.withQueries_template,
    `Qed.App.guardRehydrate_template
  ].filter env0.contains
  let fwNames := (viewFrameworkUnfolds env0).filter (· != ``V.render_forEach) ++ #[
    ``View.render_mapScope, ``View.renderEach_mapScopeEach,
    ``V.canonical_render_forEach, ``SoundMemo.eval,
    ``Html.ofOption, ``List.map_cons, ``List.map_nil, ``List.map_map,
    ``Function.comp_def, ``Array.toList_map,
    ``mkCanonicalElem, ``onlySignalBind, ``Attr.canonical
  ]
  let s1 ← stage1.mapM toLemma
  let fw ← (fwNames.filter env0.contains).mapM toLemma
  try evalTactic (← `(tactic| try simp only [$[$s1],*])) catch _ => pure ()
  for _ in [0:5] do
    if (← getGoals).isEmpty then break
    let before ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    try evalTactic (← `(tactic| (qedUnfoldForValidHtml; try simp [-Qed.V.render_forEach, $[$fw],*]))) catch _ => pure ()
    if (← getGoals).isEmpty then break
    let after ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    if before == after then break
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic| all_goals first
      | rfl
      | ((repeat' split) <;> simp_all [Qed.mkCanonicalElem, Qed.onlySignalBind, Qed.Attr.canonical])))
    catch _ => pure ()

structure SchemaFormInfo where
  fullName     : Lean.Name
  formViewName : Lean.Name
  ctxBinders   : Array Lean.Name
deriving Inhabited

initialize schemaFormRegistry :
    Lean.SimplePersistentEnvExtension SchemaFormInfo (Lean.NameMap SchemaFormInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.fullName info) acc) {}
    addEntryFn := fun m info => m.insert info.fullName info
  }

open Lean in
def lookupSchemaForm? (cName : Name) : CoreM (Option SchemaFormInfo) := do
  let env ← getEnv
  let reg := schemaFormRegistry.getState env
  let ns ← getCurrNamespace
  if let some info := reg.find? (ns ++ cName) then return some info
  if let some info := reg.find? cName then return some info
  if cName.getString! == "Form" then
    for (fullView, _) in ResolveName.resolveGlobalName env {} ns (← getOpenDecls) (cName.getPrefix ++ `formView) do
      if let some info := reg.find? (fullView.getPrefix ++ `Form) then return some info
  return none

end Qed
