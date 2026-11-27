import Qed.Runtime.ValidLemmas
import Qed.Verify.Core

namespace Qed
open Lean Meta Elab Tactic Qed.Verify.Core Qed.ValidLemmas

private def mkAppNode (c : Name) (xs : Array Expr) : Expr := mkAppN (mkConst c) xs

private def boolVal? (e : Expr) : MetaM (Option Bool) := do
  let r ← whnf e
  return if r.isConstOf ``Bool.true then some true else if r.isConstOf ``Bool.false then some false else none

private def tagModeTable : Array (Name × TagMode) := #[
  (``TagMode.normal, .normal), (``TagMode.ulOl, .ulOl), (``TagMode.dl, .dl), (``TagMode.table, .table),
  (``TagMode.colgroup, .colgroup), (``TagMode.tableSection, .tableSection), (``TagMode.tableRow, .tableRow),
  (``TagMode.select, .select), (``TagMode.optgroup, .optgroup), (``TagMode.option, .option),
  (``TagMode.rawStyle, .rawStyle), (``TagMode.textarea, .textarea), (``TagMode.svg, .svg)]

private def htmlCtxVal? (e : Expr) : MetaM (Option HtmlCtx) := do
  if e.hasFVar || e.hasMVar then return none
  let r ← whnf e; if !r.isAppOfArity ``HtmlCtx.mk 4 then return none
  let a := r.getAppArgs; let modeR ← whnf a[0]!
  let some (_, mode) := tagModeTable.find? (fun (n, _) => modeR.isConstOf n) | return none
  let some inP ← boolVal? a[1]! | return none
  let some interactive ← boolVal? a[2]! | return none
  let some inForm ← boolVal? a[3]! | return none
  return some { mode, inP, interactive, inForm }

private def htmlCtxExpr (c : HtmlCtx) : Expr :=
  mkApp4 (mkConst ``HtmlCtx.mk) (mkConst ((tagModeTable.find? (·.2 == c.mode)).map Prod.fst |>.getD ``TagMode.normal)) (toExpr c.inP) (toExpr c.interactive) (toExpr c.inForm)

dsimproc [simp] reduceStepHtmlCtx (stepHtmlCtx _ _) := fun e => do
  let a := e.getAppArgs; if a.size != 2 then return .continue
  let some tag := strLitVal? a[1]! | return .continue
  let some ctx ← htmlCtxVal? a[0]! | return .continue
  return .done <| match Qed.stepHtmlCtx ctx tag with
    | some next => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) (htmlCtxExpr next)
    | none      => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``HtmlCtx)

private def strBoolSimproc (f : String → Bool) : Simp.DSimproc := fun e => do
  let some s := strLitVal? e.appArg! | return .continue
  return .done (toExpr (f s))

dsimproc [simp] reduceIsVoidTag (isVoidTag _) := strBoolSimproc Qed.isVoidTag
dsimproc [simp] reduceIsSafeAttrName (isSafeAttrName _) := strBoolSimproc Qed.isSafeAttrName
dsimproc [simp] reduceIsUrlAttrName (isUrlAttrName _) := strBoolSimproc Qed.isUrlAttrName
dsimproc [simp] reduceIsSafeUrl (isSafeUrl _) := strBoolSimproc Qed.isSafeUrl
dsimproc [simp] reduceTagBlocksDirectSpan (tagBlocksDirectSpan _) := strBoolSimproc Qed.tagBlocksDirectSpan
dsimproc [simp] reduceTagBlocksSpanSubtree (tagBlocksSpanSubtree _) := strBoolSimproc Qed.tagBlocksSpanSubtree
dsimproc [simp] reduceContainsCloseSeq (containsCloseSeq (String.toList _)) := fun e => do
  let some s := strLitVal? e.appArg!.appArg! | return .continue
  return .done (toExpr (Qed.containsCloseSeq s.toList))

private def isUnfoldableUserDef (env : Environment) (viewOnly : Bool) (n : Name) : MetaM Bool := do
  if !qedIsHelper env n then return false
  if viewOnly && (qedLooksGenerated n || match n with
      | .str _ s => ["formView", "keyOf", "update", "updateKeyed", "regs", "reg", "init", "subscriptions"].contains s | _ => false) then return false
  if (← getProjectionFnInfo? n).isSome then return false
  match env.find? n with
  | some (.defnInfo d) =>
      if #[``Qed.Theme, ``Qed.Keyframes, ``Qed.Url, `Qed.LocalDef].any d.type.isConstOf ||
         #[(``Qed.TypedToken, 1), (`Qed.Codec, 1), (`Qed.App, 2), (`Qed.Dehydrate, 1)].any (fun (c, k) => d.type.isAppOfArity c k) then return false
      return !viewOnly || d.type.getForallBody.getUsedConstants.any (#[``Qed.Html, ``Qed.View, ``Qed.Attr, ``Qed.VAttr, `Qed.Component].contains ·)
  | _ => return false

def qedHtmlHelperNames : Array Name := #[
  ``Qed.text, ``Qed.lazy, ``Qed.el, ``Qed.link, ``Qed.linkTo, ``Qed.cls, ``Qed.attr, ``Qed.role,
  ``Qed.on, ``Qed.onValue, ``Qed.onClick, ``Qed.onInput, ``Qed.onChange, ``Qed.onCheck, ``Qed.onKeydown, ``Qed.onKeyup,
  ``Qed.onSubmit, ``Qed.onBlur, ``Qed.onFocus, ``Qed.onDoubleClick, ``Qed.onMouseDown, ``Qed.onMouseUp,
  ``Qed.key, ``Qed.value, ``Qed.placeholder, ``Qed.name, ``Qed.href, ``Qed.src, ``Qed.action, ``Qed.alt, ``Qed.title,
  ``Qed.style, ``Qed.inlineStyle, ``Qed.styleVars, ``Qed.type', ``Qed.disabled, ``Qed.required, ``Qed.checked, ``Qed.readOnly]
def qedForEachHelperNames : Array Name := #[`Qed.ForEachItems.toList_array, `Qed.ForEachItems.toList_list, `Qed.ForEachItems.toArray, `Qed.mapList_eq]
private def viewEquivHelperNames (env : Environment) : Array Name :=
  #[``V.bindAttr, ``V.dynAttr, ``V.onClick', ``V.onInput', ``V.onCheck'] ++ qedHtmlHelperNames ++
    (#[`Qed.Component.render, `Qed.localMount, `Qed.localMountWith] ++ qedForEachHelperNames).filter env.contains
def viewCoreUnfolds : Array Name := #[
  ``View.render, ``View.renderEach, ``View.showIf, ``View.ofHtml, ``VAttr.eval, ``V.el, ``V.text, ``V.dyn,
  ``V.ifElse, ``V.static, ``V.dynNode, ``V.memo, ``V.render_forEach, ``View.isDyn]
private def viewFrameworkUnfolds (env : Environment) : Array Name :=
  #[``Html.valid, ``Html.validIn, ``Html.validListIn, ``Attr.validKeyValue, ``View.renderSig, ``View.renderSigList,
    ``View.hasOpaque, ``View.hasOpaqueList, ``View.collectDyn, ``View.collectDynList, ``dynValGets, ``SoundMemo.ofLawful] ++ viewCoreUnfolds ++ viewEquivHelperNames env

private def qedUnfoldHelpers (maxIters : Nat) (allowView : Bool) (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[])
    (includeLCtx : Bool := false) (tryRfl : Bool := false) : TacticM Unit :=
  qedUnfoldHelperLoop maxIters (isUnfoldableUserDef · allowView ·) extraLemmas (includeLCtx := includeLCtx) (tryRfl := tryRfl)
private def simpAllGoalsWith (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) : TacticM Unit := do setGoals <| ← (← getGoals).filterMapM (simpGoalOnly · ctx sp)

private def runGoalsFixpoint (maxIters : Nat) (step : TacticM Unit) : TacticM Unit := do
  let snap := fun () => do (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
  let rec go : Nat → TacticM Unit
    | 0 => pure ()
    | n + 1 => do if !(← getGoals).isEmpty then let before ← snap (); step; if !(← getGoals).isEmpty then if before != (← snap ()) then go n
  go maxIters

private abbrev ProveValidM := StateRefT (Array MVarId) MetaM
private def rflBoolTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
private def rflBoolFalse : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)
private def mkBoolEq (lhs rhs : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs
private def mkBoolEqTrue (lhs : Expr) : Expr := mkBoolEq lhs (mkConst ``Bool.true)
private def defaultHtmlCtx : HtmlCtx := {}
private def defaultHtmlCtxExpr : Expr := htmlCtxExpr defaultHtmlCtx
private def emitValidMVar (goalTy : Expr) : ProveValidM Expr := do let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy; modify (·.push m.mvarId!); return m
private def isMatcherOrCases (fn : Name) : MetaM Bool := do
  if ← Meta.isMatcher fn then return true
  return match fn with | .str _ s => s == "casesOn" || s == "recOn" | _ => false
private def isSafeKeyLit (k : Expr) : Bool := (strLitVal? k).any Qed.isSafeAttrName
private def isSafeKeyValLit (k v : Expr) : Bool := (strLitVal? k).any fun ks => Qed.isSafeAttrName ks && (!Qed.isUrlAttrName ks || (strLitVal? v).any Qed.isSafeUrl)
private def stripLetFuel : Nat := 256
def stripLetE : Nat → Expr → Expr
  | 0, e => e.consumeMData.headBeta
  | fuel + 1, e => match e.consumeMData.headBeta with | .letE _ _ val body _ => stripLetE fuel (body.instantiate1 val) | e => e

private inductive AttrKind where | zeroCostNonCell | zeroCostCell | nonCellSafe | nonCellCheck (defValid : Bool) | unknown
private def classifyAttr (a : Expr) : AttrKind :=
  let a := stripLetE stripLetFuel a; let args := a.getAppArgs
  match a.getAppFn.constName? with
  | some fn =>
      if #[``Attr.cls, ``Qed.cls, ``Attr.key, ``Qed.key, ``Attr.empty, ``Attr.signalBind].contains fn then .zeroCostNonCell
      else if #[``Attr.localCell, `Qed.localMount, `Qed.localMountWith].contains fn then .zeroCostCell
      else if fn == ``Qed.onCheck || fn == ``Qed.value || fn == ``Qed.ariaRole || qedAttrWrapperMap.contains fn ||
              (fn == ``VAttr.eval && args.size == 4 && args[3]!.consumeMData.getAppFn.constName? == some ``V.onCheck') then .nonCellSafe
      else if #[``Attr.flag, ``Attr.on, ``Attr.onValue].contains fn && args.size >= 3 then .nonCellCheck (isSafeKeyLit args[1]!)
      else if (fn == ``Attr.attr || fn == ``Attr.signalAttr) && args.size >= 3 then .nonCellCheck (isSafeKeyValLit args[args.size - 2]! args[args.size - 1]!)
      else if fn == ``Qed.attr && args.size == 5 then .nonCellCheck (isSafeKeyValLit args[3]! args[4]!)
      else if #[``Qed.href, ``Qed.src, ``Qed.action, ``Attr.flag, ``Attr.on, ``Attr.onValue, ``Attr.attr, ``Attr.signalAttr, ``Qed.attr].contains fn then .nonCellCheck false
      else .unknown
  | none => .unknown
private def AttrKind.isZeroCost : AttrKind → Bool | .zeroCostNonCell | .zeroCostCell => true | _ => false
private def AttrKind.isDefValid : AttrKind → Bool | .zeroCostNonCell | .zeroCostCell | .nonCellSafe | .nonCellCheck true => true | _ => false
private def AttrKind.isNonCell : AttrKind → Bool | .zeroCostNonCell | .nonCellSafe | .nonCellCheck _ => true | _ => false

private def evalVAttrExpr (sigmaTy msgTy sExpr va : Expr) : Expr :=
  let va := va.consumeMData; let a := va.getAppArgs
  match va.getAppFn.constName?, a.size with
  | some ``VAttr.stat, 3 => a[2]! | some ``VAttr.bind, 3 | some ``V.bindAttr, 3 => (mkApp a[2]! sExpr).headBeta
  | some ``VAttr.dynVal, 4 | some ``V.dynAttr, 4 => mkApp3 (mkConst ``Attr.attr) a[1]! a[2]! (mkApp a[3]! sExpr)
  | some ``VAttr.dynOn, 4 => mkApp3 (mkConst ``Attr.on) a[1]! a[2]! (mkApp a[3]! sExpr)
  | some ``V.onClick', 3 => mkApp3 (mkConst ``Attr.on) a[1]! (toExpr "click") (mkApp a[2]! sExpr)
  | some ``V.onInput', 3 => mkApp3 (mkConst ``Attr.onValue) a[1]! (toExpr "input") (mkApp a[2]! sExpr)
  | _, _ => mkApp4 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr va

private def expandVAttrMap (sigmaTy msgTy sExpr : Expr) : Nat → Expr → Expr
  | fuel, vattrs =>
      let fallback := mkAppN (mkConst ``List.map [Level.zero, Level.zero]) #[mkApp2 (mkConst ``VAttr) sigmaTy msgTy, mkApp (mkConst ``Attr) msgTy, mkApp3 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr, vattrs]
      match fuel with
      | 0 => fallback
      | fuel + 1 =>
          let v := vattrs.consumeMData.headBeta
          if v.isAppOfArity ``List.nil 1 then mkApp (mkConst ``List.nil [Level.zero]) (mkApp (mkConst ``Attr) msgTy)
          else if v.isAppOfArity ``List.cons 3 then
            let a := v.getAppArgs
            mkApp3 (mkConst ``List.cons [Level.zero]) (mkApp (mkConst ``Attr) msgTy) (evalVAttrExpr sigmaTy msgTy sExpr a[1]!) (expandVAttrMap sigmaTy msgTy sExpr fuel a[2]!)
          else fallback

private def normalizeAttrsExpr (attrs : Expr) : Expr :=
  let attrs := attrs.consumeMData.headBeta
  if attrs.isAppOfArity ``List.map 4 then
    let a := attrs.getAppArgs; let fn := a[2]!.consumeMData
    if fn.isAppOfArity ``VAttr.eval 3 then let f := fn.getAppArgs; expandVAttrMap f[0]! f[1]! f[2]! 128 a[3]! else attrs
  else attrs

private def allAttrList (p : AttrKind → Bool) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, attrs => let a := attrs.consumeMData; a.isAppOfArity ``List.nil 1 || (a.isAppOfArity ``List.cons 3 && p (classifyAttr a.getAppArgs[1]!) && allAttrList p fuel a.getAppArgs[2]!)

private def withHypLam (ty : Expr) (k : Expr → ProveValidM Expr) : ProveValidM Expr := withLocalDeclD `_qed_h ty fun h => do mkLambdaFVars #[h] (← k h)
private def proveResBranches (α ready loading failed idle : Expr) (k : Expr → ProveValidM Expr) : ProveValidM (Array Expr) := do
  return #[← k idle, ← k loading, ← withHypLam α (k <| mkApp ready ·), ← withHypLam (mkConst ``String) (k <| mkApp failed ·)]

private structure CtrlFlowSpec where
  (iteLem? diteLem? : Option Name := none) (prefixArgs postBranchArgs : Array Expr := #[]) (allowSplit allowUnfold : Bool := true)

@[noinline] private def proveCtrlFlow? (env : Environment) (spec : CtrlFlowSpec) (e : Expr) (proveRec : Expr → ProveValidM Expr) (onSplit : ProveValidM Expr) : ProveValidM (Option Expr) := do
  let a := e.getAppArgs
  let branch (lem : Name) (isDite : Bool) := do
    let pfT ← withHypLam a[1]! fun fv => proveRec (if isDite then mkApp a[3]! fv else a[3]!)
    let pfF ← withHypLam (mkApp (mkConst ``Not) a[1]!) fun fv => proveRec (if isDite then mkApp a[4]! fv else a[4]!)
    return some <| mkAppNode lem (spec.prefixArgs ++ #[a[1]!, a[2]!, a[3]!, a[4]!] ++ spec.postBranchArgs ++ #[pfT, pfF])
  if let some lem := spec.iteLem? then if e.isAppOfArity ``ite 5 then return ← branch lem false
  if let some lem := spec.diteLem? then if e.isAppOfArity ``dite 5 then return ← branch lem true
  if let some fn := e.getAppFn.constName? then
    if spec.allowSplit then if ← isMatcherOrCases fn then return some (← onSplit)
    if spec.allowUnfold then if ← liftM (isUnfoldableUserDef env true fn) then
      if let some eUnf ← Meta.unfoldDefinition? e then return some (← proveRec eUnf)
  return none

private structure ListCombinatorSpec where
  (nilExpr? : Option Expr := none) (consLem : Name) (appendLem? mapLem? toListMapLem? : Option Name := none) (prefixArgs : Array Expr) (postArgs : Array Expr := #[])

@[noinline] private def proveListCombinator? (spec : ListCombinatorSpec) (xs : Expr) (proveElem proveRec : Expr → ProveValidM Expr) : ProveValidM (Option Expr) := do
  let a := xs.getAppArgs
  if let some nilPf := spec.nilExpr? then if xs.isAppOfArity ``List.nil 1 then return some nilPf
  if xs.isAppOfArity ``List.cons 3 then return some <| mkAppNode spec.consLem (spec.prefixArgs ++ #[a[1]!, a[2]!] ++ spec.postArgs ++ #[← proveElem a[1]!, ← proveRec a[2]!])
  if let some appLem := spec.appendLem? then if xs.isAppOfArity ``HAppend.hAppend 6 then
    return some <| mkAppNode appLem (spec.prefixArgs ++ #[a[4]!, a[5]!] ++ spec.postArgs ++ #[← proveRec a[4]!, ← proveRec a[5]!])
  let proveMap (lem : Name) (m : Array Expr) := do
    return some <| mkAppNode lem (#[m[0]!] ++ spec.prefixArgs ++ #[m[3]!, m[2]!] ++ spec.postArgs ++ #[← withHypLam m[0]! fun x => proveElem (mkApp m[2]! x)])
  if let some mapLem := spec.mapLem? then if xs.isAppOfArity ``List.map 4 then return ← proveMap mapLem a
  if let some tlmLem := spec.toListMapLem? then
    if xs.isAppOfArity ``Array.toList 2 then let inner := a[1]!.consumeMData; if inner.isAppOfArity ``Array.map 4 then return ← proveMap tlmLem inner.getAppArgs
  return none

private def urlAttrLemmas : List (Name × Name) := [(``Qed.href, ``Qed.Attr.valid_href), (``Qed.src, ``Qed.Attr.valid_src), (``Qed.action, ``Qed.Attr.valid_action)]
private def localAttrLemmas : List (Name × Name) := [(`Qed.Attr.localProps, `Qed.Attr.valid_localProps_intro), (`Qed.Attr.localInit, `Qed.Attr.valid_localInit_intro)]

@[noinline] private def proveAttrValid (env : Environment) (msgTy a : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a))
  | fuel + 1 => do
      let a := stripLetE stripLetFuel a; let kind := classifyAttr a
      if kind.isZeroCost then return rflBoolTrue
      if let some pf := fastAttrValidProof? msgTy a then return pf
      if kind.isDefValid then return rflBoolTrue
      let args := a.getAppArgs; let fn? := a.getAppFn.constName?
      if let some (_, lem) := fn?.bind fun fn => if args.size == 4 then urlAttrLemmas.find? (·.1 == fn) else none then return mkApp4 (mkConst lem) args[0]! args[1]! args[2]! args[3]!
      if let some (_, lem) := fn?.bind fun fn => if args.size == 5 then localAttrLemmas.find? (·.1 == fn) else none then
        if env.contains lem then return mkAppNode lem (args.push (← proveAttrValid env msgTy args[3]! fuel))
      if a.isAppOfArity ``Attr.attr 3 && isSafeKeyLit args[1]! then
        let val := args[2]!.consumeMData
        if val.isAppOfArity ``Qed.ToHref.toHref 3 then let t := val.getAppArgs; return mkAppNode ``Qed.ToHref.valid_attr #[args[0]!, t[0]!, t[1]!, args[1]!, t[2]!, rflBoolTrue]
      let goalTy := mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a)
      if let some pf ← proveCtrlFlow? env { iteLem? := some ``Qed.Attr.valid_ite_intro, diteLem? := some ``ValidLemmas.attr_valid_dite_intro, prefixArgs := #[msgTy], allowSplit := false } a (proveAttrValid env msgTy · fuel) (emitValidMVar goalTy) then return pf
      emitValidMVar goalTy

private def proveAttrValidList (env : Environment) (msgTy attrs : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))
  | fuel + 1 => do
      let attrs := normalizeAttrsExpr attrs
      if attrs.isAppOfArity ``List.nil 1 || allAttrList AttrKind.isZeroCost 128 attrs then return rflBoolTrue
      if let some pf ← proveListCombinator? { consLem := ``Qed.Attr.validList_cons_intro, appendLem? := some ``Qed.Attr.validList_append_intro, prefixArgs := #[msgTy] } attrs (proveAttrValid env msgTy · fuel) (proveAttrValidList env msgTy · fuel) then return pf
      emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))

private def proveAttrIsLocalCellFalse (msgTy a : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let a := stripLetE stripLetFuel a
      if (classifyAttr a).isNonCell then some rflBoolFalse
      else
        let args := a.getAppArgs
        let branch? := if a.isAppOfArity ``ite 5 then some (``Qed.Attr.isLocalCell_ite_eq_false, `_qed_h, `_qed_h, args[3]!, args[4]!)
          else if a.isAppOfArity ``dite 5 then match args[3]!.consumeMData, args[4]!.consumeMData with
            | .lam nT _ bT _, .lam nF _ bF _ => if !bT.hasLooseBVars && !bF.hasLooseBVars then some (``ValidLemmas.attr_isLocalCell_dite_eq_false, nT, nF, bT, bF) else none | _, _ => none
          else none
        branch?.bind fun (lem, nT, nF, bT, bF) => do
          let pT ← proveAttrIsLocalCellFalse msgTy bT fuel; let pF ← proveAttrIsLocalCellFalse msgTy bF fuel
          return mkAppNode lem #[msgTy, args[1]!, args[2]!, args[3]!, args[4]!, .lam nT args[1]! pT .default, .lam nF (mkApp (mkConst ``Not) args[1]!) pF .default]

private def proveAttrHasLocalCellFalse (msgTy attrs : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let attrs := normalizeAttrsExpr attrs
      if allAttrList AttrKind.isNonCell 128 attrs || attrs.isAppOfArity ``List.nil 1 then some rflBoolFalse
      else if attrs.isAppOfArity ``List.cons 3 then let a := attrs.getAppArgs; do return mkAppNode ``Qed.Attr.hasLocalCell_cons_eq_false #[msgTy, a[1]!, a[2]!, ← proveAttrIsLocalCellFalse msgTy a[1]! fuel, ← proveAttrHasLocalCellFalse msgTy a[2]! fuel]
      else if attrs.isAppOfArity ``HAppend.hAppend 6 then let a := attrs.getAppArgs; do return mkAppNode ``Qed.Attr.hasLocalCell_append_eq_false #[msgTy, a[4]!, a[5]!, ← proveAttrHasLocalCellFalse msgTy a[4]! fuel, ← proveAttrHasLocalCellFalse msgTy a[5]! fuel]
      else none

private def proveNotOrEmpty (elemTy predE kids : Expr) (pFalse? : Option Expr) : ProveValidM Expr := do
  let notP := mkApp (mkConst ``Bool.not) predE
  if kids.consumeMData.isAppOfArity ``List.nil 1 then return mkApp (mkConst ``Bool.or_true) notP
  let isEmptyE := mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids
  if let some pF := pFalse? then return mkApp3 (mkConst ``Qed.Bool.not_false_or) predE isEmptyE pF
  emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Bool.or) notP isEmptyE))

private def proveVoidObligation (elemTy tagE kids : Expr) (tagS : String) : ProveValidM Expr := do
  if !Qed.isVoidTag tagS then
    let isEmptyE := mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids
    return match nonVoidTagMap[tagS]? with | some lem => mkApp3 (mkConst ``ValidLemmas.not_isVoidTag_or) tagE isEmptyE (mkConst lem) | none => rflBoolTrue
  proveNotOrEmpty elemTy (mkApp (mkConst ``Qed.isVoidTag) tagE) kids none

private def proveCellObligation (elemTy msgTy evalAttrs kids : Expr) : ProveValidM Expr := do
  if allAttrList AttrKind.isNonCell 128 evalAttrs then return rflBoolTrue
  proveNotOrEmpty elemTy (mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs) kids (proveAttrHasLocalCellFalse msgTy evalAttrs 128)

private def proveTextValidIn (ctxV : HtmlCtx) (str goalTy : Expr) : ProveValidM Expr := do
  match ctxV.mode with
  | .normal | .option | .textarea | .svg => return rflBoolTrue
  | .rawStyle =>
      if strLitVal? str == some "" || (strLitVal? str).any (!Qed.containsCloseSeq ·.toList) then return rflBoolTrue
      if str.consumeMData.isAppOfArity ``Qed.escapeRawText 1 then return mkApp4 (mkConst ``Qed.validTextIn_rawStyle_escape) (toExpr ctxV.inP) (toExpr ctxV.interactive) (toExpr ctxV.inForm) str.consumeMData.appArg!
      emitValidMVar goalTy
  | _ => if strLitVal? str == some "" then return rflBoolTrue else emitValidMVar goalTy

private def tryFormViewValidIn (env : Environment) (ctxV : HtmlCtx) (fn : Name) (args : Array Expr) : ProveValidM (Option Expr) := do
  if fn.toString.endsWith ".formView" && args.size >= 4 && ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
    let lem := fn.getPrefix ++ `formView_validIn
    if env.contains lem then
      let k := args.size - 3; let pf := mkAppNode lem (args.extract 0 k ++ #[toExpr ctxV.inForm] ++ args.extract k args.size)
      if ← Meta.isTypeCorrect pf then return some pf
  return none

private inductive TargetKind where | html | view (sigmaTy sExpr : Expr)
private def htmlNodeWrappers : List (Name × Nat × Name) := [(``Qed.withKey, 3, ``Qed.Html.validIn_withKey_intro), (``Html.prefixSignals, 3, ``Qed.Html.validIn_prefixSignals_intro), (``Html.map, 4, ``Qed.Html.validIn_map_intro)]
private def htmlListWrappers : List (Name × Nat × Name) := [(``Html.prefixSignalsList, 3, ``Qed.Html.validListIn_prefixSignalsList_intro), (``Html.mapChildren, 4, ``Qed.Html.validListIn_mapChildren_intro)]

@[noinline] private def proveWrapper? (wrappers : List (Name × Nat × Name)) (fn? : Option Name) (a : Array Expr)
    (ctxE msgTy : Expr) (proveRec : Expr → Expr → ProveValidM Expr) : ProveValidM (Option Expr) := do
  let some fn := fn? | return none
  let some (_, ar, lem) := wrappers.find? fun (c, n, _) => c == fn && n == a.size | return none
  if ar == 3 then return some <| mkAppNode lem #[msgTy, ctxE, a[1]!, a[2]!, ← proveRec msgTy a[2]!]
  else return some <| mkAppNode lem #[a[0]!, a[1]!, ctxE, a[2]!, a[3]!, ← proveRec a[0]! a[3]!]

@[noinline] private def proveElementCore (env : Environment) (kind : TargetKind) (ctxV : HtmlCtx) (msgTy tagE attrs kids : Expr) (tagS : String) :
    ProveValidM (Option (HtmlCtx × Expr × Expr × Expr × Expr × Expr)) := do
  let some childCtx := Qed.stepHtmlCtx ctxV tagS | return none
  let childCtxE := htmlCtxExpr childCtx
  let (evalAttrs, elemTy) := match kind with | .html => (attrs, mkApp (mkConst ``Html) msgTy) | .view σ s => (expandVAttrMap σ msgTy s 128 attrs, mkApp2 (mkConst ``View) σ msgTy)
  return some (childCtx, childCtxE, proveStepHtmlCtx ctxV tagS childCtxE, ← proveAttrValidList env msgTy evalAttrs 128, ← proveVoidObligation elemTy tagE kids tagS, ← proveCellObligation elemTy msgTy evalAttrs kids)

@[noinline] private def finishForEachProof (env : Environment) (ctxV : HtmlCtx)
    (sigmaTy msgTy ctxE childCtxE tagE alpha items key child attrs sigPrefix sExpr pfChild : Expr) (tagS : String) : ProveValidM Expr := do
  let evalAttrs := expandVAttrMap sigmaTy msgTy sExpr 128 attrs
  let hcell ← if allAttrList AttrKind.isNonCell 128 evalAttrs then pure rflBoolTrue
    else if let some pF := proveAttrHasLocalCellFalse msgTy evalAttrs 128 then Meta.mkAppM ``congrArg #[mkConst ``Bool.not, pF]
    else emitValidMVar (mkBoolEqTrue (mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs)))
  let partialArgs := #[alpha, sigmaTy, msgTy, ctxE, childCtxE, tagE, items, key, child, attrs, sigPrefix, sExpr,
    proveStepHtmlCtx ctxV tagS childCtxE, (nonVoidTagMap[tagS]?.map mkConst).getD rflBoolFalse, hcell, ← proveAttrValidList env msgTy evalAttrs 128, pfChild]
  let hsigTy := (← Meta.inferType (mkAppNode ``V.validIn_render_forEach partialArgs)).bindingDomain!
  let hsig ← if ← Meta.isDefEq hsigTy (mkBoolEqTrue (mkConst ``Bool.true)) then pure rflBoolTrue else emitValidMVar hsigTy
  return mkAppNode ``V.validIn_render_forEach (partialArgs.push hsig)

mutual
  @[noinline] private partial def proveSplitSubgoal (fuel : Nat) (env : Environment) (goalTy : Expr) : ProveValidM Expr := do
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
        match ← try m.mvarId!.withContext do Meta.splitTarget? m.mvarId! catch _ => pure none with
        | some sgs => sgs.forM (proveGoalMVar fuel env); instantiateMVars m | none => modify (·.push m.mvarId!); return m

  @[noinline] private partial def proveHtmlNode (fuel : Nat) (env : Environment) (ctxV : HtmlCtx) (ctxE msgTy node goalTy : Expr) : ProveValidM Expr := do
    let a := node.getAppArgs; let fn? := node.getAppFn.constName?
    if node.isAppOfArity ``Html.text 2 then return ← proveTextValidIn ctxV a[1]! goalTy
    if node.isAppOfArity ``Qed.text 4 then match ctxV.mode with | .normal | .option | .textarea | .svg => return rflBoolTrue | _ => pure ()
    if let some pf ← proveWrapper? htmlNodeWrappers fn? a ctxE msgTy (proveNode fuel env .html ctxV ctxE) then return pf
    if node.isAppOfArity ``Html.ofOption 2 then
      let opt := a[1]!.consumeMData
      if opt.isAppOfArity ``Option.none 1 then return mkApp (mkConst ``Qed.validTextIn_empty) ctxE
      if opt.isAppOfArity ``Option.some 2 then return ← proveNode fuel env .html ctxV ctxE msgTy opt.getAppArgs[1]!
      return ← proveSplitSubgoal fuel env goalTy
    if node.isAppOfArity ``View.render 4 then return ← proveNode fuel env (.view a[0]! a[3]!) ctxV ctxE a[1]! a[2]!
    if fn? == some ``Qed.lazy && a.size == 5 then return ← proveNode fuel env .html ctxV ctxE msgTy (mkApp a[3]! a[4]!).headBeta
    if fn? == some ``Qed.link || fn? == some ``Qed.linkTo then if let some hUnf ← Meta.unfoldDefinition? node then return ← proveNode fuel env .html ctxV ctxE msgTy hUnf
    if fn? == some `Qed.Resource.awaitView && a.size == 9 && env.contains `Qed.Resource.validIn_awaitView_intro then
      return mkAppNode `Qed.Resource.validIn_awaitView_intro (#[a[0]!, a[1]!, msgTy, a[3]!, ctxE, a[4]!, a[5]!, a[6]!, a[7]!, a[8]!] ++ (← proveResBranches a[1]! a[5]! a[6]! a[7]! a[8]! (proveNode fuel env .html ctxV ctxE msgTy)))
    if (fn? == some `Qed.Resource.view || (fn? == some `Qed.Cached.view && env.contains `Qed.Cached.state)) && a.size == 7 && env.contains `Qed.Resource.validIn_view_intro then
      let r := if fn? == some `Qed.Cached.view then mkApp2 (mkConst `Qed.Cached.state) a[0]! a[2]! else a[2]!
      return mkAppNode `Qed.Resource.validIn_view_intro (#[a[0]!, msgTy, ctxE, r, a[3]!, a[4]!, a[5]!, a[6]!] ++ (← proveResBranches a[0]! a[3]! a[4]! a[5]! a[6]! (proveNode fuel env .html ctxV ctxE msgTy)))
    if let some fn := fn? then if let some pf ← tryFormViewValidIn env ctxV fn a then return pf
    if let some pf ← proveCtrlFlow? env { iteLem? := some ``Qed.Html.validIn_ite_intro, diteLem? := some ``Qed.Html.validIn_dite_intro, prefixArgs := #[msgTy, ctxE] } node (proveNode fuel env .html ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
    emitValidMVar goalTy

  @[noinline] private partial def proveViewNode (fuel : Nat) (env : Environment) (sigmaTy sExpr : Expr) (ctxV : HtmlCtx) (ctxE msgTy node goalTy : Expr) : ProveValidM Expr := do
    let kind := TargetKind.view sigmaTy sExpr; let a := node.getAppArgs; let fn? := node.getAppFn.constName?
    let loweredHtml? : Option Expr := match fn?, a.size with
      | some ``View.text, 3 | some ``V.text, 3 => some (mkApp2 (mkConst ``Html.text) msgTy a[2]!)
      | some ``View.dyn, 3 | some ``V.dyn, 3 => some (mkApp2 (mkConst ``Html.text) msgTy (mkApp a[2]! sExpr))
      | some ``View.static, 3 | some ``V.static, 3 => some a[2]!
      | some ``View.dynNode, 3 | some ``V.dynNode, 3 | some ``View.ofHtml, 3 => some (mkApp a[2]! sExpr)
      | some ``V.memo, 6 => some (mkApp a[4]! (mkApp a[5]! sExpr))
      | some ``View.memo, 3 => if a[2]!.consumeMData.isAppOfArity ``SoundMemo.ofLawful 6 then let sm := a[2]!.consumeMData.getAppArgs; some (mkApp sm[4]! (mkApp sm[5]! sExpr)) else none
      | _, _ => none
    if let some hExpr := loweredHtml? then return ← proveNode fuel env .html ctxV ctxE msgTy hExpr
    if node.isAppOfArity ``View.showIf 4 || node.isAppOfArity ``V.showIf 4 then
      return mkAppNode ``View.validIn_render_showIf #[sigmaTy, msgTy, ctxE, a[2]!, a[3]!, sExpr, ← withHypLam (mkBoolEqTrue (mkApp a[2]! sExpr)) fun _ => proveNode fuel env kind ctxV ctxE msgTy a[3]!]
    if node.isAppOfArity ``View.ifElse 5 || node.isAppOfArity ``V.ifElse 5 then
      let pfY ← withHypLam (mkBoolEqTrue (mkApp a[2]! sExpr)) fun _ => proveNode fuel env kind ctxV ctxE msgTy a[3]!
      let pfN ← withHypLam (mkBoolEq (mkApp a[2]! sExpr) (mkConst ``Bool.false)) fun _ => proveNode fuel env kind ctxV ctxE msgTy a[4]!
      return mkAppNode ``View.validIn_render_ifElse #[sigmaTy, msgTy, ctxE, a[2]!, a[3]!, a[4]!, sExpr, pfY, pfN]
    if node.isAppOfArity ``V.forEach 9 then
      if let some tagS := strLitVal? a[3]! then if !Qed.isVoidTag tagS then if let some childCtx := Qed.stepHtmlCtx ctxV tagS then
        let childCtxE := htmlCtxExpr childCtx
        let pfChild ← withHypLam a[2]! fun x => proveNode fuel env (.view a[2]! x) childCtx childCtxE msgTy a[6]!
        return ← finishForEachProof env ctxV sigmaTy msgTy ctxE childCtxE a[3]! a[2]! a[4]! a[5]! a[6]! a[7]! a[8]! sExpr pfChild tagS
    if node.isAppOfArity ``View.mapScope 5 then
      return mkAppNode ``Qed.View.validIn_render_mapScope_intro #[sigmaTy, a[1]!, msgTy, ctxE, a[3]!, a[4]!, sExpr, ← proveNode fuel env (.view a[1]! (mkApp a[3]! sExpr)) ctxV ctxE msgTy a[4]!]
    if let some pf ← proveCtrlFlow? env { iteLem? := some ``Qed.View.validIn_render_ite_intro, prefixArgs := #[sigmaTy, msgTy, ctxE], postBranchArgs := #[sExpr] } node (proveNode fuel env kind ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
    emitValidMVar goalTy

  @[noinline] private partial def proveNode (fuel : Nat) (env : Environment) (kind : TargetKind) (ctxV : HtmlCtx) (ctxE msgTy node : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue <| mkApp3 (mkConst ``Html.validIn) msgTy ctxE <| match kind with | .html => node | .view σ s => mkApp4 (mkConst ``View.render) σ msgTy node s
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let node := stripLetE stripLetFuel node; let a := node.getAppArgs
        let elemArgs? := match kind with
          | .html => if node.isAppOfArity ``Html.element 4 || node.isAppOfArity ``Qed.el 4 then some (a[1]!, a[2]!, a[3]!) else none
          | .view _ _ => if node.isAppOfArity ``View.element 5 || node.isAppOfArity ``V.el 5 then some (a[2]!, a[3]!, a[4]!) else none
        if let some (tagE, attrsE, kidsE) := elemArgs? then
          if let some tagS := strLitVal? tagE then
            if let some (childCtx, childCtxE, hstep, hattrs, hvoid, hcell) ← proveElementCore env kind ctxV msgTy tagE attrsE kidsE tagS then
              let hkids ← proveNodeList fuel env kind childCtx childCtxE msgTy kidsE
              return match kind with
                | .html => mkAppNode ``Qed.Html.validIn_element_intro #[msgTy, ctxE, childCtxE, tagE, attrsE, kidsE, hstep, hattrs, hvoid, hcell, hkids]
                | .view σ s => mkAppNode ``View.validIn_render_element_intro #[σ, msgTy, ctxE, childCtxE, tagE, attrsE, kidsE, s, hstep, hattrs, hvoid, hcell, hkids]
          return ← emitValidMVar goalTy
        match kind with
        | .html => proveHtmlNode fuel env ctxV ctxE msgTy node goalTy
        | .view σ s => proveViewNode fuel env σ s ctxV ctxE msgTy node goalTy

  @[noinline] private partial def proveNodeList (fuel : Nat) (env : Environment) (kind : TargetKind) (ctxV : HtmlCtx) (ctxE msgTy cs : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue <| mkApp3 (mkConst ``Html.validListIn) msgTy ctxE <| match kind with | .html => cs | .view σ s => mkApp4 (mkConst ``View.renderEach) σ msgTy cs s
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let cs := stripLetE stripLetFuel cs; let a := cs.getAppArgs; let fn? := cs.getAppFn.constName?
        if fn? == some `Qed.ForEachItems.toList || fn? == some ``Qed.mapList then
          if let some csUnf ← Meta.unfoldDefinition? cs then return ← proveNodeList fuel env kind ctxV ctxE msgTy csUnf
        match kind with
        | .html =>
            let listSpec : ListCombinatorSpec := {
              nilExpr? := some (mkApp2 (mkConst ``Qed.Html.validListIn_nil) msgTy ctxE), consLem := ``Qed.Html.validListIn_cons_intro,
              appendLem? := some ``Qed.Html.validListIn_append_intro, mapLem? := some ``Qed.Html.validListIn_map_intro,
              toListMapLem? := some ``Qed.Html.validListIn_toList_map_intro, prefixArgs := #[msgTy, ctxE] }
            if let some pf ← proveListCombinator? listSpec cs (proveNode fuel env .html ctxV ctxE msgTy) (proveNodeList fuel env .html ctxV ctxE msgTy) then return pf
            if let some pf ← proveWrapper? htmlListWrappers fn? a ctxE msgTy (proveNodeList fuel env .html ctxV ctxE) then return pf
            if cs.isAppOfArity ``View.renderEach 4 then return ← proveNodeList fuel env (.view a[0]! a[3]!) ctxV ctxE a[1]! a[2]!
            if fn? == some `Qed.Codec.formFieldRow && a.size == 7 && env.contains `Qed.Codec.formFieldRow_validListIn && ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
              return mkAppNode `Qed.Codec.formFieldRow_validListIn #[msgTy, toExpr ctxV.inForm, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, ← proveNode fuel env .html ctxV ctxE msgTy a[6]!]
            if let some pf ← proveCtrlFlow? env { iteLem? := some ``Qed.Html.validListIn_ite_intro, diteLem? := some ``ValidLemmas.validListIn_dite_intro, prefixArgs := #[msgTy, ctxE] } cs (proveNodeList fuel env .html ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
            emitValidMVar goalTy
        | .view sigmaTy sExpr =>
            let listSpec : ListCombinatorSpec := {
              nilExpr? := some (mkAppNode ``Qed.View.validListIn_renderEach_nil #[sigmaTy, msgTy, ctxE, sExpr]),
              consLem := ``Qed.View.validListIn_renderEach_cons, mapLem? := some ``Qed.View.validListIn_renderEach_map_intro,
              prefixArgs := #[sigmaTy, msgTy, ctxE], postArgs := #[sExpr] }
            if let some pf ← proveListCombinator? listSpec cs (proveNode fuel env kind ctxV ctxE msgTy) (proveNodeList fuel env kind ctxV ctxE msgTy) then return pf
            if cs.isAppOfArity ``View.mapScopeEach 5 then
              return mkAppNode ``Qed.View.validListIn_renderEach_mapScopeEach_intro #[sigmaTy, a[1]!, msgTy, ctxE, a[3]!, a[4]!, sExpr, ← proveNodeList fuel env (.view a[1]! (mkApp a[3]! sExpr)) ctxV ctxE msgTy a[4]!]
            if let some fn := fn? then if ← isMatcherOrCases fn then return ← proveSplitSubgoal fuel env goalTy
            proveNodeList fuel env .html ctxV ctxE msgTy (mkApp4 (mkConst ``View.renderEach) sigmaTy msgTy cs sExpr)

  @[noinline] private partial def proveGoalMVar (fuel : Nat) (env : Environment) (g : MVarId) : ProveValidM Unit := do
    if ← g.isAssigned then return
    match fuel with
    | 0 => modify (·.push g)
    | fuel + 1 =>
        let (_, g') ← g.intros
        g'.withContext do
          let some (_, lhsRaw, rhs) := (← instantiateMVars (← g'.getType)).consumeMData.headBeta.eq? | modify (·.push g'); return
          if !rhs.consumeMData.isConstOf ``Bool.true then modify (·.push g'); return
          let lhs := lhsRaw.consumeMData.headBeta
          let pf? : Option Expr ←
            if lhs.isAppOfArity ``Html.valid 2 then some <$> proveNode fuel env .html defaultHtmlCtx defaultHtmlCtxExpr lhs.getAppArgs[0]! lhs.getAppArgs[1]!
            else if lhs.isAppOfArity ``Html.validIn 3 || lhs.isAppOfArity ``Html.validListIn 3 then
              let a := lhs.getAppArgs
              match ← htmlCtxVal? a[1]! with
              | some ctxV => some <$> (if lhs.isAppOfArity ``Html.validIn 3 then proveNode else proveNodeList) fuel env .html ctxV a[1]! a[0]! a[2]!
              | none => pure none
            else pure none
          match pf? with | some pf => g'.assign pf | none => modify (·.push g')
end

private def styleRawTextMsg : String := "unescaped dynamic text inside `<style>` (use a `style`/`theme` block or wrap with `escapeRawText`)"

private def diagnoseHtmlStepFailure (ctx : HtmlCtx) (tag : String) : Option String :=
  let childErr (c e : String) := some s!"`<{tag}>` cannot be a direct child of {c} (expected {e})"
  if isForbiddenTag tag then some s!"`<{tag}>` is forbidden in Qed views (untrusted script/plugin sink)"
  else if !isSafeTagName tag then some s!"invalid HTML tag name `<{tag}>`"
  else match ctx.mode with
    | .ulOl => childErr "`<ul>` or `<ol>`" "`<li>`" | .dl => childErr "`<dl>`" "`<dt>` or `<dd>`"
    | .table => childErr "`<table>`" "`<thead>`, `<tbody>`, `<tfoot>`, `<caption>`, or `<colgroup>`"
    | .colgroup => childErr "`<colgroup>`" "`<col>`" | .tableSection => childErr "`<thead>`/`<tbody>`/`<tfoot>`" "`<tr>`"
    | .tableRow => childErr "`<tr>`" "`<td>` or `<th>`" | .select => childErr "`<select>`" "`<option>` or `<optgroup>`" | .optgroup => childErr "`<optgroup>`" "`<option>`"
    | .option | .textarea | .rawStyle => some s!"`<{tag}>` cannot be nested inside a text-only element (`<option>`, `<textarea>`, or `<style>`)"
    | .normal =>
        if isContextOnlyTag tag then some s!"`<{tag}>` must be placed inside its required parent container (e.g. `<li>` in `<ul>`/`<ol>`, `<tr>` in `<tbody>`, `<td>`/`<th>` in `<tr>`, `<option>` in `<select>`)"
        else if ctx.inP && closesPTag tag then some s!"`<{tag}>` cannot be nested inside `<p>` or a heading (`<h1>-<h6>`)"
        else if ctx.interactive && (isInteractiveTag tag || tag == "label" || tag == "form") then some s!"`<{tag}>` cannot be nested inside an interactive element (`<a>`, `<button>`, `<details>`, `<summary>`, `<textarea>`, or `<select>`)"
        else if ctx.inForm && tag == "form" then some "`<form>` cannot be nested inside another `<form>`" else none
    | .svg => none

@[noinline] private def diagnoseValidGoal (g : MVarId) : MetaM (Option String) := g.withContext do
  let some (_, lhsRaw, rhs) := (← instantiateMVars (← g.getType)).consumeMData.headBeta.eq? | return none
  unless rhs.consumeMData.isConstOf ``Bool.true do return none
  let lhs := lhsRaw.consumeMData.headBeta
  if lhs.isAppOfArity ``Html.validIn 3 then
    if let some ctxV ← htmlCtxVal? lhs.getAppArgs[1]! then
      let node := lhs.getAppArgs[2]!.consumeMData.headBeta
      if node.isAppOfArity ``Html.element 4 || node.isAppOfArity ``Qed.el 4 then
        if let some reason := (strLitVal? node.getAppArgs[1]!).bind (diagnoseHtmlStepFailure ctxV) then return some reason
      else if node.isAppOfArity ``Html.text 2 || node.isAppOfArity ``Qed.text 4 then
        let rawErr (c : String) (w : String := "") := some s!"raw text cannot appear directly inside {c}{w}"
        if let some msg := match ctxV.mode with
            | .rawStyle => some styleRawTextMsg | .ulOl => rawErr "`<ul>`/`<ol>`" " (wrap it in `<li>`)" | .dl => rawErr "`<dl>`" " (wrap it in `<dt>` or `<dd>`)"
            | .table | .tableSection => rawErr "`<table>`/`<tbody>`" " (wrap it in `<tr>`/`<td>`)" | .tableRow => rawErr "`<tr>`" " (wrap it in `<td>` or `<th>`)"
            | .select | .optgroup => rawErr "`<select>`" " (wrap it in `<option>`)" | .colgroup => rawErr "`<colgroup>`" | _ => none then return some msg
  let attrKey? := if lhs.isAppOfArity ``Attr.validKeyValue 2 then some lhs.getAppArgs[0]!
    else if lhs.isAppOfArity ``Attr.valid 2 then let a := lhs.getAppArgs[1]!.consumeMData.headBeta; if a.isAppOfArity ``Attr.attr 3 then some a.getAppArgs[1]! else none else none
  if let some k := attrKey?.bind strLitVal? then
    let kl := k.toLower
    if kl == "srcdoc" || kl.startsWith "on" then return some s!"forbidden attribute `{k}` (inline event handlers and `srcdoc` are disallowed)"
    if Qed.isUrlAttrName k then return some s!"URL attribute `{k}` must use a typed `Router` route or `Url` (raw dynamic strings are disallowed)"
  if lhs.isAppOfArity ``Bool.or 2 then
    let o0 := lhs.getAppArgs[0]!.consumeMData.headBeta
    if o0.isAppOfArity ``Bool.not 1 then
      let inner := o0.getAppArgs[0]!.consumeMData.headBeta
      if inner.isAppOfArity ``Qed.isVoidTag 1 then if let some tagS := strLitVal? inner.getAppArgs[0]! then return some s!"`<{tagS}>` is an HTML5 void element and cannot have children; write it self-closing (`<{tagS} .../>`)"
      if inner.isAppOfArity ``Attr.hasLocalCell 2 then return some "a mounted local component cannot have extra children directly on its mount element"
  if lhs.getUsedConstants.contains ``Qed.containsCloseSeq then return some styleRawTextMsg
  if lhs.getUsedConstants.contains ``Qed.Url.isSafe then return some "dynamic URL attribute must use a typed `Router` route or `Url` (raw strings are disallowed)"
  return none

@[noinline] private def runProveValidHtml : TacticM Unit := do
  setGoals (← (← getGoals).mapM fun g => return (← g.intros).2)
  let env ← getEnv
  let residuals ← (← getGoals).foldlM (init := #[]) fun acc g => return acc ++ (← (proveGoalMVar 2048 env g).run #[]).2
  let preDiags ← residuals.toList.mapM fun r => return (r, ← diagnoseValidGoal r)
  setGoals residuals.toList
  if !(← getGoals).isEmpty then
    let fwCtx ← mkSimpCtxWithBase (viewFrameworkUnfolds env) (cacheKey? := some "validHtmlFw"); let sp := #[← Simp.getSimprocs]
    runGoalsFixpoint 4 do
      qedUnfoldHelpers 8 true; if (← getGoals).isEmpty then return
      simpAllGoalsWith fwCtx sp; if (← getGoals).isEmpty then return
      setGoals <| (← ((← getGoals).mapM (fun g => do match ← trySplitTarget g with | some sgs => sgs.filterMapM (simpGoalOnly · fwCtx sp) | none => pure [g]) : MetaM _)).flatten
    if !(← getGoals).isEmpty then
      let baseCtx ← mkSimpCtxWithBase
      let closeOne (g : MVarId) : MetaM (List MVarId) := do
        if ← tryReflGoal g then return []
        if ← tryDirectDecide g then return []
        match ← trySplitTarget g with | some sgs => sgs.filterMapM (simpGoalOnly · baseCtx sp) | none => return [g]
      setGoals (← ((← getGoals).mapM closeOne : MetaM _)).flatten
  if (← getUnsolvedGoals).isEmpty then return
  let specific ← preDiags.foldlM (init := #[]) fun acc (origG, diag?) => do
    if (← instantiateMVars (mkMVar origG)).hasExprMVar then if let some d := diag? then if !acc.contains d then return acc.push d
    return acc
  if !specific.isEmpty then throwError m!"Invalid HTML / XSS check failed for this view:\n{String.intercalate "\n" (specific.toList.map (s!"  • {·}"))}"
  Qed.Diag.throwUnsolvedGoals m!"Invalid HTML / XSS check failed for this view:"
    m!"\n\nCommon causes:\n    • Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<a>`/`<button>`, non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)\n    • Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount\n    • Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute\n    • Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`\n    • Unescaped dynamic text inside `<style>` (use a `style`/`theme` block or wrap with `escapeRawText`)"
    (formatGoal? := some fun g => do match ← diagnoseValidGoal g with | some d => return some s!"  • {d}" | none => g.withContext do return some s!"  • unsolved validity obligation: {← Qed.Diag.ppQedExpr (← g.getType) ["m"]}")

private def dehydrateProjLemmas (env0 : Environment) : Array Name :=
  (appProjSimpNames env0 #["template", "dehydrate", "rehydrate"] |>.filter fun n => n != `Qed.Internal.App.withDehydrate_dehydrate && n != `Qed.Internal.App.withDehydrate_rehydrate) ++ #[
    `Qed.Internal.App.withFullDehydrate, `Qed.Internal.App.withDehydrate_rehydrate_dehydrate, `Qed.App.guardRehydrate_template, `Qed.App.guardRehydrate_dehydrate,
    `Qed.Dehydrate.full_project, `Qed.Dehydrate.slice_project, `Qed.Dehydrate.const_project, `Qed.InvTarget.proj_id, `Qed.InvTarget.proj_fst].filter env0.contains

private def closeGoalsByRfl : TacticM Unit := do setGoals <| ← (← getGoals).filterM fun g => return !(← tryReflGoal g)

private def tryFastFullDehydrateInv (tgt : Expr) : MetaM (Option Expr) := do
  let .forallE _ _ (.forallE _ _ (.forallE _ invDom (.forallE _ eqDom _ _) _) _) _ := tgt | return none
  if invDom.hasLooseBVar 0 then return none
  let some (_, lhsRaw, _) := eqDom.consumeMData.eq? | return none
  let lhs := lhsRaw.consumeMData; if !lhs.isAppOfArity `Qed.App.rehydrate 4 then return none
  let lArgs := lhs.getAppArgs; let (modelTy, msgTy, appE) := (lArgs[0]!, lArgs[1]!, lArgs[2]!)
  let rec unwrapApp : Nat → Expr → Option Expr
    | 0, _ => none
    | n + 1, e =>
        let e := e.consumeMData
        if e.isAppOfArity `Qed.Internal.App.withFullDehydrate 4 then some e
        else if let some fn := e.getAppFn.constName? then let a := e.getAppArgs; if appPassThroughWrappers.contains fn && a.size ≥ 4 then unwrapApp n a[a.size - 1]! else none else none
  let some wfd := unwrapApp 8 appE | return none
  let rt := mkApp2 (mkConst `Qed.Dehydrate.round_trip) modelTy (mkApp2 (mkConst `Qed.Dehydrate.full) modelTy wfd.getAppArgs[2]!)
  let invLam := Expr.lam `_m modelTy (invDom.lowerLooseBVars 1 1) .default
  let hprojLam := Expr.lam `_m modelTy (Expr.lam `_h (mkApp invLam (Expr.bvar 0)) (Expr.bvar 0) .default) .default
  let pf := mkAppNode `Qed.Internal.App.dehydrate_preserves_of_project #[modelTy, msgTy, invLam, appE, mkApp (mkConst ``id [Level.one]) modelTy, rt, hprojLam]
  return if ← Meta.isDefEq (← Meta.inferType pf) tgt then some pf else none

@[noinline] private def splitAllRec : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do match ← trySplitTarget g with | some sub => splitAllRec fuel (sub ++ rest) | none => return g :: (← splitAllRec fuel rest)

@[noinline] private def closeDehydrateInvGoal (baseCtx : Simp.Context) (sp : Simp.SimprocsArray) (sg : MVarId) : MetaM (Option MVarId) := do
  if ← sg.assumptionCore then return none
  if ← tryCloseBasic sg then return none
  tryRestoreM (some sg) Option.isNone do
    match ← trySimpAll sg baseCtx sp with
    | none => return none
    | some sg' => if ← sg'.assumptionCore then return none else if ← tryCloseBasic sg' then return none else return some sg

@[noinline] def runProveDehydrate (isInv : Bool) : TacticM Unit := do
  let env0 ← getEnv; let pNames := dehydrateProjLemmas env0
  if isInv && env0.contains `Qed.Internal.App.dehydrate_preserves_of_project && env0.contains `Qed.Dehydrate.full then
    if ← tryRestoreM false id <| withMainContext do
        let g ← getMainGoal
        let some pf ← tryFastFullDehydrateInv (← instantiateMVars (← g.getType)) | return false
        g.assign pf; setGoals []; return true
    then return
  let g0 :: rest ← getGoals | return
  let simpNames ← if !isInv then
      let (_, g1) ← g0.intro `_qed_m; setGoals (g1 :: rest); closeGoalsByRfl
      if (← getGoals).isEmpty then return
      let vNames := pNames ++ viewCoreUnfolds.filter env0.contains
      simpAllGoalsWith (← mkCachedSimpCtx "dehydrateViewProj" vNames).1; closeGoalsByRfl; pure vNames
    else
      let (fvs, g1) ← g0.introN 4 [`_qed_m, `_qed_m', `_qed_hinv, `_qed_hre]
      match (← Meta.simpGoal g1 (← mkCachedSimpCtx "dehydrateInvProj" pNames).1 #[] none false #[fvs[3]!]).1 with
      | none => setGoals rest; return
      | some (newFvs, g2) =>
          let gs ← try pure ((← g2.cases (newFvs.getD 0 fvs[3]!)).toList.map (·.mvarId)) catch _ => pure [g2]
          setGoals ((← gs.filterM fun sg => return !(← sg.assumptionCore)) ++ rest); pure pNames
  if !(← getGoals).isEmpty then qedUnfoldHelpers 6 false (← namesToSimpLemmas simpNames) isInv true
  if !(← getGoals).isEmpty then
    let sp := #[← Simp.getSimprocs]
    if !isInv then
      simpAllGoalsWith (← mkSimpCtxWithBase simpNames (cacheKey? := some "dehydrateViewFull")) sp; closeGoalsByRfl
    else
      let baseCtx ← mkSimpCtxWithBase
      setGoals (← ((← splitAllRec 16 (← getGoals)).filterMapM (closeDehydrateInvGoal baseCtx sp) : MetaM _))
      if !(← getGoals).isEmpty && env0.contains `Qed.Lang.QedVal.val_id then simpAllGoalsWith (← mkCachedSimpCtx "valIdOnly" #[``Qed.Lang.QedVal.val_id]).1
  let (hdr, hint, bullet) := if !isInv then
    (m!"SSR hydration mismatch: `ephemeral` field affects the rendered view:", m!"\n\nHint: Do not mark fields read by `view:` as `ephemeral` (rehydration resets them to their initial value).", "  • view mismatch after rehydration:  ")
  else
    (m!"SSR rehydration can violate the component's state invariant:", m!"\n\nHint: Rehydration resets `ephemeral` fields to their initial value. Remove `ephemeral` from fields constrained by an `invariant`, or weaken the invariant.", "  • after rehydration must satisfy:  ")
  Qed.Diag.throwUnsolvedGoals hdr hint (stripPrefixes := ["_qed_m", "m"]) (bulletPrefix := bullet)

@[simp] theorem ite_bool_eq_true (c : Prop) [Decidable c] {α : Sort _} (a b : α) : (if (if c then true else false) = true then a else b) = (if c then a else b) := by by_cases hc : c <;> simp [hc]

private def viewEquivCoreNames : Array Name :=
  (viewCoreUnfolds.filter fun n => n != ``V.render_forEach && n != ``View.isDyn) ++ #[``View.render_mapScope, ``View.renderEach_mapScopeEach, ``List.map_cons, ``List.map_nil]

private def viewEquivBaseNames : Array Name :=
  viewEquivCoreNames ++ #[
    ``V.canonical_render_forEach, ``SoundMemo.ofLawful, ``SoundMemo.eval, ``Html.ofOption, ``Html.canonical, ``Html.canonicalList, ``Html.canonicalList_map,
    ``Attr.isSignalBind, ``Attr.isSignalBind_ite, ``Attr.canonical_ite, ``List.map_map, ``List.filterMap_cons, ``List.filterMap_nil, ``List.all_cons, ``List.all_nil,
    ``List.isEmpty_cons, ``List.isEmpty_nil, ``Function.comp_def, ``Array.toList_map, ``id_eq, ``Bool.false_eq_true, ``Option.map_some, ``Option.map_none,
    ``mkCanonicalElem, ``onlySignalBind, ``Attr.canonical, `Qed.toString_field, ``toString_string] ++ boolConstSimpNames

@[noinline] private def runProveViewEquiv (appId viewId : Ident) : TacticM Unit := do
  let appName ← realizeGlobalConstNoOverloadWithInfo appId; let viewName ← realizeGlobalConstNoOverloadWithInfo viewId
  let env0 ← getEnv
  let stage1 := #[appName, viewName] ++ (#[`Qed.App.view, `Qed.Internal.App.withFullDehydrate, `Qed.App.guardRehydrate_template].filter env0.contains) ++ appProjSimpNames env0 #["template"]
  simpAllGoalsWith (← mkDynamicSimpCtx stage1); if (← getGoals).isEmpty then return
  simpAllGoalsWith (← mkCachedSimpCtx "viewEquivCore" viewEquivCoreNames).1; closeGoalsByRfl; if (← getGoals).isEmpty then return
  let used ← match ← getGoals with | g :: _ => collectGoalConsts g false | [] => pure {}
  simpAllGoalsWith (← mkDynamicSimpCtx ((viewEquivHelperNames env0).filter used.contains) (some ("viewEquivBase", viewEquivBaseNames)))
  closeGoalsByRfl; if (← getGoals).isEmpty then return
  let fwCtx0 ← mkSimpCtxWithBase (viewEquivBaseNames ++ viewEquivHelperNames env0) (cacheKey? := some "viewEquivFull")
  let fwCtx ← Simp.mkContext fwCtx0.config (fwCtx0.simpTheorems.map (·.eraseCore (.decl ``Qed.V.render_forEach))) fwCtx0.congrTheorems
  let sp := #[← Simp.getSimprocs]
  simpAllGoalsWith fwCtx sp; runGoalsFixpoint 5 do qedUnfoldHelpers 8 true; simpAllGoalsWith fwCtx sp
  if !(← getGoals).isEmpty then
    let canonCtx ← mkSimpCtxWithBase #[``Qed.mkCanonicalElem, ``Qed.onlySignalBind, ``Qed.Attr.canonical] (cacheKey? := some "viewEquivCanon")
    let gs ← (← getGoals).filterM fun g => return !(← tryReflGoal g)
    setGoals <| ← ((← splitAllRec 16 gs).filterMapM (trySimpAll · canonCtx sp) : MetaM _)

elab "qedProveValidHtml" : tactic => runProveValidHtml
elab "qedProveDehydrateView" : tactic => runProveDehydrate false
elab "qedProveDehydrateInv" : tactic => runProveDehydrate true
elab "qedProveViewEquiv" appId:ident viewId:ident : tactic => runProveViewEquiv appId viewId

end Qed
