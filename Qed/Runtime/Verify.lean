import Qed.Runtime.ValidLemmas
import Qed.Verify.Core

namespace Qed

open Lean Meta Elab Tactic Qed.Verify.Core

private def strLitVal? (e : Expr) : Option String :=
  match e.consumeMData with | .lit (.strVal s) => some s | _ => none

private def boolVal? (e : Expr) : MetaM (Option Bool) := do
  let r ← whnf e
  return if r.isConstOf ``Bool.true then some true else if r.isConstOf ``Bool.false then some false else none

private def tagModeTable : Array (Name × TagMode) := #[
  (``TagMode.normal, .normal), (``TagMode.ulOl, .ulOl), (``TagMode.dl, .dl),
  (``TagMode.table, .table), (``TagMode.colgroup, .colgroup), (``TagMode.tableSection, .tableSection),
  (``TagMode.tableRow, .tableRow), (``TagMode.select, .select), (``TagMode.optgroup, .optgroup),
  (``TagMode.option, .option), (``TagMode.rawStyle, .rawStyle), (``TagMode.textarea, .textarea),
  (``TagMode.svg, .svg)]

private def htmlCtxVal? (e : Expr) : MetaM (Option HtmlCtx) := do
  if e.hasFVar || e.hasMVar then return none
  let r ← whnf e
  if !r.isAppOfArity ``HtmlCtx.mk 4 then return none
  let args := r.getAppArgs
  let modeR ← whnf args[0]!
  let some (_, mode) := tagModeTable.find? fun (n, _) => modeR.isConstOf n | return none
  let some inP    ← boolVal? args[1]! | return none
  let some inter  ← boolVal? args[2]! | return none
  let some inForm ← boolVal? args[3]! | return none
  return some { mode, inP, interactive := inter, inForm }

private def htmlCtxExpr (c : HtmlCtx) : Expr :=
  let modeNm := (tagModeTable.find? fun (_, m) => m == c.mode).map Prod.fst |>.getD ``TagMode.normal
  mkApp4 (mkConst ``HtmlCtx.mk) (mkConst modeNm) (toExpr c.inP) (toExpr c.interactive) (toExpr c.inForm)

dsimproc [simp] reduceStepHtmlCtx (stepHtmlCtx _ _) := fun e => do
  let args := e.getAppArgs
  if args.size != 2 then return .continue
  let some tag := strLitVal? args[1]! | return .continue
  let some ctx ← htmlCtxVal? args[0]! | return .continue
  match Qed.stepHtmlCtx ctx tag with
  | some next => return .done (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) (htmlCtxExpr next))
  | none      => return .done (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``HtmlCtx))

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
      | .str _ s => ["formView", "keyOf", "update", "updateKeyed", "regs", "reg", "init", "subscriptions"].contains s
      | _ => false) then return false
  if (← getProjectionFnInfo? n).isSome then return false
  match env.find? n with
  | some (.defnInfo d) =>
      if d.type.isAppOfArity ``Qed.TypedToken 1 || d.type.isConstOf ``Qed.Theme ||
         d.type.isConstOf ``Qed.Keyframes || d.type.isConstOf ``Qed.Url ||
         d.type.isAppOfArity `Qed.Codec 1 || d.type.isConstOf `Qed.LocalDef ||
         d.type.isAppOfArity `Qed.App 2 || d.type.isAppOfArity `Qed.Dehydrate 1 then return false
      return !viewOnly || d.type.getForallBody.getUsedConstants.any fun c =>
        c == ``Qed.Html || c == ``Qed.View || c == ``Qed.Attr || c == ``Qed.VAttr || c == `Qed.Component
  | _ => return false

def qedHtmlHelperNames : Array Name := #[
  ``Qed.text, ``Qed.lazy, ``Qed.el, ``Qed.link, ``Qed.linkTo,
  ``Qed.cls, ``Qed.attr, ``Qed.role, ``Qed.on, ``Qed.onValue, ``Qed.onClick, ``Qed.onInput,
  ``Qed.onChange, ``Qed.onCheck, ``Qed.onKeydown, ``Qed.onKeyup, ``Qed.onSubmit,
  ``Qed.onBlur, ``Qed.onFocus, ``Qed.onDoubleClick, ``Qed.onMouseDown, ``Qed.onMouseUp,
  ``Qed.key, ``Qed.value, ``Qed.placeholder, ``Qed.name, ``Qed.href, ``Qed.src, ``Qed.action,
  ``Qed.alt, ``Qed.title, ``Qed.style, ``Qed.inlineStyle, ``Qed.styleVars, ``Qed.type', ``Qed.disabled, ``Qed.required,
  ``Qed.checked, ``Qed.readOnly]

def qedForEachHelperNames : Array Name := #[
  `Qed.ForEachItems.toList_array, `Qed.ForEachItems.toList_list, `Qed.ForEachItems.toArray, `Qed.mapList_eq]

private def viewEquivHelperNames (env : Environment) : Array Name :=
  #[``V.bindAttr, ``V.dynAttr, ``V.onClick', ``V.onInput', ``V.onCheck'] ++ qedHtmlHelperNames ++
    (#[`Qed.Component.render, `Qed.localMount, `Qed.localMountWith] ++ qedForEachHelperNames).filter env.contains

private def viewCoreUnfolds : Array Name := #[
  ``View.render, ``View.renderEach, ``View.showIf, ``View.ofHtml,
  ``VAttr.eval, ``V.el, ``V.text, ``V.dyn, ``V.ifElse, ``V.showIf, ``V.static,
  ``V.dynNode, ``V.memo, ``V.render_forEach, ``View.isDyn]

private def viewFrameworkUnfolds (env : Environment) : Array Name :=
  #[``Html.valid, ``Html.validIn, ``Html.validListIn, ``Attr.validKeyValue,
    ``View.renderSig, ``View.renderSigList, ``View.hasOpaque, ``View.hasOpaqueList,
    ``View.collectDyn, ``View.collectDynList, ``dynValGets, ``SoundMemo.ofLawful
  ] ++ viewCoreUnfolds ++ viewEquivHelperNames env

private def qedUnfoldHelpers (maxIters : Nat) (allowView : Bool)
    (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[])
    (includeLCtx : Bool := false) (tryRfl : Bool := false) : TacticM Unit :=
  qedUnfoldHelperLoop maxIters (fun env n => isUnfoldableUserDef env allowView n)
    extraLemmas (includeLCtx := includeLCtx) (tryRfl := tryRfl)

private def simpAllGoalsWith (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) : TacticM Unit := do
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    if let some g' ← simpGoalOnly g ctx sp then rem := rem ++ [g']
  setGoals rem

private def runHtmlSimpLoop (maxIters : Nat) (ctx : Simp.Context) (sp : Simp.SimprocsArray) : TacticM Unit := do
  for _ in [0:maxIters] do
    if (← getGoals).isEmpty then return
    let before ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    qedUnfoldHelpers 8 true
    if (← getGoals).isEmpty then return
    simpAllGoalsWith ctx sp
    if (← getGoals).isEmpty then return
    let mut afterSplit : List MVarId := []
    for g in (← getGoals) do
      match ← trySplitTarget g with
      | some sgs =>
          for sg in sgs do
            if let some sg' ← simpGoalOnly sg ctx sp then afterSplit := afterSplit ++ [sg']
      | none => afterSplit := afterSplit ++ [g]
    setGoals afterSplit
    if (← getGoals).isEmpty then return
    let after ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    if before == after then break

/-! ## Direct Proof-Term Builder (`ProveValidM`) -/

private abbrev ProveValidM := StateRefT (Array MVarId) MetaM

private def rflBoolTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
private def rflBoolFalse : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)
private def mkBoolEq (lhs rhs : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs
private def mkBoolEqTrue (lhs : Expr) : Expr := mkBoolEq lhs (mkConst ``Bool.true)
private def defaultHtmlCtx : HtmlCtx := {}
private def defaultHtmlCtxExpr : Expr := htmlCtxExpr defaultHtmlCtx

private def emitValidMVar (goalTy : Expr) : ProveValidM Expr := do
  let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
  modify (·.push m.mvarId!)
  return m

private def isMatcherOrCases (fn : Name) : MetaM Bool := do
  if ← Meta.isMatcher fn then return true
  return match fn with | .str _ s => s == "casesOn" || s == "recOn" | _ => false

private def isSafeKeyLit (k : Expr) : Bool := (strLitVal? k).any Qed.isSafeAttrName

private def isSafeKeyValLit (k v : Expr) : Bool :=
  match strLitVal? k with
  | some ks => Qed.isSafeAttrName ks && (!Qed.isUrlAttrName ks || (strLitVal? v).any Qed.isSafeUrl)
  | none    => false

def stripLetE : Nat → Expr → Expr
  | 0, e => e.consumeMData.headBeta
  | fuel + 1, e =>
      match e.consumeMData.headBeta with
      | .letE _ _ val body _ => stripLetE fuel (body.instantiate1 val)
      | e => e

/-- Single attribute classifier replacing overlapping validity / local-cell / zero-cost checks. -/
private inductive AttrKind where
  | zeroCostNonCell | zeroCostCell | nonCellSafe | nonCellCheck (defValid : Bool) | unknown

private def classifyAttr (a : Expr) : AttrKind :=
  let a := stripLetE 32 a
  let args := a.getAppArgs
  match a.getAppFn.constName? with
  | some fn =>
      if fn == ``Attr.cls || fn == ``Qed.cls || fn == ``Attr.key || fn == ``Qed.key ||
         fn == ``Attr.empty || fn == ``Attr.signalBind then .zeroCostNonCell
      else if fn == ``Attr.localCell || fn == `Qed.localMount || fn == `Qed.localMountWith then .zeroCostCell
      else if fn == ``Qed.onCheck || fn == ``Qed.value || fn == ``Qed.ariaRole ||
              ValidLemmas.qedAttrWrapperMap.contains fn ||
              (fn == ``VAttr.eval && args.size == 4 &&
                (args[3]!).consumeMData.getAppFn.constName? == some ``V.onCheck') then .nonCellSafe
      else if (fn == ``Attr.flag || fn == ``Attr.on || fn == ``Attr.onValue) && args.size >= 3 then
        .nonCellCheck (isSafeKeyLit args[1]!)
      else if (fn == ``Attr.attr || fn == ``Attr.signalAttr) && args.size >= 3 then
        .nonCellCheck (isSafeKeyValLit args[args.size - 2]! args[args.size - 1]!)
      else if fn == ``Qed.attr && args.size == 5 then .nonCellCheck (isSafeKeyValLit args[3]! args[4]!)
      else if fn == ``Qed.href || fn == ``Qed.src || fn == ``Qed.action ||
              fn == ``Attr.flag || fn == ``Attr.on || fn == ``Attr.onValue ||
              fn == ``Attr.attr || fn == ``Attr.signalAttr || fn == ``Qed.attr then .nonCellCheck false
      else .unknown
  | none => .unknown

private def AttrKind.isZeroCost : AttrKind → Bool | .zeroCostNonCell | .zeroCostCell => true | _ => false
private def AttrKind.isDefValid : AttrKind → Bool
  | .zeroCostNonCell | .zeroCostCell | .nonCellSafe | .nonCellCheck true => true | _ => false
private def AttrKind.isNonCell : AttrKind → Bool
  | .zeroCostNonCell | .nonCellSafe | .nonCellCheck _ => true | _ => false

private def evalVAttrExpr (sigmaTy msgTy sExpr va : Expr) : Expr :=
  let va := va.consumeMData; let args := va.getAppArgs
  if va.isAppOfArity ``VAttr.stat 3 then args[2]!
  else if va.isAppOfArity ``VAttr.bind 3 || va.isAppOfArity ``V.bindAttr 3 then (mkApp args[2]! sExpr).headBeta
  else if va.isAppOfArity ``VAttr.dynVal 4 || va.isAppOfArity ``V.dynAttr 4 then
    mkApp3 (mkConst ``Attr.attr) args[1]! args[2]! (mkApp args[3]! sExpr)
  else if va.isAppOfArity ``VAttr.dynOn 4 then mkApp3 (mkConst ``Attr.on) args[1]! args[2]! (mkApp args[3]! sExpr)
  else if va.isAppOfArity ``V.onClick' 3 then mkApp3 (mkConst ``Attr.on) args[1]! (toExpr "click") (mkApp args[2]! sExpr)
  else if va.isAppOfArity ``V.onInput' 3 then mkApp3 (mkConst ``Attr.onValue) args[1]! (toExpr "input") (mkApp args[2]! sExpr)
  else mkApp4 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr va

private def expandVAttrMap (sigmaTy msgTy sExpr : Expr) : Nat → Expr → Expr
  | fuel, vattrs =>
      let fallback := mkAppN (mkConst ``List.map [Level.zero, Level.zero])
        #[mkApp2 (mkConst ``VAttr) sigmaTy msgTy, mkApp (mkConst ``Attr) msgTy,
          mkApp3 (mkConst ``VAttr.eval) sigmaTy msgTy sExpr, vattrs]
      match fuel with
      | 0 => fallback
      | fuel + 1 =>
          let vattrs := vattrs.consumeMData.headBeta
          if vattrs.isAppOfArity ``List.nil 1 then mkApp (mkConst ``List.nil [Level.zero]) (mkApp (mkConst ``Attr) msgTy)
          else if vattrs.isAppOfArity ``List.cons 3 then
            let args := vattrs.getAppArgs
            mkApp3 (mkConst ``List.cons [Level.zero]) (mkApp (mkConst ``Attr) msgTy)
              (evalVAttrExpr sigmaTy msgTy sExpr args[1]!) (expandVAttrMap sigmaTy msgTy sExpr fuel args[2]!)
          else fallback

private def normalizeAttrsExpr (attrs : Expr) : Expr :=
  let attrs := attrs.consumeMData.headBeta
  if attrs.isAppOfArity ``List.map 4 then
    let args := attrs.getAppArgs; let fn := args[2]!.consumeMData
    if fn.isAppOfArity ``VAttr.eval 3 then
      let fArgs := fn.getAppArgs; expandVAttrMap fArgs[0]! fArgs[1]! fArgs[2]! 128 args[3]!
    else attrs
  else attrs

private def allAttrList (p : AttrKind → Bool) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, attrs =>
      let attrs := attrs.consumeMData
      attrs.isAppOfArity ``List.nil 1 ||
      (attrs.isAppOfArity ``List.cons 3 &&
        p (classifyAttr attrs.getAppArgs[1]!) && allAttrList p fuel attrs.getAppArgs[2]!)

private def withHypLam (ty : Expr) (k : Expr → ProveValidM Expr) : ProveValidM Expr :=
  withLocalDeclD `_qed_h ty fun h => do mkLambdaFVars #[h] (← k h)

private def proveIteBranches (c : Expr) (onT onF : ProveValidM Expr) : ProveValidM (Expr × Expr) :=
  return (← withHypLam c fun _ => onT, ← withHypLam (mkApp (mkConst ``Not) c) fun _ => onF)

private def proveResBranches (α ready loading failed idle : Expr) (k : Expr → ProveValidM Expr) :
    ProveValidM (Array Expr) := do
  return #[← k idle, ← k loading, ← withHypLam α fun a => k (mkApp ready a),
           ← withHypLam (mkConst ``String) fun e => k (mkApp failed e)]

/-- Shared control-flow proof dispatcher (`ite`, `dite`, match/cases split, user-def unfold). -/
private structure CtrlFlowSpec where
  iteLem? : Option Name := none
  diteLem? : Option Name := none
  prefixArgs : Array Expr := #[]
  postBranchArgs : Array Expr := #[]
  allowSplit : Bool := true
  allowUnfold : Bool := true

private def proveCtrlFlow? (env : Environment) (spec : CtrlFlowSpec) (e : Expr)
    (proveRec : Expr → ProveValidM Expr) (onSplit : ProveValidM Expr) : ProveValidM (Option Expr) := do
  let args := e.getAppArgs
  if let some iteLem := spec.iteLem? then
    if e.isAppOfArity ``ite 5 then
      let (pfT, pfF) ← proveIteBranches args[1]! (proveRec args[3]!) (proveRec args[4]!)
      return some <| mkAppN (mkConst iteLem) (spec.prefixArgs ++ #[args[1]!, args[2]!, args[3]!, args[4]!] ++ spec.postBranchArgs ++ #[pfT, pfF])
  if let some diteLem := spec.diteLem? then
    if e.isAppOfArity ``dite 5 then
      let pfT ← withHypLam args[1]! fun fv => proveRec (mkApp args[3]! fv)
      let pfF ← withHypLam (mkApp (mkConst ``Not) args[1]!) fun fv => proveRec (mkApp args[4]! fv)
      return some <| mkAppN (mkConst diteLem) (spec.prefixArgs ++ #[args[1]!, args[2]!, args[3]!, args[4]!] ++ spec.postBranchArgs ++ #[pfT, pfF])
  if let some fn := e.getAppFn.constName? then
    if spec.allowSplit && (← isMatcherOrCases fn) then return some (← onSplit)
    if spec.allowUnfold && (← liftM (isUnfoldableUserDef env true fn)) then
      if let some eUnf ← Meta.unfoldDefinition? e then return some (← proveRec eUnf)
  return none

/-- Shared list-combinator proof dispatcher (`nil`, `cons`, `++`, `List.map`, `Array.toList ∘ Array.map`). -/
private structure ListCombinatorSpec where
  nilExpr? : Option Expr := none
  consLem : Name
  appendLem? : Option Name := none
  mapLem? : Option Name := none
  toListMapLem? : Option Name := none
  prefixArgs : Array Expr
  postArgs : Array Expr := #[]

private def proveListCombinator? (spec : ListCombinatorSpec) (xs : Expr)
    (proveElem proveRec : Expr → ProveValidM Expr) : ProveValidM (Option Expr) := do
  let args := xs.getAppArgs
  if let some nilPf := spec.nilExpr? then
    if xs.isAppOfArity ``List.nil 1 then return some nilPf
  if xs.isAppOfArity ``List.cons 3 then
    return some <| mkAppN (mkConst spec.consLem)
      (spec.prefixArgs ++ #[args[1]!, args[2]!] ++ spec.postArgs ++ #[← proveElem args[1]!, ← proveRec args[2]!])
  if let some appLem := spec.appendLem? then
    if xs.isAppOfArity ``HAppend.hAppend 6 then
      return some <| mkAppN (mkConst appLem)
        (spec.prefixArgs ++ #[args[4]!, args[5]!] ++ spec.postArgs ++ #[← proveRec args[4]!, ← proveRec args[5]!])
  if let some mapLem := spec.mapLem? then
    if xs.isAppOfArity ``List.map 4 then
      let pfF ← withHypLam args[0]! fun a => proveElem (mkApp args[2]! a)
      return some <| mkAppN (mkConst mapLem) (#[args[0]!] ++ spec.prefixArgs ++ #[args[3]!, args[2]!] ++ spec.postArgs ++ #[pfF])
  if let some tlmLem := spec.toListMapLem? then
    if xs.isAppOfArity ``Array.toList 2 then
      let inner := args[1]!.consumeMData
      if inner.isAppOfArity ``Array.map 4 then
        let m := inner.getAppArgs
        let pfF ← withHypLam m[0]! fun a => proveElem (mkApp m[2]! a)
        return some <| mkAppN (mkConst tlmLem) (#[m[0]!] ++ spec.prefixArgs ++ #[m[3]!, m[2]!] ++ spec.postArgs ++ #[pfF])
  return none

private def proveAttrValid (env : Environment) (msgTy a : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a))
  | fuel + 1 => do
      let a := a.consumeMData.headBeta
      if let .letE _ _ val body _ := a then return ← proveAttrValid env msgTy (body.instantiate1 val) fuel
      let kind := classifyAttr a
      if kind.isZeroCost then return rflBoolTrue
      if let some pf := ValidLemmas.fastAttrValidProof? msgTy a then return pf
      if kind.isDefValid then return rflBoolTrue
      let args := a.getAppArgs; let aFn? := a.getAppFn.constName?
      for (ctor, lem) in #[(``Qed.href, ``Qed.Attr.valid_href), (``Qed.src, ``Qed.Attr.valid_src), (``Qed.action, ``Qed.Attr.valid_action)] do
        if a.isAppOfArity ctor 4 then return mkApp4 (mkConst lem) args[0]! args[1]! args[2]! args[3]!
      for (ctor, lem) in #[(`Qed.Attr.localProps, `Qed.Attr.valid_localProps_intro), (`Qed.Attr.localInit, `Qed.Attr.valid_localInit_intro)] do
        if aFn? == some ctor && args.size == 5 && env.contains lem then
          return mkAppN (mkConst lem) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, ← proveAttrValid env msgTy args[3]! fuel]
      if a.isAppOfArity ``Attr.attr 3 && isSafeKeyLit args[1]! then
        let val := args[2]!.consumeMData
        if val.isAppOfArity ``Qed.ToHref.toHref 3 then
          let t := val.getAppArgs
          return mkAppN (mkConst ``Qed.ToHref.valid_attr) #[args[0]!, t[0]!, t[1]!, args[1]!, t[2]!, rflBoolTrue]
      let goalTy := mkBoolEqTrue (mkApp2 (mkConst ``Attr.valid) msgTy a)
      let cfSpec : CtrlFlowSpec := {
        iteLem? := some ``Qed.Attr.valid_ite_intro, diteLem? := some ``ValidLemmas.attr_valid_dite_intro
        prefixArgs := #[msgTy], allowSplit := false }
      if let some pf ← proveCtrlFlow? env cfSpec a (fun x => proveAttrValid env msgTy x fuel) (emitValidMVar goalTy) then return pf
      emitValidMVar goalTy

private def proveAttrValidList (env : Environment) (msgTy attrs : Expr) : Nat → ProveValidM Expr
  | 0 => emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))
  | fuel + 1 => do
      let attrs := normalizeAttrsExpr attrs
      if attrs.isAppOfArity ``List.nil 1 || allAttrList AttrKind.isZeroCost 128 attrs then return rflBoolTrue
      let spec : ListCombinatorSpec := {
        consLem := ``Qed.Attr.validList_cons_intro, appendLem? := some ``Qed.Attr.validList_append_intro, prefixArgs := #[msgTy] }
      if let some pf ← proveListCombinator? spec attrs (proveAttrValid env msgTy · fuel) (proveAttrValidList env msgTy · fuel) then return pf
      emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Attr.validList) msgTy attrs))

private def proveAttrIsLocalCellFalse (msgTy a : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let a := stripLetE 32 a
      if (classifyAttr a).isNonCell then some rflBoolFalse
      else if a.isAppOfArity ``ite 5 then
        let args := a.getAppArgs
        match proveAttrIsLocalCellFalse msgTy args[3]! fuel, proveAttrIsLocalCellFalse msgTy args[4]! fuel with
        | some pT, some pF =>
            some <| mkAppN (mkConst ``Qed.Attr.isLocalCell_ite_eq_false)
              #[msgTy, args[1]!, args[2]!, args[3]!, args[4]!, Expr.lam `_qed_h args[1]! pT .default, Expr.lam `_qed_h (mkApp (mkConst ``Not) args[1]!) pF .default]
        | _, _ => none
      else if a.isAppOfArity ``dite 5 then
        let args := a.getAppArgs
        match args[3]!.consumeMData, args[4]!.consumeMData with
        | .lam nT _ bT _, .lam nF _ bF _ =>
            if !bT.hasLooseBVars && !bF.hasLooseBVars then
              match proveAttrIsLocalCellFalse msgTy bT fuel, proveAttrIsLocalCellFalse msgTy bF fuel with
              | some pT, some pF =>
                  some <| mkAppN (mkConst ``ValidLemmas.attr_isLocalCell_dite_eq_false)
                    #[msgTy, args[1]!, args[2]!, args[3]!, args[4]!, Expr.lam nT args[1]! pT .default, Expr.lam nF (mkApp (mkConst ``Not) args[1]!) pF .default]
              | _, _ => none
            else none
        | _, _ => none
      else none

private def proveAttrHasLocalCellFalse (msgTy attrs : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let attrs := normalizeAttrsExpr attrs
      if allAttrList AttrKind.isNonCell 128 attrs || attrs.isAppOfArity ``List.nil 1 then some rflBoolFalse
      else if attrs.isAppOfArity ``List.cons 3 then
        let args := attrs.getAppArgs
        match proveAttrIsLocalCellFalse msgTy args[1]! fuel, proveAttrHasLocalCellFalse msgTy args[2]! fuel with
        | some pA, some pR => some <| mkAppN (mkConst ``Qed.Attr.hasLocalCell_cons_eq_false) #[msgTy, args[1]!, args[2]!, pA, pR]
        | _, _ => none
      else if attrs.isAppOfArity ``HAppend.hAppend 6 then
        let args := attrs.getAppArgs
        match proveAttrHasLocalCellFalse msgTy args[4]! fuel, proveAttrHasLocalCellFalse msgTy args[5]! fuel with
        | some pX, some pY => some <| mkAppN (mkConst ``Qed.Attr.hasLocalCell_append_eq_false) #[msgTy, args[4]!, args[5]!, pX, pY]
        | _, _ => none
      else none

private def proveVoidObligation (elemTy tagE kids : Expr) (tagS : String) : ProveValidM Expr := do
  let isEmptyE := mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids
  if !Qed.isVoidTag tagS then
    return match ValidLemmas.nonVoidTagMap[tagS]? with
      | some lem => mkApp3 (mkConst ``ValidLemmas.not_isVoidTag_or) tagE isEmptyE (mkConst lem)
      | none     => rflBoolTrue
  let notVoid := mkApp (mkConst ``Bool.not) (mkApp (mkConst ``Qed.isVoidTag) tagE)
  if kids.consumeMData.isAppOfArity ``List.nil 1 then return mkApp (mkConst ``Bool.or_true) notVoid
  emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Bool.or) notVoid isEmptyE))

private def proveCellObligation (elemTy msgTy evalAttrs kids : Expr) : ProveValidM Expr := do
  if allAttrList AttrKind.isNonCell 128 evalAttrs then return rflBoolTrue
  let hasCellE := mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs
  let notCellE := mkApp (mkConst ``Bool.not) hasCellE
  if kids.consumeMData.isAppOfArity ``List.nil 1 then return mkApp (mkConst ``Bool.or_true) notCellE
  let isEmptyE := mkApp2 (mkConst ``List.isEmpty [Level.zero]) elemTy kids
  if let some pFalse := proveAttrHasLocalCellFalse msgTy evalAttrs 128 then
    return mkApp3 (mkConst ``Qed.Bool.not_false_or) hasCellE isEmptyE pFalse
  emitValidMVar (mkBoolEqTrue (mkApp2 (mkConst ``Bool.or) notCellE isEmptyE))

private def proveTextValidIn (ctxV : HtmlCtx) (str goalTy : Expr) : ProveValidM Expr := do
  match ctxV.mode with
  | .normal | .option | .textarea | .svg => return rflBoolTrue
  | .rawStyle =>
      if strLitVal? str == some "" then return rflBoolTrue
      if str.consumeMData.isAppOfArity ``Qed.escapeRawText 1 then
        return mkApp4 (mkConst ``Qed.validTextIn_rawStyle_escape)
          (toExpr ctxV.inP) (toExpr ctxV.interactive) (toExpr ctxV.inForm) str.consumeMData.appArg!
      if (strLitVal? str).any fun s => !Qed.containsCloseSeq s.toList then return rflBoolTrue
      emitValidMVar goalTy
  | _ => if strLitVal? str == some "" then return rflBoolTrue else emitValidMVar goalTy

private def tryFormViewValidIn (env : Environment) (ctxV : HtmlCtx) (fn : Name) (args : Array Expr) :
    ProveValidM (Option Expr) := do
  if fn.toString.endsWith ".formView" && args.size >= 4 && ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
    let lem := fn.getPrefix ++ `formView_validIn
    if env.contains lem then
      let k := args.size - 3
      let pf := mkAppN (mkConst lem) (args.extract 0 k ++ #[toExpr ctxV.inForm] ++ args.extract k args.size)
      if ← Meta.isTypeCorrect pf then return some pf
  return none

/-- Unified target domain for `proveNode` / `proveNodeList` (`.html` vs `.view σ s`). -/
private inductive TargetKind where | html | view (sigmaTy sExpr : Expr)

private def proveElementCore (env : Environment) (kind : TargetKind) (ctxV : HtmlCtx)
    (msgTy tagE attrs kids : Expr) (tagS : String) :
    ProveValidM (Option (HtmlCtx × Expr × Expr × Expr × Expr × Expr)) := do
  let some childCtx := Qed.stepHtmlCtx ctxV tagS | return none
  let childCtxE := htmlCtxExpr childCtx
  let (evalAttrs, elemTy) := match kind with
    | .html => (attrs, mkApp (mkConst ``Html) msgTy)
    | .view σ s => (expandVAttrMap σ msgTy s 128 attrs, mkApp2 (mkConst ``View) σ msgTy)
  return some (childCtx, childCtxE, ValidLemmas.proveStepHtmlCtx ctxV tagS childCtxE,
               ← proveAttrValidList env msgTy evalAttrs 128,
               ← proveVoidObligation elemTy tagE kids tagS,
               ← proveCellObligation elemTy msgTy evalAttrs kids)

private def finishForEachProof (env : Environment) (ctxV : HtmlCtx)
    (sigmaTy msgTy ctxE childCtxE tagE alpha items key child attrs sigPrefix sExpr pfChild : Expr)
    (tagS : String) : ProveValidM Expr := do
  let hstep := ValidLemmas.proveStepHtmlCtx ctxV tagS childCtxE
  let hvoid := (ValidLemmas.nonVoidTagMap[tagS]?.map mkConst).getD rflBoolFalse
  let evalAttrs := expandVAttrMap sigmaTy msgTy sExpr 128 attrs
  let hcell ←
    if allAttrList AttrKind.isNonCell 128 evalAttrs then pure rflBoolTrue
    else if let some pF := proveAttrHasLocalCellFalse msgTy evalAttrs 128 then Meta.mkAppM ``congrArg #[mkConst ``Bool.not, pF]
    else emitValidMVar (mkBoolEqTrue (mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Attr.hasLocalCell) msgTy evalAttrs)))
  let partialArgs := #[alpha, sigmaTy, msgTy, ctxE, childCtxE, tagE, items, key, child, attrs, sigPrefix, sExpr,
                       hstep, hvoid, hcell, ← proveAttrValidList env msgTy evalAttrs 128, pfChild]
  let hsigTy := (← Meta.inferType (mkAppN (mkConst ``V.validIn_render_forEach) partialArgs)).bindingDomain!
  let hsig ← if ← Meta.isDefEq hsigTy (mkBoolEqTrue (mkConst ``Bool.true)) then pure rflBoolTrue else emitValidMVar hsigTy
  return mkAppN (mkConst ``V.validIn_render_forEach) (partialArgs.push hsig)

mutual
  private partial def proveSplitSubgoal (fuel : Nat) (env : Environment) (goalTy : Expr) : ProveValidM Expr := do
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
        match ← try m.mvarId!.withContext do Meta.splitTarget? m.mvarId! catch _ => pure none with
        | some sgs =>
            for sg in sgs do proveGoalMVar fuel env sg
            instantiateMVars m
        | none     => modify (·.push m.mvarId!); return m

  private partial def proveNode (fuel : Nat) (env : Environment) (kind : TargetKind)
      (ctxV : HtmlCtx) (ctxE msgTy node : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue <| mkApp3 (mkConst ``Html.validIn) msgTy ctxE <| match kind with
      | .html => node | .view σ s => mkApp4 (mkConst ``View.render) σ msgTy node s
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let node := node.consumeMData.headBeta
        if let .letE _ _ val body _ := node then return ← proveNode fuel env kind ctxV ctxE msgTy (body.instantiate1 val)
        let args := node.getAppArgs; let fn? := node.getAppFn.constName?
        match kind with
        | .html =>
            if node.isAppOfArity ``Html.text 2 then return ← proveTextValidIn ctxV args[1]! goalTy
            if node.isAppOfArity ``Qed.text 4 then
              match ctxV.mode with | .normal | .option | .textarea | .svg => return rflBoolTrue | _ => pure ()
            if node.isAppOfArity ``Html.element 4 || node.isAppOfArity ``Qed.el 4 then
              if let some tagS := strLitVal? args[1]! then
                if let some (childCtx, childCtxE, hstep, hattrs, hvoid, hcell) ←
                    proveElementCore env .html ctxV msgTy args[1]! args[2]! args[3]! tagS then
                  let hkids ← proveNodeList fuel env .html childCtx childCtxE msgTy args[3]!
                  return mkAppN (mkConst ``Qed.Html.validIn_element_intro)
                    #[msgTy, ctxE, childCtxE, args[1]!, args[2]!, args[3]!, hstep, hattrs, hvoid, hcell, hkids]
              return ← emitValidMVar goalTy
            if node.isAppOfArity ``Qed.withKey 3 then
              return mkAppN (mkConst ``Qed.Html.validIn_withKey_intro) #[msgTy, ctxE, args[1]!, args[2]!, ← proveNode fuel env .html ctxV ctxE msgTy args[2]!]
            if node.isAppOfArity ``Html.map 4 then
              return mkAppN (mkConst ``Qed.Html.validIn_map_intro) #[args[0]!, args[1]!, ctxE, args[2]!, args[3]!, ← proveNode fuel env .html ctxV ctxE args[0]! args[3]!]
            if node.isAppOfArity ``Html.prefixSignals 3 then
              return mkAppN (mkConst ``Qed.Html.validIn_prefixSignals_intro) #[msgTy, ctxE, args[1]!, args[2]!, ← proveNode fuel env .html ctxV ctxE msgTy args[2]!]
            if node.isAppOfArity ``Html.ofOption 2 then
              let opt := args[1]!.consumeMData
              if opt.isAppOfArity ``Option.none 1 then return mkApp (mkConst ``Qed.validTextIn_empty) ctxE
              if opt.isAppOfArity ``Option.some 2 then return ← proveNode fuel env .html ctxV ctxE msgTy opt.getAppArgs[1]!
              return ← proveSplitSubgoal fuel env goalTy
            if node.isAppOfArity ``View.render 4 then
              return ← proveNode fuel env (.view args[0]! args[3]!) ctxV ctxE args[1]! args[2]!
            if fn? == some ``Qed.lazy && args.size == 5 then
              return ← proveNode fuel env .html ctxV ctxE msgTy (mkApp args[3]! args[4]!).headBeta
            if fn? == some ``Qed.link || fn? == some ``Qed.linkTo then
              if let some hUnf ← Meta.unfoldDefinition? node then return ← proveNode fuel env .html ctxV ctxE msgTy hUnf
            if fn? == some `Qed.Resource.awaitView && args.size == 9 && env.contains `Qed.Resource.validIn_awaitView_intro then
              let pfs ← proveResBranches args[1]! args[5]! args[6]! args[7]! args[8]! (proveNode fuel env .html ctxV ctxE msgTy)
              return mkAppN (mkConst `Qed.Resource.validIn_awaitView_intro) (#[args[0]!, args[1]!, msgTy, args[3]!, ctxE, args[4]!, args[5]!, args[6]!, args[7]!, args[8]!] ++ pfs)
            if (fn? == some `Qed.Resource.view || (fn? == some `Qed.Cached.view && env.contains `Qed.Cached.state)) &&
                args.size == 7 && env.contains `Qed.Resource.validIn_view_intro then
              let r := if fn? == some `Qed.Cached.view then mkApp2 (mkConst `Qed.Cached.state) args[0]! args[2]! else args[2]!
              let pfs ← proveResBranches args[0]! args[3]! args[4]! args[5]! args[6]! (proveNode fuel env .html ctxV ctxE msgTy)
              return mkAppN (mkConst `Qed.Resource.validIn_view_intro) (#[args[0]!, msgTy, ctxE, r, args[3]!, args[4]!, args[5]!, args[6]!] ++ pfs)
            if let some fn := fn? then
              if let some pf ← tryFormViewValidIn env ctxV fn args then return pf
            let cfSpec : CtrlFlowSpec := {
              iteLem? := some ``Qed.Html.validIn_ite_intro, diteLem? := some ``Qed.Html.validIn_dite_intro, prefixArgs := #[msgTy, ctxE] }
            if let some pf ← proveCtrlFlow? env cfSpec node (proveNode fuel env .html ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
            emitValidMVar goalTy
        | .view sigmaTy sExpr =>
            let loweredHtml? : Option Expr :=
              if node.isAppOfArity ``View.text 3 || node.isAppOfArity ``V.text 3 then some (mkApp2 (mkConst ``Html.text) msgTy args[2]!)
              else if node.isAppOfArity ``View.dyn 3 || node.isAppOfArity ``V.dyn 3 then some (mkApp2 (mkConst ``Html.text) msgTy (mkApp args[2]! sExpr))
              else if node.isAppOfArity ``View.static 3 || node.isAppOfArity ``V.static 3 then some args[2]!
              else if node.isAppOfArity ``View.dynNode 3 || node.isAppOfArity ``V.dynNode 3 || node.isAppOfArity ``View.ofHtml 3 then some (mkApp args[2]! sExpr)
              else if node.isAppOfArity ``V.memo 6 then some (mkApp args[4]! (mkApp args[5]! sExpr))
              else if node.isAppOfArity ``View.memo 3 && args[2]!.consumeMData.isAppOfArity ``SoundMemo.ofLawful 6 then
                let sm := args[2]!.consumeMData.getAppArgs; some (mkApp sm[4]! (mkApp sm[5]! sExpr))
              else none
            if let some hExpr := loweredHtml? then return ← proveNode fuel env .html ctxV ctxE msgTy hExpr
            if node.isAppOfArity ``View.element 5 || node.isAppOfArity ``V.el 5 then
              if let some tagS := strLitVal? args[2]! then
                if let some (childCtx, childCtxE, hstep, hattrs, hvoid, hcell) ←
                    proveElementCore env kind ctxV msgTy args[2]! args[3]! args[4]! tagS then
                  let hkids ← proveNodeList fuel env kind childCtx childCtxE msgTy args[4]!
                  return mkAppN (mkConst ``View.validIn_render_element_intro)
                    #[sigmaTy, msgTy, ctxE, childCtxE, args[2]!, args[3]!, args[4]!, sExpr, hstep, hattrs, hvoid, hcell, hkids]
              return ← emitValidMVar goalTy
            if node.isAppOfArity ``View.showIf 4 || node.isAppOfArity ``V.showIf 4 then
              let pfY ← withHypLam (mkBoolEqTrue (mkApp args[2]! sExpr)) fun _ => proveNode fuel env kind ctxV ctxE msgTy args[3]!
              return mkAppN (mkConst ``View.validIn_render_showIf) #[sigmaTy, msgTy, ctxE, args[2]!, args[3]!, sExpr, pfY]
            if node.isAppOfArity ``View.ifElse 5 || node.isAppOfArity ``V.ifElse 5 then
              let pfY ← withHypLam (mkBoolEqTrue (mkApp args[2]! sExpr)) fun _ => proveNode fuel env kind ctxV ctxE msgTy args[3]!
              let pfN ← withHypLam (mkBoolEq (mkApp args[2]! sExpr) (mkConst ``Bool.false)) fun _ => proveNode fuel env kind ctxV ctxE msgTy args[4]!
              return mkAppN (mkConst ``View.validIn_render_ifElse) #[sigmaTy, msgTy, ctxE, args[2]!, args[3]!, args[4]!, sExpr, pfY, pfN]
            if node.isAppOfArity ``V.forEach 9 then
              if let some tagS := strLitVal? args[3]! then
                if !Qed.isVoidTag tagS then
                  if let some childCtx := Qed.stepHtmlCtx ctxV tagS then
                    let childCtxE := htmlCtxExpr childCtx
                    let pfChild ← withHypLam args[2]! fun a => proveNode fuel env (.view args[2]! a) childCtx childCtxE msgTy args[6]!
                    return ← finishForEachProof env ctxV sigmaTy msgTy ctxE childCtxE
                      args[3]! args[2]! args[4]! args[5]! args[6]! args[7]! args[8]! sExpr pfChild tagS
            if node.isAppOfArity ``View.mapScope 5 then
              let pf ← proveNode fuel env (.view args[1]! (mkApp args[3]! sExpr)) ctxV ctxE msgTy args[4]!
              return mkAppN (mkConst ``Qed.View.validIn_render_mapScope_intro) #[sigmaTy, args[1]!, msgTy, ctxE, args[3]!, args[4]!, sExpr, pf]
            let cfSpec : CtrlFlowSpec := {
              iteLem? := some ``Qed.View.validIn_render_ite_intro, prefixArgs := #[sigmaTy, msgTy, ctxE], postBranchArgs := #[sExpr] }
            if let some pf ← proveCtrlFlow? env cfSpec node (proveNode fuel env kind ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
            emitValidMVar goalTy

  private partial def proveNodeList (fuel : Nat) (env : Environment) (kind : TargetKind)
      (ctxV : HtmlCtx) (ctxE msgTy cs : Expr) : ProveValidM Expr := do
    let goalTy := mkBoolEqTrue <| mkApp3 (mkConst ``Html.validListIn) msgTy ctxE <| match kind with
      | .html => cs | .view σ s => mkApp4 (mkConst ``View.renderEach) σ msgTy cs s
    match fuel with
    | 0 => emitValidMVar goalTy
    | fuel + 1 =>
        let cs := cs.consumeMData.headBeta
        if let .letE _ _ val body _ := cs then return ← proveNodeList fuel env kind ctxV ctxE msgTy (body.instantiate1 val)
        let args := cs.getAppArgs; let csFn? := cs.getAppFn.constName?
        if csFn? == some `Qed.ForEachItems.toList || csFn? == some ``Qed.mapList then
          if let some csUnf ← Meta.unfoldDefinition? cs then return ← proveNodeList fuel env kind ctxV ctxE msgTy csUnf
        match kind with
        | .html =>
            let listSpec : ListCombinatorSpec := {
              nilExpr? := some (mkApp2 (mkConst ``Qed.Html.validListIn_nil) msgTy ctxE)
              consLem := ``Qed.Html.validListIn_cons_intro, appendLem? := some ``Qed.Html.validListIn_append_intro
              mapLem? := some ``Qed.Html.validListIn_map_intro, toListMapLem? := some ``Qed.Html.validListIn_toList_map_intro
              prefixArgs := #[msgTy, ctxE] }
            if let some pf ← proveListCombinator? listSpec cs (proveNode fuel env .html ctxV ctxE msgTy) (proveNodeList fuel env .html ctxV ctxE msgTy) then return pf
            if cs.isAppOfArity ``Html.mapChildren 4 then
              return mkAppN (mkConst ``Qed.Html.validListIn_mapChildren_intro) #[args[0]!, args[1]!, ctxE, args[2]!, args[3]!, ← proveNodeList fuel env .html ctxV ctxE args[0]! args[3]!]
            if cs.isAppOfArity ``Html.prefixSignalsList 3 then
              return mkAppN (mkConst ``Qed.Html.validListIn_prefixSignalsList_intro) #[msgTy, ctxE, args[1]!, args[2]!, ← proveNodeList fuel env .html ctxV ctxE msgTy args[2]!]
            if cs.isAppOfArity ``View.renderEach 4 then
              return ← proveNodeList fuel env (.view args[0]! args[3]!) ctxV ctxE args[1]! args[2]!
            if csFn? == some `Qed.Codec.formFieldRow && args.size == 7 && env.contains `Qed.Codec.formFieldRow_validListIn &&
                ctxV.mode == .normal && !ctxV.inP && !ctxV.interactive then
              return mkAppN (mkConst `Qed.Codec.formFieldRow_validListIn)
                #[msgTy, toExpr ctxV.inForm, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, ← proveNode fuel env .html ctxV ctxE msgTy args[6]!]
            let cfSpec : CtrlFlowSpec := {
              iteLem? := some ``Qed.Html.validListIn_ite_intro, diteLem? := some ``ValidLemmas.validListIn_dite_intro, prefixArgs := #[msgTy, ctxE] }
            if let some pf ← proveCtrlFlow? env cfSpec cs (proveNodeList fuel env .html ctxV ctxE msgTy) (proveSplitSubgoal fuel env goalTy) then return pf
            emitValidMVar goalTy
        | .view sigmaTy sExpr =>
            let listSpec : ListCombinatorSpec := {
              nilExpr? := some (mkAppN (mkConst ``Qed.View.validListIn_renderEach_nil) #[sigmaTy, msgTy, ctxE, sExpr])
              consLem := ``Qed.View.validListIn_renderEach_cons, mapLem? := some ``Qed.View.validListIn_renderEach_map_intro
              prefixArgs := #[sigmaTy, msgTy, ctxE], postArgs := #[sExpr] }
            if let some pf ← proveListCombinator? listSpec cs (proveNode fuel env kind ctxV ctxE msgTy) (proveNodeList fuel env kind ctxV ctxE msgTy) then return pf
            if cs.isAppOfArity ``View.mapScopeEach 5 then
              let pf ← proveNodeList fuel env (.view args[1]! (mkApp args[3]! sExpr)) ctxV ctxE msgTy args[4]!
              return mkAppN (mkConst ``Qed.View.validListIn_renderEach_mapScopeEach_intro) #[sigmaTy, args[1]!, msgTy, ctxE, args[3]!, args[4]!, sExpr, pf]
            if let some fn := csFn? then
              if ← isMatcherOrCases fn then return ← proveSplitSubgoal fuel env goalTy
            proveNodeList fuel env .html ctxV ctxE msgTy (mkApp4 (mkConst ``View.renderEach) sigmaTy msgTy cs sExpr)

  private partial def proveGoalMVar (fuel : Nat) (env : Environment) (g : MVarId) : ProveValidM Unit := do
    if ← g.isAssigned then return
    match fuel with
    | 0 => modify (·.push g)
    | fuel + 1 =>
        let (_, g') ← g.intros
        g'.withContext do
          let tgt := (← instantiateMVars (← g'.getType)).consumeMData.headBeta
          let some (_, lhsRaw, rhs) := tgt.eq? | modify (·.push g'); return
          if !rhs.consumeMData.isConstOf ``Bool.true then modify (·.push g'); return
          let lhs := lhsRaw.consumeMData.headBeta
          let pf? : Option Expr ←
            if lhs.isAppOfArity ``Html.valid 2 then
              some <$> proveNode fuel env .html defaultHtmlCtx defaultHtmlCtxExpr lhs.getAppArgs[0]! lhs.getAppArgs[1]!
            else if lhs.isAppOfArity ``Html.validIn 3 then
              let a := lhs.getAppArgs
              match ← htmlCtxVal? a[1]! with | some ctxV => some <$> proveNode fuel env .html ctxV a[1]! a[0]! a[2]! | none => pure none
            else if lhs.isAppOfArity ``Html.validListIn 3 then
              let a := lhs.getAppArgs
              match ← htmlCtxVal? a[1]! with | some ctxV => some <$> proveNodeList fuel env .html ctxV a[1]! a[0]! a[2]! | none => pure none
            else pure none
          match pf? with | some pf => g'.assign pf | none => modify (·.push g')
end

/-! ## HTML Validity Diagnostics -/

private def diagnoseHtmlStepFailure (ctx : HtmlCtx) (tag : String) : Option String :=
  if isForbiddenTag tag then some s!"`<{tag}>` is forbidden in Qed views (untrusted script/plugin sink)"
  else if !isSafeTagName tag then some s!"invalid HTML tag name `<{tag}>`"
  else match ctx.mode with
    | .ulOl => some s!"`<{tag}>` cannot be a direct child of `<ul>` or `<ol>` (expected `<li>`)"
    | .dl => some s!"`<{tag}>` cannot be a direct child of `<dl>` (expected `<dt>` or `<dd>`)"
    | .table => some s!"`<{tag}>` cannot be a direct child of `<table>` (expected `<thead>`, `<tbody>`, `<tfoot>`, `<caption>`, or `<colgroup>`)"
    | .colgroup => some s!"`<{tag}>` cannot be a direct child of `<colgroup>` (expected `<col>`)"
    | .tableSection => some s!"`<{tag}>` cannot be a direct child of `<thead>`/`<tbody>`/`<tfoot>` (expected `<tr>`)"
    | .tableRow => some s!"`<{tag}>` cannot be a direct child of `<tr>` (expected `<td>` or `<th>`)"
    | .select => some s!"`<{tag}>` cannot be a direct child of `<select>` (expected `<option>` or `<optgroup>`)"
    | .optgroup => some s!"`<{tag}>` cannot be a direct child of `<optgroup>` (expected `<option>`)"
    | .option | .textarea | .rawStyle =>
        some s!"`<{tag}>` cannot be nested inside a text-only element (`<option>`, `<textarea>`, or `<style>`)"
    | .normal =>
        if isContextOnlyTag tag then
          some s!"`<{tag}>` must be placed inside its required parent container (e.g. `<li>` in `<ul>`/`<ol>`, `<tr>` in `<tbody>`, `<td>`/`<th>` in `<tr>`, `<option>` in `<select>`)"
        else if ctx.inP && closesPTag tag then
          some s!"`<{tag}>` cannot be nested inside `<p>` or a heading (`<h1>`–`<h6>`)"
        else if ctx.interactive && (isInteractiveTag tag || tag == "label" || tag == "form") then
          some s!"`<{tag}>` cannot be nested inside an interactive element (`<a>`, `<button>`, `<details>`, `<summary>`, `<textarea>`, or `<select>`)"
        else if ctx.inForm && tag == "form" then some "`<form>` cannot be nested inside another `<form>`"
        else none
    | .svg => none

private def diagnoseAttrKey (k : String) : Option String :=
  let kl := k.toLower
  if kl == "srcdoc" || kl.startsWith "on" then
    some s!"forbidden attribute `{k}` (inline event handlers and `srcdoc` are disallowed)"
  else if ["href", "src", "action", "formaction", "poster", "cite", "data"].contains kl then
    some s!"URL attribute `{k}` must use a typed `Router` route or `Url` (raw dynamic strings are disallowed)"
  else none

private def diagnoseValidGoal (g : MVarId) : MetaM (Option String) := g.withContext do
  let some (_, lhsRaw, rhs) := (← instantiateMVars (← g.getType)).consumeMData.headBeta.eq? | return none
  unless rhs.consumeMData.isConstOf ``Bool.true do return none
  let lhs := lhsRaw.consumeMData.headBeta
  if lhs.isAppOfArity ``Html.validIn 3 then
    let lArgs := lhs.getAppArgs
    let some ctxV ← htmlCtxVal? lArgs[1]! | return none
    let node := lArgs[2]!.consumeMData.headBeta
    if node.isAppOfArity ``Html.element 4 || node.isAppOfArity ``Qed.el 4 then
      if let some reason := (strLitVal? node.getAppArgs[1]!).bind (diagnoseHtmlStepFailure ctxV) then return some reason
    else if node.isAppOfArity ``Html.text 2 || node.isAppOfArity ``Qed.text 4 then
      match ctxV.mode with
      | .rawStyle => return some "unescaped dynamic text inside `<style>` (use a `style`/`theme` block or wrap with `escapeRawText`)"
      | .ulOl => return some "raw text cannot appear directly inside `<ul>`/`<ol>` (wrap it in `<li>`)"
      | .dl => return some "raw text cannot appear directly inside `<dl>` (wrap it in `<dt>` or `<dd>`)"
      | .table | .tableSection => return some "raw text cannot appear directly inside `<table>`/`<tbody>` (wrap it in `<tr>`/`<td>`)"
      | .tableRow => return some "raw text cannot appear directly inside `<tr>` (wrap it in `<td>` or `<th>`)"
      | .select | .optgroup => return some "raw text cannot appear directly inside `<select>` (wrap it in `<option>`)"
      | .colgroup => return some "raw text cannot appear directly inside `<colgroup>`"
      | _ => pure ()
  if lhs.isAppOfArity ``Attr.validKeyValue 2 then
    if let some msg := (strLitVal? lhs.getAppArgs[0]!).bind diagnoseAttrKey then return some msg
  if lhs.isAppOfArity ``Attr.valid 2 then
    let attrE := lhs.getAppArgs[1]!.consumeMData.headBeta
    if attrE.isAppOfArity ``Attr.attr 3 then
      if let some msg := (strLitVal? attrE.getAppArgs[1]!).bind diagnoseAttrKey then return some msg
  if lhs.isAppOfArity ``Bool.or 2 then
    let o0 := lhs.getAppArgs[0]!.consumeMData.headBeta
    if o0.isAppOfArity ``Bool.not 1 then
      let inner := o0.getAppArgs[0]!.consumeMData.headBeta
      if inner.isAppOfArity ``Qed.isVoidTag 1 then
        if let some tagS := strLitVal? inner.getAppArgs[0]! then
          return some s!"`<{tagS}>` is an HTML5 void element and cannot have children — write it self-closing (`<{tagS} .../>`)"
      if inner.isAppOfArity ``Attr.hasLocalCell 2 then
        return some "a mounted local component cannot have extra children directly on its mount element"
  if lhs.getUsedConstants.contains ``Qed.containsCloseSeq then
    return some "unescaped dynamic text inside `<style>` (use a `style`/`theme` block or wrap with `escapeRawText`)"
  if lhs.getUsedConstants.contains ``Qed.Url.isSafe then
    return some "dynamic URL attribute must use a typed `Router` route or `Url` (raw strings are disallowed)"
  return none

private def runValidHtmlPipeline : TacticM (Array (MVarId × Option String)) := do
  evalTactic (← `(tactic| intros))
  let env ← getEnv
  let mut residuals : Array MVarId := #[]
  for g in (← getGoals) do
    residuals := residuals ++ (← (proveGoalMVar 2048 env g).run #[]).2
  let preDiags ← residuals.mapM fun r => return (r, ← diagnoseValidGoal r)
  setGoals residuals.toList
  if !(← getGoals).isEmpty then
    let fwCtx ← mkSimpCtxWithBase (viewFrameworkUnfolds env) (cacheKey? := some "validHtmlFw")
    runHtmlSimpLoop 4 fwCtx #[← Simp.getSimprocs]
    if !(← getGoals).isEmpty then
      try evalTactic (← `(tactic| all_goals (first | rfl | decide | (split <;> simp)))) catch _ => pure ()
  return preDiags

private def runProveValidHtml : TacticM Unit := do
  let preDiags ← runValidHtmlPipeline
  if (← getUnsolvedGoals).isEmpty then return
  let mut specific : Array String := #[]
  for (origG, diag?) in preDiags do
    if (← instantiateMVars (mkMVar origG)).hasExprMVar then
      if let some d := diag? then unless specific.contains d do specific := specific.push d
  if !specific.isEmpty then
    throwError m!"Invalid HTML / XSS check failed for this view:\n{String.intercalate "\n" (specific.toList.map (s!"  • {·}"))}"
  Qed.Diag.throwUnsolvedGoals m!"Invalid HTML / XSS check failed for this view:"
    m!"\n\nCommon causes:\n\
    • Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<a>`/`<button>`, \
      non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)\n\
    • Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount\n\
    • Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute\n\
    • Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`\n\
    • Unescaped dynamic text inside `<style>` (use a `style`/`theme` block or wrap with `escapeRawText`)"
    (formatGoal? := some fun g => do
      match ← diagnoseValidGoal g with
      | some d => return some s!"  • {d}"
      | none   => g.withContext do return some s!"  • unsolved validity obligation: {← Qed.Diag.ppQedExpr (← g.getType) ["m"]}")

/-! ## Dehydrate & View Equivalence Provers -/

private def dehydrateProjLemmas (env0 : Environment) : Array Name :=
  (appProjSimpNames env0 #["template", "dehydrate", "rehydrate"] |>.filter fun n =>
    n != `Qed.Internal.App.withDehydrate_dehydrate && n != `Qed.Internal.App.withDehydrate_rehydrate) ++ #[
    `Qed.Internal.App.withFullDehydrate, `Qed.Internal.App.withDehydrate_rehydrate_dehydrate,
    `Qed.App.guardRehydrate_template, `Qed.App.guardRehydrate_dehydrate,
    `Qed.Dehydrate.full_project, `Qed.Dehydrate.slice_project, `Qed.Dehydrate.const_project,
    `Qed.InvTarget.proj_id, `Qed.InvTarget.proj_fst].filter env0.contains

private def closeGoalsByRfl : TacticM Unit := do
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    let s ← saveState; try g.refl catch _ => restoreState s; rem := rem ++ [g]
  setGoals rem

private def runProveDehydrateView : TacticM Unit := do
  evalTactic (← `(tactic| intro _qed_m))
  closeGoalsByRfl
  if (← getGoals).isEmpty then return
  let env0 ← getEnv
  let viewSimpNames := dehydrateProjLemmas env0 ++ viewCoreUnfolds.filter env0.contains
  simpAllGoalsWith (← mkCachedSimpCtx "dehydrateViewProj" viewSimpNames).1; closeGoalsByRfl
  if (← getGoals).isEmpty then return
  qedUnfoldHelpers 6 false (← namesToSimpLemmas viewSimpNames) false true
  if !(← getGoals).isEmpty then
    simpAllGoalsWith (← mkSimpCtxWithBase viewSimpNames (cacheKey? := some "dehydrateViewFull")) #[← Simp.getSimprocs]
    closeGoalsByRfl
  Qed.Diag.throwUnsolvedGoals
    m!"SSR hydration mismatch: `ephemeral` field affects the rendered view:"
    m!"\n\nHint: Do not mark fields read by `view:` as `ephemeral` (rehydration resets them to their initial value)."
    (stripPrefixes := ["_qed_m", "m"]) (bulletPrefix := "  • view mismatch after rehydration:  ")

private def tryFastFullDehydrateInv (tgt : Expr) : MetaM (Option Expr) := do
  let .forallE _ _ (.forallE _ _ (.forallE _ invDom (.forallE _ eqDom _ _) _) _) _ := tgt | return none
  if invDom.hasLooseBVar 0 then return none
  let some (_, lhsRaw, _) := eqDom.consumeMData.eq? | return none
  let lhs := lhsRaw.consumeMData
  if !lhs.isAppOfArity `Qed.App.rehydrate 4 then return none
  let lArgs := lhs.getAppArgs; let modelTy := lArgs[0]!; let msgTy := lArgs[1]!; let appE := lArgs[2]!
  let rec unwrapApp : Nat → Expr → Option Expr
    | 0, _ => none
    | n + 1, e =>
        let e := e.consumeMData
        if e.isAppOfArity `Qed.Internal.App.withFullDehydrate 4 then some e
        else match e.getAppFn.constName?, e.getAppArgs with
        | some fn, args =>
            if [`Qed.Internal.App.withQueries, `Qed.Internal.App.withSubscriptions, `Qed.Internal.App.withStylesheets,
                `Qed.Internal.App.withExtraStyles, `Qed.App.withHead, `Qed.App.withSsrStatus].contains fn && args.size ≥ 4 then
              unwrapApp n args[args.size - 1]!
            else none
        | _, _ => none
  let some wfd := unwrapApp 8 appE | return none
  let rt := mkApp2 (mkConst `Qed.Dehydrate.round_trip) modelTy (mkApp2 (mkConst `Qed.Dehydrate.full) modelTy wfd.getAppArgs[2]!)
  let invLam := Expr.lam `_m modelTy (invDom.lowerLooseBVars 1 1) .default
  let hprojLam := Expr.lam `_m modelTy (Expr.lam `_h (mkApp invLam (Expr.bvar 0)) (Expr.bvar 0) .default) .default
  let pf := mkAppN (mkConst `Qed.Internal.App.dehydrate_preserves_of_project)
    #[modelTy, msgTy, invLam, appE, mkApp (mkConst ``id [Level.one]) modelTy, rt, hprojLam]
  return if ← Meta.isDefEq (← Meta.inferType pf) tgt then some pf else none

private def runProveDehydrateInv : TacticM Unit := do
  let env0 ← getEnv
  if env0.contains `Qed.Internal.App.dehydrate_preserves_of_project && env0.contains `Qed.Dehydrate.full then
    let saved ← saveState
    if ← try withMainContext do
        let g ← getMainGoal
        match ← tryFastFullDehydrateInv (← instantiateMVars (← g.getType)) with
        | some pf => g.assign pf; setGoals []; pure true | none => pure false
      catch _ => pure false then return
    restoreState saved
  let g0 :: rest ← getGoals | return
  let (fvs, g1) ← g0.introN 4 [`_qed_m, `_qed_m', `_qed_hinv, `_qed_hre]
  let pNames := dehydrateProjLemmas env0
  let some g2 ← simpGoalOnly g1 (← mkCachedSimpCtx "dehydrateInvProj" pNames).1 #[] #[fvs[3]!] false false
    | setGoals rest; return
  setGoals (g2 :: rest)
  let hreId := mkIdent `_qed_hre; let hinvId := mkIdent `_qed_hinv
  try evalTactic (← `(tactic| cases $hreId:ident)) catch _ => pure ()
  try evalTactic (← `(tactic| exact $hinvId:ident)) catch _ => pure ()
  if (← getGoals).isEmpty then return
  qedUnfoldHelpers 6 false (← namesToSimpLemmas pNames) true true
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic|
      ((repeat' split) <;> first | exact $hinvId:ident | rfl | decide | omega | (simp_all <;> first | exact $hinvId:ident | rfl | decide | omega))))
    catch _ => pure ()
  if !(← getGoals).isEmpty && env0.contains `Qed.Lang.QedVal.val_id then
    simpAllGoalsWith (← mkCachedSimpCtx "valIdOnly" #[``Qed.Lang.QedVal.val_id]).1
  Qed.Diag.throwUnsolvedGoals
    m!"SSR rehydration can violate the component's state invariant:"
    m!"\n\nHint: Rehydration resets `ephemeral` fields to their initial value. Remove `ephemeral` from fields constrained by an `invariant`, or weaken the invariant."
    (stripPrefixes := ["_qed_m", "m"]) (bulletPrefix := "  • after rehydration must satisfy:  ")

@[simp] theorem ite_bool_eq_true (c : Prop) [Decidable c] {α : Sort _} (a b : α) :
    (if (if c then true else false) = true then a else b) = (if c then a else b) := by
  by_cases hc : c <;> simp [hc]

private def viewEquivBaseNames : Array Name := #[
  ``View.render, ``View.renderEach, ``View.render_mapScope, ``View.renderEach_mapScopeEach,
  ``View.showIf, ``View.ofHtml, ``VAttr.eval, ``V.el, ``V.text, ``V.dyn, ``V.ifElse, ``V.showIf,
  ``V.static, ``V.dynNode, ``V.memo, ``V.canonical_render_forEach, ``SoundMemo.ofLawful, ``SoundMemo.eval,
  ``Html.ofOption, ``Html.canonical, ``Html.canonicalList, ``Html.canonicalList_map,
  ``Attr.isSignalBind, ``Attr.isSignalBind_ite, ``Attr.canonical_ite,
  ``List.map_cons, ``List.map_nil, ``List.map_map, ``List.filterMap_cons, ``List.filterMap_nil,
  ``List.all_cons, ``List.all_nil, ``List.isEmpty_cons, ``List.isEmpty_nil,
  ``Function.comp_def, ``Array.toList_map, ``id_eq, ``Bool.false_eq_true,
  ``Option.map_some, ``Option.map_none, ``mkCanonicalElem, ``onlySignalBind, ``Attr.canonical
] ++ boolConstSimpNames

private def runProveViewEquiv (appId viewId : Ident) : TacticM Unit := do
  let appName ← realizeGlobalConstNoOverloadWithInfo appId
  let viewName ← realizeGlobalConstNoOverloadWithInfo viewId
  let env0 ← getEnv
  let stage1 := #[appName, viewName] ++
    (#[`Qed.App.view, `Qed.Internal.App.withFullDehydrate, `Qed.App.guardRehydrate_template].filter env0.contains) ++
    appProjSimpNames env0 #["template"]
  simpAllGoalsWith (← mkDynamicSimpCtx stage1)
  if (← getGoals).isEmpty then return
  let used ← match ← getGoals with | g :: _ => collectGoalConsts g false | [] => pure {}
  simpAllGoalsWith (← mkDynamicSimpCtx ((viewEquivHelperNames env0).filter used.contains) (some ("viewEquivBase", viewEquivBaseNames)))
  closeGoalsByRfl
  if (← getGoals).isEmpty then return
  let fwFull ← namesToSimpLemmas (viewEquivBaseNames ++ viewEquivHelperNames env0)
  try evalTactic (← `(tactic| try simp [-Qed.V.render_forEach, $[$fwFull],*])) catch _ => pure ()
  for _ in [0:5] do
    if (← getGoals).isEmpty then break
    let before ← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)
    qedUnfoldHelpers 8 true
    try evalTactic (← `(tactic| try simp [-Qed.V.render_forEach, $[$fwFull],*])) catch _ => pure ()
    if (← getGoals).isEmpty then break
    if before == (← (← getGoals).mapM fun g => g.withContext do instantiateMVars (← g.getType)) then break
  if !(← getGoals).isEmpty then
    try evalTactic (← `(tactic| all_goals first | rfl | ((repeat' split) <;> simp_all [Qed.mkCanonicalElem, Qed.onlySignalBind, Qed.Attr.canonical])))
    catch _ => pure ()

elab "qedProveValidHtml" : tactic => runProveValidHtml
elab "qedProveDehydrateView" : tactic => runProveDehydrateView
elab "qedProveDehydrateInv" : tactic => runProveDehydrateInv
elab "qedProveViewEquiv" appId:ident viewId:ident : tactic => runProveViewEquiv appId viewId

end Qed
