import Qed.Component.Rewrite
import Qed.Runtime
import Qed.Invariant.ForEach
import Qed.Server.Invariant

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

private structure PendingRpcCheck where
  callRef      : Syntax
  srvShort     : String
  methodName   : String
  reqConst?    : Option Name
  reqLabel     : String
  requiresAuth : Bool
  argExprs     : Array Expr
  lctx         : LocalContext
  localInsts   : LocalInstances
  mctx         : MetavarContext
  sessionVar?  : Option Name

private initialize pendingRpcChecks : IO.Ref (Array PendingRpcCheck) ← IO.mkRef #[]
private initialize currentCompSessionRef : IO.Ref (Option Ident) ← IO.mkRef none

/-! ## Shared Structure, Binder & Codegen Helpers -/

private def mkStructBinder (f : FieldDecl) : CommandElabM (TSyntax ``Lean.Parser.Command.structExplicitBinder) :=
  match f.ty?, f.def? with
  | some ty, some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty := $d))
  | some ty, none   => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty))
  | none,    some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) := $d))
  | none,    none   => throwErrorAt f.id s!"field `{f.id.getId}` needs a type or default value"

private def resolveBindTy (bd : FieldDecl) : CommandElabM Term := do
  match bd.ty?, bd.def? with
  | some ty, _ => pure ty
  | none, some d => `(type_of% $d)
  | none, none => throwErrorAt bd.id s!"`bind {bd.id.getId}` needs a type or default"

private def freshCompInvIdent (ref : Syntax) (compId : Name) : CommandElabM Ident := do
  let env ← getEnv; let ns ← getCurrNamespace
  let base := compId ++ `inv
  if !env.contains (ns ++ base) then return mkIdentFrom ref base
  let mut idx := 2
  while env.contains (ns ++ compId ++ Name.mkSimple s!"inv_{idx}") do idx := idx + 1
  return mkIdentFrom ref (compId ++ Name.mkSimple s!"inv_{idx}")

private def resolveInvIdent (invStx : Syntax) (compId : Name) : CommandElabM Ident :=
  match invStx[1].find? (·.isIdent) with
  | some idStx => pure (mkIdentFrom idStx (compId ++ idStx.getId))
  | none       => freshCompInvIdent invStx compId

/-! ## Pure View Component Elaboration (`CompMountKind.pureView`) -/

private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  let doc?    := spec.doc?
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  let msgV    := mkIdent `msg
  let mut pBinders ← spec.props.mapM mkStructBinder
  let mut propReadNames := spec.propNames
  for sl in spec.slots do
    propReadNames := propReadNames.push sl.id.getId
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder|
      ($(sl.id) : Html $msgV := $(← sl.def?.getDM `(Qed.Html.empty)))))
  for bd in spec.binds do
    propReadNames := propReadNames.push bd.id.getId
    let bTy ← resolveBindTy bd
    let setF := mkIdentFrom bd.id (Name.mkSimple s!"set_{bd.id.getId}")
    pBinders := pBinders.push (← mkStructBinder { bd with ty? := some bTy })
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($setF : $bTy → $msgV)))
  for ev in spec.events do
    propReadNames := propReadNames.push ev.id.getId
    let evTy ← ev.params.foldrM (init := (⟨msgV.raw⟩ : Term)) fun (_, pTy) acc => `($pTy → $acc)
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(ev.id) : $evTy)))
  if spec.hasChildren then
    propReadNames := propReadNames.push `children
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent `children) : List (Html $msgV) := [])))
  elabCommand (← `(command| structure $propsId ($msgV : Type) where $[$pBinders:structExplicitBinder]*))
  let mut viewBody := body'
  for g in propReadNames.reverse do
    if mentionsIdent viewBody.raw g then
      let gId := mkIdent g
      viewBody ← `(let $gId:ident := (p.$gId:ident); $viewBody)
  let needsProps := !pBinders.isEmpty
  let viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if needsProps then pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $propsId $msgV))]
    else pure #[← `(bracketedBinder| {$msgV : Type})]
  elabCommand (← `(command| $[$doc?:docComment]? @[inline] def $viewId $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody))
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` applies to stateful components"
    let invId ← resolveInvIdent invStx tId
    let rawClauses := invStx[2].getSepArgs
    let loweredClauses ← rawClauses.mapM (lowerCompExpr .val)
    let vPred ← match loweredClauses.toList with
      | [p] => pure p
      | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
      | [] => throwErrorAt invStx "empty view invariant"
    let predStr := String.intercalate ", " (rawClauses.toList.map fun c => (c.reprint.getD "this rule").trimmed)
    let vCall ← if needsProps then `($viewId p) else `(($viewId : Html $msgV))
    let pf? : Option Term := if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let rhs ← pf?.getDM `(by
      let _qed_hv := fun (_ : Unit) => $vCall
      suffices ∀ u, ($vPred) (_qed_hv u) = true from this ()
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

/-! ## Stateful & Effectful Component Elaboration (`CompMountKind.stateful`) -/

private def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool)
    (body : Term) : CommandElabM Term := do
  let mut out := body
  for po in spec.portOuts.reverse do
    if shouldBind po.id.getId then
      let poId := mkIdent po.id.getId
      out ← `(let $poId:ident := $(mkIdent (spec.t.getId ++ po.id.getId)); $out)
  for ev in spec.events.reverse do
    if shouldBind ev.id.getId then
      let evId := mkIdent ev.id.getId
      out ← `(let $evId:ident := $(mkIdent (spec.t.getId ++ `Out ++ ev.id.getId)); $out)
  for g in spec.allNames.reverse do
    if shouldBind g then
      let gId := mkIdent g
      out ← if spec.fieldNames.contains g then `(let $gId:ident := (s.$gId:ident); $out)
            else `(let $gId:ident := (p.$gId:ident); $out)
  return out

private def mkPropsBinders (spec : ComponentSpec) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if spec.hasProps then return #[← `(bracketedBinder| (p : $(mkIdent (spec.t.getId ++ `Props))))]
  else return #[]

private def resolveStructFieldTypes (compName structKind : Name)
    (decls : Array FieldDecl) : CommandElabM (Array FieldDecl) := do
  let ns ← getCurrNamespace; let env ← getEnv
  decls.mapM fun d => do
    let resolved ← match d.ty? with
      | some ty => pure ty
      | none =>
          let some info := env.find? (ns ++ compName ++ structKind ++ d.id.getId)
            | throwErrorAt d.id s!"could not infer type of `{d.id.getId}`; add an explicit `: Type`"
          liftTermElabM <| Meta.forallTelescope info.type fun _ cod => PrettyPrinter.delab cod
    return { d with ty := resolved }

private def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub)
    (formDrafts : Array FieldDecl) (resetForms : Array ResetFormSub) : CommandElabM ComponentSpec := do
  if spec.outTy?.isSome then
    let outId := mkIdent (spec.t.getId ++ `Out)
    let evCtors ← spec.events.mapM fun ev => do
      let pIds := ev.params.map (·.1); let pTys := ev.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $(mkIdent ev.id.getId):ident $[($pIds:ident : $pTys)]*)
    let bdCtors ← spec.binds.mapM fun bd => do
      let setC := mkIdent (Name.mkSimple s!"set_{bd.id.getId}")
      `(Lean.Parser.Command.ctor| | $setC:ident (v : $(← resolveBindTy bd)))
    elabCommand (← `(command| inductive $outId where $[$(evCtors ++ bdCtors):ctor]*))
  let allProps := spec.props ++ spec.binds
  let allStates := spec.states ++ formDrafts ++ hoisted.map fun h => {
    id := h.fieldId, ty? := some (mkIdent (h.info.fullName ++ `State)),
    def? := some (mkIdent (h.info.fullName ++ `init)) }
  let propsId := mkIdent (spec.t.getId ++ `Props)
  let stateId := mkIdent (spec.t.getId ++ `State)
  elabCommand (← `(command| structure $propsId where $[$(← allProps.mapM mkStructBinder):structExplicitBinder]*))
  elabCommand (← `(command| structure $stateId where $[$(← allStates.mapM mkStructBinder):structExplicitBinder]*))
  let resolvedProps  ← resolveStructFieldTypes spec.t.getId `Props allProps
  let resolvedStates ← resolveStructFieldTypes spec.t.getId `State allStates
  let resolvedBinds  := spec.binds.map fun bd =>
    { bd with ty := (resolvedProps.find? (·.id.getId == bd.id.getId)).map (·.ty) |>.getD bd.ty }
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted, resetForms }

private def mkCmdBatch (cmds : Array Term) : CommandElabM Term := do
  if cmds.isEmpty then `(Qed.Cmd.none)
  else if cmds.size == 1 then return cmds[0]!
  else `(Qed.Cmd.batch [$[$cmds],*])

private def mkUpdateRet (spec : ComponentSpec) (sTerm : Term) (out? : Option Term)
    (cmds : Array Term) : CommandElabM Term := do
  let oVal ← match out? with | some o => `(some $o) | none => `(none)
  match spec.outTy?.isSome, spec.hasEffects with
  | false, false => return sTerm
  | true,  false => `(($sTerm, $oVal))
  | false, true  => `(($sTerm, $(← mkCmdBatch cmds)))
  | true,  true  => `(($sTerm, $oVal, $(← mkCmdBatch cmds)))

private def unpackRetTuple (hasOut hasEffects : Bool) (v : Ident) :
    CommandElabM (Term × Option Term × Option Term) := do
  let sE ← if !hasOut && !hasEffects then `($v:ident) else `(($v:ident).1)
  let oE? ← if !hasOut then pure none
    else if hasEffects then some <$> `(($v:ident).2.1) else some <$> `(($v:ident).2)
  let cE? ← if !hasEffects then pure none
    else if hasOut then some <$> `(($v:ident).2.2) else some <$> `(($v:ident).2)
  return (sE, oE?, cE?)

private def mkHoistedPropsTerm (h : HoistedSub) : CommandElabM Term := do
  let fIds := h.dataProps.map (·.1); let fVals := h.dataProps.map (·.2)
  `(({ $[$fIds:ident := $fVals],* } : $(mkIdent (h.info.fullName ++ `Props))))

private def flushAssigns (sBase : Term) (assigns : Array (Name × Option Term)) : CommandElabM Term := do
  if assigns.isEmpty then return sBase
  let fIds := assigns.map (mkIdent ·.1)
  let vals ← assigns.mapM (·.2.getDM `(v))
  `({ $sBase with $[$fIds:ident := $vals],* })

private def flushMutated (sBase : Term) (mutated : Array Name) : CommandElabM Term := do
  if mutated.isEmpty then return sBase
  let uniq := mutated.toList.eraseDups.toArray
  let fIds := uniq.map mkIdent
  let fVals : Array Term := fIds.map (⟨·.raw⟩)
  `({ $sBase with $[$fIds:ident := $fVals:term],* })

private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (mutated : Array Name) (out? : Option Term) (cmds : Array Term)
    (stmts : List Syntax) : CommandElabM Term := do
  match stmts with
  | [] => mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
  | s :: rest =>
      let sk := s.getKind
      if sk == ``qedStmtPass then
        compileStmts spec sBase mutated out? cmds rest
      else if sk == ``qedStmtReturn then
        mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
      else if sk == ``qedStmtEnsure then
        let cond ← lowerCompExpr .propGuard s[1]
        let tT ← compileStmts spec sBase mutated out? cmds rest
        let eT ← mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
        `(if $(mkIdent `_qedIf):ident : $cond then $tT else $eT)
      else if sk == ``qedStmtLet then
        let lVal ← lowerCompExpr .val s[4]
        let cont ← compileStmts spec sBase mutated out? cmds rest
        if s[1].isIdent then
          let lId : Ident := ⟨s[1]⟩
          if s[2].getNumArgs == 2 then
            let lTy ← liftMacroM (return (← lowerQedType s[2][1] false).1)
            `(let $lId:ident : $lTy := $lVal; $cont)
          else `(let $lId:ident := $lVal; $cont)
        else `(let _ := $lVal; $cont)
      else if sk == ``qedStmtAssign then
        let op := atomStr s[1]
        if s[0].getKind == ``qedIdent then
          let fId : Ident := ⟨s[0][0]⟩
          let fname := fId.getId.eraseMacroScopes
          let valTerm ←
            if op == "=" && isCdot s[2] then `(v)
            else desugarAssign fname op (← lowerCompExpr .val s[2])
          if spec.bindNames.contains fname then
            if out?.isSome then
              throwErrorAt s s!"cannot assign `bind` field `{fname}` here: this action already emits an output event (an action emits at most one output)"
            let outCtor := mkIdent (spec.t.getId ++ `Out ++ Name.mkSimple s!"set_{fname}")
            let oTerm ← `($outCtor $valTerm)
            return ← compileStmts spec sBase mutated (some oTerm) cmds rest
          unless spec.fieldNames.contains fname do
            throwNotMutableStateField fId s!"`{fname}`" fname spec.fieldNames spec.propNames
          let cont ← compileStmts spec sBase (mutated.push fname) out? cmds rest
          let fIdent := mkIdent fname
          `(let $fIdent:ident := $valTerm; $cont)
        else if s[0].getKind == ``qedIndex && s[0][0].getKind == ``qedIdent && op == "=" then
          let fId : Ident := ⟨s[0][0][0]⟩
          let fname := fId.getId.eraseMacroScopes
          unless spec.fieldNames.contains fname do
            throwNotMutableStateField fId s!"`{fname}`" fname spec.fieldNames spec.propNames
          let idxT ← lowerCompExpr .val s[0][2]
          let rhsT ← lowerCompExpr .val s[2]
          let fIdent := mkIdent fname
          let cont ← compileStmts spec sBase (mutated.push fname) out? cmds rest
          `(let $fIdent:ident := ($fIdent).set $idxT $rhsT (by first | get_elem_tactic | (simp (config := { zetaDelta := false }) only [$fIdent:ident, Array.size_set, Array.size_push] <;> omega)); $cont)
        else
          let lhsStr := stxSnippet s[0]
          let what := if lhsStr.isEmpty then "" else s!" `{lhsStr} {op} ...`"
          throwErrorAt s s!"unsupported assignment{what} in component action; expected `field = val`, `field += val`, `field -= val`, or `arr[i] = val`"
      else if sk == ``qedStmtExpr then
        if let some (targetStx, elemStx) := matchPushCall? s[0] then
          unless targetStx.getKind == ``qedIdent do
            let tgtStr := stxSnippet targetStx
            let got := if tgtStr.isEmpty then "" else s!", got `{tgtStr}.push(...)`"
            throwErrorAt targetStx s!"array `.push(...)` in component actions requires a simple `state` field (e.g. `items.push(x)`){got}"
          let fId : Ident := ⟨targetStx[0]⟩
          let fname := fId.getId.eraseMacroScopes
          unless spec.fieldNames.contains fname do
            throwNotMutableStateField fId s!"`{fname}`" fname spec.fieldNames spec.propNames
          let elemT ← lowerCompExpr .val elemStx
          let fIdent := mkIdent fname
          let cont ← compileStmts spec sBase (mutated.push fname) out? cmds rest
          `(let $fIdent:ident := ($fIdent).push $elemT; $cont)
        else
          let sn := stxSnippet s[0]
          let what := if sn.isEmpty then "" else s!" `{sn}`"
          throwErrorAt s s!"bare expression{what} has no effect in a component action; assign a `state` field (`field = ...`), call `arr.push(...)`, `perform ...`, or `send ...`"
      else if sk == ``qedStmtSend then
        let callStx := unwrapParens1 s[1]
        let matchedSub? : Option SubDecl :=
          if callStx.getKind == ``qedCall && callStx[0].getKind == ``qedIdent then
            let cname := callStx[0][0].getId.eraseMacroScopes
            spec.subscriptions.find? (·.id.getId.eraseMacroScopes == cname)
          else none
        match matchedSub? with
        | some sub =>
            unless sub.chInfo.hasSend do
              throwErrorAt s s!"channel `{sub.chInfo.ownerShort}.{sub.chInfo.channelName}` does not declare `on_send` / `send`"
            let rawArgs := callStx[2].getSepArgs
            if rawArgs.size != sub.chInfo.sendParamCount then
              throwErrorAt callStx s!"`send {sub.id.getId}(...)` expects {sub.chInfo.sendParamCount} argument(s), got {rawArgs.size}"
            let argTerms ← rawArgs.mapM fun ra => do
              unless ra.getKind == ``qedCallArgPos do
                throwErrorAt ra s!"named arguments are not supported in `send {sub.id.getId}(...)`"
              lowerCompExpr .val ra[0]
            let chFullId := mkIdentFrom s sub.chInfo.fullName
            let slotLit := Syntax.mkStrLit sub.id.getId.toString
            let sendCmd ← withRef s `(qedCheckChanSend% $chFullId:ident [$[$argTerms:term],*] $slotLit:str)
            let cmdId := mkIdent (Name.mkSimple s!"_wsSendCmd_{cmds.size}")
            let cont ← compileStmts spec sBase mutated out? (cmds.push (cmdId : Term)) rest
            `(let $cmdId:ident := $sendCmd; $cont)
        | none =>
            unless spec.outTy?.isSome do noEmitsErr s
            if out?.isSome then throwErrorAt s "duplicate `send` in action; an action emits at most one output"
            let sendT ← lowerCompExpr .val s[1]
            compileStmts spec sBase mutated (some sendT) cmds rest
      else if sk == ``qedStmtPerform then
        let perfT ← lowerCompExpr .val s[1]
        let cmdId := mkIdent (Name.mkSimple s!"_perfCmd_{cmds.size}")
        let cont ← compileStmts spec sBase mutated out? (cmds.push (cmdId : Term)) rest
        `(let $cmdId:ident := $perfT; $cont)
      else if sk == ``qedStmtIf || sk == ``qedStmtIfLet || sk == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt s
        let sFlushed ← flushMutated sBase mutated
        let tailStmts := if passTail then rest else []
        let compileBranch (seq : Array Syntax) := compileStmts spec sFlushed #[] out? cmds (seq.toList ++ tailStmts)
        let branchTerm ←
          if sk == ``qedStmtIf then
            let cond ← lowerCompExpr .propGuard s[1]
            let tT ← compileBranch (suiteStmts s[3])
            let eT ← compileBranch ((desugarElifs s[4].getArgs s[5]).getD #[])
            `(if $(mkIdent `_qedIf):ident : $cond then $tT else $eT)
          else if sk == ``qedStmtIfLet then
            let pat ← liftMacroM (lowerQedPat s[2])
            let scrut ← lowerCompExpr .val s[4]
            let tT ← compileBranch (suiteStmts s[6])
            let eT ← compileBranch (if s[7].getNumArgs == 3 then suiteStmts s[7][2] else #[])
            `(if let $pat := $scrut then $tT else $eT)
          else
            let scruts ← s[1].getSepArgs.mapM (lowerCompExpr .val)
            let alts ← s[3].getArgs.mapM fun alt => do
              let pats ← alt[1].getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
              `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $(← compileBranch (suiteStmts alt[3])))
            `(match $[$scruts:term],* with $[$alts:matchAlt]*)
        if passTail || rest.isEmpty then return branchTerm
        let brId := mkIdent `_qedBr
        let (sNext, oNext, cOpt) ← unpackRetTuple spec.outTy?.isSome spec.hasEffects brId
        let cNext := match cOpt with | some c => #[c] | none => #[]
        let tail ← match oNext with
          | none => compileStmts spec sNext #[] none cNext rest
          | some oExpr =>
              let oVal := mkIdent `_qedOut
              `(match $oExpr:term with
                | none => $(← compileStmts spec sNext #[] none cNext rest)
                | some $oVal:ident => $(← compileStmts spec sNext #[] (some ⟨oVal.raw⟩) cNext rest))
        let mut rebound := tail
        for fn in spec.fieldNames.reverse do
          if rest.any (mentionsIdent · fn) then
            let fId := mkIdent fn
            rebound ← `(let $fId:ident := ($sNext).$fId:ident; $rebound)
        `(let $brId:ident := $branchTerm; $rebound)
      else
        let sn := stxSnippet s
        let what := if sn.isEmpty then "" else s!" `{sn}`"
        throwErrorAt s s!"unsupported statement{what} in component action"

private def mkRightTuple (unit : CommandElabM Term) (pair : Term → Term → CommandElabM Term) :
    List Term → CommandElabM Term
  | [] => unit | [t] => pure t | t :: ts => do pair t (← mkRightTuple unit pair ts)

private def mkGuardedBranches (spec : ComponentSpec) (pfx : String)
    (paramTypeConsts : Array Name) (args : Array Term)
    (whenPat? : Option (Term × Term × Array Name)) (whenGuards : Array Term)
    (elseTerm : Term) (depMatch : Bool) (leafFn : Array Ident → CommandElabM Term) :
    CommandElabM Term := do
  let qaIds : Array Ident := (Array.range args.size).map fun i => mkIdent (Name.mkSimple s!"{pfx}_{i}")
  let mut body ← (qaIds.zip (paramTypeConsts.zip args)).foldrM
    (init := ← leafFn qaIds) fun (qaId, pTy, arg) acc =>
      `(let $qaId:ident : $(mkIdent pTy) := $arg; $acc)
  if !whenGuards.isEmpty then
    let guardProp ← mkConjBody whenGuards
    body ← if depMatch then `(if $(mkIdent (Name.mkSimple s!"_h{pfx}When")):ident : $guardProp then $body else $elseTerm)
           else `(if $guardProp then $body else $elseTerm)
  let patIds := whenPat?.map (·.2.2) |>.getD #[]
  if let some (pat, scrut, _) := whenPat? then
    body ← if depMatch then `(match $(mkIdent (Name.mkSimple s!"_h{pfx}Pat")):ident : $scrut:term with | $pat:term => $body | _ => $elseTerm)
           else `(match $scrut:term with | $pat:term => $body | _ => $elseTerm)
  bindMentionedFields spec (fun g =>
    (whenPat?.any fun (_, scrut, _) => mentionsIdent scrut.raw g) ||
    (!patIds.contains g &&
      (args.any (mentionsIdent ·.raw g) || whenGuards.any (mentionsIdent ·.raw g)))) body

private def mkRpcQueryBranches (spec : ComponentSpec) (rspec : RpcQuerySpec)
    (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term := do
  mkGuardedBranches spec "_qa" rspec.mInfo.paramTypeConsts rspec.args
    rspec.whenPat? rspec.whenGuards (← `(none)) true leafFn

private def mkRpcQueryParamsBody (spec : ComponentSpec) (rspec : RpcQuerySpec) : CommandElabM Term :=
  mkRpcQueryBranches spec rspec fun qaIds => do
    `(some $(← mkRightTuple (`(())) (fun a b => `(($a, $b))) (qaIds.toList.map (⟨·.raw⟩))))

private def mkSubBranches (spec : ComponentSpec) (sub : SubDecl) (elseTerm : Term)
    (depMatch : Bool) (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term :=
  mkGuardedBranches spec "_sa" sub.chInfo.paramTypeConsts sub.args
    sub.whenPat? sub.whenGuards elseTerm depMatch leafFn

private def mkSubKeyExpr (spec : ComponentSpec) (sub : SubDecl) : CommandElabM Term := do
  let keyFnId := mkIdentFrom sub.chanRef sub.chInfo.keyHelperConst
  mkSubBranches spec sub (← `("")) false fun qaIds =>
    qaIds.foldlM (init := (keyFnId : Term)) fun acc a => `($acc $a)

private def subKeyFnName (tId : Name) (sub : SubDecl) : Name :=
  tId ++ Name.mkSimple s!"_wsKey_{sub.id.getId}"

private def mkMsgInductiveCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId   := spec.t.getId
  let msgId := mkIdent (tId ++ `Msg)
  let mut ctors ← sites.mapM fun site => do
    let cId := mkIdent site.ctor
    if !site.params.isEmpty then
      let ids := site.params.map (·.1); let ts := site.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $cId:ident $[($ids:ident : $ts)]*)
    else match site.assigns.find? (·.2.isNone) with
    | some (f, _) =>
        let some d := (spec.states ++ spec.props).find? (·.id.getId == f)
          | throwError s!"component: internal unknown field `{f}`"
        `(Lean.Parser.Command.ctor| | $cId:ident (v : $(d.ty)))
    | none => `(Lean.Parser.Command.ctor| | $cId:ident)
  if let some rd := spec.route? then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_onRoute):ident (_r : $(rd.ty))))
  if spec.sessionField?.isSome then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_onSession):ident (_u : Option String)))
  if spec.outTy?.isSome then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_emit):ident (_o : $(mkIdent (tId ++ `Out)))))
  for (colField, colChild) in spec.collections do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent colField.getId):ident (key : String) (msg : $(mkIdent (colChild.getId ++ `Msg)))))
  for q in spec.queries do
    let qCtor := mkIdent q.ctorName
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $qCtor:ident (key : String) (res : Resource $(q.msgTy))))
  for sub in spec.subscriptions do
    let joinTy : Term ← if sub.chInfo.hasJoinSnapshot then pure (mkIdent sub.chInfo.joinTypeConst : Term) else `(Unit)
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent sub.joinCtor):ident (key : String) (snap : $joinTy)))
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent sub.msgCtor):ident (key : String) (ev : $(sub.msgEvTy))))
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent sub.statusCtor):ident (key : String) (st : Qed.SocketStatus)))
  for h in spec.hoisted do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent h.ctorName):ident (msg : $(mkIdent (h.info.fullName ++ `Msg)))))
  for rf in spec.resetForms do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent rf.ctorName):ident))
  let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
    else `(command| inductive $msgId where $[$ctors:ctor]*)
  let mut outCmds : Array (TSyntax `command) := #[msgCmd]
  for po in spec.portOuts do
    let poName := mkIdent (tId ++ po.id.getId)
    let poLit := Syntax.mkStrLit po.id.getId.toString
    outCmds := outCmds.push (← `(command| def $poName (x : $(po.ty)) : Cmd $msgId :=
      Cmd.port $poLit (Json.render (ToJson.toJson x))))
  if spec.outTy?.isSome then
    outCmds := outCmds.push (← `(command|
      instance $(mkIdent (tId ++ `Out ++ `instCoeMsg)):ident : Coe $(mkIdent (tId ++ `Out)) $msgId := ⟨$(mkIdent (tId ++ `Msg ++ `_emit))⟩))
  return outCmds

private def mkOwnUpdateArms (spec : ComponentSpec) (sites : Array SetSite) (unchanged : Term) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let tId := spec.t.getId
  let mut ownArms ← sites.mapM fun site => do
    let cFull := mkIdent (tId ++ `Msg ++ site.ctor)
    let mut rhs ← (match site.stmts? with
      | some stmts => do
          let isPureNoop := stmts.all fun st =>
            ![``qedStmtAssign, ``qedStmtExpr, ``qedStmtSend, ``qedStmtPerform,
              ``qedStmtIf, ``qedStmtIfLet, ``qedStmtMatch, ``qedStmtPass, ``qedStmtEnsure].contains st.getKind
          if isPureNoop then
            throwErrorAt stmts[0]! s!"action `{site.ctor}` has no state update, effect, or `send`; add a state assignment, `perform`, `send`, or `pass`"
          compileStmts spec (← `(s)) #[] none #[] stmts.toList
      | none => do mkUpdateRet spec (← flushAssigns (← `(s)) site.assigns) site.send? #[])
    if let some guard := site.guard? then rhs ← `(if $(mkIdent `_qedWhen):ident : $guard then $rhs else $unchanged)
    if let some (pat, scrut) := site.whenPat? then
      rhs ← `(match $(mkIdent `_qedWhenPat):ident : $scrut:term with | $pat:term => $rhs | _ => $unchanged)
    rhs ← bindMentionedFields spec (fun g =>
      (site.stmts?.any (·.any (mentionsIdent · g))) ||
      (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
      (site.send?.any (mentionsIdent ·.raw g)) ||
      (site.guard?.any (mentionsIdent ·.raw g)) ||
      (site.whenPat?.any fun (_, sc) => mentionsIdent sc.raw g)) rhs
    if !site.params.isEmpty then
      let ids : Array Term := site.params.map (⟨·.1.raw⟩)
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
    else if site.assigns.any (·.2.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
    else `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
  if let some rd := spec.route? then
    let cFull := mkIdent (tId ++ `Msg ++ `_onRoute)
    let rVal := mkIdent `_r
    let sWithR ← `({ s with $(rd.field):ident := $rVal:ident })
    let mut rhs ← (if rd.alts.isEmpty then mkUpdateRet spec sWithR none #[]
      else do
        let alts ← rd.alts.mapM fun alt => do
          let pats ← alt[1].getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
          `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* =>
              $(← compileStmts spec sWithR #[] none #[] (suiteStmts alt[3]).toList))
        `(match $rVal:ident with $[$alts:matchAlt]*))
    rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
    rhs ← `(let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $rVal:ident => $rhs))
  if let some sfId := spec.sessionField? then
    let cFull := mkIdent (tId ++ `Msg ++ `_onSession)
    let uVar := mkIdent `_u
    let next ← `({ s with $sfId:ident := $uVar:ident })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $uVar:ident => $(← mkUpdateRet spec next none #[])))
  if spec.outTy?.isSome then
    let oVar := mkIdent `_o
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(mkIdent (tId ++ `Msg ++ `_emit)):ident $oVar:ident => $(← mkUpdateRet spec (← `(s)) (some ⟨oVar.raw⟩) #[])))
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    let next ← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(mkIdent (tId ++ `Msg ++ colField.getId)) k msg => $(← mkUpdateRet spec next none #[])))
  for q in spec.queries do
    let qNm := q.id
    let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
    let (keyBound, plainRes) ← match q.source with
      | .url keyExpr _ =>
          pure (← bindMentionedFields spec (mentionsIdent keyExpr.raw) keyExpr, (⟨(mkIdent `_qr).raw⟩ : Term))
      | .rpc rspec =>
          let kb ← `(Qed.rpcQueryKey $(← mkRpcQueryParamsBody spec rspec))
          let pr ← if rspec.hasMsgEnsured then `(Qed.Resource.stripEnsured _qr) else `(_qr)
          pure (kb, pr)
    let next ← `({ s with $qNm:ident := (s.$qNm:ident).put _qk $plainRes $keyBound })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $qCtor:ident _qk _qr => $(← mkUpdateRet spec next none #[])))
  for sub in spec.subscriptions do
    let subNm := sub.id
    let wsKeyId := mkIdent (subKeyFnName tId sub)
    let joinCtor := mkIdent (tId ++ `Msg ++ sub.joinCtor)
    let msgCtor := mkIdent (tId ++ `Msg ++ sub.msgCtor)
    let stCtor := mkIdent (tId ++ `Msg ++ sub.statusCtor)
    -- `_wsJoin`
    let joinBody ← match sub.onJoin? with
      | some (binder?, stmts) =>
          let mut b ← compileStmts spec (← `(s)) #[] none #[] stmts.toList
          b ← bindMentionedFields spec (fun g => stmts.any (mentionsIdent · g)) b
          match binder? with
          | some bStx =>
              if bStx.isIdent then
                let bId : Ident := ⟨bStx⟩
                `(let $bId:ident := _wsnap; $b)
              else pure b
          | none => pure b
      | none => pure unchanged
    let joinGuarded ← `(if $wsKeyId s == _wk then $joinBody else $unchanged)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $joinCtor:ident _wk _wsnap => $joinGuarded))
    -- `_wsMsg`
    let msgBody ← match sub.onMsg? with
      | some (bStx, stmts) =>
          let mut b ← compileStmts spec (← `(s)) #[] none #[] stmts.toList
          b ← bindMentionedFields spec (fun g => stmts.any (mentionsIdent · g)) b
          if sub.hasMsgEnsured then
            if bStx.isIdent then
              let bId : Ident := ⟨bStx⟩
              `(let $bId:ident := (_wev).val; have _hWsEns := (_wev).ok; $b)
            else
              `(have _hWsEns := (_wev).ok; $b)
          else
            if bStx.isIdent then
              let bId : Ident := ⟨bStx⟩
              `(let $bId:ident := _wev; $b)
            else pure b
      | none => pure unchanged
    let msgGuarded ← `(if $wsKeyId s == _wk then $msgBody else $unchanged)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $msgCtor:ident _wk _wev => $msgGuarded))
    -- `_wsStatus`
    let sWithSt ← `({ s with $subNm:ident := _wst })
    let stBody ← match sub.onStatus? with
      | some (bStx, stmts) =>
          let mut b ← compileStmts spec sWithSt #[] none #[] stmts.toList
          b ← bindMentionedFields spec (fun g => g != subNm.getId && stmts.any (mentionsIdent · g)) b
          b ← `(let $(mkIdent subNm.getId):ident := _wst; $b)
          if bStx.isIdent then
            let bId : Ident := ⟨bStx⟩
            `(let $bId:ident := _wst; $b)
          else pure b
      | none => mkUpdateRet spec sWithSt none #[]
    let stGuarded ← `(if $wsKeyId s == _wk then $stBody else $unchanged)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $stCtor:ident _wk _wst => $stGuarded))
  return ownArms

private def mkHoistedUpdateCmds (spec : ComponentSpec)
    (pBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (ownArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (unchanged retTy : Term) : CommandElabM (Array (TSyntax `command)) := do
  let tId      := spec.t.getId
  let stateId  := mkIdent (tId ++ `State)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let stepOwnId := mkIdent (tId ++ `stepOwn)
  let subNoopArms ← spec.hoisted.mapM fun h =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ `Msg ++ h.ctorName)) _ => $unchanged)
  let rfNoopArms ← spec.resetForms.mapM fun rf =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ `Msg ++ rf.ctorName)) => $unchanged)
  let stepOwnCmd ← `(command| def $stepOwnId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy :=
    fun m => match m with $[$(ownArms ++ subNoopArms ++ rfNoopArms):matchAlt]*)
  let callStepOwn (sArg mArg : Term) : CommandElabM Term :=
    if spec.hasProps then `($stepOwnId p $sArg $mArg) else `($stepOwnId $sArg $mArg)
  let mut fullArms ← spec.hoisted.mapM fun h => do
    let subCtor := mkIdent (tId ++ `Msg ++ h.ctorName)
    let cUpd := mkIdent (h.info.fullName ++ `update)
    let subF := h.fieldId; let cmVar := mkIdent `_cm; let crVar := mkIdent `_cr; let s1Var := mkIdent `_s1
    let cCall ← if h.info.hasProps then `($cUpd $(← mkHoistedPropsTerm h) s.$subF:ident $cmVar:ident)
      else `($cUpd s.$subF:ident $cmVar:ident)
    let (csExpr, coExpr?, rawC?) ← unpackRetTuple h.info.hasOut h.info.hasEffects crVar
    let ccExpr? ← rawC?.mapM fun rc => `(Cmd.map $subCtor $rc)
    let noOutRet ← mkUpdateRet spec ⟨s1Var.raw⟩ none (match ccExpr? with | some c => #[c] | none => #[])
    let afterSub : Term ← match coExpr? with
      | none => pure noOutRet
      | some coE =>
          let outVar := mkIdent `_co
          let mapOutToMsg? : Option Term ←
            if !h.outArms.isEmpty then
              some <$> (liftMacroM <| mkOutMatchTerm h.info.fullName
                (h.info.events.size + h.info.bindNames.size) h.outArms outVar)
            else pure none
          match mapOutToMsg? with
          | none => pure noOutRet
          | some pmOpt =>
              let pmVar := mkIdent `_pm
              let stepCall ← callStepOwn ⟨s1Var.raw⟩ ⟨pmVar.raw⟩
              let mergedStep ← match ccExpr?, spec.hasEffects with
                | some cc, true =>
                    let srVar := mkIdent `_sr
                    if spec.outTy?.isSome then
                      `(let $srVar:ident := $stepCall; (($srVar:ident).1, ($srVar:ident).2.1, Cmd.batch [$cc, ($srVar:ident).2.2]))
                    else `(let $srVar:ident := $stepCall; (($srVar:ident).1, Cmd.batch [$cc, ($srVar:ident).2]))
                | _, _ => pure stepCall
              `(match $coE:term with
                | none => $noOutRet
                | some $outVar:ident => match $pmOpt:term with
                  | none => $noOutRet
                  | some $pmVar:ident => $mergedStep)
    let mut armBody ← `(let $crVar:ident := $cCall; let $s1Var:ident := { s with $subF:ident := $csExpr }; $afterSub)
    armBody ← bindMentionedFields spec (mentionsIdent armBody.raw) armBody
    `(Lean.Parser.Term.matchAltExpr| | $subCtor $cmVar:ident => $armBody)
  for rf in spec.resetForms do
    let subCtor := mkIdent (tId ++ `Msg ++ rf.ctorName)
    let emptyExpr := mkIdent (`_root_ ++ rf.schemaName ++ `Draft ++ `empty)
    let df := rf.draftField
    let fvId := mkIdent `_fv
    let mut armBody ← `(
      match ($(rf.parseCall) s.$df:ident) with
      | some $fvId:ident =>
          let _s1 := if $(rf.resetCond) then { s with $df:ident := $emptyExpr } else s
          $(← callStepOwn (← `(_s1)) (← `(($(rf.handler) $fvId))))
      | none => $unchanged)
    armBody ← bindMentionedFields spec (mentionsIdent armBody.raw) armBody
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $subCtor => $armBody))
  if !ownArms.isEmpty then
    let otherVar := mkIdent `_m
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $otherVar:ident => $(← callStepOwn (← `(s)) ⟨otherVar.raw⟩)))
  let updateBody ← if fullArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$fullArms:matchAlt]*)
  return #[stepOwnCmd, ← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody)]

private def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId      := spec.t.getId
  let stateId  := mkIdent (tId ++ `State)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let mut outCmds ← mkMsgInductiveCmds spec sites
  for sub in spec.subscriptions do
    let wsKeyId := mkIdent (subKeyFnName tId sub)
    let keyBody ← mkSubKeyExpr spec sub
    outCmds := outCmds.push (← `(command|
      set_option linter.unusedVariables false in
      def $wsKeyId (s : $stateId) : String := $keyBody))
  let unchanged ← mkUpdateRet spec (← `(s)) none #[]
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none,   false => `($stateId)
    | some o, false => `($stateId × Option $o)
    | none,   true  => `($stateId × Cmd $msgId)
    | some o, true  => `($stateId × Option $o × Cmd $msgId)
  let pBinders ← mkPropsBinders spec
  if spec.hoisted.isEmpty && spec.resetForms.isEmpty then
    let updateBody ← if ownArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$ownArms:matchAlt]*)
    return outCmds.push (← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody))
  return outCmds ++ (← mkHoistedUpdateCmds spec pBinders ownArms unchanged retTy)

private def mkViewCmds (spec : ComponentSpec) (body' : Term)
    (msgAndUpdateCmds : Array (TSyntax `command)) : CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let renderId := mkIdent (tId ++ `_qed_render)
  let pBinders ← mkPropsBinders spec
  let mut cmds := msgAndUpdateCmds
  if spec.hasSlotsOrKids then
    let pMsg := mkIdent `_msg; let wrapId := mkIdent `_wrap
    let mut slotBinders ← spec.slots.mapM fun sl => do
      `(bracketedBinder| ($(sl.id) : Html $pMsg := $(← sl.def?.getDM `(Qed.Html.empty))))
    if spec.hasChildren then
      slotBinders := slotBinders.push (← `(bracketedBinder| ($(mkIdent `children) : List (Html $pMsg) := [])))
    let renderBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
    cmds := cmds.push (← `(command| def $renderId {$pMsg : Type} $[$pBinders:bracketedBinder]* ($wrapId : $msgId → $pMsg)
        (s : $stateId) $[$slotBinders:bracketedBinder]* : Html $pMsg := $renderBody))
    let viewCall ← if spec.hasProps then `($renderId p id s) else `($renderId id s)
    return cmds.push (← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewCall))
  let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  cmds := cmds.push (← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewBody))
  let rendered ← if spec.hasProps then `($viewId p s) else `($viewId s)
  cmds := cmds.push (← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]*
      (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route))
  if spec.outTy?.isNone && !spec.hasEffects then
    let renderTagId := mkIdent (tId ++ `_qed_renderTag)
    let compId      := mkIdent (tId ++ `_qed_toComponent)
    let appOptP (fn : Ident) := if spec.hasProps then `($fn p) else `($fn)
    let compExpr ← appOptP compId
    cmds := cmds ++ #[
      ← (match spec.keyF? with
        | some kf =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : String → $msgId → parentMsg) (s : $stateId)
              (k : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)) : Html parentMsg := ($rendered).map (route k))
        | none =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route)),
      ← `(command| $[$doc?:docComment]? def $compId $[$pBinders:bracketedBinder]*
            : Component $stateId $msgId := { update := $(← appOptP updateId), view := $(← appOptP viewId) }) ]
    if let some kf := spec.keyF? then
      let keyOfId := mkIdent (tId ++ `keyOf)
      cmds := cmds ++ #[
        ← `(command| def $keyOfId (s : $stateId) : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)),
        ← `(command| def $(mkIdent (tId ++ `updateKeyed)) $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (k : String) (msg : $msgId) : Array $stateId :=
              Component.updateKeyed $compExpr $keyOfId rows k msg) ]
  return cmds

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyTerm
      return ((← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _) &&
             ((← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _)
    catch _ => return false

private def mkStructJsonCmds (sName : Name) (decls : Array FieldDecl) :
    CommandElabM (Array (TSyntax `command)) := do
  let sId := mkIdent sName; let ids := decls.map (·.id)
  let enc ← decls.mapM fun d => `(($(Syntax.mkStrLit d.id.getId.toString), toJson (x.$(d.id):ident)))
  let dec ← decls.mapM fun d => `((FromJsonField.fromField j $(Syntax.mkStrLit d.id.getId.toString) : Except String $(d.ty)))
  pure #[
    ← `(command| instance $(mkIdent (sName ++ `instToJson)):ident : ToJson $sId := ⟨fun x => Json.obj [$[$enc],*]⟩),
    ← `(command| instance $(mkIdent (sName ++ `instFromJson)):ident : FromJson $sId := ⟨fun j => do
          $[let $ids:ident ← $dec:term]*
          return { $[$ids:ident],* }⟩) ]

private def mkOutJsonCmds (tId : Name) (outCtorSpecs : Array (Name × Array (Ident × Term))) :
    CommandElabM (Array (TSyntax `command)) := do
  let outId := mkIdent (tId ++ `Out)
  let encAlts ← outCtorSpecs.mapM fun (cName, ps) => do
    let cId := mkIdent (tId ++ `Out ++ cName)
    let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let kvPairs ← (List.range pIds.size).toArray.mapM fun i =>
      `(($(Syntax.mkStrLit (toString i)), toJson $(pIds[i]!):ident))
    let allPairs := #[← `(("t", Json.str $(Syntax.mkStrLit cName.toString)))] ++ kvPairs
    `(Lean.Parser.Term.matchAltExpr| | $cId $pTerms* => Json.obj [$[$allPairs],*])
  let mut decBody : Term ← `(Except.error "unknown Out tag")
  for (cName, ps) in outCtorSpecs.reverse do
    let cId := mkIdent (tId ++ `Out ++ cName)
    let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let decSteps ← (List.range ps.size).toArray.mapM fun i =>
      `((FromJsonField.fromField j $(Syntax.mkStrLit (toString i)) : Except String $(ps[i]!.2)))
    let okBr ← `(do
      $[let $pIds:ident ← $decSteps:term]*
      return ($cId $pTerms*))
    decBody ← `(if tag == $(Syntax.mkStrLit cName.toString) then $okBr else $decBody)
  pure #[
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instToJson)):ident : ToJson $outId := ⟨fun o => match o with $[$encAlts:matchAlt]*⟩),
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instFromJson)):ident : FromJson $outId := ⟨fun j => do
          let tag ← (FromJsonField.fromField j "t" : Except String String)
          $decBody:term⟩) ]

private def mkCompLocalDefCmds (spec : ComponentSpec) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let tId      := spec.t.getId
  let initId   := mkIdent (tId ++ `init)
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let regId    := mkIdent (tId ++ `reg)
  let mut cmds : Array (TSyntax `command) := #[
    ← (if spec.hasProps then
        if spec.outTy?.isNone then `(command| def $regId : LocalDef :=
          LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
        else `(command| def $regId : LocalDef := LocalDef.ofProps $idLit $initId $viewId $updateId)
      else if spec.outTy?.isNone then `(command| $[$doc?:docComment]? def $regId : LocalDef :=
        LocalDef.ofSimple $idLit $initId $viewId $updateId)
      else `(command| $[$doc?:docComment]? def $regId : LocalDef :=
        LocalDef.of $idLit $initId $viewId $updateId)),
    ← `(command| $[$doc?:docComment]? def $(mkIdent (tId ++ `_qed_mount)) {msg : Type} (key : String) : Attr msg :=
          localMount $idLit key) ]
  if let some o := spec.outTy? then
    cmds := cmds.push (← `(command| def $(mkIdent (tId ++ `_qed_mountWithOpt)) {msg : Type}
          (key : String) (onOut : $o → Option msg) : Attr msg :=
          localMountWith $idLit key onOut))
  return cmds

private def canSynthDecidablePred (stateId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let pVal ← Term.elabTermEnsuringType pred (← Term.elabType (← `($stateId → Prop)))
      Term.synthesizeSyntheticMVarsNoPostponing
      if ((← Core.getMessageLog).toList.drop preCount).any (·.severity == .error) then return false
      let expected ← Meta.mkAppM ``DecidablePred #[pVal]
      return (← Meta.trySynthInstance expected) matches .some _
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

private def mkCompQueriesCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.queries.isEmpty then return none
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let msgId := mkIdent (tId ++ `Msg)
  let qTerms ← spec.queries.mapM fun q => do
    let qNm := q.id
    let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
    match q.source with
    | .url keyExpr urlExpr =>
        let keyBound ← bindMentionedFields spec (mentionsIdent keyExpr.raw) keyExpr
        `(Resource.query
            (key := fun (s : $stateId) => $keyBound)
            (url := $urlExpr)
            (got := $qCtor)
            (get := fun (s : $stateId) => s.$qNm:ident)
            (set := fun c (s : $stateId) => { s with $qNm:ident := c }))
    | .rpc rspec =>
        let reqTupleTy ← mkRightTuple (`(Unit)) (fun a b => `($a × $b))
          (rspec.mInfo.paramTypeConsts.toList.map fun n => (mkIdent n : Term))
        let paramsBody ← mkRpcQueryParamsBody spec rspec
        let fetchBody ← mkRpcQueryBranches spec rspec fun qaIds => do
          let cbTerm : Term ← if !rspec.hasMsgEnsured then
              `(_qgot _qk)
            else
              let some ensConst := rspec.mInfo.ensPredConst
                | throwErrorAt rspec.rpcRef "internal: missing server `ensures` predicate in `query`"
              let ensApp ← qaIds.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
              let exPrf ← qaIds.foldrM (init := ← `(_qe.ok)) fun qa acc => `(Exists.intro $qa $acc)
              `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => _qgot _qk (_qr.map fun _qe => ⟨_qe.val, $exPrf⟩))
          let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
          let srvId := mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName
          let methId := mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)
          `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$qaTerms:term],*] $cbTerm)))
        `(Qed.Resource.rpcQuery (Req := $reqTupleTy)
            (params? := fun (s : $stateId) => $paramsBody)
            (fetch := fun (s : $stateId) _qgot _qk => $fetchBody)
            (got := $qCtor)
            (get := fun (s : $stateId) => s.$qNm:ident)
            (set := fun c (s : $stateId) => { s with $qNm:ident := c }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(mkIdent (tId ++ `queries)) : List (Query $stateId $msgId) := [$[$qTerms],*]))

private def mkCompSubscriptionsCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.subscriptions.isEmpty then return none
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let msgId := mkIdent (tId ++ `Msg)
  let subTerms ← spec.subscriptions.mapM fun sub => do
    let subNm := sub.id
    let slotLit := Syntax.mkStrLit subNm.getId.toString
    let wsKeyId := mkIdent (subKeyFnName tId sub)
    let joinCtor := mkIdent (tId ++ `Msg ++ sub.joinCtor)
    let msgCtor := mkIdent (tId ++ `Msg ++ sub.msgCtor)
    let stCtor := mkIdent (tId ++ `Msg ++ sub.statusCtor)
    let recTerm ← liftMacroM <| sub.reconnect.toSyntaxTerm
    let unsubFnId := mkIdentFrom sub.chanRef sub.chInfo.unsubHelperConst
    let chFullId := mkIdentFrom sub.chanRef sub.chInfo.fullName
    let openBody ← mkSubBranches spec sub (← `(none)) true fun qaIds => do
      let onJoinCb ← `($joinCtor _wk)
      let onStCb ← `($stCtor _wk)
      let onMsgCb ← if !sub.hasMsgEnsured then
          `($msgCtor _wk)
        else
          let some ensConst := sub.chInfo.ensPredConst
            | throwErrorAt sub.chanRef "internal: missing channel `ensures` predicate in `subscribe`"
          let evTyId := mkIdentFrom sub.chanRef sub.chInfo.eventTypeConst
          let ensApp ← qaIds.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
          let exPrf ← qaIds.foldrM (init := ← `(_we.ok)) fun qa acc => `(Exists.intro $qa $acc)
          `(fun (_we : Qed.Ensured $evTyId ($ensApp)) => $msgCtor _wk ⟨_we.val, $exPrf⟩)
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      let subCmd ← withRef sub.chanRef `(qedCheckChanSub% $chFullId:ident [$[$qaTerms:term],*] $slotLit:str ($recTerm, $onJoinCb, $onMsgCb, $onStCb))
      `(some $subCmd)
    `(Qed.Subscription.mk
        $slotLit
        $wsKeyId
        (fun _wk (s : $stateId) => $openBody)
        ($unsubFnId $slotLit)
        (fun (s : $stateId) => { s with $subNm:ident := Qed.SocketStatus.disconnected }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(mkIdent (tId ++ `subscriptions)) : List (Qed.Subscription $stateId $msgId) := [$[$subTerms],*]))

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvPreds : Array Term) : CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let doc?       := spec.doc?
  let tId        := spec.t.getId
  let stateId    := mkIdent (tId ++ `State)
  let initId     := mkIdent (tId ++ `init)
  let startCmdId := mkIdent (tId ++ `startCmd)
  let msgId      := mkIdent (tId ++ `Msg)
  let updateId   := mkIdent (tId ++ `update)
  let viewId     := mkIdent (tId ++ `view)
  let regsId     := mkIdent (tId ++ `regs)
  let mut cmds : Array (TSyntax `command) := #[]
  let startArg : Term ← if hasStart then `($startCmdId) else `(Qed.Cmd.none)
  let onPortArg : Term ← if spec.portIns.isEmpty then `(Option.none) else do
    let onPortId := mkIdent (tId ++ `onPort)
    let inTuples ← spec.portIns.mapM fun p => do
      let pLit := Syntax.mkStrLit p.id.getId.toString
      let pCtor := mkIdent (tId ++ `Msg ++ p.id.getId)
      `(($pLit, fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $pCtor))
    cmds := cmds.push (← `(command| def $onPortId : String → String → Option $msgId :=
      dispatchPorts #[$inTuples,*]))
    `(some $onPortId)
  let expandedBody ← liftMacroM <| Qed.Jsx.expandJsxIn body'.raw
  let mut templateTerm : Term := ⟨← liftMacroM <|
    Qed.Internal.liftViewWithFields (mkIdent `_qed_s) (spec.states.map (·.id)) expandedBody⟩
  for po in spec.portOuts.reverse do
    if mentionsIdent templateTerm.raw po.id.getId then
      let poId := mkIdent po.id.getId
      templateTerm ← `(let $poId:ident := $(mkIdent (tId ++ po.id.getId)); $templateTerm)
  let appUpdate : Term ← if spec.hasEffects then `($updateId)
    else `(fun s m => ($updateId s m, Qed.Cmd.none))
  let onSessionArg : Term ← match spec.sessionField? with
    | some _ => `(some $(mkIdent (tId ++ `Msg ++ `_onSession)))
    | none   => `(none)
  let baseApp0 : Term ← match spec.route? with
    | some _ => `(Qed.Internal.mkRoutedApp $initId $appUpdate $templateTerm
        (onRoute := $(mkIdent (tId ++ `Msg ++ `_onRoute))) (onSession := $onSessionArg)
        (start := $startArg) (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
    | none   => `(Qed.Internal.mkApp $initId $appUpdate $templateTerm (onSession := $onSessionArg)
        (start := $startArg) (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
  let baseApp1 : Term ← if spec.themes.isEmpty then pure baseApp0 else do
    let env ← getEnv; let currNs ← getCurrNamespace; let openDecls := (← getScope).openDecls
    let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
    let mut thStyleTerms : Array Term := #[]
    for thId in spec.themes do
      let nm := thId.getId
      let thInfo? := (thReg.find? (currNs ++ nm)).orElse (fun _ => thReg.find? nm) |>.orElse fun _ =>
        openDecls.findSome? fun
          | .simple ns _ => thReg.find? (ns ++ nm)
          | .explicit id declName => if id == nm then thReg.find? declName else none
      let some thInfo := thInfo?
        | throwErrorAt thId s!"unknown `theme` `{nm}`"
      thStyleTerms := thStyleTerms.push (mkIdentFrom thId thInfo.styleConst)
    `(Qed.Internal.App.withExtraStyles [$[$thStyleTerms],*] $baseApp0)
  let baseApp : Term ← if spec.stylesheets.isEmpty then pure baseApp1 else do
    let shLits := spec.stylesheets.map Syntax.mkStrLit
    `(Qed.Internal.App.withStylesheets [$[$shLits:str],*] $baseApp1)
  let dehydApp : Term ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $initId $baseApp)
    else `(Qed.Internal.App.withDehydrate (Dehydrate.except $initId [$[$spec.ephemeralFields:ident],*]) $baseApp)
  let queriedApp : Term ← if spec.queries.isEmpty then pure dehydApp else
    `(Qed.Internal.App.withQueries $(mkIdent (tId ++ `queries)) $dehydApp)
  let subbedApp : Term ← if spec.subscriptions.isEmpty then pure queriedApp else
    `(Qed.Internal.App.withSubscriptions $(mkIdent (tId ++ `subscriptions)) $queriedApp)
  let compInv? : Option Term ← if stateInvPreds.isEmpty then pure none
    else if stateInvPreds.size == 1 then pure (some (← `(($(stateInvPreds[0]!) : $stateId → Prop))))
    else do
      let sVar := mkIdent `_qed_s
      let checks ← stateInvPreds.mapM fun p => `(($p) $sVar)
      pure (some (← `(fun ($sVar:ident : $stateId) => $(← mkConjBody checks))))
  let hasDecInv ← match compInv? with
    | some inv => canSynthDecidablePred stateId inv
    | none     => pure false
  let finalApp : Term ← match compInv?, hasDecInv with
    | some inv, true => `(Qed.App.guardRehydrate ($inv) $subbedApp)
    | _, _           => pure subbedApp
  let appIdent := mkIdent (tId ++ `app)
  let viewIdent := mkIdent (tId ++ `view)
  cmds := cmds.push (← `(command| $[$doc?:docComment]? def $appIdent : App $stateId $msgId :=
    $finalApp))
  match compInv?, hasDecInv with
  | some inv, true =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `rehydrate_inv)) (raw : String) (m' : $stateId) :
            ($appIdent).rehydrate raw = some m' → ($inv) m' :=
          Qed.App.guardRehydrate_sound _ _ _ raw m'))
  | some inv, false =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `dehydrate_inv)) :
            ∀ m m', ($inv) m → ($appIdent).rehydrate (($appIdent).dehydrate m) = some m' → ($inv) m' := by
          dsimp only [$appIdent:ident]; qedProveDehydrateInv))
  | none, _ => pure ()
  let appViewEqCmd ← `(command|
    theorem $(mkIdent (tId ++ `app_view_eq)) (s : $stateId) :
        Qed.Html.canonical (Qed.App.view $appIdent s) = Qed.Html.canonical ($viewIdent s) := by
      qedProveViewEquiv $appIdent $viewIdent)
  return (cmds, appViewEqCmd)

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command) × Bool × Bool) := do
  let tId        := spec.t.getId
  let fs         := spec.states.map (·.id)
  let stateId    := mkIdent (tId ++ `State)
  let initId     := mkIdent (tId ++ `init)
  let startCmdId := mkIdent (tId ++ `startCmd)
  let msgId      := mkIdent (tId ++ `Msg)
  let viewId     := mkIdent (tId ++ `view)
  let regId      := mkIdent (tId ++ `reg)
  let regsId     := mkIdent (tId ++ `regs)
  let mut cmds : Array (TSyntax `command) := #[]
  if spec.mountable then
    let dsT := spec.states.filterMap (·.def?)
    cmds := cmds.push (← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }))
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart)
  let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  if hasStart then
    let pBinders ← mkPropsBinders spec
    let subStarts ← hoistedStarts.mapM fun h => do
      let cStart := mkIdent (h.info.fullName ++ `startCmd)
      let call ← if h.info.hasProps then `($cStart $(← mkHoistedPropsTerm h)) else `($cStart)
      `(Cmd.map $(mkIdent (tId ++ `Msg ++ h.ctorName)) $call)
    let mut startBody ← mkCmdBatch (starts' ++ subStarts)
    if spec.mountable then
      startBody ← bindMentionedFields spec (mentionsIdent startBody.raw) startBody
      if mentionsIdent startBody.raw `s then
        startBody ← `(let s := $initId; $startBody)
    cmds := cmds.push (← `(command| def $startCmdId $[$pBinders:bracketedBinder]* : Cmd $msgId := $startBody))
  let outCtorSpecs : Array (Name × Array (Ident × Term)) :=
    spec.events.map (fun ev => (ev.id.getId, ev.params)) ++
    spec.binds.map (fun bd => (Name.mkSimple s!"set_{bd.id.getId}", #[(mkIdent `v, bd.ty)]))
  let propsOk ← spec.props.allM (canSynthJson ``FromJsonField ·.ty)
  let stateOk ← spec.states.allM (canSynthJson ``FromJsonField ·.ty)
  let outJsonOk ←
    if spec.outTy?.isSome then outCtorSpecs.allM fun (_, ps) => ps.allM (canSynthJson ``FromJsonField ·.2)
    else pure true
  let canEmitCodecs := propsOk && stateOk
  if canEmitCodecs then
    cmds := cmds ++ (← mkStructJsonCmds (tId ++ `Props) spec.props) ++ (← mkStructJsonCmds (tId ++ `State) spec.states)
  if spec.outTy?.isSome && outJsonOk then
    cmds := cmds ++ (← mkOutJsonCmds tId outCtorSpecs)
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && canEmitCodecs && outJsonOk
  if hasLocalDef then
    cmds := cmds ++ (← mkCompLocalDefCmds spec idLit)
  let own : Term ← if hasLocalDef then `([$regId]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
    LocalDef.dedupe ($own ++ qedInternalLocalRegistrations% $viewId)))
  return (cmds, hasStart, hasLocalDef)

/-! ## Inline Invariant Elaboration -/

private def isViewPred (msgId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let expected ← Term.elabType (← `(Html $msgId → Bool))
      let _ ← Term.elabTermEnsuringType pred expected
      Term.synthesizeSyntheticMVarsNoPostponing
      return ((← Core.getMessageLog).toList.drop preCount).all (·.severity != .error)
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

private def isForEachStyled (invStx : Syntax) : CommandElabM Bool := do
  let pred ← lowerCompExpr .val invStx[2]
  let hasHoldsIn := invStx[5].getNumArgs > 0
  let using? : Option Ident := if invStx[6].getNumArgs == 2 then some ⟨invStx[6][1]⟩ else none
  if hasHoldsIn then return true
  let some pid := using?.or (if pred.raw.isIdent then some ⟨pred.raw⟩ else none) | return false
  liftTermElabM do
    try
      let cn ← realizeGlobalConstNoOverload pid
      Meta.forallTelescope (← getConstInfo cn).type fun _ body => return body.eq?.isSome
    catch _ => return false

private def elabForEachInlineInv (spec : ComponentSpec) (invStx : Syntax) (isStyled : Bool) :
    CommandElabM (Option Term) := do
  let tId      := spec.t.getId
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let invId ← resolveInvIdent invStx tId
  let pred ← lowerCompExpr .val invStx[2]
  let colField : Ident := ⟨invStx[4]⟩
  let using? : Option Ident := if invStx[6].getNumArgs == 2 then some ⟨invStx[6][1]⟩ else none
  let pf? : Option Term := if invStx[7].getNumArgs == 2 then some ⟨invStx[7][1]⟩ else none
  let (predToEmit, usingToEmit?) ← match using?, pf? with
    | some u, _ => pure (pred, some u)
    | none, some _ =>
        unless pred.raw.isIdent do
          throwErrorAt invStx "specify `using <ChildInvariant>` when proving a custom predicate"
        let childInv : Ident := ⟨pred.raw⟩
        let ep ← if isStyled then
          liftTermElabM do
            let cn ← realizeGlobalConstNoOverload childInv
            Meta.forallTelescope (← getConstInfo cn).type fun _ body => do
              let some lhs := body.eq?.map (·.2.1) | throwErrorAt childInv
                "`{childInv}` doesn't look like a `… holds_in …` invariant"
              PrettyPrinter.delab lhs.appFn!
        else liftTermElabM (extractInvPred childInv)
        pure (ep, some childInv)
    | none, none =>
        unless pred.raw.isIdent do
          throwErrorAt invStx "specify `using <ChildInvariant>` for an inline `for_each` predicate"
        pure (pred, none)
  match isStyled, usingToEmit? with
  | true,  some u => elabCommand (← `(qedInternalInvariant $invId : $predToEmit for_each $colField holds_in $viewId using $u $[:= $pf?]?))
  | true,  none   =>
      let pid : Ident := ⟨predToEmit.raw⟩
      elabCommand (← `(qedInternalInvariant $invId : $pid for_each $colField holds_in $viewId))
  | false, some u => elabCommand (← `(qedInternalInvariant $invId : $predToEmit for_each $colField preserved_by $updateId using $u $[:= $pf?]?))
  | false, none   =>
      let pid : Ident := ⟨predToEmit.raw⟩
      elabCommand (← `(qedInternalInvariant $invId : $pid for_each $colField preserved_by $updateId))
  if isStyled then return none
  try
    return some (← liftTermElabM (extractInvPred invId))
  catch _ => return none

private def elabViewInlineInv (spec : ComponentSpec) (invStx : Syntax) (invId : Ident)
    (rawClauses : Array Syntax) (clauses : Array Term) (assume? pf? : Option Term) : CommandElabM Unit := do
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  let vPred ← match clauses.toList with
    | [p] => pure p
    | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
    | [] => throwErrorAt invStx "empty view styling invariant"
  let predStr := String.intercalate ", " (rawClauses.toList.map fun c => (c.reprint.getD "this rule").trimmed)
  if spec.hasProps then
    let rhs ← pf?.getDM `(by
      let _qed_hv := $viewId p
      change ∀ m, ($vPred) (_qed_hv m) = true
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := $rhs))
  else
    let prop ← match assume? with
      | some a =>
          let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
          `(∀ m, ($P) m → ($vPred) ($viewId m) = true)
      | none => `(∀ m, ($vPred) ($viewId m) = true)
    match pf? with
    | some p => elabCommand (← `(theorem $invId:ident : $prop := $p))
    | none   => elabCommand (← `(
        set_option linter.unusedSimpArgs false in
        theorem $invId:ident : $prop := by
          qedDischargeStyling $viewId $invId $(Syntax.mkStrLit predStr)))
    let fullView ← liftCoreM (resolveGlobalConstNoOverload viewId)
    let compFull := fullView.getPrefix
    let appViewEqName := compFull ++ `app_view_eq
    if (← getEnv).contains appViewEqName then
      let appId : Ident := mkIdent (compFull ++ `app)
      let appViewEqId : Ident := mkIdent appViewEqName
      let appInvId : Ident := mkIdentFrom invId (invId.getId.appendAfter "_app")
      let saved ← get
      try
        match assume? with
        | some a =>
            let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
            elabCommand (← `(command| set_option linter.unusedSimpArgs false in
              theorem $appInvId : ∀ m, ($P) m → ($vPred) (Qed.App.view $appId m) = true :=
                fun m ha =>
                  (Qed.canonical_congr_pred ($appViewEqId m)
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])).trans
                    ($invId m ha)))
        | none =>
            elabCommand (← `(command| set_option linter.unusedSimpArgs false in
              theorem $appInvId : ∀ m, ($vPred) (Qed.App.view $appId m) = true :=
                fun m =>
                  (Qed.canonical_congr_pred ($appViewEqId m)
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])).trans
                    ($invId m)))
      catch _ => set saved

private def elabStateInlineInv (spec : ComponentSpec) (invId : Ident)
    (clauses : Array Term) (using? : Option (Array Term)) (pf? : Option Term) : CommandElabM Term := do
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let initId   := mkIdent (tId ++ `init)
  let updateId := mkIdent (tId ++ `update)
  let conj ← mkConjBody clauses
  let pred ← `(fun (s : $stateId) => $(← bindMentionedFields spec (mentionsIdent conj.raw) conj))
  let usingL := using?.getD #[]
  if spec.hasProps then
    if spec.mountable then
      let initInvId := mkIdentFrom invId (invId.getId.appendAfter "_init")
      elabCommand (← `(theorem $initInvId:ident : ($pred) $initId := by
        qedDischargeInit [$[$usingL],*] $initId $invId ($pred)))
    let rhs ← pf?.getDM `(by qedDischargePreserved [$[$usingL],*] ($updateId p) $invId ($pred))
    elabCommand (← `(theorem $invId:ident (p : $propsId) :
      ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := $rhs))
  else
    let stepPf? ← pf?.mapM fun pf =>
      if spec.mountable then
        `(by exact ⟨by qedDischargeInit [$[$usingL],*] $initId $invId ($pred), $pf⟩)
      else pure pf
    let initOpt? : Option Term := if spec.mountable then some initId else none
    elabCommand (← `(qedInternalInvariant $invId : $pred $[from $initOpt?]? preserved_by $updateId using [$[$usingL],*] $[ := $stepPf?]?))
  return pred

private def elabInlineInvariantsPhase (spec : ComponentSpec) (wantView : Bool) : CommandElabM (Array Term) := do
  let tId   := spec.t.getId
  let msgId := mkIdent (tId ++ `Msg)
  let mut statePreds : Array Term := #[]
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      let isStyled ← isForEachStyled invStx
      if isStyled == wantView then
        if let some pred ← elabForEachInlineInv spec invStx isStyled then
          statePreds := statePreds.push pred
      continue
    let rawClauses := invStx[2].getSepArgs
    let hasHoldsIn := invStx[3].getNumArgs > 0
    let assume? : Option Term ←
      if hasHoldsIn && invStx[3][2].getNumArgs == 2 then some <$> lowerCompExpr .val invStx[3][2][1] else pure none
    let using? : Option (Array Term) :=
      if invStx[4].getNumArgs == 4 then some (invStx[4][2].getSepArgs.map (⟨·⟩)) else none
    let pf? : Option Term := if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let valClauses? : Option (Array Term) ←
      if hasHoldsIn then
        some <$> rawClauses.mapM (lowerCompExpr .val)
      else if using?.isSome || rawClauses.isEmpty then
        pure none
      else
        try some <$> rawClauses.mapM (lowerCompExpr .val) catch _ => pure none
    let autoView ← match valClauses? with
      | some vc =>
          if !hasHoldsIn && !vc.any (fun c => spec.allNames.any (mentionsIdent c.raw)) then
            vc.allM (isViewPred msgId)
          else pure false
      | none => pure false
    let isView := hasHoldsIn || autoView
    if isView == wantView then
      let invId ← resolveInvIdent invStx tId
      if isView then
        let valClauses ← match valClauses? with
          | some vc => pure vc
          | none => rawClauses.mapM (lowerCompExpr .val)
        elabViewInlineInv spec invStx invId rawClauses valClauses assume? pf?
      else
        let propClauses ← rawClauses.mapM (lowerCompExpr .propInv)
        statePreds := statePreds.push (← elabStateInlineInv spec invId propClauses using? pf?)
  return statePreds

private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then
    withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k
  else k

open Lean Elab Term Meta in
@[term_elab qedCheckRpcCallTerm]
def elabQedCheckRpcCall : TermElab := fun stx expectedType? => do
  let srvId : Ident := ⟨stx[1]⟩
  let methId : Ident := ⟨stx[2]⟩
  let argTerms : Array Term := stx[4].getSepArgs.map (⟨·⟩)
  let cbTerm : Term := ⟨stx[6]⟩
  let srvName := srvId.getId
  let methStr := methId.getId.toString
  let env ← getEnv
  let some srvInfo := (serverRegistry.getState env).find? srvName
    | throwErrorAt stx s!"internal: unknown server `{srvName}` in RPC check"
  let some mInfo := srvInfo.methods.find? (·.name == methStr)
    | throwErrorAt stx s!"internal: unknown method `{methStr}` on `{srvName}` in RPC check"
  let rawRpcId := mkIdentFrom stx mInfo.rawRpcConst
  let callApp ← argTerms.foldlM (init := (rawRpcId : Term)) fun acc a => `($acc $a)
  let fullCall ← `($callApp $cbTerm)
  let resExpr ← elabTerm fullCall expectedType?
  let resExpr ← instantiateMVars resExpr
  let mut argExprs : Array Expr := #[]
  let fnArgs := resExpr.getAppArgs
  if resExpr.isAppOf mInfo.rawRpcConst && fnArgs.size ≥ 2 + mInfo.paramCount then
    for i in [0:mInfo.paramCount] do
      argExprs := argExprs.push (← instantiateMVars fnArgs[2 + i]!)
  else
    for (aT, i) in argTerms.zipIdx do
      let pTy := Lean.mkConst mInfo.paramTypeConsts[i]!
      argExprs := argExprs.push (← instantiateMVars (← elabTermEnsuringType aT pTy))
  if mInfo.hasClientReq || mInfo.requiresAuth then
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let mctx ← getMCtx
    let sessionId? ← currentCompSessionRef.get
    pendingRpcChecks.modify (·.push {
      callRef := stx
      srvShort := srvInfo.shortName
      methodName := mInfo.name
      reqConst? := mInfo.clientReqConst
      reqLabel := mInfo.clientReqLabel
      requiresAuth := mInfo.requiresAuth
      argExprs
      lctx
      localInsts
      mctx
      sessionVar? := sessionId?.map (·.getId)
    })
  return resExpr

open Lean Elab Meta in
private def verifyPendingRpcChecks (spec : ComponentSpec) (invPreds : Array Term) :
    CommandElabM Unit := do
  let checks ← pendingRpcChecks.get
  if checks.isEmpty then return
  let stateConstName ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent (spec.t.getId ++ `State))
  for chk in checks do
    liftTermElabM do
      let proofLctx : LocalContext := chk.lctx.foldl (init := {}) fun acc decl =>
        match decl with
        | .ldecl _ fv nm ty val _ k => acc.mkLetDecl fv nm ty val (nondep := false) (kind := k)
        | .cdecl _ fv nm ty bi k    => acc.mkLocalDecl fv nm ty bi (kind := k)
      Meta.withMCtx chk.mctx <| withLCtx proofLctx chk.localInsts do
        let mut invProps : Array Expr := #[]
        let mut stateFVar? : Option Expr := none
        for decl in chk.lctx do
          if !decl.isImplementationDetail && !decl.isLet then
            if (← Meta.whnf decl.type).isConstOf stateConstName then
              if stateFVar?.isNone then stateFVar? := some decl.toExpr
              let fnTy := Expr.forallE `_ (Lean.mkConst stateConstName) (Expr.sort Level.zero) .default
              for predT in invPreds do
                let predExpr ← Term.elabTermEnsuringType predT fnTy
                Term.synthesizeSyntheticMVarsNoPostponing
                let predExpr ← instantiateMVars predExpr
                invProps := invProps.push ((Expr.app predExpr decl.toExpr).headBeta)
        let cleanGoalExpr (e : Expr) : MetaM String := do
          let e ← instantiateMVars e
          let e ← Meta.zetaReduce e
          let e ← Meta.transform e (pre := fun sub => do
            if sub.isAppOfArity ``Qed.Lang.QedVal.val 4 then
              return .visit (sub.getArg! 3)
            return .continue)
          let fmt ← Meta.ppExpr e
          return (fmt.pretty.replace "✝" "").trimmed
        let tryDischarge (goalBody : Expr) : TermElabM (Option String) := do
          let fullGoal ← invProps.foldrM (init := goalBody) fun hyp acc =>
            pure (Expr.forallE `_ hyp acc .default)
          let fullGoal ← instantiateMVars fullGoal
          let mv ← Meta.mkFreshExprSyntheticOpaqueMVar fullGoal
          try
            let unsolved ← Tactic.run mv.mvarId! do
              Tactic.evalTactic (← `(tactic| intros; qedProveRpcReq))
            if unsolved.isEmpty then return none
            let msg ← unsolved[0]!.withContext do cleanGoalExpr (← unsolved[0]!.getType)
            return some msg
          catch _ =>
            let reduced := (← Meta.unfoldDefinition? goalBody).getD goalBody
            return some (← cleanGoalExpr reduced)
        if chk.requiresAuth then
          let some sfName := chk.sessionVar?
            | throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`ctx.userId != none`), but component `{spec.t.getId}` has no `session` state.\nAdd `session user` and guard the call with `when user.isSome:` or `if user.isSome: ...`."
          let sfExpr : Expr ←
            match chk.lctx.findDecl? fun decl =>
                if !decl.isImplementationDetail && decl.userName.eraseMacroScopes == sfName then some decl.toExpr else none with
            | some e => pure e
            | none =>
                let some sFVar := stateFVar?
                  | throwErrorAt chk.callRef m!"internal: could not locate component state while checking session auth for `{chk.srvShort}.{chk.methodName}`"
                Meta.mkProjection sFVar sfName
          let sfTy ← Meta.whnf (← Meta.inferType sfExpr)
          let elemTy := if sfTy.isAppOfArity ``Option 1 then sfTy.appArg! else Lean.mkConst ``String
          let noneExpr ← Meta.mkAppOptM ``Option.none #[some elemTy]
          let authGoal ← Meta.mkAppM ``Ne #[sfExpr, noneExpr]
          if (← tryDischarge authGoal).isSome then
            throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`{sfName} != none`), which could not be proved at this call site.\nGuard this call with `when {sfName}.isSome`, `if {sfName}.isSome: ...`, or declare `invariant ...: {sfName}.isSome`."
        if let some reqConst := chk.reqConst? then
          let reqGoal := mkAppN (Lean.mkConst reqConst) chk.argExprs
          if let some obl ← tryDischarge reqGoal then
            let oblLine := if obl.isEmpty then "" else s!"\nRemaining proof obligation:\n  {obl}"
            throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` precondition `{chk.reqLabel}` could not be proved at this call site.{oblLine}\nSupply valid arguments, guard with `when`/`if`, pass refined `Field`/`Ensured` values, or declare a component `invariant`."

open Lean Elab Term Meta in
private def elabAndRecordChanCheck (stx : Syntax) (expectedType? : Option Expr)
    (argTerms : Array Term) (slotLit : TSyntax `str)
    (helperConst : Name) (paramCount : Nat) (paramTypeConsts : Array Name)
    (trailingArgs : Array Term) (srvShort methodName : String)
    (reqConst? : Option Name) (reqLabel : String) (requiresAuth : Bool) : TermElabM Expr := do
  let fnId := mkIdentFrom stx helperConst
  let mut fullCall : Term ← `($fnId $slotLit)
  for a in argTerms do
    fullCall ← `($fullCall ($a))
  for t in trailingArgs do
    fullCall ← `($fullCall ($t))
  let resExpr ← instantiateMVars (← elabTerm fullCall expectedType?)
  let mut argExprs : Array Expr := #[]
  let fnArgs := resExpr.getAppArgs
  if resExpr.isAppOf helperConst && fnArgs.size ≥ 2 + paramCount then
    for i in [0:paramCount] do
      argExprs := argExprs.push (← instantiateMVars fnArgs[2 + i]!)
  else
    for (aT, i) in argTerms.zipIdx do
      argExprs := argExprs.push (← instantiateMVars (← elabTermEnsuringType aT (Lean.mkConst paramTypeConsts[i]!)))
  if reqConst?.isSome || requiresAuth then
    pendingRpcChecks.modify (·.push {
      callRef := stx, srvShort, methodName, reqConst?, reqLabel, requiresAuth, argExprs,
      lctx := ← getLCtx, localInsts := ← getLocalInstances, mctx := ← getMCtx,
      sessionVar? := (← currentCompSessionRef.get).map (·.getId)
    })
  return resExpr

open Lean Elab Term Meta in
@[term_elab qedCheckChanSubTerm]
def elabCheckChanSub : TermElab := fun stx expectedType? => do
  let chFullName := stx[1].getId
  let some chInfo := (Qed.channelRegistry.getState (← getEnv)).find? chFullName
    | throwErrorAt stx s!"internal: unknown channel `{chFullName}` in subscription check"
  elabAndRecordChanCheck stx expectedType? (stx[3].getSepArgs.map (⟨·⟩)) ⟨stx[5]⟩
    chInfo.subHelperConst chInfo.paramCount chInfo.paramTypeConsts
    #[⟨stx[7]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩, ⟨stx[13]⟩]
    chInfo.ownerShort chInfo.channelName chInfo.clientReqConst chInfo.clientReqLabel chInfo.requiresAuth

open Lean Elab Term Meta in
@[term_elab qedCheckChanSendTerm]
def elabCheckChanSend : TermElab := fun stx expectedType? => do
  let chFullName := stx[1].getId
  let some chInfo := (Qed.channelRegistry.getState (← getEnv)).find? chFullName
    | throwErrorAt stx s!"internal: unknown channel `{chFullName}` in send check"
  elabAndRecordChanCheck stx expectedType? (stx[3].getSepArgs.map (⟨·⟩)) ⟨stx[5]⟩
    chInfo.sendHelperConst chInfo.sendParamCount chInfo.sendParamTypeConsts #[]
    chInfo.ownerShort s!"{chInfo.channelName}.send" chInfo.sendReqConst chInfo.sendReqLabel false

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let errsInit := (← get).messages.toList.filter (·.severity == .error) |>.length
  let compNs := (← getCurrNamespace) ++ stx[2].getId
  pendingRpcChecks.set #[]
  currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    -- Elaborate component-colocated `style` clauses into `<Comp>.<styleName>` before opening `compNs`
    for stCl in rawSpec.styles do
      withOpenNs compNs do
        let sNameId : Ident := ⟨stCl[1]⟩
        let qualifiedId := mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId)
        let extendsIds : Array Ident :=
          if stCl[2].getNumArgs == 1 then stCl[2][0][1].getSepArgs.map (⟨·⟩) else #[]
        let strictTokens := stCl[3].getNumArgs == 1
        let bodyStxs := stCl[5].getArgs
        Qed.StyleDsl.elabStyleDef none qualifiedId extendsIds strictTokens bodyStxs
    withOpenNs compNs do
      if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
          rawSpec.starts.isEmpty && rawSpec.sessionField?.isNone &&
          rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty &&
          rawSpec.subscriptions.isEmpty then
        let sitesRef ← IO.mkRef #[]
        let hoistedRef ← IO.mkRef #[]
        let formDraftsRef ← IO.mkRef #[]
        let resetFormsRef ← IO.mkRef #[]
        let usedRpcsRef ← IO.mkRef #[]
        let contCtrRef ← IO.mkRef 0
        let rCtx : RewriteCtx := {
          stateFields := #[], bindFields := rawSpec.bindNames, propNames := rawSpec.propNames,
          isPureComp := true,
          msgPath := rawSpec.t.getId ++ `Msg, hasOut := false, collections := #[],
          sites := sitesRef, hoisted := hoistedRef,
          formDrafts := formDraftsRef, resetForms := resetFormsRef,
          allowHoist := true, usedRpcs := usedRpcsRef, contCounter := contCtrRef }
        let body' ← lowerCompExpr .val (← rewriteIn rCtx false rawSpec.body)
        if (← hoistedRef.get).isEmpty && (← formDraftsRef.get).isEmpty && (← resetFormsRef.get).isEmpty then
          elabPureComponent rawSpec body'
          okRef.set true
          return
      let idLit := Syntax.mkStrLit compNs.toString
      let (sites, route'?, queries', starts', body', hoisted, formDrafts, resetForms, ownUsedRpcs) ←
        collectSitesAndRewriteStateful rawSpec
      let mut allUsedRpcs := ownUsedRpcs
      let mut allUsedChannels : Array (String × String) := #[]
      for sub in rawSpec.subscriptions do
        match sub.chInfo.kind with
        | .fullstack _ srvShort _ =>
            let pair := (srvShort, sub.chInfo.channelName)
            unless allUsedChannels.contains pair do
              allUsedChannels := allUsedChannels.push pair
        | .external .. => pure ()
      for h in hoisted do
        for ep in h.info.usedRpcs do
          unless allUsedRpcs.contains ep do
            allUsedRpcs := allUsedRpcs.push ep
        for ch in h.info.usedChannels do
          unless allUsedChannels.contains ch do
            allUsedChannels := allUsedChannels.push ch
      let ownHasEffects :=
        !starts'.isEmpty ||
        !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty || !queries'.isEmpty ||
        !rawSpec.subscriptions.isEmpty ||
        sites.any (fun s => s.stmts?.any (·.any hasPerformNode)) ||
        (route'?.any fun rd => rd.alts.any hasPerformNode) ||
        hoisted.any (·.info.hasEffects)
      let spec ← elabStructsAndResolveTypes {
        rawSpec with route? := route'?, queries := queries', hasEffects := ownHasEffects,
                     usedRpcs := allUsedRpcs, usedChannels := allUsedChannels
      } hoisted formDrafts resetForms
      currentCompSessionRef.set spec.sessionField?
      let errsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
      let coreCmds ← mkViewCmds spec body' (← mkMsgAndUpdateCmds spec sites)
      for c in coreCmds do elabCommand c
      let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec starts' idLit
      for c in mountCmds do elabCommand c
      if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
        if let some qCmd ← mkCompQueriesCmd? spec then elabCommand qCmd
        if let some sCmd ← mkCompSubscriptionsCmd? spec then elabCommand sCmd
      let stateInvPreds ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
      let errsAfterInvs := (← get).messages.toList.filter (·.severity == .error) |>.length
      let activePreds := if errsAfterInvs == errsBefore then stateInvPreds else #[]
      verifyPendingRpcChecks spec activePreds
      let errsAfterState := (← get).messages.toList.filter (·.severity == .error) |>.length
      if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
        let (appCmds, eqCmd) ← mkCompAppCmds spec body' hasStart activePreds
        for c in appCmds do elabCommand c
        let errsAfterApp := (← get).messages.toList.filter (·.severity == .error) |>.length
        if errsAfterApp == errsBefore then elabCommand eqCmd
      let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
      let usedRpcsId := mkIdent (spec.t.getId ++ `usedRpcs)
      let epTerms ← allUsedRpcs.mapM fun (sStr, mStr) =>
        `((($(Syntax.mkStrLit sStr), $(Syntax.mkStrLit mStr)) : String × String))
      elabCommand (← `(command| def $usedRpcsId : List (String × String) := [$[$epTerms],*]))
      let usedChsId := mkIdent (spec.t.getId ++ `usedChannels)
      let chTerms ← allUsedChannels.mapM fun (sStr, cStr) =>
        `((($(Syntax.mkStrLit sStr), $(Syntax.mkStrLit cStr)) : String × String))
      elabCommand (← `(command| def $usedChsId : List (String × String) := [$[$chTerms],*]))
      let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
      modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
        hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects,
        hasStart, mountable := spec.mountable, hasLocalDef,
        usedRpcs := allUsedRpcs, usedChannels := allUsedChannels }
      okRef.set true
  finally
    pendingRpcChecks.set #[]
    currentCompSessionRef.set none
    let errsEnd := (← get).messages.toList.filter (·.severity == .error) |>.length
    if !(← okRef.get) || errsEnd > errsInit then
      setEnv savedEnv

end CompElab
end Qed
