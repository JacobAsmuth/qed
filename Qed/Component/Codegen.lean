import Qed.Component.Rewrite
import Qed.Runtime.Cmd

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Shared Structure, Binder & Codegen Helpers -/

def subKeyDefName   (tId : Name) (h : HoistedSub) : Name := tId ++ Name.mkSimple s!"_subKey_{h.fieldId.getId}"
def subPropsDefName (tId : Name) (h : HoistedSub) : Name := tId ++ Name.mkSimple s!"_subProps_{h.fieldId.getId}"
def queryParamsFnName (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qParams_{q.id.getId}"
def queryKeyFnName    (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qKey_{q.id.getId}"
def queryFetchFnName  (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qFetch_{q.id.getId}"
def subKeyFnName      (tId : Name) (sub : SubDecl) : Name := tId ++ Name.mkSimple s!"_wsKey_{sub.id.getId}"

@[noinline] def mkPureCompFnCmds (spec : ComponentSpec) (fieldTys : Array (Name × Term)) : CommandElabM (Array CmdStx) :=
  Lang.foldlCmd spec.pureFns #[] fun cmds f => do
    let some retTy := f.retTy? | return cmds
    let capPairs ← Lang.mapCmd f.capturedFields fun cn => do
      let some (_, ty) := fieldTys.find? (·.1 == cn) | throwErrorAt f.id s!"internal: missing resolved type for field `{cn}` in `fn {f.id.getId}`"
      return (mkIdent cn, ty)
    let bodyT ← lowerPureFnStmts s!"fn {spec.t.getId}.{f.id.getId}" f.stmts.toList (lowerCompExpr .val) (lowerCompExpr .propGuard)
    return cmds.push (← Lang.runPQ do
      let mkB := fun (id, ty) => `(bracketedBinder| ($id:ident : $ty))
      let (capBinders, pBinders) := (← Lang.mapPQ capPairs mkB, ← Lang.mapPQ f.params mkB)
      `(command| set_option linter.unusedVariables false in def $(spec.id f.id.getId) $[$capBinders:bracketedBinder]* $[$pBinders:bracketedBinder]* : $retTy := $bodyT))

private partial def anonymizePat (stx : Syntax) : Syntax :=
  let mapSep (n : Syntax) := Syntax.node n.getHeadInfo n.getKind (n.getArgs.map fun a => if a.isAtom then a else anonymizePat a)
  let mapInner (i : Nat) := let inner := stx.getArg i; setStxArg stx i (setStxArg inner 1 (mapSep (inner.getArg 1)))
  match stx.getKind with
  | ``qedPatIdent =>
      if (stx.getArg 1).getNumArgs == 3 then mapInner 1
      else
        let vn := (stx.getArg 0).getId.eraseMacroScopes; let s := vn.toString
        if vn.isAtomic && !["_", "none", "true", "false"].contains s && !s.front.isUpper then
          Syntax.node stx.getHeadInfo ``qedPatWild #[Syntax.atom stx.getHeadInfo "_"]
        else stx
  | ``qedPatDot   => if (stx.getArg 2).getNumArgs == 3 then mapInner 2 else stx
  | ``qedPatParen | ``qedPatList => setStxArg stx 1 (mapSep (stx.getArg 1))
  | ``qedPatCons  => setStxArg (setStxArg stx 0 (anonymizePat (stx.getArg 0))) 2 (anonymizePat (stx.getArg 2))
  | _ => stx

@[noinline] def wrapViewGuards (guards : Array ViewGuard) (leaf fallback : Term) : CommandElabM Term :=
  Lang.foldlCmd guards.reverse leaf fun acc g => do
    match g with
    | .ifCond cond isThen =>
        let cT ← lowerCompExpr .propGuard cond
        Lang.runPQ (if isThen then `(if $cT then $acc else $fallback) else `(if $cT then $fallback else $acc))
    | .ifLet pat scrut isThen =>
        let sT ← lowerCompExpr .val scrut
        let pT ← liftMacroM (lowerQedPat (if isThen then pat else anonymizePat pat))
        Lang.runPQ (if isThen then `(match $sT:term with | $pT:term => $acc | _ => $fallback) else `(match $sT:term with | $pT:term => $fallback | _ => $acc))
    | .matchArm scruts allArmPats activeIdx =>
        let scrutTs ← Lang.mapCmd scruts (lowerCompExpr .val)
        let altGroups ← Lang.mapCmd allArmPats.zipIdx fun (ag, i) =>
          return (← Lang.mapCmd ag (Lang.mapCmd · fun p => liftMacroM (lowerQedPat (if i == activeIdx then p else anonymizePat p))), i == activeIdx)
        Lang.runPQ do
          let alts ← Lang.mapPQ altGroups fun (terms, isAct) => mkMatchAltFromAlts terms (if isAct then acc else fallback)
          `(match $[$scrutTs:term],* with $[$alts:matchAlt]*)

def mkStructBinder (f : FieldDecl) : CommandElabM (TSyntax ``Lean.Parser.Command.structExplicitBinder) :=
  if f.ty?.isNone && f.def?.isNone then throwErrorAt f.id s!"field `{f.id.getId}` needs a type or default value"
  else Lang.runPQ do match f.ty?, f.def? with
    | some ty, some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty := $d))
    | some ty, none   => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty))
    | _,       some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) := $d))
    | _,       _      => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : _))

def resolveBindTy (bd : FieldDecl) : CommandElabM Term := match bd.ty?, bd.def? with
  | some ty, _ => pure ty | none, some d => Lang.runPQ `(type_of% $d) | none, none => throwErrorAt bd.id s!"`bind {bd.id.getId}` needs a type or default"

def mkPropsBindersPure (spec : ComponentSpec) : PureQuotM (Array BinderStx) :=
  if spec.hasProps then do pure #[← `(bracketedBinder| (p : $(spec.propsId)))] else pure #[]

private def mkCtorPure (nm : Name) (bs : Array (Ident × Term) := #[]) : PureQuotM (TSyntax ``Lean.Parser.Command.ctor) :=
  let (ids, ts) := (bs.map (·.1), bs.map (·.2))
  `(Lean.Parser.Command.ctor| | $(mkIdent nm):ident $[($ids:ident : $ts)]*)

private def resolveStructFieldTypes (compName structKind : Name) (decls : Array FieldDecl) : CommandElabM (Array FieldDecl) := do
  let (ns, env) := (← getCurrNamespace, ← getEnv)
  Lang.mapCmd decls fun d => do
    let ty ← d.ty?.getDM do
      let some info := env.find? (ns ++ compName ++ structKind ++ d.id.getId) | throwErrorAt d.id s!"could not infer type of `{d.id.getId}`; add an explicit `: Type`"
      liftTermElabM <| Meta.forallTelescope info.type fun _ cod => PrettyPrinter.delab cod
    return { d with ty }

@[noinline] def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub)
    (formDrafts : Array FieldDecl) (resetForms : Array ResetFormSub) : CommandElabM ComponentSpec := do
  if spec.outTy?.isSome then
    let bdTys ← Lang.mapCmd spec.binds resolveBindTy
    let allDecEq ← liftTermElabM do
      for tyT in spec.events.flatMap (·.params.map (·.2)) ++ bdTys do
        let ty ← try Term.elabType tyT.raw catch _ => return false
        if !((← Meta.trySynthInstance (← Meta.mkAppM ``DecidableEq #[ty])) matches .some _) then return false
      return true
    Lang.elabPureCmd do
      let ctors := (← Lang.mapPQ spec.events fun ev => mkCtorPure ev.id.getId ev.params) ++
        (← Lang.mapPQ (spec.binds.zip bdTys) fun (bd, ty) => mkCtorPure (bindSetName bd.id.getId) #[(mkIdent `v, ty)])
      if allDecEq then `(command| inductive $(spec.id `Out) where $[$ctors:ctor]* deriving DecidableEq)
      else `(command| inductive $(spec.id `Out) where $[$ctors:ctor]*)
  let allProps := spec.props ++ spec.binds
  let extraSession : Array FieldDecl ←
    if spec.sessionField?.isNone && hoisted.any (·.info.hasSession) then
      Lang.runPQ do return #[{ id := mkIdent `_qed_session, ty? := some (← `(Option String)), def? := some (← `(none)) }]
    else pure #[]
  let allStates := spec.states ++ extraSession ++ formDrafts ++ hoisted.map fun h =>
    { id := h.fieldId, ty? := some (mkIdent (h.info.fullName ++ `State)), def? := some (mkIdent (h.info.fullName ++ `init)) }
  let (propBinders, stateBinders) := (← Lang.mapCmd allProps mkStructBinder, ← Lang.mapCmd allStates mkStructBinder)
  Lang.elabPureCmds do return #[
    ← `(command| structure $(spec.propsId) where $[$propBinders:structExplicitBinder]*),
    ← `(command| structure $(spec.stateId) where $[$stateBinders:structExplicitBinder]*)]
  let (resolvedProps, resolvedStates) := (← resolveStructFieldTypes spec.t.getId `Props allProps, ← resolveStructFieldTypes spec.t.getId `State allStates)
  let resolvedBinds := spec.binds.map fun bd => { bd with ty := (resolvedProps.find? (·.id.getId == bd.id.getId)).map (·.ty) |>.getD bd.ty }
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted, resetForms }

def mkCmdBatchPure (cmds : Array Term) : PureQuotM Term :=
  if cmds.isEmpty then `(Qed.Cmd.none) else if cmds.size == 1 then pure cmds[0]! else `(Qed.Cmd.batch [$[$cmds],*])

@[noinline] private def mkUpdateRetPure (spec : ComponentSpec) (sTerm : Term) (out? : Option Term := none) (cmds : Array Term := #[]) : PureQuotM Term := do
  let oVal ← match out? with | some o => `(some $o) | none => `(none)
  match spec.outTy?.isSome, spec.hasEffects with
  | false, false => pure sTerm | true, false => `(($sTerm, $oVal))
  | false, true  => `(($sTerm, $(← mkCmdBatchPure cmds))) | true, true => `(($sTerm, $oVal, $(← mkCmdBatchPure cmds)))

@[noinline] private def unpackRetTuplePure (hasOut hasEffects : Bool) (v : Ident) : PureQuotM (Term × Option Term × Option Term) := do
  let sE ← if !hasOut && !hasEffects then `($v:ident) else `(($v:ident).1)
  let oE? ← if !hasOut then pure none else some <$> (if hasEffects then `(($v:ident).2.1) else `(($v:ident).2))
  let cE? ← if !hasEffects then pure none else some <$> (if hasOut then `(($v:ident).2.2) else `(($v:ident).2))
  return (sE, oE?, cE?)

def mkHoistedPropsTermPure (h : HoistedSub) : PureQuotM Term :=
  let (fIds, fVals) := (h.dataProps.map (·.1), h.dataProps.map (·.2))
  `(({ $[$fIds:ident := $fVals],* } : $(mkIdent (h.info.fullName ++ `Props))))

def mkEnsuredExistentialWrapPure (ensConst : Name) (qaIds : Array Ident) (elemVar : Ident) : PureQuotM (Term × Term) := do
  return (← mkAppTermsPure (mkIdent ensConst) (qaIds.map (⟨·.raw⟩)),
          ← Lang.foldrPQ qaIds (← `(($elemVar:ident).ok)) fun qa acc => `(Exists.intro $qa $acc))

def appWithPropsPure (spec : ComponentSpec) (fn : Ident) (args : Array Term := #[]) : PureQuotM Term := do
  let pT ← `(p); mkAppTermsPure fn (if spec.hasProps then #[pT] ++ args else args)

@[noinline] private def resolveNestedFieldTy (spec : ComponentSpec) (a : SiteAssign) : CommandElabM Term := do
  let some d := (spec.states ++ spec.props).find? (·.id.getId == a.field) | throwError s!"component: internal unknown field `{a.field}`"
  if a.path.isEmpty then return d.ty
  let lamT ← Lang.runPQ do let xId := mkIdent `_qed_fld; `(fun ($xId:ident : $(d.ty)) => $(← Qed.Server.foldProjTerms d.ty.raw ⟨xId.raw⟩ a.path.toList))
  liftTermElabM do
    let e ← Term.elabTerm lamT none; Term.synthesizeSyntheticMVarsNoPostponing
    let .forallE _ _ body _ ← Meta.whnf (← Meta.inferType e) | throwError s!"could not infer field type for `{a.field}`"
    if body.hasLooseBVars then throwError s!"dependent field type is not supported in setter for `{a.field}`"
    PrettyPrinter.delab body

@[noinline] private def flushAssignsPure (sBase : Term) (assigns : Array SiteAssign) : PureQuotM Term := do
  if assigns.isEmpty then return sBase
  if assigns.all (·.path.isEmpty) then
    let (fIds, vals) := (assigns.map (mkIdent ·.field), ← Lang.mapPQ assigns (·.val?.getDM `(v)))
    return ← `({ $sBase with $[$fIds:ident := $vals],* })
  Lang.foldlPQ assigns sBase fun acc a => do
    let val ← a.val?.getDM `(v); let fId := mkIdent a.field
    if a.path.isEmpty then `({ $acc with $fId:ident := $val })
    else `({ $acc with $fId:ident := $(← buildRecordUpdateFromPure (← `(($acc).$fId:ident)) a.path (fun _ => pure val)) })

private def flushMutatedPure (sBase : Term) (mutated : Array Name) : PureQuotM Term := do
  if mutated.isEmpty then return sBase
  let fIds := mutated.toList.eraseDups.toArray.map mkIdent; let fVals : Array Term := fIds.map (⟨·.raw⟩)
  `({ $sBase with $[$fIds:ident := $fVals:term],* })

private abbrev CompileContFn := Term → Array Name → Option Term → Array Term → List Syntax → CommandElabM Term

@[noinline] private def continueFromSubWith (spec : ComponentSpec) (comp : CompileContFn) (brId : Ident) (subTerm : Term)
    (priorOut? : Option Term) (priorCmds : Array Term) (rest : List Syntax) : CommandElabM Term := do
  let (sNext, oNext, cOpt) ← Lang.runPQ (unpackRetTuplePure spec.outTy?.isSome spec.hasEffects brId)
  let cNext := match cOpt with | some c => priorCmds.push c | none => priorCmds
  let tail ← match oNext with
    | none => comp sNext #[] priorOut? cNext rest
    | some oExpr =>
        let oVal := mkIdent `_qedOut
        let (nBr, sBr) := (← comp sNext #[] priorOut? cNext rest, ← comp sNext #[] (some ⟨oVal.raw⟩) cNext rest)
        Lang.runPQ `(match $oExpr:term with | none => $nBr | some $oVal:ident => $sBr)
  Lang.runPQ do
    let rebound ← Lang.foldrPQ spec.fieldNames tail fun fn acc =>
      if rest.any (mentionsIdent · fn) then let fId := mkIdent fn; `(let $fId:ident := ($sNext).$fId:ident; $acc) else pure acc
    `(let $brId:ident := $subTerm; $rebound)

private def queryMethTable : List (String × Nat × Name × Bool) :=
  [("refetch", 0, `Qed.Cached.markRefetch, false), ("invalidate", 0, `Qed.Cached.invalidateAll, false),
   ("update", 1, `Qed.Cached.updateCurrent, true), ("set", 1, `Qed.Cached.setKey, true)]

@[noinline] private def compileExprStmt (spec : ComponentSpec) (comp : CompileContFn) (sBase : Term)
    (mutated : Array Name) (out? : Option Term) (cmds : Array Term) (s : Syntax) (rest : List Syntax) : CommandElabM Term := do
  let exprStx := s.getArg 0; let uExpr := unwrapParens1 exprStx
  if uExpr.getKind == ``qedCall && (uExpr.getArg 0).getKind == ``qedIdent then
    let cn := ((uExpr.getArg 0).getArg 0).getId.eraseMacroScopes
    if let some mfn := spec.mutFns.find? (·.id.getId.eraseMacroScopes == cn) then
      let argTs ← lowerPosCallArgs exprStx s!"{cn}(...)" (some mfn.params.size) (uExpr.getArg 2).getSepArgs
      let fnCall ← Lang.runPQ do appWithPropsPure spec (spec.id mfn.id.getId) (#[← flushMutatedPure sBase mutated] ++ argTs)
      if rest.isEmpty && out?.isNone && cmds.isEmpty then return fnCall
      return ← continueFromSubWith spec comp (mkIdent `_qedFn) fnCall out? cmds rest
  let bindCmd (pfx : String) (cmdT : Term) : CommandElabM Term := do
    let cmdId := mkIdent (Name.mkSimple s!"_{pfx}_{cmds.size}")
    let tail ← comp sBase mutated out? (cmds.push cmdId) rest
    Lang.runPQ `(let $cmdId:ident := $cmdT; $tail)
  let fallbackCmd : CommandElabM Term := withRef s do
    let e ← lowerCompExpr .val exprStx; bindCmd "cmd" (← Lang.runPQ `(($e : Qed.Cmd $(spec.msgId))))
  match matchIdentMethodCall? exprStx with
  | some (targetId, "emit", rawArgs) =>
      let tname := targetId.getId.eraseMacroScopes
      let some ev := spec.events.find? (·.id.getId.eraseMacroScopes == tname)
        | unless spec.outTy?.isSome do noEmitsErr s
          throwErrorAt targetId s!"unknown `event` `{tname}` in `{tname}.emit(...)`"
      if out?.isSome then throwErrorAt s "duplicate `.emit(...)` in action; an action emits at most one output"
      let argTs ← lowerPosCallArgs exprStx s!"{tname}.emit(...)" (some ev.params.size) rawArgs
      comp sBase mutated (some (← Lang.runPQ (mkAppTermsPure (mkIdentFrom targetId (spec.t.getId ++ `Out ++ ev.id.getId)) argTs))) cmds rest
  | some (targetId, "send", rawArgs) =>
      let tname := targetId.getId.eraseMacroScopes
      if let some sub := spec.subscriptions.find? (·.id.getId.eraseMacroScopes == tname) then
        unless sub.chInfo.hasSend do throwErrorAt s s!"channel `{sub.chInfo.ownerShort}.{sub.chInfo.channelName}` does not declare `on_send` / `send`"
        let argTs ← lowerPosCallArgs exprStx s!"{sub.id.getId}.send(...)" (some sub.chInfo.sendParamCount) rawArgs
        bindCmd "wsSendCmd" (← withRef s <| Lang.runPQ `(qedCheckChanSend% $(mkIdentFrom s sub.chInfo.fullName):ident [$[$argTs:term],*] $(Syntax.mkStrLit sub.id.getId.toString):str))
      else if let some po := spec.portOuts.find? (·.id.getId.eraseMacroScopes == tname) then
        bindCmd "portCmd" (← mkPortSendTerm spec.t.getId exprStx targetId po.id.getId rawArgs)
      else throwErrorAt targetId s!"unknown `subscribe` channel or outbound `port` `{tname}` in `{tname}.send(...)`"
  | some (targetId, qMeth, rawArgs) =>
      let tname := targetId.getId.eraseMacroScopes
      match spec.queries.find? (·.id.getId.eraseMacroScopes == tname), queryMethTable.find? (·.1 == qMeth) with
      | some q, some (_, arity, helperNm, withKey) =>
          let argTs ← lowerPosCallArgs exprStx (if arity == 0 then s!"{tname}.{qMeth}()" else s!"{tname}.{qMeth}(...)") (some arity) rawArgs
          let tail ← comp sBase (mutated.push q.id.getId) out? cmds rest
          let qId := mkIdentFrom targetId q.id.getId
          Lang.runPQ do
            if withKey then
              let qKeyCall ← appWithPropsPure spec (mkIdent (queryKeyFnName spec.t.getId q)) #[← flushMutatedPure sBase mutated]
              `(let $qId:ident := $(mkIdent helperNm) $qId:ident ($qKeyCall) ($(argTs[0]!)); $tail)
            else `(let $qId:ident := $(mkIdent helperNm) $qId:ident; $tail)
      | _, _ => fallbackCmd
  | _ =>
      if !spec.queries.isEmpty then
        if let some rawArgs := matchInvalidateCall? exprStx then
          if rawArgs.isEmpty then throwErrorAt exprStx "`invalidate(...)` requires at least one declared `query` name"
          let validQs := spec.queries.toList.map (·.id.getId.eraseMacroScopes.toString)
          let qTargets ← Lang.mapCmd rawArgs fun ra => do
            if ra.getKind != ``qedCallArgPos then throwErrorAt ra "`invalidate(...)` expects positional `query` names"
            let u := unwrapParens1 (ra.getArg 0)
            unless u.getKind == ``qedIdent do throwErrorAt ra "`invalidate(...)` arguments must be declared `query` names"
            let qRef : Ident := ⟨u.getArg 0⟩; let qNm := qRef.getId.eraseMacroScopes
            let some q := spec.queries.find? (·.id.getId.eraseMacroScopes == qNm)
              | throwErrorAt qRef s!"unknown `query` `{qNm}` in `invalidate(...)`{Qed.Diag.didYouMean qNm.toString validQs} (declared queries: {String.intercalate ", " validQs})"
            return (mkIdentFrom qRef q.id.getId, q.id.getId)
          let tail ← comp sBase (qTargets.foldl (fun m (_, qn) => m.push qn) mutated) out? cmds rest
          return ← Lang.runPQ do
            let invAllId := mkIdent `Qed.Cached.invalidateAll
            Lang.foldrPQ qTargets tail fun (qId, _) acc => `(let $qId:ident := $invAllId $qId:ident; $acc)
      fallbackCmd

@[noinline] private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (mutated : Array Name) (out? : Option Term) (cmds : Array Term) (stmts : List Syntax) : CommandElabM Term := do
  match stmts with
  | [] => Lang.runPQ do mkUpdateRetPure spec (← flushMutatedPure sBase mutated) out? cmds
  | s :: rest => withRef s do
      match s.getKind with
      | ``qedStmtPass   => compileStmts spec sBase mutated out? cmds rest
      | ``qedStmtReturn => Lang.runPQ do mkUpdateRetPure spec (← flushMutatedPure sBase mutated) out? cmds
      | ``qedStmtLet    => lowerLetStmt s (lowerCompExpr .val) (← compileStmts spec sBase mutated out? cmds rest)
      | ``qedStmtIf | ``qedStmtIfLet | ``qedStmtMatch =>
          let passTail := !rest.isEmpty && hasReturnStmt s; let sFlushed ← Lang.runPQ (flushMutatedPure sBase mutated)
          let branchTerm ← lowerControlFlowStmt s (lowerCompExpr .val) fun seq => compileStmts spec sFlushed #[] out? cmds (seq.toList ++ if passTail then rest else [])
          if passTail || rest.isEmpty then return branchTerm
          continueFromSubWith spec (compileStmts spec) (mkIdent `_qedBr) branchTerm none #[] rest
      | sk =>
          if let some (_, fname, path) := (if sk == ``qedStmtAssign then parseCompLVal? (s.getArg 0) else none).filter (fun (_, fn, _) => spec.bindNames.contains fn) then
            let op := atomStr (s.getArg 1)
            let leafT ← if op == "=" && isPlaceholder (s.getArg 2) then Lang.runPQ `(v) else do desugarAssignPath fname path op (← lowerCompExpr .val (s.getArg 2))
            if out?.isSome then throwErrorAt s s!"cannot assign `bind` field `{fname}` here: this action already emits an output event (an action emits at most one output)"
            let outE ← Lang.runPQ do
              let valTerm ← if path.isEmpty then pure leafT else buildRecordUpdateFromPure ⟨(mkIdent fname).raw⟩ path (fun _ => pure leafT)
              `($(spec.outCtor (bindSetName fname)) $valTerm)
            compileStmts spec sBase mutated (some outE) cmds rest
          else if let some (fname, wrap) ← lowerMutStmt? spec s true then
            wrap (← compileStmts spec sBase (mutated.push fname) out? cmds rest)
          else if sk == ``qedStmtExpr then
            compileExprStmt spec (compileStmts spec) sBase mutated out? cmds s rest
          else let sn := stxSnippet s; throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in component action"

@[noinline] private def mkGuardedBranchesPure (spec : ComponentSpec) (pfx : String) (paramTypeConsts : Array Name)
    (args : Array Term) (whenPat? : Option (Term × Term × Array Name)) (whenGuards : Array Term)
    (elseTerm : Term) (depMatch : Bool) (leafFn : Array Ident → PureQuotM Term) : PureQuotM Term := do
  let qaIds := (Array.range args.size).map fun i => mkIdent (Name.mkSimple s!"{pfx}_{i}")
  let mut body ← Lang.foldrPQ (qaIds.zip (paramTypeConsts.zip args)) (← leafFn qaIds) fun (qaId, pTy, arg) acc => `(let $qaId:ident : $(mkIdent pTy) := $arg; $acc)
  if !whenGuards.isEmpty then
    let g ← mkConjBody whenGuards
    body ← if depMatch then `(if $(mkIdent (Name.mkSimple s!"_h{pfx}When")):ident : $g then $body else $elseTerm) else `(if $g then $body else $elseTerm)
  let patIds := whenPat?.map (·.2.2) |>.getD #[]
  if let some (pat, scrut, _) := whenPat? then
    body ← if depMatch then `(match $(mkIdent (Name.mkSimple s!"_h{pfx}Pat")):ident : $scrut:term with | $pat:term => $body | _ => $elseTerm)
           else `(match $scrut:term with | $pat:term => $body | _ => $elseTerm)
  bindMentionedFieldsPure spec (fun g => (whenPat?.any fun (_, scrut, _) => mentionsIdent scrut.raw g) ||
    (!patIds.contains g && (args.any (mentionsIdent ·.raw g) || whenGuards.any (mentionsIdent ·.raw g)))) body

def mkRpcQueryBranchesPure (spec : ComponentSpec) (rspec : RpcQuerySpec) (leafFn : Array Ident → PureQuotM Term) : PureQuotM Term := do
  mkGuardedBranchesPure spec "_qa" rspec.mInfo.paramTypeConsts rspec.args rspec.whenPat? rspec.whenGuards (← `(none)) true leafFn
def mkSubBranchesPure (spec : ComponentSpec) (sub : SubDecl) (elseTerm : Term) (depMatch : Bool) (leafFn : Array Ident → PureQuotM Term) : PureQuotM Term :=
  mkGuardedBranchesPure spec "_sa" sub.chInfo.paramTypeConsts sub.args sub.whenPat? sub.whenGuards elseTerm depMatch leafFn

@[noinline] private def mkMsgInductiveCmds (spec : ComponentSpec) (sites : Array SetSite) : CommandElabM (Array CmdStx) := do
  let siteSpecs ← Lang.mapCmd sites fun site => do
    if !site.params.isEmpty then return (site.ctor, site.params)
    match site.assigns.find? (·.val?.isNone) with
    | some a => return (site.ctor, #[(mkIdent `v, ← resolveNestedFieldTy spec a)])
    | none   => return (site.ctor, #[])
  Lang.runPQ do
    let keyB := (mkIdent `key, ← `(String))
    let c0 ← Lang.mapPQ siteSpecs fun (c, ps) => mkCtorPure c ps
    let c1 ← match spec.route? with | some rd => do pure (c0.push (← mkCtorPure `_onRoute #[(mkIdent `_r, rd.ty)])) | none => pure c0
    let c2 ← if spec.hasAnySession then do pure (c1.push (← mkCtorPure `_onSession #[(mkIdent `_u, ← `(Option String))])) else pure c1
    let c3 ← if spec.outTy?.isSome then do pure (c2.push (← mkCtorPure `_emit #[(mkIdent `_o, spec.id `Out)])) else pure c2
    let c4 ← Lang.foldlPQ spec.collections c3 fun cs (colField, colChild) => return cs.push (← mkCtorPure colField.getId #[keyB, (mkIdent `msg, mkIdent (colChild.getId ++ `Msg))])
    let c5 ← Lang.foldlPQ spec.queries c4 fun cs q => return cs.push (← mkCtorPure q.ctorName #[keyB, (mkIdent `res, ← `(Resource $(q.msgTy)))])
    let c6 ← Lang.foldlPQ spec.subscriptions c5 fun cs sub => do
      let joinTy : Term ← if sub.chInfo.hasJoinSnapshot then pure (mkIdent sub.chInfo.joinTypeConst : Term) else `(Unit)
      return cs ++ #[← mkCtorPure (sub.ctor "Join") #[keyB, (mkIdent `snap, joinTy)], ← mkCtorPure (sub.ctor "Msg") #[keyB, (mkIdent `ev, sub.msgEvTy)],
                     ← mkCtorPure (sub.ctor "Status") #[keyB, (mkIdent `st, ← `(Qed.SocketStatus))]]
    let c7 ← Lang.foldlPQ spec.hoisted c6 fun cs h => return cs.push (← mkCtorPure h.ctorName #[(mkIdent `msg, mkIdent (h.info.fullName ++ `Msg))])
    let ctors ← Lang.foldlPQ spec.resetForms c7 fun cs rf => return cs.push (← mkCtorPure rf.ctorName)
    let indCmd ← if ctors.isEmpty then `(command| inductive $(spec.msgId)) else `(command| inductive $(spec.msgId) where $[$ctors:ctor]*)
    let portCmds ← Lang.mapPQ spec.portOuts fun po =>
      `(command| def $(spec.id po.id.getId) (x : $(po.ty)) : Cmd $(spec.msgId) := Cmd.port $(Syntax.mkStrLit po.id.getId.toString) (Json.render (ToJson.toJson x)))
    let outCmds := #[indCmd] ++ portCmds
    if spec.outTy?.isSome then return outCmds.push (← `(command| instance $(spec.id (`Out ++ `instCoeMsg)):ident : Coe $(spec.id `Out) $(spec.msgId) := ⟨$(spec.msgCtor `_emit)⟩))
    return outCmds

@[noinline] private def mkSiteUpdateArm (spec : ComponentSpec) (site : SetSite) : CommandElabM MatchAltStx := do
  let rhs0 ← match site.stmts? with
    | some stmts =>
        if stmts.all fun st => ![``qedStmtAssign, ``qedStmtExpr, ``qedStmtIf, ``qedStmtIfLet, ``qedStmtMatch, ``qedStmtPass].contains st.getKind then
          throwErrorAt stmts[0]! s!"action `{site.ctor}` has no state update or effect; add a state assignment, effect, or `pass`"
        compileStmts spec (← Lang.runPQ `(s)) #[] none #[] stmts.toList
    | none => Lang.runPQ do mkUpdateRetPure spec (← flushAssignsPure (← `(s)) site.assigns) site.send?
  Lang.runPQ do
    let (cFull, rhs) := (spec.msgCtor site.ctor, ← bindMentionedFieldsPure spec (mentionsIdent rhs0.raw) rhs0)
    if !site.params.isEmpty then let ids : Array Term := site.params.map (⟨·.1.raw⟩); `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
    else if site.assigns.any (·.val?.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
    else `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)

@[noinline] private def mkSubUpdateArms (spec : ComponentSpec) (sub : SubDecl) (unchanged : Term) : CommandElabM (Array MatchAltStx) := do
  let (subNm, wsKeyId) := (sub.id, mkIdent (subKeyFnName spec.t.getId sub))
  let (snapId, evId, stId) := (mkIdent `_wsnap, mkIdent `_wev, mkIdent `_wst)
  let (sBase, sWithSt, statusFb) ← Lang.runPQ do let sw ← `({ s with $subNm:ident := $stId:ident }); return (← `(s), sw, ← mkUpdateRetPure spec sw)
  let bindOpt (valExpr : Term) (b? : Option Syntax) (b : Term) : PureQuotM Term :=
    match b? with | some bStx => if bStx.isIdent then `(let $(⟨bStx⟩):ident := $valExpr; $b) else pure b | none => pure b
  let mkArm (ctorName : Name) (valId : Ident) (sB fallback : Term) (handler? : Option (Option Syntax × Array Syntax))
      (wrapBody : Option Syntax → Term → PureQuotM Term) (skipField? : Option Name := none) : CommandElabM MatchAltStx := do
    let compiled? ← handler?.mapM fun (b?, stmts) => return (b?, ← compileStmts spec sB #[] none #[] stmts.toList)
    Lang.runPQ do
      let body ← match compiled? with
        | some (b?, b) => wrapBody b? (← bindMentionedFieldsPure spec (fun g => skipField? != some g && mentionsIdent b.raw g) b)
        | none => pure fallback
      `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor ctorName):ident _wk $valId:ident => if $(← appWithPropsPure spec wsKeyId #[← `(s)]) == _wk then $body else $unchanged)
  return #[
    ← mkArm (sub.ctor "Join") snapId sBase unchanged sub.onJoin? (bindOpt snapId),
    ← mkArm (sub.ctor "Msg") evId sBase unchanged (sub.onMsg?.map fun (b, ss) => (some b, ss)) fun b? b => do
        if sub.hasMsgEnsured then bindOpt (← `(($evId:ident).val)) b? (← `(have _hWsEns := ($evId:ident).ok; $b)) else bindOpt evId b? b,
    ← mkArm (sub.ctor "Status") stId sWithSt statusFb (sub.onStatus?.map fun (b, ss) => (some b, ss))
        (skipField? := some subNm.getId) fun b? b => do bindOpt stId b? (← `(let $(mkIdent subNm.getId):ident := $stId:ident; $b))]

@[noinline] private def mkOwnUpdateArms (spec : ComponentSpec) (sites : Array SetSite) (unchanged : Term) : CommandElabM (Array MatchAltStx) := do
  let arms0 ← Lang.mapCmd sites (mkSiteUpdateArm spec)
  let arms1 ← match spec.route? with
    | none => pure arms0
    | some rd => do
        let rVal := mkIdent `_r; let sWithR ← Lang.runPQ `({ s with $(rd.field):ident := $rVal:ident })
        let compiledAlts ← Lang.mapCmd rd.alts fun alt => return (← liftMacroM (lowerCasePatAlts (alt.getArg 1)), ← compileStmts spec sWithR #[] none #[] (suiteStmts (alt.getArg 3)).toList)
        pure (arms0.push (← Lang.runPQ do
          let rhs0 ← if compiledAlts.isEmpty then mkUpdateRetPure spec sWithR else do
            let alts ← Lang.mapPQ compiledAlts fun (ps, b) => mkMatchAltFromAlts ps b
            `(match $rVal:ident with $[$alts:matchAlt]*)
          let rhs ← bindMentionedFieldsPure spec (fun g => g != rd.field.getId && mentionsIdent rhs0.raw g) rhs0
          `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onRoute):ident $rVal:ident => let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs)))
  let extra ← Lang.runPQ do
    let a0 ← if spec.hasAnySession then do pure #[← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onSession):ident _u => $(← mkUpdateRetPure spec (← `($(spec.id `setSession) s _u))))] else pure #[]
    let a1 ← if spec.outTy?.isSome then do pure (a0.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_emit):ident _o => $(← mkUpdateRetPure spec (← `(s)) (some (← `(_o))))))) else pure a0
    let a2 ← Lang.foldlPQ spec.collections a1 fun xs (colField, colChild) => do
      let nm := mkIdent colField.getId
      return xs.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor colField.getId) k msg => $(← mkUpdateRetPure spec (← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })))))
    Lang.foldlPQ spec.queries a2 fun xs q => do
      let keyBound ← appWithPropsPure spec (mkIdent (queryKeyFnName spec.t.getId q)) #[← `(s)]
      let plainRes ← if q.rpc.hasMsgEnsured then `($(mkIdent `Qed.Resource.stripEnsured) _qr) else `(_qr)
      return xs.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor q.ctorName):ident _qk _qr => $(← mkUpdateRetPure spec (← `({ s with $(q.id):ident := (s.$(q.id):ident).putRev _qk $plainRes $keyBound })))))
  Lang.foldlCmd spec.subscriptions (arms1 ++ extra) fun acc sub => return acc ++ (← mkSubUpdateArms spec sub unchanged)

private def mkHoistedGuardedPure (spec : ComponentSpec) (h : HoistedSub) (stateVar fallback : Term)
    (keyTerm? : Option Term) (alwaysCheckKey : Bool) (mkBody : Option Term → PureQuotM Term) : PureQuotM Term := do
  if !h.hasLifecycle then
    let p? ← if h.info.hasProps then some <$> mkHoistedPropsTermPure h else pure none
    return ← mkBody p?
  let core ← if h.info.hasProps then
      let cpVar := mkIdent `_cp
      `(match $(← appWithPropsPure spec (mkIdent (subPropsDefName spec.t.getId h)) #[stateVar]):term with | Option.none => $fallback | Option.some $cpVar:ident => $(← mkBody (some ⟨cpVar.raw⟩)))
    else mkBody none
  if alwaysCheckKey || !h.info.hasProps then
    let keyE ← keyTerm?.getDM (appWithPropsPure spec (mkIdent (subKeyDefName spec.t.getId h)) #[stateVar])
    `(if ($keyE).isEmpty then $fallback else $core)
  else pure core

@[noinline] private def mkHoistedSubArmPure (spec : ComponentSpec) (stepOwnId : Ident) (unchanged : Term) (h : HoistedSub) : PureQuotM MatchAltStx := do
  let (subCtor, subF, cmVar, crVar, s1Var) := (spec.msgCtor h.ctorName, h.fieldId, mkIdent `_cm, mkIdent `_cr, mkIdent `_s1)
  let (cUpd, slotPfxLit) := (mkIdent (h.info.fullName ++ `update), Syntax.mkStrLit s!"{h.fieldId.getId}.")
  let armBody ← mkHoistedGuardedPure spec h (← `(s)) unchanged none false fun propsArg? => do
    let cCall ← match propsArg? with | some pt => `($cUpd $pt s.$subF:ident $cmVar:ident) | none => `($cUpd s.$subF:ident $cmVar:ident)
    let (csExpr, coExpr?, rawC?) ← unpackRetTuplePure h.info.hasOut h.info.hasEffects crVar
    let ccExpr? ← rawC?.mapM fun rc => `(Cmd.mapScoped $slotPfxLit $subCtor $rc)
    let noOutRet ← mkUpdateRetPure spec ⟨s1Var.raw⟩ none (match ccExpr? with | some c => #[c] | none => #[])
    let afterSub : Term ← match coExpr? with
      | some coE =>
          if h.outArms.isEmpty then pure noOutRet else do
            let (outVar, pmVar, srVar) := (mkIdent `_co, mkIdent `_pm, mkIdent `_sr)
            let pmOpt ← mkOutMatchTermPure h.info.fullName (h.info.events.size + h.info.bindNames.size) h.outArms outVar
            let stepCall ← appWithPropsPure spec stepOwnId #[s1Var, pmVar]
            let mergedStep ← match ccExpr?, spec.hasEffects with
              | some cc, true =>
                  let (srS, srO?, srC?) ← unpackRetTuplePure spec.outTy?.isSome true srVar
                  `(let $srVar:ident := $stepCall; $(← mkUpdateRetPure spec srS srO? #[cc, srC?.get!]))
              | _, _ => pure stepCall
            `(match $coE:term with | none => $noOutRet | some $outVar:ident => match $pmOpt:term with | none => $noOutRet | some $pmVar:ident => $mergedStep)
      | none => pure noOutRet
    `(let $crVar:ident := $cCall; let $s1Var:ident := { s with $subF:ident := $csExpr }; $afterSub)
  `(Lean.Parser.Term.matchAltExpr| | $subCtor $cmVar:ident => $(← bindMentionedFieldsPure spec (mentionsIdent armBody.raw) armBody))

@[noinline] def mkHoistedStartCmdExprPure (spec : ComponentSpec) (h : HoistedSub) (stateVar : Term) (keyTerm? : Option Term)
    (fallback : Term) (wrapScoped : Term → PureQuotM Term) : PureQuotM Term := do
  let (cStart, subCtor, pfxLit) := (mkIdent (h.info.fullName ++ `startCmd), spec.msgCtor h.ctorName, Syntax.mkStrLit s!"{h.fieldId.getId}.")
  mkHoistedGuardedPure spec h stateVar fallback keyTerm? true fun propsArg? => do
    let call ← match propsArg? with | some pt => `($cStart $pt) | none => `($cStart)
    wrapScoped (← `(Cmd.mapScoped $pfxLit $subCtor $call))

@[noinline] private def mkReconcileHoistedCmdPure (spec : ComponentSpec) (pBinders : Array BinderStx) (retTy : Term) : PureQuotM CmdStx := do
  let (sOldV, resV, sNextId) := (mkIdent `_sOld, mkIdent `_res, mkIdent `_sNext)
  let (sCur0, outCur?, cmdCur?) ← unpackRetTuplePure spec.outTy?.isSome spec.hasEffects resV
  let (subFieldIds, subFieldVals, startSpecs) ← Lang.foldlPQ (spec.hoisted.filter HoistedSub.hasLifecycle) (#[], #[], #[]) fun (fIds, fVals, sSpecs) h => do
    let (keyCallOld, keyCallNew) := (← appWithPropsPure spec (mkIdent (subKeyDefName spec.t.getId h)) #[⟨sOldV.raw⟩], ← appWithPropsPure spec (mkIdent (subKeyDefName spec.t.getId h)) #[⟨sNextId.raw⟩])
    let childInit := mkIdent (h.info.fullName ++ `init)
    let childResetVal : Term ← match h.info.hasSession, spec.effectiveSessionField? with
      | true, some sfId => `($(mkIdent (h.info.fullName ++ `setSession)) $childInit ($sNextId:ident).$sfId:ident)
      | _, _ => pure childInit
    let subF := h.fieldId
    if spec.hasEffects && h.info.hasStart then
      let (kOldId, kNewId) := (mkIdent (Name.mkSimple s!"_kOld_{subF.getId}"), mkIdent (Name.mkSimple s!"_kNew_{subF.getId}"))
      let subVal ← `(if $kOldId == $kNewId then ($sNextId:ident).$subF:ident else $childResetVal)
      return (fIds.push subF, fVals.push subVal, sSpecs.push (kOldId, keyCallOld, kNewId, keyCallNew, h))
    else
      let subVal ← `(if $keyCallOld == $keyCallNew then ($sNextId:ident).$subF:ident else $childResetVal)
      return (fIds.push subF, fVals.push subVal, sSpecs)
  let sOutExpr ← `({ $sNextId:ident with $[$subFieldIds:ident := $subFieldVals:term],* })
  let cId := mkIdent `_rc
  let rcExpr? := if spec.hasEffects then some (if startSpecs.isEmpty then cmdCur?.get! else ⟨cId.raw⟩) else none
  let body0 ← match outCur?, rcExpr? with
    | none, none => pure sOutExpr | some o, none => `(($sOutExpr, $o)) | none, some c => `(($sOutExpr, $c)) | some o, some c => `(($sOutExpr, $o, $c))
  let body ← if startSpecs.isEmpty then pure body0 else do
    let b1 ← Lang.foldrPQ startSpecs body0 fun (kOldId, _, kNewId, _, h) acc => do
      let nextCmd ← mkHoistedStartCmdExprPure spec h ⟨sNextId.raw⟩ (some ⟨kNewId.raw⟩) ⟨cId.raw⟩ fun c => `(Qed.Cmd.batch [$cId:ident, $c])
      `(let $cId:ident := if $kOldId == $kNewId then $cId:ident else $nextCmd; $acc)
    let b2 ← `(let $cId:ident := $(cmdCur?.get!); $b1)
    Lang.foldrPQ startSpecs b2 fun (kOldId, keyCallOld, kNewId, keyCallNew, _) acc =>
      `(let $kOldId:ident := $keyCallOld; let $kNewId:ident := $keyCallNew; $acc)
  `(command| set_option linter.unusedVariables false in def $(spec.id `_reconcileHoisted) $[$pBinders:bracketedBinder]* ($sOldV:ident : $(spec.stateId)) ($resV:ident : $retTy) : $retTy := let $sNextId:ident := $sCur0; $body)

@[noinline] private def mkQueryHelperCmdsPure (spec : ComponentSpec) (pBinders : Array BinderStx) (q : QueryDecl) : PureQuotM (Array CmdStx) := do
  let rspec := q.rpc; let reqTupleTy ← buildProdTypePure (rspec.mInfo.paramTypeConsts.map fun n => (mkIdent n : Term))
  let (paramsId, keyId, fetchId) := (mkIdent (queryParamsFnName spec.t.getId q), mkIdent (queryKeyFnName spec.t.getId q), mkIdent (queryFetchFnName spec.t.getId q))
  let paramsBody ← mkRpcQueryBranchesPure spec rspec fun qaIds => do `(some $(← buildTupleValPure (qaIds.map (⟨·.raw⟩))))
  let paramsCall ← appWithPropsPure spec paramsId #[← `(s)]
  let fetchBody ← mkRpcQueryBranchesPure spec rspec fun qaIds => do
    let cbTerm : Term ← match rspec.hasMsgEnsured, rspec.mInfo.ensPredConst with
      | true, some ensConst =>
          let qeId := mkIdent `_qe; let (ensApp, exPrf) ← mkEnsuredExistentialWrapPure ensConst qaIds qeId
          `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => $(spec.msgCtor q.ctorName) _qk (_qr.map fun $qeId => ⟨($qeId:ident).val, $exPrf⟩))
      | _, _ => `($(spec.msgCtor q.ctorName) _qk)
    let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
    `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $(mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName):ident $(mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)):ident [$[$qaTerms:term],*] $cbTerm)))
  return #[
    ← `(command| set_option linter.unusedVariables false in def $paramsId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Option $reqTupleTy := $paramsBody),
    ← `(command| set_option linter.unusedVariables false in def $keyId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $(mkIdent `Qed.rpcQueryKey) $paramsCall),
    ← `(command| set_option linter.unusedVariables false in def $fetchId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) (_qk : String) : Option (Qed.Cmd $(spec.msgId)) := $fetchBody)]

@[noinline] private def mkHoistedLifecycleCmds (spec : ComponentSpec) (pBinders : Array BinderStx) (h : HoistedSub) : CommandElabM (Array CmdStx) := do
  if !h.hasLifecycle then return #[]
  let (keyLeaf, emptyStr, propsPair?) ← Lang.runPQ do
    let kl ← match h.keyExpr? with | some k => `("k:" ++ toString ($k)) | none => `("1")
    let pp? ← if h.info.hasProps then do pure (some (← `(Option.some $(← mkHoistedPropsTermPure h)), ← `(Option.none))) else pure none
    return (kl, ← `(""), pp?)
  let keyRaw ← wrapViewGuards h.guards keyLeaf emptyStr
  let propsRaw? ← propsPair?.mapM fun (pl, pn) => wrapViewGuards h.guards pl pn
  Lang.runPQ do
    let keyBody ← bindMentionedFieldsPure spec (mentionsIdent keyRaw.raw) keyRaw
    let cs := #[← `(command| set_option linter.unusedVariables false in def $(mkIdent (subKeyDefName spec.t.getId h)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $keyBody)]
    match propsRaw? with
    | none => return cs
    | some pr =>
        let propsBody ← bindMentionedFieldsPure spec (mentionsIdent pr.raw) pr
        return cs.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subPropsDefName spec.t.getId h)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Option $(mkIdent (h.info.fullName ++ `Props)) := $propsBody))

@[noinline] def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) : CommandElabM (Array CmdStx) := do
  Lang.foldlCmd spec.queries () fun _ q =>
    if q.rpc.hasMsgEnsured && q.rpc.mInfo.ensPredConst.isNone then throwErrorAt q.rpc.rpcRef "internal: missing server `ensures` predicate in `query`" else pure ()
  let msgCmds ← mkMsgInductiveCmds spec sites
  let (pBinders, retTy, unchanged, helperCmds) ← Lang.runPQ do
    let pBinders ← mkPropsBindersPure spec
    let retTy : Term ← match spec.outTy?, spec.hasEffects with
      | none, false => `($(spec.stateId)) | some o, false => `($(spec.stateId) × Option $o)
      | none, true  => `($(spec.stateId) × Cmd $(spec.msgId)) | some o, true => `($(spec.stateId) × Option $o × Cmd $(spec.msgId))
    let c0 : Array CmdStx ← match spec.effectiveSessionField? with
      | none => pure #[]
      | some sfId =>
          let sessChildren := spec.hoisted.filter (·.info.hasSession)
          let fIds := #[sfId] ++ sessChildren.map (·.fieldId)
          let fVals := #[← `(_u)] ++ (← Lang.mapPQ sessChildren fun h => `($(mkIdent (h.info.fullName ++ `setSession)) s.$(h.fieldId):ident _u))
          pure #[← `(command| @[reducible] def $(spec.id `setSession) (s : $(spec.stateId)) (_u : Option String) : $(spec.stateId) := { s with $[$fIds:ident := $fVals],* })]
    let c1 ← Lang.foldlPQ spec.queries c0 fun cs q => return cs ++ (← mkQueryHelperCmdsPure spec pBinders q)
    let c2 ← Lang.foldlPQ spec.subscriptions c1 fun cs sub => do
      let keyBody ← mkSubBranchesPure spec sub (← `("")) false fun qaIds => mkAppTermsPure (mkIdentFrom sub.chanRef sub.chInfo.keyHelperConst) (qaIds.map (⟨·.raw⟩))
      return cs.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subKeyFnName spec.t.getId sub)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $keyBody))
    return (pBinders, retTy, ← mkUpdateRetPure spec (← `(s)), c2)
  let sIdT ← Lang.runPQ `(s)
  let mutFnCmds ← Lang.mapCmd spec.mutFns fun f => do
    let rawBody ← compileStmts spec sIdT #[] none #[] f.stmts.toList
    Lang.runPQ do
      let fnBinders ← Lang.mapPQ f.params fun (pid, pty) => `(bracketedBinder| ($pid:ident : $pty))
      `(command| set_option linter.unusedVariables false in def $(spec.id f.id.getId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) $[$fnBinders:bracketedBinder]* : $retTy := $(← bindMentionedFieldsPure spec (mentionsIdent rawBody.raw) rawBody))
  let hoistCmds ← Lang.foldlCmd spec.hoisted #[] fun cs h => return cs ++ (← mkHoistedLifecycleCmds spec pBinders h)
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let tailCmds ← Lang.runPQ do
    let hasLifecycleHoisted := spec.hoisted.any HoistedSub.hasLifecycle
    let cs : Array CmdStx ← if hasLifecycleHoisted then do pure #[← mkReconcileHoistedCmdPure spec pBinders retTy] else pure #[]
    let mkUpdDef (fnId : Ident) (arms : Array MatchAltStx) (reconcile : Bool := false) : PureQuotM CmdStx := do
      let core ← if arms.isEmpty then `(nomatch m) else `(match m with $[$arms:matchAlt]*)
      let wrapped ← if reconcile && hasLifecycleHoisted then appWithPropsPure spec (spec.id `_reconcileHoisted) #[← `(s), core] else pure core
      `(command| def $fnId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy := fun m => $wrapped)
    if spec.hoisted.isEmpty && spec.resetForms.isEmpty then return cs.push (← mkUpdDef spec.updateId ownArms)
    let stepOwnId := spec.id `stepOwn
    let subNoops ← Lang.mapPQ spec.hoisted fun h => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor h.ctorName) _ => $unchanged)
    let rfNoops ← Lang.mapPQ spec.resetForms fun rf => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $unchanged)
    let fa0 ← Lang.mapPQ spec.hoisted (mkHoistedSubArmPure spec stepOwnId unchanged)
    let fa1 ← Lang.foldlPQ spec.resetForms fa0 fun fullArms rf => do
      let (df, fvId) := (rf.draftField, mkIdent `_fv)
      let ab ← `(match ($(rf.parseCall) s.$df:ident) with
        | some $fvId:ident => let _s1 := if $(rf.resetCond) then { s with $df:ident := $(mkIdent (`_root_ ++ rf.schemaName ++ `Draft ++ `empty)) } else s; $(← appWithPropsPure spec stepOwnId #[← `(_s1), ← `(($(rf.handler) $fvId))])
        | none => $unchanged)
      return fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $(← bindMentionedFieldsPure spec (mentionsIdent ab.raw) ab)))
    let fullArms ← if ownArms.isEmpty then pure fa1 else do pure (fa1.push (← `(Lean.Parser.Term.matchAltExpr| | _m => $(← appWithPropsPure spec stepOwnId #[← `(s), ← `(_m)]))))
    return cs ++ #[← mkUpdDef stepOwnId (ownArms ++ subNoops ++ rfNoops), ← mkUpdDef spec.updateId fullArms (reconcile := true)]
  return msgCmds ++ helperCmds ++ mutFnCmds ++ hoistCmds ++ tailCmds

@[noinline] def mkViewCmdsPure (spec : ComponentSpec) (body' : Term) (msgAndUpdateCmds : Array CmdStx) : PureQuotM (Array CmdStx) := do
  let (renderId, pBinders) := (spec.id `_qed_render, ← mkPropsBindersPure spec)
  let viewBody ← bindMentionedFieldsPure spec (mentionsIdent body'.raw) body'
  if spec.hasSlotsOrKids then
    let (pMsg, wrapId) := (mkIdent `_msg, mkIdent `_wrap)
    let sb0 ← Lang.mapPQ spec.slots fun sl => do `(bracketedBinder| ($(sl.id) : Html $pMsg := $(← sl.def?.getDM `(Qed.Html.empty))))
    let slotBinders ← if spec.hasChildren then do pure (sb0.push (← `(bracketedBinder| ($(mkIdent `children) : List (Html $pMsg) := [])))) else pure sb0
    return msgAndUpdateCmds ++ #[
      ← `(command| def $renderId {$pMsg : Type} $[$pBinders:bracketedBinder]* ($wrapId : $(spec.msgId) → $pMsg) (s : $(spec.stateId)) $[$slotBinders:bracketedBinder]* : Html $pMsg := $viewBody),
      ← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $(← appWithPropsPure spec renderId #[← `(id), ← `(s)]))]
  let rendered ← appWithPropsPure spec spec.viewId #[← `(s)]
  let cmds0 := msgAndUpdateCmds ++ #[
    ← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $viewBody),
    ← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]* (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route)]
  if !spec.outTy?.isNone || spec.hasEffects then return cmds0
  let compId := spec.id `_qed_toComponent; let compExpr ← appWithPropsPure spec compId
  let cmds1 := cmds0 ++ #[
    ← (match spec.keyF? with
      | some kf => `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId)) (route : String → $(spec.msgId) → parentMsg) (s : $(spec.stateId)) (k : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)) : Html parentMsg := ($rendered).map (route k))
      | none    => `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId)) (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route)),
    ← `(command| $[$(spec.doc?):docComment]? def $compId $[$pBinders:bracketedBinder]* : Component $(spec.stateId) $(spec.msgId) := { update := $(← appWithPropsPure spec spec.updateId), view := $(← appWithPropsPure spec spec.viewId) })]
  let some kf := spec.keyF? | return cmds1
  let keyOfId := spec.id `keyOf
  return cmds1 ++ #[
    ← `(command| def $keyOfId (s : $(spec.stateId)) : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)),
    ← `(command| def $(spec.id `updateKeyed) $[$pBinders:bracketedBinder]* (rows : Array $(spec.stateId)) (k : String) (msg : $(spec.msgId)) : Array $(spec.stateId) := Component.updateKeyed $compExpr $keyOfId rows k msg)]

end CompElab
end Qed
