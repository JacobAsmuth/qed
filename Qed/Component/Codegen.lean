import Qed.Component.Rewrite
import Qed.Runtime.Cmd
import Qed.Invariant.State

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Shared Structure, Binder & Codegen Helpers -/

def subKeyDefName   (tId : Name) (h : HoistedSub) : Name := tId ++ Name.mkSimple s!"_subKey_{h.fieldId.getId}"
def subPropsDefName (tId : Name) (h : HoistedSub) : Name := tId ++ Name.mkSimple s!"_subProps_{h.fieldId.getId}"

@[noinline]
def mkPureCompFnCmds (spec : ComponentSpec) (fieldTys : Array (Name × Term)) : CommandElabM (Array CmdStx) := do
  let mut cmds : Array CmdStx := #[]
  for f in spec.pureFns do
    let some retTy := f.retTy? | continue
    let capBinders : Array BinderStx ← f.capturedFields.mapM fun cn => do
      let some (_, ty) := fieldTys.find? (·.1 == cn)
        | throwErrorAt f.id s!"internal: missing resolved type for field `{cn}` in `fn {f.id.getId}`"
      `(bracketedBinder| ($(mkIdent cn):ident : $ty))
    let pBinders : Array BinderStx ← f.params.mapM fun (pid, pty) => `(bracketedBinder| ($pid:ident : $pty))
    let bodyT ← lowerPureFnStmts s!"fn {spec.t.getId}.{f.id.getId}" f.stmts.toList (lowerCompExpr .val) (lowerCompExpr .propGuard)
    cmds := cmds.push (← `(command|
      set_option linter.unusedVariables false in
      def $(spec.id f.id.getId) $[$capBinders:bracketedBinder]* $[$pBinders:bracketedBinder]* : $retTy := $bodyT))
  return cmds

private partial def anonymizePat (stx : Syntax) : Syntax :=
  let mapSep (n : Syntax) := Syntax.node n.getHeadInfo n.getKind (n.getArgs.map fun a => if a.isAtom then a else anonymizePat a)
  let mapInner (i : Nat) := let inner := stx.getArg i; setStxArg stx i (setStxArg inner 1 (mapSep (inner.getArg 1)))
  let k := stx.getKind
  if k == ``qedPatIdent then
    if (stx.getArg 1).getNumArgs == 3 then mapInner 1
    else
      let vn := (stx.getArg 0).getId.eraseMacroScopes; let s := vn.toString
      if vn.isAtomic && !["_", "none", "true", "false"].contains s && !s.front.isUpper then
        Syntax.node stx.getHeadInfo ``qedPatWild #[Syntax.atom stx.getHeadInfo "_"]
      else stx
  else if k == ``qedPatDot && (stx.getArg 2).getNumArgs == 3 then mapInner 2
  else if k == ``qedPatParen then setStxArg stx 1 (mapSep (stx.getArg 1))
  else stx

@[noinline]
def wrapViewGuards (guards : Array ViewGuard) (leaf fallback : Term) : CommandElabM Term :=
  guards.foldrM (init := leaf) fun g acc => do
    match g with
    | .ifCond cond isThen =>
        let cT ← lowerCompExpr .propGuard cond
        if isThen then `(if $cT then $acc else $fallback) else `(if $cT then $fallback else $acc)
    | .ifLet pat scrut isThen =>
        let (pT, sT) := (← liftMacroM (lowerQedPat pat), ← lowerCompExpr .val scrut)
        if isThen then `(match $sT:term with | $pT:term => $acc | _ => $fallback)
        else `(match $sT:term with | $(← liftMacroM (lowerQedPat (anonymizePat pat))):term => $fallback | _ => $acc)
    | .matchArm scruts allArmPats activeIdx =>
        let scrutTs ← scruts.mapM (lowerCompExpr .val)
        let alts ← allArmPats.zipIdx.mapM fun (altGroups, i) => do
          let altTerms ← altGroups.mapM (·.mapM fun p => liftMacroM (lowerQedPat (if i == activeIdx then p else anonymizePat p)))
          let rhs := if i == activeIdx then acc else fallback
          mkMatchAltFromAlts altTerms rhs
        `(match $[$scrutTs:term],* with $[$alts:matchAlt]*)

def mkStructBinder (f : FieldDecl) : CommandElabM (TSyntax ``Lean.Parser.Command.structExplicitBinder) :=
  match f.ty?, f.def? with
  | some ty, some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty := $d))
  | some ty, none   => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty))
  | none,    some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) := $d))
  | none,    none   => throwErrorAt f.id s!"field `{f.id.getId}` needs a type or default value"

def resolveBindTy (bd : FieldDecl) : CommandElabM Term := match bd.ty?, bd.def? with
  | some ty, _ => pure ty | none, some d => `(type_of% $d) | none, none => throwErrorAt bd.id s!"`bind {bd.id.getId}` needs a type or default"

def mkPropsBinders (spec : ComponentSpec) : CommandElabM (Array BinderStx) :=
  if spec.hasProps then do pure #[← `(bracketedBinder| (p : $(spec.propsId)))] else pure #[]

private def mkCtor (nm : Name) (bs : Array (Ident × Term) := #[]) : CommandElabM (TSyntax ``Lean.Parser.Command.ctor) :=
  let (ids, ts) := (bs.map (·.1), bs.map (·.2))
  `(Lean.Parser.Command.ctor| | $(mkIdent nm):ident $[($ids:ident : $ts)]*)

private def resolveStructFieldTypes (compName structKind : Name) (decls : Array FieldDecl) : CommandElabM (Array FieldDecl) := do
  let (ns, env) := (← getCurrNamespace, ← getEnv)
  decls.mapM fun d => do
    let ty ← d.ty?.getDM do
      let some info := env.find? (ns ++ compName ++ structKind ++ d.id.getId) | throwErrorAt d.id s!"could not infer type of `{d.id.getId}`; add an explicit `: Type`"
      liftTermElabM <| Meta.forallTelescope info.type fun _ cod => PrettyPrinter.delab cod
    return { d with ty }

def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub)
    (formDrafts : Array FieldDecl) (resetForms : Array ResetFormSub) : CommandElabM ComponentSpec := do
  if spec.outTy?.isSome then
    let evCtors ← spec.events.mapM fun ev => mkCtor ev.id.getId ev.params
    let bdCtors ← spec.binds.mapM fun bd => do mkCtor (bindSetName bd.id.getId) #[(mkIdent `v, ← resolveBindTy bd)]
    elabCommand (← `(command| inductive $(spec.id `Out) where $[$(evCtors ++ bdCtors):ctor]*))
  let allProps := spec.props ++ spec.binds
  let extraSession : Array FieldDecl ←
    if spec.sessionField?.isNone && hoisted.any (·.info.hasSession) then
      pure #[{ id := mkIdent `_qed_session, ty? := some (← `(Option String)), def? := some (← `(none)) }]
    else pure #[]
  let allStates := spec.states ++ extraSession ++ formDrafts ++ hoisted.map fun h =>
    { id := h.fieldId, ty? := some (mkIdent (h.info.fullName ++ `State)), def? := some (mkIdent (h.info.fullName ++ `init)) }
  elabCommand (← `(command| structure $(spec.propsId) where $[$(← allProps.mapM mkStructBinder):structExplicitBinder]*))
  elabCommand (← `(command| structure $(spec.stateId) where $[$(← allStates.mapM mkStructBinder):structExplicitBinder]*))
  let (resolvedProps, resolvedStates) := (← resolveStructFieldTypes spec.t.getId `Props allProps, ← resolveStructFieldTypes spec.t.getId `State allStates)
  let resolvedBinds := spec.binds.map fun bd => { bd with ty := (resolvedProps.find? (·.id.getId == bd.id.getId)).map (·.ty) |>.getD bd.ty }
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted, resetForms }

def mkCmdBatch (cmds : Array Term) : CommandElabM Term :=
  if cmds.isEmpty then `(Qed.Cmd.none) else if cmds.size == 1 then pure cmds[0]! else `(Qed.Cmd.batch [$[$cmds],*])

private def mkUpdateRet (spec : ComponentSpec) (sTerm : Term) (out? : Option Term := none) (cmds : Array Term := #[]) : CommandElabM Term := do
  let oVal ← match out? with | some o => `(some $o) | none => `(none)
  match spec.outTy?.isSome, spec.hasEffects with
  | false, false => pure sTerm | true, false => `(($sTerm, $oVal))
  | false, true  => `(($sTerm, $(← mkCmdBatch cmds))) | true, true => `(($sTerm, $oVal, $(← mkCmdBatch cmds)))

private def unpackRetTuple (hasOut hasEffects : Bool) (v : Ident) : CommandElabM (Term × Option Term × Option Term) := do
  let sE ← if !hasOut && !hasEffects then `($v:ident) else `(($v:ident).1)
  let oE? ← if !hasOut then pure none else some <$> (if hasEffects then `(($v:ident).2.1) else `(($v:ident).2))
  let cE? ← if !hasEffects then pure none else some <$> (if hasOut then `(($v:ident).2.2) else `(($v:ident).2))
  return (sE, oE?, cE?)

def mkHoistedPropsTerm (h : HoistedSub) : CommandElabM Term := do
  let (fIds, fVals) := (h.dataProps.map (·.1), h.dataProps.map (·.2))
  `(({ $[$fIds:ident := $fVals],* } : $(mkIdent (h.info.fullName ++ `Props))))

def queryParamsFnName (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qParams_{q.id.getId}"
def queryKeyFnName    (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qKey_{q.id.getId}"
def queryFetchFnName  (tId : Name) (q : QueryDecl) : Name := tId ++ Name.mkSimple s!"_qFetch_{q.id.getId}"

def mkEnsuredExistentialWrap (ensConst : Name) (qaIds : Array Ident) (elemVar : Ident) : CommandElabM (Term × Term) := do
  return (← Qed.Lang.mkAppTerms (mkIdent ensConst) (qaIds.map (⟨·.raw⟩)),
          ← qaIds.foldrM (init := ← `(($elemVar:ident).ok)) fun qa acc => `(Exists.intro $qa $acc))

@[noinline]
private def resolveNestedFieldTy (spec : ComponentSpec) (a : SiteAssign) : CommandElabM Term := do
  let some d := (spec.states ++ spec.props).find? (·.id.getId == a.field)
    | throwError s!"component: internal unknown field `{a.field}`"
  if a.path.isEmpty then return d.ty
  let xId := mkIdent `_qed_fld
  let projT ← Qed.Server.foldProjTerms d.ty.raw ⟨xId.raw⟩ a.path.toList
  let lamT ← `(fun ($xId:ident : $(d.ty)) => $projT)
  liftTermElabM do
    let e ← Term.elabTerm lamT none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fnTy ← Meta.whnf (← Meta.inferType e)
    let .forallE _ _ body _ := fnTy | throwError s!"could not infer field type for `{a.field}`"
    if body.hasLooseBVars then throwError s!"dependent field type is not supported in setter for `{a.field}`"
    PrettyPrinter.delab body

private def flushAssigns (sBase : Term) (assigns : Array SiteAssign) : CommandElabM Term := do
  if assigns.isEmpty then return sBase
  if assigns.all (·.path.isEmpty) then
    let (fIds, vals) := (assigns.map (mkIdent ·.field), ← assigns.mapM (·.val?.getDM `(v)))
    return ← `({ $sBase with $[$fIds:ident := $vals],* })
  assigns.foldlM (init := sBase) fun acc a => do
    let val ← a.val?.getDM `(v)
    let fId := mkIdent a.field
    if a.path.isEmpty then `({ $acc with $fId:ident := $val })
    else
      let upd ← buildRecordUpdateFrom (← `(($acc).$fId:ident)) a.path (fun _ => pure val)
      `({ $acc with $fId:ident := $upd })

private def flushMutated (sBase : Term) (mutated : Array Name) : CommandElabM Term := do
  if mutated.isEmpty then return sBase
  let fIds := mutated.toList.eraseDups.toArray.map mkIdent; let fVals : Array Term := fIds.map (⟨·.raw⟩)
  `({ $sBase with $[$fIds:ident := $fVals:term],* })

def appWithProps (spec : ComponentSpec) (fn : Ident) (args : Array Term := #[]) : CommandElabM Term := do
  let pT ← `(p); Qed.Lang.mkAppTerms fn (if spec.hasProps then #[pT] ++ args else args)

private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (mutated : Array Name) (out? : Option Term) (cmds : Array Term) (stmts : List Syntax) : CommandElabM Term := do
  let continueFromSub (brId : Ident) (subTerm : Term) (priorOut? : Option Term) (priorCmds : Array Term) (rest : List Syntax) : CommandElabM Term := do
    let (sNext, oNext, cOpt) ← unpackRetTuple spec.outTy?.isSome spec.hasEffects brId
    let cNext := match cOpt with | some c => priorCmds.push c | none => priorCmds
    let tail ← match oNext with
      | none => compileStmts spec sNext #[] priorOut? cNext rest
      | some oExpr =>
          let oVal := mkIdent `_qedOut
          `(match $oExpr:term with | none => $(← compileStmts spec sNext #[] priorOut? cNext rest) | some $oVal:ident => $(← compileStmts spec sNext #[] (some ⟨oVal.raw⟩) cNext rest))
    let mut rebound := tail
    for fn in spec.fieldNames.reverse do
      if rest.any (mentionsIdent · fn) then let fId := mkIdent fn; rebound ← `(let $fId:ident := ($sNext).$fId:ident; $rebound)
    `(let $brId:ident := $subTerm; $rebound)
  match stmts with
  | [] => mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
  | s :: rest => withRef s do
      let sk := s.getKind
      if sk == ``qedStmtPass then compileStmts spec sBase mutated out? cmds rest
      else if sk == ``qedStmtReturn then mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
      else if sk == ``qedStmtLet then lowerLetStmt s (lowerCompExpr .val) (← compileStmts spec sBase mutated out? cmds rest)
      else if let some (_, fname, path) := (if sk == ``qedStmtAssign then parseCompLVal? (s.getArg 0) else none).filter (fun (_, fn, _) => spec.bindNames.contains fn) then
        let op := atomStr (s.getArg 1)
        let leafT ← if op == "=" && isPlaceholder (s.getArg 2) then `(v) else desugarAssignPath fname path op (← lowerCompExpr .val (s.getArg 2))
        let valTerm ← if path.isEmpty then pure leafT else buildRecordUpdateFrom ⟨(mkIdent fname).raw⟩ path (fun _ => pure leafT)
        if out?.isSome then throwErrorAt s s!"cannot assign `bind` field `{fname}` here: this action already emits an output event (an action emits at most one output)"
        compileStmts spec sBase mutated (some (← `($(spec.outCtor (bindSetName fname)) $valTerm))) cmds rest
      else if let some (fname, wrap) ← lowerMutStmt? spec s true then
        wrap (← compileStmts spec sBase (mutated.push fname) out? cmds rest)
      else if sk == ``qedStmtExpr then
        let exprStx := s.getArg 0
        let uExpr := unwrapParens1 exprStx
        if uExpr.getKind == ``qedCall && (uExpr.getArg 0).getKind == ``qedIdent then
          let cn := ((uExpr.getArg 0).getArg 0).getId.eraseMacroScopes
          if let some mfn := spec.mutFns.find? (·.id.getId.eraseMacroScopes == cn) then
            let argTs ← lowerPosCallArgs exprStx s!"{cn}(...)" (some mfn.params.size) (uExpr.getArg 2).getSepArgs
            let sFlushed ← flushMutated sBase mutated
            let fnCall ← appWithProps spec (spec.id mfn.id.getId) (#[sFlushed] ++ argTs)
            if rest.isEmpty && out?.isNone && cmds.isEmpty then return fnCall
            return ← continueFromSub (mkIdent `_qedFn) fnCall out? cmds rest
        let bindCmd (pfx : String) (cmdT : Term) : CommandElabM Term := do
          let cmdId := mkIdent (Name.mkSimple s!"_{pfx}_{cmds.size}")
          `(let $cmdId:ident := $cmdT; $(← compileStmts spec sBase mutated out? (cmds.push cmdId) rest))
        match matchIdentMethodCall? exprStx with
        | some (targetId, "emit", rawArgs) =>
            let tname := targetId.getId.eraseMacroScopes
            let some ev := spec.events.find? (·.id.getId.eraseMacroScopes == tname)
              | unless spec.outTy?.isSome do noEmitsErr s
                throwErrorAt targetId s!"unknown `event` `{tname}` in `{tname}.emit(...)`"
            if out?.isSome then throwErrorAt s "duplicate `.emit(...)` in action; an action emits at most one output"
            let argTs ← lowerPosCallArgs exprStx s!"{tname}.emit(...)" (some ev.params.size) rawArgs
            compileStmts spec sBase mutated (some (← Qed.Lang.mkAppTerms (mkIdentFrom targetId (spec.t.getId ++ `Out ++ ev.id.getId)) argTs)) cmds rest
        | some (targetId, "send", rawArgs) =>
            let tname := targetId.getId.eraseMacroScopes
            if let some sub := spec.subscriptions.find? (·.id.getId.eraseMacroScopes == tname) then
              unless sub.chInfo.hasSend do throwErrorAt s s!"channel `{sub.chInfo.ownerShort}.{sub.chInfo.channelName}` does not declare `on_send` / `send`"
              let argTs ← lowerPosCallArgs exprStx s!"{sub.id.getId}.send(...)" (some sub.chInfo.sendParamCount) rawArgs
              bindCmd "wsSendCmd" (← withRef s `(qedCheckChanSend% $(mkIdentFrom s sub.chInfo.fullName):ident [$[$argTs:term],*] $(Syntax.mkStrLit sub.id.getId.toString):str))
            else if let some po := spec.portOuts.find? (·.id.getId.eraseMacroScopes == tname) then
              bindCmd "portCmd" (← mkPortSendTerm spec.t.getId exprStx targetId po.id.getId rawArgs)
            else throwErrorAt targetId s!"unknown `subscribe` channel or outbound `port` `{tname}` in `{tname}.send(...)`"
        | some (targetId, qMeth, rawArgs) =>
            let tname := targetId.getId.eraseMacroScopes
            if let some q := spec.queries.find? (·.id.getId.eraseMacroScopes == tname) then
              let qId := mkIdentFrom targetId q.id.getId
              let sFlushed ← flushMutated sBase mutated
              let qKeyCall ← appWithProps spec (mkIdent (queryKeyFnName spec.t.getId q)) #[sFlushed]
              match qMeth with
              | "refetch" | "invalidate" =>
                  let _ ← lowerPosCallArgs exprStx s!"{tname}.{qMeth}()" (some 0) rawArgs
                  let fnId := mkIdent (if qMeth == "refetch" then `Qed.Cached.markRefetch else `Qed.Cached.invalidateAll)
                  `(let $qId:ident := $fnId $qId:ident; $(← compileStmts spec sBase (mutated.push q.id.getId) out? cmds rest))
              | "update" | "set" =>
                  let argTs ← lowerPosCallArgs exprStx s!"{tname}.{qMeth}(...)" (some 1) rawArgs
                  let fnId := mkIdent (if qMeth == "update" then `Qed.Cached.updateCurrent else `Qed.Cached.setKey)
                  `(let $qId:ident := $fnId $qId:ident ($qKeyCall) ($(argTs[0]!)); $(← compileStmts spec sBase (mutated.push q.id.getId) out? cmds rest))
              | _ => withRef s <| bindCmd "cmd" (← `(($(← lowerCompExpr .val exprStx) : Qed.Cmd $(spec.msgId))))
            else withRef s <| bindCmd "cmd" (← `(($(← lowerCompExpr .val exprStx) : Qed.Cmd $(spec.msgId))))
        | _ =>
            if !spec.queries.isEmpty then
              if let some rawArgs := matchInvalidateCall? exprStx then
                if rawArgs.isEmpty then throwErrorAt exprStx "`invalidate(...)` requires at least one declared `query` name"
                let validQs := spec.queries.toList.map (·.id.getId.eraseMacroScopes.toString)
                let mut qTargets : Array (Ident × Name) := #[]
                for ra in rawArgs do
                  if ra.getKind != ``qedCallArgPos then throwErrorAt ra "`invalidate(...)` expects positional `query` names"
                  let u := unwrapParens1 (ra.getArg 0)
                  unless u.getKind == ``qedIdent do throwErrorAt ra "`invalidate(...)` arguments must be declared `query` names"
                  let qRef : Ident := ⟨u.getArg 0⟩; let qNm := qRef.getId.eraseMacroScopes
                  let some q := spec.queries.find? (·.id.getId.eraseMacroScopes == qNm)
                    | throwErrorAt qRef s!"unknown `query` `{qNm}` in `invalidate(...)`{Qed.Diag.didYouMean qNm.toString validQs} (declared queries: {String.intercalate ", " validQs})"
                  qTargets := qTargets.push (mkIdentFrom qRef q.id.getId, q.id.getId)
                let mut mut' := mutated
                for (_, qn) in qTargets do mut' := mut'.push qn
                let tail ← compileStmts spec sBase mut' out? cmds rest
                let invAllId := mkIdent `Qed.Cached.invalidateAll
                return ← qTargets.foldrM (init := tail) fun (qId, _) acc => `(let $qId:ident := $invAllId $qId:ident; $acc)
            withRef s <| bindCmd "cmd" (← `(($(← lowerCompExpr .val exprStx) : Qed.Cmd $(spec.msgId))))
      else if sk == ``qedStmtIf || sk == ``qedStmtIfLet || sk == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt s; let sFlushed ← flushMutated sBase mutated
        let branchTerm ← lowerControlFlowStmt s (lowerCompExpr .val) fun seq => compileStmts spec sFlushed #[] out? cmds (seq.toList ++ if passTail then rest else [])
        if passTail || rest.isEmpty then return branchTerm
        continueFromSub (mkIdent `_qedBr) branchTerm none #[] rest
      else let sn := stxSnippet s; throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in component action"

private def mkGuardedBranches (spec : ComponentSpec) (pfx : String) (paramTypeConsts : Array Name)
    (args : Array Term) (whenPat? : Option (Term × Term × Array Name)) (whenGuards : Array Term)
    (elseTerm : Term) (depMatch : Bool) (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term := do
  let qaIds := (Array.range args.size).map fun i => mkIdent (Name.mkSimple s!"{pfx}_{i}")
  let mut body ← (qaIds.zip (paramTypeConsts.zip args)).foldrM (init := ← leafFn qaIds) fun (qaId, pTy, arg) acc => `(let $qaId:ident : $(mkIdent pTy) := $arg; $acc)
  if !whenGuards.isEmpty then
    let g ← mkConjBody whenGuards
    body ← if depMatch then `(if $(mkIdent (Name.mkSimple s!"_h{pfx}When")):ident : $g then $body else $elseTerm) else `(if $g then $body else $elseTerm)
  let patIds := whenPat?.map (·.2.2) |>.getD #[]
  if let some (pat, scrut, _) := whenPat? then
    body ← if depMatch then `(match $(mkIdent (Name.mkSimple s!"_h{pfx}Pat")):ident : $scrut:term with | $pat:term => $body | _ => $elseTerm)
           else `(match $scrut:term with | $pat:term => $body | _ => $elseTerm)
  bindMentionedFields spec (fun g => (whenPat?.any fun (_, scrut, _) => mentionsIdent scrut.raw g) ||
    (!patIds.contains g && (args.any (mentionsIdent ·.raw g) || whenGuards.any (mentionsIdent ·.raw g)))) body

def mkRpcQueryBranches (spec : ComponentSpec) (rspec : RpcQuerySpec) (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term := do
  mkGuardedBranches spec "_qa" rspec.mInfo.paramTypeConsts rspec.args rspec.whenPat? rspec.whenGuards (← `(none)) true leafFn
def mkRpcQueryParamsBody (spec : ComponentSpec) (rspec : RpcQuerySpec) : CommandElabM Term :=
  mkRpcQueryBranches spec rspec fun qaIds => do `(some $(← Qed.Lang.buildTupleVal (qaIds.map (⟨·.raw⟩))))
def mkSubBranches (spec : ComponentSpec) (sub : SubDecl) (elseTerm : Term) (depMatch : Bool) (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term :=
  mkGuardedBranches spec "_sa" sub.chInfo.paramTypeConsts sub.args sub.whenPat? sub.whenGuards elseTerm depMatch leafFn
def subKeyFnName (tId : Name) (sub : SubDecl) : Name := tId ++ Name.mkSimple s!"_wsKey_{sub.id.getId}"

private def mkMsgInductiveCmds (spec : ComponentSpec) (sites : Array SetSite) : CommandElabM (Array CmdStx) := do
  let mut ctors ← sites.mapM fun site => do
    if !site.params.isEmpty then mkCtor site.ctor site.params
    else match site.assigns.find? (·.val?.isNone) with
    | some a => mkCtor site.ctor #[(mkIdent `v, ← resolveNestedFieldTy spec a)]
    | none => mkCtor site.ctor
  if let some rd := spec.route? then ctors := ctors.push (← mkCtor `_onRoute #[(mkIdent `_r, rd.ty)])
  if spec.hasAnySession then ctors := ctors.push (← mkCtor `_onSession #[(mkIdent `_u, ← `(Option String))])
  if spec.outTy?.isSome then ctors := ctors.push (← mkCtor `_emit #[(mkIdent `_o, spec.id `Out)])
  let keyB := (mkIdent `key, ← `(String))
  for (colField, colChild) in spec.collections do ctors := ctors.push (← mkCtor colField.getId #[keyB, (mkIdent `msg, mkIdent (colChild.getId ++ `Msg))])
  for q in spec.queries do ctors := ctors.push (← mkCtor q.ctorName #[keyB, (mkIdent `res, ← `(Resource $(q.msgTy)))])
  for sub in spec.subscriptions do
    let joinTy : Term ← if sub.chInfo.hasJoinSnapshot then pure (mkIdent sub.chInfo.joinTypeConst : Term) else `(Unit)
    ctors := ctors ++ #[← mkCtor (sub.ctor "Join") #[keyB, (mkIdent `snap, joinTy)], ← mkCtor (sub.ctor "Msg") #[keyB, (mkIdent `ev, sub.msgEvTy)],
                        ← mkCtor (sub.ctor "Status") #[keyB, (mkIdent `st, ← `(Qed.SocketStatus))]]
  for h in spec.hoisted do ctors := ctors.push (← mkCtor h.ctorName #[(mkIdent `msg, mkIdent (h.info.fullName ++ `Msg))])
  for rf in spec.resetForms do ctors := ctors.push (← mkCtor rf.ctorName)
  let mut outCmds : Array CmdStx := #[← if ctors.isEmpty then `(command| inductive $(spec.msgId)) else `(command| inductive $(spec.msgId) where $[$ctors:ctor]*)]
  for po in spec.portOuts do
    outCmds := outCmds.push (← `(command| def $(spec.id po.id.getId) (x : $(po.ty)) : Cmd $(spec.msgId) := Cmd.port $(Syntax.mkStrLit po.id.getId.toString) (Json.render (ToJson.toJson x))))
  if spec.outTy?.isSome then outCmds := outCmds.push (← `(command| instance $(spec.id (`Out ++ `instCoeMsg)):ident : Coe $(spec.id `Out) $(spec.msgId) := ⟨$(spec.msgCtor `_emit)⟩))
  return outCmds

private def mkSiteUpdateArm (spec : ComponentSpec) (site : SetSite) : CommandElabM MatchAltStx := do
  let cFull := spec.msgCtor site.ctor
  let mut rhs ← (match site.stmts? with
    | some stmts => do
        if stmts.all fun st => ![``qedStmtAssign, ``qedStmtExpr, ``qedStmtIf, ``qedStmtIfLet, ``qedStmtMatch, ``qedStmtPass].contains st.getKind then
          throwErrorAt stmts[0]! s!"action `{site.ctor}` has no state update or effect; add a state assignment, effect, or `pass`"
        compileStmts spec (← `(s)) #[] none #[] stmts.toList
    | none => do mkUpdateRet spec (← flushAssigns (← `(s)) site.assigns) site.send?)
  rhs ← bindMentionedFields spec (mentionsIdent rhs.raw) rhs
  if !site.params.isEmpty then let ids : Array Term := site.params.map (⟨·.1.raw⟩); `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
  else if site.assigns.any (·.val?.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
  else `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)

private def mkSubUpdateArms (spec : ComponentSpec) (sub : SubDecl) (unchanged : Term) : CommandElabM (Array MatchAltStx) := do
  let (subNm, wsKeyId) := (sub.id, mkIdent (subKeyFnName spec.t.getId sub))
  let bindOpt (valExpr : Term) (b? : Option Syntax) (b : Term) : CommandElabM Term :=
    match b? with | some bStx => if bStx.isIdent then `(let $(⟨bStx⟩):ident := $valExpr; $b) else pure b | none => pure b
  let mkArm (ctorName : Name) (valId : Ident) (sBase fallback : Term) (handler? : Option (Option Syntax × Array Syntax))
      (wrapBody : Option Syntax → Term → CommandElabM Term) (skipField? : Option Name := none) := do
    let body ← match handler? with
      | some (b?, stmts) => let b ← compileStmts spec sBase #[] none #[] stmts.toList
                            wrapBody b? (← bindMentionedFields spec (fun g => skipField? != some g && mentionsIdent b.raw g) b)
      | none => pure fallback
    let wsKeyCall ← appWithProps spec wsKeyId #[← `(s)]
    `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor ctorName):ident _wk $valId:ident => if $wsKeyCall == _wk then $body else $unchanged)
  let (sBase, snapId, evId, stId) := (← `(s), mkIdent `_wsnap, mkIdent `_wev, mkIdent `_wst)
  let sWithSt ← `({ s with $subNm:ident := $stId:ident })
  pure #[
    ← mkArm (sub.ctor "Join") snapId sBase unchanged sub.onJoin? (bindOpt snapId),
    ← mkArm (sub.ctor "Msg") evId sBase unchanged (sub.onMsg?.map fun (b, ss) => (some b, ss)) fun b? b => do
        if sub.hasMsgEnsured then bindOpt (← `(($evId:ident).val)) b? (← `(have _hWsEns := ($evId:ident).ok; $b)) else bindOpt evId b? b,
    ← mkArm (sub.ctor "Status") stId sWithSt (← mkUpdateRet spec sWithSt) (sub.onStatus?.map fun (b, ss) => (some b, ss))
        (skipField? := some subNm.getId) fun b? b => do bindOpt stId b? (← `(let $(mkIdent subNm.getId):ident := $stId:ident; $b)) ]

private def mkOwnUpdateArms (spec : ComponentSpec) (sites : Array SetSite) (unchanged : Term) : CommandElabM (Array MatchAltStx) := do
  let mut arms ← sites.mapM (mkSiteUpdateArm spec)
  if let some rd := spec.route? then
    let rVal := mkIdent `_r; let sWithR ← `({ s with $(rd.field):ident := $rVal:ident })
    let mut rhs ← (if rd.alts.isEmpty then mkUpdateRet spec sWithR else do
      let alts ← rd.alts.mapM fun alt => do
        mkMatchAltFromAlts (← liftMacroM (lowerCasePatAlts (alt.getArg 1))) (← compileStmts spec sWithR #[] none #[] (suiteStmts (alt.getArg 3)).toList)
      `(match $rVal:ident with $[$alts:matchAlt]*))
    rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onRoute):ident $rVal:ident => let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs))
  if spec.hasAnySession then
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onSession):ident _u => $(← mkUpdateRet spec (← `($(spec.id `setSession) s _u)))))
  if spec.outTy?.isSome then
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_emit):ident _o => $(← mkUpdateRet spec (← `(s)) (some (← `(_o))))))
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor colField.getId) k msg => $(← mkUpdateRet spec (← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })))))
  for q in spec.queries do
    let keyBound ← appWithProps spec (mkIdent (queryKeyFnName spec.t.getId q)) #[← `(s)]
    let plainRes ← if q.rpc.hasMsgEnsured then `($(mkIdent `Qed.Resource.stripEnsured) _qr) else `(_qr)
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor q.ctorName):ident _qk _qr => $(← mkUpdateRet spec (← `({ s with $(q.id):ident := (s.$(q.id):ident).putRev _qk $plainRes $keyBound })))))
  for sub in spec.subscriptions do arms := arms ++ (← mkSubUpdateArms spec sub unchanged)
  return arms

private def mkHoistedSubArm (spec : ComponentSpec) (stepOwnId : Ident) (unchanged : Term) (h : HoistedSub) : CommandElabM MatchAltStx := do
  let (subCtor, subF, cmVar, crVar, s1Var) := (spec.msgCtor h.ctorName, h.fieldId, mkIdent `_cm, mkIdent `_cr, mkIdent `_s1)
  let cUpd := mkIdent (h.info.fullName ++ `update)
  let slotPfxLit := Syntax.mkStrLit s!"{h.fieldId.getId}."
  let buildDispatch (propsArg? : Option Term) : CommandElabM Term := do
    let cCall ← match propsArg? with | some pt => `($cUpd $pt s.$subF:ident $cmVar:ident) | none => `($cUpd s.$subF:ident $cmVar:ident)
    let (csExpr, coExpr?, rawC?) ← unpackRetTuple h.info.hasOut h.info.hasEffects crVar
    let ccExpr? ← rawC?.mapM fun rc => `(Cmd.mapScoped $slotPfxLit $subCtor $rc)
    let noOutRet ← mkUpdateRet spec ⟨s1Var.raw⟩ none (match ccExpr? with | some c => #[c] | none => #[])
    let afterSub : Term ← match coExpr? with
      | some coE =>
          if h.outArms.isEmpty then pure noOutRet else do
            let (outVar, pmVar, srVar) := (mkIdent `_co, mkIdent `_pm, mkIdent `_sr)
            let pmOpt ← liftMacroM <| mkOutMatchTerm h.info.fullName (h.info.events.size + h.info.bindNames.size) h.outArms outVar
            let stepCall ← appWithProps spec stepOwnId #[s1Var, pmVar]
            let mergedStep ← match ccExpr?, spec.hasEffects with
              | some cc, true =>
                  let (srS, srO?, srC?) ← unpackRetTuple spec.outTy?.isSome true srVar
                  `(let $srVar:ident := $stepCall; $(← mkUpdateRet spec srS srO? #[cc, srC?.get!]))
              | _, _ => pure stepCall
            `(match $coE:term with | none => $noOutRet | some $outVar:ident => match $pmOpt:term with | none => $noOutRet | some $pmVar:ident => $mergedStep)
      | none => pure noOutRet
    `(let $crVar:ident := $cCall; let $s1Var:ident := { s with $subF:ident := $csExpr }; $afterSub)
  let armBody : Term ←
    if h.hasLifecycle then
      if h.info.hasProps then
        let cpVar := mkIdent `_cp
        let propsCall ← appWithProps spec (mkIdent (subPropsDefName spec.t.getId h)) #[← `(s)]
        let disp ← buildDispatch (some ⟨cpVar.raw⟩)
        `(match $propsCall:term with | Option.none => $unchanged | Option.some $cpVar:ident => $disp)
      else do
        let keyCall ← appWithProps spec (mkIdent (subKeyDefName spec.t.getId h)) #[← `(s)]
        let disp ← buildDispatch none
        `(if ($keyCall).isEmpty then $unchanged else $disp)
    else do
      let pArg? ← if h.info.hasProps then some <$> mkHoistedPropsTerm h else pure none
      buildDispatch pArg?
  `(Lean.Parser.Term.matchAltExpr| | $subCtor $cmVar:ident => $(← bindMentionedFields spec (mentionsIdent armBody.raw) armBody))

@[noinline]
private def mkReconcileHoistedCmd (spec : ComponentSpec) (pBinders : Array BinderStx) (retTy : Term) : CommandElabM CmdStx := do
  let lifecycleSubs := spec.hoisted.filter HoistedSub.hasLifecycle
  let (sOldV, resV) := (mkIdent `_sOld, mkIdent `_res)
  let (sCur0, outCur?, cmdCur?) ← unpackRetTuple spec.outTy?.isSome spec.hasEffects resV
  let sId := mkIdent `_rs; let cId := mkIdent `_rc
  let mut stepBody ← mkUpdateRet spec ⟨sId.raw⟩ outCur? (if spec.hasEffects then #[⟨cId.raw⟩] else #[])
  for h in lifecycleSubs.reverse do
    let keyCallOld ← appWithProps spec (mkIdent (subKeyDefName spec.t.getId h)) #[⟨sOldV.raw⟩]
    let keyCallNew ← appWithProps spec (mkIdent (subKeyDefName spec.t.getId h)) #[⟨sId.raw⟩]
    let childInit := mkIdent (h.info.fullName ++ `init)
    let childResetVal : Term ← match h.info.hasSession, spec.effectiveSessionField? with
      | true, some sfId => `($(mkIdent (h.info.fullName ++ `setSession)) $childInit ($sId:ident).$sfId:ident)
      | _, _ => pure childInit
    let resetState ← `({ $sId:ident with $(h.fieldId):ident := $childResetVal })
    let nextCmd : Term ← if !spec.hasEffects then pure ⟨cId.raw⟩
      else if !h.info.hasStart then pure ⟨cId.raw⟩
      else do
        let cStart := mkIdent (h.info.fullName ++ `startCmd)
        let subCtor := spec.msgCtor h.ctorName
        let pfxLit := Syntax.mkStrLit s!"{h.fieldId.getId}."
        let startCmdExpr ← if h.info.hasProps then
            let propsCall ← appWithProps spec (mkIdent (subPropsDefName spec.t.getId h)) #[resetState]
            `(match $propsCall:term with | Option.none => $cId:ident | Option.some _cp => Qed.Cmd.batch [$cId:ident, Cmd.mapScoped $pfxLit $subCtor ($cStart _cp)])
          else `(Qed.Cmd.batch [$cId:ident, Cmd.mapScoped $pfxLit $subCtor $cStart])
        `(if (_kNew).isEmpty then $cId:ident else $startCmdExpr)
    let updatePair ← if spec.hasEffects then
        `(let $cId:ident := if _kOld == _kNew then $cId:ident else $nextCmd; let $sId:ident := if _kOld == _kNew then $sId:ident else $resetState; $stepBody)
      else
        `(let $sId:ident := if _kOld == _kNew then $sId:ident else $resetState; $stepBody)
    stepBody ← `(let _kOld := $keyCallOld; let _kNew := $keyCallNew; $updatePair)
  let fullBody ← if spec.hasEffects then `(let $sId:ident := $sCur0; let $cId:ident := $(cmdCur?.get!); $stepBody) else `(let $sId:ident := $sCur0; $stepBody)
  `(command| set_option linter.unusedVariables false in def $(spec.id `_reconcileHoisted) $[$pBinders:bracketedBinder]* ($sOldV:ident : $(spec.stateId)) ($resV:ident : $retTy) : $retTy := $fullBody)

def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) : CommandElabM (Array CmdStx) := do
  let mut outCmds ← mkMsgInductiveCmds spec sites
  let pBinders ← mkPropsBinders spec
  if let some sfId := spec.effectiveSessionField? then
    let sessChildren := spec.hoisted.filter (·.info.hasSession)
    let fIds : Array Ident := #[sfId] ++ sessChildren.map (·.fieldId)
    let fVals : Array Term := #[← `(_u)] ++ (← sessChildren.mapM fun h => `($(mkIdent (h.info.fullName ++ `setSession)) s.$(h.fieldId):ident _u))
    outCmds := outCmds.push (← `(command| @[reducible] def $(spec.id `setSession) (s : $(spec.stateId)) (_u : Option String) : $(spec.stateId) := { s with $[$fIds:ident := $fVals],* }))
  for q in spec.queries do
    let rspec := q.rpc
    let reqTupleTy ← Qed.Lang.buildProdType (rspec.mInfo.paramTypeConsts.map fun n => (mkIdent n : Term))
    let paramsId := mkIdent (queryParamsFnName spec.t.getId q)
    let keyId := mkIdent (queryKeyFnName spec.t.getId q)
    let fetchId := mkIdent (queryFetchFnName spec.t.getId q)
    let paramsBody ← mkRpcQueryParamsBody spec rspec
    let paramsCall ← appWithProps spec paramsId #[← `(s)]
    let fetchBody ← mkRpcQueryBranches spec rspec fun qaIds => do
      let cbTerm : Term ← if !rspec.hasMsgEnsured then `($(spec.msgCtor q.ctorName) _qk) else do
        let some ensConst := rspec.mInfo.ensPredConst | throwErrorAt rspec.rpcRef "internal: missing server `ensures` predicate in `query`"
        let qeId := mkIdent `_qe; let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds qeId
        `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => $(spec.msgCtor q.ctorName) _qk (_qr.map fun $qeId => ⟨($qeId:ident).val, $exPrf⟩))
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $(mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName):ident $(mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)):ident [$[$qaTerms:term],*] $cbTerm)))
    outCmds := outCmds ++ #[
      ← `(command| set_option linter.unusedVariables false in def $paramsId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Option $reqTupleTy := $paramsBody),
      ← `(command| set_option linter.unusedVariables false in def $keyId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $(mkIdent `Qed.rpcQueryKey) $paramsCall),
      ← `(command| set_option linter.unusedVariables false in def $fetchId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) (_qk : String) : Option (Qed.Cmd $(spec.msgId)) := $fetchBody)
    ]
  for sub in spec.subscriptions do
    let keyBody ← mkSubBranches spec sub (← `("")) false fun qaIds => Qed.Lang.mkAppTerms (mkIdentFrom sub.chanRef sub.chInfo.keyHelperConst) (qaIds.map (⟨·.raw⟩))
    outCmds := outCmds.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subKeyFnName spec.t.getId sub)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $keyBody))
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none, false => `($(spec.stateId)) | some o, false => `($(spec.stateId) × Option $o)
    | none, true  => `($(spec.stateId) × Cmd $(spec.msgId)) | some o, true => `($(spec.stateId) × Option $o × Cmd $(spec.msgId))
  for f in spec.mutFns do
    let fnBinders : Array BinderStx ← f.params.mapM fun (pid, pty) => `(bracketedBinder| ($pid:ident : $pty))
    let rawBody ← compileStmts spec (← `(s)) #[] none #[] f.stmts.toList
    let body ← bindMentionedFields spec (mentionsIdent rawBody.raw) rawBody
    outCmds := outCmds.push (← `(command| set_option linter.unusedVariables false in def $(spec.id f.id.getId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) $[$fnBinders:bracketedBinder]* : $retTy := $body))
  for h in spec.hoisted do
    if h.hasLifecycle then
      let keyLeaf ← match h.keyExpr? with | some k => `("k:" ++ toString ($k)) | none => `("1")
      let keyRaw ← wrapViewGuards h.guards keyLeaf (← `(""))
      let keyBody ← bindMentionedFields spec (mentionsIdent keyRaw.raw) keyRaw
      outCmds := outCmds.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subKeyDefName spec.t.getId h)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : String := $keyBody))
      if h.info.hasProps then
        let propsRaw ← wrapViewGuards h.guards (← `(Option.some $(← mkHoistedPropsTerm h))) (← `(Option.none))
        let propsBody ← bindMentionedFields spec (mentionsIdent propsRaw.raw) propsRaw
        outCmds := outCmds.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subPropsDefName spec.t.getId h)) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Option $(mkIdent (h.info.fullName ++ `Props)) := $propsBody))
  let hasLifecycleHoisted := spec.hoisted.any HoistedSub.hasLifecycle
  if hasLifecycleHoisted then outCmds := outCmds.push (← mkReconcileHoistedCmd spec pBinders retTy)
  let unchanged ← mkUpdateRet spec (← `(s))
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let mkUpdDef (fnId : Ident) (arms : Array MatchAltStx) (reconcile : Bool := false) : CommandElabM CmdStx := do
    let core ← if arms.isEmpty then `(nomatch m) else `(match m with $[$arms:matchAlt]*)
    let wrapped ← if reconcile && hasLifecycleHoisted then appWithProps spec (spec.id `_reconcileHoisted) #[← `(s), core] else pure core
    `(command| def $fnId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy := fun m => $wrapped)
  if spec.hoisted.isEmpty && spec.resetForms.isEmpty then return outCmds.push (← mkUpdDef spec.updateId ownArms)
  let stepOwnId := spec.id `stepOwn
  let subNoops ← spec.hoisted.mapM fun h => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor h.ctorName) _ => $unchanged)
  let rfNoops ← spec.resetForms.mapM fun rf => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $unchanged)
  let mut fullArms ← spec.hoisted.mapM (mkHoistedSubArm spec stepOwnId unchanged)
  for rf in spec.resetForms do
    let (df, fvId) := (rf.draftField, mkIdent `_fv)
    let ab ← `(match ($(rf.parseCall) s.$df:ident) with
      | some $fvId:ident => let _s1 := if $(rf.resetCond) then { s with $df:ident := $(mkIdent (`_root_ ++ rf.schemaName ++ `Draft ++ `empty)) } else s; $(← appWithProps spec stepOwnId #[← `(_s1), ← `(($(rf.handler) $fvId))])
      | none => $unchanged)
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $(← bindMentionedFields spec (mentionsIdent ab.raw) ab)))
  if !ownArms.isEmpty then fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | _m => $(← appWithProps spec stepOwnId #[← `(s), ← `(_m)])))
  return outCmds ++ #[← mkUpdDef stepOwnId (ownArms ++ subNoops ++ rfNoops), ← mkUpdDef spec.updateId fullArms (reconcile := true)]

def mkViewCmds (spec : ComponentSpec) (body' : Term) (msgAndUpdateCmds : Array CmdStx) : CommandElabM (Array CmdStx) := do
  let (renderId, pBinders) := (spec.id `_qed_render, ← mkPropsBinders spec)
  let mut cmds := msgAndUpdateCmds; let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  if spec.hasSlotsOrKids then
    let (pMsg, wrapId) := (mkIdent `_msg, mkIdent `_wrap)
    let mut slotBinders ← spec.slots.mapM fun sl => do `(bracketedBinder| ($(sl.id) : Html $pMsg := $(← sl.def?.getDM `(Qed.Html.empty))))
    if spec.hasChildren then slotBinders := slotBinders.push (← `(bracketedBinder| ($(mkIdent `children) : List (Html $pMsg) := [])))
    return cmds ++ #[
      ← `(command| def $renderId {$pMsg : Type} $[$pBinders:bracketedBinder]* ($wrapId : $(spec.msgId) → $pMsg) (s : $(spec.stateId)) $[$slotBinders:bracketedBinder]* : Html $pMsg := $viewBody),
      ← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $(← appWithProps spec renderId #[← `(id), ← `(s)]))]
  let rendered ← appWithProps spec spec.viewId #[← `(s)]
  cmds := cmds ++ #[
    ← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $viewBody),
    ← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]* (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route)]
  if spec.outTy?.isNone && !spec.hasEffects then
    let compId := spec.id `_qed_toComponent; let compExpr ← appWithProps spec compId
    cmds := cmds ++ #[
      ← (match spec.keyF? with
        | some kf => `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId)) (route : String → $(spec.msgId) → parentMsg) (s : $(spec.stateId)) (k : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)) : Html parentMsg := ($rendered).map (route k))
        | none    => `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId)) (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route)),
      ← `(command| $[$(spec.doc?):docComment]? def $compId $[$pBinders:bracketedBinder]* : Component $(spec.stateId) $(spec.msgId) := { update := $(← appWithProps spec spec.updateId), view := $(← appWithProps spec spec.viewId) })]
    if let some kf := spec.keyF? then
      let keyOfId := spec.id `keyOf
      cmds := cmds ++ #[
        ← `(command| def $keyOfId (s : $(spec.stateId)) : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)),
        ← `(command| def $(spec.id `updateKeyed) $[$pBinders:bracketedBinder]* (rows : Array $(spec.stateId)) (k : String) (msg : $(spec.msgId)) : Array $(spec.stateId) := Component.updateKeyed $compExpr $keyOfId rows k msg)]
  return cmds

end CompElab
end Qed
