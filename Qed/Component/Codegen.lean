import Qed.Component.Rewrite
import Qed.Runtime.Cmd

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Shared Structure, Binder & Codegen Helpers -/

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
  let allStates := spec.states ++ formDrafts ++ hoisted.map fun h =>
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

private def flushAssigns (sBase : Term) (assigns : Array (Name × Option Term)) : CommandElabM Term := do
  if assigns.isEmpty then return sBase
  let (fIds, vals) := (assigns.map (mkIdent ·.1), ← assigns.mapM (·.2.getDM `(v)))
  `({ $sBase with $[$fIds:ident := $vals],* })

private def flushMutated (sBase : Term) (mutated : Array Name) : CommandElabM Term := do
  if mutated.isEmpty then return sBase
  let fIds := mutated.toList.eraseDups.toArray.map mkIdent; let fVals : Array Term := fIds.map (⟨·.raw⟩)
  `({ $sBase with $[$fIds:ident := $fVals:term],* })

private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (mutated : Array Name) (out? : Option Term) (cmds : Array Term) (stmts : List Syntax) : CommandElabM Term := do
  match stmts with
  | [] => mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
  | s :: rest =>
      let sk := s.getKind
      if sk == ``qedStmtPass then compileStmts spec sBase mutated out? cmds rest
      else if sk == ``qedStmtReturn then mkUpdateRet spec (← flushMutated sBase mutated) out? cmds
      else if sk == ``qedStmtLet then lowerLetStmt s (lowerCompExpr .val) (← compileStmts spec sBase mutated out? cmds rest)
      else if sk == ``qedStmtAssign && (s.getArg 0).getKind == ``qedIdent && spec.bindNames.contains ((s.getArg 0).getArg 0).getId.eraseMacroScopes then
        let (op, fname) := (atomStr (s.getArg 1), ((s.getArg 0).getArg 0).getId.eraseMacroScopes)
        let valTerm ← if op == "=" && isPlaceholder (s.getArg 2) then `(v) else desugarAssign fname op (← lowerCompExpr .val (s.getArg 2))
        if out?.isSome then throwErrorAt s s!"cannot assign `bind` field `{fname}` here: this action already emits an output event (an action emits at most one output)"
        compileStmts spec sBase mutated (some (← `($(spec.outCtor (bindSetName fname)) $valTerm))) cmds rest
      else if let some (fname, wrap) ← lowerMutStmt? spec s true then
        wrap (← compileStmts spec sBase (mutated.push fname) out? cmds rest)
      else if sk == ``qedStmtExpr then
        let exprStx := s.getArg 0
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
        | _ => bindCmd "cmd" (← `(($(← lowerCompExpr .val exprStx) : Qed.Cmd $(spec.msgId))))
      else if sk == ``qedStmtIf || sk == ``qedStmtIfLet || sk == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt s; let sFlushed ← flushMutated sBase mutated
        let branchTerm ← lowerControlFlowStmt s (lowerCompExpr .val) fun seq => compileStmts spec sFlushed #[] out? cmds (seq.toList ++ if passTail then rest else [])
        if passTail || rest.isEmpty then return branchTerm
        let brId := mkIdent `_qedBr; let (sNext, oNext, cOpt) ← unpackRetTuple spec.outTy?.isSome spec.hasEffects brId
        let cNext := match cOpt with | some c => #[c] | none => #[]
        let tail ← match oNext with
          | none => compileStmts spec sNext #[] none cNext rest
          | some oExpr =>
              let oVal := mkIdent `_qedOut
              `(match $oExpr:term with | none => $(← compileStmts spec sNext #[] none cNext rest) | some $oVal:ident => $(← compileStmts spec sNext #[] (some ⟨oVal.raw⟩) cNext rest))
        let mut rebound := tail
        for fn in spec.fieldNames.reverse do
          if rest.any (mentionsIdent · fn) then let fId := mkIdent fn; rebound ← `(let $fId:ident := ($sNext).$fId:ident; $rebound)
        `(let $brId:ident := $branchTerm; $rebound)
      else let sn := stxSnippet s; throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in component action"

private def appWithProps (spec : ComponentSpec) (fn : Ident) (args : Array Term := #[]) : CommandElabM Term := do
  let pT ← `(p); Qed.Lang.mkAppTerms fn (if spec.hasProps then #[pT] ++ args else args)

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
    else match site.assigns.find? (·.2.isNone) with
    | some (f, _) =>
        let some d := (spec.states ++ spec.props).find? (·.id.getId == f) | throwError s!"component: internal unknown field `{f}`"
        mkCtor site.ctor #[(mkIdent `v, d.ty)]
    | none => mkCtor site.ctor
  if let some rd := spec.route? then ctors := ctors.push (← mkCtor `_onRoute #[(mkIdent `_r, rd.ty)])
  if spec.sessionField?.isSome then ctors := ctors.push (← mkCtor `_onSession #[(mkIdent `_u, ← `(Option String))])
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
  else if site.assigns.any (·.2.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
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
    `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor ctorName):ident _wk $valId:ident => if $wsKeyId s == _wk then $body else $unchanged)
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
        `(Lean.Parser.Term.matchAltExpr| | $[$(← (alt.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)):term],* => $(← compileStmts spec sWithR #[] none #[] (suiteStmts (alt.getArg 3)).toList))
      `(match $rVal:ident with $[$alts:matchAlt]*))
    rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onRoute):ident $rVal:ident => let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs))
  if let some sfId := spec.sessionField? then
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onSession):ident _u => $(← mkUpdateRet spec (← `({ s with $sfId:ident := _u })))))
  if spec.outTy?.isSome then
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_emit):ident _o => $(← mkUpdateRet spec (← `(s)) (some (← `(_o))))))
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor colField.getId) k msg => $(← mkUpdateRet spec (← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })))))
  for q in spec.queries do
    let keyBound ← `($(mkIdent `Qed.rpcQueryKey) $(← mkRpcQueryParamsBody spec q.rpc))
    let plainRes ← if q.rpc.hasMsgEnsured then `($(mkIdent `Qed.Resource.stripEnsured) _qr) else `(_qr)
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor q.ctorName):ident _qk _qr => $(← mkUpdateRet spec (← `({ s with $(q.id):ident := (s.$(q.id):ident).put _qk $plainRes $keyBound })))))
  for sub in spec.subscriptions do arms := arms ++ (← mkSubUpdateArms spec sub unchanged)
  return arms

private def mkHoistedSubArm (spec : ComponentSpec) (stepOwnId : Ident) (h : HoistedSub) : CommandElabM MatchAltStx := do
  let (subCtor, subF, cmVar, crVar, s1Var) := (spec.msgCtor h.ctorName, h.fieldId, mkIdent `_cm, mkIdent `_cr, mkIdent `_s1)
  let cUpd := mkIdent (h.info.fullName ++ `update)
  let cCall ← if h.info.hasProps then `($cUpd $(← mkHoistedPropsTerm h) s.$subF:ident $cmVar:ident) else `($cUpd s.$subF:ident $cmVar:ident)
  let (csExpr, coExpr?, rawC?) ← unpackRetTuple h.info.hasOut h.info.hasEffects crVar
  let ccExpr? ← rawC?.mapM fun rc => `(Cmd.map $subCtor $rc)
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
  let armBody ← `(let $crVar:ident := $cCall; let $s1Var:ident := { s with $subF:ident := $csExpr }; $afterSub)
  `(Lean.Parser.Term.matchAltExpr| | $subCtor $cmVar:ident => $(← bindMentionedFields spec (mentionsIdent armBody.raw) armBody))

def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) : CommandElabM (Array CmdStx) := do
  let mut outCmds ← mkMsgInductiveCmds spec sites
  for sub in spec.subscriptions do
    let keyBody ← mkSubBranches spec sub (← `("")) false fun qaIds => Qed.Lang.mkAppTerms (mkIdentFrom sub.chanRef sub.chInfo.keyHelperConst) (qaIds.map (⟨·.raw⟩))
    outCmds := outCmds.push (← `(command| set_option linter.unusedVariables false in def $(mkIdent (subKeyFnName spec.t.getId sub)) (s : $(spec.stateId)) : String := $keyBody))
  let unchanged ← mkUpdateRet spec (← `(s))
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none, false => `($(spec.stateId)) | some o, false => `($(spec.stateId) × Option $o)
    | none, true  => `($(spec.stateId) × Cmd $(spec.msgId)) | some o, true => `($(spec.stateId) × Option $o × Cmd $(spec.msgId))
  let pBinders ← mkPropsBinders spec
  let mkUpdDef (fnId : Ident) (arms : Array MatchAltStx) : CommandElabM CmdStx := do
    let body ← if arms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$arms:matchAlt]*)
    `(command| def $fnId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy := $body)
  if spec.hoisted.isEmpty && spec.resetForms.isEmpty then return outCmds.push (← mkUpdDef spec.updateId ownArms)
  let stepOwnId := spec.id `stepOwn
  let subNoops ← spec.hoisted.mapM fun h => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor h.ctorName) _ => $unchanged)
  let rfNoops ← spec.resetForms.mapM fun rf => `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $unchanged)
  let mut fullArms ← spec.hoisted.mapM (mkHoistedSubArm spec stepOwnId)
  for rf in spec.resetForms do
    let (df, fvId) := (rf.draftField, mkIdent `_fv)
    let ab ← `(match ($(rf.parseCall) s.$df:ident) with
      | some $fvId:ident => let _s1 := if $(rf.resetCond) then { s with $df:ident := $(mkIdent (`_root_ ++ rf.schemaName ++ `Draft ++ `empty)) } else s; $(← appWithProps spec stepOwnId #[← `(_s1), ← `(($(rf.handler) $fvId))])
      | none => $unchanged)
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $(← bindMentionedFields spec (mentionsIdent ab.raw) ab)))
  if !ownArms.isEmpty then fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | _m => $(← appWithProps spec stepOwnId #[← `(s), ← `(_m)])))
  return outCmds ++ #[← mkUpdDef stepOwnId (ownArms ++ subNoops ++ rfNoops), ← mkUpdDef spec.updateId fullArms]

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
