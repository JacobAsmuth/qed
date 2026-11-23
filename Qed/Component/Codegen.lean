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

def resolveBindTy (bd : FieldDecl) : CommandElabM Term := do
  match bd.ty?, bd.def? with
  | some ty, _ => pure ty
  | none, some d => `(type_of% $d)
  | none, none => throwErrorAt bd.id s!"`bind {bd.id.getId}` needs a type or default"

def mkPropsBinders (spec : ComponentSpec) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if spec.hasProps then return #[← `(bracketedBinder| (p : $(spec.propsId)))]
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

def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub)
    (formDrafts : Array FieldDecl) (resetForms : Array ResetFormSub) : CommandElabM ComponentSpec := do
  if spec.outTy?.isSome then
    let evCtors ← spec.events.mapM fun ev => do
      let pIds := ev.params.map (·.1); let pTys := ev.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $(mkIdent ev.id.getId):ident $[($pIds:ident : $pTys)]*)
    let bdCtors ← spec.binds.mapM fun bd => do
      let setC := mkIdent (Name.mkSimple s!"set_{bd.id.getId}")
      `(Lean.Parser.Command.ctor| | $setC:ident (v : $(← resolveBindTy bd)))
    elabCommand (← `(command| inductive $(spec.id `Out) where $[$(evCtors ++ bdCtors):ctor]*))
  let allProps := spec.props ++ spec.binds
  let allStates := spec.states ++ formDrafts ++ hoisted.map fun h => {
    id := h.fieldId, ty? := some (mkIdent (h.info.fullName ++ `State)),
    def? := some (mkIdent (h.info.fullName ++ `init)) }
  elabCommand (← `(command| structure $(spec.propsId) where $[$(← allProps.mapM mkStructBinder):structExplicitBinder]*))
  elabCommand (← `(command| structure $(spec.stateId) where $[$(← allStates.mapM mkStructBinder):structExplicitBinder]*))
  let resolvedProps  ← resolveStructFieldTypes spec.t.getId `Props allProps
  let resolvedStates ← resolveStructFieldTypes spec.t.getId `State allStates
  let resolvedBinds  := spec.binds.map fun bd =>
    { bd with ty := (resolvedProps.find? (·.id.getId == bd.id.getId)).map (·.ty) |>.getD bd.ty }
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted, resetForms }

def mkCmdBatch (cmds : Array Term) : CommandElabM Term := do
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

def mkHoistedPropsTerm (h : HoistedSub) : CommandElabM Term := do
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

private def mkEmitOutTerm (spec : ComponentSpec) (s exprStx : Syntax) (targetId : Ident)
    (rawArgs : Array Syntax) (ev : EventDecl) (out? : Option Term) : CommandElabM Term := do
  let tname := targetId.getId.eraseMacroScopes
  if out?.isSome then
    throwErrorAt s "duplicate `.emit(...)` in action; an action emits at most one output"
  let argTerms ← lowerPosCallArgs exprStx s!"{tname}.emit(...)" (some ev.params.size) rawArgs
  Qed.Lang.mkAppTerms (mkIdentFrom targetId (spec.t.getId ++ `Out ++ ev.id.getId)) argTerms

private def mkChanSendCmdTerm (s exprStx : Syntax) (rawArgs : Array Syntax) (sub : SubDecl) :
    CommandElabM Term := do
  unless sub.chInfo.hasSend do
    throwErrorAt s s!"channel `{sub.chInfo.ownerShort}.{sub.chInfo.channelName}` does not declare `on_send` / `send`"
  let argTerms ← lowerPosCallArgs exprStx s!"{sub.id.getId}.send(...)" (some sub.chInfo.sendParamCount) rawArgs
  let chFullId := mkIdentFrom s sub.chInfo.fullName
  let slotLit := Syntax.mkStrLit sub.id.getId.toString
  withRef s `(qedCheckChanSend% $chFullId:ident [$[$argTerms:term],*] $slotLit:str)

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
      else if sk == ``qedStmtLet then
        lowerLetStmt s (lowerCompExpr .val) (← compileStmts spec sBase mutated out? cmds rest)
      else if sk == ``qedStmtAssign && (s.getArg 0).getKind == ``qedIdent &&
          spec.bindNames.contains ((s.getArg 0).getArg 0).getId.eraseMacroScopes then
        let op := atomStr (s.getArg 1)
        let fname := ((s.getArg 0).getArg 0).getId.eraseMacroScopes
        let valTerm ←
          if op == "=" && isPlaceholder (s.getArg 2) then `(v)
          else desugarAssign fname op (← lowerCompExpr .val (s.getArg 2))
        if out?.isSome then
          throwErrorAt s s!"cannot assign `bind` field `{fname}` here: this action already emits an output event (an action emits at most one output)"
        let outCtor := spec.outCtor (Name.mkSimple s!"set_{fname}")
        let oTerm ← `($outCtor $valTerm)
        return ← compileStmts spec sBase mutated (some oTerm) cmds rest
      else if let some (fname, wrap) ← lowerMutStmt? spec s true then
        wrap (← compileStmts spec sBase (mutated.push fname) out? cmds rest)
      else if sk == ``qedStmtExpr then
        let exprStx := s.getArg 0
        let bindCmd (pfx : String) (cmdT : Term) : CommandElabM Term := do
          let cmdId := mkIdent (Name.mkSimple s!"_{pfx}_{cmds.size}")
          let cont ← compileStmts spec sBase mutated out? (cmds.push (cmdId : Term)) rest
          `(let $cmdId:ident := $cmdT; $cont)
        let bindRawCmd : CommandElabM Term := do
          let cmdT ← lowerCompExpr .val exprStx
          bindCmd "cmd" (← `(($cmdT : Qed.Cmd $(mkIdent (spec.t.getId ++ `Msg)))))
        if let some (targetId, meth, rawArgs) := matchIdentMethodCall? exprStx then
          let tname := targetId.getId.eraseMacroScopes
          if meth == "emit" then
            match spec.events.find? (·.id.getId.eraseMacroScopes == tname) with
            | some ev =>
                let outTerm ← mkEmitOutTerm spec s exprStx targetId rawArgs ev out?
                compileStmts spec sBase mutated (some outTerm) cmds rest
            | none =>
                unless spec.outTy?.isSome do noEmitsErr s
                throwErrorAt targetId s!"unknown `event` `{tname}` in `{tname}.emit(...)`"
          else if meth == "send" then
            if let some sub := spec.subscriptions.find? (·.id.getId.eraseMacroScopes == tname) then
              bindCmd "wsSendCmd" (← mkChanSendCmdTerm s exprStx rawArgs sub)
            else if let some po := spec.portOuts.find? (·.id.getId.eraseMacroScopes == tname) then
              bindCmd "portCmd" (← mkPortSendTerm spec.t.getId exprStx targetId po.id.getId rawArgs)
            else
              throwErrorAt targetId s!"unknown `subscribe` channel or outbound `port` `{tname}` in `{tname}.send(...)`"
          else bindRawCmd
        else bindRawCmd
      else if sk == ``qedStmtIf || sk == ``qedStmtIfLet || sk == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt s
        let sFlushed ← flushMutated sBase mutated
        let tailStmts := if passTail then rest else []
        let branchTerm ← lowerControlFlowStmt s (lowerCompExpr .val) fun seq =>
          compileStmts spec sFlushed #[] out? cmds (seq.toList ++ tailStmts)
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

private def appWithProps (spec : ComponentSpec) (fn : Ident) (args : Array Term := #[]) :
    CommandElabM Term := do
  let pTerm ← `(p)
  Qed.Lang.mkAppTerms fn (if spec.hasProps then #[pTerm] ++ args else args)

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

def mkRpcQueryBranches (spec : ComponentSpec) (rspec : RpcQuerySpec)
    (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term := do
  mkGuardedBranches spec "_qa" rspec.mInfo.paramTypeConsts rspec.args
    rspec.whenPat? rspec.whenGuards (← `(none)) true leafFn

def mkRpcQueryParamsBody (spec : ComponentSpec) (rspec : RpcQuerySpec) : CommandElabM Term :=
  mkRpcQueryBranches spec rspec fun qaIds => do
    `(some $(← Qed.Lang.buildTupleVal (qaIds.map (⟨·.raw⟩))))

def mkSubBranches (spec : ComponentSpec) (sub : SubDecl) (elseTerm : Term)
    (depMatch : Bool) (leafFn : Array Ident → CommandElabM Term) : CommandElabM Term :=
  mkGuardedBranches spec "_sa" sub.chInfo.paramTypeConsts sub.args
    sub.whenPat? sub.whenGuards elseTerm depMatch leafFn

private def mkSubKeyExpr (spec : ComponentSpec) (sub : SubDecl) : CommandElabM Term := do
  let keyFnId := mkIdentFrom sub.chanRef sub.chInfo.keyHelperConst
  mkSubBranches spec sub (← `("")) false fun qaIds =>
    Qed.Lang.mkAppTerms keyFnId (qaIds.map (⟨·.raw⟩))

def subKeyFnName (tId : Name) (sub : SubDecl) : Name :=
  tId ++ Name.mkSimple s!"_wsKey_{sub.id.getId}"

private def mkMsgInductiveCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (Array (TSyntax `command)) := do
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
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_emit):ident (_o : $(spec.id `Out))))
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
  let msgCmd ← if ctors.isEmpty then `(command| inductive $(spec.msgId))
    else `(command| inductive $(spec.msgId) where $[$ctors:ctor]*)
  let mut outCmds : Array (TSyntax `command) := #[msgCmd]
  for po in spec.portOuts do
    let poLit := Syntax.mkStrLit po.id.getId.toString
    outCmds := outCmds.push (← `(command| def $(spec.id po.id.getId) (x : $(po.ty)) : Cmd $(spec.msgId) :=
      Cmd.port $poLit (Json.render (ToJson.toJson x))))
  if spec.outTy?.isSome then
    outCmds := outCmds.push (← `(command|
      instance $(spec.id (`Out ++ `instCoeMsg)):ident : Coe $(spec.id `Out) $(spec.msgId) := ⟨$(spec.msgCtor `_emit)⟩))
  return outCmds

private def mkSiteUpdateArm (spec : ComponentSpec) (site : SetSite) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let cFull := spec.msgCtor site.ctor
  let mut rhs ← (match site.stmts? with
    | some stmts => do
        let isPureNoop := stmts.all fun st =>
          ![``qedStmtAssign, ``qedStmtExpr,
            ``qedStmtIf, ``qedStmtIfLet, ``qedStmtMatch, ``qedStmtPass].contains st.getKind
        if isPureNoop then
          throwErrorAt stmts[0]! s!"action `{site.ctor}` has no state update or effect; add a state assignment, effect, or `pass`"
        compileStmts spec (← `(s)) #[] none #[] stmts.toList
    | none => do mkUpdateRet spec (← flushAssigns (← `(s)) site.assigns) site.send? #[])
  rhs ← bindMentionedFields spec (mentionsIdent rhs.raw) rhs
  if !site.params.isEmpty then
    let ids : Array Term := site.params.map (⟨·.1.raw⟩)
    `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
  else if site.assigns.any (·.2.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
  else `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)

private def mkRouteUpdateArm (spec : ComponentSpec) (rd : RouteDecl) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let rVal := mkIdent `_r
  let sWithR ← `({ s with $(rd.field):ident := $rVal:ident })
  let mut rhs ← (if rd.alts.isEmpty then mkUpdateRet spec sWithR none #[]
    else do
      let alts ← rd.alts.mapM fun alt => do
        let pats ← (alt.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
        `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* =>
            $(← compileStmts spec sWithR #[] none #[] (suiteStmts (alt.getArg 3)).toList))
      `(match $rVal:ident with $[$alts:matchAlt]*))
  rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
  rhs ← `(let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs)
  `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onRoute):ident $rVal:ident => $rhs)

private def mkSubUpdateArms (spec : ComponentSpec) (sub : SubDecl) (unchanged : Term) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let subNm := sub.id
  let wsKeyId := mkIdent (subKeyFnName spec.t.getId sub)
  let mkGuardedSubArm (ctorName : Name) (valId : Ident) (sBase fallback : Term)
      (handler? : Option (Option Syntax × Array Syntax))
      (wrapBody : Option Syntax → Term → CommandElabM Term)
      (skipField? : Option Name := none) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
    let body ← match handler? with
      | some (b?, stmts) =>
          let mut b ← compileStmts spec sBase #[] none #[] stmts.toList
          b ← bindMentionedFields spec (fun g => skipField? != some g && mentionsIdent b.raw g) b
          wrapBody b? b
      | none => pure fallback
    let guarded ← `(if $wsKeyId s == _wk then $body else $unchanged)
    `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor ctorName):ident _wk $valId:ident => $guarded)
  let bindOpt (valExpr : Term) (b? : Option Syntax) (b : Term) : CommandElabM Term := do
    match b? with
    | some bStx => if bStx.isIdent then `(let $(⟨bStx⟩):ident := $valExpr; $b) else pure b
    | none      => pure b
  let sBase ← `(s)
  let snapId := mkIdent `_wsnap
  let evId   := mkIdent `_wev
  let stId   := mkIdent `_wst
  let sWithSt ← `({ s with $subNm:ident := $stId:ident })
  let joinArm ← mkGuardedSubArm sub.joinCtor snapId sBase unchanged sub.onJoin? (bindOpt (← `($snapId:ident)))
  let msgArm ← mkGuardedSubArm sub.msgCtor evId sBase unchanged
    (sub.onMsg?.map fun (b, ss) => (some b, ss)) fun b? b => do
      if sub.hasMsgEnsured then
        let b' ← `(have _hWsEns := ($evId:ident).ok; $b)
        bindOpt (← `(($evId:ident).val)) b? b'
      else bindOpt (← `($evId:ident)) b? b
  let stArm ← mkGuardedSubArm sub.statusCtor stId sWithSt (← mkUpdateRet spec sWithSt none #[])
    (sub.onStatus?.map fun (b, ss) => (some b, ss)) (skipField? := some subNm.getId) fun b? b => do
      bindOpt (← `($stId:ident)) b? (← `(let $(mkIdent subNm.getId):ident := $stId:ident; $b))
  pure #[joinArm, msgArm, stArm]

private def mkOwnUpdateArms (spec : ComponentSpec) (sites : Array SetSite) (unchanged : Term) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let mut ownArms ← sites.mapM (mkSiteUpdateArm spec)
  if let some rd := spec.route? then
    ownArms := ownArms.push (← mkRouteUpdateArm spec rd)
  if let some sfId := spec.sessionField? then
    let uVar := mkIdent `_u
    let next ← `({ s with $sfId:ident := $uVar:ident })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor `_onSession):ident $uVar:ident => $(← mkUpdateRet spec next none #[])))
  if spec.outTy?.isSome then
    let oVar := mkIdent `_o
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(spec.msgCtor `_emit):ident $oVar:ident => $(← mkUpdateRet spec (← `(s)) (some ⟨oVar.raw⟩) #[])))
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    let next ← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(spec.msgCtor colField.getId) k msg => $(← mkUpdateRet spec next none #[])))
  for q in spec.queries do
    let qNm := q.id
    let rspec := q.rpc
    let keyBound ← `($(mkIdent `Qed.rpcQueryKey) $(← mkRpcQueryParamsBody spec rspec))
    let plainRes ← if rspec.hasMsgEnsured then `($(mkIdent `Qed.Resource.stripEnsured) _qr) else `(_qr)
    let next ← `({ s with $qNm:ident := (s.$qNm:ident).put _qk $plainRes $keyBound })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(spec.msgCtor q.ctorName):ident _qk _qr => $(← mkUpdateRet spec next none #[])))
  for sub in spec.subscriptions do
    ownArms := ownArms ++ (← mkSubUpdateArms spec sub unchanged)
  return ownArms

private def mkHoistedSubArm (spec : ComponentSpec) (stepOwnId : Ident) (h : HoistedSub) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let subCtor := spec.msgCtor h.ctorName
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
            let stepCall ← appWithProps spec stepOwnId #[s1Var, pmVar]
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

private def mkResetFormArm (spec : ComponentSpec) (stepOwnId : Ident) (unchanged : Term)
    (rf : ResetFormSub) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let emptyExpr := mkIdent (`_root_ ++ rf.schemaName ++ `Draft ++ `empty)
  let df := rf.draftField
  let fvId := mkIdent `_fv
  let callStep ← appWithProps spec stepOwnId #[← `(_s1), ← `(($(rf.handler) $fvId))]
  let mut armBody ← `(
    match ($(rf.parseCall) s.$df:ident) with
    | some $fvId:ident =>
        let _s1 := if $(rf.resetCond) then { s with $df:ident := $emptyExpr } else s
        $callStep
    | none => $unchanged)
  armBody ← bindMentionedFields spec (mentionsIdent armBody.raw) armBody
  `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $armBody)

private def mkHoistedUpdateCmds (spec : ComponentSpec)
    (pBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (ownArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (unchanged retTy : Term) : CommandElabM (Array (TSyntax `command)) := do
  let stepOwnId := spec.id `stepOwn
  let subNoopArms ← spec.hoisted.mapM fun h =>
    `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor h.ctorName) _ => $unchanged)
  let rfNoopArms ← spec.resetForms.mapM fun rf =>
    `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rf.ctorName) => $unchanged)
  let stepOwnCmd ← `(command| def $stepOwnId $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy :=
    fun m => match m with $[$(ownArms ++ subNoopArms ++ rfNoopArms):matchAlt]*)
  let mut fullArms ← spec.hoisted.mapM (mkHoistedSubArm spec stepOwnId)
  for rf in spec.resetForms do
    fullArms := fullArms.push (← mkResetFormArm spec stepOwnId unchanged rf)
  if !ownArms.isEmpty then
    let otherVar := mkIdent `_m
    let callOwn ← appWithProps spec stepOwnId #[← `(s), otherVar]
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $otherVar:ident => $callOwn))
  let updateBody ← if fullArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$fullArms:matchAlt]*)
  return #[stepOwnCmd, ← `(command| def $(spec.updateId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy := $updateBody)]

def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (Array (TSyntax `command)) := do
  let mut outCmds ← mkMsgInductiveCmds spec sites
  for sub in spec.subscriptions do
    let wsKeyId := mkIdent (subKeyFnName spec.t.getId sub)
    let keyBody ← mkSubKeyExpr spec sub
    outCmds := outCmds.push (← `(command|
      set_option linter.unusedVariables false in
      def $wsKeyId (s : $(spec.stateId)) : String := $keyBody))
  let unchanged ← mkUpdateRet spec (← `(s)) none #[]
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none,   false => `($(spec.stateId))
    | some o, false => `($(spec.stateId) × Option $o)
    | none,   true  => `($(spec.stateId) × Cmd $(spec.msgId))
    | some o, true  => `($(spec.stateId) × Option $o × Cmd $(spec.msgId))
  let pBinders ← mkPropsBinders spec
  if spec.hoisted.isEmpty && spec.resetForms.isEmpty then
    let updateBody ← if ownArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$ownArms:matchAlt]*)
    return outCmds.push (← `(command| def $(spec.updateId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : $(spec.msgId) → $retTy := $updateBody))
  return outCmds ++ (← mkHoistedUpdateCmds spec pBinders ownArms unchanged retTy)

private def mkPureCompViewExtras (spec : ComponentSpec)
    (pBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (rendered : Term) : CommandElabM (Array (TSyntax `command)) := do
  let compId := spec.id `_qed_toComponent
  let compExpr ← appWithProps spec compId
  let mut cmds : Array (TSyntax `command) := #[
    ← (match spec.keyF? with
      | some kf =>
        `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId))
            (route : String → $(spec.msgId) → parentMsg) (s : $(spec.stateId))
            (k : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)) : Html parentMsg := ($rendered).map (route k))
      | none =>
        `(command| def $(spec.id `_qed_renderTag) {parentMsg : Type} (p : $(spec.propsId))
            (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route)),
    ← `(command| $[$(spec.doc?):docComment]? def $compId $[$pBinders:bracketedBinder]*
          : Component $(spec.stateId) $(spec.msgId) := { update := $(← appWithProps spec spec.updateId), view := $(← appWithProps spec spec.viewId) }) ]
  if let some kf := spec.keyF? then
    let keyOfId := spec.id `keyOf
    cmds := cmds ++ #[
      ← `(command| def $keyOfId (s : $(spec.stateId)) : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)),
      ← `(command| def $(spec.id `updateKeyed) $[$pBinders:bracketedBinder]*
            (rows : Array $(spec.stateId)) (k : String) (msg : $(spec.msgId)) : Array $(spec.stateId) :=
            Component.updateKeyed $compExpr $keyOfId rows k msg) ]
  return cmds

def mkViewCmds (spec : ComponentSpec) (body' : Term)
    (msgAndUpdateCmds : Array (TSyntax `command)) : CommandElabM (Array (TSyntax `command)) := do
  let renderId := spec.id `_qed_render
  let pBinders ← mkPropsBinders spec
  let mut cmds := msgAndUpdateCmds
  let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  if spec.hasSlotsOrKids then
    let pMsg := mkIdent `_msg; let wrapId := mkIdent `_wrap
    let mut slotBinders ← spec.slots.mapM fun sl => do
      `(bracketedBinder| ($(sl.id) : Html $pMsg := $(← sl.def?.getDM `(Qed.Html.empty))))
    if spec.hasChildren then
      slotBinders := slotBinders.push (← `(bracketedBinder| ($(mkIdent `children) : List (Html $pMsg) := [])))
    cmds := cmds.push (← `(command| def $renderId {$pMsg : Type} $[$pBinders:bracketedBinder]* ($wrapId : $(spec.msgId) → $pMsg)
        (s : $(spec.stateId)) $[$slotBinders:bracketedBinder]* : Html $pMsg := $viewBody))
    let viewCall ← appWithProps spec renderId #[← `(id), ← `(s)]
    return cmds.push (← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $viewCall))
  cmds := cmds.push (← `(command| def $(spec.viewId) $[$pBinders:bracketedBinder]* (s : $(spec.stateId)) : Html $(spec.msgId) := $viewBody))
  let rendered ← appWithProps spec spec.viewId #[← `(s)]
  cmds := cmds.push (← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]*
      (route : $(spec.msgId) → parentMsg) (s : $(spec.stateId)) : Html parentMsg := ($rendered).map route))
  if spec.outTy?.isNone && !spec.hasEffects then
    cmds := cmds ++ (← mkPureCompViewExtras spec pBinders rendered)
  return cmds


end CompElab
end Qed
