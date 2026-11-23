import Qed.Component.Codegen
import Qed.Component.AwaitLift
import Qed.Component.Speculative
import Qed.Component.Invariants
import Qed.Component.RpcChecks
import Qed.Speculative
import Qed.View.Lift
import Qed.Runtime
import Qed.Resource
import Qed.Socket

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

private def elabPureCompInvariants (spec : ComponentSpec) (viewId : Ident) (msgV : Ident)
    (needsProps : Bool) (viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :
    CommandElabM Unit := do
  let tId := spec.t.getId
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause ||
       invStx.getKind == ``compExampleClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` and `example` apply to stateful components"
    let invId := resolveInvIdent invStx tId
    let rawClauses := (invStx.getArg 2).getSepArgs
    let loweredClauses ← rawClauses.mapM (lowerCompExpr .val)
    let (vPred, predStr) ← mkViewPredAndStr invStx rawClauses loweredClauses "empty view invariant"
    let vCall ← if needsProps then `($viewId p) else `(($viewId : Html $msgV))
    let pf? : Option Term := if (invStx.getArg 5).getNumArgs == 2 then some ⟨((invStx.getArg 5).getArg 1)⟩ else none
    let rhs ← pf?.getDM `(by
      let _qed_hv := fun (_ : Unit) => $vCall
      suffices ∀ u, ($vPred) (_qed_hv u) = true from this ()
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))

private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  let doc? := spec.doc?
  let msgV := mkIdent `msg
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
  elabCommand (← `(command| structure $(spec.propsId) ($msgV : Type) where $[$pBinders:structExplicitBinder]*))
  let mut viewBody := body'
  for g in propReadNames.reverse do
    if mentionsIdent viewBody.raw g then
      let gId := mkIdent g
      viewBody ← `(let $gId:ident := (p.$gId:ident); $viewBody)
  let needsProps := !pBinders.isEmpty
  let viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if needsProps then pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $(spec.propsId) $msgV))]
    else pure #[← `(bracketedBinder| {$msgV : Type})]
  elabCommand (← `(command| $[$doc?:docComment]? @[inline] def $(spec.viewId) $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody))
  elabPureCompInvariants spec spec.viewId msgV needsProps viewBinders
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyTerm
      return ((← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _) &&
             ((← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _)
    catch _ => return false

private def mkCompStructJsonCmds (sName : Name) (decls : Array FieldDecl) :
    CommandElabM (Array (TSyntax `command)) :=
  Qed.mkStructJsonCmds (mkIdent sName)
    (decls.map fun d => { ident := d.id, wireKey := d.id.getId.toString, valTy := d.ty })
    { emitNamedDefs := false }

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
  let doc? := spec.doc?
  let regId := spec.id `reg
  let regRhs ← match spec.hasProps, spec.outTy?.isNone with
    | true,  true  => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) (fun p s m => ($(spec.updateId) p s m, (none : Option Bool))))
    | true,  false => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, true  => `(LocalDef.ofSimple $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, false => `(LocalDef.of $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
  let regDoc? := if spec.hasProps then none else doc?
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| $[$regDoc?:docComment]? def $regId : LocalDef := $regRhs),
    ← `(command| $[$doc?:docComment]? def $(spec.id `_qed_mount) {msg : Type} (key : String) : Attr msg :=
          localMount $idLit key) ]
  if let some o := spec.outTy? then
    cmds := cmds.push (← `(command| def $(spec.id `_qed_mountWithOpt) {msg : Type}
          (key : String) (onOut : $o → Option msg) : Attr msg :=
          localMountWith $idLit key onOut))
  return cmds

private def canSynthDecidablePred (stateId : Ident) (pred : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let pVal ← Term.elabTermEnsuringType pred (← Term.elabType (← `($stateId → Prop)))
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← Meta.trySynthInstance (← Meta.mkAppM ``DecidablePred #[pVal])) matches .some _

private def mkEnsuredExistentialWrap (ensConst : Name) (qaIds : Array Ident)
    (elemVar : Ident) : CommandElabM (Term × Term) := do
  let ensApp ← Qed.Lang.mkAppTerms (mkIdent ensConst) (qaIds.map (⟨·.raw⟩))
  let exPrf ← qaIds.foldrM (init := ← `(($elemVar:ident).ok)) fun qa acc => `(Exists.intro $qa $acc)
  return (ensApp, exPrf)

private def mkCompQueriesCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.queries.isEmpty then return none
  let qTerms ← spec.queries.mapM fun q => do
    let qNm := q.id
    let rspec := q.rpc
    let reqTupleTy ← Qed.Lang.buildProdType (rspec.mInfo.paramTypeConsts.map fun n => (mkIdent n : Term))
    let paramsBody ← mkRpcQueryParamsBody spec rspec
    let fetchBody ← mkRpcQueryBranches spec rspec fun qaIds => do
      let cbTerm : Term ← if !rspec.hasMsgEnsured then
          `(_qgot _qk)
        else
          let some ensConst := rspec.mInfo.ensPredConst
            | throwErrorAt rspec.rpcRef "internal: missing server `ensures` predicate in `query`"
          let qeId := mkIdent `_qe
          let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds qeId
          `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => _qgot _qk (_qr.map fun $qeId => ⟨($qeId:ident).val, $exPrf⟩))
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      let srvId := mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName
      let methId := mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)
      `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$qaTerms:term],*] $cbTerm)))
    `(Qed.Resource.rpcQuery (Req := $reqTupleTy)
        (params? := fun (s : $(spec.stateId)) => $paramsBody)
        (fetch := fun (s : $(spec.stateId)) _qgot _qk => $fetchBody)
        (got := $(spec.msgCtor q.ctorName))
        (get := fun (s : $(spec.stateId)) => s.$qNm:ident)
        (set := fun c (s : $(spec.stateId)) => { s with $qNm:ident := c }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(spec.id `queries) : List (Query $(spec.stateId) $(spec.msgId)) := [$[$qTerms],*]))

private def mkCompSubscriptionsCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.subscriptions.isEmpty then return none
  let subTerms ← spec.subscriptions.mapM fun sub => do
    let subNm := sub.id
    let slotLit := Syntax.mkStrLit subNm.getId.toString
    let wsKeyId := mkIdent (subKeyFnName spec.t.getId sub)
    let msgCtor := spec.msgCtor sub.msgCtor
    let recTerm ← liftMacroM <| sub.reconnect.toSyntaxTerm
    let unsubFnId := mkIdentFrom sub.chanRef sub.chInfo.unsubHelperConst
    let chFullId := mkIdentFrom sub.chanRef sub.chInfo.fullName
    let openBody ← mkSubBranches spec sub (← `(none)) true fun qaIds => do
      let onJoinCb ← `($(spec.msgCtor sub.joinCtor) _wk)
      let onStCb ← `($(spec.msgCtor sub.statusCtor) _wk)
      let onMsgCb ← if !sub.hasMsgEnsured then
          `($msgCtor _wk)
        else
          let some ensConst := sub.chInfo.ensPredConst
            | throwErrorAt sub.chanRef "internal: missing channel `ensures` predicate in `subscribe`"
          let evTyId := mkIdentFrom sub.chanRef sub.chInfo.eventTypeConst
          let weId := mkIdent `_we
          let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds weId
          `(fun ($weId : Qed.Ensured $evTyId ($ensApp)) => $msgCtor _wk ⟨($weId:ident).val, $exPrf⟩)
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      let subCmd ← withRef sub.chanRef `(qedCheckChanSub% $chFullId:ident [$[$qaTerms:term],*] $slotLit:str ($recTerm, $onJoinCb, $onMsgCb, $onStCb))
      `(some $subCmd)
    `(Qed.Subscription.mk
        $slotLit
        $wsKeyId
        (fun _wk (s : $(spec.stateId)) => $openBody)
        ($unsubFnId $slotLit)
        (fun (s : $(spec.stateId)) => { s with $subNm:ident := Qed.SocketStatus.disconnected }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(spec.id `subscriptions) : List (Qed.Subscription $(spec.stateId) $(spec.msgId)) := [$[$subTerms],*]))


private def mkSpecStepPf (sVar mVar : Ident) : List Ident → Term → CommandElabM Term
  | [], _ => `(trivial)
  | [id0], hTerm => `(($id0:ident).2 $sVar $mVar $hTerm)
  | lastId :: prevRev, hTerm => do
      let leftPf ← mkSpecStepPf sVar mVar prevRev (← `(($hTerm).1))
      `(And.intro $leftPf (($lastId:ident).2 $sVar $mVar ($hTerm).2))

private def mkSpecPropPair (spec : ComponentSpec) (suffix : String)
    (prop initPf stepFn : Term) : CommandElabM (Array (TSyntax `command)) := do
  let appIdent := spec.id `app
  pure #[
    ← `(command|
      theorem $(spec.id (Name.mkSimple s!"specApp_init_{suffix}")) :
          $prop ($appIdent).init.1 := $initPf),
    ← `(command|
      theorem $(spec.id (Name.mkSimple s!"specApp_preserves_{suffix}"))
          (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) (msg : $(spec.msgId)) (h : $prop st) :
          $prop (($appIdent).update st msg).1 := $stepFn st msg h) ]

private def mkSpecInvThmCmds (spec : ComponentSpec) (baseAppIdent clsIdent : Ident)
    (inv : Term) (stateInvEntries : Array (Term × Option Ident)) :
    CommandElabM (Array (TSyntax `command)) := do
  let invIds? : Option (Array Ident) :=
    stateInvEntries.foldl (init := some #[]) fun acc (_, id?) =>
      match acc, id? with
      | some arr, some id => some (arr.push id)
      | _, _ => none
  let some invIds := invIds? | return #[]
  if invIds.isEmpty then return #[]
  let initPf : Term ← match invIds.toList with
    | [id0] => `(($id0:ident).1)
    | id0 :: rest =>
        rest.foldlM (init := ← `(($id0:ident).1)) fun acc id => `(And.intro $acc ($id:ident).1)
    | [] => `(trivial)
  let sVar := mkIdent `_s
  let mVar := mkIdent `_m
  let hVar := mkIdent `_h
  let stepPf ← mkSpecStepPf sVar mVar invIds.toList.reverse hVar
  mkSpecPropPair spec "inv"
    (← `(Qed.SpecEngine.SpecInv ($inv)))
    (← `(Qed.Internal.App.withSpeculative_init_inv $clsIdent $baseAppIdent $initPf))
    (← `(Qed.Internal.App.withSpeculative_step_inv $clsIdent $baseAppIdent (fun $sVar $mVar $hVar => $stepPf)))

private def mkSpecCoreCmds (spec : ComponentSpec) (baseAppIdent clsIdent : Ident) (finalApp : Term) :
    CommandElabM (Array (TSyntax `command)) := do
  let doc? := spec.doc?
  let cohCmds ← mkSpecPropPair spec "coherent"
    (← `(Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1)))
    (← `(Qed.Internal.App.withSpeculative_init_coherent $clsIdent $baseAppIdent))
    (← `(Qed.Internal.App.withSpeculative_step_coherent $clsIdent $baseAppIdent))
  let wfCmds ← mkSpecPropPair spec "wellFormedIds"
    (← `(Qed.SpecEngine.WellFormedIds))
    (← `(Qed.Internal.App.withSpeculative_init_wellFormedIds $clsIdent $baseAppIdent))
    (← `(Qed.Internal.App.withSpeculative_step_wellFormedIds $clsIdent $baseAppIdent))
  return #[
    ← `(command| def $baseAppIdent : App $(spec.stateId) $(spec.msgId) := $finalApp),
    ← `(command| $[$doc?:docComment]? def $(spec.id `app) :
      App (Qed.SpecState $(spec.stateId) $(spec.msgId)) $(spec.msgId) :=
      Qed.Internal.App.withSpeculative $clsIdent $baseAppIdent)
  ] ++ cohCmds ++ wfCmds

private def mkRehydrateInvCmds (spec : ComponentSpec) (specBaseApp? : Option Ident)
    (compInv? : Option Term) (hasDecInv : Bool) : CommandElabM (Array (TSyntax `command)) := do
  let some inv := compInv? | return #[]
  let appIdent := spec.id `app
  let (stTy, invWrap) ← match specBaseApp? with
    | some _ => pure (← `(Qed.SpecState $(spec.stateId) $(spec.msgId)), ← `(Qed.SpecEngine.SpecInv ($inv)))
    | none   => pure ((spec.stateId : Term), inv)
  if hasDecInv then
    let pf ← match specBaseApp? with
      | some _ => `(Qed.Internal.App.withSpeculative_rehydrate_sound _ _ (Qed.App.guardRehydrate_sound _ _ _) raw st')
      | none   => `(Qed.App.guardRehydrate_sound _ _ _ raw st')
    pure #[← `(command|
      theorem $(spec.id `rehydrate_inv) (raw : String) (st' : $stTy) :
          ($appIdent).rehydrate raw = some st' → ($invWrap) st' := $pf)]
  else
    let pf ← match specBaseApp? with
      | some baseAppId =>
          `(Qed.Internal.App.withSpeculative_dehydrate_inv _ _ (by dsimp only [$baseAppId:ident]; qedProveDehydrateInv))
      | none => `(by dsimp only [$appIdent:ident]; qedProveDehydrateInv)
    pure #[← `(command|
      theorem $(spec.id `dehydrate_inv) :
          ∀ st st', ($invWrap) st → ($appIdent).rehydrate (($appIdent).dehydrate st) = some st' → ($invWrap) st' := $pf)]

private def mkViewEqThm (thmId appId viewId stateId : Ident) : CommandElabM (TSyntax `command) :=
  `(command|
    theorem $thmId (s : $stateId) :
        Qed.Html.canonical (Qed.App.view $appId s) = Qed.Html.canonical ($viewId s) := by
      qedProveViewEquiv $appId $viewId)

private def mkSpecAppCmds (spec : ComponentSpec) (finalApp : Term) (compInv? : Option Term)
    (hasDecInv : Bool) (stateInvEntries : Array (Term × Option Ident))
    (initCmds : Array (TSyntax `command)) :
    CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let appIdent := spec.id `app
  let baseAppIdent := spec.id `_baseApp
  let clsIdent := spec.id `_specClassify
  let mut cmds := initCmds ++ (← mkSpecCoreCmds spec baseAppIdent clsIdent finalApp)
  if spec.queries.isEmpty && spec.subscriptions.isEmpty then
    if let some inv := compInv? then
      cmds := cmds ++ (← mkSpecInvThmCmds spec baseAppIdent clsIdent inv stateInvEntries)
  cmds := cmds ++ (← mkRehydrateInvCmds spec (some baseAppIdent) compInv? hasDecInv)
  let baseViewEqIdent := spec.id `_base_app_view_eq
  cmds := cmds.push (← mkViewEqThm baseViewEqIdent baseAppIdent spec.viewId spec.stateId)
  let appViewEqCmd ← `(command|
    theorem $(spec.id `app_view_eq) (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) :
        Qed.Html.canonical (Qed.App.view $appIdent st) = Qed.Html.canonical ($(spec.viewId) st.visible) := by
      simpa [Qed.Internal.App.withSpeculative_view, $appIdent:ident] using $baseViewEqIdent st.visible)
  return (cmds, appViewEqCmd)

private def resolveThemeStyles (themes : Array Ident) : CommandElabM (Array Term) := do
  let env ← getEnv; let currNs ← getCurrNamespace; let openDecls := (← getScope).openDecls
  let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
  themes.mapM fun thId => do
    let some thInfo := Qed.StyleDsl.resolveInRegistry thReg env currNs openDecls thId.getId.toString
      | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
    return mkIdentFrom thId thInfo.styleConst

private def applyHeadDirectives (hmId stId : Ident) (dirs : Array Syntax) (tail : Term) :
    CommandElabM Term := do
  dirs.foldrM (init := tail) fun d acc => do
    match d.getKind with
    | `Qed.compHeadTitle | `Qed.compHeadDescription | `Qed.compHeadCanonical =>
        let v ← lowerCompExpr .val (d.getArg 1)
        let fId := mkIdent <| match d.getKind with
          | `Qed.compHeadTitle => `title | `Qed.compHeadDescription => `description | _ => `canonical
        `(let $hmId:ident := { $hmId with $fId:ident := Option.some ($v : String) }; $acc)
    | `Qed.compHeadMeta =>
        let k ← lowerCompExpr .val (d.getArg 1)
        let v ← lowerCompExpr .val (d.getArg 3)
        `(let $hmId:ident := { $hmId with metaTags := ($hmId).metaTags ++ [(($k : String), ($v : String))] }; $acc)
    | `Qed.compHeadStatus =>
        let n ← lowerCompExpr .val (d.getArg 1)
        `(let $stId:ident : Nat := $n; $acc)
    | `Qed.compHeadRedirect =>
        let u ← lowerCompExpr .val (d.getArg 1)
        let optSt := d.getArg 2
        let stT ← if optSt.getNumArgs == 4 then lowerCompExpr .val (optSt.getArg 3) else `((302 : Nat))
        `(let $hmId:ident := { $hmId with redirect := Option.some ($u : String) };
          let $stId:ident : Nat := $stT; $acc)
    | _ =>
        throwErrorAt d "unexpected directive in `head:`"

private def mkCompHeadCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  let some headStx := spec.headClause? | return none
  let hmId := mkIdent `_qed_hm
  let stId := mkIdent `_qed_st
  let items := (headStx.getArg 2).getArgs
  let mut sharedDirs : Array Syntax := #[]
  let mut caseItems : Array Syntax := #[]
  for item in items do
    if item.getKind == `Qed.compHeadCase then
      caseItems := caseItems.push item
    else
      if !caseItems.isEmpty then
        throwErrorAt item "shared `head:` directives must appear before `case` arms"
      sharedDirs := sharedDirs.push item
  let coreTail : Term ←
    if caseItems.isEmpty then
      `(($hmId, $stId))
    else
      let some rd := spec.route?
        | throwErrorAt caseItems[0]! s!"`case` inside `head:` requires a `route` declaration on `component {spec.t.getId}`"
      let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for c in caseItems do
        let rawPats := (c.getArg 1).getSepArgs
        let armDirs := (c.getArg 3).getArgs
        let armBody ← applyHeadDirectives hmId stId armDirs (← `(($hmId, $stId)))
        for p in rawPats do
          let patT ← liftMacroM (lowerQedPat p)
          alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $patT => $armBody))
      `(match $(rd.field):ident with $[$alts:matchAlt]*)
  let withDirs ← applyHeadDirectives hmId stId sharedDirs coreTail
  let fullBody ← `(let $hmId:ident : Qed.HeadMeta := {}; let $stId:ident : Nat := 200; $withDirs)
  let boundBody ← bindMentionedFields spec (mentionsIdent fullBody.raw) fullBody
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(spec.id `headInfo) (s : $(spec.stateId)) : Qed.HeadMeta × Nat := $boundBody))

private def buildCompFinalApp (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvPreds : Array Term) :
    CommandElabM (Array (TSyntax `command) × Term × Option Term × Bool) := do
  let mut cmds : Array (TSyntax `command) := #[]
  let startArg : Term ← if hasStart then `($(spec.id `startCmd)) else `(Qed.Cmd.none)
  let onPortArg : Term ← if spec.portIns.isEmpty then `(Option.none) else do
    let onPortId := spec.id `onPort
    let inTuples ← spec.portIns.mapM fun p => do
      let pLit := Syntax.mkStrLit p.id.getId.toString
      `(($pLit, fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $(spec.msgCtor p.id.getId)))
    cmds := cmds.push (← `(command| def $onPortId : String → String → Option $(spec.msgId) :=
      dispatchPorts #[$inTuples,*]))
    `(some $onPortId)
  let expandedBody ← liftMacroM <| Qed.Jsx.expandJsxIn body'.raw
  let mut templateTerm : Term := ⟨← liftMacroM <|
    Qed.Internal.liftViewWithFields (mkIdent `_qed_s) (spec.states.map (·.id)) expandedBody⟩
  for po in spec.portOuts.reverse do
    if mentionsIdent templateTerm.raw po.id.getId then
      let poId := mkIdent po.id.getId
      templateTerm ← `(let $poId:ident := $(spec.id po.id.getId); $templateTerm)
  let appUpdate : Term ← if spec.hasEffects then `($(spec.updateId))
    else `(fun s m => ($(spec.updateId) s m, Qed.Cmd.none))
  let onSessionArg : Term ← match spec.sessionField? with
    | some _ => `(some $(spec.msgCtor `_onSession))
    | none   => `(none)
  let app0 : Term ← match spec.route? with
    | some _ => `(Qed.Internal.mkRoutedApp $(spec.initId) $appUpdate $templateTerm
        (onRoute := $(spec.msgCtor `_onRoute)) (onSession := $onSessionArg)
        (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg))
    | none   => `(Qed.Internal.mkApp $(spec.initId) $appUpdate $templateTerm (onSession := $onSessionArg)
        (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg))
  let mut appT : Term := app0
  if !spec.themes.isEmpty then
    let thStyleTerms ← resolveThemeStyles spec.themes
    appT ← `(Qed.Internal.App.withExtraStyles [$[$thStyleTerms],*] $appT)
  if !spec.stylesheets.isEmpty then
    let shLits := spec.stylesheets.map Syntax.mkStrLit
    appT ← `(Qed.Internal.App.withStylesheets [$[$shLits:str],*] $appT)
  appT ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $(spec.initId) $appT)
    else `(Qed.Internal.App.withDehydrate (Dehydrate.except $(spec.initId) [$[$spec.ephemeralFields:ident],*]) $appT)
  if !spec.queries.isEmpty then
    appT ← `(Qed.Internal.App.withQueries $(spec.id `queries) $appT)
  if !spec.subscriptions.isEmpty then
    appT ← `(Qed.Internal.App.withSubscriptions $(spec.id `subscriptions) $appT)
  if spec.headClause?.isSome then
    let headInfoId := spec.id `headInfo
    appT ← `(Qed.App.withSsrStatus (fun _s => ($headInfoId _s).2) (Qed.App.withHead (fun _s => ($headInfoId _s).1) $appT))
  let compInv? : Option Term ← if stateInvPreds.isEmpty then pure none
    else if stateInvPreds.size == 1 then pure (some (← `(($(stateInvPreds[0]!) : $(spec.stateId) → Prop))))
    else do
      let sVar := mkIdent `_qed_s
      let checks ← stateInvPreds.mapM fun p => `(($p) $sVar)
      pure (some (← `(fun ($sVar:ident : $(spec.stateId)) => $(← mkConjBody checks))))
  let hasDecInv ← match compInv? with
    | some inv => canSynthDecidablePred spec.stateId inv
    | none     => pure false
  if let (some inv, true) := (compInv?, hasDecInv) then
    appT ← `(Qed.App.guardRehydrate ($inv) $appT)
  return (cmds, appT, compInv?, hasDecInv)

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvEntries : Array (Term × Option Ident)) : CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let (initCmds, finalApp, compInv?, hasDecInv) ←
    buildCompFinalApp spec body' hasStart (stateInvEntries.map (·.1))
  if spec.hasSpeculative then
    return ← mkSpecAppCmds spec finalApp compInv? hasDecInv stateInvEntries initCmds
  let doc? := spec.doc?
  let appIdent := spec.id `app
  let cmds := initCmds.push (← `(command| $[$doc?:docComment]? def $appIdent : App $(spec.stateId) $(spec.msgId) :=
    $finalApp)) ++ (← mkRehydrateInvCmds spec none compInv? hasDecInv)
  return (cmds, ← mkViewEqThm (spec.id `app_view_eq) appIdent spec.viewId spec.stateId)

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command) × Bool × Bool) := do
  let tId := spec.t.getId
  let fs := spec.states.map (·.id)
  let mut cmds : Array (TSyntax `command) := #[]
  if spec.mountable then
    let dsT := spec.states.filterMap (·.def?)
    cmds := cmds.push (← `(command| def $(spec.initId) : $(spec.stateId) := { $[$fs:ident := $dsT],* }))
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart)
  let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  if hasStart then
    let pBinders ← mkPropsBinders spec
    let subStarts ← hoistedStarts.mapM fun h => do
      let cStart := mkIdent (h.info.fullName ++ `startCmd)
      let call ← if h.info.hasProps then `($cStart $(← mkHoistedPropsTerm h)) else `($cStart)
      `(Cmd.map $(spec.msgCtor h.ctorName) $call)
    let mut startBody ← mkCmdBatch (starts' ++ subStarts)
    if spec.mountable then
      startBody ← bindMentionedFields spec (mentionsIdent startBody.raw) startBody
      if mentionsIdent startBody.raw `s then
        startBody ← `(let s := $(spec.initId); $startBody)
    cmds := cmds.push (← `(command| def $(spec.id `startCmd) $[$pBinders:bracketedBinder]* : Cmd $(spec.msgId) := $startBody))
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
    cmds := cmds ++ (← mkCompStructJsonCmds (tId ++ `Props) spec.props) ++ (← mkCompStructJsonCmds (tId ++ `State) spec.states)
  if spec.outTy?.isSome && outJsonOk then
    cmds := cmds ++ (← mkOutJsonCmds tId outCtorSpecs)
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && canEmitCodecs && outJsonOk
  if hasLocalDef then
    cmds := cmds ++ (← mkCompLocalDefCmds spec idLit)
  let own : Term ← if hasLocalDef then `([$(spec.id `reg)]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $(spec.id `regs) : List LocalDef :=
    LocalDef.dedupe ($own ++ qedInternalLocalRegistrations% $(spec.viewId))))
  return (cmds, hasStart, hasLocalDef)


private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then
    withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k
  else k

private def elabCompStyles (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
  for stCl in rawSpec.styles do
    withOpenNs compNs do
      let sNameId : Ident := ⟨stCl.getArg 1⟩
      Qed.StyleDsl.elabStyleDef none (mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId))
        (Qed.StyleDsl.extractStyleExtends (stCl.getArg 2)) ((stCl.getArg 3).getNumArgs == 1) (stCl.getArg 5).getArgs

private def collectCompEndpoints (rawSpec : ComponentSpec) (hoisted : Array HoistedSub)
    (ownUsedRpcs : Array (String × String)) : Array (String × String) × Array (String × String) := Id.run do
  let mut allUsedRpcs := ownUsedRpcs
  let mut allUsedChannels : Array (String × String) := #[]
  for sub in rawSpec.subscriptions do
    if let .fullstack _ srvShort _ := sub.chInfo.kind then
      allUsedChannels := pushUnique allUsedChannels (srvShort, sub.chInfo.channelName)
  for h in hoisted do
    allUsedRpcs := h.info.usedRpcs.foldl pushUnique allUsedRpcs
    allUsedChannels := h.info.usedChannels.foldl pushUnique allUsedChannels
  return (allUsedRpcs, allUsedChannels)

private def elabCompRegistryAndMeta (spec : ComponentSpec) (hasStart hasLocalDef : Bool)
    (allUsedRpcs allUsedChannels : Array (String × String)) : CommandElabM Unit := do
  let elabPairListDef (defName : Name) (pairs : Array (String × String)) : CommandElabM Unit := do
    let ts ← pairs.mapM fun (a, b) => `((($(Syntax.mkStrLit a), $(Syntax.mkStrLit b)) : String × String))
    elabCommand (← `(command| def $(mkIdent (spec.t.getId ++ defName)) : List (String × String) := [$[$ts],*]))
  elabPairListDef `usedRpcs allUsedRpcs
  elabPairListDef `usedChannels allUsedChannels
  let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
  modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
    hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects,
    hasStart, mountable := spec.mountable, hasLocalDef,
    usedRpcs := allUsedRpcs, usedChannels := allUsedChannels }

private def elabStatefulComponentBody (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
  if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
      rawSpec.starts.isEmpty && rawSpec.sessionField?.isNone &&
      rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty &&
      rawSpec.subscriptions.isEmpty && rawSpec.headClause?.isNone then
    let rCtx ← mkRewriteCtx rawSpec true (allowHoist := true)
    let body' ← lowerCompExpr .val (← rewriteIn rCtx false rawSpec.body)
    if (← rCtx.hoisted.get).isEmpty && (← rCtx.formDrafts.get).isEmpty && (← rCtx.resetForms.get).isEmpty then
      elabPureComponent rawSpec body'
      return
  let idLit := Syntax.mkStrLit compNs.toString
  let rw ← collectSitesAndRewriteStateful rawSpec
  if let some rs0 := rw.specResolves[0]? then
    checkTopLevelMountable rawSpec rs0.callRef "speculative `predict`"
  let (allUsedRpcs, allUsedChannels) := collectCompEndpoints rawSpec rw.hoisted rw.usedRpcs
  let eventNames := rawSpec.events.map (·.id.getId)
  let ownHasEffects :=
    !rw.starts.isEmpty ||
    !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty || !rawSpec.queries.isEmpty ||
    !rawSpec.subscriptions.isEmpty ||
    !rw.specResolves.isEmpty ||
    rw.sites.any (fun s => s.stmts?.any (·.any (hasEffectStmt eventNames))) ||
    (rw.route?.any fun rd => rd.alts.any (hasEffectStmt eventNames)) ||
    rw.hoisted.any (·.info.hasEffects)
  let spec ← elabStructsAndResolveTypes {
    rawSpec with route? := rw.route?, hasEffects := ownHasEffects,
                 usedRpcs := allUsedRpcs, usedChannels := allUsedChannels,
                 specDispatches := rw.specDispatches, specNodes := rw.specNodes, specResolves := rw.specResolves
  } rw.hoisted rw.formDrafts rw.resetForms
  currentCompSessionRef.set spec.sessionField?
  let errsBefore ← getErrorCount
  let coreCmds ← mkViewCmds spec rw.body (← mkMsgAndUpdateCmds spec rw.sites)
  for c in coreCmds do elabCommand c
  let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec rw.starts idLit
  for c in mountCmds do elabCommand c
  let isTopMount := spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids
  if isTopMount then
    if let some qCmd ← mkCompQueriesCmd? spec then elabCommand qCmd
    if let some sCmd ← mkCompSubscriptionsCmd? spec then elabCommand sCmd
    if let some hCmd ← mkCompHeadCmd? spec then elabCommand hCmd
    for clsCmd in (← mkSpecClassifyCmds spec) do elabCommand clsCmd
  let stateInvEntries ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
  let errsAfterInvs ← getErrorCount
  let activeInvEntries := if errsAfterInvs == errsBefore then stateInvEntries else #[]
  if errsAfterInvs == errsBefore then
    withOpenNs compNs (elabCompReachableAndWitnesses spec)
  verifyPendingRpcChecks spec (activeInvEntries.map (·.1))
  if isTopMount then
    let (appCmds, eqCmd) ← mkCompAppCmds spec rw.body hasStart activeInvEntries
    for c in appCmds do elabCommand c
    if (← getErrorCount) == errsBefore then elabCommand eqCmd
  let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
  elabCompRegistryAndMeta spec hasStart hasLocalDef allUsedRpcs allUsedChannels

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let errsInit ← getErrorCount
  let priorTasks := (← get).snapshotTasks.size
  let compNs := (← getCurrNamespace) ++ (stx.getArg 2).getId
  pendingRpcChecks.set #[]
  pendingPredictChecks.set #[]
  currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    elabCompStyles compNs rawSpec
    withOpenNs compNs (elabStatefulComponentBody compNs rawSpec)
    okRef.set true
  finally
    pendingRpcChecks.set #[]
    pendingPredictChecks.set #[]
    currentCompSessionRef.set none
    let errsEnd ← getErrorCount
    let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
    let asyncErr := newTasks.any fun t => Qed.Diag.snapshotTreeHasErrors 64 t.get
    if !(← okRef.get) || errsEnd > errsInit || asyncErr then
      setEnv savedEnv

end CompElab
end Qed
