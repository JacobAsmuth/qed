import Qed.Component.Rewrite
import Qed.Runtime
import Qed.Invariant.ForEach

namespace Qed
section CompElab
open Lean Elab Command

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
    let clauses : Array Term := invStx[2].getSepArgs.map (⟨·⟩)
    if clauses.size != 1 then
      throwErrorAt invStx "a pure component has no local state; only single-clause view styling invariants apply"
    let vPred := clauses[0]!
    let predStr := (vPred.raw.reprint.getD "this rule").trimmed
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

private def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub) :
    CommandElabM ComponentSpec := do
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
  let allStates := spec.states ++ hoisted.map fun h => {
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
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted }

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

private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (assigns : Array (Name × Option Term)) (out? : Option Term) (cmds : Array Term)
    (stmts : List Syntax) : CommandElabM Term := do
  match stmts with
  | [] => mkUpdateRet spec (← flushAssigns sBase assigns) out? cmds
  | s :: rest =>
      let sk := s.getKind
      if sk == ``actionNoopStmt then
        compileStmts spec sBase assigns out? cmds rest
      else if sk == ``actionReturnStmt then
        mkUpdateRet spec (← flushAssigns sBase assigns) out? cmds
      else if sk == ``actionLetStmt then
        let lId : Ident := ⟨s[1]⟩; let lVal : Term := ⟨s[4]⟩
        let cont ← compileStmts spec sBase assigns out? cmds rest
        if s[2].getNumArgs == 2 then
          let lTy : Term := ⟨s[2][1]⟩
          `(let $lId:ident : $lTy := $lVal; $cont)
        else `(let $lId:ident := $lVal; $cont)
      else if sk == ``actionAssignStmt then
        let fId : Ident := ⟨s[0]⟩
        let fname := fId.getId.eraseMacroScopes
        let expr? : Option Term ←
          if atomStr s[1] == ":=" && isCdot s[2] then pure none
          else some <$> desugarAssign fname (atomStr s[1]) ⟨s[2]⟩
        if spec.bindNames.contains fname then
          if out?.isSome then throwErrorAt s "duplicate output in action"
          let outCtor := mkIdent (spec.t.getId ++ `Out ++ Name.mkSimple s!"set_{fname}")
          let oTerm ← `($outCtor $(← expr?.getDM `(v)))
          return ← compileStmts spec sBase assigns (some oTerm) cmds rest
        unless spec.fieldNames.contains fname do
          throwErrorAt fId "`{fname}`: not a `state` field of this component (fields: {spec.fieldNames.toList})"
        if assigns.any (·.1 == fname) then
          throwErrorAt fId "`{fname}`: this handler already updates `{fname}`"
        compileStmts spec sBase (assigns.push (fname, expr?)) out? cmds rest
      else if sk == ``actionSendStmt then
        unless spec.outTy?.isSome do noEmitsErr s
        if out?.isSome then throwErrorAt s "duplicate `send` in action; an action emits at most one output"
        compileStmts spec sBase assigns (some ⟨s[1]⟩) cmds rest
      else if sk == ``actionPerformStmt then
        compileStmts spec sBase assigns out? (cmds.push ⟨s[1]⟩) rest
      else if sk == ``actionIfStmt || sk == ``actionIfLetStmt || sk == ``actionMatchStmt then
        let passTail := !rest.isEmpty && hasReturnStmt s
        let sFlushed ← flushAssigns sBase assigns
        let preId := mkIdent `_qedPre
        let (brBase, wrapPre) := if passTail && !assigns.isEmpty then ((preId : Term), true) else (sFlushed, false)
        let tailStmts := if passTail then rest else []
        let compileBranch (seq : Array Syntax) := compileStmts spec brBase #[] out? cmds (seq.toList ++ tailStmts)
        let compileOptElse (opt : Syntax) :=
          compileBranch (if opt.getNumArgs == 2 then unpackSeq opt[1] else #[])
        let branchTerm ←
          if sk == ``actionIfStmt then
            let cond : Term := ⟨s[2]⟩
            let tT ← compileBranch (unpackSeq s[4]); let eT ← compileOptElse s[5]
            if s[1].getNumArgs > 0 then
              let hId : Ident := ⟨s[1][0]⟩
              `(if $hId:ident : $cond then $tT else $eT)
            else `(if $cond then $tT else $eT)
          else if sk == ``actionIfLetStmt then
            let pat : Term := ⟨s[2]⟩; let scrut : Term := ⟨s[4]⟩
            `(if let $pat := $scrut then $(← compileBranch (unpackSeq s[6])) else $(← compileOptElse s[7]))
          else
            let scruts : Array Term := s[1].getSepArgs.map (⟨·⟩)
            let alts ← s[3].getArgs.mapM fun alt => do
              let pats : Array Term := alt[1].getSepArgs.map (⟨·⟩)
              `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $(← compileBranch (unpackSeq alt[3])))
            `(match $[$scruts:term],* with $[$alts:matchAlt]*)
        if passTail then
          let mut br := branchTerm
          if wrapPre then
            for (fn, _) in assigns.reverse do
              if tailStmts.any (mentionsIdent · fn) then
                let fId := mkIdent fn
                br ← `(let $fId:ident := ($preId).$fId:ident; $br)
            br ← `(let $preId:ident := $sFlushed; $br)
          return br
        if rest.isEmpty then return branchTerm
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
        throwErrorAt s "unsupported statement in component action"

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
  if spec.outTy?.isSome then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_emit):ident (_o : $(mkIdent (tId ++ `Out)))))
  for (colField, colChild) in spec.collections do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent colField.getId):ident (key : String) (msg : $(mkIdent (colChild.getId ++ `Msg)))))
  for q in spec.queries do
    let qCtor := mkIdent q.ctorName
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $qCtor:ident (key : String) (res : Resource $(q.ty))))
  for h in spec.hoisted do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent h.ctorName):ident (msg : $(mkIdent (h.info.fullName ++ `Msg)))))
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
            ![``actionAssignStmt, ``actionSendStmt, ``actionPerformStmt,
              ``actionIfStmt, ``actionIfLetStmt, ``actionMatchStmt, ``actionNoopStmt].contains st.getKind
          if isPureNoop then throwErrorAt stmts[0]! "an action must update state, perform an effect, or send an output"
          compileStmts spec (← `(s)) #[] none #[] stmts.toList
      | none => do mkUpdateRet spec (← flushAssigns (← `(s)) site.assigns) site.send? #[])
    if let some guard := site.guard? then rhs ← `(if $guard then $rhs else $unchanged)
    rhs ← bindMentionedFields spec (fun g =>
      (site.stmts?.any (·.any (mentionsIdent · g))) ||
      (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
      (site.send?.any (mentionsIdent ·.raw g)) ||
      (site.guard?.any (mentionsIdent ·.raw g))) rhs
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
          let pats : Array Term := alt[1].getSepArgs.map (⟨·⟩)
          `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* =>
              $(← compileStmts spec sWithR #[] none #[] (unpackSeq alt[3]).toList))
        `(match $rVal:ident with $[$alts:matchAlt]*))
    rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
    rhs ← `(let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $rVal:ident => $rhs))
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
    let keyBound ← bindMentionedFields spec (mentionsIdent q.keyExpr.raw) q.keyExpr
    let next ← `({ s with $qNm:ident := (s.$qNm:ident).put _qk _qr $keyBound })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $qCtor:ident _qk _qr => $(← mkUpdateRet spec next none #[])))
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
  let stepOwnCmd ← `(command| def $stepOwnId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy :=
    fun m => match m with $[$(ownArms ++ subNoopArms):matchAlt]*)
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
  let outCmds ← mkMsgInductiveCmds spec sites
  let unchanged ← mkUpdateRet spec (← `(s)) none #[]
  let ownArms ← mkOwnUpdateArms spec sites unchanged
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none,   false => `($stateId)
    | some o, false => `($stateId × Option $o)
    | none,   true  => `($stateId × Cmd $msgId)
    | some o, true  => `($stateId × Option $o × Cmd $msgId)
  let pBinders ← mkPropsBinders spec
  if spec.hoisted.isEmpty then
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

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool) :
    CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
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
  let baseApp : Term ← match spec.route? with
    | some _ => `(Qed.Internal.mkRoutedApp $initId $appUpdate $templateTerm
        (onRoute := $(mkIdent (tId ++ `Msg ++ `_onRoute))) (start := $startArg)
        (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
    | none   => `(Qed.Internal.mkApp $initId $appUpdate $templateTerm (start := $startArg)
        (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
  let dehydApp : Term ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $initId $baseApp)
    else `(Qed.Internal.App.withDehydrate (Dehydrate.except $initId [$[$spec.ephemeralFields:ident],*]) $baseApp)
  let finalApp : Term ← if spec.queries.isEmpty then pure dehydApp else do
    let qTerms ← spec.queries.mapM fun q => do
      let qNm := q.id
      let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
      let keyBound ← bindMentionedFields spec (mentionsIdent q.keyExpr.raw) q.keyExpr
      `(Resource.query
          (key := fun (s : $stateId) => $keyBound)
          (url := $(q.urlExpr))
          (got := $qCtor)
          (get := fun (s : $stateId) => s.$qNm:ident)
          (set := fun c (s : $stateId) => { s with $qNm:ident := c }))
    `(Qed.Internal.App.withQueries [$[$qTerms],*] $dehydApp)
  let appIdent := mkIdent (tId ++ `app)
  let viewIdent := mkIdent (tId ++ `view)
  cmds := cmds.push (← `(command| $[$doc?:docComment]? def $appIdent : App $stateId $msgId :=
    $finalApp))
  let appViewEqCmd ← `(command|
    theorem $(mkIdent (tId ++ `app_view_eq)) (s : $stateId) :
        Qed.Html.canonical (Qed.App.view $appIdent s) = Qed.Html.canonical ($viewIdent s) := by
      qedProveViewEquiv $appIdent $viewIdent)
  return (cmds, appViewEqCmd)

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (body' : Term) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command) × Bool × Bool × Option (TSyntax `command)) := do
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
  let mut appViewEqCmd? : Option (TSyntax `command) := none
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
  if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
    let (appCmds, eqCmd) ← mkCompAppCmds spec body' hasStart
    cmds := cmds ++ appCmds
    appViewEqCmd? := some eqCmd
  return (cmds, hasStart, hasLocalDef, appViewEqCmd?)

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

private def elabForEachInlineInv (spec : ComponentSpec) (invStx : Syntax) : CommandElabM Unit := do
  let tId      := spec.t.getId
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let invId ← resolveInvIdent invStx tId
  let pred : Term := ⟨invStx[2]⟩
  let colField : Ident := ⟨invStx[4]⟩
  let hasHoldsIn := invStx[5].getNumArgs > 0
  let using? : Option Ident := if invStx[6].getNumArgs == 2 then some ⟨invStx[6][1]⟩ else none
  let pf? : Option Term := if invStx[7].getNumArgs == 2 then some ⟨invStx[7][1]⟩ else none
  let probeId? := using?.or (if pred.raw.isIdent then some ⟨pred.raw⟩ else none)
  let isStyled ← if hasHoldsIn then pure true
    else match probeId? with
    | some pid =>
        liftTermElabM do
          try
            let cn ← realizeGlobalConstNoOverload pid
            Meta.forallTelescope (← getConstInfo cn).type fun _ body => return body.eq?.isSome
          catch _ => return false
    | none => pure false
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

private def elabViewInlineInv (spec : ComponentSpec) (invStx : Syntax) (invId : Ident)
    (clauses : Array Term) (assume? pf? : Option Term) : CommandElabM Unit := do
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  if clauses.size != 1 then throwErrorAt invStx[2] "a view styling invariant takes a single styling rule"
  let vPred := clauses[0]!
  if spec.hasProps then
    let predStr := (vPred.raw.reprint.getD "this rule").trimmed
    let rhs ← pf?.getDM `(by
      let _qed_hv := $viewId p
      change ∀ m, ($vPred) (_qed_hv m) = true
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := $rhs))
  else
    elabCommand (← `(invariant $invId : $vPred holds_in $viewId $[assuming $assume?]? $[ := $pf?]?))
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
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical])
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical])).trans
                    ($invId m ha)))
        | none =>
            elabCommand (← `(command| set_option linter.unusedSimpArgs false in
              theorem $appInvId : ∀ m, ($vPred) (Qed.App.view $appId m) = true :=
                fun m =>
                  (Qed.canonical_congr_pred ($appViewEqId m)
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical])
                    (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical])).trans
                    ($invId m)))
      catch _ => set saved

private def elabStateInlineInv (spec : ComponentSpec) (invId : Ident)
    (clauses : Array Term) (using? : Option (Array Term)) (pf? : Option Term) : CommandElabM Unit := do
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let initId   := mkIdent (tId ++ `init)
  let updateId := mkIdent (tId ++ `update)
  let conj ← mkConjBody clauses
  let pred ← `(fun (s : $stateId) => $(← bindMentionedFields spec (mentionsIdent conj.raw) conj))
  let usingL := using?.getD #[]
  if spec.hasProps then
    let rhs ← pf?.getDM `(by qedDischargePreserved [$[$usingL],*] ($updateId p) $invId ($pred))
    elabCommand (← `(theorem $invId:ident (p : $propsId) :
      ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := $rhs))
  else
    let stepPf? ← pf?.mapM fun pf =>
      if spec.mountable then
        `(by exact ⟨by first | rfl | decide | (simp [$initId:ident]; decide) | (simp [$initId:ident]; omega), $pf⟩)
      else pure pf
    let initOpt? : Option Term := if spec.mountable then some initId else none
    elabCommand (← `(qedInternalInvariant $invId : $pred $[from $initOpt?]? preserved_by $updateId using [$[$usingL],*] $[ := $stepPf?]?))

private def elabInlineInvariants (spec : ComponentSpec) : CommandElabM Unit := do
  let tId   := spec.t.getId
  let msgId := mkIdent (tId ++ `Msg)
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      elabForEachInlineInv spec invStx
      continue
    let invId ← resolveInvIdent invStx tId
    let clauses : Array Term := invStx[2].getSepArgs.map (⟨·⟩)
    let hasHoldsIn := invStx[3].getNumArgs > 0
    let assume? : Option Term :=
      if hasHoldsIn && invStx[3][2].getNumArgs == 2 then some ⟨invStx[3][2][1]⟩ else none
    let using? : Option (Array Term) :=
      if invStx[4].getNumArgs == 4 then some (invStx[4][2].getSepArgs.map (⟨·⟩)) else none
    let pf? : Option Term := if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let autoView ← if !hasHoldsIn && clauses.size == 1 && using?.isNone &&
        !spec.allNames.any (mentionsIdent clauses[0]!.raw) then
      isViewPred msgId clauses[0]!
    else pure false
    if hasHoldsIn || autoView then
      elabViewInlineInv spec invStx invId clauses assume? pf?
    else
      elabStateInlineInv spec invId clauses using? pf?

private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then
    withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k
  else k

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let compNs := (← getCurrNamespace) ++ stx[2].getId
  withOpenNs compNs do
    let rawSpec ← parseComponentSpec stx
    if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
        rawSpec.starts.isEmpty &&
        rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty then
      let sitesRef ← IO.mkRef #[]
      let hoistedRef ← IO.mkRef #[]
      let rCtx : RewriteCtx := {
        stateFields := #[], bindFields := rawSpec.bindNames, isPureComp := true,
        msgPath := rawSpec.t.getId ++ `Msg, hasOut := false, collections := #[],
        sites := sitesRef, hoisted := hoistedRef, allowHoist := true }
      let body' : Term := ⟨← rewriteIn rCtx false rawSpec.body⟩
      if (← hoistedRef.get).isEmpty then
        return ← elabPureComponent rawSpec body'
    let idLit := Syntax.mkStrLit compNs.toString
    let (sites, route'?, queries', starts', body', hoisted) ← collectSitesAndRewriteStateful rawSpec
    let ownHasEffects :=
      !starts'.isEmpty ||
      !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty || !queries'.isEmpty ||
      sites.any (fun s => s.stmts?.any (·.any hasPerformNode)) ||
      (route'?.any fun rd => rd.alts.any hasPerformNode) ||
      hoisted.any (·.info.hasEffects)
    let spec ← elabStructsAndResolveTypes { rawSpec with route? := route'?, queries := queries', hasEffects := ownHasEffects } hoisted
    let errsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
    let coreCmds ← mkViewCmds spec body' (← mkMsgAndUpdateCmds spec sites)
    for c in coreCmds do elabCommand c
    let (mountCmds, hasStart, hasLocalDef, appViewEqCmd?) ← mkCodecAndMountCmds spec starts' body' idLit
    for c in mountCmds do elabCommand c
    let errsAfter := (← get).messages.toList.filter (·.severity == .error) |>.length
    if errsAfter == errsBefore then
      if let some eqCmd := appViewEqCmd? then elabCommand eqCmd
    withOpenNs compNs (elabInlineInvariants spec)
    let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
    modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
      hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects,
      hasStart, mountable := spec.mountable, hasLocalDef }

end CompElab
end Qed
