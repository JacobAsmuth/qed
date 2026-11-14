import Qed.Component.Core
import Qed.Runtime
import Lean

namespace Qed

open Lean Parser in
@[term_parser] def setTerm := leading_parser:maxPrec
  nonReservedSymbol "set" (includeIdent := true) >> Parser.ident >>
  optional (checkColGt >> termParser maxPrec) >>
  many (node `Qed.setMore
    (atomic (", " >> nonReservedSymbol "set" (includeIdent := true)) >> Parser.ident >>
     optional (checkColGt >> termParser maxPrec))) >>
  optional (", " >> nonReservedSymbol "send" (includeIdent := true) >> termParser maxPrec)

open Lean Parser in
@[term_parser] def sendTerm := leading_parser:maxPrec
  nonReservedSymbol "send" (includeIdent := true) >> termParser maxPrec

open Lean in
@[macro setTerm] def expandSetTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx
    "`set …` is the component state setter; it only has meaning inside a `component … view =>` body"

open Lean in
@[macro sendTerm] def expandSendTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx
    "`send …` is the component output; it only has meaning inside a `component … view =>` body"

open Lean Parser in
-- `identEq` keeps `component`/`state`/`key`/`view` non-reserved (note: an open-ended `def`/`#check`
-- right before `component` needs a `/-- ... -/` doc comment so Lean's term parser stops at the token);
-- `manyIndent` + `maxPrec` prevent clauses or JSX bodies from swallowing subsequent declarations.
@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >> atomic (identEq `component) >> ident >> " where " >>
  manyIndent (node `Qed.componentStateItem
    ((atomic (identEq `state) <|> atomic (identEq `prop) <|> atomic (identEq `collection)) >> ident >> " : " >> termParser >>
     optional (" := " >> termParser maxPrec))) >>
  optional (node `Qed.componentKey (atomic (identEq `key) >> ident)) >>
  optional (node `Qed.componentEmits (atomic (identEq `emits) >> termParser maxPrec)) >>
  manyIndent (node `Qed.componentAction (atomic (identEq `action) >> ident >> many (node `Qed.componentActionParam ("(" >> ident >> " : " >> termParser >> ")")) >> optional (atomic (identEq `when) >> termParser maxPrec) >> " => " >> termParser maxPrec)) >>
  identEq `view >> " => " >> termParser maxPrec

private structure SetSite where
  key     : String
  assigns : Array (Lean.Name × Option Lean.Term)
  ctor    : Lean.Name
  send?   : Option Lean.Term
  params  : Array (Lean.Ident × Lean.Term) := #[]
  guard?  : Option Lean.Term := none

private partial def mentionsIdent (stx : Lean.Syntax) (n : Lean.Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

open Lean Elab Command in
private def registerSite (sites : IO.Ref (Array SetSite))
    (assigns : Array (Name × Option Term)) (send? : Option Term) : CommandElabM Name := do
  let pp : Option Term → String := fun
    | some e => e.raw.reprint.getD (toString e.raw)
    | none   => "·"
  let key := String.intercalate "|" (assigns.toList.map fun (f, e?) => s!"{f}={pp e?}")
    ++ s!"|{pp send?}"
  let cur ← sites.get
  match cur.find? (·.key == key) with
  | some site => return site.ctor
  | none =>
      let base := if assigns.isEmpty then "send"
        else "set_" ++ String.intercalate "_" (assigns.toList.map (toString ·.1))
      let mut name := Name.mkSimple base
      let mut i := 2
      while cur.any (·.ctor == name) do
        name := Name.mkSimple s!"{base}_{i}"
        i := i + 1
      sites.set (cur.push { key, assigns, ctor := name, send? })
      return name

open Lean Elab Command in
private partial def replaceSets (fields : Array Name) (msgPath : Name) (hasEmits : Bool)
    (sites : IO.Ref (Array SetSite)) (stx : Syntax) : CommandElabM Syntax := do
  let noEmits (ref : Syntax) : CommandElabM Unit :=
    throwErrorAt ref "`send` bubbles an output, but this component declares no output type; \
      add `emits T` between the `state` fields and the `view`"
  if stx.getKind == ``setTerm then
    let mut assigns : Array (Name × Option Term) := #[]
    let pairs := #[(stx[1], stx[2])] ++ stx[3].getArgs.map fun more => (more[2], more[3])
    for (fId, eOpt) in pairs do
      let fname := fId.getId.eraseMacroScopes
      unless fields.contains fname do
        throwErrorAt fId "`set {fname}`: not a `state` field of this component (fields: {fields.toList})"
      if assigns.any (·.1 == fname) then
        throwErrorAt fId "`set {fname}`: this handler already sets `{fname}`"
      let expr? : Option Term := if eOpt.getNumArgs == 1 then some ⟨eOpt[0]⟩ else none
      if expr?.isNone && assigns.any (·.2.isNone) then
        throwErrorAt fId "`set {fname}`: only one payload-form `set` (no expression) per \
          handler, there is just one incoming value to store"
      assigns := assigns.push (fname, expr?)
    let send? : Option Term := if stx[4].getNumArgs == 3 then some ⟨stx[4][2]⟩ else none
    if send?.isSome && !hasEmits then noEmits stx[4]
    return mkIdent (msgPath ++ (← registerSite sites assigns send?))
  else if stx.getKind == ``sendTerm then
    unless hasEmits do noEmits stx
    return mkIdent (msgPath ++ (← registerSite sites #[] (some ⟨stx[1]⟩)))
  else
    match stx with
    | .node info kind args =>
        return .node info kind (← args.mapM (replaceSets fields msgPath hasEmits sites))
    | _ => return stx

open Lean Elab Command in
private structure ComponentSpec where
  doc?        : Option (TSyntax ``Lean.Parser.Command.docComment)
  t           : Ident
  collections : Array Syntax
  fs          : Array Ident
  tys         : Array Term
  ds          : Array (Option Term)
  pfs         : Array Ident
  ptys        : Array Term
  pds         : Array (Option Term)
  hasProps    : Bool
  keyF?       : Option Ident
  outTy?      : Option Term
  actions     : Array Syntax
  body        : Term
  fieldNames  : Array Name
  allNames    : Array Name

open Lean Elab Command in
private def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let t : Ident := ⟨stx[2]⟩
  let allItems := stx[4].getArgs
  let propItems := allItems.filter (fun it => it[0].getId == `prop)
  let collections := allItems.filter (fun it => it[0].getId == `collection)
  let items := allItems.filter (fun it => it[0].getId != `prop)
  let fs  : Array Ident := items.map fun it => ⟨it[1]⟩
  let tys : Array Term ← items.mapM fun it =>
    if it[0].getId == `collection then `(Array $(mkIdent (it[3].getId ++ `State)))
    else pure ⟨it[3]⟩
  let ds : Array (Option Term) ← items.mapM fun it =>
    if it[4].getNumArgs == 2 then pure (some ⟨it[4][1]⟩)
    else if it[0].getId == `collection then return some (← `(#[]))
    else pure none
  let pfs : Array Ident := propItems.map fun it => ⟨it[1]⟩
  let ptys : Array Term := propItems.map fun it => ⟨it[3]⟩
  let pds : Array (Option Term) := propItems.map fun it =>
    if it[4].getNumArgs == 2 then some ⟨it[4][1]⟩ else none
  let hasProps := !propItems.isEmpty
  let keyF?  : Option Ident := if stx[5].getNumArgs == 1 then some ⟨stx[5][0][1]⟩ else none
  let outTy? : Option Term  := if stx[6].getNumArgs == 1 then some ⟨stx[6][0][1]⟩ else none
  let actions := stx[7].getArgs
  let body : Term := ⟨stx[10]⟩
  let fieldNames := fs.map (·.getId)
  let allNames := fieldNames ++ pfs.map (·.getId)
  if allNames.toList.eraseDups.length != allNames.size then
    throwErrorAt t "component fields must have distinct names"
  if let some kf := keyF? then
    unless fieldNames.contains kf.getId.eraseMacroScopes do
      throwErrorAt kf "`key {kf.getId}`: not a `state` field of this component (fields: {fieldNames.toList})"
    if outTy?.isSome then
      throwErrorAt kf "`key` marks the row identity for parent-owned use (`state=\{…}`), \
        and a parent-owned child's `emits` output would have no receiver; drop one of the two"
  return { doc?, t, collections, fs, tys, ds, pfs, ptys, pds,
           hasProps, keyF?, outTy?, actions, body, fieldNames, allNames }

open Lean Elab Command in
private def collectSitesAndRewriteBody (spec : ComponentSpec) :
    CommandElabM (Array SetSite × Term) := do
  let sitesRef ← IO.mkRef (#[] : Array SetSite)
  for a in spec.actions do
    let name := a[1].getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·[1].getId == name) then
      throwErrorAt a[1] "duplicate action name `{name}`"
    let before ← sitesRef.get
    let actionRef ← IO.mkRef (#[] : Array SetSite)
    let _ ← replaceSets spec.fieldNames (spec.t.getId ++ `Msg) spec.outTy?.isSome actionRef a[5]
    let actionSites ← actionRef.get
    unless actionSites.size == 1 && (a[5].getKind == ``setTerm || a[5].getKind == ``sendTerm) do
      throwErrorAt a[5] "an action must be a `set`/`send` chain"
    let some site := actionSites[0]? | throwErrorAt a "empty action"
    let params : Array (Ident × Term) := a[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩)
    if !params.isEmpty && site.assigns.any (·.2.isNone) then
      throwErrorAt a "use an explicit set value in an action with parameters"
    let names := params.map (·.1.getId)
    if names.toList.eraseDups.length != names.size || names.any spec.allNames.contains then
      throwErrorAt a "action parameters must be distinct and must not shadow fields"
    let guard? : Option Term := if a[3].getNumArgs == 2 then some ⟨a[3][1]⟩ else none
    sitesRef.set (before.push { site with ctor := name, key := s!"action:{name}", params, guard? })
  let body' : Term := ⟨← replaceSets spec.fieldNames (spec.t.getId ++ `Msg) spec.outTy?.isSome sitesRef spec.body⟩
  return (← sitesRef.get, body')

open Lean Elab Command in
private def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool)
    (body : Term) : CommandElabM Term := do
  let mut out := body
  for g in spec.allNames.reverse do
    if shouldBind g then
      let gId := mkIdent g
      if spec.fieldNames.contains g then
        out ← `(let $gId:ident := (s.$gId:ident); $out)
      else
        out ← `(let $gId:ident := (p.$gId:ident); $out)
  return out

open Lean Elab Command in
private def mkPropsBinders (spec : ComponentSpec) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if spec.hasProps then
    let propsId := mkIdent (spec.t.getId ++ `Props)
    return #[← `(bracketedBinder| (p : $propsId))]
  else return #[]

open Lean Elab Command in
private def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (TSyntax `command × TSyntax `command) := do
  let stateId  := mkIdent (spec.t.getId ++ `State)
  let msgId    := mkIdent (spec.t.getId ++ `Msg)
  let updateId := mkIdent (spec.t.getId ++ `update)
  let mut ctors ← sites.mapM fun site => do
    let cId := mkIdent site.ctor
    if !site.params.isEmpty then
      let ids := site.params.map (·.1)
      let ts := site.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $cId:ident $[($ids:ident : $ts)]*)
    else match site.assigns.find? (·.2.isNone) with
    | some (f, _) =>
      let some idx := spec.fieldNames.findIdx? (· == f) | throwError "component: internal"
      `(Lean.Parser.Command.ctor| | $cId:ident (v : $(spec.tys[idx]!)))
    | none =>
      `(Lean.Parser.Command.ctor| | $cId:ident)
  for col in spec.collections do
    let nm := mkIdent col[1].getId
    let cm := mkIdent (col[3].getId ++ `Msg)
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $nm:ident (key : String) (msg : $cm)))
  let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
    else `(command| inductive $msgId where $[$ctors:ctor]*)
  let mut arms ← sites.mapM fun site => do
    let cFull := mkIdent (spec.t.getId ++ `Msg ++ site.ctor)
    let stateTerm : Term ←
      if site.assigns.isEmpty then `(s)
      else do
        let fIds := site.assigns.map fun (f, _) => mkIdent f
        let vals ← site.assigns.mapM fun (_, e?) => e?.getDM `(v)
        `({ s with $[$fIds:ident := $vals],* })
    let rhs0 : Term ← match spec.outTy? with
      | none   => pure stateTerm
      | some _ => match site.send? with
        | some o => `(($stateTerm, some $o))
        | none   => `(($stateTerm, none))
    let mut rhs := rhs0
    if let some guard := site.guard? then
      let unchanged ← if spec.outTy?.isSome then `((s, none)) else `(s)
      rhs ← `(if $guard then $rhs else $unchanged)
    rhs ← bindMentionedFields spec (fun g =>
      (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
      (site.send?.any (mentionsIdent ·.raw g)) ||
      (site.guard?.any (mentionsIdent ·.raw g))) rhs
    if !site.params.isEmpty then
      let ids : Array Term := site.params.map (fun p => ⟨p.1.raw⟩)
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
    else if site.assigns.any (·.2.isNone) then
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
    else
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
  for col in spec.collections do
    let nm := mkIdent col[1].getId
    let ctor := mkIdent (spec.t.getId ++ `Msg ++ col[1].getId)
    let upd := mkIdent (col[3].getId ++ `updateKeyed)
    let next ← `({ s with $nm:ident := $upd s.$nm:ident k msg })
    let rhs ← if spec.outTy?.isSome then `(($next, none)) else pure next
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $ctor k msg => $rhs))
  let retTy : Term ← match spec.outTy? with
    | some o => `($stateId × Option $o)
    | none   => `($stateId)
  let updateBody ← if arms.isEmpty then `(fun m => nomatch m)
    else `(fun m => match m with $[$arms:matchAlt]*)
  let pBinders ← mkPropsBinders spec
  let updateCmd ← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody)
  return (msgCmd, updateCmd)

open Lean Elab Command in
private def mkStructFields (ids : Array Ident) (tys : Array Term) (ds : Array (Option Term)) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Command.structExplicitBinder)) :=
  ((ids.zip tys).zip ds).mapM fun ((f, ty), d?) =>
    match d? with
    | some d => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty := $d))
    | none   => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty))

open Lean Elab Command in
private def mkStructAndViewCmds (spec : ComponentSpec) (body' : Term)
    (msgCmd updateCmd : TSyntax `command) : CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let propsId  := mkIdent (spec.t.getId ++ `Props)
  let stateId  := mkIdent (spec.t.getId ++ `State)
  let msgId    := mkIdent (spec.t.getId ++ `Msg)
  let updateId := mkIdent (spec.t.getId ++ `update)
  let viewId   := mkIdent (spec.t.getId ++ `view)
  let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  let propFields  ← mkStructFields spec.pfs spec.ptys spec.pds
  let stateFields ← mkStructFields spec.fs spec.tys spec.ds
  let pBinders ← mkPropsBinders spec
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| structure $propsId where $[$propFields:structExplicitBinder]*),
    ← `(command| structure $stateId where $[$stateFields:structExplicitBinder]*),
    msgCmd,
    updateCmd,
    ← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewBody) ]
  if spec.outTy?.isNone then
    let renderId    := mkIdent (spec.t.getId ++ `render)
    let renderTagId := mkIdent (spec.t.getId ++ `renderTag)
    let compId      := mkIdent (spec.t.getId ++ `component)
    let rendered ← if spec.hasProps then `($viewId p s) else `($viewId s)
    let updExpr  ← if spec.hasProps then `($updateId p) else `($updateId)
    let viewExpr ← if spec.hasProps then `($viewId p) else `($viewId)
    let compExpr ← if spec.hasProps then `($compId p) else `($compId)
    cmds := cmds ++ #[
      ← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]*
            (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route),
      ← (match spec.keyF? with
        | some kf =>
          let kfId := mkIdent kf.getId.eraseMacroScopes
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : String → $msgId → parentMsg) (s : $stateId)
              (k : String := toString s.$kfId) : Html parentMsg := ($rendered).map (route k))
        | none =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route)),
      ← `(command| $[$doc?:docComment]? def $compId $[$pBinders:bracketedBinder]*
            : Component $stateId $msgId := { update := $updExpr, view := $viewExpr }) ]
    if let some kf := spec.keyF? then
      let keyOfId       := mkIdent (spec.t.getId ++ `keyOf)
      let updateKeyedId := mkIdent (spec.t.getId ++ `updateKeyed)
      let eachId        := mkIdent (spec.t.getId ++ `each)
      let kfId          := mkIdent kf.getId.eraseMacroScopes
      cmds := cmds ++ #[
        ← `(command| def $keyOfId (s : $stateId) : String := toString s.$kfId),
        ← `(command| def $updateKeyedId $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (k : String) (msg : $msgId) : Array $stateId :=
              Component.updateKeyed $compExpr $keyOfId rows k msg),
        ← `(command| def $eachId {parentMsg : Type} $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (route : String → $msgId → parentMsg)
              (wrap : $stateId → Html parentMsg → Html parentMsg := fun _ child => child)
              : Array (Html parentMsg) := Component.each $compExpr $keyOfId rows route wrap) ]
  return cmds

open Lean Elab Command in
private def mkCodecAndMountCmds (spec : ComponentSpec) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command)) := do
  let doc?       := spec.doc?
  let fs         := spec.fs
  let pfs        := spec.pfs
  let propsId    := mkIdent (spec.t.getId ++ `Props)
  let stateId    := mkIdent (spec.t.getId ++ `State)
  let initId     := mkIdent (spec.t.getId ++ `init)
  let msgId      := mkIdent (spec.t.getId ++ `Msg)
  let updateId   := mkIdent (spec.t.getId ++ `update)
  let viewId     := mkIdent (spec.t.getId ++ `view)
  let regId      := mkIdent (spec.t.getId ++ `reg)
  let mountId    := mkIdent (spec.t.getId ++ `mount)
  let toJsonId   := mkIdent (spec.t.getId ++ `State ++ `toJson)
  let fromJsonId := mkIdent (spec.t.getId ++ `State ++ `fromJson)
  let mkCodecParts (ids : Array Ident) (tys : Array Term) := do
    let ks := ids.map fun f => Syntax.mkStrLit (toString f.getId)
    let enc ← (ids.zip ks).mapM fun (f, k) => `(($k, toJson (x.$f:ident)))
    let dec ← (tys.zip ks).mapM fun (ty, k) => `((FromJsonField.fromField j $k : Except String $ty))
    return (enc, dec)
  let (pairs, decodes) ← mkCodecParts fs spec.tys
  let (pp, pd)         ← mkCodecParts pfs spec.ptys
  let propsToJsonId   := mkIdent (spec.t.getId ++ `Props ++ `instToJson)
  let propsFromJsonId := mkIdent (spec.t.getId ++ `Props ++ `instFromJson)
  let stateToJsonId   := mkIdent (spec.t.getId ++ `State ++ `instToJson)
  let stateFromJsonId := mkIdent (spec.t.getId ++ `State ++ `instFromJson)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| instance $propsToJsonId:ident : ToJson $propsId := ⟨fun x => Json.obj [$[$pp],*]⟩),
    ← `(command| instance $propsFromJsonId:ident : FromJson $propsId := ⟨fun j => do
      $[let $pfs:ident ← $pd:term]*
      return { $[$pfs:ident],* }⟩),
    ← `(command| def $toJsonId (x : $stateId) : Json := Json.obj [$[$pairs],*]),
    ← `(command| def $fromJsonId (j : Json) : Except String $stateId := do
          $[let $fs:ident ← $decodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| instance $stateToJsonId:ident : ToJson $stateId := ⟨$toJsonId⟩),
    ← `(command| instance $stateFromJsonId:ident : FromJson $stateId := ⟨$fromJsonId⟩)]
  let mountable := spec.ds.all (·.isSome)
  if mountable then
    let dsT := spec.ds.filterMap id
    cmds := cmds ++ #[
      ← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }),
      ← (if spec.hasProps then
          match spec.outTy? with
          | none => `(command| def $regId : LocalDef :=
              LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
          | some _ => `(command| def $regId : LocalDef :=
              LocalDef.ofProps $idLit $initId $viewId $updateId)
        else match spec.outTy? with
        | none => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
            LocalDef.ofSimple $idLit $initId $viewId $updateId)
        | some _ => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
            LocalDef.of $idLit $initId $viewId $updateId)),
      ← `(command| $[$doc?:docComment]? def $mountId {msg : Type} (key : String) : Attr msg :=
            localMount $idLit key) ]
    if let some o := spec.outTy? then
      let mountWithId := mkIdent (spec.t.getId ++ `mountWith)
      cmds := cmds.push <|
        ← `(command| $[$doc?:docComment]? def $mountWithId {msg : Type}
              (key : String) (onOut : $o → msg) : Attr msg :=
              localMountWith $idLit key (fun out => some (onOut out)))
  let regsId := mkIdent (spec.t.getId ++ `regs)
  let own : Term ← if mountable then `([$regId]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
    LocalDef.dedupe ($own ++ localRegistrations $viewId)))
  if mountable && spec.outTy?.isNone && !spec.hasProps then
    let appId := mkIdent (spec.t.getId ++ `app)
    cmds := cmds.push <|
      ← `(command| $[$doc?:docComment]? def $appId : App $stateId $msgId :=
            withLocalRegistry (mkApp $initId $updateId (View.ofHtml $viewId) (locals := $regsId)))
  return cmds

open Lean Elab Command in
@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let spec ← parseComponentSpec stx
  let idLit := Syntax.mkStrLit (((← getCurrNamespace) ++ spec.t.getId).toString)
  let (sites, body') ← collectSitesAndRewriteBody spec
  let (msgCmd, updateCmd) ← mkMsgAndUpdateCmds spec sites
  let coreCmds ← mkStructAndViewCmds spec body' msgCmd updateCmd
  let mountCmds ← mkCodecAndMountCmds spec idLit
  for c in coreCmds ++ mountCmds do
    elabCommand c

end Qed
