import Lean
import Qed.Lang

namespace Qed.Server

/-! ## Server, External & Fullstack Surface Syntax (Sharing `Qed.Lang` Expressions, Statements & Types) -/

declare_syntax_cat extClause
declare_syntax_cat extParam
declare_syntax_cat extWsSubClause
declare_syntax_cat srvClause
declare_syntax_cat srvChanSubClause
declare_syntax_cat fullstackClause

section SrvParsers
open Lean Parser Qed.Lang

def srvParam : Parser :=
  node `Qed.Server.srvParam (ident >> ":" >> categoryParser `qedType 0)

def srvRequiresLine : Parser :=
  node `Qed.Server.srvRequiresLine
    (withPosition (atomic (identEq `requires) >> sepBy1 (categoryParser `qedExpr 0) ","))

def srvEnsuresLine : Parser :=
  node `Qed.Server.srvEnsuresLine
    (withPosition (atomic (identEq `ensures) >> sepBy1 (categoryParser `qedExpr 0) ","))

def srvContractLine : Parser := srvRequiresLine <|> srvEnsuresLine

-- `external` clauses & command
@[extParam_parser] def extParamHeader : Parser := leading_parser
  atomic (identEq `header >> checkNoWsBefore "" >> "(") >> strLit >> ")" >> ident >> ":" >> categoryParser `qedType 0

@[extParam_parser] def extParamPlain : Parser := leading_parser
  ident >> ":" >> categoryParser `qedType 0

@[extClause_parser] def extBaseClause : Parser := leading_parser
  withPosition (atomic (identEq `base) >> strLit)

@[extClause_parser] def extAuthBearer : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `bearer) >>
    "(" >> identEq `secret >> "(" >> strLit >> ")" >> ")")

@[extClause_parser] def extAuthHeader : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `header) >>
    "(" >> strLit >> ", " >> identEq `secret >> "(" >> strLit >> ")" >> ")")

@[extClause_parser] def extAuthGcp : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `gcpServiceAccount) >>
    "(" >> identEq `secret >> "(" >> strLit >> ")" >>
    optional (", " >> strLit) >> ")")

def extHttpMethod : Parser :=
  identEq `get <|> identEq `post <|> identEq `put <|> identEq `patch <|> identEq `delete

@[extClause_parser] def extEndpointClause : Parser := leading_parser
  withPosition (
    extHttpMethod >> strLit >>
    checkColGt "expected endpoint signature" >>
    ident >> checkNoWsBefore "" >> "(" >> sepBy (categoryParser `extParam 0) "," >> ")" >>
    " -> " >> categoryParser `qedType 0)

@[extWsSubClause_parser] def extWsReqClause : Parser := leading_parser srvRequiresLine
@[extWsSubClause_parser] def extWsReconnectClause : Parser := leading_parser
  withPosition (atomic (kw "reconnect") >> categoryParser `qedExpr 0)
@[extWsSubClause_parser] def extWsSendClause : Parser := leading_parser
  withPosition (
    atomic (kw "send" >> checkNoWsBefore "" >> "(") >> sepBy1 srvParam "," >> ")" >>
    optional (":" >> checkColGt "expected indented `requires` clauses" >> many1Indent srvRequiresLine))

@[extClause_parser] def extWsClause : Parser := leading_parser
  withPosition (
    atomic (identEq `ws) >> strLit >>
    checkColGt "expected WebSocket channel signature" >>
    ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >>
    " -> " >> categoryParser `qedType 0 >>
    optional (":" >> checkColGt "expected indented `ws` channel clauses" >>
      many1Indent (categoryParser `extWsSubClause 0)))

@[command_parser] def externalCmd : Parser := leading_parser
  withPosition (
    "external " >> ident >> ":" >>
    checkColGt "expected indented `external` clauses" >>
    many1Indent (categoryParser `extClause 0))

-- `server` & `fullstack` clauses & commands
@[srvClause_parser] def srvDbClause : Parser := leading_parser
  withPosition (atomic (identEq `use) >> ident >> ":" >> ident)

@[srvClause_parser] def srvEnvClause : Parser := leading_parser
  withPosition (atomic (identEq `env) >> ident >> "=" >> strLit >> optional (" ?? " >> strLit))

@[srvClause_parser] def srvStateClause : Parser := leading_parser
  withPosition (atomic (identEq `state) >> ident >> ":" >> categoryParser `qedType 0 >>
    optional ("=" >> categoryParser `qedExpr 0))

@[srvClause_parser] def srvInvMutatingClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> ident >> ":" >> identEq `mutating) >>
    ident >> kw "requires" >> categoryParser `qedExpr 0)

@[srvClause_parser] def srvInvClause : Parser := leading_parser
  withPosition (
    "invariant " >> ident >> ":" >> notFollowedBy (identEq `mutating) "mutating" >>
    sepBy1 (categoryParser `qedExpr 0) ",")

@[srvChanSubClause_parser] def srvChanReqClause : Parser := leading_parser srvRequiresLine
@[srvChanSubClause_parser] def srvChanEnsClause : Parser := leading_parser srvEnsuresLine
@[srvChanSubClause_parser] def srvChanReconnectClause : Parser := leading_parser
  withPosition (atomic (kw "reconnect") >> categoryParser `qedExpr 0)

@[srvChanSubClause_parser] def srvChanOnJoinClause : Parser := leading_parser
  withPosition (
    atomic (identEq `on_join) >>
    optional (" -> " >> categoryParser `qedType 0) >> ":" >>
    qedSuite)

@[srvChanSubClause_parser] def srvChanOnSendClause : Parser := leading_parser
  withPosition (
    atomic (identEq `on_send >> checkNoWsBefore "" >> "(") >> sepBy1 srvParam "," >> ")" >> ":" >>
    checkColGt "expected indented `on_send` body" >>
    withPosition (
      many (atomic (checkColEq "requires" >> srvRequiresLine)) >>
      many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

@[srvChanSubClause_parser] def srvChanOnLeaveClause : Parser := leading_parser
  withPosition (
    atomic (identEq `on_leave) >> ":" >> qedSuite)

@[srvClause_parser] def srvChannelClause : Parser := leading_parser
  withPosition (
    atomic (identEq `channel) >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >>
    " -> " >> categoryParser `qedType 0 >>
    optional (":" >> checkColGt "expected indented `channel` clauses" >>
      many1Indent (categoryParser `srvChanSubClause 0)))

private def identDotTransaction : Parser :=
  leading_parser withFn (fun fn c s =>
    let s' := fn c s
    if s'.hasError then s'
    else
      match s'.stxStack.back.getId.eraseMacroScopes with
      | .str (.str .anonymous _) "transaction" => s'
      | _ => s.mkError "expected `<db>.transaction`") Parser.ident

@[qedStmt_parser] def qedStmtDbTransaction : Parser := leading_parser
  withPosition (atomic (identDotTransaction >> ":") >> qedSuite)

@[srvClause_parser] def srvHttpRouteClause : Parser := leading_parser
  withPosition (
    atomic (identEq `http >> extHttpMethod) >> strLit >> ":" >>
    checkColGt "expected indented `http` route body" >>
    withPosition (
      many (atomic (checkColEq "contract" >> srvContractLine)) >>
      many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

@[srvClause_parser] def srvStreamClause : Parser := leading_parser
  withPosition (
    atomic (identEq `stream) >> strLit >> ":" >>
    checkColGt "expected indented `stream` body" >>
    withPosition (
      many (atomic (checkColEq "contract" >> srvContractLine)) >>
      many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

@[srvClause_parser] def srvFnClause : Parser := leading_parser
  withPosition (
    symbol "def" >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >>
    " -> " >> categoryParser `qedType 0 >> ":" >>
    checkColGt "expected indented function body" >>
    withPosition (
      many (atomic (checkColEq "contract" >> srvContractLine)) >>
      many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

@[srvClause_parser] def srvJobClause : Parser := leading_parser
  withPosition (
    atomic (identEq `every) >> numLit >> ident >> ident >> ":" >> qedSuite)

@[command_parser] def serverCmd : Parser := leading_parser
  withPosition (
    "server " >> ident >> ":" >>
    checkColGt "expected indented `server` body" >>
    many1Indent (categoryParser `srvClause 0))

@[fullstackClause_parser] def fsServerClause : Parser := leading_parser
  withPosition ("server " >> ident)

@[fullstackClause_parser] def fsClientClause : Parser := leading_parser
  withPosition (atomic (identEq `client) >> ident)

@[fullstackClause_parser] def fsTitleClause : Parser := leading_parser
  withPosition (atomic (identEq `title) >> strLit)

@[command_parser] def fullstackCmd : Parser := leading_parser
  withPosition (
    "fullstack " >> ident >> ":" >>
    checkColGt "expected indented `fullstack` clauses" >>
    many1Indent (categoryParser `fullstackClause 0))

end SrvParsers

/-! ## Parsed Type Representation & Lowering Helpers (over unified `qedType`) -/

abbrev SrvTypeMod := Qed.Lang.TypeMod

structure ParsedSrvType where
  ref        : Lean.Syntax
  baseIdent  : Lean.Ident
  isProto    : Bool := false
  mods       : Array SrvTypeMod := #[]
  tupleElems : Array Lean.Term := #[]
deriving Inhabited

namespace ParsedSrvType

private def buildProdTerm (elems : Array Lean.Term) : Lean.MacroM Lean.Term := do
  if elems.isEmpty then `(Unit)
  else if elems.size == 1 then return elems[0]!
  else
    let mut acc := elems.back!
    for revIdx in [1:elems.size] do
      acc ← `($(elems[elems.size - 1 - revIdx]!) × $acc)
    return acc

partial def parse (stx : Lean.Syntax) : Lean.MacroM ParsedSrvType := do
  let k := stx.getKind
  if k == ``Qed.Lang.qedTypeProto then
    let (baseId, initMods) ← Qed.Lang.splitIdentMods ⟨(stx.getArg 2)⟩
    return { ref := stx, baseIdent := baseId, isProto := true,
             mods := initMods ++ (← (stx.getArg 4).getArgs.mapM Qed.Lang.parseTypeModNode) }
  else if k == ``Qed.Lang.qedTypeParen then
    let elemStxs := (stx.getArg 1).getSepArgs
    let mods ← (stx.getArg 3).getArgs.mapM Qed.Lang.parseTypeModNode
    let mut elemTerms : Array Lean.Term := #[]
    for eStx in elemStxs do
      let pe ← parse eStx
      if pe.mods.contains .fallible then
        Lean.Macro.throwErrorAt eStx "fallible `!` modifier cannot appear inside a tuple type"
      let baseT ← if pe.tupleElems.isEmpty then pure (Qed.Lang.resolveBaseTypeTerm pe.baseIdent)
                  else buildProdTerm pe.tupleElems
      let et ← Qed.Lang.applyTypeMods baseT pe.mods true pe.ref
      elemTerms := elemTerms.push et.1
    return { ref := stx, baseIdent := Lean.mkIdentFrom stx `Prod, isProto := false,
             mods, tupleElems := elemTerms }
  else if k == ``Qed.Lang.qedTypeAtom then
    let (baseId, initMods) ← Qed.Lang.splitIdentMods ⟨(stx.getArg 0)⟩
    return { ref := stx, baseIdent := baseId, isProto := false,
             mods := initMods ++ (← (stx.getArg 1).getArgs.mapM Qed.Lang.parseTypeModNode) }
  else if k == ``Qed.Lang.qedTypeApp && (stx.getArg 0).getKind == ``Qed.Lang.qedTypeAtom && ((stx.getArg 0).getArg 1).getArgs.isEmpty then
    let fnName := ((stx.getArg 0).getArg 0).getId.eraseMacroScopes
    let argStr := let s := Qed.Lang.stxSnippet (stx.getArg 1); if s.isEmpty then "T" else s
    if fnName == `Array || fnName == `Option then
      Lean.Macro.throwErrorAt stx s!"use `{argStr}{if fnName == `Array then "[]" else "?"}` instead of `{fnName} {argStr}`"
    else
      let sn := Qed.Lang.stxSnippet stx
      let what := if sn.isEmpty then "" else s!" `{sn}`"
      Lean.Macro.throwErrorAt stx s!"invalid server type{what}; expected `T`, `T[]`, `T?`, `T!`, `(T, U)`, or `Proto(T)`"
  else
    let sn := Qed.Lang.stxSnippet stx
    let what := if sn.isEmpty then "" else s!" `{sn}`"
    Lean.Macro.throwErrorAt stx s!"invalid server type{what}; expected `T`, `T[]`, `T?`, `T!`, `(T, U)`, or `Proto(T)`"

def hasFallible (t : ParsedSrvType) : Bool := t.mods.contains .fallible

/-- Validates that `!` only appears at the outermost position when permitted. -/
def validate (t : ParsedSrvType) (allowFallible : Bool) (ctxDesc : String) : Lean.MacroM Unit := do
  if !allowFallible && t.hasFallible then
    Lean.Macro.throwErrorAt t.ref s!"fallible `!` modifier is not allowed on {ctxDesc}; only server `def` return types may use `T!`"
  for i in [0:t.mods.size] do
    if t.mods[i]! == .fallible && i + 1 < t.mods.size then
      Lean.Macro.throwErrorAt t.ref "place `!` last on fallible return types (for example `Book[]!` instead of `Book![]`)"

/-- Lowers the non-`!` payload type (e.g. `Book[]!` → `Array Book`, `(A, B)[]!` → `Array (A × B)`). -/
def toPayloadTerm (t : ParsedSrvType) : Lean.MacroM Lean.Term := do
  let baseTerm ←
    if t.tupleElems.isEmpty then pure (Qed.Lang.resolveBaseTypeTerm t.baseIdent)
    else buildProdTerm t.tupleElems
  return (← Qed.Lang.applyTypeMods baseTerm t.mods true t.ref).1

end ParsedSrvType

syntax (name := srvAutoFieldStx) "srvAutoField(" term ")" : term
syntax (name := srvAutoEmitStx)  "srvAutoEmit(" term ")" : term
syntax (name := srvTypedAsStx)   "srvTypedAs(" term ", " term ")" : term
syntax (name := srvGetElemStx)   "srvGetElem(" term ", " term ")" : term
syntax (name := srvSetElemStx)   "srvSetElem(" term ", " term ", " term ")" : term

syntax "qedSrvProveStep " "[" ident,* "]" str str : tactic
syntax "qedSrvProveAsync " ident "[" ident,* "]" str str : tactic
syntax "qedSrvProveAsyncEnsures " ident "[" ident,* "]" str str : tactic
syntax "qedProveRpcReq" : tactic

end Qed.Server
