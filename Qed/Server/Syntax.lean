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

private def srvContractSuite (expectedMsg : String) : Parser :=
  checkColGt expectedMsg >>
  withPosition (
    many (atomic (checkColEq "contract" >> srvContractLine)) >>
    many1 (checkColEq "statement" >> categoryParser `qedStmt 0))

@[srvClause_parser] def srvHttpRouteClause : Parser := leading_parser
  withPosition (atomic (extHttpMethod >> strLit >> ":") >> srvContractSuite "expected indented HTTP route body")

@[srvClause_parser] def srvStreamClause : Parser := leading_parser
  withPosition (atomic (identEq `stream) >> strLit >> ":" >> srvContractSuite "expected indented `stream` body")

@[srvClause_parser] def srvFnClause : Parser := leading_parser
  withPosition (
    symbol "def" >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >>
    " -> " >> categoryParser `qedType 0 >> ":" >> srvContractSuite "expected indented function body")

@[srvClause_parser] def srvJobClause : Parser := leading_parser
  withPosition (
    atomic (identEq `every) >> numLit >> ident >> ident >> ":" >> qedSuite)

@[srvClause_parser] def srvOnCreateAccountClause : Parser := leading_parser
  withPosition (
    atomic (identEq `onCreateAccount >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)

@[srvClause_parser] def srvOnSignInClause : Parser := leading_parser
  withPosition (
    atomic (identEq `onSignIn >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)

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

/-! ## Server Type Lowering Helper (Thin Wrapper over `Qed.Lang.lowerQedTypeInfo`) -/

def lowerSrvType (stx : Lean.Syntax) (allowFallible : Bool := false) (ctxDesc : String := "") :
    Lean.MacroM Qed.Lang.LoweredQedType :=
  Qed.Lang.lowerQedTypeInfo stx (allowFallible := allowFallible) (allowHigherOrder := false)
    (ctxDesc? := if ctxDesc.isEmpty then none else some ctxDesc)

/-- Thin compatibility wrapper over `Qed.Lang.LoweredQedType` retained for `Qed/Server/External.lean`
    until it migrates directly to `lowerSrvType`. -/
structure ParsedSrvType where
  ref  : Lean.Syntax
  info : Qed.Lang.LoweredQedType
deriving Inhabited

namespace ParsedSrvType
def baseIdent (t : ParsedSrvType) : Lean.Ident := Lean.mkIdentFrom t.ref t.info.baseName
def isProto (t : ParsedSrvType) : Bool := t.info.isProto
def mods (t : ParsedSrvType) : Array Qed.Lang.TypeMod := t.info.mods
def parse (stx : Lean.Syntax) : Lean.MacroM ParsedSrvType :=
  return { ref := stx, info := ← Qed.Lang.lowerQedTypeInfo stx (allowFallible := true) (allowHigherOrder := false) }
def validate (t : ParsedSrvType) (allowFallible : Bool) (ctxDesc : String) : Lean.MacroM Unit := do
  if !allowFallible && t.info.isFallible then
    Lean.Macro.throwErrorAt t.ref s!"fallible `!` modifier is not allowed on {ctxDesc}; only server `def` return types may use `T!`"
def toPayloadTerm (t : ParsedSrvType) : Lean.MacroM Lean.Term := pure t.info.term
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
