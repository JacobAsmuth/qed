import Lean
import Qed.Lang

namespace Qed.Server

/-! ## Server, External & Fullstack Surface Syntax -/

declare_syntax_cat extClause
declare_syntax_cat srvClause

section SrvParsers
open Lean Parser Qed.Lang

private def qExpr : Parser := categoryParser `qedExpr 0
private def qType : Parser := withPosition (categoryParser `qedType 0)
private def withP (k : Name) (p : Parser) : Parser := node k (withPosition p)
private def indentedP (msg : String) (p : Parser) : Parser := ":" >> checkColGt msg >> many1Indent p
private def callSig (p : Parser) : Parser := ident >> checkNoWsBefore "" >> "(" >> commaSep p >> ")" >> " -> " >> qType
private def secretArg : Parser := identEq `secret >> "(" >> strLit >> ")"
private def authP (k kw : Name) (inner : Parser) : Parser := withP k (atomic (identEq `auth >> identEq kw) >> "(" >> inner >> ")")
private def authHook (k kw : Name) : Parser := withP k (atomic (identEq kw >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)
private def reconnectP (k : Name) : Parser := node k (withPosition (atomic (kw "reconnect") >> qExpr))
private def srvContractSuite (msg : String) (lineP : Parser) : Parser :=
  (checkLineEq >> pushNone >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
  (checkColGt msg >> withPosition (many (atomic (checkColEq "contract" >> lineP)) >> many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))
private def optLine (k kw : Name) (p : Parser) : Parser := withP k (atomic (identEq kw) >> p >> Qed.fnOptProof)

def srvParam : Parser := node `Qed.Server.srvParam (ident >> ":" >> qType >> optional ("=" >> qExpr))
def srvRequiresLine : Parser := withP `Qed.Server.srvRequiresLine (atomic (identEq `requires) >> sepBy1 qExpr ",")
def srvEnsuresLine : Parser := optLine `Qed.Server.srvEnsuresLine `ensures (sepBy1 qExpr ",")
def srvEnsuresFailsLine : Parser := optLine `Qed.Server.srvEnsuresFailsLine `ensures_fails (optional (checkLineEq >> numLit))
def srvEffectTag : Parser := node `Qed.Server.srvEffectTag (identEq `no_http <|> identEq `no_decrypt <|> identEq `no_crypto <|> identEq `no_db_write <|> identEq `no_proc <|> identEq `no_fs)
def srvEffectLine : Parser := withP `Qed.Server.srvEffectLine (atomic (sepBy1 srvEffectTag ",") >> Qed.fnOptProof)
def srvBlindToLine : Parser := optLine `Qed.Server.srvBlindToLine `blindTo (sepBy1 Qed.fnBlindTarget ",")
private def srvContractLineFuel : Nat → Parser
  | 0 => srvRequiresLine <|> srvEnsuresLine <|> srvEnsuresFailsLine <|> srvEffectLine <|> srvBlindToLine
  | n + 1 => srvContractLineFuel 0 <|>
      withP `Qed.Server.srvCIIf (atomic (symbol "if" >> notFollowedBy (symbol "let") "let" >> sepBy1 qExpr "," >> ":" >>
        checkColGt "expected indented contract clauses" >> many1Indent { fn := fun c s => (srvContractLineFuel n).fn c s }))
def srvContractLine : Parser := srvContractLineFuel 32
def extHttpMethod : Parser := identEq `get <|> identEq `post <|> identEq `put <|> identEq `patch <|> identEq `delete

def extParamHeader : Parser := node `Qed.Server.extParamHeader (atomic (identEq `header >> checkNoWsBefore "" >> "(") >> strLit >> ")" >> ident >> ":" >> qType)
def extParamQuery  : Parser := node `Qed.Server.extParamQuery (atomic (identEq `query >> optional (checkNoWsBefore "" >> "(" >> strLit >> ")") >> ident >> ":") >> qType)
def extParamPlain  : Parser := node `Qed.Server.extParamPlain (ident >> ":" >> qType)
def extBaseWhereEnum : Parser := node `Qed.Server.extBaseWhereEnum (atomic (ident >> ":") >> ident)
def extBaseWhereIn   : Parser := node `Qed.Server.extBaseWhereIn (atomic (ident >> symbol "in" >> "[") >> sepBy1 strLit "," >> "]")
def extBaseClause : Parser := withP `Qed.Server.extBaseClause
  (atomic (identEq `base) >> strLit >> optional (checkLineEq >> symbol "where" >> sepBy1 (extBaseWhereIn <|> extBaseWhereEnum) ","))
def extSsrfGuardClause : Parser := withP `Qed.Server.extSsrfGuardClause (atomic (identEq `ssrf_guard) >> optional (checkLineEq >> (identEq `true <|> identEq `false)))
def extAuthBearer : Parser := authP `Qed.Server.extAuthBearer `bearer secretArg
def extAuthHeader : Parser := authP `Qed.Server.extAuthHeader `header (strLit >> ", " >> secretArg)
def extAuthGcp : Parser := authP `Qed.Server.extAuthGcp `gcpServiceAccount (secretArg >> optional (", " >> strLit))
def extAuthGcpMeta : Parser := withP `Qed.Server.extAuthGcpMeta (atomic (identEq `auth >> identEq `gcpMetadata) >> optional ("(" >> strLit >> ")"))
def extEndpointClause : Parser := withP `Qed.Server.extEndpointClause
  (atomic (extHttpMethod >> strLit) >> checkColGt "expected endpoint signature" >> callSig (extParamHeader <|> extParamQuery <|> extParamPlain) >>
    optional (atomic (checkColGt "expected `ok [...]`" >> identEq `ok >> "[") >> sepBy1 numLit "," >> "]"))
def extWsReconnectClause : Parser := reconnectP `Qed.Server.extWsReconnectClause
def extWsSendClause : Parser := withP `Qed.Server.extWsSendClause
  (atomic (kw "send" >> checkNoWsBefore "" >> "(") >> commaSep1 srvParam >> ")" >> optional (indentedP "expected indented `requires` clauses" srvRequiresLine))
def extWsClause : Parser := withP `Qed.Server.extWsClause
  (atomic (identEq `ws) >> strLit >> checkColGt "expected WebSocket channel signature" >>
    callSig srvParam >> optional (indentedP "expected indented `ws` channel clauses" (srvRequiresLine <|> extWsReconnectClause <|> extWsSendClause)))
def extInvClause : Parser := withP `Qed.Server.extInvClause (atomic (identEq `invariant >> ident >> ":") >> sepBy1 qExpr ",")
@[extClause_parser] def extClauseP : Parser := opaqueP (
  extBaseClause <|> extSsrfGuardClause <|> extAuthBearer <|> extAuthHeader <|> extAuthGcp <|> extAuthGcpMeta <|> extEndpointClause <|> extWsClause <|> extInvClause)
@[command_parser] def externalCmd : Parser := opaqueP (
  node `Qed.Server.externalCmd (optional Command.docComment >> withPosition (atomic (identEq `external >> ident >> ":") >> checkColGt "expected indented `external` clauses" >> many1Indent (categoryParser `extClause 0))))

def srvDbClause : Parser := withP `Qed.Server.srvDbClause (atomic (identEq `use) >> ident >> ":" >> ident)
def srvEnvClause : Parser := withP `Qed.Server.srvEnvClause (atomic (identEq `env) >> ident >> "=" >> strLit >> optional (" ?? " >> strLit))
def srvSecretClause : Parser := withP `Qed.Server.srvSecretClause (atomic (identEq `secret) >> ident >> "=" >> strLit)
def srvStateClause : Parser := withP `Qed.Server.srvStateClause (atomic (identEq `state) >> ident >> ":" >> qType >> optional ("=" >> qExpr))
def srvInvMutatingClause : Parser := withP `Qed.Server.srvInvMutatingClause (atomic (identEq `invariant >> ident >> ":" >> identEq `mutating) >> ident >> kw "requires" >> qExpr)
def srvInvClause : Parser := withP `Qed.Server.srvInvClause
  (atomic (identEq `invariant >> ident >> ":") >> notFollowedBy (identEq `mutating) "state invariant" >> sepBy1 qExpr ",")
def srvChanReconnectClause : Parser := reconnectP `Qed.Server.srvChanReconnectClause
def srvChanOnJoinClause : Parser := withP `Qed.Server.srvChanOnJoinClause (atomic (identEq `on_join) >> optional (" -> " >> qType) >> ":" >> qedSuite)
def srvChanOnSendClause : Parser := withP `Qed.Server.srvChanOnSendClause
  (atomic (identEq `on_send >> checkNoWsBefore "" >> "(") >> commaSep1 srvParam >> ")" >> ":" >> srvContractSuite "expected indented `on_send` body" srvRequiresLine)
def srvChanOnLeaveClause : Parser := withP `Qed.Server.srvChanOnLeaveClause (atomic (identEq `on_leave) >> ":" >> qedSuite)
def srvChanProjectClause : Parser := withP `Qed.Server.srvChanProjectClause
  (atomic (identEq `project >> checkNoWsBefore "" >> "(") >> srvParam >> ")" >> optional (" -> " >> qType) >> ":" >>
    checkColGt "expected indented `project` body" >>
    withPosition (many (atomic (checkColEq "contract" >> categoryParser `qedFnContract 0)) >> many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))
def srvChannelClause : Parser := withP `Qed.Server.srvChannelClause
  (atomic (identEq `channel) >> callSig srvParam >> optional (indentedP "expected indented `channel` clauses"
    (srvRequiresLine <|> srvEnsuresLine <|> srvChanReconnectClause <|> srvChanOnJoinClause <|> srvChanOnSendClause <|> srvChanOnLeaveClause <|> srvChanProjectClause)))

private def identDotTransaction : Parser :=
  withFn (fun fn c s =>
    let s' := fn c s
    if s'.hasError then s'
    else match s'.stxStack.back.getId.eraseMacroScopes with
      | .str (.str .anonymous _) "transaction" => s' | _ => s.mkError "expected `<db>.transaction`") Parser.ident
@[qedStmt_parser] def qedStmtDbTransaction : Parser := opaqueP (
  withP `Qed.Server.qedStmtDbTransaction (atomic (identDotTransaction >> optional (identEq `as >> ident) >> ":") >> qedSuite))

def srvHttpRouteClause : Parser := withP `Qed.Server.srvHttpRouteClause (atomic (extHttpMethod >> strLit >> ":") >> srvContractSuite "expected indented HTTP route body" srvContractLine)
def srvStreamClause : Parser := withP `Qed.Server.srvStreamClause (atomic (identEq `stream) >> strLit >> ":" >> srvContractSuite "expected indented `stream` body" srvContractLine)
def srvFnClause : Parser := withP `Qed.Server.srvFnClause
  (atomic (optional (identEq `read_only) >> identEq `rpc) >> callSig srvParam >> ":" >> srvContractSuite "expected indented RPC body" srvContractLine)
def srvHelperFnClause : Parser := withP `Qed.Server.srvHelperFnClause
  (atomic (optional (identEq `read_only) >> identEq `fn) >> ident >> checkNoWsBefore "" >> "(" >> commaSep srvParam >> ")" >> optional (" -> " >> qType) >> ":" >>
    srvContractSuite "expected indented helper function body" srvContractLine)
def srvBeforeClause : Parser := withP `Qed.Server.srvBeforeClause (atomic (identEq `before >> ":") >> qedSuite)
def srvJobClause : Parser := withP `Qed.Server.srvJobClause
  (atomic (identEq `every) >> numLit >> ident >> ident >> optional (" -> " >> qType) >> ":" >> srvContractSuite "expected indented `every` job body" srvContractLine)
def srvExMethod : Parser := extHttpMethod <|> identEq `GET <|> identEq `POST <|> identEq `PUT <|> identEq `PATCH <|> identEq `DELETE
private def srvExItemP : Parser :=
  withP `Qed.Server.srvExWithEq    (atomic (symbol "with" >> (identEq `now <|> identEq `session <|> identEq `query <|> identEq `body <|> identEq `principal <|> identEq `ctx <|> identEq `state) >> "=") >> qExpr) <|>
  withP `Qed.Server.srvExWithStrEq (atomic (symbol "with" >> (identEq `env <|> identEq `header <|> identEq `file)) >> strLit >> "=" >> qExpr) <|>
  withP `Qed.Server.srvExWithExpr  (atomic (symbol "with" >> (identEq `user <|> identEq `role)) >> qExpr) <|>
  withP `Qed.Server.srvExWithHttp  (atomic (symbol "with" >> (identEq `http <|> identEq `http_error)) >> srvExMethod >> strLit >> "=>" >> numLit >> optional (checkLineEq >> qExpr)) <|>
  withP `Qed.Server.srvExWithProc  (atomic (symbol "with" >> identEq `proc) >> strLit >> "=>" >> numLit >> optional (checkLineEq >> qExpr)) <|>
  withP `Qed.Server.srvExDb        (atomic (symbol "with" >> identEq `db) >> ident >> "=" >> qExpr) <|>
  withP `Qed.Server.srvExCall      (atomic (identEq `call) >> ident >> checkNoWsBefore "" >> "(" >> commaSep qExpr >> ")") <|>
  withP `Qed.Server.srvExReq       (atomic (extHttpMethod >> strLit)) <|>
  withP `Qed.Server.srvExExpectOk     (atomic (identEq `expect >> identEq `ok) >> optional (checkNoWsBefore "" >> "(" >> qExpr >> ")")) <|>
  withP `Qed.Server.srvExExpectErr    (atomic (identEq `expect >> identEq `error) >> optional (checkNoWsBefore "" >> "(" >> numLit >> ")")) <|>
  withP `Qed.Server.srvExExpectStatus (atomic (identEq `expect >> identEq `status >> "==") >> qExpr) <|>
  withP `Qed.Server.srvExExpectExpr   (atomic (identEq `expect >> notFollowedBy (identEq `ok <|> identEq `error <|> (identEq `status >> "==")) "expect expr") >> qExpr)
def srvExampleClause : Parser := withP `Qed.Server.srvExampleClause (atomic (symbol "example" >> ident >> ":") >> checkColGt "expected indented `example` steps" >> many1Indent srvExItemP)
def srvOnCreateAccountClause : Parser := authHook `Qed.Server.srvOnCreateAccountClause `onCreateAccount
def srvOnSignInClause : Parser := authHook `Qed.Server.srvOnSignInClause `onSignIn
def srvDocClause : Parser := withP `Qed.Server.srvDocClause (Command.docComment >> checkColEq >> categoryParser `srvClause 0)
@[srvClause_parser] def srvClauseP : Parser := opaqueP (
  srvDocClause <|> srvDbClause <|> srvEnvClause <|> srvSecretClause <|> srvStateClause <|>
  srvInvMutatingClause <|> srvInvClause <|>
  srvChannelClause <|> srvHttpRouteClause <|> srvStreamClause <|> srvFnClause <|> srvHelperFnClause <|>
  srvBeforeClause <|> srvJobClause <|> srvExampleClause <|> srvOnCreateAccountClause <|> srvOnSignInClause)

@[command_parser] def serverCmd : Parser := opaqueP (
  node `Qed.Server.serverCmd (optional Command.docComment >> withPosition (atomic (identEq `server >> optional (atomic (identEq `stateless)) >> ident >> ":") >> checkColGt "expected indented `server` body" >> many1Indent (categoryParser `srvClause 0))))
@[command_parser] def serviceCmd : Parser := opaqueP (
  node `Qed.Server.serviceCmd (optional Command.docComment >> withPosition (atomic (identEq `service >> ident >> ":") >> checkColGt "expected indented `service` body" >> many1Indent (categoryParser `srvClause 0))))
@[command_parser] def fullstackCmd : Parser := opaqueP (
  node `Qed.Server.fullstackCmd (optional Command.docComment >> withPosition (atomic (identEq `fullstack >> ident >> ":") >> checkColGt "expected indented `fullstack` clauses" >>
    many1Indent (withP `Qed.Server.fsServerClause (atomic (identEq `server) >> ident) <|> withP `Qed.Server.fsClientClause (atomic (identEq `client) >> ident) <|> withP `Qed.Server.fsTitleClause (atomic (identEq `title) >> strLit)))))

end SrvParsers

def lowerSrvType (stx : Lean.Syntax) (allowFallible : Bool := false) (ctxDesc : String := "") : Lean.MacroM Qed.Lang.LoweredQedType :=
  Qed.Lang.lowerQedTypeInfo stx (allowFallible := allowFallible) (allowHigherOrder := false) (ctxDesc? := if ctxDesc.isEmpty then none else some ctxDesc)

syntax (name := srvAutoFieldStx) "srvAutoField(" term ")" : term
syntax (name := srvAutoEmitStx)  "srvAutoEmit(" term ")" : term
syntax (name := srvTypedAsStx)   "srvTypedAs(" term ", " term ")" : term
syntax (name := srvGetElemStx)   "srvGetElem(" term ", " term ")" : term
syntax (name := srvSetElemStx)   "srvSetElem(" term ", " term ", " term ")" : term
syntax "qedSrvProveStep " "[" ident,* "]" str str : tactic
syntax "qedSrvPrepStep " "[" ident,* "]" : tactic
syntax "qedSrvProveAsync " ident "[" ident,* "]" str str : tactic
syntax "qedSrvProveAsyncEnsures " ident "[" ident,* "]" str str : tactic
syntax "qedSrvPrepAsyncEnsures " ident "[" ident,* "]" : tactic
syntax "qedSrvProveEffSpec " ident "[" ident,* "]" str str : tactic
syntax "qedSrvPrepEffSpec " ident "[" ident,* "]" : tactic
syntax "qedSrvProveSafeIO " ident : tactic
syntax "qedProveRpcReq" : tactic

end Qed.Server
