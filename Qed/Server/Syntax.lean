import Lean
import Qed.Lang

namespace Qed.Server

/-! ## Server, External & Fullstack Surface Syntax -/

declare_syntax_cat extClause
declare_syntax_cat extParam
declare_syntax_cat extWsSubClause
declare_syntax_cat srvClause
declare_syntax_cat srvChanSubClause
declare_syntax_cat fullstackClause
declare_syntax_cat srvExItem

section SrvParsers
open Lean Parser Qed.Lang

private def qExpr : Parser := categoryParser `qedExpr 0
private def qType : Parser := withPosition (categoryParser `qedType 0)
private def secretArg : Parser := identEq `secret >> "(" >> strLit >> ")"
private def indentedCat (msg : String) (cat : Name) : Parser := ":" >> checkColGt msg >> many1Indent (categoryParser cat 0)
private def blockCmd (kw msg : String) (cat : Name) : Parser := withPosition (kw >> ident >> indentedCat msg cat)
private def authHook (kw : Name) : Parser := withPosition (atomic (identEq kw >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)
private def authP (kw : Name) (inner : Parser) : Parser := withPosition (atomic (identEq `auth >> identEq kw) >> "(" >> inner >> ")")
private def callSig (p : Parser) : Parser := ident >> checkNoWsBefore "" >> "(" >> sepBy p "," >> ")" >> " -> " >> qType
private def reconnectP : Parser := withPosition (atomic (kw "reconnect") >> qExpr)
private def srvContractSuite (msg : String) (lineP : Parser) : Parser :=
  (checkLineEq >> pushNone >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
  (checkColGt msg >> withPosition (many (atomic (checkColEq "contract" >> lineP)) >> many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

declare_syntax_cat srvContractItem

def srvParam : Parser := node `Qed.Server.srvParam (ident >> ":" >> qType >> optional ("=" >> qExpr))
def srvRequiresLine : Parser := node `Qed.Server.srvRequiresLine (withPosition (atomic (identEq `requires) >> sepBy1 qExpr ","))
def srvEnsuresLine : Parser := node `Qed.Server.srvEnsuresLine (withPosition (atomic (identEq `ensures) >> sepBy1 qExpr "," >> Qed.fnOptProof))
def srvEnsuresErrLine : Parser := node `Qed.Server.srvEnsuresErrLine (withPosition (atomic (identEq `ensures_error) >> sepBy1 qExpr "," >> Qed.fnOptProof))
def srvEnsuresFailsLine : Parser := node `Qed.Server.srvEnsuresFailsLine (withPosition (atomic (identEq `ensures_fails) >> optional (checkLineEq >> numLit) >> Qed.fnOptProof))
def srvEffectTag : Parser := node `Qed.Server.srvEffectTag (identEq `no_http <|> identEq `no_decrypt <|> identEq `no_crypto <|> identEq `no_db_write)
def srvEffectLine : Parser := node `Qed.Server.srvEffectLine (withPosition (atomic (sepBy1 srvEffectTag ",") >> Qed.fnOptProof))
def srvBlindToLine : Parser := node `Qed.Server.srvBlindToLine (withPosition (atomic (identEq `blindTo) >> sepBy1 Qed.fnBlindTarget "," >> Qed.fnOptProof))
@[srvContractItem_parser] def srvCIReq : Parser := leading_parser srvRequiresLine
@[srvContractItem_parser] def srvCIEns : Parser := leading_parser srvEnsuresLine
@[srvContractItem_parser] def srvCIEnsErr : Parser := leading_parser srvEnsuresErrLine
@[srvContractItem_parser] def srvCIEnsFails : Parser := leading_parser srvEnsuresFailsLine
@[srvContractItem_parser] def srvCIEff : Parser := leading_parser srvEffectLine
@[srvContractItem_parser] def srvCIBlind : Parser := leading_parser srvBlindToLine
@[srvContractItem_parser] def srvCIIf : Parser := leading_parser
  withPosition (atomic (symbol "if" >> notFollowedBy (symbol "let") "let" >> sepBy1 qExpr "," >> ":" >>
    checkColGt "expected indented contract clauses" >> many1Indent (categoryParser `srvContractItem 0)))
def srvContractLine : Parser := categoryParser `srvContractItem 0
def extHttpMethod : Parser := identEq `get <|> identEq `post <|> identEq `put <|> identEq `patch <|> identEq `delete

@[extParam_parser] def extParamHeader : Parser := leading_parser atomic (identEq `header >> checkNoWsBefore "" >> "(") >> strLit >> ")" >> ident >> ":" >> qType
@[extParam_parser] def extParamQuery  : Parser := leading_parser atomic (identEq `query >> optional (checkNoWsBefore "" >> "(" >> strLit >> ")") >> ident >> ":") >> qType
@[extParam_parser] def extParamPlain  : Parser := leading_parser ident >> ":" >> qType
def extBaseWhereEnum : Parser := node `Qed.Server.extBaseWhereEnum (atomic (ident >> ":") >> ident)
def extBaseWhereIn   : Parser := node `Qed.Server.extBaseWhereIn (atomic (ident >> symbol "in" >> "[") >> sepBy1 strLit "," >> "]")
def extBaseWhereItem : Parser := extBaseWhereIn <|> extBaseWhereEnum
@[extClause_parser] def extBaseClause : Parser := leading_parser
  withPosition (atomic (identEq `base) >> strLit >> optional (checkLineEq >> symbol "where" >> sepBy1 extBaseWhereItem ","))
@[extClause_parser] def extSsrfGuardClause : Parser := leading_parser withPosition (atomic (identEq `ssrf_guard) >> optional (checkLineEq >> (identEq `true <|> identEq `false)))
@[extClause_parser] def extAuthBearer : Parser := leading_parser authP `bearer secretArg
@[extClause_parser] def extAuthHeader : Parser := leading_parser authP `header (strLit >> ", " >> secretArg)
@[extClause_parser] def extAuthGcp : Parser := leading_parser authP `gcpServiceAccount (secretArg >> optional (", " >> strLit))
@[extClause_parser] def extAuthGcpMeta : Parser := leading_parser
  withPosition (atomic (identEq `auth >> identEq `gcpMetadata) >> optional ("(" >> strLit >> ")"))
@[extClause_parser] def extEndpointClause : Parser := leading_parser
  withPosition (extHttpMethod >> strLit >> checkColGt "expected endpoint signature" >> callSig (categoryParser `extParam 0) >>
    optional (atomic (checkColGt "expected `ok [...]`" >> identEq `ok >> "[") >> sepBy1 numLit "," >> "]"))
@[extWsSubClause_parser] def extWsReqClause : Parser := leading_parser srvRequiresLine
@[extWsSubClause_parser] def extWsReconnectClause : Parser := leading_parser reconnectP
@[extWsSubClause_parser] def extWsSendClause : Parser := leading_parser
  withPosition (atomic (kw "send" >> checkNoWsBefore "" >> "(") >> sepBy1 srvParam "," >> ")" >>
    optional (":" >> checkColGt "expected indented `requires` clauses" >> many1Indent srvRequiresLine))
@[extClause_parser] def extWsClause : Parser := leading_parser
  withPosition (atomic (identEq `ws) >> strLit >> checkColGt "expected WebSocket channel signature" >>
    callSig srvParam >> optional (indentedCat "expected indented `ws` channel clauses" `extWsSubClause))
@[command_parser] def externalCmd : Parser := leading_parser optional Command.docComment >> blockCmd "external " "expected indented `external` clauses" `extClause

@[srvClause_parser] def srvDbClause : Parser := leading_parser withPosition (atomic (identEq `use) >> ident >> ":" >> ident)
@[srvClause_parser] def srvEnvClause : Parser := leading_parser withPosition (atomic (identEq `env) >> ident >> "=" >> strLit >> optional (" ?? " >> strLit))
@[srvClause_parser] def srvSecretClause : Parser := leading_parser withPosition (atomic (identEq `secret) >> ident >> "=" >> strLit)
@[srvClause_parser] def srvStateClause : Parser := leading_parser withPosition (atomic (identEq `state) >> ident >> ":" >> qType >> optional ("=" >> qExpr))
@[srvClause_parser] def srvInvMutatingClause : Parser := leading_parser withPosition (atomic ("invariant " >> ident >> ":" >> identEq `mutating) >> ident >> kw "requires" >> qExpr)
@[srvClause_parser] def srvInvRoutesAuthClause : Parser := leading_parser
  withPosition (atomic ("invariant " >> ident >> ":" >> identEq `routes) >> strLit >>
    optional (identEq `except >> "[" >> sepBy strLit "," >> "]") >> identEq `require >> identEq `auth)
@[srvClause_parser] def srvInvRpcsAuthClause : Parser := leading_parser
  withPosition (atomic ("invariant " >> ident >> ":" >> identEq `rpcs) >>
    optional (identEq `except >> "[" >> sepBy strLit "," >> "]") >> identEq `require >> identEq `auth)
@[srvClause_parser] def srvInvNoSecretsClause : Parser := leading_parser
  withPosition (atomic ("invariant " >> ident >> ":" >> identEq `no_required_secrets))
@[srvClause_parser] def srvInvClause : Parser := leading_parser
  withPosition ("invariant " >> ident >> ":" >> notFollowedBy (identEq `mutating <|> identEq `routes <|> identEq `rpcs <|> identEq `no_required_secrets) "state invariant" >> sepBy1 qExpr ",")

@[srvChanSubClause_parser] def srvChanReqClause : Parser := leading_parser srvRequiresLine
@[srvChanSubClause_parser] def srvChanEnsClause : Parser := leading_parser srvEnsuresLine
@[srvChanSubClause_parser] def srvChanReconnectClause : Parser := leading_parser reconnectP
@[srvChanSubClause_parser] def srvChanOnJoinClause : Parser := leading_parser withPosition (atomic (identEq `on_join) >> optional (" -> " >> qType) >> ":" >> qedSuite)
@[srvChanSubClause_parser] def srvChanOnSendClause : Parser := leading_parser
  withPosition (atomic (identEq `on_send >> checkNoWsBefore "" >> "(") >> sepBy1 srvParam "," >> ")" >> ":" >> srvContractSuite "expected indented `on_send` body" srvRequiresLine)
@[srvChanSubClause_parser] def srvChanOnLeaveClause : Parser := leading_parser withPosition (atomic (identEq `on_leave) >> ":" >> qedSuite)
@[srvChanSubClause_parser] def srvChanProjectClause : Parser := leading_parser
  withPosition (atomic (identEq `project >> checkNoWsBefore "" >> "(") >> srvParam >> ")" >> optional (" -> " >> qType) >> ":" >>
    checkColGt "expected indented `project` body" >>
    withPosition (many (atomic (checkColEq "contract" >> categoryParser `qedFnContract 0)) >>
                  many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))
@[srvClause_parser] def srvChannelClause : Parser := leading_parser
  withPosition (atomic (identEq `channel) >> callSig srvParam >> optional (indentedCat "expected indented `channel` clauses" `srvChanSubClause))

private def identDotTransaction : Parser :=
  leading_parser withFn (fun fn c s =>
    let s' := fn c s
    if s'.hasError then s'
    else match s'.stxStack.back.getId.eraseMacroScopes with
      | .str (.str .anonymous _) "transaction" => s'
      | _ => s.mkError "expected `<db>.transaction`") Parser.ident

@[qedStmt_parser] def qedStmtDbTransaction : Parser := leading_parser
  withPosition (atomic (identDotTransaction >> optional (identEq `as >> ident) >> ":") >> qedSuite)
@[srvClause_parser] def srvHttpRouteClause : Parser := leading_parser withPosition (atomic (extHttpMethod >> strLit >> ":") >> srvContractSuite "expected indented HTTP route body" srvContractLine)
@[srvClause_parser] def srvStreamClause : Parser := leading_parser withPosition (atomic (identEq `stream) >> strLit >> ":" >> srvContractSuite "expected indented `stream` body" srvContractLine)
@[srvClause_parser] def srvFnClause : Parser := leading_parser
  withPosition (optional (atomic (identEq `read_only)) >> atomic (identEq `rpc) >> callSig srvParam >> ":" >> srvContractSuite "expected indented RPC body" srvContractLine)
@[srvClause_parser] def srvHelperFnClause : Parser := leading_parser
  withPosition (optional (atomic (identEq `read_only)) >> atomic (identEq `fn) >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >> optional (" -> " >> qType) >> ":" >>
    srvContractSuite "expected indented helper function body" srvContractLine)
@[srvClause_parser] def srvBeforeClause : Parser := leading_parser withPosition (atomic (identEq `before >> ":") >> qedSuite)
@[srvClause_parser] def srvJobClause : Parser := leading_parser
  withPosition (atomic (identEq `every) >> numLit >> ident >> ident >> optional (" -> " >> qType) >> ":" >>
    srvContractSuite "expected indented `every` job body" srvContractLine)
def srvExMethod : Parser := extHttpMethod <|> identEq `GET <|> identEq `POST <|> identEq `PUT <|> identEq `PATCH <|> identEq `DELETE
@[srvExItem_parser] def srvExEnv : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `env) >> strLit >> "=" >> qExpr)
@[srvExItem_parser] def srvExNow : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `now >> "=") >> qExpr)
@[srvExItem_parser] def srvExUser : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `user) >> qExpr)
@[srvExItem_parser] def srvExRole : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `role) >> qExpr)
@[srvExItem_parser] def srvExSession : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `session >> "=") >> qExpr)
@[srvExItem_parser] def srvExHeader : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `header) >> strLit >> "=" >> qExpr)
@[srvExItem_parser] def srvExQuery : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `query >> "=") >> qExpr)
@[srvExItem_parser] def srvExBody : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `body >> "=") >> qExpr)
@[srvExItem_parser] def srvExCtx : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `ctx >> "=") >> qExpr)
@[srvExItem_parser] def srvExState : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `state >> "=") >> qExpr)
@[srvExItem_parser] def srvExHttp : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `http) >> srvExMethod >> strLit >> "=>" >> numLit >> optional (checkLineEq >> qExpr))
@[srvExItem_parser] def srvExHttpErr : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `http_error) >> srvExMethod >> strLit >> "=>" >> numLit >> optional (checkLineEq >> qExpr))
@[srvExItem_parser] def srvExDb : Parser := leading_parser withPosition (atomic (symbol "with" >> identEq `db) >> ident >> "=" >> qExpr)
@[srvExItem_parser] def srvExCall : Parser := leading_parser withPosition (atomic (identEq `call) >> ident >> checkNoWsBefore "" >> "(" >> sepBy qExpr "," >> ")")
@[srvExItem_parser] def srvExReq : Parser := leading_parser withPosition (atomic (extHttpMethod >> strLit))
@[srvExItem_parser] def srvExExpectOk : Parser := leading_parser withPosition (atomic (identEq `expect >> identEq `ok) >> optional (checkNoWsBefore "" >> "(" >> qExpr >> ")"))
@[srvExItem_parser] def srvExExpectErr : Parser := leading_parser withPosition (atomic (identEq `expect >> identEq `error) >> optional (checkNoWsBefore "" >> "(" >> numLit >> ")"))
@[srvExItem_parser] def srvExExpectStatus : Parser := leading_parser withPosition (atomic (identEq `expect >> identEq `status >> "==") >> qExpr)
@[srvExItem_parser] def srvExExpectExpr : Parser := leading_parser withPosition (atomic (identEq `expect >> notFollowedBy (identEq `ok <|> identEq `error <|> (identEq `status >> "==")) "expect expr") >> qExpr)

@[srvClause_parser] def srvExampleClause : Parser := leading_parser
  withPosition (atomic (symbol "example" >> ident >> ":") >>
    checkColGt "expected indented `example` steps" >> many1Indent (categoryParser `srvExItem 0))
@[srvClause_parser] def srvOnCreateAccountClause : Parser := leading_parser authHook `onCreateAccount
@[srvClause_parser] def srvOnSignInClause : Parser := leading_parser authHook `onSignIn
@[srvClause_parser] def srvDocClause : Parser := leading_parser withPosition (Command.docComment >> checkColEq >> categoryParser `srvClause 0)
@[command_parser] def serverCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition ("server " >> optional (atomic (identEq `stateless)) >> ident >> indentedCat "expected indented `server` body" `srvClause)
@[command_parser] def serviceCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (atomic (identEq `service >> ident >> ":") >> checkColGt "expected indented `service` body" >> many1Indent (categoryParser `srvClause 0))

@[fullstackClause_parser] def fsServerClause : Parser := leading_parser withPosition ("server " >> ident)
@[fullstackClause_parser] def fsClientClause : Parser := leading_parser withPosition (atomic (identEq `client) >> ident)
@[fullstackClause_parser] def fsTitleClause : Parser := leading_parser withPosition (atomic (identEq `title) >> strLit)
@[command_parser] def fullstackCmd : Parser := leading_parser blockCmd "fullstack " "expected indented `fullstack` clauses" `fullstackClause

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
