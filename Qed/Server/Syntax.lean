import Lean
import Qed.Lang
import Qed.Invariant.State

namespace Qed.Server

/-! ## Server, External & Fullstack Surface Syntax -/

declare_syntax_cat extClause
declare_syntax_cat extParam
declare_syntax_cat extWsSubClause
declare_syntax_cat srvClause
declare_syntax_cat srvChanSubClause
declare_syntax_cat fullstackClause

section SrvParsers
open Lean Parser Qed.Lang

private def qExpr : Parser := categoryParser `qedExpr 0
private def qType : Parser := categoryParser `qedType 0
private def secretArg : Parser := identEq `secret >> "(" >> strLit >> ")"
private def indentedCat (msg : String) (cat : Name) : Parser := ":" >> checkColGt msg >> many1Indent (categoryParser cat 0)
private def blockCmd (kw msg : String) (cat : Name) : Parser := withPosition (kw >> ident >> indentedCat msg cat)
private def authHook (kw : Name) : Parser := withPosition (atomic (identEq kw >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)
private def authP (kw : Name) (inner : Parser) : Parser := withPosition (atomic (identEq `auth >> identEq kw) >> "(" >> inner >> ")")
private def callSig (p : Parser) : Parser := ident >> checkNoWsBefore "" >> "(" >> sepBy p "," >> ")" >> " -> " >> qType
private def reconnectP : Parser := withPosition (atomic (kw "reconnect") >> qExpr)
private def srvContractSuite (msg : String) (lineP : Parser) : Parser :=
  checkColGt msg >> withPosition (many (atomic (checkColEq "contract" >> lineP)) >> many1 (checkColEq "statement" >> categoryParser `qedStmt 0))

def srvParam : Parser := node `Qed.Server.srvParam (ident >> ":" >> qType >> optional ("=" >> qExpr))
def srvRequiresLine : Parser := node `Qed.Server.srvRequiresLine (withPosition (atomic (identEq `requires) >> sepBy1 qExpr ","))
def srvEnsuresLine : Parser := node `Qed.Server.srvEnsuresLine (withPosition (atomic (identEq `ensures) >> sepBy1 qExpr "," >> Qed.fnOptProof))
def srvContractLine : Parser := srvRequiresLine <|> srvEnsuresLine
def extHttpMethod : Parser := identEq `get <|> identEq `post <|> identEq `put <|> identEq `patch <|> identEq `delete

@[extParam_parser] def extParamHeader : Parser := leading_parser atomic (identEq `header >> checkNoWsBefore "" >> "(") >> strLit >> ")" >> ident >> ":" >> qType
@[extParam_parser] def extParamQuery  : Parser := leading_parser atomic (identEq `query >> optional (checkNoWsBefore "" >> "(" >> strLit >> ")") >> ident >> ":") >> qType
@[extParam_parser] def extParamPlain  : Parser := leading_parser ident >> ":" >> qType
@[extClause_parser] def extBaseClause : Parser := leading_parser withPosition (atomic (identEq `base) >> strLit)
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
@[command_parser] def externalCmd : Parser := leading_parser blockCmd "external " "expected indented `external` clauses" `extClause

@[srvClause_parser] def srvDbClause : Parser := leading_parser withPosition (atomic (identEq `use) >> ident >> ":" >> ident)
@[srvClause_parser] def srvEnvClause : Parser := leading_parser withPosition (atomic (identEq `env) >> ident >> "=" >> strLit >> optional (" ?? " >> strLit))
@[srvClause_parser] def srvSecretClause : Parser := leading_parser withPosition (atomic (identEq `secret) >> ident >> "=" >> strLit)
@[srvClause_parser] def srvStateClause : Parser := leading_parser withPosition (atomic (identEq `state) >> ident >> ":" >> qType >> optional ("=" >> qExpr))
@[srvClause_parser] def srvInvMutatingClause : Parser := leading_parser withPosition (atomic ("invariant " >> ident >> ":" >> identEq `mutating) >> ident >> kw "requires" >> qExpr)
@[srvClause_parser] def srvInvClause : Parser := leading_parser withPosition ("invariant " >> ident >> ":" >> notFollowedBy (identEq `mutating) "mutating" >> sepBy1 qExpr ",")

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

@[qedStmt_parser] def qedStmtDbTransaction : Parser := leading_parser withPosition (atomic (identDotTransaction >> ":") >> qedSuite)
@[srvClause_parser] def srvHttpRouteClause : Parser := leading_parser withPosition (atomic (extHttpMethod >> strLit >> ":") >> srvContractSuite "expected indented HTTP route body" srvContractLine)
@[srvClause_parser] def srvStreamClause : Parser := leading_parser withPosition (atomic (identEq `stream) >> strLit >> ":" >> srvContractSuite "expected indented `stream` body" srvContractLine)
@[srvClause_parser] def srvFnClause : Parser := leading_parser
  withPosition (optional (atomic (identEq `read_only)) >> atomic (identEq `rpc) >> callSig srvParam >> ":" >> srvContractSuite "expected indented RPC body" srvContractLine)
@[srvClause_parser] def srvHelperFnClause : Parser := leading_parser
  withPosition (optional (atomic (identEq `read_only)) >> atomic (identEq `fn) >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >> optional (" -> " >> qType) >> ":" >>
    srvContractSuite "expected indented helper function body" srvContractLine)
@[srvClause_parser] def srvBeforeClause : Parser := leading_parser withPosition (atomic (identEq `before >> ":") >> qedSuite)
@[srvClause_parser] def srvJobClause : Parser := leading_parser withPosition (atomic (identEq `every) >> numLit >> ident >> ident >> ":" >> qedSuite)
@[srvClause_parser] def srvOnCreateAccountClause : Parser := leading_parser authHook `onCreateAccount
@[srvClause_parser] def srvOnSignInClause : Parser := leading_parser authHook `onSignIn
@[command_parser] def serverCmd : Parser := leading_parser
  withPosition ("server " >> optional (atomic (identEq `stateless)) >> ident >> indentedCat "expected indented `server` body" `srvClause)
@[command_parser] def serviceCmd : Parser := leading_parser
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
syntax "qedSrvProveSafeIO " ident : tactic
syntax "qedProveRpcReq" : tactic

end Qed.Server
