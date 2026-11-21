import Lean
import Qed.Lang

namespace Qed.Auth

/-! ## `auth` Block Surface Syntax (Sharing `Qed.Lang` Types & Expressions) -/

declare_syntax_cat authClause
declare_syntax_cat authClaimClause

section AuthParsers
open Lean Parser Qed.Lang

def authEnvRefParser : Parser :=
  node `Qed.Auth.envRef
    ((identEq `secret <|> identEq `env) >> "(" >> strLit >> ")" >> optional (" ?? " >> strLit))

@[authClause_parser] def authIssuerClause : Parser := leading_parser
  withPosition (atomic (identEq `issuer) >> authEnvRefParser)

@[authClause_parser] def authAudienceClause : Parser := leading_parser
  withPosition (atomic (identEq `audience) >> authEnvRefParser)

@[authClause_parser] def authClientIdClause : Parser := leading_parser
  withPosition (atomic (identEq `clientId) >> authEnvRefParser)

@[authClause_parser] def authClientSecretClause : Parser := leading_parser
  withPosition (atomic (identEq `clientSecret) >> authEnvRefParser)

@[authClause_parser] def authProvidersClause : Parser := leading_parser
  withPosition (atomic (identEq `providers) >> "[" >> sepBy ident "," >> "]")

@[authClause_parser] def authSessionClause : Parser := leading_parser
  withPosition (atomic (identEq `session) >> identEq `ttl >> "=" >> numLit)

@[authClaimClause_parser] def authClaimLine : Parser := leading_parser
  withPosition (
    ident >> ":" >> categoryParser `qedType 91 >>
    optional (checkLineEq >> "=" >> categoryParser `qedExpr 0))

@[authClause_parser] def authClaimsClause : Parser := leading_parser
  withPosition (
    atomic (identEq `claims) >> ":" >>
    checkColGt "expected indented `claims:` fields" >>
    many1Indent (categoryParser `authClaimClause 0))

@[command_parser] def authCmd : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> ident >> ":") >>
    checkColGt "expected indented `auth` clauses" >>
    many1Indent (categoryParser `authClause 0))

end AuthParsers

end Qed.Auth
