import Lean
import Qed.Lang
import Qed.Server.Core

namespace Qed.Server.Db

/-! ## `database` Block Surface Syntax (Sharing `Qed.Lang` Expressions & Types) -/

declare_syntax_cat dbClause
declare_syntax_cat dbEndpointSpec
declare_syntax_cat dbManagedSubClause
declare_syntax_cat dbTableClause
declare_syntax_cat dbColMod

section DbParsers
open Lean Parser Qed.Lang

def dbSecretOrEnv : Parser :=
  node `Qed.Server.Db.envRef ((identEq `secret <|> identEq `env) >> "(" >> strLit >> ")" >> optional (" ?? " >> strLit))

-- Endpoint specs (usable both as primary clause and after `dev `)
@[dbEndpointSpec_parser] def dbEpUrl : Parser := leading_parser
  atomic (identEq `url) >> dbSecretOrEnv

@[dbEndpointSpec_parser] def dbEpPostgres : Parser := leading_parser
  atomic (identEq `postgres) >> dbSecretOrEnv

@[dbEndpointSpec_parser] def dbEpSqliteLit : Parser := leading_parser
  atomic (identEq `sqlite) >> strLit

@[dbEndpointSpec_parser] def dbEpSqliteEnv : Parser := leading_parser
  atomic (identEq `sqlite) >> dbSecretOrEnv

@[dbEndpointSpec_parser] def dbEpD1 : Parser := leading_parser
  atomic (identEq `d1) >>
  identEq `account >> "=" >> dbSecretOrEnv >> "," >>
  identEq `db >> "=" >> dbSecretOrEnv >> "," >>
  identEq `token >> "=" >> dbSecretOrEnv

@[dbEndpointSpec_parser] def dbEpTurso : Parser := leading_parser
  atomic (identEq `turso) >>
  identEq `url >> "=" >> dbSecretOrEnv >> "," >>
  identEq `token >> "=" >> dbSecretOrEnv

@[dbEndpointSpec_parser] def dbEpHttp : Parser := leading_parser
  atomic (identEq `http) >>
  identEq `url >> "=" >> dbSecretOrEnv >>
  optional ("," >> identEq `token >> "=" >> dbSecretOrEnv)

-- Column modifiers
@[dbColMod_parser] def dbModPk        : Parser := leading_parser atomic (identEq `primary_key)
@[dbColMod_parser] def dbModImmutable : Parser := leading_parser atomic (identEq `immutable)
@[dbColMod_parser] def dbModUnique    : Parser := leading_parser atomic (identEq `unique)
@[dbColMod_parser] def dbModRefs      : Parser := leading_parser
  atomic (identEq `references) >> ident >> "(" >> ident >> ")"

-- Table sub-clauses
def dbPolicyOp : Parser :=
  node `Qed.Server.Db.policyOp (
    identEq `read <|> identEq `write <|> identEq `insert <|> identEq `update <|> identEq `delete)

@[dbTableClause_parser] def dbTablePolicyClause : Parser := leading_parser
  withPosition (
    atomic (identEq `policy) >> sepBy1 dbPolicyOp "," >>
    kw "requires" >> sepBy1 (categoryParser `qedExpr 0) ",")

def dbTransEdge : Parser :=
  node `Qed.Server.Db.transEdge (sepBy1 (categoryParser `qedExpr 55) "->")

@[dbTableClause_parser] def dbTableTransInvClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> ident >> ":" >> identEq `transition) >>
    categoryParser `qedExpr 90 >> ":" >> sepBy1 dbTransEdge ",")

@[dbTableClause_parser] def dbTableInvClause : Parser := leading_parser
  withPosition (
    "invariant " >> ident >> ":" >> notFollowedBy (identEq `transition) "transition" >>
    sepBy1 (categoryParser `qedExpr 0) ",")

@[dbTableClause_parser] def dbTableIndexClause : Parser := leading_parser
  withPosition (atomic (identEq `index) >> "(" >> sepBy1 ident "," >> ")")

@[dbTableClause_parser] def dbTableColClause : Parser := leading_parser
  withPosition (
    notFollowedBy (identEq `policy <|> identEq `index <|> symbol "invariant") "column" >>
    ident >> ":" >> categoryParser `qedType 91 >>
    many (checkLineEq >> categoryParser `dbColMod 0) >>
    optional (checkLineEq >> symbol "where" >> sepBy1 (categoryParser `qedExpr 0) ","))

-- Sub-clauses for `managed postgres:`
@[dbManagedSubClause_parser] def dbManagedPreviewEphemeral : Parser := leading_parser
  withPosition (atomic (identEq `preview >> identEq `ephemeral))

@[dbManagedSubClause_parser] def dbManagedEnvOverride : Parser := leading_parser
  withPosition (
    atomic ((identEq `dev <|> identEq `preview <|> identEq `staging <|> identEq `prod) >> notFollowedBy (identEq `ephemeral) "ephemeral") >>
    categoryParser `dbEndpointSpec 0)

-- Top-level `database` clauses
@[dbClause_parser] def dbManagedClause : Parser := leading_parser
  withPosition (
    atomic (identEq `managed >> identEq `postgres) >>
    optional (":" >> checkColGt "expected indented `managed postgres:` clauses" >>
      many1Indent (categoryParser `dbManagedSubClause 0)))

@[dbClause_parser] def dbEnvEpClause : Parser := leading_parser
  withPosition (
    atomic (identEq `prod <|> identEq `staging <|> identEq `preview <|> identEq `dev) >>
    categoryParser `dbEndpointSpec 0)

@[dbClause_parser] def dbPrimaryEpClause : Parser := leading_parser
  withPosition (categoryParser `dbEndpointSpec 0)

@[dbClause_parser] def dbTableClauseTop : Parser := leading_parser
  withPosition (
    atomic (identEq `table) >> ident >> ":" >>
    checkColGt "expected indented `table` columns/policies" >>
    many1Indent (categoryParser `dbTableClause 0))

@[command_parser] def databaseCmd : Parser := leading_parser
  withPosition (
    "database " >> ident >> ":" >>
    checkColGt "expected indented `database` clauses" >>
    many1Indent (categoryParser `dbClause 0))

end DbParsers

end Qed.Server.Db
