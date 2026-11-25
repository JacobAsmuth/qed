import Lean
import Qed.Lang
import Qed.Schema.Registry
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime

namespace Qed.Server.Db

/-! ## `database` Block Surface Syntax -/

declare_syntax_cat dbClause
declare_syntax_cat dbEndpointSpec
declare_syntax_cat dbManagedSubClause
declare_syntax_cat dbTableClause
declare_syntax_cat dbColMod

section DbParsers
open Lean Parser Qed.Lang

private def dbEnvName : Parser := identEq `dev <|> identEq `preview <|> identEq `staging <|> identEq `prod
private def dbExpr : Parser := categoryParser `qedExpr 0
def dbSecretOrEnv : Parser := node `Qed.Server.Db.envRef ((identEq `secret <|> identEq `env) >> "(" >> strLit >> ")" >> optional (" ?? " >> strLit))
private def dbKv (k : Name) : Parser := identEq k >> "=" >> dbSecretOrEnv
private def dbIndented (msg : String) (cat : Name) : Parser := ":" >> checkColGt msg >> many1Indent (categoryParser cat 0)

@[dbEndpointSpec_parser] def dbEpUrl       : Parser := leading_parser atomic (identEq `url) >> dbSecretOrEnv
@[dbEndpointSpec_parser] def dbEpPostgres  : Parser := leading_parser atomic (identEq `postgres) >> dbSecretOrEnv
@[dbEndpointSpec_parser] def dbEpSqliteLit : Parser := leading_parser atomic (identEq `sqlite) >> strLit
@[dbEndpointSpec_parser] def dbEpSqliteEnv : Parser := leading_parser atomic (identEq `sqlite) >> dbSecretOrEnv
@[dbEndpointSpec_parser] def dbEpD1        : Parser := leading_parser atomic (identEq `d1) >> dbKv `account >> "," >> dbKv `db >> "," >> dbKv `token
@[dbEndpointSpec_parser] def dbEpTurso     : Parser := leading_parser atomic (identEq `turso) >> dbKv `url >> "," >> dbKv `token
@[dbEndpointSpec_parser] def dbEpHttp      : Parser := leading_parser atomic (identEq `http) >> dbKv `url >> optional ("," >> dbKv `token)

@[dbColMod_parser] def dbModPk        : Parser := leading_parser atomic (identEq `primary_key)
@[dbColMod_parser] def dbModImmutable : Parser := leading_parser atomic (identEq `immutable)
@[dbColMod_parser] def dbModUnique    : Parser := leading_parser atomic (identEq `unique)
@[dbColMod_parser] def dbModRefs      : Parser := leading_parser
  atomic (identEq `references) >> ident >> "(" >> ident >> ")" >>
    optional (checkLineEq >> identEq `on_delete >> (identEq `cascade <|> identEq `set_null <|> identEq `restrict))

def dbPolicyOp : Parser := node `Qed.Server.Db.policyOp (identEq `read <|> identEq `write <|> identEq `insert <|> identEq `update <|> identEq `delete)
def dbTransEdge : Parser := node `Qed.Server.Db.transEdge (sepBy1 (categoryParser `qedExpr 55) "->")
def dbEncColTy : Parser := node `Qed.Server.Db.encColTy
  (atomic (identEq `encrypted >> checkNoWsBefore "" >> "(") >>
    categoryParser `qedType 91 >> "," >> identEq `key >> "=" >> dbSecretOrEnv >> ")" >> optional "?")

@[dbTableClause_parser] def dbTablePolicyClause : Parser := leading_parser withPosition (atomic (identEq `policy) >> sepBy1 dbPolicyOp "," >> kw "requires" >> sepBy1 dbExpr ",")
@[dbTableClause_parser] def dbTableTransInvClause : Parser := leading_parser withPosition (atomic ("invariant " >> ident >> ":" >> identEq `transition) >> categoryParser `qedExpr 90 >> ":" >> sepBy1 dbTransEdge ",")
@[dbTableClause_parser] def dbTableInvClause : Parser := leading_parser withPosition ("invariant " >> ident >> ":" >> notFollowedBy (identEq `transition) "transition" >> sepBy1 dbExpr ",")
@[dbTableClause_parser] def dbTableIndexClause : Parser := leading_parser withPosition (atomic (identEq `index) >> "(" >> sepBy1 ident "," >> ")")
@[dbTableClause_parser] def dbTableColClause : Parser := leading_parser
  withPosition (notFollowedBy (identEq `policy <|> identEq `index <|> symbol "invariant") "column" >>
    ident >> ":" >> (dbEncColTy <|> categoryParser `qedType 91) >> many (checkLineEq >> categoryParser `dbColMod 0) >>
    optional (checkLineEq >> symbol "where" >> sepBy1 dbExpr ","))

@[dbManagedSubClause_parser] def dbManagedPreviewEphemeral : Parser := leading_parser withPosition (atomic (identEq `preview >> identEq `ephemeral))
@[dbManagedSubClause_parser] def dbManagedEnvOverride : Parser := leading_parser withPosition (atomic (dbEnvName >> notFollowedBy (identEq `ephemeral) "ephemeral") >> categoryParser `dbEndpointSpec 0)

@[dbClause_parser] def dbManagedClause : Parser := leading_parser withPosition (atomic (identEq `managed >> identEq `postgres) >> optional (dbIndented "expected indented `managed postgres:` clauses" `dbManagedSubClause))
@[dbClause_parser] def dbEnvEpClause : Parser := leading_parser withPosition (atomic (identEq `prod <|> identEq `staging <|> identEq `preview <|> identEq `dev) >> categoryParser `dbEndpointSpec 0)
@[dbClause_parser] def dbPrimaryEpClause : Parser := leading_parser withPosition (categoryParser `dbEndpointSpec 0)
def dbBackfillSetItem : Parser := node `Qed.Server.Db.backfillSetItem (ident >> "=" >> dbExpr)
@[dbClause_parser] def dbBackfillClause : Parser := leading_parser
  withPosition (atomic (identEq `backfill) >> ident >> identEq `set >> "{" >> sepBy1 dbBackfillSetItem "," >> "}" >>
    optional (checkLineEq >> symbol "where" >> dbExpr))
@[dbClause_parser] def dbTableClauseTop : Parser := leading_parser withPosition (atomic (identEq `table) >> ident >> dbIndented "expected indented `table` columns/policies" `dbTableClause)
@[command_parser] def databaseCmd : Parser := leading_parser withPosition ("database " >> ident >> dbIndented "expected indented `database` clauses" `dbClause)

end DbParsers

/-! ## `database` Command Elaborator -/

open Qed.Lang

private structure ParsedCol where
  ident         : Lean.Ident
  colName       : String
  tyTerm        : Lean.Term
  sqlColType    : SqlColType
  isNullable    : Bool
  isNat         : Bool
  isBytes       : Bool
  isPrimaryKey  : Bool
  isImmutable   : Bool
  isUnique      : Bool
  refs?         : Option (Lean.Ident × Lean.Ident)
  onDelete      : OnDeleteAction := .noAction
  enumVariants? : Option (Array String) := none
  encKey?       : Option (String × Option String × Bool) := none
  whereExprs    : Array Lean.Syntax

private structure ParsedTable where
  ident       : Lean.Ident
  tableName   : String
  cols        : Array ParsedCol
  encSecrets  : Array String := #[]
  readPols    : Array Lean.Syntax
  insertPols  : Array Lean.Syntax
  updatePols  : Array Lean.Syntax
  deletePols  : Array Lean.Syntax
  singleInvs  : Array Lean.Syntax
  transInvs   : Array Lean.Syntax
  transChains : Array (Lean.Syntax × Array (Array Lean.Syntax))
  indexes     : Array (Array Lean.Ident)

section DbElabImpl
open Lean Elab Command

@[noinline]
private def parseEndpointSpec (stx : Syntax) (pinEnv? : Option Qed.Cloud.DeployEnv := none) :
    CommandElabM (Term × Array String × Qed.Cloud.DbEnvSpec) := do
  let k := stx.getKind; let secsRef ← IO.mkRef (#[] : Array String)
  let scope : Qed.Cloud.SecretScope := pinEnv?.elim .envScoped .pinned
  let readRef (s : Syntax) (recordSec := true) (onlyIfNoDefault := false) : CommandElabM (Term × Term × String × Option String) := do
    let er ← parseQedEnvRef "database" s
    if recordSec && er.isSecret && (!onlyIfNoDefault || er.default?.isNone) then secsRef.modify (·.push er.envKey)
    return (quote er.envKey, quote er.default?, er.envKey, er.default?)
  let (epT, spec) : Term × Qed.Cloud.DbEnvSpec ←
    if k == ``dbEpUrl then let (kT, _, kS, _) ← readRef (stx.getArg 1); pure (← `(Qed.Server.Db.DbEndpoint.urlEnv $kT), .byoUrl { envVar := kS, scope })
    else if k == ``dbEpPostgres then let (kT, _, kS, _) ← readRef (stx.getArg 1); pure (← `(Qed.Server.Db.DbEndpoint.postgresEnv $kT), .byoPostgres { envVar := kS, scope })
    else if k == ``dbEpSqliteLit then let p := (⟨stx.getArg 1⟩ : TSyntax `str).getString; pure (← `(Qed.Server.Db.DbEndpoint.sqlitePath $(Syntax.mkStrLit p)), .byoSqlite p)
    else if k == ``dbEpSqliteEnv then let (kT, dT, kS, dS?) ← readRef (stx.getArg 1) (onlyIfNoDefault := true); pure (← `(Qed.Server.Db.DbEndpoint.sqliteEnv $kT $dT), .byoSqliteEnv kS dS?)
    else if k == ``dbEpD1 then
      let (accK, accD, accS, _) ← readRef (stx.getArg 3) false; let (dbK, dbD, dbS, _) ← readRef (stx.getArg 7) false; let (tokK, _, tokS, _) ← readRef (stx.getArg 11)
      pure (← `(Qed.Server.Db.DbEndpoint.cloudflareD1 $accK $accD $dbK $dbD $tokK), .byoD1 accS dbS { envVar := tokS, scope })
    else if k == ``dbEpTurso then
      let (uK, _, uS, _) ← readRef (stx.getArg 3); let (tokK, _, tokS, _) ← readRef (stx.getArg 7)
      pure (← `(Qed.Server.Db.DbEndpoint.turso $uK $tokK), .byoTurso uS { envVar := tokS, scope })
    else if k == ``dbEpHttp then
      let (uK, _, uS, _) ← readRef (stx.getArg 3); let tokOpt := stx.getArg 4
      let (tokT, tokRef?) ← if tokOpt.getNumArgs == 4 then let (tT, _, tS, _) ← readRef (tokOpt.getArg 3); pure (← `(some $tT), some { envVar := tS, scope }) else pure (← `(none), none)
      pure (← `(Qed.Server.Db.DbEndpoint.httpSql $uK $tokT), .byoHttpSql uS tokRef?)
    else throwErrorAt stx "unexpected database endpoint specification"
  return (epT, ← secsRef.get, spec)

private partial def unwrapFieldTypeName (e : Expr) : MetaM Name := do
  let e' ← Meta.whnf e
  if e'.isAppOfArity ``Qed.Field 2 then unwrapFieldTypeName e'.getAppArgs[0]!
  else pure (e'.constName?.getD .anonymous)

private def inferSqlColType (pty : LoweredQedType) : CommandElabM (SqlColType × Bool × Bool × Bool) := do
  let mut base := pty.baseName
  if base != `Nat && base != `Int && base != `Bool && base != `Bytes && base != `ByteArray && base != `String && base != `Date then
    let innerTerm := pty.innerOpt?.getD pty.term
    if let some resolved ← liftTermElabM (try pure (some (← unwrapFieldTypeName (← Term.elabType innerTerm))) catch _ => pure none) then
      base := resolved
  match base with
  | `Nat => pure (.int, pty.isOption, true, false)
  | `Int => pure (.int, pty.isOption, false, false)
  | `Bool => pure (.bool, pty.isOption, false, false)
  | `Bytes | `ByteArray => pure (.bytes, pty.isOption, false, true)
  | _ => pure (.text, pty.isOption, false, false)

private partial def lowerDbExpr (colNames : Array String) (rowVar : Ident)
    (oldVar? ctxVar? : Option Ident) (asProp : Bool) (stx : Syntax) : CommandElabM Term := do
  let hooks : LowerHooks CommandElabM := { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun ref id mode => do
      let comps := id.getId.eraseMacroScopes.components
      let t ← match comps with
        | [] => throwErrorAt ref "empty identifier in database predicate"
        | root :: rest =>
            let rs := root.toString
            if rest.isEmpty && rs == "true" then if mode == .propInv then `(True) else `(true)
            else if rest.isEmpty && rs == "false" then if mode == .propInv then `(False) else `(false)
            else if rest.isEmpty && rs == "none" then `(Option.none)
            else if rs == "row" then foldProjTerms ref ⟨rowVar.raw⟩ rest
            else if rs == "ctx" then
              let some cv := ctxVar? | throwErrorAt ref "`ctx` is only in scope inside `policy ... requires ...`"
              foldProjTerms ref ⟨cv.raw⟩ rest
            else if colNames.contains rs then foldProjTerms ref (← `($rowVar.$(mkIdentFrom ref root))) rest
            else pure ⟨id.raw⟩
      if mode == .propInv && comps != [`true] && comps != [`false] then `(qedAsProp($t)) else pure t
    lowerProj := fun _ base field mode => do let t ← `($base.$field); if mode == .propInv then `(qedAsProp($t)) else pure t
    lowerIndex := fun ref _ _ _ => throwErrorAt ref "indexing is not supported in database predicates"
    lowerCall := fun ref callee rawArgs mode go => do
      if callee.getKind == ``qedIdent then
        let nm := (callee.getArg 0).getId.eraseMacroScopes
        if nm == `old || nm == `some then
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt ref s!"`{nm}(...)` expects a single argument"
          let arg := rawArgs[0]!.getArg 0
          if nm == `old then
            let some ov := oldVar? | throwErrorAt ref "`old(...)` is only allowed inside two-state table `invariant` clauses"
            return some (← lowerDbExpr colNames ov none ctxVar? (mode == .propInv) arg)
          else return some (← `(Option.some $(← go .val arg)))
      return none
  }
  lowerQedExpr hooks (if asProp then .propInv else .val) stx

private def quoteSqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

private partial def renderSqlPred? (colNames : Array String) (forRls : Bool) (stx : Syntax) : Option String :=
  let recR := renderSqlPred? colNames forRls; let k := stx.getKind
  if !forRls && k == ``qedLitNum then some (toString (⟨stx.getArg 0⟩ : TSyntax `num).getNat)
  else if !forRls && (k == ``qedLitStr || k == ``qedDotIdent) then
    let s := if k == ``qedLitStr then (⟨stx.getArg 0⟩ : TSyntax `str).getString else (stx.getArg 1).getId.eraseMacroScopes.toString
    if s.any (· == '\x00') then none else some (quoteSqlLit s)
  else if forRls && k == ``qedCall then
    let c := stx.getArg 0; let args := (stx.getArg 2).getSepArgs
    if c.getKind == ``qedIdent && (c.getArg 0).getId.eraseMacroScopes == `some && args.size == 1 && args[0]!.getKind == ``qedCallArgPos then recR (args[0]!.getArg 0) else none
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs; if args.size == 1 then (recR args[0]!).map fun s => "(" ++ s ++ ")" else none
  else if k == ``qedIdent || k == ``qedProj then
    match extractDottedChain? stx with
    | some [s] => if colNames.contains s then some ("\"" ++ s ++ "\"") else if s == "true" then some (if forRls then "TRUE" else "1") else if s == "false" then some (if forRls then "FALSE" else "0") else none
    | some ["row", col] => if colNames.contains col then some ("\"" ++ col ++ "\"") else none
    | some ["ctx", "userId"] => if forRls then some "current_setting('qed.user_id', true)" else none
    | some [col, "length"] | some ["row", col, "length"] => if !forRls && colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | _ => if !forRls && k == ``qedProj && (stx.getArg 2).getId.eraseMacroScopes == `length then (recR (stx.getArg 0)).map fun s => "LENGTH(" ++ s ++ ")" else none
  else if k == ``qedAnd || k == ``qedOr then do return "(" ++ (← recR (stx.getArg 0)) ++ (if k == ``qedAnd then " AND " else " OR ") ++ (← recR (stx.getArg 2)) ++ ")"
  else if !forRls && k == ``qedNot then (recR (stx.getArg 1)).map fun s => "(NOT " ++ s ++ ")"
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs; if links.isEmpty || (forRls && links.size != 1) then none
    let mapOp : String → Option String | "==" => some "=" | "!=" => some "<>" | "<=" => some "<=" | ">=" => some ">=" | "<" => some "<" | ">" => some ">" | _ => none
    let mut lhs := stx.getArg 0; let mut parts : Array String := #[]
    for lk in links do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1; let l ← recR lhs
      let part ← if forRls && opStr == "!=" && rhs.getKind == ``qedIdent && (rhs.getArg 0).getId.eraseMacroScopes == `none then some s!"({l} IS NOT NULL AND {l} <> '')"
        else do let op ← mapOp opStr; let r ← recR rhs; some (if forRls then s!"({l} {op} {r})" else s!"{l} {op} {r}")
      parts := parts.push part; lhs := rhs
    some (String.intercalate " AND " parts.toList)
  else none

private def extractPlainByteBounds (colName : String) (isBytes : Bool) (acc : Nat × Option Nat) (stx : Syntax) : Nat × Option Nat :=
  let u := unwrapParens1 stx
  if u.getKind != ``qedCmp then acc else
  let metric? (s : Syntax) : Option (Nat × Nat) := match extractDottedChain? (unwrapParens1 s) with
    | some [c, m] | some ["row", c, m] =>
        if c != colName then none else if m == "utf8ByteSize" || (isBytes && m == "size") then some (1, 1)
        else if !isBytes && m == "length" then some (1, 4) else none
    | _ => none
  let litNat? (s : Syntax) : Option Nat := let v := unwrapParens1 s; if v.getKind == ``qedLitNum then some (⟨v.getArg 0⟩ : TSyntax `num).getNat else none
  let updMax (cur : Nat × Option Nat) (v : Nat) : Nat × Option Nat := (cur.1, some (cur.2.elim v (min · v)))
  let applyCmp (cur : Nat × Option Nat) (opStr : String) (m : Nat × Nat) (n : Nat) : Nat × Option Nat := match opStr with
    | "<=" => updMax cur (n * m.2) | "<" => updMax cur (if n > 0 then (n - 1) * m.2 else 0)
    | ">=" => (max cur.1 (n * m.1), cur.2) | ">" => (max cur.1 ((n + 1) * m.1), cur.2)
    | "==" => updMax (max cur.1 (n * m.1), cur.2) (n * m.2) | _ => cur
  let flipOp : String → String | "<=" => ">=" | "<" => ">" | ">=" => "<=" | ">" => "<" | s => s
  ((u.getArg 1).getArgs.foldl (init := (u.getArg 0, acc)) fun (lhs, cur) lk =>
    let opStr := cmpOpKind (lk.getArg 0); let rhs := lk.getArg 1
    let cur' := match metric? lhs, litNat? rhs, litNat? lhs, metric? rhs with
      | some m, some n, _, _ => applyCmp cur opStr m n
      | _, _, some n, some m => applyCmp cur (flipOp opStr) m n
      | _, _, _, _ => cur
    (rhs, cur')).2

private def renderEncryptedCheckSql (colName : String) (isBytes : Bool) (whereExprs : Array Syntax) : String :=
  let (minB, maxB?) := (whereExprs.flatMap splitAndStx).foldl (extractPlainByteBounds colName isBytes) (0, none)
  let minC := aeadBase64Len minB
  match maxB? with
  | some maxB => s!"{minC} <= LENGTH(\"{colName}\") AND LENGTH(\"{colName}\") <= {aeadBase64Len maxB}"
  | none => s!"{minC} <= LENGTH(\"{colName}\")"

@[noinline]
private def parseTableClause (dbName : Name) (existing : Array ParsedTable) (c : Syntax) : CommandElabM ParsedTable := do
  let tIdent : Ident := ⟨c.getArg 1⟩; let tName := tIdent.getId.eraseMacroScopes.toString
  if !isSafeSqlIdent tName then throwErrorAt tIdent s!"invalid SQL table name `{tName}`"
  if existing.any (·.tableName == tName) then throwErrorAt tIdent s!"duplicate `table {tName}` in `database {dbName}`"
  let mut cols : Array ParsedCol := #[]; let mut encSecrets : Array String := #[]
  let mut readPols : Array Syntax := #[]; let mut insertPols : Array Syntax := #[]
  let mut updatePols : Array Syntax := #[]; let mut deletePols : Array Syntax := #[]; let mut singleInvs : Array Syntax := #[]
  let mut transInvs : Array Syntax := #[]; let mut transChains : Array (Syntax × Array (Array Syntax)) := #[]; let mut indexes : Array (Array Ident) := #[]
  for sc in (c.getArg 3).getArgs do
    let sk := sc.getKind
    if sk == ``dbTableColClause then
      let colId : Ident := ⟨sc.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
      if !isSafeSqlIdent colName then throwErrorAt colId s!"invalid SQL column name `{colName}`"
      if cols.any (·.colName == colName) then throwErrorAt colId s!"duplicate column `{colName}` in `table {tName}`"
      let tyStx := sc.getArg 2
      let (tyTerm, sqlColType, isNullable, isNat, isBytes, encKey?, enumVariants?) ←
        if tyStx.getKind == `Qed.Server.Db.encColTy then
          let inner ← liftMacroM <| lowerSrvType (tyStx.getArg 2) false s!"encrypted column `{colName}`"
          let isB := inner.baseName == `Bytes || inner.baseName == `ByteArray
          unless inner.baseName == `String || isB do
            throwErrorAt (tyStx.getArg 2) s!"`encrypted(...)` column `{colName}` only supports `String` or `Bytes` inner types"
          let outerOpt := (tyStx.getArg 8).getNumArgs == 1
          let isNull := inner.isOption || outerOpt
          let tyT ← if outerOpt && !inner.isOption then `(Option $(inner.term)) else pure inner.term
          let er ← parseQedEnvRef "database" (tyStx.getArg 6)
          if er.isSecret && er.default?.isNone then encSecrets := pushUnique encSecrets er.envKey
          pure (tyT, SqlColType.text, isNull, false, isB, some (er.envKey, er.default?, isB), none)
        else
          let pty ← liftMacroM <| lowerSrvType tyStx false s!"column `{colName}`"
          let (sqlTy, isNull, isN, isB) ← inferSqlColType pty
          let enumVs? := (Qed.lookupUnitEnum? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pty.baseName).map (·.variants)
          pure (pty.term, sqlTy, isNull, isN, isB, none, enumVs?)
      let mut isPk := false; let mut isImm := false; let mut isUniq := false
      let mut refs? : Option (Ident × Ident) := none; let mut onDelete : OnDeleteAction := .noAction
      for m in (sc.getArg 3).getArgs do
        let mk := m.getKind
        if mk == ``dbModPk then
          if encKey?.isSome then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot be `primary_key`"
          isPk := true
        else if mk == ``dbModImmutable then isImm := true
        else if mk == ``dbModUnique then
          if encKey?.isSome then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot be `unique` (AES-256-GCM uses randomized nonces)"
          isUniq := true
        else if mk == ``dbModRefs then
          if encKey?.isSome then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot use `references`"
          refs? := some (⟨m.getArg 1⟩, ⟨m.getArg 3⟩)
          let odOpt := m.getArg 5
          if odOpt.getNumArgs == 2 then
            onDelete ← match (odOpt.getArg 1).getId.eraseMacroScopes with
              | `cascade => pure .cascade
              | `set_null =>
                  unless isNullable do throwErrorAt (odOpt.getArg 1) s!"`on_delete set_null` on `{tName}.{colName}` requires a nullable column (`T?`)"
                  pure .setNull
              | `restrict => pure .restrict
              | other => throwErrorAt (odOpt.getArg 1) s!"unknown `on_delete` action `{other}` (expected `cascade`, `set_null`, or `restrict`)"
      let wOpt := sc.getArg 4
      cols := cols.push {
        ident := colId, colName, tyTerm, sqlColType, isNullable, isNat, isBytes,
        isPrimaryKey := isPk, isImmutable := isImm, isUnique := isUniq, refs?, onDelete, enumVariants?, encKey?,
        whereExprs := if wOpt.getNumArgs == 2 then (wOpt.getArg 1).getSepArgs else #[] }
    else if sk == ``dbTablePolicyClause then
      let es := (sc.getArg 3).getSepArgs
      for opNode in (sc.getArg 1).getSepArgs do match (opNode.getArg 0).getId.eraseMacroScopes with
        | `read => readPols := readPols ++ es | `insert => insertPols := insertPols ++ es | `update => updatePols := updatePols ++ es
        | `delete => deletePols := deletePols ++ es | `write => insertPols := insertPols ++ es; updatePols := updatePols ++ es; deletePols := deletePols ++ es | _ => pure ()
    else if sk == ``dbTableTransInvClause then
      let chains := (sc.getArg 6).getSepArgs.map fun ch => (ch.getArg 0).getSepArgs
      for ch in chains do if ch.size < 2 then throwErrorAt sc "`transition` invariant expects at least one `a -> b` transition arrow"
      transChains := transChains.push (sc.getArg 4, chains)
    else if sk == ``dbTableInvClause then
      for e in (sc.getArg 3).getSepArgs do if Qed.Server.exprCallsOld e then transInvs := transInvs.push e else singleInvs := singleInvs.push e
    else if sk == ``dbTableIndexClause then indexes := indexes.push ((sc.getArg 2).getSepArgs.map fun s => (⟨s⟩ : Ident))
    else throwErrorAt sc s!"unexpected clause in `table {tName}`"
  if cols.isEmpty then throwErrorAt tIdent s!"`table {tName}` must declare at least one column"
  return { ident := tIdent, tableName := tName, cols, encSecrets, readPols, insertPols, updatePols, deletePols, singleInvs, transInvs, transChains, indexes }

@[noinline]
private def elabTableSchema (t : ParsedTable) (rowTypeName : Name) (colNames : Array String) : CommandElabM Term := do
  let optSqlStr (ps : Array String) : Term := quote (if ps.isEmpty then none else some (String.intercalate " AND " ps.toList))
  let colSchemaTerms ← t.cols.mapM fun col => do
    let cTyT : Term := mkIdent <| match col.sqlColType with | .text => `Qed.Server.Db.SqlColType.text | .int => `Qed.Server.Db.SqlColType.int | .bool => `Qed.Server.Db.SqlColType.bool | .bytes => `Qed.Server.Db.SqlColType.bytes
    let refT ← match col.refs? with
      | some (rt, rc) =>
          let rtT ← mkSqlIdentTerm rt rt.getId.eraseMacroScopes.toString
          let rcT ← mkSqlIdentTerm rc rc.getId.eraseMacroScopes.toString
          `(some ($rtT, $rcT))
      | none => `(none)
    let onDelT : Term := mkIdent <| match col.onDelete with
      | .noAction => `Qed.Server.Db.OnDeleteAction.noAction | .cascade => `Qed.Server.Db.OnDeleteAction.cascade
      | .setNull => `Qed.Server.Db.OnDeleteAction.setNull | .restrict => `Qed.Server.Db.OnDeleteAction.restrict
    let enumChkParts := match col.enumVariants? with
      | some vs =>
          if vs.isEmpty then #[]
          else #["\"" ++ col.colName ++ "\" IN (" ++ String.intercalate ", " (vs.toList.map quoteSqlLit) ++ ")"]
      | none => #[]
    let chkParts := if col.encKey?.isSome then
        #[renderEncryptedCheckSql col.colName col.isBytes col.whereExprs]
      else
        (if col.isNat && !col.isNullable then #["\"" ++ col.colName ++ "\" >= 0"] else #[]) ++
        enumChkParts ++ col.whereExprs.filterMap (renderSqlPred? colNames false)
    let colNameT ← mkSqlIdentTerm col.ident col.colName
    `({ name := $colNameT, colType := $cTyT, nullable := $(quote col.isNullable),
        isPrimaryKey := $(quote col.isPrimaryKey), isUnique := $(quote col.isUnique), isImmutable := $(quote col.isImmutable),
        references? := $refT, onDelete := $onDelT, checkSql? := $(optSqlStr chkParts) : Qed.Server.Db.ColumnSchema })
  let idxTerms ← t.indexes.mapM fun idxs => do
    let idxColTs ← idxs.mapM fun ic => mkSqlIdentTerm ic ic.getId.eraseMacroScopes.toString
    `([$[$idxColTs:term],*])
  let tblNameT ← mkSqlIdentTerm t.ident t.tableName; let schemaId := mkIdentFrom t.ident (rowTypeName ++ `schema)
  let tblCheckTerms : Array Term := (t.singleInvs.filterMap (renderSqlPred? colNames false)).map quote
  let rlsReadT := optSqlStr (t.readPols.filterMap (renderSqlPred? colNames true))
  let rlsWriteT := optSqlStr (t.updatePols.filterMap (renderSqlPred? colNames true))
  elabCommand (← `(command| def $schemaId : Qed.Server.Db.TableSchema := { name := $tblNameT, columns := [$[$colSchemaTerms:term],*], indexes := [$[$idxTerms:term],*], checks := [$[$tblCheckTerms:term],*], rlsRead? := $rlsReadT, rlsWrite? := $rlsWriteT }))
  `($schemaId)

@[noinline]
private def elabTable (dbName fullDbName : Name) (t : ParsedTable) : CommandElabM (DbTableInfo × Term) := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTypeId := mkIdentFrom t.ident rowTypeName
  let (colNames, fIds, fTys) := (t.cols.map (·.colName), t.cols.map (·.ident), t.cols.map (·.tyTerm))
  let (allInhab, allRepr) ← liftTermElabM do
    let mut (hI, hR) := (true, !t.cols.any (·.isBytes))
    for tyT in fTys do
      let ty ← Term.elabType tyT.raw
      if hI then hI := (← Meta.trySynthInstance (← Meta.mkAppM ``Inhabited #[ty])) matches .some _
      if hR then hR := (← Meta.trySynthInstance (← Meta.mkAppM ``Repr #[ty])) matches .some _
    return (hI, hR)
  let mut derives : Array Ident := #[mkIdent `DecidableEq]
  if allInhab then derives := derives.push (mkIdent `Inhabited)
  if allRepr then derives := derives.push (mkIdent `Repr)
  elabCommand (← `(command| structure $rowTypeId where $[$fIds:ident : $fTys:term]* deriving $[$derives:ident],*))
  let specs : Array Qed.StructFieldSpec := t.cols.map fun c => { ident := c.ident, wireKey := c.colName, valTy := c.tyTerm }
  for cmd in (← Qed.mkStructJsonCmds rowTypeId specs { emitNamedDefs := false }) ++ (← Qed.mkStructProtoCmds rowTypeId specs { emitBytesCodec := false, emitLawful := true }) do elabCommand cmd
  let (rowVar, oldVar, ctxVar, valsVar) := (mkIdent `_row, mkIdent `_old, mkIdent `_ctx, mkIdent `_vals)
  let mkSub (s : Name) := mkIdentFrom t.ident (rowTypeName ++ s)
  let allRowExprs := t.cols.flatMap (·.whereExprs) ++ t.singleInvs
  let (rowInvId, rowInvBoolId, rowInvSoundId, transInvId, decodeRowId, encodeRowId) :=
    (mkSub `RowInv, mkSub `rowInvBool, mkSub `rowInvBool_sound, mkSub `TransInv, mkSub `decodeRow, mkSub `encodeRow)
  let mut transProps ← t.transInvs.mapM (lowerDbExpr colNames rowVar (some oldVar) none true)
  for (tgtStx, chains) in t.transChains do
    let oldTgt ← lowerDbExpr colNames oldVar none none false tgtStx; let newTgt ← lowerDbExpr colNames rowVar none none false tgtStx
    let mut disj ← `($newTgt = $oldTgt)
    for ch in chains do for i in [0 : ch.size - 1] do
      disj ← `($disj ∨ ($oldTgt = $(← lowerDbExpr colNames rowVar none none false ch[i]!) ∧ $newTgt = $(← lowerDbExpr colNames rowVar none none false ch[i + 1]!)))
    transProps := transProps.push disj
  let mkPolDef (suf : Name) (es : Array Syntax) : CommandElabM String := do
    let polId := mkSub suf; let conj ← Qed.mkConjBody (← es.mapM (lowerDbExpr colNames rowVar none (some ctxVar) true)) (ascribeProp := false)
    elabCommand (← `(command| set_option linter.unusedVariables false in @[simp] abbrev $polId ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj))
    return String.intercalate " and " (es.toList.map fun pe => (pe.reprint.getD "policy").trimAscii.toString)
  let colDecStmts ← t.cols.zipIdx.mapM fun (col, idx) =>
    `(match ($valsVar)[$(Syntax.mkNumLit (toString idx))]? with
      | some _v => Qed.Server.Db.FromSql.fromSql (α := $(col.tyTerm)) _v
      | none    => Except.error ("missing column `" ++ $(Syntax.mkStrLit col.colName) ++ "` in database row"))
  let fVals2 := fIds
  let rowInvBody ← Qed.mkConjBody (← allRowExprs.mapM (lowerDbExpr colNames rowVar none none true)) (ascribeProp := false)
  let rowInvBoolBody ← mkBoolConj (← allRowExprs.mapM (lowerDbExpr colNames rowVar none none false))
  let transInvBody ← Qed.mkConjBody transProps (ascribeProp := false)
  let encPairs ← t.cols.mapM fun col => do
    `(($(← mkSqlIdentTerm col.ident col.colName), Qed.Server.Db.ToSql.toSql ($rowVar:ident).$(col.ident):ident))
  let tableCmds : Array Syntax := #[
    ← `(command| set_option linter.unusedVariables false in @[simp] abbrev $rowInvId ($rowVar:ident : $rowTypeId) : Prop := $rowInvBody),
    ← `(command| set_option linter.unusedVariables false in def $rowInvBoolId ($rowVar:ident : $rowTypeId) : Bool := $rowInvBoolBody),
    ← `(command| set_option linter.unusedVariables false in theorem $rowInvSoundId ($rowVar:ident : $rowTypeId) (h : $rowInvBoolId $rowVar = true) : $rowInvId $rowVar := by
        unfold $rowInvBoolId at h; simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Qed.Lang.QedVal.val_id] at h
        try exact trivial
        try exact h
        try simp_all),
    ← `(command| set_option linter.unusedVariables false in @[simp] abbrev $transInvId ($oldVar:ident $rowVar:ident : $rowTypeId) : Prop := $transInvBody),
    ← `(command|
        def $decodeRowId ($valsVar:ident : Qed.Server.Db.DbRow) : Except String $rowTypeId := do
          $[let $fIds:ident ← $colDecStmts:term]*
          return { $[$fIds:ident := $fVals2:ident],* }),
    ← `(command|
        def $encodeRowId ($rowVar:ident : $rowTypeId) : List (Qed.Server.Db.SqlIdent × Qed.Server.Db.SqlVal) :=
          [$[$encPairs:term],*])]
  for cmd in tableCmds do elabCommand cmd
  let (readPolLbl, insertPolLbl, updatePolLbl, deletePolLbl) :=
    (← mkPolDef `ReadPolicy t.readPols, ← mkPolDef `InsertPolicy t.insertPols, ← mkPolDef `UpdatePolicy t.updatePols, ← mkPolDef `DeletePolicy t.deletePols)
  let schemaTerm ← elabTableSchema t rowTypeName colNames
  let colInfos : Array DbColumnInfo := t.cols.map fun c => {
    name := c.colName, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable, isUnique := c.isUnique,
    isNullable := c.isNullable, isNat := c.isNat, refs? := c.refs?.map fun (rt, rc) => (rt.getId.eraseMacroScopes.toString, rc.getId.eraseMacroScopes.toString),
    encKey? := c.encKey? }
  return ({
    tableName := t.tableName, rowTypeConst := fullDbName ++ t.ident.getId, columns := colInfos,
    hasReadPolicy := !t.readPols.isEmpty, hasInsertPolicy := !t.insertPols.isEmpty, hasUpdatePolicy := !t.updatePols.isEmpty,
    hasDeletePolicy := !t.deletePols.isEmpty, hasTransInv := !t.transInvs.isEmpty || !t.transChains.isEmpty,
    readPolicyLabel := readPolLbl, insertPolicyLabel := insertPolLbl, updatePolicyLabel := updatePolLbl, deletePolicyLabel := deletePolLbl }, schemaTerm)

private def backfillBinOps : Array (Lean.Name × Lean.Name) := #[
  (``qedAnd, `Qed.Server.Db.SqlBinOp.and), (``qedOr, `Qed.Server.Db.SqlBinOp.or),
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub), (``qedMul, `Qed.Server.Db.SqlBinOp.mul)]

@[noinline]
private partial def lowerBackfillSqlExpr (tbl : ParsedTable) (rowTyId : Ident) (rowVar? : Option String) (stx : Syntax) : CommandElabM Term := do
  let u := unwrapParens1 stx; let k := u.getKind
  let colNames := tbl.cols.map (·.colName)
  let matchCol? (s : Syntax) : Option String :=
    match extractDottedChain? (unwrapParens1 s) with
    | some [rv, col] => if rowVar? == some rv && colNames.contains col then some col else none
    | some [col] => if rowVar?.isNone && colNames.contains col then some col else none
    | _ => none
  let checkNotEnc (ref : Syntax) (col : String) : CommandElabM Unit := do
    if tbl.cols.any fun c => c.colName == col && c.encKey?.isSome then
      throwErrorAt ref s!"`backfill` cannot reference encrypted column `{tbl.tableName}.{col}`"
  let lowerConst (colHint? : Option String) (valStx : Syntax) : CommandElabM Term := do
    let uv := unwrapParens1 valStx
    if uv.getKind == ``qedIdent then
      match (uv.getArg 0).getId.eraseMacroScopes with
      | `true => return ← `(Qed.Server.Db.SqlExpr.litTrue) | `false => return ← `(Qed.Server.Db.SqlExpr.litFalse) | _ => pure ()
    let vT ← liftMacroM (lowerSimpleQedExpr .val valStx)
    match colHint? with
    | some col => mkTypedSqlParamTerm rowTyId (mkIdentFrom valStx (Name.mkSimple col)) vT
    | none => `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $vT))
  if let some col := matchCol? u then
    checkNotEnc u col; return ← `(Qed.Server.Db.SqlExpr.col $(← mkSqlIdentTerm u col))
  match extractDottedChain? u with
  | some [rv, col, "length"] => if rowVar? == some rv && colNames.contains col then
      checkNotEnc u col; return ← `(Qed.Server.Db.SqlExpr.strLen (Qed.Server.Db.SqlExpr.col $(← mkSqlIdentTerm u col)))
  | some [col, "length"] => if rowVar?.isNone && colNames.contains col then
      checkNotEnc u col; return ← `(Qed.Server.Db.SqlExpr.strLen (Qed.Server.Db.SqlExpr.col $(← mkSqlIdentTerm u col)))
  | _ => pure ()
  let sub := lowerBackfillSqlExpr tbl rowTyId rowVar?
  if let some (_, op) := backfillBinOps.find? (·.1 == k) then `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← sub (u.getArg 0)) $(← sub (u.getArg 2)))
  else if k == ``qedNot then `(Qed.Server.Db.SqlExpr.not $(← sub (u.getArg 1)))
  else if k == ``qedCmp then
    let mut lhs := u.getArg 0; let mut cs : Array Term := #[]
    for lk in (u.getArg 1).getArgs do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1
      let rhsNone := (unwrapParens1 rhs).getKind == ``qedIdent && ((unwrapParens1 rhs).getArg 0).getId.eraseMacroScopes == `none
      let c ← if rhsNone && (opStr == "==" || opStr == "!=") then
          let l ← sub lhs; if opStr == "==" then `(Qed.Server.Db.SqlExpr.isNull $l) else `(Qed.Server.Db.SqlExpr.isNotNull $l)
        else
          let some (_, op) := sqlCmpOps.find? (·.1 == opStr) | throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}` in `backfill`"
          let lowerSide (side other : Syntax) := match matchCol? other with
            | some col => if (matchCol? side).isNone && !rowVar?.any (stxMentionsVar · side) then lowerConst (some col) side else sub side
            | none => sub side
          `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← lowerSide lhs rhs) $(← lowerSide rhs lhs))
      cs := cs.push c; lhs := rhs
    match cs.toList with | [] => `(Qed.Server.Db.SqlExpr.litTrue) | c :: rs => rs.foldlM (init := c) fun a x => `(Qed.Server.Db.SqlExpr.binOp .and $a $x)
  else lowerConst none u

@[noinline]
private def elabBackfillClause (dbName : Name) (tables : Array ParsedTable) (bc : Syntax) : CommandElabM Term := do
  let tblId : Ident := ⟨bc.getArg 1⟩; let tblName := tblId.getId.eraseMacroScopes.toString
  let some tbl := tables.find? (·.tableName == tblName) | throwErrorAt tblId s!"`backfill` references unknown table `{tblName}` in `database {dbName}`"
  let rowTyId := mkIdentFrom tblId (dbName ++ tbl.ident.getId)
  let setItems := (bc.getArg 4).getSepArgs
  let mut setPairs : Array Term := #[]
  for item in setItems do
    let colId : Ident := ⟨item.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString; let valStx := item.getArg 2
    let some col := tbl.cols.find? (·.colName == colName) | throwErrorAt colId s!"`backfill {tblName}` references unknown column `{colName}`"
    if col.isPrimaryKey then throwErrorAt colId s!"`backfill {tblName}` cannot modify `primary_key` column `{colName}`"
    if col.encKey?.isSome then throwErrorAt colId s!"`backfill {tblName}` cannot modify encrypted column `{colName}`"
    let valT ← liftMacroM (lowerSimpleQedExpr .val valStx)
    let sqlValT ← mkTypedSqlParamTerm rowTyId (mkIdentFrom colId (Name.mkSimple colName)) valT
    setPairs := setPairs.push (← `(($(← mkSqlIdentTerm colId colName), $sqlValT)))
  let whereT ← if (bc.getArg 6).getNumArgs == 2 then
      let wRaw := unwrapParens1 ((bc.getArg 6).getArg 1)
      if wRaw.getKind == ``qedLam1 then
        let b := wRaw.getArg 0; let rVar := if b.isIdent then b.getId.eraseMacroScopes.toString else "_row"
        lowerBackfillSqlExpr tbl rowTyId (some rVar) (wRaw.getArg 2)
      else lowerBackfillSqlExpr tbl rowTyId none wRaw
    else `(Qed.Server.Db.SqlExpr.litTrue)
  `(Qed.Server.Db.SqlQuery.update $(← mkSqlIdentTerm tblId tblName) [$[$setPairs:term],*] $whereT [])

@[noinline, command_elab databaseCmd]
def elabDatabaseCmd : CommandElab := fun stx => do
  let dbIdent : Ident := ⟨stx.getArg 1⟩; let dbName := dbIdent.getId; let dbShort := dbName.toString; let fullDbName := (← getCurrNamespace) ++ dbName
  let mut primaryEp? : Option (Term × Qed.Cloud.DbEnvSpec) := none
  let mut envSlots : Qed.Cloud.EnvMap (Option (Term × Qed.Cloud.DbEnvSpec)) := Qed.Cloud.EnvMap.ofDefault none
  let mut isManaged := false; let mut hasExplicitEnv := false; let mut secrets : Array String := #[]
  let mut tables : Array ParsedTable := #[]; let mut backfillClauses : Array Syntax := #[]
  let pushSecs (secs cur : Array String) := secs.foldl pushUnique cur
  let managedSpecToTerm : Qed.Cloud.DbEnvSpec → CommandElabM Term
    | .managedPostgres nm env => `(Qed.Server.Db.DbEndpoint.managedPostgres $(quote nm) $(mkIdent (`Qed.Cloud.DeployEnv ++ Name.mkSimple env.toString)))
    | .ephemeralSqlite p | .byoSqlite p => `(Qed.Server.Db.DbEndpoint.sqlitePath $(quote p))
    | _ => throwErrorAt dbIdent s!"internal error lowering managed database target in `database {dbName}`"
  let setEnvSlot (ref : Syntax) (envStr : String) (epStx : Syntax) (inManaged : Bool)
      (curSlots : Qed.Cloud.EnvMap (Option (Term × Qed.Cloud.DbEnvSpec))) (curSecs : Array String) := do
    let some env := Qed.Cloud.DeployEnv.parse? envStr | throwErrorAt ref s!"unexpected environment `{envStr}` in `database {dbName}`"
    if inManaged && env == .prod then throwErrorAt ref s!"cannot override `prod` inside `managed postgres:` in `database {dbName}`"
    if (curSlots.get env).isSome then throwErrorAt ref s!"duplicate `{envStr}` endpoint in `database {dbName}`"
    let (epT, secs, spec) ← parseEndpointSpec epStx (some env)
    return (curSlots.set env (some (epT, spec)), if env == .dev then curSecs else pushSecs secs curSecs)

  for c in (stx.getArg 3).getArgs do
    let k := c.getKind
    if k == ``dbManagedClause then
      if isManaged || primaryEp?.isSome || Qed.Cloud.DeployEnv.all.any (envSlots.get · |>.isSome) then
        throwErrorAt c s!"cannot combine `managed postgres` with other endpoint clauses in `database {dbName}` (nest overrides under `managed postgres:`)"
      isManaged := true; hasExplicitEnv := true; let mut previewEphemeral := false
      if (c.getArg 2).getNumArgs == 2 then
        for sc in ((c.getArg 2).getArg 1).getArgs do
          let sk := sc.getKind
          if sk == ``dbManagedPreviewEphemeral then
            if previewEphemeral || envSlots.preview.isSome then throwErrorAt sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
            previewEphemeral := true
          else if sk == ``dbManagedEnvOverride then
            let envStr := (sc.getArg 0).getId.eraseMacroScopes.toString
            if envStr == "preview" && previewEphemeral then throwErrorAt sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
            let (ns, nsec) ← setEnvSlot sc envStr (sc.getArg 1) true envSlots secrets; envSlots := ns; secrets := nsec
          else throwErrorAt sc s!"unexpected clause in `managed postgres:`"
      let targets := Qed.Cloud.managedPostgresTargets dbShort previewEphemeral (envSlots.dev.map Prod.snd)
      for e in Qed.Cloud.DeployEnv.all do if (envSlots.get e).isNone then let sp := targets.get e; envSlots := envSlots.set e (some (← managedSpecToTerm sp, sp))
      for sr in targets.prod.secrets do secrets := pushSecs #[sr.envVar] secrets
    else if k == ``dbPrimaryEpClause then
      if isManaged || primaryEp?.isSome || envSlots.prod.isSome then throwErrorAt c s!"duplicate endpoint specification in `database {dbName}`"
      let (epT, secs, spec) ← parseEndpointSpec (c.getArg 0) none; primaryEp? := some (epT, spec); secrets := pushSecs secs secrets
    else if k == ``dbEnvEpClause then
      let envStr := (c.getArg 0).getId.eraseMacroScopes.toString
      if isManaged then throwErrorAt c s!"cannot combine `managed postgres` with top-level `{envStr}` endpoint in `database {dbName}` (nest overrides under `managed postgres:`)"
      if envStr == "prod" && primaryEp?.isSome then throwErrorAt c s!"cannot combine a default endpoint with `prod` in `database {dbName}`"
      if envStr != "dev" then hasExplicitEnv := true
      let (ns, nsec) ← setEnvSlot c envStr (c.getArg 1) false envSlots secrets; envSlots := ns; secrets := nsec
    else if k == ``dbTableClauseTop then
      let tbl ← parseTableClause dbName tables c
      secrets := pushSecs tbl.encSecrets secrets
      tables := tables.push tbl
    else if k == ``dbBackfillClause then
      backfillClauses := backfillClauses.push c
    else throwErrorAt c s!"unexpected clause in `database {dbName}`"

  let some _ := envSlots.prod.orElse (fun _ => primaryEp?)
    | throwErrorAt dbIdent s!"`database {dbName}` must specify an endpoint (e.g. `managed postgres`, `postgres ...`, `sqlite ...`, `url secret(\"DATABASE_URL\")`, `d1 ...`, `turso ...`, or `http ...`)"
  let resolved ← envSlots.mapM fun e slot? => match slot?.orElse (fun _ => primaryEp?) with
    | some p => pure p | none => throwErrorAt dbIdent s!"`database {dbName}` is missing a `{e}` endpoint (specify `{e} ...`, a default endpoint, or use `managed postgres`)"
  if tables.isEmpty then throwErrorAt dbIdent s!"`database {dbName}` must declare at least one `table`"

  for t in tables do
    let colNames := t.cols.map (·.colName)
    for col in t.cols do if let some (rtId, rcId) := col.refs? then
      let (rt, rc) := (rtId.getId.eraseMacroScopes.toString, rcId.getId.eraseMacroScopes.toString)
      let some targetTbl := tables.find? (·.tableName == rt) | throwErrorAt rtId s!"table `{t.tableName}` column `{col.colName}` references unknown table `{rt}` in `database {dbName}`"
      unless targetTbl.cols.any (·.colName == rc) do throwErrorAt rcId s!"table `{t.tableName}` column `{col.colName}` references unknown column `{rt}.{rc}`"
    for idxCols in t.indexes do for ic in idxCols do
      let cn := ic.getId.eraseMacroScopes.toString
      unless colNames.contains cn do throwErrorAt ic s!"index on `table {t.tableName}` references unknown column `{cn}`"
      if t.cols.any fun c => c.colName == cn && c.encKey?.isSome then
        throwErrorAt ic s!"cannot index encrypted column `{t.tableName}.{cn}` (AES-256-GCM uses randomized nonces)"

  let mkDb (s : Name) := mkIdentFrom dbIdent (dbName ++ s)
  let (markerId, secretsId, configId, ddlId, rlsDdlId, ensureId, instId, mId) :=
    (mkDb `_qed_database_marker, mkDb `secrets, mkDb `config, mkDb `ddl, mkDb `rlsDdl, mkDb `ensureSchema, mkDb `instSafeIOEnsureSchema, mkIdent `m)
  elabCommand (← `(command| def $markerId : Unit := ()))
  let (tableInfos, tableSchemaTerms) := (← tables.mapM (elabTable dbName fullDbName)).unzip
  let backfillTerms ← backfillClauses.mapM (elabBackfillClause dbName tables)
  let devEpTerm ← match envSlots.dev with | some (dt, _) => `(some $dt) | none => `(none)
  let envEndpointsTerm ← if hasExplicitEnv then `(some ({ dev := $(resolved.dev.1), preview := $(resolved.preview.1), staging := $(resolved.staging.1), prod := $(resolved.prod.1) } : Qed.Cloud.EnvMap Qed.Server.Db.DbEndpoint)) else `(none)
  let secLits := secrets.map Syntax.mkStrLit
  let clientStructId := mkDb `Client
  let clientWithId := mkDb `clientWith
  let clientId := mkDb `client
  let cfgParamId := mkIdent `_cfg
  let mut clientFields : Array (Ident × Term) := #[(mkIdent `config, ← `(Qed.Server.Db.DbConfig))]
  let mut clientInits : Array (Ident × Term) := #[(mkIdent `config, ⟨cfgParamId.raw⟩)]
  for t in tables do
    let rowTyId := mkIdentFrom t.ident (dbName ++ t.ident.getId)
    let tblNameT ← mkSqlIdentTerm t.ident t.tableName
    let colIdTs ← t.cols.mapM fun c => mkSqlIdentTerm c.ident c.colName
    let mut ewTs : Array Term := #[]; let mut erTs : Array Term := #[]
    for (c, idx) in t.cols.zipIdx do
      if let some (kEnv, fb?, isB) := c.encKey? then
        let sp ← mkEncColSpecTerm t.tableName c.colName kEnv fb? isB
        ewTs := ewTs.push (← `(($(Syntax.mkStrLit c.colName), $sp)))
        erTs := erTs.push (← `(($(Syntax.mkNumLit (toString idx)), $sp)))
    let fldId := mkIdentFrom t.ident (Name.mkSimple t.tableName)
    let hTy ← `(Qed.Server.Db.TableHandle $rowTyId)
    let hVal ← `({ config := $cfgParamId, tableName := $tblNameT, columns := [$[$colIdTs:term],*],
                   decodeRow := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `decodeRow)),
                   encodeRow := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `encodeRow)),
                   rowInvBool := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `rowInvBool)),
                   encWrite := [$[$ewTs:term],*], encRead := [$[$erTs:term],*] : Qed.Server.Db.TableHandle $rowTyId })
    clientFields := clientFields.push (fldId, hTy)
    clientInits := clientInits.push (fldId, hVal)
  let cfIds := clientFields.map (·.1); let cfTys := clientFields.map (·.2)
  let ciIds := clientInits.map (·.1); let ciVals := clientInits.map (·.2)
  for cmd in #[
    ← `(command| def $secretsId : Array String := #[$[$secLits:term],*]),
    ← `(command| def $configId : Qed.Server.Db.DbConfig := { name := $(Syntax.mkStrLit dbShort), endpoint := $(resolved.prod.1), devFallback? := $devEpTerm, envEndpoints? := $envEndpointsTerm, isManaged := $(quote isManaged), tables := [$[$tableSchemaTerms:term],*], backfills := [$[$backfillTerms:term],*] }),
    ← `(command| def $ddlId (dialect : Qed.Server.Db.SqlDialect := .postgres) : String := Qed.Server.Db.renderDatabaseDdl dialect ($configId).tables),
    ← `(command| def $rlsDdlId : String := Qed.Server.Db.renderDatabaseRlsDdl ($configId).tables),
    ← `(command| def $ensureId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl $configId),
    ← `(command| instance $instId:ident {_σ : Type} : Qed.Server.SafeIO (@$ensureId (Qed.Server.ThreadProg _σ) _ _) where noAtomic := .io (.dbExecDdl $configId) _ .pure),
    ← `(command| structure $clientStructId where $[$cfIds:ident : $cfTys:term]*),
    ← `(command| def $clientWithId ($cfgParamId:ident : Qed.Server.Db.DbConfig) : $clientStructId := { $[$ciIds:ident := $ciVals:term],* }),
    ← `(command| def $clientId : $clientStructId := $clientWithId $configId),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `ensureSchema)) {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl _c.config),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `transaction)) {$mId:ident : Type → Type} {α : Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) (body : UInt64 → $mId (Except Qed.Server.ApiError α)) : $mId (Except Qed.Server.ApiError α) := Qed.Server.Db.withTransaction _c.config body)
  ] do elabCommand cmd
  modifyEnv fun env => databaseRegistry.addEntry env {
    dbName := fullDbName, shortName := dbShort, configConst := fullDbName ++ `config, ensureSchemaConst := fullDbName ++ `ensureSchema,
    secrets, hasDevFallback := envSlots.dev.isSome, isManaged,
    envSpecs := { dev := resolved.dev.2, preview := resolved.preview.2, staging := resolved.staging.2, prod := resolved.prod.2 }, tables := tableInfos }

end DbElabImpl
end Qed.Server.Db
