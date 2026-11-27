import Lean
import Qed.Lang
import Qed.Verify.Core
import Qed.Schema.Registry
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime
import Qed.Server.Db.QueryLower

namespace Qed.Server.Db

/-! ## `qedDbProve` Tactic (Decoupled from `QueryLower.lean`) -/

open Lean Meta Elab Tactic in
@[noinline, tactic qedDbProveTac] def elabQedDbProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  let simpNames := Qed.Verify.Core.dbBaseSimpNames.push ``eq_self; let simprocs := #[``Qed.Server.qedReduceStrLen]
  let okOpaque ← Qed.Verify.Core.tryRestoreM false id do
    let g0 ← getMainGoal
    let g1 ← g0.withContext do
      let fvs ← Qed.Verify.Core.collectLCtxDecls fun ld =>
        pure (if ld.isLet && ld.userName.eraseMacroScopes == `_insRow then some ld.fvarId else none)
      if fvs.isEmpty then pure g0 else g0.replaceTargetDefEq (← Meta.zetaDeltaFVars (← instantiateMVars (← g0.getType)) fvs)
    replaceMainGoal [g1]
    Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs (simpCfg := { zetaDelta := false }) (harvestFacts := true) (scanLCtxValues := false) (clearErrorsOnFail := true)
  if okOpaque then return
  if !(← Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs (harvestFacts := true)) then
    Qed.Diag.throwUnsolvedGoals
      m!"Database {(⟨stx.getArg 4⟩ : TSyntax `str).getString} failed in `{(⟨stx.getArg 5⟩ : TSyntax `str).getString}`:"
      m!"\n\nHint: {(⟨stx.getArg 6⟩ : TSyntax `str).getString}"
      (ref? := some stx) (stripPrefixes := ["_row", "_old", "_new", "r"]) (bulletPrefix := "  • must prove: ")
      (goals? := some [(← getUnsolvedGoals).headD (← getMainGoal)])

/-! ## `database` Block Surface Syntax -/

declare_syntax_cat dbClause
declare_syntax_cat dbTableClause

section DbParsers
open Lean Parser Qed.Lang

private def dbEnvName : Parser := identEq `dev <|> identEq `preview <|> identEq `staging <|> identEq `prod
private def dbExpr : Parser := categoryParser `qedExpr 0
private def dbKv (k : Name) : Parser := identEq k >> "=" >> qedEnvRef
private def dbIndented (msg : String) (p : Parser) : Parser := ":" >> checkColGt msg >> many1Indent p
private def dbEp1 (k n : Name) (p : Parser) : Parser := node k (atomic (identEq n) >> p)

private def dbEndpointSpec : Parser :=
  dbEp1 `Qed.Server.Db.epUrl `url qedEnvRef <|> dbEp1 `Qed.Server.Db.epPostgres `postgres qedEnvRef <|>
  dbEp1 `Qed.Server.Db.epSqlite `sqlite (strLit <|> qedEnvRef) <|>
  dbEp1 `Qed.Server.Db.epD1 `d1 (dbKv `account >> "," >> dbKv `db >> "," >> dbKv `token) <|>
  dbEp1 `Qed.Server.Db.epTurso `turso (dbKv `url >> "," >> dbKv `token) <|>
  dbEp1 `Qed.Server.Db.epHttp `http (dbKv `url >> optional ("," >> dbKv `token))

private def dbColMod : Parser :=
  node `Qed.Server.Db.modSimple (atomic (identEq `primary_key <|> identEq `immutable <|> identEq `unique)) <|>
  node `Qed.Server.Db.modRefs (atomic (identEq `references) >> ident >> "(" >> ident >> ")" >>
    optional (checkLineEq >> identEq `on_delete >> (identEq `cascade <|> identEq `set_null <|> identEq `restrict)))

def dbPolicyOp : Parser := node `Qed.Server.Db.policyOp (identEq `read <|> identEq `write <|> identEq `insert <|> identEq `update <|> identEq `delete)
def dbTransEdge : Parser := node `Qed.Server.Db.transEdge (sepBy1 (categoryParser `qedExpr 55) "->")
def dbEncColTy : Parser := node `Qed.Server.Db.encColTy
  (atomic (identEq `encrypted >> checkNoWsBefore "" >> "(") >> categoryParser `qedType 91 >> "," >> identEq `key >> "=" >> qedEnvRef >>
    optional ("," >> identEq `prevKeys >> "=" >> "[" >> sepBy qedEnvRef "," >> "]") >> ")" >> optional "?")

def dbAssignItem : Parser := node `Qed.Server.Db.assignItem (ident >> "=" >> dbExpr)
def dbPolicyExItem : Parser :=
  node `Qed.Server.Db.polExKv (withPosition (atomic ((identEq `user <|> identEq `role <|> identEq `session <|> identEq `ctx <|> identEq `row) >> "=") >> dbExpr)) <|>
  node `Qed.Server.Db.polExSnap (withPosition (atomic (identEq `snap >> ident >> "=") >> dbExpr))

@[dbTableClause_parser] def dbTablePolicyClause : Parser := leading_parser withPosition (atomic (identEq `policy) >> sepBy1 dbPolicyOp "," >> kw "requires" >> sepBy1 dbExpr ",")
@[dbTableClause_parser] def dbTableTransInvClause : Parser := leading_parser withPosition (atomic ("invariant " >> ident >> ":" >> identEq `transition) >> categoryParser `qedExpr 90 >> ":" >> sepBy1 dbTransEdge ",")
@[dbTableClause_parser] def dbTableInvClause : Parser := leading_parser withPosition ("invariant " >> ident >> ":" >> notFollowedBy (identEq `transition) "transition" >> sepBy1 dbExpr ",")
@[dbTableClause_parser] def dbTableIndexClause : Parser := leading_parser withPosition (atomic (identEq `index) >> "(" >> sepBy1 ident "," >> ")")
@[dbTableClause_parser] def dbTableRowExClause : Parser := leading_parser
  withPosition (atomic ((symbol "example" <|> identEq `rejects) >> ident) >> optional (symbol "from" >> ident) >> ":" >> sepBy1 dbAssignItem ",")
@[dbTableClause_parser] def dbTableTransExClause : Parser := leading_parser
  withPosition (atomic ((identEq `transition_example <|> identEq `transition_rejects) >> ident >> ":") >>
    categoryParser `qedExpr 55 >> "->" >> (sepBy1 (atomic dbAssignItem) "," <|> dbExpr))
@[dbTableClause_parser] def dbTablePolExClause : Parser := leading_parser
  withPosition (atomic ((identEq `policy_allows <|> identEq `policy_denies) >> dbPolicyOp >> ident >> ":") >>
    checkColGt "expected indented policy example clauses" >> many1Indent dbPolicyExItem)
@[dbTableClause_parser] def dbTableColClause : Parser := leading_parser
  withPosition (notFollowedBy (identEq `policy <|> identEq `index <|> symbol "invariant" <|> symbol "example" <|> identEq `rejects <|>
      identEq `transition_example <|> identEq `transition_rejects <|> identEq `policy_allows <|> identEq `policy_denies) "column" >>
    ident >> ":" >> (dbEncColTy <|> categoryParser `qedType 91) >> many (checkLineEq >> dbColMod) >> optional (checkLineEq >> symbol "where" >> sepBy1 dbExpr ","))

private def dbManagedSubClause : Parser :=
  node `Qed.Server.Db.managedPreviewEphemeral (withPosition (atomic (identEq `preview >> identEq `ephemeral))) <|>
  node `Qed.Server.Db.managedEnvOverride (withPosition (atomic (dbEnvName >> notFollowedBy (identEq `ephemeral) "ephemeral") >> dbEndpointSpec))

@[dbClause_parser] def dbManagedClause : Parser := leading_parser withPosition (atomic (identEq `managed >> identEq `postgres) >> optional (dbIndented "expected indented `managed postgres:` clauses" dbManagedSubClause))
@[dbClause_parser] def dbEnvEpClause : Parser := leading_parser withPosition (atomic dbEnvName >> dbEndpointSpec)
@[dbClause_parser] def dbPrimaryEpClause : Parser := leading_parser withPosition dbEndpointSpec
def dbBackfillSetItem : Parser := node `Qed.Server.Db.backfillSetItem (ident >> "=" >> dbExpr)
@[dbClause_parser] def dbBackfillClause : Parser := leading_parser
  withPosition (atomic (identEq `backfill) >> ident >> identEq `set >> "{" >> sepBy1 dbBackfillSetItem "," >> "}" >> optional (checkLineEq >> symbol "where" >> dbExpr))
@[dbClause_parser] def dbTableClauseTop : Parser := leading_parser withPosition (atomic (identEq `table) >> ident >> dbIndented "expected indented `table` columns/policies" (categoryParser `dbTableClause 0))
@[command_parser] def databaseCmd : Parser := leading_parser optional Command.docComment >> withPosition ("database " >> ident >> dbIndented "expected indented `database` clauses" (categoryParser `dbClause 0))

end DbParsers

/-! ## `database` Command Elaborator -/

open Qed.Lang

private structure ParsedCol where
  ident : Lean.Ident
  colName : String
  tyTerm : Lean.Term
  sqlColType : SqlColType
  isNullable : Bool
  isNat : Bool
  isBytes : Bool
  isPrimaryKey : Bool
  isImmutable : Bool
  isUnique : Bool
  refs? : Option (Lean.Ident × Lean.Ident)
  onDelete : OnDeleteAction := .noAction
  enumVariants? : Option (Array String) := none
  encKey? : Option DbEncKeyInfo := none
  whereExprs : Array Lean.Syntax

private structure ParsedTable where
  ident : Lean.Ident
  tableName : String
  cols : Array ParsedCol := #[]
  encSecrets : Array String := #[]
  readPols : Array Lean.Syntax := #[]
  insertPols : Array Lean.Syntax := #[]
  updatePols : Array Lean.Syntax := #[]
  deletePols : Array Lean.Syntax := #[]
  singleInvs : Array Lean.Syntax := #[]
  transInvs : Array Lean.Syntax := #[]
  transChains : Array (Lean.Syntax × Array (Array Lean.Syntax)) := #[]
  indexes : Array (Array Lean.Ident) := #[]
  examples : Array Lean.Syntax := #[]
  rejects : Array Lean.Syntax := #[]
  transExamples : Array Lean.Syntax := #[]
  polExamples : Array Lean.Syntax := #[]

section DbElabImpl
open Lean Elab Command

@[noinline] private def readEpRef (secsRef : IO.Ref (Array String)) (s : Syntax)
    (recordSec := true) (onlyIfNoDefault := false) : CommandElabM (Term × Term × String × Option String) := do
  let er ← parseQedEnvRef "database" s
  if recordSec && er.isSecret && (!onlyIfNoDefault || er.default?.isNone) then secsRef.modify (·.push er.envKey)
  return (quote er.envKey, quote er.default?, er.envKey, er.default?)

@[noinline] private def parseEndpointSpec (qctx : PureQuotCtx) (stx : Syntax) (pinEnv? : Option Qed.Cloud.DeployEnv := none) :
    CommandElabM (Term × Array String × Qed.Cloud.DbEnvSpec) := do
  let secsRef ← IO.mkRef (#[] : Array String); let scope : Qed.Cloud.SecretScope := pinEnv?.elim .envScoped .pinned
  let (epT, spec) : Term × Qed.Cloud.DbEnvSpec ← match stx.getKind with
    | `Qed.Server.Db.epUrl => let (kT, _, kS, _) ← readEpRef secsRef (stx.getArg 1); pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.urlEnv $kT), .byoUrl { envVar := kS, scope })
    | `Qed.Server.Db.epPostgres => let (kT, _, kS, _) ← readEpRef secsRef (stx.getArg 1); pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.postgresEnv $kT), .byoPostgres { envVar := kS, scope })
    | `Qed.Server.Db.epSqlite =>
        let a := stx.getArg 1
        if a.isOfKind strLitKind then let p := (⟨a⟩ : TSyntax `str).getString; pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.sqlitePath $(Syntax.mkStrLit p)), .byoSqlite p)
        else let (kT, dT, kS, dS?) ← readEpRef secsRef a (onlyIfNoDefault := true); pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.sqliteEnv $kT $dT), .byoSqliteEnv kS dS?)
    | `Qed.Server.Db.epD1 =>
        let (accK, accD, accS, _) ← readEpRef secsRef (stx.getArg 3) false; let (dbK, dbD, dbS, _) ← readEpRef secsRef (stx.getArg 7) false; let (tokK, _, tokS, _) ← readEpRef secsRef (stx.getArg 11)
        pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.cloudflareD1 $accK $accD $dbK $dbD $tokK), .byoD1 accS dbS { envVar := tokS, scope })
    | `Qed.Server.Db.epTurso =>
        let (uK, _, uS, _) ← readEpRef secsRef (stx.getArg 3); let (tokK, _, tokS, _) ← readEpRef secsRef (stx.getArg 7)
        pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.turso $uK $tokK), .byoTurso uS { envVar := tokS, scope })
    | `Qed.Server.Db.epHttp =>
        let (uK, _, uS, _) ← readEpRef secsRef (stx.getArg 3); let tokOpt := stx.getArg 4
        let (tokT, tokRef?) ← if tokOpt.getNumArgs == 4 then let (tT, _, tS, _) ← readEpRef secsRef (tokOpt.getArg 3); pure (runQuot qctx `(some $tT), some { envVar := tS, scope })
          else pure (runQuot qctx `(none), none)
        pure (runQuot qctx `(Qed.Server.Db.DbEndpoint.httpSql $uK $tokT), .byoHttpSql uS tokRef?)
    | _ => throwErrorAt stx "unexpected database endpoint specification"
  return (epT, ← secsRef.get, spec)

private partial def unwrapFieldTypeName (e : Expr) : MetaM Name := do
  let e' ← Meta.whnf e
  if e'.isAppOfArity ``Qed.Field 2 then unwrapFieldTypeName e'.getAppArgs[0]! else pure (e'.constName?.getD .anonymous)

private def inferSqlColType (pty : LoweredQedType) : CommandElabM (SqlColType × Bool × Bool × Bool) := do
  let mut base := pty.baseName
  if !#[`Nat, `Int, `Bool, `Bytes, `ByteArray, `String, `Date].contains base then
    if let some r ← liftTermElabM (try pure (some (← unwrapFieldTypeName (← Term.elabType (pty.innerOpt?.getD pty.term)))) catch _ => pure none) then base := r
  match base with
  | `Nat => pure (.int, pty.isOption, true, false) | `Int => pure (.int, pty.isOption, false, false)
  | `Bool => pure (.bool, pty.isOption, false, false) | `Bytes | `ByteArray => pure (.bytes, pty.isOption, false, true)
  | _ => pure (.text, pty.isOption, false, false)

private def exprHasAnyIn (stx : Syntax) : Bool := stxAny (·.getKind == ``qedAnyIn) stx

private partial def validateCrossTableAnyIn (tables : Array ParsedTable) (stx : Syntax) : CommandElabM Unit := do
  if stx.getKind == ``qedAnyIn then
    let aliasId : Ident := ⟨stx.getArg 1⟩; let aliasStr := aliasId.getId.eraseMacroScopes.toString
    unless isSafeSqlIdent aliasStr do throwErrorAt aliasId s!"invalid SQL alias `{aliasStr}` in `any {aliasStr} in ...`"
    let tgt := unwrapParens1 (stx.getArg 3)
    unless tgt.getKind == ``qedIdent do throwErrorAt tgt "cross-table `any <alias> in <table>:` expects a sibling table name from the same `database`"
    let tblName := (tgt.getArg 0).getId.eraseMacroScopes.toString
    let some subTbl := tables.find? (·.tableName == tblName) | throwErrorAt tgt s!"unknown table `{tblName}` in cross-table `any {aliasStr} in {tblName}:`"
    let body := stx.getArg 5
    for col in subTbl.cols do if col.encKey?.isSome then
      if stxAny (fun s => match extractDottedChain? s with | some [a, c] => a == aliasStr && c == col.colName | _ => false) body then
        throwErrorAt body s!"cannot reference encrypted column `{tblName}.{col.colName}` inside cross-table `any {aliasStr} in {tblName}:` predicate"
    validateCrossTableAnyIn tables body
  else for ch in stx.getArgs do validateCrossTableAnyIn tables ch

@[noinline] private partial def lowerDbExpr (qctx : PureQuotCtx) (colNames : Array String) (rowVar : Ident)
    (oldVar? ctxVar? : Option Ident) (asProp : Bool) (stx : Syntax)
    (tables : Array ParsedTable := #[]) (snapVar? : Option Ident := none) : CommandElabM Term := do
  let hooks : LowerHooks (ReaderT (Array String) CommandElabM) := { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun ref id mode => do
      let locals ← read; let comps := id.getId.eraseMacroScopes.components
      let t ← match comps with
        | [] => throwErrorAt ref "empty identifier in database predicate"
        | root :: rest =>
            let rs := root.toString
            if rest.isEmpty && (rs == "true" || rs == "false" || rs == "none") then
              pure (runQuot qctx (if rs == "none" then `(Option.none) else if mode == .propInv then (if rs == "true" then `(True) else `(False)) else (if rs == "true" then `(true) else `(false))))
            else if locals.contains rs then pure (runQuot qctx (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest))
            else if rs == "row" then pure (runQuot qctx (foldProjTerms ref ⟨rowVar.raw⟩ rest))
            else if rs == "ctx" then
              let some cv := ctxVar? | throwErrorAt ref "`ctx` is only in scope inside `policy ... requires ...`"
              pure (runQuot qctx (foldProjTerms ref ⟨cv.raw⟩ rest))
            else if colNames.contains rs then pure (runQuot qctx do foldProjTerms ref (← `($rowVar.$(mkIdentFrom ref root))) rest)
            else if rest.isEmpty && snapVar?.isSome && tables.any (·.tableName == rs) then pure (runQuot qctx `($(snapVar?.get!).$(mkIdentFrom ref root)))
            else pure ⟨id.raw⟩
      return if mode == .propInv && comps != [`true] && comps != [`false] then runQuot qctx `(qedAsProp($t)) else t
    lowerProj := fun _ base field mode => pure (runQuot qctx do let t ← `($base.$field); if mode == .propInv then `(qedAsProp($t)) else pure t)
    lowerIndex := fun ref _ _ _ => throwErrorAt ref "indexing is not supported in database predicates"
    lowerCall := fun ref callee rawArgs mode go => do
      if callee.getKind == ``qedIdent then
        let nm := (callee.getArg 0).getId.eraseMacroScopes
        if nm == `old || nm == `some then
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt ref s!"`{nm}(...)` expects a single argument"
          let arg := rawArgs[0]!.getArg 0
          if nm == `old then
            let some ov := oldVar? | throwErrorAt ref "`old(...)` is only allowed inside two-state table `invariant` clauses"
            return some (← liftM <| lowerDbExpr qctx colNames ov none ctxVar? (mode == .propInv) arg tables snapVar?)
          else let aT ← go .val arg; return some (runQuot qctx `(Option.some $aT))
      return none
    withLocals := fun names k => withReader (· ++ names) k }
  (lowerQedExpr hooks (if asProp then .propInv else .val) stx).run #[]

private def quoteSqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

private partial def renderSqlPred? (tblName : String) (colNames : Array String) (forRls : Bool)
    (tables : Array ParsedTable := #[]) (subAliases : Array (String × Array String) := #[]) (stx : Syntax) : Option String :=
  let recR := renderSqlPred? tblName colNames forRls tables subAliases; let k := stx.getKind
  let renderLit? (s : Syntax) : Option String :=
    let u := unwrapParens1 s; let uk := u.getKind
    if uk == ``qedLitNum then some (toString (⟨u.getArg 0⟩ : TSyntax `num).getNat)
    else if uk == ``qedLitStr || uk == ``qedDotIdent then
      let raw := if uk == ``qedLitStr then (⟨u.getArg 0⟩ : TSyntax `str).getString else (u.getArg 1).getId.eraseMacroScopes.toString
      if raw.any (· == '\x00') then none else some (quoteSqlLit raw)
    else none
  if k == ``qedLitNum || k == ``qedLitStr || k == ``qedDotIdent then renderLit? stx
  else if forRls && k == ``qedAnyIn then do
    let aliasStr := (stx.getArg 1).getId.eraseMacroScopes.toString; guard (isSafeSqlIdent aliasStr)
    let tgt := unwrapParens1 (stx.getArg 3); guard (tgt.getKind == ``qedIdent)
    let subTblName := (tgt.getArg 0).getId.eraseMacroScopes.toString
    let subTbl ← tables.find? (·.tableName == subTblName)
    let subCols := subTbl.cols.filter (·.encKey?.isNone) |>.map (·.colName)
    let bodySql ← renderSqlPred? tblName colNames true tables (subAliases.push (aliasStr, subCols)) (stx.getArg 5)
    some s!"EXISTS (SELECT 1 FROM \"{subTblName}\" AS \"{aliasStr}\" WHERE {bodySql})"
  else if forRls && k == ``qedCall then
    let c := stx.getArg 0; let args := (stx.getArg 2).getSepArgs
    if c.getKind == ``qedIdent && (c.getArg 0).getId.eraseMacroScopes == `some && args.size == 1 && args[0]!.getKind == ``qedCallArgPos then recR (args[0]!.getArg 0) else none
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs; if args.size == 1 then (recR args[0]!).map fun s => "(" ++ s ++ ")" else none
  else if k == ``qedIdent || k == ``qedProj then
    let qualCol (c : String) := if forRls then "\"" ++ tblName ++ "\".\"" ++ c ++ "\"" else "\"" ++ c ++ "\""
    match extractDottedChain? stx with
    | some [al, col] =>
        if let some (_, alCols) := subAliases.reverse.find? (·.1 == al) then if alCols.contains col then some ("\"" ++ al ++ "\".\"" ++ col ++ "\"") else none
        else if al == "row" && colNames.contains col then some (qualCol col)
        else if al == "ctx" && col == "userId" && forRls then some "current_setting('qed.user_id', true)"
        else if !forRls && col == "length" && colNames.contains al then some ("LENGTH(\"" ++ al ++ "\")") else none
    | some [s] =>
        if colNames.contains s then some (qualCol s)
        else if s == "true" then some (if forRls then "TRUE" else "1") else if s == "false" then some (if forRls then "FALSE" else "0") else none
    | some ["row", col, "length"] => if !forRls && colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | _ => if !forRls && k == ``qedProj && (stx.getArg 2).getId.eraseMacroScopes == `length then (recR (stx.getArg 0)).map fun s => "LENGTH(" ++ s ++ ")" else none
  else if k == ``qedAnd || k == ``qedOr then do return "(" ++ (← recR (stx.getArg 0)) ++ (if k == ``qedAnd then " AND " else " OR ") ++ (← recR (stx.getArg 2)) ++ ")"
  else if k == ``qedNot then (recR (stx.getArg 1)).map fun s => "(NOT " ++ s ++ ")"
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs; if links.isEmpty || (forRls && links.size != 1) then none
    let mapOp : String → Option String | "==" => some "=" | "!=" => some "<>" | "<=" => some "<=" | ">=" => some ">=" | "<" => some "<" | ">" => some ">" | _ => none
    let mut lhs := stx.getArg 0; let mut parts : Array String := #[]
    for lk in links do
      let opStr := cmpOpKind (lk.getArg 0); let rhs := lk.getArg 1; let l ← recR lhs
      let part ←
        if forRls && opStr == "!=" && (unwrapParens1 rhs).getKind == ``qedIdent && ((unwrapParens1 rhs).getArg 0).getId.eraseMacroScopes == `none then
          some s!"({l} IS NOT NULL AND {l} <> '')"
        else if opStr == "in" || opStr == "not in" then do
          let uArr := unwrapParens1 rhs; guard (uArr.getKind == ``qedArrLit)
          let items ← (uArr.getArg 1).getSepArgs.mapM renderLit?
          if items.isEmpty then some (if opStr == "in" then (if forRls then "FALSE" else "0") else (if forRls then "TRUE" else "1"))
          else some s!"({l} {if opStr == "in" then "IN" else "NOT IN"} ({String.intercalate ", " items.toList}))"
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
  let updMax (cur : Nat × Option Nat) (v : Nat) := (cur.1, some (cur.2.elim v (min · v)))
  let applyCmp (cur : Nat × Option Nat) (opStr : String) (m : Nat × Nat) (n : Nat) := match opStr with
    | "<=" => updMax cur (n * m.2) | "<" => updMax cur (if n > 0 then (n - 1) * m.2 else 0)
    | ">=" => (max cur.1 (n * m.1), cur.2) | ">" => (max cur.1 ((n + 1) * m.1), cur.2)
    | "==" => updMax (max cur.1 (n * m.1), cur.2) (n * m.2) | _ => cur
  let flipOp : String → String | "<=" => ">=" | "<" => ">" | ">=" => "<=" | ">" => "<" | s => s
  ((u.getArg 1).getArgs.foldl (init := (u.getArg 0, acc)) fun (lhs, cur) lk =>
    let opStr := cmpOpKind (lk.getArg 0); let rhs := lk.getArg 1
    let cur' := match metric? lhs, litNat? rhs, litNat? lhs, metric? rhs with
      | some m, some n, _, _ => applyCmp cur opStr m n | _, _, some n, some m => applyCmp cur (flipOp opStr) m n | _, _, _, _ => cur
    (rhs, cur')).2

private def renderEncryptedCheckSql (colName : String) (isBytes : Bool) (whereExprs : Array Syntax) : String :=
  let (minB, maxB?) := (whereExprs.flatMap splitAndStx).foldl (extractPlainByteBounds colName isBytes) (0, none)
  let minC := aeadBase64Len minB
  match maxB? with | some maxB => s!"{minC} <= LENGTH(\"{colName}\") AND LENGTH(\"{colName}\") <= {aeadBase64Len maxB}" | none => s!"{minC} <= LENGTH(\"{colName}\")"

@[noinline] private def parseColMods (tName colName : String) (isNullable isEnc : Bool) (mods : Array Syntax) :
    CommandElabM (Bool × Bool × Bool × Option (Ident × Ident) × OnDeleteAction) := do
  let mut (isPk, isImm, isUniq) := (false, false, false)
  let mut refs? : Option (Ident × Ident) := none; let mut onDelete : OnDeleteAction := .noAction
  for m in mods do
    match m.getKind with
    | `Qed.Server.Db.modSimple =>
        match (m.getArg 0).getId.eraseMacroScopes with
        | `primary_key => do
            if isEnc then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot be `primary_key`"
            isPk := true
        | `immutable => isImm := true
        | `unique => do
            if isEnc then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot be `unique` (AES-256-GCM uses randomized nonces)"
            isUniq := true
        | _ => pure ()
    | `Qed.Server.Db.modRefs =>
        if isEnc then throwErrorAt m s!"encrypted column `{tName}.{colName}` cannot use `references`"
        refs? := some (⟨m.getArg 1⟩, ⟨m.getArg 3⟩); let odOpt := m.getArg 5
        if odOpt.getNumArgs == 2 then
          onDelete ← match (odOpt.getArg 1).getId.eraseMacroScopes with
            | `cascade => pure .cascade | `restrict => pure .restrict
            | `set_null => do
                unless isNullable do throwErrorAt (odOpt.getArg 1) s!"`on_delete set_null` on `{tName}.{colName}` requires a nullable column (`T?`)"
                pure .setNull
            | other => throwErrorAt (odOpt.getArg 1) s!"unknown `on_delete` action `{other}` (expected `cascade`, `set_null`, or `restrict`)"
    | _ => pure ()
  return (isPk, isImm, isUniq, refs?, onDelete)

@[noinline] private def parseTableColClause (qctx : PureQuotCtx) (tName : String) (existingCols : Array ParsedCol) (sc : Syntax) :
    CommandElabM (ParsedCol × Option String) := do
  let colId : Ident := ⟨sc.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
  if !isSafeSqlIdent colName then throwErrorAt colId s!"invalid SQL column name `{colName}`"
  if existingCols.any (·.colName == colName) then throwErrorAt colId s!"duplicate column `{colName}` in `table {tName}`"
  let tyStx := sc.getArg 2; let mut encSec? : Option String := none
  let (tyTerm, sqlColType, isNullable, isNat, isBytes, encKey?, enumVariants?) ←
    if tyStx.getKind == `Qed.Server.Db.encColTy then
      let inner ← liftMacroM <| lowerSrvType (tyStx.getArg 2) false s!"encrypted column `{colName}`"
      let isB := inner.baseName == `Bytes || inner.baseName == `ByteArray
      unless inner.baseName == `String || isB do throwErrorAt (tyStx.getArg 2) s!"`encrypted(...)` column `{colName}` only supports `String` or `Bytes` inner types"
      let outerOpt := (tyStx.getArg 9).getNumArgs == 1; let isNull := inner.isOption || outerOpt
      let tyT := if outerOpt && !inner.isOption then runQuot qctx `(Option $(inner.term)) else inner.term
      let er ← parseQedEnvRef "database" (tyStx.getArg 6)
      if er.isSecret && er.default?.isNone then encSec? := some er.envKey
      let prevOpt := tyStx.getArg 7
      let prevKeys ← if prevOpt.getNumArgs == 6 then (·.toList.map fun pr => (pr.envKey, pr.default?)) <$> (prevOpt.getArg 4).getSepArgs.mapM (parseQedEnvRef "database") else pure []
      pure (tyT, SqlColType.text, isNull, false, isB, some { keyEnv := er.envKey, fallback? := er.default?, isBytes := isB, prevKeys }, none)
    else
      let pty ← liftMacroM <| lowerSrvType tyStx false s!"column `{colName}`"
      let (sqlTy, isNull, isN, isB) ← inferSqlColType pty
      pure (pty.term, sqlTy, isNull, isN, isB, none, (Qed.lookupUnitEnum? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pty.baseName).map (·.variants))
  let (isPrimaryKey, isImmutable, isUnique, refs?, onDelete) ← parseColMods tName colName isNullable encKey?.isSome (sc.getArg 3).getArgs
  let wOpt := sc.getArg 4
  return ({ ident := colId, colName, tyTerm, sqlColType, isNullable, isNat, isBytes, isPrimaryKey, isImmutable, isUnique, refs?, onDelete, enumVariants?, encKey?,
            whereExprs := if wOpt.getNumArgs == 2 then (wOpt.getArg 1).getSepArgs else #[] }, encSec?)

@[noinline] private def applyTableSubClause (qctx : PureQuotCtx) (t : ParsedTable) (sc : Syntax) : CommandElabM ParsedTable := do
  match sc.getKind with
  | ``dbTableColClause =>
      let (col, encSec?) ← parseTableColClause qctx t.tableName t.cols sc
      return { t with cols := t.cols.push col, encSecrets := encSec?.elim t.encSecrets (pushUnique t.encSecrets ·) }
  | ``dbTablePolicyClause =>
      let es := (sc.getArg 3).getSepArgs
      return (sc.getArg 1).getSepArgs.foldl (init := t) fun acc opNode => match (opNode.getArg 0).getId.eraseMacroScopes with
        | `read => { acc with readPols := acc.readPols ++ es } | `insert => { acc with insertPols := acc.insertPols ++ es }
        | `update => { acc with updatePols := acc.updatePols ++ es } | `delete => { acc with deletePols := acc.deletePols ++ es }
        | `write => { acc with insertPols := acc.insertPols ++ es, updatePols := acc.updatePols ++ es, deletePols := acc.deletePols ++ es } | _ => acc
  | ``dbTableTransInvClause =>
      let chains := (sc.getArg 6).getSepArgs.map fun ch => (ch.getArg 0).getSepArgs
      for ch in chains do if ch.size < 2 then throwErrorAt sc "`transition` invariant expects at least one `a -> b` transition arrow"
      return { t with transChains := t.transChains.push (sc.getArg 4, chains) }
  | ``dbTableInvClause =>
      return (sc.getArg 3).getSepArgs.foldl (init := t) fun acc e =>
        if Qed.Server.exprCallsOld e then { acc with transInvs := acc.transInvs.push e } else { acc with singleInvs := acc.singleInvs.push e }
  | ``dbTableIndexClause => return { t with indexes := t.indexes.push ((sc.getArg 2).getSepArgs.map fun s => (⟨s⟩ : Ident)) }
  | ``dbTableRowExClause => return if (sc.getArg 0).isIdent then { t with rejects := t.rejects.push sc } else { t with examples := t.examples.push sc }
  | ``dbTableTransExClause => return { t with transExamples := t.transExamples.push sc }
  | ``dbTablePolExClause => return { t with polExamples := t.polExamples.push sc }
  | _ => throwErrorAt sc s!"unexpected clause in `table {t.tableName}`"

@[noinline] private def parseTableClause (qctx : PureQuotCtx) (dbName : Name) (existing : Array ParsedTable) (c : Syntax) : CommandElabM ParsedTable := do
  let tIdent : Ident := ⟨c.getArg 1⟩; let tName := tIdent.getId.eraseMacroScopes.toString
  if !isSafeSqlIdent tName then throwErrorAt tIdent s!"invalid SQL table name `{tName}`"
  if existing.any (·.tableName == tName) then throwErrorAt tIdent s!"duplicate `table {tName}` in `database {dbName}`"
  let t ← (c.getArg 3).getArgs.foldlM (init := { ident := tIdent, tableName := tName }) (applyTableSubClause qctx)
  if t.cols.isEmpty then throwErrorAt tIdent s!"`table {tName}` must declare at least one column"
  return t

private def optSqlStr (ps : Array String) : Term := quote (if ps.isEmpty then none else some (String.intercalate " AND " ps.toList))

@[noinline] private def mkColSchemaTermPure (tableName : String) (colNames : Array String) (col : ParsedCol) : PureQuotM Term := do
  let cTyT : Term := mkIdent <| match col.sqlColType with | .text => `Qed.Server.Db.SqlColType.text | .int => `Qed.Server.Db.SqlColType.int | .bool => `Qed.Server.Db.SqlColType.bool | .bytes => `Qed.Server.Db.SqlColType.bytes
  let refT ← match col.refs? with
    | some (rt, rc) => `(some ($(← mkSqlIdentTermPure rt.getId.eraseMacroScopes.toString), $(← mkSqlIdentTermPure rc.getId.eraseMacroScopes.toString))) | none => `(none)
  let onDelT : Term := mkIdent <| match col.onDelete with
    | .noAction => `Qed.Server.Db.OnDeleteAction.noAction | .cascade => `Qed.Server.Db.OnDeleteAction.cascade
    | .setNull => `Qed.Server.Db.OnDeleteAction.setNull | .restrict => `Qed.Server.Db.OnDeleteAction.restrict
  let enumChk := match col.enumVariants? with
    | some vs => if vs.isEmpty then #[] else #["\"" ++ col.colName ++ "\" IN (" ++ String.intercalate ", " (vs.toList.map quoteSqlLit) ++ ")"] | none => #[]
  let chkParts := if col.encKey?.isSome then #[renderEncryptedCheckSql col.colName col.isBytes col.whereExprs]
    else (if col.isNat && !col.isNullable then #["\"" ++ col.colName ++ "\" >= 0"] else #[]) ++ enumChk ++ col.whereExprs.filterMap (renderSqlPred? tableName colNames false)
  `({ name := $(← mkSqlIdentTermPure col.colName), colType := $cTyT, nullable := $(quote col.isNullable),
      isPrimaryKey := $(quote col.isPrimaryKey), isUnique := $(quote col.isUnique), isImmutable := $(quote col.isImmutable),
      references? := $refT, onDelete := $onDelT, checkSql? := $(optSqlStr chkParts) : Qed.Server.Db.ColumnSchema })

@[noinline] private def mkTableSchemaCmdPure (t : ParsedTable) (tables : Array ParsedTable) (rowTypeName : Name) (colNames : Array String) :
    PureQuotM (TSyntax `command × Term) := do
  let colSchemaTerms ← t.cols.mapM (mkColSchemaTermPure t.tableName colNames)
  let idxTerms ← t.indexes.mapM fun idxs => do let ts ← idxs.mapM fun ic => mkSqlIdentTermPure ic.getId.eraseMacroScopes.toString; `([$[$ts:term],*])
  let schemaId := mkIdentFrom t.ident (rowTypeName ++ `schema)
  let tblCheckTerms : Array Term := (t.singleInvs.filterMap (renderSqlPred? t.tableName colNames false)).map quote
  let cmd ← `(command| def $schemaId : Qed.Server.Db.TableSchema := {
    name := $(← mkSqlIdentTermPure t.tableName), columns := [$[$colSchemaTerms:term],*], indexes := [$[$idxTerms:term],*],
    checks := [$[$tblCheckTerms:term],*], rlsRead? := $(optSqlStr (t.readPols.filterMap (renderSqlPred? t.tableName colNames true tables))),
    rlsWrite? := $(optSqlStr (t.updatePols.filterMap (renderSqlPred? t.tableName colNames true tables))) })
  return (cmd, ← `($schemaId))

@[noinline] private def elabRowStructAndCodecs (qctx : PureQuotCtx) (tyId : Ident) (cols : Array ParsedCol) : CommandElabM Unit := do
  let (fIds, fTys) := (cols.map (·.ident), cols.map (·.tyTerm))
  let (allInhab, allRepr) ← liftTermElabM do
    let mut (hI, hR) := (true, !cols.any (·.isBytes))
    for tyT in fTys do
      let ty ← Term.elabType tyT.raw
      if hI then hI := (← Meta.trySynthInstance (← Meta.mkAppM ``Inhabited #[ty])) matches .some _
      if hR then hR := (← Meta.trySynthInstance (← Meta.mkAppM ``Repr #[ty])) matches .some _
    return (hI, hR)
  let derives := #[mkIdent `DecidableEq] ++ (if allInhab then #[mkIdent `Inhabited] else #[]) ++ (if allRepr then #[mkIdent `Repr] else #[])
  elabCommand (runQuot qctx `(command| structure $tyId where $[$fIds:ident : $fTys:term]* deriving $[$derives:ident],*))
  let specs : Array Qed.StructFieldSpec := cols.map fun c => { ident := c.ident, wireKey := c.colName, valTy := c.tyTerm }
  for cmd in (← Qed.mkStructJsonCmds tyId specs { emitNamedDefs := false }) ++ (← Qed.mkStructProtoCmds tyId specs { emitBytesCodec := false, emitLawful := true }) do elabCommand cmd

@[noinline] private def mkDecodeRowCmdPure (decFnId tyId : Ident) (cols : Array ParsedCol) : PureQuotM (TSyntax `command) := do
  let valsVar := mkIdent `_vals; let fIds := cols.map (·.ident); let fVals := fIds
  let colDecs ← cols.mapM fun c => return (c.ident, c.colName, ← `(Qed.Server.Db.FromSql.fromSql (α := $(c.tyTerm))))
  let body ← mkDecodeRowBody valsVar colDecs (← `({ $[$fIds:ident := $fVals:ident],* }))
  `(command| def $decFnId ($valsVar:ident : Qed.Server.Db.DbRow) : Except String $tyId := $body)

@[noinline] private def mkTableCoreCmdsPure (rowTypeId : Ident) (mkSub : Name → Ident) (cols : Array ParsedCol)
    (rowInvBody rowInvBoolBody transInvBody : Term) : PureQuotM (Array (TSyntax `command)) := do
  let (rowVar, oldVar) := (mkIdent `_row, mkIdent `_old)
  let (rowInvId, rowInvBoolId, rowInvSoundId) := (mkSub `RowInv, mkSub `rowInvBool, mkSub `rowInvBool_sound)
  let encPairs ← cols.mapM fun col => do `(($(← mkSqlIdentTermPure col.colName), Qed.Server.Db.ToSql.toSql ($rowVar:ident).$(col.ident):ident))
  return #[
    ← `(command| set_option linter.unusedVariables false in @[simp] abbrev $rowInvId ($rowVar:ident : $rowTypeId) : Prop := $rowInvBody),
    ← `(command| set_option linter.unusedVariables false in def $rowInvBoolId ($rowVar:ident : $rowTypeId) : Bool := $rowInvBoolBody),
    ← `(command| set_option linter.unusedVariables false in theorem $rowInvSoundId ($rowVar:ident : $rowTypeId) (h : $rowInvBoolId $rowVar = true) : $rowInvId $rowVar := by
        unfold $rowInvBoolId at h; simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Qed.Lang.QedVal.val_id] at h
        try exact trivial
        try exact h
        try simp_all),
    ← `(command| set_option linter.unusedVariables false in @[simp] abbrev $(mkSub `TransInv) ($oldVar:ident $rowVar:ident : $rowTypeId) : Prop := $transInvBody),
    ← mkDecodeRowCmdPure (mkSub `decodeRow) rowTypeId cols,
    ← `(command| def $(mkSub `encodeRow) ($rowVar:ident : $rowTypeId) : List (Qed.Server.Db.SqlIdent × Qed.Server.Db.SqlVal) := [$[$encPairs:term],*])]

@[noinline] private def mkTableMetaCmdsPure (mkSub : Name → Ident) (metaTyId : Ident) (metaCols : Array ParsedCol) : PureQuotM (Array (TSyntax `command)) := do
  let mColIdTs ← metaCols.mapM fun c => mkSqlIdentTermPure c.colName
  let mColStrLits : Array Term := metaCols.map fun c => Syntax.mkStrLit c.colName
  return #[
    ← `(command| def $(mkSub `metaColumns) : List Qed.Server.Db.SqlIdent := [$[$mColIdTs:term],*]),
    ← `(command| def $(mkSub `metaColNames) : List String := [$[$mColStrLits:term],*]),
    ← mkDecodeRowCmdPure (mkSub `decodeMetaRow) metaTyId metaCols]

@[noinline] private def elabTablePolicy (qctx : PureQuotCtx) (t : ParsedTable) (tables : Array ParsedTable)
    (colNames : Array String) (rowTypeId : Ident) (mkSub : Name → Ident) (snapTyId? : Option Ident)
    (suf : Name) (es : Array Syntax) : CommandElabM (TSyntax `command × String × Bool) := do
  let (rowVar, ctxVar, snapVar) := (mkIdent `_row, mkIdent `_ctx, mkIdent `_dbSnap); let isCross := es.any exprHasAnyIn
  for e in es do if exprHasAnyIn e then validateCrossTableAnyIn tables e
  let lowered ← es.mapM (lowerDbExpr qctx colNames rowVar none (some ctxVar) true · tables (if isCross then snapTyId?.map (fun _ => snapVar) else none))
  if isCross && snapTyId?.isNone then throwErrorAt t.ident "internal error: missing database `Snap` type for cross-table policy"
  let cmd := runQuot qctx do
    let conj ← Qed.mkConjBody lowered (ascribeProp := false)
    if isCross then `(command| set_option linter.unusedVariables false in @[simp] abbrev $(mkSub suf) ($snapVar:ident : $(snapTyId?.get!)) ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj)
    else `(command| set_option linter.unusedVariables false in @[simp] abbrev $(mkSub suf) ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj)
  return (cmd, String.intercalate " and " (es.toList.map fun pe => (pe.reprint.getD "policy").trimAscii.toString), isCross)

@[noinline] private def elabTableBody (qctx : PureQuotCtx) (dbName fullDbName : Name) (tables : Array ParsedTable)
    (snapTyId? : Option Ident) (t : ParsedTable) : CommandElabM (DbTableInfo × Term) := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTypeId := mkIdentFrom t.ident rowTypeName
  let colNames := t.cols.map (·.colName); let (rowVar, oldVar) := (mkIdent `_row, mkIdent `_old)
  let mkSub (s : Name) := mkIdentFrom t.ident (rowTypeName ++ s)
  let allRowExprs := t.cols.flatMap (·.whereExprs) ++ t.singleInvs
  for e in allRowExprs ++ t.transInvs do
    if exprHasAnyIn e then throwErrorAt e "cross-table `any ... in ...:` is only supported in `policy` clauses and query `where` predicates, not single-row `where` / `invariant` rules"
  let mut transProps ← t.transInvs.mapM (lowerDbExpr qctx colNames rowVar (some oldVar) none true)
  for (tgtStx, chains) in t.transChains do
    let (oldTgt, newTgt) := (← lowerDbExpr qctx colNames oldVar none none false tgtStx, ← lowerDbExpr qctx colNames rowVar none none false tgtStx)
    let mut edgePairs : Array (Term × Term) := #[]
    for ch in chains do for i in [0 : ch.size - 1] do
      edgePairs := edgePairs.push (← lowerDbExpr qctx colNames rowVar none none false ch[i]!, ← lowerDbExpr qctx colNames rowVar none none false ch[i + 1]!)
    transProps := transProps.push <| runQuot qctx do edgePairs.foldlM (init := ← `($newTgt = $oldTgt)) fun d (ci, ci1) => `($d ∨ ($oldTgt = $ci ∧ $newTgt = $ci1))
  let rowPropTs ← allRowExprs.mapM (lowerDbExpr qctx colNames rowVar none none true)
  let rowBoolTs ← allRowExprs.mapM (lowerDbExpr qctx colNames rowVar none none false)
  for cmd in (runQuot qctx do mkTableCoreCmdsPure rowTypeId mkSub t.cols (← Qed.mkConjBody rowPropTs (ascribeProp := false)) (← mkBoolConj rowBoolTs) (← Qed.mkConjBody transProps (ascribeProp := false))) do
    elabCommand cmd
  let metaCols := t.cols.filter (·.encKey?.isNone); let hasMeta := t.cols.any (·.encKey?.isSome) && !metaCols.isEmpty
  if hasMeta then
    let metaTyId := mkSub `Meta; elabRowStructAndCodecs qctx metaTyId metaCols
    for cmd in runQuot qctx (mkTableMetaCmdsPure mkSub metaTyId metaCols) do elabCommand cmd
  let polRes ← #[(`ReadPolicy, t.readPols), (`InsertPolicy, t.insertPols), (`UpdatePolicy, t.updatePols), (`DeletePolicy, t.deletePols)].mapM fun (s, es) =>
    elabTablePolicy qctx t tables colNames rowTypeId mkSub snapTyId? s es
  let (schemaCmd, schemaTerm) := runQuot qctx (mkTableSchemaCmdPure t tables rowTypeName colNames)
  for (cmd, _, _) in polRes do elabCommand cmd
  elabCommand schemaCmd
  let colInfos : Array DbColumnInfo := t.cols.map fun c => {
    name := c.colName, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable, isUnique := c.isUnique,
    isNullable := c.isNullable, isNat := c.isNat, isInt := c.sqlColType == .int && !c.isNat,
    refs? := c.refs?.map fun (rt, rc) => (rt.getId.eraseMacroScopes.toString, rc.getId.eraseMacroScopes.toString), encKey? := c.encKey? }
  return ({
    tableName := t.tableName, rowTypeConst := fullDbName ++ t.ident.getId, columns := colInfos, hasMeta,
    hasReadPolicy := !t.readPols.isEmpty, hasInsertPolicy := !t.insertPols.isEmpty, hasUpdatePolicy := !t.updatePols.isEmpty, hasDeletePolicy := !t.deletePols.isEmpty,
    hasCrossReadPolicy := polRes[0]!.2.2, hasCrossInsertPolicy := polRes[1]!.2.2, hasCrossUpdatePolicy := polRes[2]!.2.2, hasCrossDeletePolicy := polRes[3]!.2.2,
    hasTransInv := !t.transInvs.isEmpty || !t.transChains.isEmpty,
    readPolicyLabel := polRes[0]!.2.1, insertPolicyLabel := polRes[1]!.2.1, updatePolicyLabel := polRes[2]!.2.1, deletePolicyLabel := polRes[3]!.2.1 }, schemaTerm)

@[noinline] private def elabBackfillClause (qctx : PureQuotCtx) (dbName : Name) (tableInfos : Array DbTableInfo) (bc : Syntax) : CommandElabM Term := do
  let tblId : Ident := ⟨bc.getArg 1⟩; let tblName := tblId.getId.eraseMacroScopes.toString
  let some tInfo := tableInfos.find? (·.tableName == tblName) | throwErrorAt tblId s!"`backfill` references unknown table `{tblName}` in `database {dbName}`"
  let rowTyId := mkIdentFrom tblId tInfo.rowTypeConst
  let setPairs ← (bc.getArg 4).getSepArgs.mapM fun item => do
    let colId : Ident := ⟨item.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
    let some col := tInfo.columns.find? (·.name == colName) | throwErrorAt colId s!"`backfill {tblName}` references unknown column `{colName}`"
    if col.isPrimaryKey then throwErrorAt colId s!"`backfill {tblName}` cannot modify `primary_key` column `{colName}`"
    if col.encKey?.isSome then throwErrorAt colId s!"`backfill {tblName}` cannot modify encrypted column `{colName}`"
    let valT ← liftMacroM (lowerSimpleQedExpr .val (item.getArg 2)); let colSql ← mkSqlIdentTerm colId colName
    return runQuot qctx do `(($colSql, $(← mkTypedSqlParamTerm rowTyId (mkIdentFrom colId (Name.mkSimple colName)) valT)))
  let whereT ← if (bc.getArg 6).getNumArgs == 2 then
      let wRaw := unwrapParens1 ((bc.getArg 6).getArg 1)
      let (rVar, bodyStx) := if wRaw.getKind == ``qedLam1 then let b := wRaw.getArg 0; (if b.isIdent then b.getId.eraseMacroScopes.toString else "_row", wRaw.getArg 2) else ("", wRaw)
      lowerRowSqlExpr (fun _ e => liftMacroM (lowerSimpleQedExpr .val e)) { dbName, shortName := dbName.toString, configConst := .anonymous, ensureSchemaConst := .anonymous, secrets := #[], tables := tableInfos } #[(rVar, tInfo, tblName)] bodyStx
    else pure (runQuot qctx `(Qed.Server.Db.SqlExpr.litTrue))
  let tblSql ← mkSqlIdentTerm tblId tblName
  return runQuot qctx `(Qed.Server.Db.SqlQuery.update $tblSql [$[$setPairs:term],*] $whereT [])

@[noinline] private def lowerDbExExpr (dbName : Name) (curTable : ParsedTable) (allEx : Std.HashMap String (Array Name)) (stx : Syntax) : CommandElabM Term := do
  let curEx := allEx.getD curTable.tableName #[]
  let hooks : LowerHooks MacroM := { LowerHooks.mkDefault (fun ref msg => Macro.throwErrorAt ref msg) with
    lowerIdent := fun ref id m => do
      let n := id.getId.eraseMacroScopes
      let resolved : Ident := match n with
        | .str .anonymous s => if curEx.contains n then mkIdentFrom ref (dbName ++ curTable.ident.getId ++ n) else if allEx.contains s then mkIdentFrom ref (dbName ++ n) else id
        | .str (.str .anonymous tbl) ex => if (allEx.getD tbl #[]).contains (Name.mkSimple ex) then mkIdentFrom ref (dbName ++ Name.mkSimple tbl ++ Name.mkSimple ex) else id
        | _ => id
      finishTermMode m ⟨resolved.raw⟩ }
  liftMacroM (lowerQedExpr hooks .val stx)

@[noinline] private def parseTableAssigns (dbName : Name) (t : ParsedTable) (allEx : Std.HashMap String (Array Name))
    (clauseKind : String) (exName : Ident) (assigns : Array Syntax) (checkDup : Bool := true) :
    CommandElabM (Array Ident × Array Term × Std.HashSet String) := do
  let colNames := t.cols.map (·.colName); let mut seen : Std.HashSet String := {}; let mut fIds : Array Ident := #[]; let mut fVals : Array Term := #[]
  for item in assigns do
    let fid : Ident := ⟨item.getArg 0⟩; let fn := fid.getId.eraseMacroScopes.toString
    unless colNames.contains fn do throwErrorAt fid s!"table `{t.tableName}` {clauseKind} `{exName.getId}`: unknown column `{fn}` (expected: {String.intercalate ", " colNames.toList})"
    if checkDup && seen.contains fn then throwErrorAt fid s!"table `{t.tableName}` {clauseKind} `{exName.getId}`: duplicate column `{fn}`"
    seen := seen.insert fn; fIds := fIds.push (mkIdentFrom fid (Name.mkSimple fn)); fVals := fVals.push (← lowerDbExExpr dbName t allEx (item.getArg 2))
  return (fIds, fVals, seen)

@[noinline] private def buildTableRowTerm (qctx : PureQuotCtx) (dbName : Name) (t : ParsedTable) (allEx : Std.HashMap String (Array Name))
    (rowTyId : Ident) (hasInhab : Bool) (clauseKind : String) (exName : Ident) (baseOpt : Syntax) (assigns : Array Syntax) : CommandElabM Term := do
  let (fIds, fVals, seen) ← parseTableAssigns dbName t allEx clauseKind exName assigns
  if baseOpt.getNumArgs == 2 then
    let baseId : Ident := ⟨baseOpt.getArg 1⟩; let bn := baseId.getId.eraseMacroScopes
    let baseTerm : Term := if (allEx.getD t.tableName #[]).contains bn then mkIdentFrom baseId (dbName ++ t.ident.getId ++ bn) else ⟨baseId.raw⟩
    return runQuot qctx `({ ($baseTerm : $rowTyId) with $[$fIds:ident := $fVals:term],* })
  else if hasInhab && seen.size < t.cols.size then return runQuot qctx `({ (default : $rowTyId) with $[$fIds:ident := $fVals:term],* })
  else
    for col in t.cols do unless seen.contains col.colName do throwErrorAt exName s!"table `{t.tableName}` {clauseKind} `{exName.getId}`: missing column `{col.colName}`"
    return runQuot qctx `(({ $[$fIds:ident := $fVals:term],* } : $rowTyId))

@[noinline] private def elabTableCheckThm (qctx : PureQuotCtx) (ref : Syntax) (thmId : Ident) (goal : Term) (simpIds : Array Ident) (errMsg : String) : CommandElabM Unit :=
  withRef ref <| elabCommand <| runQuot qctx `(command| theorem $thmId : $goal := by
    (try simp only [$[$simpIds:ident],*, Qed.Lang.QedVal.val_id]); all_goals (first | trivial | qedCloseGround | rfl | decide | omega | fail $(Syntax.mkStrLit errMsg)))

@[noinline] private def elabOneRowEx (qctx : PureQuotCtx) (dbName : Name) (t : ParsedTable) (allEx : Std.HashMap String (Array Name))
    (hasInhab isRejects : Bool) (stx : Syntax) : CommandElabM Unit := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTyId := mkIdentFrom t.ident rowTypeName; let rowInvId := mkIdentFrom t.ident (rowTypeName ++ `RowInv)
  let id : Ident := ⟨stx.getArg 1⟩; let nm := id.getId.eraseMacroScopes
  let rowTerm ← buildTableRowTerm qctx dbName t allEx rowTyId hasInhab (if isRejects then "rejects" else "example") id (stx.getArg 2) (stx.getArg 4).getSepArgs
  if isRejects then
    elabTableCheckThm qctx id (mkIdentFrom id (rowTypeName ++ Name.mkSimple s!"rejects_{nm}")) (runQuot qctx `(¬ $rowInvId ($rowTerm))) #[rowInvId]
      s!"Database `rejects {nm}` on table `{t.tableName}` could not be proved invalid (row may satisfy all invariants)"
  else
    let defId := mkIdentFrom id (rowTypeName ++ nm); elabCommand (runQuot qctx `(command| def $defId : $rowTyId := $rowTerm))
    elabTableCheckThm qctx id (mkIdentFrom id (rowTypeName ++ Name.mkSimple s!"{nm}_valid")) (runQuot qctx `($rowInvId $defId)) #[rowInvId, defId]
      s!"Database `example {nm}` on table `{t.tableName}` does not satisfy row invariants"

@[noinline] private def elabOneTransEx (qctx : PureQuotCtx) (dbName : Name) (t : ParsedTable) (allEx : Std.HashMap String (Array Name)) (trStx : Syntax) : CommandElabM Unit := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTyId := mkIdentFrom t.ident rowTypeName; let transInvId := mkIdentFrom t.ident (rowTypeName ++ `TransInv)
  let isAllows := (trStx.getArg 0).getId.eraseMacroScopes == `transition_example; let trId : Ident := ⟨trStx.getArg 1⟩; let nm := trId.getId.eraseMacroScopes
  let oldTerm ← lowerDbExExpr dbName t allEx (trStx.getArg 3); let rhsNode := trStx.getArg 5
  let newTerm ← if rhsNode.getNumArgs > 0 && (rhsNode.getArg 0).getKind == `Qed.Server.Db.assignItem then
      let (fIds, fVals, _) ← parseTableAssigns dbName t allEx "transition" trId rhsNode.getSepArgs false
      pure (runQuot qctx `({ ($oldTerm : $rowTyId) with $[$fIds:ident := $fVals:term],* }))
    else lowerDbExExpr dbName t allEx rhsNode
  let goal := runQuot qctx (if isAllows then `($transInvId ($oldTerm) ($newTerm)) else `(¬ $transInvId ($oldTerm) ($newTerm)))
  elabTableCheckThm qctx trId (mkIdentFrom trId (rowTypeName ++ Name.mkSimple s!"{if isAllows then "trans_" else "trans_rejects_"}{nm}")) goal #[transInvId]
    s!"Database `{if isAllows then "transition_example" else "transition_rejects"} {nm}` on table `{t.tableName}` failed transition invariant check"

@[noinline] private def elabOnePolEx (qctx : PureQuotCtx) (dbName : Name) (tables : Array ParsedTable) (t : ParsedTable) (tInfo : DbTableInfo)
    (allEx : Std.HashMap String (Array Name)) (snapTyId? : Option Ident) (pStx : Syntax) : CommandElabM Unit := do
  let rowTypeName := dbName ++ t.ident.getId; let isAllows := (pStx.getArg 0).getId.eraseMacroScopes == `policy_allows
  let opName := ((pStx.getArg 1).getArg 0).getId.eraseMacroScopes; let pId : Ident := ⟨pStx.getArg 2⟩
  let mut kvs : Std.HashMap Name Term := {}; let mut user? : Option Syntax := none; let mut snaps : Std.HashMap String Term := {}
  for item in (pStx.getArg 4).getArgs do
    match item.getKind with
    | `Qed.Server.Db.polExKv =>
        let k := (item.getArg 0).getId.eraseMacroScopes; let rhs := item.getArg 2
        if k == `user then user? := some rhs else kvs := kvs.insert k (← lowerDbExExpr dbName t allEx rhs)
    | `Qed.Server.Db.polExSnap =>
        let stblId : Ident := ⟨item.getArg 1⟩; let stbl := stblId.getId.eraseMacroScopes.toString
        unless tables.any (·.tableName == stbl) do throwErrorAt stblId s!"policy example `{pId.getId}`: unknown table `{stbl}` in `snap`"
        snaps := snaps.insert stbl (← lowerDbExExpr dbName t allEx (item.getArg 3))
    | _ => pure ()
  let some rowTerm := kvs[`row]? | throwErrorAt pStx s!"`table {t.tableName}` policy example `{pId.getId}` requires `row = ...`"
  let userVal? ← match user? with
    | none => pure none
    | some uStx => let uu := unwrapParens1 uStx; if uu.getKind == ``qedIdent && (uu.getArg 0).getId.eraseMacroScopes == `none then pure none else some <$> lowerDbExExpr dbName t allEx uStx
  let mkP (s : Name) (c : Bool) := (mkIdentFrom pId (rowTypeName ++ s), c)
  let polSpecs : Array (Ident × Bool) := match opName with
    | `read => #[mkP `ReadPolicy tInfo.hasCrossReadPolicy] | `insert => #[mkP `InsertPolicy tInfo.hasCrossInsertPolicy]
    | `update => #[mkP `UpdatePolicy tInfo.hasCrossUpdatePolicy] | `delete => #[mkP `DeletePolicy tInfo.hasCrossDeletePolicy]
    | `write => #[mkP `InsertPolicy tInfo.hasCrossInsertPolicy, mkP `UpdatePolicy tInfo.hasCrossUpdatePolicy, mkP `DeletePolicy tInfo.hasCrossDeletePolicy] | _ => #[]
  if polSpecs.any (·.2) && snapTyId?.isNone then throwErrorAt pStx "internal error: missing Snap for cross-table policy example"
  let fullGoal := runQuot qctx do
    let ctxTerm ← match kvs[`ctx]? with
      | some ct => pure ct
      | none =>
          let uT ← match userVal? with | none => `(Option.none) | some u => `(Option.some $u)
          let cT ← match kvs[`role]? with | none => `([]) | some r => `([("role", $r)])
          let aT ← match kvs[`session]? with | some s => `(if $s then Qed.Server.AuthMethod.session else Qed.Server.AuthMethod.bearer) | none => if userVal?.isSome then `(Qed.Server.AuthMethod.bearer) else `(Qed.Server.AuthMethod.none)
          `({ userId := $uT, claims := $cT, authMethod := $aT : Qed.Server.RequestCtx })
    let snapTerm? ← snapTyId?.mapM fun sTyId => do
      let sFIds := tables.map (·.ident); let sFVals ← tables.mapM fun tbl => match snaps[tbl.tableName]? with | some v => pure v | none => `([])
      `({ $[$sFIds:ident := $sFVals:term],* : $sTyId })
    Qed.mkConjBody (← polSpecs.mapM fun (polId, isC) => do
      let app ← if isC then `($polId $(snapTerm?.get!) $ctxTerm ($rowTerm)) else `($polId $ctxTerm ($rowTerm))
      if isAllows then pure app else `(¬ $app)) (ascribeProp := false)
  let verb := if isAllows then "allows" else "denies"
  elabTableCheckThm qctx pId (mkIdentFrom pId (rowTypeName ++ Name.mkSimple s!"policy_{opName}_{verb}_{pId.getId.eraseMacroScopes}")) fullGoal (polSpecs.map (·.1))
    s!"Database `policy_{verb} {opName} {pId.getId.eraseMacroScopes}` on table `{t.tableName}` failed policy check"

@[noinline] private def elabAllTableExamples (qctx : PureQuotCtx) (dbName : Name) (tables : Array ParsedTable)
    (tableInfos : Array DbTableInfo) (snapTyId? : Option Ident) : CommandElabM Unit := do
  let mut allEx : Std.HashMap String (Array Name) := {}
  for t in tables do
    let mut names : Array Name := #[]
    for exStx in t.examples do
      let exId : Ident := ⟨exStx.getArg 1⟩; let n := exId.getId.eraseMacroScopes
      if names.contains n then throwErrorAt exId s!"duplicate `example {n}` in `table {t.tableName}`"
      names := names.push n
    allEx := allEx.insert t.tableName names
  let hasInhabs ← tables.mapM fun t => liftTermElabM do
    return (← Meta.trySynthInstance (← Meta.mkAppM ``Inhabited #[← Term.elabType (mkIdentFrom t.ident (dbName ++ t.ident.getId)).raw])) matches .some _
  for (t, hasInhab) in tables.zip hasInhabs do for exStx in t.examples do elabOneRowEx qctx dbName t allEx hasInhab false exStx
  for ((t, tInfo), hasInhab) in (tables.zip tableInfos).zip hasInhabs do
    for rejStx in t.rejects do elabOneRowEx qctx dbName t allEx hasInhab true rejStx
    for trStx in t.transExamples do elabOneTransEx qctx dbName t allEx trStx
    for pStx in t.polExamples do elabOnePolEx qctx dbName tables t tInfo allEx snapTyId? pStx

@[noinline] private def validateDbTables (dbName : Name) (tables : Array ParsedTable) : CommandElabM Unit := do
  for t in tables do
    let colNames := t.cols.map (·.colName)
    for col in t.cols do if let some (rtId, rcId) := col.refs? then
      let (rt, rc) := (rtId.getId.eraseMacroScopes.toString, rcId.getId.eraseMacroScopes.toString)
      let some targetTbl := tables.find? (·.tableName == rt) | throwErrorAt rtId s!"table `{t.tableName}` column `{col.colName}` references unknown table `{rt}` in `database {dbName}`"
      unless targetTbl.cols.any (·.colName == rc) do throwErrorAt rcId s!"table `{t.tableName}` column `{col.colName}` references unknown column `{rt}.{rc}`"
    for idxCols in t.indexes do for ic in idxCols do
      let cn := ic.getId.eraseMacroScopes.toString
      unless colNames.contains cn do throwErrorAt ic s!"index on `table {t.tableName}` references unknown column `{cn}`"
      if t.cols.any fun c => c.colName == cn && c.encKey?.isSome then throwErrorAt ic s!"cannot index encrypted column `{t.tableName}.{cn}` (AES-256-GCM uses randomized nonces)"

@[noinline] private def mkClientTableFieldPure (dbName : Name) (cfgParamId : Ident) (t : ParsedTable) : PureQuotM (Ident × Term × Term) := do
  let rowTyId := mkIdentFrom t.ident (dbName ++ t.ident.getId); let colIdTs ← t.cols.mapM fun c => mkSqlIdentTermPure c.colName
  let encCols := t.cols.map fun c => (c.colName, c.encKey?)
  let ewTs ← mkColsEncPairs t.tableName encCols fun cn _ => Syntax.mkStrLit cn
  let erTs ← mkColsEncPairs t.tableName encCols fun _ idx => Syntax.mkNumLit (toString idx)
  let tblNameT ← mkSqlIdentTermPure t.tableName
  let hVal ← `({ config := $cfgParamId, tableName := $tblNameT, columns := [$[$colIdTs:term],*],
                 decodeRow := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `decodeRow)),
                 encodeRow := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `encodeRow)),
                 rowInvBool := $(mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `rowInvBool)),
                 encWrite := [$[$ewTs:term],*], encRead := [$[$erTs:term],*] : Qed.Server.Db.TableHandle $rowTyId })
  return (mkIdentFrom t.ident (Name.mkSimple t.tableName), ← `(Qed.Server.Db.TableHandle $rowTyId), hVal)

@[noinline] private def mkDbTailCmdsPure (dbIdent : Ident) (dbName fullDbName : Name) (dbShort : String)
    (tables : Array ParsedTable) (resolved : Qed.Cloud.EnvMap (Term × Qed.Cloud.DbEnvSpec))
    (devEp? : Option Term) (hasExplicitEnv isManaged : Bool) (secrets : Array String)
    (tableSchemaTerms backfillTerms : Array Term) : PureQuotM (Array (TSyntax `command)) := do
  let mkDb (s : Name) := mkIdentFrom dbIdent (dbName ++ s)
  let (secretsId, configId, ddlId, rlsDdlId, ensureId, instId, mId) := (mkDb `secrets, mkDb `config, mkDb `ddl, mkDb `rlsDdl, mkDb `ensureSchema, mkDb `instSafeIOEnsureSchema, mkIdent `m)
  let devEpTerm ← match devEp? with | some dt => `(some $dt) | none => `(none)
  let envEndpointsTerm ← if hasExplicitEnv then `(some ({ dev := $(resolved.dev.1), preview := $(resolved.preview.1), staging := $(resolved.staging.1), prod := $(resolved.prod.1) } : Qed.Cloud.EnvMap Qed.Server.Db.DbEndpoint)) else `(none)
  let (clientStructId, clientWithId, clientId, cfgParamId) := (mkDb `Client, mkDb `clientWith, mkDb `client, mkIdent `_cfg)
  let tblFlds ← tables.mapM (mkClientTableFieldPure dbName cfgParamId)
  let cfIds := #[mkIdent `config] ++ tblFlds.map (·.1); let ciIds := cfIds
  let cfTys := #[← `(Qed.Server.Db.DbConfig)] ++ tblFlds.map (·.2.1); let ciVals := #[⟨cfgParamId.raw⟩] ++ tblFlds.map (·.2.2)
  let secLits := secrets.map Syntax.mkStrLit
  return #[
    ← `(command| abbrev $(mkDb `Tx) : Type := Qed.Server.Db.DbTx $(Syntax.mkStrLit fullDbName.toString)),
    ← `(command| def $secretsId : Array String := #[$[$secLits:term],*]),
    ← `(command| def $configId : Qed.Server.Db.DbConfig := { name := $(Syntax.mkStrLit dbShort), endpoint := $(resolved.prod.1), devFallback? := $devEpTerm, envEndpoints? := $envEndpointsTerm, isManaged := $(quote isManaged), tables := [$[$tableSchemaTerms:term],*], backfills := [$[$backfillTerms:term],*] }),
    ← `(command| def $ddlId (dialect : Qed.Server.Db.SqlDialect := .postgres) : String := Qed.Server.Db.renderDatabaseDdl dialect ($configId).tables),
    ← `(command| def $rlsDdlId : String := Qed.Server.Db.renderDatabaseRlsDdl ($configId).tables),
    ← `(command| def $ensureId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl $configId),
    ← `(command| instance $instId:ident {_σ : Type} : Qed.Server.SafeIO (@$ensureId (Qed.Server.ThreadProg _σ) _ _) where noAtomic := Qed.Server.NoAtomic.io (.dbExecDdl $configId) _ .pure),
    ← `(command| structure $clientStructId where $[$cfIds:ident : $cfTys:term]*),
    ← `(command| def $clientWithId ($cfgParamId:ident : Qed.Server.Db.DbConfig) : $clientStructId := { $[$ciIds:ident := $ciVals:term],* }),
    ← `(command| def $clientId : $clientStructId := $clientWithId $configId),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `ensureSchema)) {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl _c.config),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `transaction)) {$mId:ident : Type → Type} {α : Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) (body : UInt64 → $mId (Except Qed.Server.ApiError α)) : $mId (Except Qed.Server.ApiError α) := Qed.Server.Db.withTransaction _c.config body)]

private structure ParsedDbState where
  primaryEp? : Option (Term × Qed.Cloud.DbEnvSpec) := none
  envSlots : Qed.Cloud.EnvMap (Option (Term × Qed.Cloud.DbEnvSpec)) := Qed.Cloud.EnvMap.ofDefault none
  isManaged : Bool := false
  hasExplicitEnv : Bool := false
  secrets : Array String := #[]
  tables : Array ParsedTable := #[]
  backfillClauses : Array Syntax := #[]

@[noinline] private def setDbEnvSlot (qctx : PureQuotCtx) (dbName : Name) (ref : Syntax) (envStr : String) (epStx : Syntax) (inManaged : Bool) (s : ParsedDbState) : CommandElabM ParsedDbState := do
  let some env := Qed.Cloud.DeployEnv.parse? envStr | throwErrorAt ref s!"unexpected environment `{envStr}` in `database {dbName}`"
  if inManaged && env == .prod then throwErrorAt ref s!"cannot override `prod` inside `managed postgres:` in `database {dbName}`"
  if (s.envSlots.get env).isSome then throwErrorAt ref s!"duplicate `{envStr}` endpoint in `database {dbName}`"
  let (epT, secs, spec) ← parseEndpointSpec qctx epStx (some env)
  return { s with envSlots := s.envSlots.set env (some (epT, spec)), secrets := if env == .dev then s.secrets else secs.foldl pushUnique s.secrets }

@[noinline] private def applyOneDbClause (qctx : PureQuotCtx) (dbIdent : Ident) (dbName : Name) (dbShort : String)
    (st : ParsedDbState) (c : Syntax) : CommandElabM ParsedDbState := do
  match c.getKind with
  | ``dbManagedClause =>
      if st.isManaged || st.primaryEp?.isSome || Qed.Cloud.DeployEnv.all.any (st.envSlots.get · |>.isSome) then
        throwErrorAt c s!"cannot combine `managed postgres` with other endpoint clauses in `database {dbName}` (nest overrides under `managed postgres:`)"
      let mut s := { st with isManaged := true, hasExplicitEnv := true }; let mut previewEphemeral := false
      if (c.getArg 2).getNumArgs == 2 then
        for sc in ((c.getArg 2).getArg 1).getArgs do
          match sc.getKind with
          | `Qed.Server.Db.managedPreviewEphemeral =>
              if previewEphemeral || s.envSlots.preview.isSome then throwErrorAt sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
              previewEphemeral := true
          | `Qed.Server.Db.managedEnvOverride =>
              let envStr := (sc.getArg 0).getId.eraseMacroScopes.toString
              if envStr == "preview" && previewEphemeral then throwErrorAt sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
              s ← setDbEnvSlot qctx dbName sc envStr (sc.getArg 1) true s
          | _ => throwErrorAt sc s!"unexpected clause in `managed postgres:`"
      let targets := Qed.Cloud.managedPostgresTargets dbShort previewEphemeral (s.envSlots.dev.map Prod.snd)
      for e in Qed.Cloud.DeployEnv.all do if (s.envSlots.get e).isNone then
        let sp := targets.get e
        let epT ← match sp with
          | .managedPostgres nm env => pure <| runQuot qctx `(Qed.Server.Db.DbEndpoint.managedPostgres $(quote nm) $(mkIdent (`Qed.Cloud.DeployEnv ++ Name.mkSimple env.toString)))
          | .ephemeralSqlite p | .byoSqlite p => pure <| runQuot qctx `(Qed.Server.Db.DbEndpoint.sqlitePath $(quote p))
          | _ => throwErrorAt dbIdent s!"internal error lowering managed database target in `database {dbName}`"
        s := { s with envSlots := s.envSlots.set e (some (epT, sp)) }
      return { s with secrets := targets.prod.secrets.foldl (fun acc sr => pushUnique acc sr.envVar) s.secrets }
  | ``dbPrimaryEpClause =>
      if st.isManaged || st.primaryEp?.isSome || st.envSlots.prod.isSome then throwErrorAt c s!"duplicate endpoint specification in `database {dbName}`"
      let (epT, secs, spec) ← parseEndpointSpec qctx (c.getArg 0) none
      return { st with primaryEp? := some (epT, spec), secrets := secs.foldl pushUnique st.secrets }
  | ``dbEnvEpClause =>
      let envStr := (c.getArg 0).getId.eraseMacroScopes.toString
      if st.isManaged then throwErrorAt c s!"cannot combine `managed postgres` with top-level `{envStr}` endpoint in `database {dbName}` (nest overrides under `managed postgres:`)"
      if envStr == "prod" && st.primaryEp?.isSome then throwErrorAt c s!"cannot combine a default endpoint with `prod` in `database {dbName}`"
      setDbEnvSlot qctx dbName c envStr (c.getArg 1) false { st with hasExplicitEnv := st.hasExplicitEnv || envStr != "dev" }
  | ``dbTableClauseTop =>
      let tbl ← parseTableClause qctx dbName st.tables c
      return { st with tables := st.tables.push tbl, secrets := tbl.encSecrets.foldl pushUnique st.secrets }
  | ``dbBackfillClause => return { st with backfillClauses := st.backfillClauses.push c }
  | _ => throwErrorAt c s!"unexpected clause in `database {dbName}`"

@[noinline, command_elab databaseCmd] def elabDatabaseCmd : CommandElab := fun stx => do
  let qctx ← getPureQuotCtx
  let dbIdent : Ident := ⟨stx.getArg 2⟩; let dbName := dbIdent.getId; let dbShort := dbName.toString; let fullDbName := (← getCurrNamespace) ++ dbName
  let st ← (stx.getArg 4).getArgs.foldlM (init := {}) (applyOneDbClause qctx dbIdent dbName dbShort)
  let some _ := st.envSlots.prod.orElse (fun _ => st.primaryEp?)
    | throwErrorAt dbIdent s!"`database {dbName}` must specify an endpoint (e.g. `managed postgres`, `postgres ...`, `sqlite ...`, `url secret(\"DATABASE_URL\")`, `d1 ...`, `turso ...`, or `http ...`)"
  let resolved ← st.envSlots.mapM fun e slot? => match slot?.orElse (fun _ => st.primaryEp?) with
    | some p => pure p | none => throwErrorAt dbIdent s!"`database {dbName}` is missing a `{e}` endpoint (specify `{e} ...`, a default endpoint, or use `managed postgres`)"
  if st.tables.isEmpty then throwErrorAt dbIdent s!"`database {dbName}` must declare at least one `table`"
  validateDbTables dbName st.tables
  elabCommand (runQuot qctx `(command| def $(mkIdentFrom dbIdent (dbName ++ `_qed_database_marker)) : Unit := ()))
  for t in st.tables do elabRowStructAndCodecs qctx (mkIdentFrom t.ident (dbName ++ t.ident.getId)) t.cols
  let (snapTyId?, snapConst?) ← if st.tables.size >= 2 || st.tables.any fun t => (t.readPols ++ t.insertPols ++ t.updatePols ++ t.deletePols).any exprHasAnyIn then do
      let snapId := mkIdentFrom dbIdent (dbName ++ `Snap); let sFIds := st.tables.map (·.ident)
      elabCommand <| runQuot qctx do
        let sFTys ← st.tables.mapM fun t => `(List $(mkIdentFrom t.ident (dbName ++ t.ident.getId)))
        `(command| structure $snapId where $[$sFIds:ident : $sFTys:term]*)
      pure (some snapId, some (fullDbName ++ `Snap))
    else pure (none, none)
  let (tableInfos, tableSchemaTerms) := (← st.tables.mapM (elabTableBody qctx dbName fullDbName st.tables snapTyId?)).unzip
  elabAllTableExamples qctx dbName st.tables tableInfos snapTyId?
  let backfillTerms ← st.backfillClauses.mapM (elabBackfillClause qctx dbName tableInfos)
  for cmd in runQuot qctx (mkDbTailCmdsPure dbIdent dbName fullDbName dbShort st.tables resolved (st.envSlots.dev.map Prod.fst) st.hasExplicitEnv st.isManaged st.secrets tableSchemaTerms backfillTerms) do elabCommand cmd
  modifyEnv fun env => databaseRegistry.addEntry env {
    dbName := fullDbName, shortName := dbShort, configConst := fullDbName ++ `config, ensureSchemaConst := fullDbName ++ `ensureSchema,
    snapTypeConst? := snapConst?, secrets := st.secrets, hasDevFallback := st.envSlots.dev.isSome, isManaged := st.isManaged,
    envSpecs := { dev := resolved.dev.2, preview := resolved.preview.2, staging := resolved.staging.2, prod := resolved.prod.2 }, tables := tableInfos }

end DbElabImpl
end Qed.Server.Db
