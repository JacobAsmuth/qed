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
  let unfoldNames ← liftMetaM <| Qed.Verify.Core.mapMeta (stx.getArg 2).getSepArgs fun id => resolveGlobalConstNoOverload id
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
private def dbNode (k : Name) (p : Parser) : Parser := node k (withPosition p)

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

private def dbPolicyOp : Parser := node `Qed.Server.Db.policyOp (identEq `read <|> identEq `write <|> identEq `insert <|> identEq `update <|> identEq `delete)
private def dbTransEdge : Parser := node `Qed.Server.Db.transEdge (sepBy1 (categoryParser `qedExpr 55) "->")
private def dbEncColTy : Parser := node `Qed.Server.Db.encColTy
  (atomic (identEq `encrypted >> checkNoWsBefore "" >> "(") >> categoryParser `qedType 91 >> "," >> identEq `key >> "=" >> qedEnvRef >>
    optional ("," >> identEq `prevKeys >> "=" >> "[" >> sepBy qedEnvRef "," >> "]") >> ")" >> optional "?")
private def dbAssignItem : Parser := node `Qed.Server.Db.assignItem (ident >> "=" >> dbExpr)
private def dbPolicyExItem : Parser :=
  node `Qed.Server.Db.polExKv (withPosition (atomic ((identEq `user <|> identEq `role <|> identEq `session <|> identEq `ctx <|> identEq `row) >> "=") >> dbExpr)) <|>
  node `Qed.Server.Db.polExSnap (withPosition (atomic (identEq `snap >> ident >> "=") >> dbExpr))

@[dbTableClause_parser] def dbTableClauseP : Parser := opaqueP (
  dbNode `Qed.Server.Db.tblPolicy (atomic (identEq `policy) >> sepBy1 dbPolicyOp "," >> kw "requires" >> sepBy1 dbExpr ",") <|>
  dbNode `Qed.Server.Db.tblTransInv (atomic (identEq `invariant >> ident >> ":" >> identEq `transition) >> categoryParser `qedExpr 90 >> ":" >> sepBy1 dbTransEdge ",") <|>
  dbNode `Qed.Server.Db.tblInv (atomic (identEq `invariant >> ident >> ":") >> notFollowedBy (identEq `transition) "transition" >> sepBy1 dbExpr ",") <|>
  dbNode `Qed.Server.Db.tblIndex (atomic (identEq `index) >> "(" >> sepBy1 ident "," >> ")") <|>
  dbNode `Qed.Server.Db.tblTransEx (atomic ((symbol "example" <|> identEq `rejects) >> identEq `transition >> ident >> ":") >>
    categoryParser `qedExpr 55 >> "->" >> (sepBy1 (atomic dbAssignItem) "," <|> dbExpr)) <|>
  dbNode `Qed.Server.Db.tblPolEx (atomic ((symbol "example" <|> identEq `rejects) >> identEq `policy >> dbPolicyOp >> ident >> ":") >>
    checkColGt "expected indented policy example clauses" >> many1Indent dbPolicyExItem) <|>
  dbNode `Qed.Server.Db.tblRowEx (atomic ((symbol "example" <|> identEq `rejects) >> ident) >> optional (symbol "from" >> ident) >> ":" >> sepBy1 dbAssignItem ",") <|>
  dbNode `Qed.Server.Db.tblCol (notFollowedBy (identEq `policy <|> identEq `index <|> identEq `invariant <|> symbol "example" <|> identEq `rejects) "column" >>
    ident >> ":" >> (dbEncColTy <|> categoryParser `qedType 91) >> many (checkLineEq >> dbColMod) >> optional (checkLineEq >> symbol "where" >> sepBy1 dbExpr ",")))

private def dbManagedSubClause : Parser :=
  dbNode `Qed.Server.Db.managedPreviewEphemeral (atomic (identEq `preview >> identEq `ephemeral)) <|>
  dbNode `Qed.Server.Db.managedEnvOverride (atomic (dbEnvName >> notFollowedBy (identEq `ephemeral) "ephemeral") >> dbEndpointSpec)

@[dbClause_parser] def dbClauseP : Parser := opaqueP (
  dbNode `Qed.Server.Db.dbManaged (atomic (identEq `managed >> identEq `postgres) >> optional (dbIndented "expected indented `managed postgres:` clauses" dbManagedSubClause)) <|>
  dbNode `Qed.Server.Db.dbEnvEp (atomic dbEnvName >> dbEndpointSpec) <|>
  dbNode `Qed.Server.Db.dbPrimaryEp dbEndpointSpec <|>
  dbNode `Qed.Server.Db.dbBackfill (atomic (identEq `backfill) >> ident >> identEq `set >> "{" >> sepBy1 dbAssignItem "," >> "}" >> optional (checkLineEq >> symbol "where" >> dbExpr)) <|>
  dbNode `Qed.Server.Db.dbInv (atomic (identEq `invariant >> ident >> ":") >> sepBy1 dbExpr ",") <|>
  dbNode `Qed.Server.Db.dbTable (atomic (identEq `table) >> ident >> dbIndented "expected indented `table` columns/policies" (categoryParser `dbTableClause 0)))

@[command_parser] def databaseCmd : Parser := opaqueP (
  node `Qed.Server.Db.databaseCmd (optional Command.docComment >> withPosition (atomic (identEq `database >> ident >> ":") >> checkColGt "expected indented `database` clauses" >> many1Indent (categoryParser `dbClause 0))))

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
  rawNamedInvs : Array (Lean.Ident × Array Lean.Syntax) := #[]
  metaInvs : Array (Lean.Ident × Array Lean.Syntax) := #[]
  examples : Array Lean.Syntax := #[]
  otherExs : Array Lean.Syntax := #[]
  transChains : Array (Lean.Syntax × Array (Array Lean.Syntax)) := #[]
  indexes : Array (Array Lean.Ident) := #[]

section DbElabImpl
open Lean Elab Command

@[noinline] private def readEpRef (secs : Array String) (s : Syntax) (recordSec := true) (onlyIfNoDefault := false) :
    CommandElabM (Array String × ParsedEnvRef) := do
  let er ← parseQedEnvRef "database" s
  let secs' := if recordSec && er.isSecret && (!onlyIfNoDefault || er.default?.isNone) then secs.push er.envKey else secs
  return (secs', er)

@[noinline] private def parseEndpointSpec (qctx : PureQuotCtx) (stx : Syntax) (pinEnv? : Option Qed.Cloud.DeployEnv := none) :
    CommandElabM (Term × Array String × Qed.Cloud.DbEnvSpec) := do
  let scope : Qed.Cloud.SecretScope := pinEnv?.elim .envScoped .pinned
  let mkEp (ctor : Name) (args : Array Term) := qctx.runPure (mkAppC ctor args)
  match stx.getKind with
  | `Qed.Server.Db.epUrl | `Qed.Server.Db.epPostgres =>
      let isPg := stx.getKind == `Qed.Server.Db.epPostgres
      let (secs, er) ← readEpRef #[] (stx.getArg 1)
      let ref : Qed.Cloud.SecretRef := { envVar := er.envKey, scope }
      return (mkEp (if isPg then `Qed.Server.Db.DbEndpoint.postgresEnv else `Qed.Server.Db.DbEndpoint.urlEnv) #[quote er.envKey], secs,
        if isPg then .byoPostgres ref else .byoUrl ref)
  | `Qed.Server.Db.epSqlite =>
      let a := stx.getArg 1
      if a.isOfKind strLitKind then
        let p := (⟨a⟩ : TSyntax `str).getString; return (mkEp `Qed.Server.Db.DbEndpoint.sqlitePath #[Syntax.mkStrLit p], #[], .byoSqlite p)
      let (secs, er) ← readEpRef #[] a (onlyIfNoDefault := true)
      return (mkEp `Qed.Server.Db.DbEndpoint.sqliteEnv #[quote er.envKey, quote er.default?], secs, .byoSqliteEnv er.envKey er.default?)
  | `Qed.Server.Db.epD1 =>
      let (s0, acc) ← readEpRef #[] (stx.getArg 3) false
      let (s1, db)  ← readEpRef s0 (stx.getArg 7) false
      let (s2, tok) ← readEpRef s1 (stx.getArg 11)
      return (mkEp `Qed.Server.Db.DbEndpoint.cloudflareD1 #[quote acc.envKey, quote acc.default?, quote db.envKey, quote db.default?, quote tok.envKey],
        s2, .byoD1 acc.envKey db.envKey { envVar := tok.envKey, scope })
  | `Qed.Server.Db.epTurso =>
      let (s0, u) ← readEpRef #[] (stx.getArg 3); let (s1, tok) ← readEpRef s0 (stx.getArg 7)
      return (mkEp `Qed.Server.Db.DbEndpoint.turso #[quote u.envKey, quote tok.envKey], s1, .byoTurso u.envKey { envVar := tok.envKey, scope })
  | `Qed.Server.Db.epHttp =>
      let (s0, u) ← readEpRef #[] (stx.getArg 3); let tokOpt := stx.getArg 4
      let (s1, tokT, tokRef?) ← if tokOpt.getNumArgs == 4 then
          let (s1, t) ← readEpRef s0 (tokOpt.getArg 3)
          pure (s1, qctx.runPure (mkOptTerm (some (quote t.envKey))), some { envVar := t.envKey, scope })
        else pure (s0, mkCIdent `Option.none, none)
      return (mkEp `Qed.Server.Db.DbEndpoint.httpSql #[quote u.envKey, tokT], s1, .byoHttpSql u.envKey tokRef?)
  | _ => mkDbErr stx "unexpected database endpoint specification"

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
    unless (stx.getArg 1).isIdent do mkDbErr (stx.getArg 1) "cross-table `any <alias> in <table>:` expects a plain table alias identifier"
    let aliasId : Ident := ⟨stx.getArg 1⟩; let aliasStr := aliasId.getId.eraseMacroScopes.toString
    unless isSafeSqlIdent aliasStr do mkDbErr aliasId s!"invalid SQL alias `{aliasStr}` in `any {aliasStr} in ...`"
    let tgt := unwrapParens1 (stx.getArg 3)
    unless tgt.getKind == ``qedIdent do mkDbErr tgt "cross-table `any <alias> in <table>:` expects a sibling table name from the same `database`"
    let tblName := (tgt.getArg 0).getId.eraseMacroScopes.toString
    let some subTbl := tables.find? (·.tableName == tblName) | mkDbErr tgt s!"unknown table `{tblName}` in cross-table `any {aliasStr} in {tblName}:`"
    let body := stx.getArg 5
    Lang.foldlCmd subTbl.cols () fun _ col => do
      if col.encKey?.isSome then
        if stxAny (fun s => match extractDottedChain? s with | some [a, c] => a == aliasStr && c == col.colName | _ => false) body then
          mkDbErr body s!"cannot reference encrypted column `{tblName}.{col.colName}` inside cross-table `any {aliasStr} in {tblName}:` predicate"
    validateCrossTableAnyIn tables body
  else Lang.foldlCmd stx.getArgs () fun _ ch => validateCrossTableAnyIn tables ch

@[noinline] private partial def lowerDbExpr (qctx : PureQuotCtx) (colNames : Array String) (rowVar : Ident)
    (oldVar? ctxVar? : Option Ident) (asProp : Bool) (stx : Syntax)
    (tables : Array ParsedTable := #[]) (snapVar? : Option Ident := none) : CommandElabM Term := do
  let hooks : LowerHooks (ReaderT (Array String) CommandElabM) := { LowerHooks.mkDefault (fun ref msg => liftM (mkDbErr ref msg)) with
    lowerIdent := fun ref id mode => do
      let locals ← read; let comps := id.getId.eraseMacroScopes.components
      let t : Term ← match comps with
        | [] => mkDbErr ref "empty identifier in database predicate"
        | root :: rest =>
            let rs := root.toString
            if rest.isEmpty && (rs == "true" || rs == "false" || rs == "none") then
              pure (mkCIdent (if rs == "none" then `Option.none else if mode == .propInv then (if rs == "true" then ``True else ``False) else (if rs == "true" then ``Bool.true else ``Bool.false)))
            else if locals.contains rs then pure (qctx.runPure (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest))
            else if rs == "row" then pure (qctx.runPure (foldProjTerms ref ⟨rowVar.raw⟩ rest))
            else if rs == "ctx" then
              let some cv := ctxVar? | mkDbErr ref "`ctx` is only in scope inside `policy ... requires ...`"
              pure (qctx.runPure (foldProjTerms ref ⟨cv.raw⟩ rest))
            else if colNames.contains rs then pure (qctx.runPure do foldProjTerms ref (← `($rowVar.$(mkIdentFrom ref root))) rest)
            else if rest.isEmpty && snapVar?.isSome && tables.any (·.tableName == rs) then pure (qctx.runPure `($(snapVar?.get!).$(mkIdentFrom ref root)))
            else pure ⟨id.raw⟩
      return if mode == .propInv && comps != [`true] && comps != [`false] then qctx.runPure `(qedAsProp($t)) else t
    lowerProj := fun _ base field mode => pure (qctx.runPure do let t ← mkProjTermPure base field; if mode == .propInv then `(qedAsProp($t)) else pure t)
    lowerIndex := fun ref _ _ _ => mkDbErr ref "indexing is not supported in database predicates"
    lowerCall := fun ref callee rawArgs mode go => do
      if callee.getKind == ``qedIdent then
        let nm := (callee.getArg 0).getId.eraseMacroScopes
        if nm == `old || nm == `some then
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then mkDbErr ref s!"`{nm}(...)` expects a single argument"
          let arg := rawArgs[0]!.getArg 0
          if nm == `old then
            let some ov := oldVar? | mkDbErr ref "`old(...)` is only allowed inside two-state table `invariant` clauses"
            return some (← liftM <| lowerDbExpr qctx colNames ov none ctxVar? (mode == .propInv) arg tables snapVar?)
          else return some (qctx.runPure (mkAppC `Option.some #[← go .val arg]))
      return none
    withLocals := fun names k => withReader (· ++ names) k }
  (lowerQedExpr hooks (if asProp then .propInv else .val) stx).run #[]

private def quoteSqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

private def renderSqlLit? (s : Syntax) : Option String :=
  let u := unwrapParens1 s; let uk := u.getKind
  if uk == ``qedLitNum then some (toString (⟨u.getArg 0⟩ : TSyntax `num).getNat)
  else if uk == ``qedLitStr || uk == ``qedDotIdent then
    let raw := if uk == ``qedLitStr then (⟨u.getArg 0⟩ : TSyntax `str).getString else (u.getArg 1).getId.eraseMacroScopes.toString
    if raw.any (· == '\x00') then none else some (quoteSqlLit raw)
  else none

private def mapOptArr {α β : Type} (xs : Array α) (f : α → Option β) : Option (Array β) :=
  let rec go : Nat → Array β → Option (Array β)
    | 0, acc => some acc
    | r + 1, acc => let i := xs.size - (r + 1); if h : i < xs.size then match f xs[i] with | some v => go r (acc.push v) | none => none else some acc
  go xs.size (Array.mkEmpty xs.size)

private partial def renderSqlPred? (tblName : String) (colNames : Array String) (forRls : Bool)
    (tables : Array ParsedTable := #[]) (subAliases : Array (String × Array String) := #[]) (stx : Syntax) : Option String :=
  let recR := renderSqlPred? tblName colNames forRls tables subAliases; let k := stx.getKind
  if k == ``qedLitNum || k == ``qedLitStr || k == ``qedDotIdent then renderSqlLit? stx
  else if forRls && k == ``qedAnyIn then do
    guard (stx.getArg 1).isIdent
    let aliasStr := (stx.getArg 1).getId.eraseMacroScopes.toString; guard (isSafeSqlIdent aliasStr)
    let tgt := unwrapParens1 (stx.getArg 3); guard (tgt.getKind == ``qedIdent)
    let subTblName := (tgt.getArg 0).getId.eraseMacroScopes.toString
    let subTbl ← tables.find? (·.tableName == subTblName)
    let subCols := subTbl.cols.foldl (init := #[]) fun acc c => if c.encKey?.isNone then acc.push c.colName else acc
    let bodySql ← renderSqlPred? tblName colNames true tables (subAliases.push (aliasStr, subCols)) (stx.getArg 5)
    some s!"EXISTS (SELECT 1 FROM \"{subTblName}\" AS \"{aliasStr}\" WHERE {bodySql})"
  else if forRls && k == ``qedCall then (extractSomeCall? stx).bind recR
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs; if args.size == 1 then (recR args[0]!).map ("(" ++ · ++ ")") else none
  else if k == ``qedIdent || k == ``qedProj then
    let qualCol (c : String) := if forRls then "\"" ++ tblName ++ "\".\"" ++ c ++ "\"" else "\"" ++ c ++ "\""
    let revAl := subAliases.reverse
    match matchRowColRef? (fun rv => rv == "row" || revAl.any (·.1 == rv)) (colNames.contains ·) stx with
    | some (some al, col, false) =>
        if let some (_, alCols) := revAl.find? (·.1 == al) then if alCols.contains col then some ("\"" ++ al ++ "\".\"" ++ col ++ "\"") else none
        else if al == "row" && colNames.contains col then some (qualCol col) else none
    | some (none, col, false) => some (qualCol col)
    | some (scope?, col, true) =>
        if !forRls && (scope?.isNone || scope? == some "row") && colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | none =>
        match extractDottedChain? stx with
        | some ["ctx", "userId"] => if forRls then some "current_setting('qed.user_id', true)" else none
        | some ["true"] => some (if forRls then "TRUE" else "1")
        | some ["false"] => some (if forRls then "FALSE" else "0")
        | _ => if !forRls && k == ``qedProj && (stx.getArg 2).isIdent && (stx.getArg 2).getId.eraseMacroScopes == `length then (recR (stx.getArg 0)).map ("LENGTH(" ++ · ++ ")") else none
  else if k == ``qedAnd || k == ``qedOr then do return "(" ++ (← recR (stx.getArg 0)) ++ (if k == ``qedAnd then " AND " else " OR ") ++ (← recR (stx.getArg 2)) ++ ")"
  else if k == ``qedNot then (recR (stx.getArg 1)).map ("(NOT " ++ · ++ ")")
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs; if links.isEmpty || (forRls && links.size != 1) then none
    let rec goLinks : Nat → Syntax → Array String → Option (Array String)
      | 0, _, parts => some parts
      | r + 1, lhs, parts =>
          let i := links.size - (r + 1)
          if h : i < links.size then do
            let lk := links[i]; let opStr := cmpOpKind (lk.getArg 0); let rhs := lk.getArg 1; let l ← recR lhs
            let part ←
              if forRls && opStr == "!=" && isNoneIdent? rhs then some s!"({l} IS NOT NULL AND {l} <> '')"
              else if opStr == "in" || opStr == "not in" then do
                let uArr := unwrapParens1 rhs; guard (uArr.getKind == ``qedArrLit)
                let items ← mapOptArr (uArr.getArg 1).getSepArgs renderSqlLit?
                if items.isEmpty then some (if opStr == "in" then (if forRls then "FALSE" else "0") else (if forRls then "TRUE" else "1"))
                else some s!"({l} {if opStr == "in" then "IN" else "NOT IN"} ({String.intercalate ", " items.toList}))"
              else do let (_, op) ← matchSqlCmpOp? opStr; let r ← recR rhs; some (if forRls then s!"({l} {op} {r})" else s!"{l} {op} {r}")
            goLinks r rhs (parts.push part)
          else some parts
    (goLinks links.size (stx.getArg 0) #[]).map fun parts => String.intercalate " AND " parts.toList
  else none

@[noinline] private def renderSqlPreds (tblName : String) (colNames : Array String) (forRls : Bool)
    (tables : Array ParsedTable) (es : Array Syntax) : Array String :=
  es.foldl (init := #[]) fun acc e => match renderSqlPred? tblName colNames forRls tables #[] e with | some s => acc.push s | none => acc

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
    CommandElabM (Bool × Bool × Bool × Option (Ident × Ident) × OnDeleteAction) :=
  Lang.foldlCmd mods (false, false, false, none, OnDeleteAction.noAction) fun (isPk, isImm, isUniq, refs?, onDelete) m => do
    match m.getKind with
    | `Qed.Server.Db.modSimple =>
        match (m.getArg 0).getId.eraseMacroScopes with
        | `primary_key =>
            if isEnc then mkDbErr m s!"encrypted column `{tName}.{colName}` cannot be `primary_key`"
            return (true, isImm, isUniq, refs?, onDelete)
        | `immutable => return (isPk, true, isUniq, refs?, onDelete)
        | `unique =>
            if isEnc then mkDbErr m s!"encrypted column `{tName}.{colName}` cannot be `unique` (AES-256-GCM uses randomized nonces)"
            return (isPk, isImm, true, refs?, onDelete)
        | _ => return (isPk, isImm, isUniq, refs?, onDelete)
    | `Qed.Server.Db.modRefs =>
        if isEnc then mkDbErr m s!"encrypted column `{tName}.{colName}` cannot use `references`"
        let odOpt := m.getArg 5
        let od ← if odOpt.getNumArgs == 2 then
            match (odOpt.getArg 1).getId.eraseMacroScopes with
            | `cascade => pure .cascade | `restrict => pure .restrict
            | `set_null =>
                unless isNullable do mkDbErr (odOpt.getArg 1) s!"`on_delete set_null` on `{tName}.{colName}` requires a nullable column (`T?`)"
                pure .setNull
            | other => mkDbErr (odOpt.getArg 1) s!"unknown `on_delete` action `{other}` (expected `cascade`, `set_null`, or `restrict`)"
          else pure onDelete
        return (isPk, isImm, isUniq, some (⟨m.getArg 1⟩, ⟨m.getArg 3⟩), od)
    | _ => return (isPk, isImm, isUniq, refs?, onDelete)

@[noinline] private def parseTableColClause (qctx : PureQuotCtx) (tName : String) (existingCols : Array ParsedCol) (sc : Syntax) :
    CommandElabM (ParsedCol × Option String) := do
  let colId : Ident := ⟨sc.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
  if !isSafeSqlIdent colName then mkDbErr colId s!"invalid SQL column name `{colName}`"
  if existingCols.any (·.colName == colName) then mkDbErr colId s!"duplicate column `{colName}` in `table {tName}`"
  let tyStx := sc.getArg 2
  let (tyTerm, sqlColType, isNullable, isNat, isBytes, encKey?, enumVariants?, encSec?) ←
    if tyStx.getKind == `Qed.Server.Db.encColTy then
      let inner ← liftMacroM <| lowerSrvType (tyStx.getArg 2) false s!"encrypted column `{colName}`"
      let isB := inner.baseName == `Bytes || inner.baseName == `ByteArray
      unless inner.baseName == `String || isB do mkDbErr (tyStx.getArg 2) s!"`encrypted(...)` column `{colName}` only supports `String` or `Bytes` inner types"
      let outerOpt := (tyStx.getArg 9).getNumArgs == 1; let isNull := inner.isOption || outerOpt
      let tyT := if outerOpt && !inner.isOption then qctx.runPure (mkAppC ``Option #[inner.term]) else inner.term
      let er ← parseQedEnvRef "database" (tyStx.getArg 6); let prevOpt := tyStx.getArg 7
      let prevKeys ← if prevOpt.getNumArgs == 6 then
          (·.toList.map fun pr => (pr.envKey, pr.default?)) <$> Lang.mapCmd (prevOpt.getArg 4).getSepArgs (parseQedEnvRef "database")
        else pure []
      pure (tyT, SqlColType.text, isNull, false, isB, some { keyEnv := er.envKey, fallback? := er.default?, isBytes := isB, prevKeys }, none,
        if er.isSecret && er.default?.isNone then some er.envKey else none)
    else
      let pty ← liftMacroM <| lowerSrvType tyStx false s!"column `{colName}`"
      let (sqlTy, isNull, isN, isB) ← inferSqlColType pty
      pure (pty.term, sqlTy, isNull, isN, isB, none, (Qed.lookupUnitEnum? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pty.baseName).map (·.variants), none)
  let (isPrimaryKey, isImmutable, isUnique, refs?, onDelete) ← parseColMods tName colName isNullable encKey?.isSome (sc.getArg 3).getArgs
  let wOpt := sc.getArg 4
  return ({ ident := colId, colName, tyTerm, sqlColType, isNullable, isNat, isBytes, isPrimaryKey, isImmutable, isUnique, refs?, onDelete, enumVariants?, encKey?,
            whereExprs := if wOpt.getNumArgs == 2 then (wOpt.getArg 1).getSepArgs else #[] }, encSec?)

@[noinline] private def applyTableSubClause (qctx : PureQuotCtx) (t : ParsedTable) (sc : Syntax) : CommandElabM ParsedTable := do
  match sc.getKind with
  | `Qed.Server.Db.tblCol =>
      let (col, encSec?) ← parseTableColClause qctx t.tableName t.cols sc
      return { t with cols := t.cols.push col, encSecrets := encSec?.elim t.encSecrets (pushUnique t.encSecrets ·) }
  | `Qed.Server.Db.tblPolicy =>
      let es := (sc.getArg 3).getSepArgs
      return (sc.getArg 1).getSepArgs.foldl (init := t) fun acc opNode => match (opNode.getArg 0).getId.eraseMacroScopes with
        | `read => { acc with readPols := acc.readPols ++ es } | `insert => { acc with insertPols := acc.insertPols ++ es }
        | `update => { acc with updatePols := acc.updatePols ++ es } | `delete => { acc with deletePols := acc.deletePols ++ es }
        | `write => { acc with insertPols := acc.insertPols ++ es, updatePols := acc.updatePols ++ es, deletePols := acc.deletePols ++ es } | _ => acc
  | `Qed.Server.Db.tblTransInv =>
      let chains := (sc.getArg 6).getSepArgs.map fun ch => (ch.getArg 0).getSepArgs
      if chains.any (·.size < 2) then mkDbErr sc "`transition` invariant expects at least one `a -> b` transition arrow"
      return { t with transChains := t.transChains.push (sc.getArg 4, chains) }
  | `Qed.Server.Db.tblInv =>
      return { t with rawNamedInvs := t.rawNamedInvs.push (⟨sc.getArg 1⟩, (sc.getArg 3).getSepArgs) }
  | `Qed.Server.Db.tblIndex => return { t with indexes := t.indexes.push ((sc.getArg 2).getSepArgs.map fun s => (⟨s⟩ : Ident)) }
  | `Qed.Server.Db.tblRowEx => return if (sc.getArg 0).isIdent then { t with otherExs := t.otherExs.push sc } else { t with examples := t.examples.push sc }
  | `Qed.Server.Db.tblTransEx | `Qed.Server.Db.tblPolEx => return { t with otherExs := t.otherExs.push sc }
  | _ => mkDbErr sc s!"unexpected clause in `table {t.tableName}`"

@[noinline] private def parseTableClause (qctx : PureQuotCtx) (dbName : Name) (existing : Array ParsedTable) (c : Syntax) : CommandElabM ParsedTable := do
  let tIdent : Ident := ⟨c.getArg 1⟩; let tName := tIdent.getId.eraseMacroScopes.toString
  if !isSafeSqlIdent tName then mkDbErr tIdent s!"invalid SQL table name `{tName}`"
  if existing.any (·.tableName == tName) then mkDbErr tIdent s!"duplicate `table {tName}` in `database {dbName}`"
  let t0 ← Lang.foldlCmd (c.getArg 3).getArgs { ident := tIdent, tableName := tName } (applyTableSubClause qctx)
  if t0.cols.isEmpty then mkDbErr tIdent s!"`table {tName}` must declare at least one column"
  let rowNames := (t0.cols.map (·.colName)).push "row"
  let metaNames : Array String := #["metaColNames", "policies"]
  let t := t0.rawNamedInvs.foldl (init := t0) fun acc (invId, exprs) =>
    if exprs.all fun e => !Qed.Server.exprCallsOld e && !Qed.Server.exprMentionsAnyIdent rowNames e && Qed.Server.exprMentionsAnyIdent metaNames e then
      { acc with metaInvs := acc.metaInvs.push (invId, exprs) }
    else
      exprs.foldl (init := acc) fun a e =>
        if Qed.Server.exprCallsOld e then { a with transInvs := a.transInvs.push e } else { a with singleInvs := a.singleInvs.push e }
  return t

private def optSqlStr (ps : Array String) : Term := quote (if ps.isEmpty then none else some (String.intercalate " AND " ps.toList))

@[noinline] private def mkColSchemaTermPure (tableName : String) (colNames : Array String) (col : ParsedCol) : PureQuotM Term := do
  let cTyT := mkCIdent <| match col.sqlColType with | .text => `Qed.Server.Db.SqlColType.text | .int => `Qed.Server.Db.SqlColType.int | .bool => `Qed.Server.Db.SqlColType.bool | .bytes => `Qed.Server.Db.SqlColType.bytes
  let refT ← match col.refs? with
    | some (rt, rc) => mkOptTerm (some (← mkPairTerm (← mkSqlIdentTermPure rt.getId.eraseMacroScopes.toString) (← mkSqlIdentTermPure rc.getId.eraseMacroScopes.toString)))
    | none => pure (mkCIdent `Option.none)
  let onDelT := mkCIdent <| match col.onDelete with
    | .noAction => `Qed.Server.Db.OnDeleteAction.noAction | .cascade => `Qed.Server.Db.OnDeleteAction.cascade
    | .setNull => `Qed.Server.Db.OnDeleteAction.setNull | .restrict => `Qed.Server.Db.OnDeleteAction.restrict
  let enumChk := match col.enumVariants? with
    | some vs => if vs.isEmpty then #[] else #["\"" ++ col.colName ++ "\" IN (" ++ String.intercalate ", " (vs.toList.map quoteSqlLit) ++ ")"] | none => #[]
  let chkParts := if col.encKey?.isSome then #[renderEncryptedCheckSql col.colName col.isBytes col.whereExprs]
    else (if col.isNat && !col.isNullable then #["\"" ++ col.colName ++ "\" >= 0"] else #[]) ++ enumChk ++ renderSqlPreds tableName colNames false #[] col.whereExprs
  mkAppC `Qed.Server.Db.ColumnSchema.mk #[← mkSqlIdentTermPure col.colName, cTyT, quote col.isNullable, quote col.isPrimaryKey,
    quote col.isUnique, quote col.isImmutable, refT, onDelT, optSqlStr chkParts]

@[noinline] private def mkTableSchemaCmdPure (t : ParsedTable) (tables : Array ParsedTable) (rowTypeName : Name) (colNames : Array String) :
    PureQuotM (TSyntax `command × Term) := do
  let colSchemaTerms ← Lang.mapPQ t.cols (mkColSchemaTermPure t.tableName colNames)
  let idxTerms ← Lang.mapPQ t.indexes fun idxs => do mkListTerm (← Lang.mapPQ idxs fun ic => mkSqlIdentTermPure ic.getId.eraseMacroScopes.toString)
  let schemaId := mkIdentFrom t.ident (rowTypeName ++ `schema)
  let schemaVal ← mkAppC `Qed.Server.Db.TableSchema.mk #[← mkSqlIdentTermPure t.tableName, ← mkListTerm colSchemaTerms, ← mkListTerm idxTerms,
    ← mkListTerm ((renderSqlPreds t.tableName colNames false #[] t.singleInvs).map quote),
    optSqlStr (renderSqlPreds t.tableName colNames true tables t.readPols),
    optSqlStr (renderSqlPreds t.tableName colNames true tables t.updatePols)]
  return (← `(command| def $schemaId : Qed.Server.Db.TableSchema := $schemaVal), schemaId)

@[noinline] private def checkColInstances (fTys : Array Term) (initRepr : Bool) : TermElabM (Bool × Bool) :=
  let rec go : Nat → Bool → Bool → TermElabM (Bool × Bool)
    | 0, hI, hR => pure (hI, hR)
    | r + 1, hI, hR => do
        if !hI && !hR then return (false, false)
        let i := fTys.size - (r + 1)
        if h : i < fTys.size then
          let ty ← Term.elabType fTys[i].raw
          let hI' ← if hI then pure ((← Meta.trySynthInstance (← Meta.mkAppM ``Inhabited #[ty])) matches .some _) else pure false
          let hR' ← if hR then pure ((← Meta.trySynthInstance (← Meta.mkAppM ``Repr #[ty])) matches .some _) else pure false
          go r hI' hR'
        else pure (hI, hR)
  go fTys.size true initRepr

@[noinline] private def elabRowStructAndCodecs (tyId : Ident) (cols : Array ParsedCol) : CommandElabM Unit := do
  let (fIds, fTys) := (cols.map (·.ident), cols.map (·.tyTerm))
  let (allInhab, allRepr) ← liftTermElabM (checkColInstances fTys (!cols.any (·.isBytes)))
  let derives := #[mkIdent `DecidableEq] ++ (if allInhab then #[mkIdent `Inhabited] else #[]) ++ (if allRepr then #[mkIdent `Repr] else #[])
  let specs : Array Qed.StructFieldSpec := cols.map fun c => { ident := c.ident, wireKey := c.colName, valTy := c.tyTerm }
  Lang.elabPureCmds do
    let sCmd ← `(command| structure $tyId where $[$fIds:ident : $fTys:term]* deriving $[$derives:ident],*)
    return #[sCmd] ++ (← Qed.mkStructJsonCmdsPure tyId specs { emitNamedDefs := false }) ++
      (← Qed.mkStructProtoCmdsPure tyId specs { emitBytesCodec := false, emitLawful := true })

@[noinline] private def mkDecodeRowCmdPure (decFnId tyId : Ident) (cols : Array ParsedCol) : PureQuotM (TSyntax `command) := do
  let valsVar := mkIdent `_vals; let fIds := cols.map (·.ident); let fVals := fIds
  let colDecs ← Lang.mapPQ cols fun c => return (c.ident, c.colName, ← `(Qed.Server.Db.FromSql.fromSql (α := $(c.tyTerm))))
  let body ← mkDecodeRowBody valsVar colDecs (← `({ $[$fIds:ident := $fVals:ident],* }))
  `(command| def $decFnId ($valsVar:ident : Qed.Server.Db.DbRow) : Except String $tyId := $body)

@[noinline] private def mkTableCoreCmdsPure (rowTypeId : Ident) (mkSub : Name → Ident) (cols : Array ParsedCol)
    (rowInvBody rowInvBoolBody transInvBody : Term) : PureQuotM (Array (TSyntax `command)) := do
  let (rowVar, oldVar) := (mkIdent `_row, mkIdent `_old)
  let (rowInvId, rowInvBoolId, rowInvSoundId) := (mkSub `RowInv, mkSub `rowInvBool, mkSub `rowInvBool_sound)
  let encPairs ← Lang.mapPQ cols fun col => do
    mkPairTerm (← mkSqlIdentTermPure col.colName) (← mkAppC `Qed.Server.Db.ToSql.toSql #[← `(($rowVar:ident).$(col.ident):ident)])
  return #[
    ← Lang.noUnusedVarsPure (← `(command| @[simp] abbrev $rowInvId ($rowVar:ident : $rowTypeId) : Prop := $rowInvBody)),
    ← Lang.noUnusedVarsPure (← `(command| def $rowInvBoolId ($rowVar:ident : $rowTypeId) : Bool := $rowInvBoolBody)),
    ← Lang.noUnusedVarsPure (← `(command| theorem $rowInvSoundId ($rowVar:ident : $rowTypeId) (h : $rowInvBoolId $rowVar = true) : $rowInvId $rowVar := by
        unfold $rowInvBoolId at h; simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Qed.Lang.QedVal.val_id] at h
        try exact trivial
        try exact h
        try simp_all)),
    ← Lang.noUnusedVarsPure (← `(command| @[simp] abbrev $(mkSub `TransInv) ($oldVar:ident $rowVar:ident : $rowTypeId) : Prop := $transInvBody)),
    ← mkDecodeRowCmdPure (mkSub `decodeRow) rowTypeId cols,
    ← `(command| def $(mkSub `encodeRow) ($rowVar:ident : $rowTypeId) : List (Qed.Server.Db.SqlIdent × Qed.Server.Db.SqlVal) := $(← mkListTerm encPairs))]

@[noinline] private def mkTableMetaCmdsPure (mkSub : Name → Ident) (metaTyId : Ident) (metaCols : Array ParsedCol) : PureQuotM (Array (TSyntax `command)) := do
  let mColIdTs ← Lang.mapPQ metaCols fun c => mkSqlIdentTermPure c.colName
  return #[
    ← `(command| def $(mkSub `metaColumns) : List Qed.Server.Db.SqlIdent := $(← mkListTerm mColIdTs)),
    ← mkDecodeRowCmdPure (mkSub `decodeMetaRow) metaTyId metaCols]

private def tablePolicyNames (t : ParsedTable) : Array String :=
  let (hasR, hasI, hasU, hasD) := (!t.readPols.isEmpty, !t.insertPols.isEmpty, !t.updatePols.isEmpty, !t.deletePols.isEmpty)
  let ps := (if hasR then #["read"] else #[]) ++ (if hasI then #["insert"] else #[]) ++
    (if hasU then #["update"] else #[]) ++ (if hasD then #["delete"] else #[])
  if hasI && hasU && hasD then ps.push "write" else ps

@[noinline] private def elabTablePolicy (qctx : PureQuotCtx) (t : ParsedTable) (tables : Array ParsedTable)
    (colNames : Array String) (rowTypeId : Ident) (mkSub : Name → Ident) (snapTyId? : Option Ident)
    (suf : Name) (es : Array Syntax) : CommandElabM (TSyntax `command × String × Bool) := do
  let (rowVar, ctxVar, snapVar) := (mkIdent `_row, mkIdent `_ctx, mkIdent `_dbSnap); let isCross := es.any exprHasAnyIn
  Lang.foldlCmd es () fun _ e => if exprHasAnyIn e then validateCrossTableAnyIn tables e else pure ()
  let lowered ← Lang.mapCmd es (lowerDbExpr qctx colNames rowVar none (some ctxVar) true · tables (if isCross then snapTyId?.map (fun _ => snapVar) else none))
  if isCross && snapTyId?.isNone then mkDbErr t.ident "internal error: missing database `Snap` type for cross-table policy"
  let cmd := qctx.runPure do
    let conj ← Qed.mkConjBody lowered (ascribeProp := false)
    Lang.noUnusedVarsPure <| ← if isCross then
      `(command| @[simp] abbrev $(mkSub suf) ($snapVar:ident : $(snapTyId?.get!)) ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj)
    else `(command| @[simp] abbrev $(mkSub suf) ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj)
  return (cmd, String.intercalate " and " (es.toList.map fun pe => (pe.reprint.getD "policy").trimAscii.toString), isCross)

@[noinline] private def elabTableBody (qctx : PureQuotCtx) (dbName fullDbName : Name) (tables : Array ParsedTable)
    (snapTyId? : Option Ident) (t : ParsedTable) : CommandElabM (DbTableInfo × Term) := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTypeId := mkIdentFrom t.ident rowTypeName
  let colNames := t.cols.map (·.colName); let (rowVar, oldVar) := (mkIdent `_row, mkIdent `_old)
  let mkSub (s : Name) := mkIdentFrom t.ident (rowTypeName ++ s)
  let allRowExprs := t.cols.flatMap (·.whereExprs) ++ t.singleInvs
  Lang.foldlCmd (allRowExprs ++ t.transInvs) () fun _ e =>
    if exprHasAnyIn e then mkDbErr e "cross-table `any ... in ...:` is only supported in `policy` clauses and query `where` predicates, not single-row `where` / `invariant` rules" else pure ()
  let transProps0 ← Lang.mapCmd t.transInvs (lowerDbExpr qctx colNames rowVar (some oldVar) none true)
  let transProps ← Lang.foldlCmd t.transChains transProps0 fun acc (tgtStx, chains) => do
    let (oldTgt, newTgt) := (← lowerDbExpr qctx colNames oldVar none none false tgtStx, ← lowerDbExpr qctx colNames rowVar none none false tgtStx)
    let edgePairs ← Lang.foldlCmd chains #[] fun eps ch =>
      Lang.foldlCmd (Array.range (ch.size - 1)) eps fun ps i => do
        return ps.push (← lowerDbExpr qctx colNames rowVar none none false ch[i]!, ← lowerDbExpr qctx colNames rowVar none none false ch[i + 1]!)
    return acc.push <| qctx.runPure do Lang.foldlPQ edgePairs (← `($newTgt = $oldTgt)) fun d (ci, ci1) => `($d ∨ ($oldTgt = $ci ∧ $newTgt = $ci1))
  let rowPropTs ← Lang.mapCmd allRowExprs (lowerDbExpr qctx colNames rowVar none none true)
  let rowBoolTs ← Lang.mapCmd allRowExprs (lowerDbExpr qctx colNames rowVar none none false)
  Lang.elabPureCmds do
    mkTableCoreCmdsPure rowTypeId mkSub t.cols (← Qed.mkConjBody rowPropTs (ascribeProp := false)) (← mkBoolConj rowBoolTs) (← Qed.mkConjBody transProps (ascribeProp := false))
  let metaCols := t.cols.filter (·.encKey?.isNone); let hasMeta := t.cols.any (·.encKey?.isSome) && !metaCols.isEmpty
  let mColStrLits : Array Term := metaCols.map fun c => Syntax.mkStrLit c.colName
  let polStrLits : Array Term := (tablePolicyNames t).map fun s => Syntax.mkStrLit s
  Lang.elabPureCmds do return #[
    ← `(command| def $(mkSub `metaColNames) : List String := $(← mkListTerm mColStrLits)),
    ← `(command| def $(mkSub `policies) : List String := $(← mkListTerm polStrLits))]
  if hasMeta then
    let metaTyId := mkSub `Meta; elabRowStructAndCodecs metaTyId metaCols
    Lang.elabPureCmds (mkTableMetaCmdsPure mkSub metaTyId metaCols)
  let tblFull := fullDbName ++ t.ident.getId
  let tblAliases : Array (String × Term) := #[("metaColNames", mkSub `metaColNames), ("policies", mkSub `policies)]
  let tblUnfolds : Array Name := #[tblFull ++ `metaColNames, tblFull ++ `policies]
  Lang.foldlCmd t.metaInvs () fun _ (invId, exprs) =>
    Qed.Verify.Core.elabStaticMetaInv s!"{dbName}.{t.tableName}" (tblFull ++ invId.getId.eraseMacroScopes) tblAliases tblUnfolds invId exprs
  let polRes ← Lang.mapCmd #[(`ReadPolicy, t.readPols), (`InsertPolicy, t.insertPols), (`UpdatePolicy, t.updatePols), (`DeletePolicy, t.deletePols)] fun (s, es) =>
    elabTablePolicy qctx t tables colNames rowTypeId mkSub snapTyId? s es
  let (schemaCmd, schemaTerm) := qctx.runPure (mkTableSchemaCmdPure t tables rowTypeName colNames)
  Lang.foldlCmd polRes () fun _ (cmd, _, _) => elabCommand cmd
  elabCommand schemaCmd
  let colInfos : Array DbColumnInfo := t.cols.map fun c => {
    name := c.colName, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable, isUnique := c.isUnique,
    isNullable := c.isNullable, isNat := c.isNat, isInt := c.sqlColType == .int && !c.isNat,
    isBool := c.sqlColType == .bool, isBytes := c.sqlColType == .bytes,
    refs? := c.refs?.map fun (rt, rc) => (rt.getId.eraseMacroScopes.toString, rc.getId.eraseMacroScopes.toString), encKey? := c.encKey? }
  return ({
    tableName := t.tableName, rowTypeConst := fullDbName ++ t.ident.getId, columns := colInfos, hasMeta,
    hasReadPolicy := !t.readPols.isEmpty, hasInsertPolicy := !t.insertPols.isEmpty, hasUpdatePolicy := !t.updatePols.isEmpty, hasDeletePolicy := !t.deletePols.isEmpty,
    hasCrossReadPolicy := polRes[0]!.2.2, hasCrossInsertPolicy := polRes[1]!.2.2, hasCrossUpdatePolicy := polRes[2]!.2.2, hasCrossDeletePolicy := polRes[3]!.2.2,
    hasTransInv := !t.transInvs.isEmpty || !t.transChains.isEmpty,
    readPolicyLabel := polRes[0]!.2.1, insertPolicyLabel := polRes[1]!.2.1, updatePolicyLabel := polRes[2]!.2.1, deletePolicyLabel := polRes[3]!.2.1 }, schemaTerm)

@[noinline] private def elabBackfillClause (qctx : PureQuotCtx) (dbName : Name) (tableInfos : Array DbTableInfo) (bc : Syntax) : CommandElabM Term := do
  let tblId : Ident := ⟨bc.getArg 1⟩; let tblName := tblId.getId.eraseMacroScopes.toString
  let some tInfo := tableInfos.find? (·.tableName == tblName) | mkDbErr tblId s!"`backfill` references unknown table `{tblName}` in `database {dbName}`"
  let rowTyId := mkIdentFrom tblId tInfo.rowTypeConst
  let parsedSet ← parseDbSetItems tInfo (bc.getArg 4).getSepArgs s!"`backfill {tblName}`" false (forbidPk := true) (forbidEncAll := true)
  let setPairs ← Lang.mapCmd parsedSet fun (colId, col, _, valStx) => do
    let valT ← liftMacroM (lowerSimpleQedExpr .val valStx); let colSql ← mkSqlIdentTerm colId col.name
    return qctx.runPure do mkPairTerm colSql (← mkTypedSqlParamTerm rowTyId (mkIdentFrom colId (Name.mkSimple col.name)) valT)
  let whereT ← if (bc.getArg 6).getNumArgs == 2 then
      let wRaw := unwrapParens1 ((bc.getArg 6).getArg 1)
      let (rVar, bodyStx) := if wRaw.getKind == ``qedLam1 then let b := wRaw.getArg 0; (if b.isIdent then b.getId.eraseMacroScopes.toString else "_row", wRaw.getArg 2) else ("", wRaw)
      lowerRowSqlExpr (fun _ e => liftMacroM (lowerSimpleQedExpr .val e)) { dbName, shortName := dbName.toString, configConst := .anonymous, ensureSchemaConst := .anonymous, secrets := #[], tables := tableInfos } #[(rVar, tInfo, tblName)] bodyStx
    else pure (mkCIdent `Qed.Server.Db.SqlExpr.litTrue)
  let tblSql ← mkSqlIdentTerm tblId tblName
  return qctx.runPure do mkAppC `Qed.Server.Db.SqlQuery.update #[tblSql, ← mkListTerm setPairs, whereT, mkCIdent `List.nil]

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
    CommandElabM (Array Ident × Array Term × Std.HashSet String) :=
  Lang.foldlCmd assigns (#[], #[], {}) fun (fIds, fVals, seen) item => do
    let fid : Ident := ⟨item.getArg 0⟩; let fn := fid.getId.eraseMacroScopes.toString
    unless t.cols.any (·.colName == fn) do
      mkDbErr fid s!"table `{t.tableName}` {clauseKind} `{exName.getId}`: unknown column `{fn}` (expected: {String.intercalate ", " (t.cols.toList.map (·.colName))})"
    if checkDup && seen.contains fn then mkDbErr fid s!"table `{t.tableName}` {clauseKind} `{exName.getId}`: duplicate column `{fn}`"
    return (fIds.push (mkIdentFrom fid (Name.mkSimple fn)), fVals.push (← lowerDbExExpr dbName t allEx (item.getArg 2)), seen.insert fn)

@[noinline] private def mkStructWithPure (baseT tyId : Term) (fIds : Array Ident) (fVals : Array Term) : PureQuotM Term :=
  `({ ($baseT : $tyId) with $[$fIds:ident := $fVals:term],* })

@[noinline] private def elabTableCheckThm (qctx : PureQuotCtx) (ref : Syntax) (thmId : Ident) (goal : Term) (simpIds : Array Ident) (errMsg : String) : CommandElabM Unit :=
  withRef ref <| elabCommand <| qctx.runPure `(command| theorem $thmId : $goal := by
    (try simp only [$[$simpIds:ident],*, Qed.Lang.QedVal.val_id]); all_goals (first | trivial | qedCloseGround | rfl | decide | omega | fail $(Syntax.mkStrLit errMsg)))

@[noinline] private def elabOneTableEx (qctx : PureQuotCtx) (dbName : Name) (tables : Array ParsedTable) (t : ParsedTable) (tInfo : DbTableInfo)
    (allEx : Std.HashMap String (Array Name)) (snapTyId? : Option Ident) (hasInhab : Bool) (stx : Syntax) : CommandElabM Unit := do
  let rowTypeName := dbName ++ t.ident.getId; let rowTyId := mkIdentFrom t.ident rowTypeName
  let mkSub (ref : Syntax) (s : Name) := mkIdentFrom ref (rowTypeName ++ s)
  let mkMaybeNot (pos : Bool) (p : Term) : PureQuotM Term := if pos then pure p else mkAppC ``Not #[p]
  match stx.getKind with
  | `Qed.Server.Db.tblRowEx =>
      let isRejects := (stx.getArg 0).isIdent; let id : Ident := ⟨stx.getArg 1⟩; let nm := id.getId.eraseMacroScopes
      let clauseKind := if isRejects then "rejects" else "example"
      let (fIds, fVals, seen) ← parseTableAssigns dbName t allEx clauseKind id (stx.getArg 4).getSepArgs
      let baseOpt := stx.getArg 2
      let baseTerm? : Option Term := if baseOpt.getNumArgs == 2 then
          let baseId : Ident := ⟨baseOpt.getArg 1⟩; let bn := baseId.getId.eraseMacroScopes
          some (if (allEx.getD t.tableName #[]).contains bn then mkIdentFrom baseId (rowTypeName ++ bn) else ⟨baseId.raw⟩)
        else if hasInhab && seen.size < t.cols.size then some (mkCIdent ``default) else none
      let rowTerm ← match baseTerm? with
        | some bt => pure <| qctx.runPure (mkStructWithPure bt rowTyId fIds fVals)
        | none =>
            if let some miss := t.cols.find? (!seen.contains ·.colName) then mkDbErr id s!"table `{t.tableName}` {clauseKind} `{id.getId}`: missing column `{miss.colName}`"
            pure <| qctx.runPure `(({ $[$fIds:ident := $fVals:term],* } : $rowTyId))
      let rowInvId := mkSub t.ident `RowInv
      if isRejects then
        elabTableCheckThm qctx id (mkSub id (Name.mkSimple s!"rejects_{nm}")) (qctx.runPure do mkAppC ``Not #[← mkAppTermsPure rowInvId #[rowTerm]]) #[rowInvId]
          s!"Database `rejects {nm}` on table `{t.tableName}` could not be proved invalid (row may satisfy all invariants)"
      else
        let defId := mkSub id nm; elabCommand (qctx.runPure `(command| def $defId : $rowTyId := $rowTerm))
        elabTableCheckThm qctx id (mkSub id (Name.mkSimple s!"{nm}_valid")) (qctx.runPure (mkAppTermsPure rowInvId #[defId])) #[rowInvId, defId]
          s!"Database `example {nm}` on table `{t.tableName}` does not satisfy row invariants"
  | `Qed.Server.Db.tblTransEx =>
      let isAllows := !(stx.getArg 0).isIdent; let trId : Ident := ⟨stx.getArg 2⟩; let nm := trId.getId.eraseMacroScopes
      let transInvId := mkSub t.ident `TransInv
      let oldTerm ← lowerDbExExpr dbName t allEx (stx.getArg 4); let rhsNode := stx.getArg 6
      let newTerm ← if rhsNode.getNumArgs > 0 && (rhsNode.getArg 0).getKind == `Qed.Server.Db.assignItem then
          let (fIds, fVals, _) ← parseTableAssigns dbName t allEx "transition" trId rhsNode.getSepArgs false
          pure (qctx.runPure (mkStructWithPure oldTerm rowTyId fIds fVals))
        else lowerDbExExpr dbName t allEx rhsNode
      let goal := qctx.runPure do mkMaybeNot isAllows (← mkAppTermsPure transInvId #[oldTerm, newTerm])
      elabTableCheckThm qctx trId (mkSub trId (Name.mkSimple s!"{if isAllows then "trans_" else "trans_rejects_"}{nm}")) goal #[transInvId]
        s!"Database `{if isAllows then "example" else "rejects"} transition {nm}` on table `{t.tableName}` failed transition invariant check"
  | `Qed.Server.Db.tblPolEx =>
      let isAllows := !(stx.getArg 0).isIdent
      let opName := ((stx.getArg 2).getArg 0).getId.eraseMacroScopes; let pId : Ident := ⟨stx.getArg 3⟩
      let (kvs, user?, snaps) ← Lang.foldlCmd (stx.getArg 5).getArgs (({} : Std.HashMap Name Term), (none : Option Syntax), ({} : Std.HashMap String Term)) fun (kvs, user?, snaps) item => do
        match item.getKind with
        | `Qed.Server.Db.polExKv =>
            let k := (item.getArg 0).getId.eraseMacroScopes; let rhs := item.getArg 2
            if k == `user then return (kvs, some rhs, snaps) else return (kvs.insert k (← lowerDbExExpr dbName t allEx rhs), user?, snaps)
        | `Qed.Server.Db.polExSnap =>
            let stblId : Ident := ⟨item.getArg 1⟩; let stbl := stblId.getId.eraseMacroScopes.toString
            unless tables.any (·.tableName == stbl) do mkDbErr stblId s!"policy example `{pId.getId}`: unknown table `{stbl}` in `snap`"
            return (kvs, user?, snaps.insert stbl (← lowerDbExExpr dbName t allEx (item.getArg 3)))
        | _ => return (kvs, user?, snaps)
      let some rowTerm := kvs[`row]? | mkDbErr stx s!"`table {t.tableName}` policy example `{pId.getId}` requires `row = ...`"
      let userVal? ← match user? with
        | none => pure none | some uStx => if isNoneIdent? uStx then pure none else some <$> lowerDbExExpr dbName t allEx uStx
      let polSpecs : Array (Ident × Bool) := match opName with
        | `read => #[(mkSub pId `ReadPolicy, tInfo.hasCrossReadPolicy)] | `insert => #[(mkSub pId `InsertPolicy, tInfo.hasCrossInsertPolicy)]
        | `update => #[(mkSub pId `UpdatePolicy, tInfo.hasCrossUpdatePolicy)] | `delete => #[(mkSub pId `DeletePolicy, tInfo.hasCrossDeletePolicy)]
        | `write => #[(mkSub pId `InsertPolicy, tInfo.hasCrossInsertPolicy), (mkSub pId `UpdatePolicy, tInfo.hasCrossUpdatePolicy), (mkSub pId `DeletePolicy, tInfo.hasCrossDeletePolicy)] | _ => #[]
      if polSpecs.any (·.2) && snapTyId?.isNone then mkDbErr stx "internal error: missing Snap for cross-table policy example"
      let fullGoal := qctx.runPure do
        let ctxTerm ← match kvs[`ctx]? with
          | some ct => pure ct
          | none =>
              let uT ← mkOptTerm userVal?
              let cT : Term ← match kvs[`role]? with | none => pure (mkCIdent `List.nil) | some r => mkListTerm #[← mkPairTerm (Syntax.mkStrLit "role") r]
              let aT : Term ← match kvs[`session]? with
                | some s => `(if $s then Qed.Server.AuthMethod.session else Qed.Server.AuthMethod.bearer)
                | none => pure (mkCIdent (if userVal?.isSome then `Qed.Server.AuthMethod.bearer else `Qed.Server.AuthMethod.none))
              `({ userId := $uT, claims := $cT, authMethod := $aT : Qed.Server.RequestCtx })
        let snapTerm? ← match snapTyId? with
          | none => pure none
          | some sTyId =>
              let sFIds := tables.map (·.ident); let sFVals : Array Term := tables.map fun tbl => snaps[tbl.tableName]?.getD (mkCIdent `List.nil : Term)
              some <$> `({ $[$sFIds:ident := $sFVals:term],* : $sTyId })
        Qed.mkConjBody (← Lang.mapPQ polSpecs fun (polId, isC) => do
          mkMaybeNot isAllows (← mkAppTermsPure polId (if isC then #[snapTerm?.get!, ctxTerm, rowTerm] else #[ctxTerm, rowTerm]))) (ascribeProp := false)
      let verb := if isAllows then "allows" else "denies"
      let kwLabel := if isAllows then "example" else "rejects"
      elabTableCheckThm qctx pId (mkSub pId (Name.mkSimple s!"policy_{opName}_{verb}_{pId.getId.eraseMacroScopes}")) fullGoal (polSpecs.map (·.1))
        s!"Database `{kwLabel} policy {opName} {pId.getId.eraseMacroScopes}` on table `{t.tableName}` failed policy check"
  | _ => pure ()

@[noinline] private def elabAllTableExamples (qctx : PureQuotCtx) (dbName : Name) (tables : Array ParsedTable)
    (tableInfos : Array DbTableInfo) (snapTyId? : Option Ident) : CommandElabM Unit := do
  let allEx ← Lang.foldlCmd tables ({} : Std.HashMap String (Array Name)) fun acc t => do
    let names ← Lang.foldlCmd t.examples #[] fun ns exStx => do
      let exId : Ident := ⟨exStx.getArg 1⟩; let n := exId.getId.eraseMacroScopes
      if ns.contains n then mkDbErr exId s!"duplicate `example {n}` in `table {t.tableName}`"
      return ns.push n
    return acc.insert t.tableName names
  let hasInhabs ← Lang.mapCmd tables fun t => liftTermElabM do
    return (← Meta.trySynthInstance (← Meta.mkAppM ``Inhabited #[← Term.elabType (mkIdentFrom t.ident (dbName ++ t.ident.getId)).raw])) matches .some _
  let zipped := (tables.zip tableInfos).zip hasInhabs
  Lang.foldlCmd zipped () fun _ ((t, tInfo), hasInhab) =>
    Lang.foldlCmd t.examples () fun _ s => elabOneTableEx qctx dbName tables t tInfo allEx snapTyId? hasInhab s
  Lang.foldlCmd zipped () fun _ ((t, tInfo), hasInhab) =>
    Lang.foldlCmd t.otherExs () fun _ s => elabOneTableEx qctx dbName tables t tInfo allEx snapTyId? hasInhab s

@[noinline] private def validateDbTables (dbName : Name) (tables : Array ParsedTable) : CommandElabM Unit :=
  Lang.foldlCmd tables () fun _ t => do
    let colNames := t.cols.map (·.colName)
    Lang.foldlCmd t.cols () fun _ col => do
      if let some (rtId, rcId) := col.refs? then
        let (rt, rc) := (rtId.getId.eraseMacroScopes.toString, rcId.getId.eraseMacroScopes.toString)
        let some targetTbl := tables.find? (·.tableName == rt) | mkDbErr rtId s!"table `{t.tableName}` column `{col.colName}` references unknown table `{rt}` in `database {dbName}`"
        unless targetTbl.cols.any (·.colName == rc) do mkDbErr rcId s!"table `{t.tableName}` column `{col.colName}` references unknown column `{rt}.{rc}`"
    Lang.foldlCmd t.indexes () fun _ idxCols =>
      Lang.foldlCmd idxCols () fun _ ic => do
        let cn := ic.getId.eraseMacroScopes.toString
        unless colNames.contains cn do mkDbErr ic s!"index on `table {t.tableName}` references unknown column `{cn}`"
        if t.cols.any fun c => c.colName == cn && c.encKey?.isSome then mkDbErr ic s!"cannot index encrypted column `{t.tableName}.{cn}` (AES-256-GCM uses randomized nonces)"

@[noinline] private def mkClientTableFieldPure (dbName : Name) (cfgParamId : Ident) (t : ParsedTable) : PureQuotM (Ident × Term × Term) := do
  let rowTyId := mkIdentFrom t.ident (dbName ++ t.ident.getId); let colIdTs ← Lang.mapPQ t.cols fun c => mkSqlIdentTermPure c.colName
  let encCols := t.cols.map fun c => (c.colName, c.encKey?)
  let ewTs ← mkColsEncPairs t.tableName encCols fun cn _ => Syntax.mkStrLit cn
  let erTs ← mkColsEncPairs t.tableName encCols fun _ idx => Syntax.mkNumLit (toString idx)
  let hVal ← mkAppC `Qed.Server.Db.TableHandle.mk #[cfgParamId, ← mkSqlIdentTermPure t.tableName, ← mkListTerm colIdTs,
    mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `decodeRow), mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `encodeRow),
    mkIdentFrom t.ident (dbName ++ t.ident.getId ++ `rowInvBool), ← mkListTerm ewTs, ← mkListTerm erTs]
  return (mkIdentFrom t.ident (Name.mkSimple t.tableName), ← mkAppC `Qed.Server.Db.TableHandle #[rowTyId], hVal)

@[noinline] private def mkDbClientCmdsPure (dbIdent : Ident) (dbName : Name) (configId : Ident) (tables : Array ParsedTable) : PureQuotM (Array (TSyntax `command)) := do
  let mkDb (s : Name) := mkIdentFrom dbIdent (dbName ++ s)
  let (clientStructId, clientWithId, cfgParamId, mId) := (mkDb `Client, mkDb `clientWith, mkIdent `_cfg, mkIdent `m)
  let tblFlds ← Lang.mapPQ tables (mkClientTableFieldPure dbName cfgParamId)
  let cfIds := #[mkIdent `config] ++ tblFlds.map (·.1); let ciIds := cfIds
  let cfTys := #[mkCIdent `Qed.Server.Db.DbConfig] ++ tblFlds.map (·.2.1); let ciVals := #[⟨cfgParamId.raw⟩] ++ tblFlds.map (·.2.2)
  return #[
    ← `(command| structure $clientStructId where $[$cfIds:ident : $cfTys:term]*),
    ← `(command| def $clientWithId ($cfgParamId:ident : Qed.Server.Db.DbConfig) : $clientStructId := { $[$ciIds:ident := $ciVals:term],* }),
    ← `(command| def $(mkDb `client) : $clientStructId := $clientWithId $configId),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `ensureSchema)) {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl _c.config),
    ← `(command| def $(mkIdentFrom dbIdent (dbName ++ `Client ++ `transaction)) {$mId:ident : Type → Type} {α : Type} [Monad $mId] [Qed.Server.MonadServer $mId] (_c : $clientStructId) (body : UInt64 → $mId (Except Qed.Server.ApiError α)) : $mId (Except Qed.Server.ApiError α) := Qed.Server.Db.withTransaction _c.config body)]

@[noinline] private def mkDbTailCmdsPure (dbIdent : Ident) (dbName fullDbName : Name) (dbShort : String)
    (tables : Array ParsedTable) (resolved : Qed.Cloud.EnvMap (Term × Qed.Cloud.DbEnvSpec))
    (devEp? : Option Term) (hasExplicitEnv isManaged : Bool) (secrets : Array String)
    (tableSchemaTerms backfillTerms : Array Term) : PureQuotM (Array (TSyntax `command)) := do
  let mkDb (s : Name) := mkIdentFrom dbIdent (dbName ++ s)
  let (configId, ensureId, mId) := (mkDb `config, mkDb `ensureSchema, mkIdent `m)
  let envEndpointsTerm ← mkOptTerm <| ← if hasExplicitEnv then
      some <$> mkAppC `Qed.Cloud.EnvMap.mk #[resolved.dev.1, resolved.preview.1, resolved.staging.1, resolved.prod.1]
    else pure none
  let cfgVal ← mkAppC `Qed.Server.Db.DbConfig.mk #[Syntax.mkStrLit dbShort, resolved.prod.1, ← mkOptTerm devEp?, envEndpointsTerm,
    quote isManaged, ← mkListTerm tableSchemaTerms, ← mkListTerm backfillTerms]
  let tblMetaTerms ← Lang.mapPQ tables fun t => do
    let sub (leaf : Name) := mkIdentFrom t.ident (dbName ++ t.ident.getId ++ leaf)
    let (hasR, hasI, hasU, hasD) := (!t.readPols.isEmpty, !t.insertPols.isEmpty, !t.updatePols.isEmpty, !t.deletePols.isEmpty)
    mkAppC `Qed.Server.Db.TableMetaInfo.mk #[Syntax.mkStrLit t.tableName, sub `metaColNames, sub `policies,
      quote hasR, quote hasI, quote hasU, quote hasD, quote (hasI && hasU && hasD)]
  let core : Array (TSyntax `command) := #[
    ← `(command| abbrev $(mkDb `Tx) : Type := Qed.Server.Db.DbTx $(Syntax.mkStrLit fullDbName.toString)),
    ← Lang.mkStrArrDefPure (mkDb `secrets) secrets,
    ← `(command| def $(mkDb `tables) : Array Qed.Server.Db.TableMetaInfo := #[$[$tblMetaTerms:term],*]),
    ← `(command| def $configId : Qed.Server.Db.DbConfig := $cfgVal),
    ← `(command| def $(mkDb `ddl) (dialect : Qed.Server.Db.SqlDialect := .postgres) : String := Qed.Server.Db.renderDatabaseDdl dialect ($configId).tables),
    ← `(command| def $(mkDb `rlsDdl) : String := Qed.Server.Db.renderDatabaseRlsDdl ($configId).tables),
    ← `(command| def $ensureId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] : $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl $configId),
    ← `(command| instance $(mkDb `instSafeIOEnsureSchema):ident {_σ : Type} : Qed.Server.SafeIO (@$ensureId (Qed.Server.ThreadProg _σ) _ _) where noAtomic := Qed.Server.NoAtomic.io (.dbExecDdl $configId) _ .pure)]
  return core ++ (← mkDbClientCmdsPure dbIdent dbName configId tables)

private structure ParsedDbState where
  primaryEp? : Option (Term × Qed.Cloud.DbEnvSpec) := none
  envSlots : Qed.Cloud.EnvMap (Option (Term × Qed.Cloud.DbEnvSpec)) := Qed.Cloud.EnvMap.ofDefault none
  isManaged : Bool := false
  hasExplicitEnv : Bool := false
  secrets : Array String := #[]
  tables : Array ParsedTable := #[]
  backfillClauses : Array Syntax := #[]
  invs : Array (Ident × Array Syntax) := #[]

@[noinline] private def setDbEnvSlot (qctx : PureQuotCtx) (dbName : Name) (ref : Syntax) (envStr : String) (epStx : Syntax) (inManaged : Bool) (s : ParsedDbState) : CommandElabM ParsedDbState := do
  let some env := Qed.Cloud.DeployEnv.parse? envStr | mkDbErr ref s!"unexpected environment `{envStr}` in `database {dbName}`"
  if inManaged && env == .prod then mkDbErr ref s!"cannot override `prod` inside `managed postgres:` in `database {dbName}`"
  if (s.envSlots.get env).isSome then mkDbErr ref s!"duplicate `{envStr}` endpoint in `database {dbName}`"
  let (epT, secs, spec) ← parseEndpointSpec qctx epStx (some env)
  return { s with envSlots := s.envSlots.set env (some (epT, spec)), secrets := if env == .dev then s.secrets else secs.foldl pushUnique s.secrets }

@[noinline] private def applyOneDbClause (qctx : PureQuotCtx) (dbIdent : Ident) (dbName : Name) (dbShort : String)
    (st : ParsedDbState) (c : Syntax) : CommandElabM ParsedDbState := do
  match c.getKind with
  | `Qed.Server.Db.dbManaged =>
      if st.isManaged || st.primaryEp?.isSome || Qed.Cloud.DeployEnv.all.any (st.envSlots.get · |>.isSome) then
        mkDbErr c s!"cannot combine `managed postgres` with other endpoint clauses in `database {dbName}` (nest overrides under `managed postgres:`)"
      let subArgs := if (c.getArg 2).getNumArgs == 2 then ((c.getArg 2).getArg 1).getArgs else #[]
      let (s, previewEphemeral) ← Lang.foldlCmd subArgs ({ st with isManaged := true, hasExplicitEnv := true }, false) fun (s, prevEph) sc => do
        match sc.getKind with
        | `Qed.Server.Db.managedPreviewEphemeral =>
            if prevEph || s.envSlots.preview.isSome then mkDbErr sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
            return (s, true)
        | `Qed.Server.Db.managedEnvOverride =>
            let envStr := (sc.getArg 0).getId.eraseMacroScopes.toString
            if envStr == "preview" && prevEph then mkDbErr sc s!"duplicate `preview` override in `managed postgres:` of `database {dbName}`"
            return (← setDbEnvSlot qctx dbName sc envStr (sc.getArg 1) true s, prevEph)
        | _ => mkDbErr sc "unexpected clause in `managed postgres:`"
      let targets := Qed.Cloud.managedPostgresTargets dbShort previewEphemeral (s.envSlots.dev.map Prod.snd)
      let s ← Lang.foldlCmd Qed.Cloud.DeployEnv.all.toArray s fun s e => do
        if (s.envSlots.get e).isSome then return s
        let sp := targets.get e
        let epT ← match sp with
          | .managedPostgres nm env => pure <| qctx.runPure (mkAppC `Qed.Server.Db.DbEndpoint.managedPostgres #[quote nm, mkCIdent (`Qed.Cloud.DeployEnv ++ Name.mkSimple env.toString)])
          | .ephemeralSqlite p | .byoSqlite p => pure <| qctx.runPure (mkAppC `Qed.Server.Db.DbEndpoint.sqlitePath #[quote p])
          | _ => mkDbErr dbIdent s!"internal error lowering managed database target in `database {dbName}`"
        return { s with envSlots := s.envSlots.set e (some (epT, sp)) }
      return { s with secrets := targets.prod.secrets.foldl (fun acc sr => pushUnique acc sr.envVar) s.secrets }
  | `Qed.Server.Db.dbPrimaryEp =>
      if st.isManaged || st.primaryEp?.isSome || st.envSlots.prod.isSome then mkDbErr c s!"duplicate endpoint specification in `database {dbName}`"
      let (epT, secs, spec) ← parseEndpointSpec qctx (c.getArg 0) none
      return { st with primaryEp? := some (epT, spec), secrets := secs.foldl pushUnique st.secrets }
  | `Qed.Server.Db.dbEnvEp =>
      let envStr := (c.getArg 0).getId.eraseMacroScopes.toString
      if st.isManaged then mkDbErr c s!"cannot combine `managed postgres` with top-level `{envStr}` endpoint in `database {dbName}` (nest overrides under `managed postgres:`)"
      if envStr == "prod" && st.primaryEp?.isSome then mkDbErr c s!"cannot combine a default endpoint with `prod` in `database {dbName}`"
      setDbEnvSlot qctx dbName c envStr (c.getArg 1) false { st with hasExplicitEnv := st.hasExplicitEnv || envStr != "dev" }
  | `Qed.Server.Db.dbTable =>
      let tbl ← parseTableClause qctx dbName st.tables c
      return { st with tables := st.tables.push tbl, secrets := tbl.encSecrets.foldl pushUnique st.secrets }
  | `Qed.Server.Db.dbBackfill => return { st with backfillClauses := st.backfillClauses.push c }
  | `Qed.Server.Db.dbInv =>
      let invId : Ident := ⟨c.getArg 1⟩; let leaf := invId.getId.eraseMacroScopes
      if st.invs.any (·.1.getId.eraseMacroScopes == leaf) then mkDbErr invId s!"duplicate invariant `{leaf}` in `database {dbName}`"
      return { st with invs := st.invs.push (invId, (c.getArg 3).getSepArgs) }
  | _ => mkDbErr c s!"unexpected clause in `database {dbName}`"

@[noinline, command_elab databaseCmd] def elabDatabaseCmd : CommandElab := fun stx => do
  let qctx ← Lang.getPureQuotCtxCmd
  let dbIdent : Ident := ⟨stx.getArg 2⟩; let dbName := dbIdent.getId; let dbShort := dbName.toString; let fullDbName := (← getCurrNamespace) ++ dbName
  let st ← Lang.foldlCmd (stx.getArg 4).getArgs {} (applyOneDbClause qctx dbIdent dbName dbShort)
  let some _ := st.envSlots.prod.orElse (fun _ => st.primaryEp?)
    | mkDbErr dbIdent s!"`database {dbName}` must specify an endpoint (e.g. `managed postgres`, `postgres ...`, `sqlite ...`, `url secret(\"DATABASE_URL\")`, `d1 ...`, `turso ...`, or `http ...`)"
  let resolved ← st.envSlots.mapM fun e slot? => match slot?.orElse (fun _ => st.primaryEp?) with
    | some p => pure p | none => mkDbErr dbIdent s!"`database {dbName}` is missing a `{e}` endpoint (specify `{e} ...`, a default endpoint, or use `managed postgres`)"
  if st.tables.isEmpty then mkDbErr dbIdent s!"`database {dbName}` must declare at least one `table`"
  validateDbTables dbName st.tables
  Lang.elabPureCmd (Lang.mkMarkerThmPure (mkIdentFrom dbIdent (dbName ++ `_qed_database_marker)))
  Lang.foldlCmd st.tables () fun _ t => elabRowStructAndCodecs (mkIdentFrom t.ident (dbName ++ t.ident.getId)) t.cols
  let (snapTyId?, snapConst?) ← if st.tables.size >= 2 || st.tables.any fun t => (t.readPols ++ t.insertPols ++ t.updatePols ++ t.deletePols).any exprHasAnyIn then do
      let snapId := mkIdentFrom dbIdent (dbName ++ `Snap); let sFIds := st.tables.map (·.ident)
      Lang.elabPureCmd do
        let sFTys ← Lang.mapPQ st.tables fun t => mkAppC ``List #[mkIdentFrom t.ident (dbName ++ t.ident.getId)]
        `(command| structure $snapId where $[$sFIds:ident : $sFTys:term]*)
      pure (some snapId, some (fullDbName ++ `Snap))
    else pure (none, none)
  let (tableInfos, tableSchemaTerms) := (← Lang.mapCmd st.tables (elabTableBody qctx dbName fullDbName st.tables snapTyId?)).unzip
  elabAllTableExamples qctx dbName st.tables tableInfos snapTyId?
  let backfillTerms ← Lang.mapCmd st.backfillClauses (elabBackfillClause qctx dbName tableInfos)
  Lang.elabPureCmds (mkDbTailCmdsPure dbIdent dbName fullDbName dbShort st.tables resolved (st.envSlots.dev.map Prod.fst) st.hasExplicitEnv st.isManaged st.secrets tableSchemaTerms backfillTerms)
  let mkDb (s : Name) := mkIdentFrom dbIdent (dbName ++ s)
  let dbAliases : Array (String × Term) := #[("secrets", mkDb `secrets), ("tables", mkDb `tables)]
  let tblMetaUnfolds := st.tables.flatMap fun t => #[fullDbName ++ t.ident.getId ++ `metaColNames, fullDbName ++ t.ident.getId ++ `policies]
  let dbUnfolds : Array Name := #[fullDbName ++ `secrets, fullDbName ++ `tables] ++ tblMetaUnfolds
  Lang.foldlCmd st.invs () fun _ (invId, exprs) =>
    Qed.Verify.Core.elabStaticMetaInv dbShort (fullDbName ++ invId.getId.eraseMacroScopes) dbAliases dbUnfolds invId exprs
  modifyEnv fun env => databaseRegistry.addEntry env {
    dbName := fullDbName, shortName := dbShort, configConst := fullDbName ++ `config, ensureSchemaConst := fullDbName ++ `ensureSchema,
    snapTypeConst? := snapConst?, secrets := st.secrets, hasDevFallback := st.envSlots.dev.isSome, isManaged := st.isManaged,
    envSpecs := { dev := resolved.dev.2, preview := resolved.preview.2, staging := resolved.staging.2, prod := resolved.prod.2 }, tables := tableInfos }

end DbElabImpl
end Qed.Server.Db
