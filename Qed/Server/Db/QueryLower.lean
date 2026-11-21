import Lean
import Qed.Lang
import Qed.Diag
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime

namespace Qed.Server.Db
open Qed.Lang

/-! ## Dual Lean + Parameterized SQL Query Lowering for `server` `use db : <Database>`
    Translates high-level `db.<table>.<op>(...)` calls inside `server` `def`s simultaneously into:
    1. A typed, injection-proof `SqlQuery` with validated `SqlIdent`s and bound `SqlVal` parameters,
    2. A matching pure Lean predicate `wherePred : Row → Bool` and updater `setFn : Row → Row`,
    3. Compile-time proof obligations discharged via `qedDbProve` for table `policy` rules,
       column `where` / `RowInv` constraints, `immutable` guards, and `old(row)` / `transition`
       invariants. -/

open Lean in
partial def extractDottedChain? (stx : Syntax) : Option (List String) :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent then
    some ((u.getArg 0).getId.eraseMacroScopes.components.map (·.toString))
  else if u.getKind == ``qedProj then
    (extractDottedChain? (u.getArg 0)).map (· ++ [(u.getArg 2).getId.eraseMacroScopes.toString])
  else none

private partial def stxMentionsVar (v : String) (stx : Lean.Syntax) : Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    match (stx.getArg 0).getId.eraseMacroScopes.components with
    | root :: _ => root.toString == v
    | []        => false
  else if k == ``qedLam1 then
    let b := if (stx.getArg 0).isIdent then (stx.getArg 0).getId.eraseMacroScopes.toString else ""
    if b == v then false else stxMentionsVar v (stx.getArg 2)
  else
    stx.getArgs.any (stxMentionsVar v)

private partial def stxCollectRowCols (rowVar : String) (colNames : Array String) (stx : Lean.Syntax) :
    Array String :=
  match extractDottedChain? stx with
  | some [rv, col] => if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ =>
      stx.getArgs.foldl (init := #[]) fun acc child =>
        (stxCollectRowCols rowVar colNames child).foldl (init := acc) fun a c =>
          if a.contains c then a else a.push c

private partial def splitAndStx (stx : Lean.Syntax) : Array Lean.Syntax :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedAnd then splitAndStx (u.getArg 0) ++ splitAndStx (u.getArg 2) else #[u]

private abbrev mkSqlIdentT := mkSqlIdentTerm

private def sqlBinOpTable : Array (Lean.Name × Lean.Name) := #[
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub),
  (``qedMul, `Qed.Server.Db.SqlBinOp.mul), (``qedAnd, `Qed.Server.Db.SqlBinOp.and),
  (``qedOr,  `Qed.Server.Db.SqlBinOp.or)
]

private def sqlCmpOpTable : Array (String × Lean.Name) := #[
  ("==", `Qed.Server.Db.SqlBinOp.eq), ("!=", `Qed.Server.Db.SqlBinOp.ne),
  ("<",  `Qed.Server.Db.SqlBinOp.lt), ("<=", `Qed.Server.Db.SqlBinOp.le),
  (">",  `Qed.Server.Db.SqlBinOp.gt), (">=", `Qed.Server.Db.SqlBinOp.ge)
]

section QueryHelpers
open Lean Elab Command

private def lowerSqlMethodCall {M : Type → Type} [Monad M] [MonadQuotation M] [MonadError M]
    (ref : Syntax) (lowerVal : Syntax → M Term) (lowerSql : Syntax → M Term)
    (lhsE : Term) (meth : String) (argStx : Syntax) : M Term := do
  match meth with
  | "startsWith" => `(Qed.Server.Db.SqlExpr.startsWith $lhsE $(← lowerSql argStx))
  | "contains"   => `(Qed.Server.Db.SqlExpr.contains $lhsE $(← lowerSql argStx))
  | "endsWith"   => `(Qed.Server.Db.SqlExpr.like $lhsE (Qed.Server.Db.SqlExpr.param (Qed.Server.Db.endsWithLikeVal $(← lowerVal argStx))))
  | "like"       => `(Qed.Server.Db.SqlExpr.like $lhsE $(← lowerSql argStx))
  | _            => throwErrorAt ref s!"unsupported method `.{meth}` in SQL `where`/`set` clause"

private def lowerOptNatArg {M : Type → Type} [Monad M] [MonadQuotation M]
    (lowerVal : Syntax → M Term) : Option Syntax → M Term
  | none   => `(none)
  | some s => do `(some ($(← lowerVal s) : Nat))

private def mkDbProveTac {M : Type → Type} [Monad M] [MonadQuotation M]
    (unfolds : Array Ident) (kind op hint : String) : M Term :=
  `(by qedDbProve [$[$unfolds],*] $(Syntax.mkStrLit kind) $(Syntax.mkStrLit op) $(Syntax.mkStrLit hint))

private def findDbTable {M : Type → Type} [Monad M] [MonadError M]
    (ref : Syntax) (dbInfo : DatabaseInfo) (tblName : String) : M DbTableInfo := do
  let some tbl := dbInfo.tables.find? (·.tableName == tblName)
    | let hint := Qed.Diag.didYouMean tblName (dbInfo.tables.map (·.tableName)).toList
      throwErrorAt ref s!"database `{dbInfo.shortName}` has no table `{tblName}`{hint}"
  return tbl

private structure TableIdents where
  rowTyId      : Ident
  rowInvId     : Ident
  rowInvBId    : Ident
  rowInvSId    : Ident
  transInvId   : Ident
  readPolId    : Ident
  insPolId     : Ident
  updPolId     : Ident
  delPolId     : Ident
  decRowId     : Ident
  tblSqlId     : Term
  allColsListT : Term

private def mkTableIdents (stx : Syntax) (tbl : DbTableInfo) : CommandElabM TableIdents := do
  let tblSqlId ← mkSqlIdentTerm stx tbl.tableName
  let colSqlIds ← tbl.columns.mapM fun c => mkSqlIdentTerm stx c.name
  return {
    rowTyId := mkIdentFrom stx tbl.rowTypeConst
    rowInvId := mkIdentFrom stx tbl.rowInvConst
    rowInvBId := mkIdentFrom stx tbl.rowInvBoolConst
    rowInvSId := mkIdentFrom stx tbl.rowInvSoundConst
    transInvId := mkIdentFrom stx tbl.transInvConst
    readPolId := mkIdentFrom stx tbl.readPolicyConst
    insPolId := mkIdentFrom stx tbl.insertPolicyConst
    updPolId := mkIdentFrom stx tbl.updatePolicyConst
    delPolId := mkIdentFrom stx tbl.deletePolicyConst
    decRowId := mkIdentFrom stx tbl.decodeRowConst
    tblSqlId, allColsListT := ← `([$[$colSqlIds:term],*])
  }

private partial def lowerRowSqlExpr {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    [MonadQuotation M] [MonadError M]
    (lowerVal : Syntax → M Term)
    (tbl : DbTableInfo) (rowVar : String) (stx : Syntax) : M Term := do
  let colNames := tbl.columns.map (·.name)
  let u := unwrapParens1 stx
  let k := u.getKind
  -- If expression does not mention `rowVar` at all, bind it as a runtime SQL parameter!
  if !stxMentionsVar rowVar u then
    if k == ``qedIdent then
      let s := (u.getArg 0).getId.eraseMacroScopes.toString
      if s == "true" then return ← `(Qed.Server.Db.SqlExpr.litTrue)
      else if s == "false" then return ← `(Qed.Server.Db.SqlExpr.litFalse)
    return ← `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $(← lowerVal u)))
  -- Direct column projection `r.col` / `r.col.length`
  match extractDottedChain? u with
  | some [rv, col] =>
      if rv == rowVar then
        unless colNames.contains col do
          let hint := Qed.Diag.didYouMean col colNames.toList
          throwErrorAt u s!"table `{tbl.tableName}` has no column `{col}`{hint}"
        return ← `(Qed.Server.Db.SqlExpr.col $(← liftM (mkSqlIdentT u col)))
  | some [rv, col, "length"] =>
      if rv == rowVar && colNames.contains col then
        return ← `(Qed.Server.Db.SqlExpr.strLen (Qed.Server.Db.SqlExpr.col $(← liftM (mkSqlIdentT u col))))
  | _ => pure ()
  -- Compound expressions referencing `rowVar`
  let lowerSub := lowerRowSqlExpr lowerVal tbl rowVar
  if k == ``qedProj then
    let fld := (u.getArg 2).getId.eraseMacroScopes.toString
    if fld == "length" then `(Qed.Server.Db.SqlExpr.strLen $(← lowerSub (u.getArg 0)))
    else throwErrorAt u s!"unsupported row projection `.{fld}` inside SQL query expression"
  else if let some (_, opCtor) := sqlBinOpTable.find? (·.1 == k) then
    `(Qed.Server.Db.SqlExpr.binOp $(mkIdent opCtor) $(← lowerSub (u.getArg 0)) $(← lowerSub (u.getArg 2)))
  else if k == ``qedNot then
    `(Qed.Server.Db.SqlExpr.not $(← lowerSub (u.getArg 1)))
  else if k == ``qedCmp then
    let mut lhsStx := u.getArg 0
    let mut clauses : Array Term := #[]
    for lk in (u.getArg 1).getArgs do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := lk.getArg 1
      let isRhsNone := (unwrapParens1 rhsStx).getKind == ``qedIdent &&
        ((unwrapParens1 rhsStx).getArg 0).getId.eraseMacroScopes == `none
      let c ←
        if isRhsNone && (opStr == "==" || opStr == "!=") then
          let l ← lowerSub lhsStx
          if opStr == "==" then `(Qed.Server.Db.SqlExpr.isNull $l) else `(Qed.Server.Db.SqlExpr.isNotNull $l)
        else
          let some (_, opCtor) := sqlCmpOpTable.find? (·.1 == opStr)
            | throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}`"
          `(Qed.Server.Db.SqlExpr.binOp $(mkIdent opCtor) $(← lowerSub lhsStx) $(← lowerSub rhsStx))
      clauses := clauses.push c
      lhsStx := rhsStx
    match clauses.toList with
    | []        => `(Qed.Server.Db.SqlExpr.litTrue)
    | c :: rest => rest.foldlM (init := c) fun acc x => `(Qed.Server.Db.SqlExpr.binOp .and $acc $x)
  else if k == ``qedCall then
    if let some (recvStx, meth, rawArgs) := matchMethodCall? u then
      if rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos then
        let argStx := rawArgs[0]!.getArg 0
        if meth == "contains" && !stxMentionsVar rowVar recvStx && stxMentionsVar rowVar argStx then
          `(Qed.Server.Db.SqlExpr.inList $(← lowerSub argStx) (Qed.Server.Db.ToSqlList.toSqlList $(← lowerVal recvStx)))
        else if meth == "startsWith" || meth == "contains" || meth == "endsWith" || meth == "like" then
          lowerSqlMethodCall u lowerVal lowerSub (← lowerSub recvStx) meth argStx
        else
          throwErrorAt u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"
      else
        throwErrorAt u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"
    else
      throwErrorAt u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause"
  else
    throwErrorAt u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, arithmetic, `.length`, `.startsWith`, `.contains`, `xs.contains(r.col)`, or bound variables)"

private def parseWhereArg {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    [MonadQuotation M] [MonadError M]
    (lowerVal : Syntax → M Term) (lowerValWithLocal : String → Syntax → M Term)
    (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax) :
    M (Term × Term × Option (String × Syntax)) := do
  match whereStx? with
  | none =>
      return (← `(fun (_ : $rowTyId) => true), ← `(Qed.Server.Db.SqlExpr.litTrue), none)
  | some wRaw =>
      let u := unwrapParens1 wRaw
      if u.getKind != ``qedLam1 then
        throwErrorAt wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`"
      let binderStx := u.getArg 0
      let rId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_row
      let rName := rId.getId.eraseMacroScopes.toString
      let bodyStx := u.getArg 2
      let predT ← `(fun ($rId:ident : $rowTyId) => ($(← lowerValWithLocal rName bodyStx) : Bool))
      let sqlT  ← lowerRowSqlExpr lowerVal tbl rName bodyStx
      return (predT, sqlT, some (rName, bodyStx))

private def parseOrderByArg (tbl : DbTableInfo) (ordStx? : Option Syntax) : CommandElabM Term := do
  match ordStx? with
  | none => `(none)
  | some stx =>
      let u := unwrapParens1 stx
      if u.getKind != ``qedLitStr then
        throwErrorAt stx "`orderBy` must be a string column name (e.g. `orderBy = \"id\"` or `orderBy = \"-version\"`)"
      let raw := (⟨(u.getArg 0)⟩ : TSyntax `str).getString
      let (colName, isDesc) :=
        if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true) else (raw, false)
      let colNames := tbl.columns.map (·.name)
      unless colNames.contains colName do
        let hint := Qed.Diag.didYouMean colName colNames.toList
        throwErrorAt stx s!"`orderBy` references unknown column `{colName}` on table `{tbl.tableName}`{hint}"
      let dirT ← if isDesc then `(Qed.Server.Db.SqlOrderDir.desc) else `(Qed.Server.Db.SqlOrderDir.asc)
      `(some ($(← mkSqlIdentT stx colName), $dirT))

private def parseQueryWindow {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M] [MonadQuotation M]
    (tbl : DbTableInfo) (lowerVal : Syntax → M Term) (findNamed : String → Option Syntax) :
    M (Term × Term × Term) :=
  return (← liftM (parseOrderByArg tbl (findNamed "orderBy")),
          ← lowerOptNatArg lowerVal (findNamed "limit"),
          ← lowerOptNatArg lowerVal (findNamed "offset"))

private def parseAggColArg (tbl : DbTableInfo) (colStx : Syntax) : CommandElabM DbColumnInfo := do
  let u := unwrapParens1 colStx
  let errMsg := "aggregate column selector must be a column name string (e.g. `\"stock\"`) or `r => r.col`"
  let colName ←
    if u.getKind == ``qedLitStr then
      pure (⟨(u.getArg 0)⟩ : TSyntax `str).getString
    else if u.getKind == ``qedLam1 then
      let b := u.getArg 0
      let rName := if b.isIdent then b.getId.eraseMacroScopes.toString else ""
      match extractDottedChain? (u.getArg 2) with
      | some [rv, col] => if rv == rName then pure col else throwErrorAt colStx errMsg
      | _ => throwErrorAt colStx errMsg
    else throwErrorAt colStx errMsg
  let some colInfo := tbl.columns.find? (·.name == colName)
    | let hint := Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList
      throwErrorAt colStx s!"table `{tbl.tableName}` has no column `{colName}`{hint}"
  return colInfo

/-- Main lowering entrypoint invoked from `Qed.Server.Lower.lowerSrvCallHook` whenever a server
    function invokes `db.<table>.<op>(...)` or `db.ensureSchema()`.
    Returns `(loweredTerm, isWriteOp)`. -/
def lowerDbCall {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    [MonadQuotation M] [MonadError M]
    (lowerVal : Syntax → M Term) (lowerValWithLocal : String → Syntax → M Term)
    (fnName : String) (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String)
    (rawArgs : Array Syntax) (txIdTerm? : Option Term := none) :
    M (Term × Bool) := do
  let cfgId := mkIdentFrom stx dbInfo.configConst
  let txOptT : Term ← match txIdTerm? with
    | some tid => `(some $tid)
    | none     => `(none)
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then throwErrorAt stx "`ensureSchema()` takes no arguments"
      return (← `($(mkIdentFrom stx dbInfo.ensureSchemaConst)), true)
  | [_, tblName, opName] =>
      let tbl ← findDbTable stx dbInfo tblName
      let { rowTyId, rowInvId, rowInvBId, rowInvSId, transInvId, readPolId, insPolId, updPolId, delPolId,
            decRowId, tblSqlId, allColsListT } ← liftM (mkTableIdents stx tbl)
      let ctxId := mkIdent `ctx
      let (posArgs, namedArgs) ← splitCallArgs "database" rawArgs (allowWhere := true)
      let findNamed (k : String) : Option Syntax := (namedArgs.find? (·.1 == k)).map Prod.snd
      let whereArg? : Option Syntax :=
        (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => posArgs[0]?
      let opQual := s!"{fnName} → {dbInfo.shortName}.{tbl.tableName}.{opName}"
      let readPolKind := s!"read policy `{dbInfo.shortName}.{tbl.tableName}.read`"
      let mkReadPolHint (t : DbTableInfo) (clause := "`where = r => ...`") : String :=
        if t.readPolicyLabel.isEmpty then s!"Check {clause} against the table's `policy read`."
        else s!"Ensure {clause} (together with `requires` / `if` guards) implies `{t.readPolicyLabel}`."

      if opName == "select" || opName == "findOne" || opName == "count" then
        let (predT, sqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let pf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        if opName == "select" then
          let (ordT, limT, offT) ← parseQueryWindow tbl lowerVal findNamed
          let qT ← `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsListT $sqlWhereT $ordT $limT $offT)
          return (← `(Qed.Server.Db.dbSelect $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId $predT $readPolId $ctxId $pf $txOptT), false)
        else if opName == "findOne" then
          let ordT ← liftM (parseOrderByArg tbl (findNamed "orderBy"))
          let qT ← `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsListT $sqlWhereT $ordT (some 1) none)
          return (← `(Qed.Server.Db.dbFindOne $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId $predT $readPolId $ctxId $pf $txOptT), false)
        else
          let qT ← `(Qed.Server.Db.SqlQuery.count $tblSqlId $sqlWhereT)
          return (← `(Qed.Server.Db.dbCount $cfgId $qT $rowInvId $predT $readPolId $ctxId $pf $txOptT), false)

      else if opName == "sum" || opName == "min" || opName == "max" then
        let some colStx := (findNamed "col").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` requires a column selector (e.g. `\"{tbl.columns[0]?.map (·.name) |>.getD "col"}\"` or `col = \"...\"`)"
        let colInfo ← liftM (parseAggColArg tbl colStx)
        let aggWhereArg? := (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ =>
          if (findNamed "col").isSome then posArgs[0]? else posArgs[1]?
        let (predT, sqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId aggWhereArg?
        let pf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        let cSqlId ← liftM (mkSqlIdentT colStx colInfo.name)
        let aggOpT ← if opName == "sum" then `(Qed.Server.Db.SqlAggOp.sum)
          else if opName == "min" then `(Qed.Server.Db.SqlAggOp.min) else `(Qed.Server.Db.SqlAggOp.max)
        let qT ← `(Qed.Server.Db.SqlQuery.aggregate $aggOpT $tblSqlId $cSqlId $sqlWhereT)
        if opName == "sum" then
          let fnId := if colInfo.isNat then mkIdent `Qed.Server.Db.dbSumNat else mkIdent `Qed.Server.Db.dbSumInt
          return (← `($fnId $cfgId $qT $rowInvId $predT $readPolId $ctxId $pf $txOptT), false)
        else
          let projT ← `(fun (_r : $rowTyId) => _r.$(mkIdentFrom colStx (Name.mkSimple colInfo.name)))
          return (← `(Qed.Server.Db.dbAggOpt $cfgId $qT $projT $rowInvId $predT $readPolId $ctxId $pf $txOptT), false)

      else if opName == "join" then
        let some rightTblStx := (findNamed "table").orElse fun _ => (findNamed "with").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.join` requires a target table name (e.g. `join(\"books\", where = ...)` )"
        let uRt := unwrapParens1 rightTblStx
        let rightTblName ←
          if uRt.getKind == ``qedLitStr then pure (⟨(uRt.getArg 0)⟩ : TSyntax `str).getString
          else if uRt.getKind == ``qedIdent then pure (uRt.getArg 0).getId.eraseMacroScopes.toString
          else throwErrorAt rightTblStx "`join` target table must be a string table name (e.g. `\"books\"`)"
        let rightTbl ← findDbTable rightTblStx dbInfo rightTblName
        let onColFilter? : Option String ← match findNamed "on" with
          | none => pure none
          | some oStx =>
              let uo := unwrapParens1 oStx
              if uo.getKind == ``qedLitStr then pure (some (⟨(uo.getArg 0)⟩ : TSyntax `str).getString)
              else throwErrorAt oStx "`on` must be a string column name"
        -- Resolve FK relationship (`left.col references right(refCol)` or reverse `right.col references left(refCol)`)
        let fkMatch? : Option (String × String) :=
          (tbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) =>
            if rt == rightTbl.tableName && onColFilter?.all (· == c.name) then some (c.name, rc) else none).orElse fun _ =>
          rightTbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) =>
            if rt == tbl.tableName && onColFilter?.all (· == rc) then some (rc, c.name) else none
        let some (leftJoinCol, rightJoinCol) := fkMatch?
          | throwErrorAt stx s!"cannot `join` `{tbl.tableName}` with `{rightTbl.tableName}`: no `references` foreign key links these tables"
        let rt ← liftM (mkTableIdents stx rightTbl)
        let (lPredT, lSqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId (findNamed "where")
        let (rPredT, rSqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal rightTbl rt.rowTyId (findNamed "rightWhere")
        let (ordT, limT, offT) ← parseQueryWindow tbl lowerVal findNamed
        let qT ← `(Qed.Server.Db.SqlQuery.joinSelect $tblSqlId $(rt.tblSqlId) $allColsListT $(rt.allColsListT)
            $(← liftM (mkSqlIdentT stx leftJoinCol)) $(← liftM (mkSqlIdentT stx rightJoinCol))
            $lSqlWhereT $rSqlWhereT $ordT $limT $offT)
        let keyLT ← `(fun (_l : $rowTyId) => _l.$(mkIdentFrom stx (Name.mkSimple leftJoinCol)))
        let keyRT ← `(fun (_r : $(rt.rowTyId)) => _r.$(mkIdentFrom stx (Name.mkSimple rightJoinCol)))
        let lPf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        let rHint := if rightTbl.readPolicyLabel.isEmpty
          then "Check `rightWhere = r => ...` against the joined table's `policy read`."
          else mkReadPolHint rightTbl "`rightWhere = r => ...`"
        let rPf ← mkDbProveTac #[rt.rowInvId, rt.readPolId]
          s!"read policy `{dbInfo.shortName}.{rightTbl.tableName}.read` (joined table)" opQual rHint
        return (← `(Qed.Server.Db.dbJoinSelect $cfgId $qT $(Syntax.mkNumLit (toString tbl.columns.size))
            $decRowId $(rt.decRowId) $rowInvId $rowInvBId $rowInvSId
            $(rt.rowInvId) $(rt.rowInvBId) $(rt.rowInvSId)
            $lPredT $rPredT $keyLT $keyRT $readPolId $(rt.readPolId) $ctxId $lPf $rPf $txOptT), false)

      else if opName == "delete" then
        let (predT, sqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let hintMsg := if tbl.deletePolicyLabel.isEmpty
          then "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`."
          else s!"Ensure `where = r => ...` implies `{tbl.deletePolicyLabel}`."
        let pf ← mkDbProveTac #[rowInvId, delPolId] s!"delete policy `{dbInfo.shortName}.{tbl.tableName}.delete`" opQual hintMsg
        let qT ← `(Qed.Server.Db.SqlQuery.delete $tblSqlId $sqlWhereT [])
        return (← `(Qed.Server.Db.dbDelete $cfgId $qT $rowInvId $predT $delPolId $ctxId $pf $txOptT), true)

      else if opName == "insert" then
        let rowTerm : Term ←
          if posArgs.size == 1 && namedArgs.isEmpty then lowerVal posArgs[0]!
          else if posArgs.isEmpty && !namedArgs.isEmpty then
            let mut fieldIds : Array Ident := #[]
            let mut fieldVals : Array Term := #[]
            for col in tbl.columns do
              match findNamed col.name with
              | some vStx =>
                  fieldIds := fieldIds.push (mkIdentFrom stx (Name.mkSimple col.name))
                  fieldVals := fieldVals.push (← lowerVal vStx)
              | none =>
                  if col.isNullable then
                    fieldIds := fieldIds.push (mkIdentFrom stx (Name.mkSimple col.name))
                    fieldVals := fieldVals.push (← `(none))
                  else
                    throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.insert` is missing required column `{col.name}`"
            for (k, _) in namedArgs do
              unless tbl.columns.any (·.name == k) do
                let hint := Qed.Diag.didYouMean k (tbl.columns.map (·.name)).toList
                throwErrorAt stx s!"unknown column `{k}` in `{dbInfo.shortName}.{tbl.tableName}.insert`{hint}"
            `({ $[$fieldIds:ident := $fieldVals:term],* : $rowTyId })
          else
            throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.insert` expects named column arguments (`col = val, ...`) or a single `{dbInfo.shortName}.{tbl.tableName}` row value"
        let rowVar := mkIdent `_insRow
        let pairTs ← tbl.columns.mapM fun col => do
          let cId ← liftM (mkSqlIdentT stx col.name)
          `(($cId, Qed.Server.Db.ToSql.toSql (($rowVar).$(mkIdentFrom stx (Name.mkSimple col.name)))))
        let invPf ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual
          "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
        let polHint := if tbl.insertPolicyLabel.isEmpty
          then "Ensure inserted row satisfies the table's `policy insert` / `policy write`."
          else s!"Ensure inserted row satisfies `{tbl.insertPolicyLabel}`."
        let polPf ← mkDbProveTac #[insPolId] s!"insert policy `{dbInfo.shortName}.{tbl.tableName}.insert`" opQual polHint
        return (← `(let $rowVar:ident : $rowTyId := $rowTerm
          Qed.Server.Db.dbInsert $cfgId (Qed.Server.Db.SqlQuery.insert $tblSqlId [$[$pairTs:term],*] [])
            $rowVar $rowInvId $insPolId $ctxId $invPf $polPf $txOptT), true)

      else if opName == "update" || opName == "updateOne" then
        let some setRaw := findNamed "set"
          | let msg := "`" ++ dbInfo.shortName ++ "." ++ tbl.tableName ++ "." ++ opName ++ "` requires `set = r => { col = expr, ... }`"
            throwErrorAt stx "{msg}"
        let (predT, sqlWhereT, whereInfo?) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let uSet := unwrapParens1 setRaw
        let (setRowVar, recStx) : (Ident × Syntax) ←
          if uSet.getKind == ``qedLam1 then
            let b := uSet.getArg 0
            pure (if b.isIdent then ⟨b⟩ else mkIdent `_row, unwrapParens1 (uSet.getArg 2))
          else if uSet.getKind == ``qedRecLit then pure (mkIdent `_row, uSet)
          else
            let msg := "`set` must be `r => { col = expr, ... }` or `{ col = expr, ... }`"
            throwErrorAt setRaw "{msg}"
        if recStx.getKind != ``qedRecLit then
          let msg := "`set` body must be a record update `{ col = expr, ... }`"
          throwErrorAt recStx "{msg}"
        let setFields := (recStx.getArg 2).getSepArgs
        if setFields.isEmpty then throwErrorAt recStx "`set` must update at least one column"
        let setRowName := setRowVar.getId.eraseMacroScopes.toString
        let mut setColNames : Array String := #[]
        let mut leanFieldIds : Array Ident := #[]
        let mut leanFieldVals : Array Term := #[]
        let mut sqlSetPairs : Array Term := #[]
        let mut postChecks : Array Term := #[]
        let postRowVar := mkIdent `_postRow

        for sf in setFields do
          let colId : Ident := ⟨(sf.getArg 0)⟩
          let colName := colId.getId.eraseMacroScopes.toString
          let valStx := sf.getArg 2
          let some colInfo := tbl.columns.find? (·.name == colName)
            | let hint := Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList
              throwErrorAt colId s!"table `{tbl.tableName}` has no column `{colName}`{hint}"
          if colInfo.isImmutable then
            throwErrorAt colId s!"cannot update `immutable` column `{dbInfo.shortName}.{tbl.tableName}.{colName}` in `{fnName}`"
          setColNames := setColNames.push colName
          let leanV ← lowerValWithLocal setRowName valStx
          let sqlE ← lowerRowSqlExpr lowerVal tbl setRowName valStx
          let cSqlId ← liftM (mkSqlIdentT colId colName)
          let fId := mkIdentFrom colId (Name.mkSimple colName)
          leanFieldIds := leanFieldIds.push fId
          leanFieldVals := leanFieldVals.push leanV
          sqlSetPairs := sqlSetPairs.push (← `(($cSqlId, $sqlE)))
          -- If the updated value doesn't depend on old row `r`, zero-trust verify `newRow.col == val`!
          if !stxMentionsVar setRowName valStx then
            postChecks := postChecks.push (← `(($postRowVar.$fId == $(← lowerVal valStx))))

        -- Preserve `where` conjuncts that only reference columns NOT modified by `set`!
        if let some (wRowName, wBodyStx) := whereInfo? then
          let colNames := tbl.columns.map (·.name)
          for conj in splitAndStx wBodyStx do
            let touchedCols := stxCollectRowCols wRowName colNames conj
            if !touchedCols.isEmpty && touchedCols.all (!setColNames.contains ·) then
              let wRenamed ← lowerValWithLocal wRowName conj
              let wRowId := mkIdent (Name.mkSimple wRowName)
              postChecks := postChecks.push (← `((fun ($wRowId:ident : $rowTyId) => ($wRenamed : Bool)) $postRowVar))

        let postPredT : Term ← match postChecks.toList with
          | []        => `(fun (_ : $rowTyId) => true)
          | c :: rest => do
              let conj ← rest.foldlM (init := c) fun acc x => `($acc && $x)
              `(fun ($postRowVar:ident : $rowTyId) => $conj)

        let setFnT ← `(fun ($setRowVar:ident : $rowTyId) => { $setRowVar with $[$leanFieldIds:ident := $leanFieldVals:term],* })
        let qT ← `(Qed.Server.Db.SqlQuery.update $tblSqlId [$[$sqlSetPairs:term],*] $sqlWhereT $allColsListT)
        let polHint := if tbl.updatePolicyLabel.isEmpty
          then "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`."
          else s!"Ensure `where = r => ...` implies `{tbl.updatePolicyLabel}`."
        let polOldPf ← mkDbProveTac #[rowInvId, updPolId] s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual polHint
        let polNewPf ← mkDbProveTac #[rowInvId, updPolId] s!"post-update policy `{dbInfo.shortName}.{tbl.tableName}.update` (anti-hijack)" opQual polHint
        let invPf    ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual
          "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`."
        let transPf  ← mkDbProveTac #[rowInvId, transInvId] s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`" opQual
          "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants."
        let fnId := if opName == "updateOne" then mkIdent `Qed.Server.Db.dbUpdateOne else mkIdent `Qed.Server.Db.dbUpdate
        return (← `($fnId $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId $transInvId
            $predT $setFnT $postPredT $updPolId $ctxId $polOldPf $polNewPf $invPf $transPf $txOptT), true)

      else
        throwErrorAt stx s!"unknown database table method `{opName}` on `{dbInfo.shortName}.{tbl.tableName}` (expected `select`, `findOne`, `count`, `sum`, `min`, `max`, `join`, `insert`, `update`, `updateOne`, or `delete`)"
  | _ =>
      throwErrorAt stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`"

end QueryHelpers

end Qed.Server.Db
