import Lean
import Qed.Lang
import Qed.Diag
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime

namespace Qed.Server.Db
open Qed.Lang

/-! ## Dual Lean + Parameterized SQL Query Lowering for `server` `use db : <Database>` -/

private partial def stxCollectRowCols (rowVar : String) (colNames : Array String) (stx : Lean.Syntax) : Array String :=
  match extractDottedChain? stx with
  | some [rv, col] => if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ => stx.getArgs.foldl (init := #[]) fun acc ch => (stxCollectRowCols rowVar colNames ch).foldl pushUnique acc

private def sqlBinOps : Array (Lean.Name × Lean.Name) := #[
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub),
  (``qedMul, `Qed.Server.Db.SqlBinOp.mul), (``qedAnd, `Qed.Server.Db.SqlBinOp.and), (``qedOr, `Qed.Server.Db.SqlBinOp.or)]

section QueryHelpers
open Lean Elab Command
variable {M : Type → Type} [Monad M] [MonadQuotation M] [MonadError M]

private def mkDbProveTac (unfolds : Array Ident) (kind op hint : String) : M Term :=
  `(by qedDbProve [$[$unfolds],*] $(Syntax.mkStrLit kind) $(Syntax.mkStrLit op) $(Syntax.mkStrLit hint))

private def findDbTable (ref : Syntax) (dbInfo : DatabaseInfo) (tblName : String) : M DbTableInfo := do
  let some tbl := dbInfo.tables.find? (·.tableName == tblName)
    | throwErrorAt ref s!"database `{dbInfo.shortName}` has no table `{tblName}`{Qed.Diag.didYouMean tblName (dbInfo.tables.map (·.tableName)).toList}"
  return tbl

private def findDbCol (ref : Syntax) (tbl : DbTableInfo) (colName : String)
    (fmtErr : String → String → String := fun c t => s!"table `{t}` has no column `{c}`") : M DbColumnInfo := do
  let some colInfo := tbl.columns.find? (·.name == colName)
    | throwErrorAt ref s!"{fmtErr colName tbl.tableName}{Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList}"
  return colInfo

private def parseStrLitArg? (stx : Syntax) : Option String :=
  let u := unwrapParens1 stx; if u.getKind == ``qedLitStr then some (⟨u.getArg 0⟩ : TSyntax `str).getString else none

private def mkPolHint (label fallback pfx : String) : String := if label.isEmpty then fallback else s!"{pfx} `{label}`."

private def mkTblSqlParts (stx : Syntax) (tbl : DbTableInfo) : CommandElabM (Term × Term) := do
  let colSqlIds ← tbl.columns.mapM fun c => mkSqlIdentTerm stx c.name
  return (← mkSqlIdentTerm stx tbl.tableName, ← `([$[$colSqlIds:term],*]))

private def mkTblEncPairs (tbl : DbTableInfo) (mkKey : DbColumnInfo → Nat → Term) : CommandElabM (Array Term) := do
  let mut out : Array Term := #[]
  for (c, i) in tbl.columns.zipIdx do
    if let some (kEnv, fb?, isB) := c.encKey? then
      let sp ← mkEncColSpecTerm tbl.tableName c.name kEnv fb? isB
      out := out.push (← `(($(mkKey c i), $sp)))
  return out

private def mkTblEncRead (tbl : DbTableInfo) (colOffset : Nat := 0) : CommandElabM (Array Term) :=
  mkTblEncPairs tbl fun _ i => Syntax.mkNumLit (toString (colOffset + i))

private def mkTblEncWriteTerm (tbl : DbTableInfo) : CommandElabM Term := do
  let es ← mkTblEncPairs tbl fun c _ => Syntax.mkStrLit c.name; `([$[$es:term],*])

private def parseOrderByArg (tbl : DbTableInfo) (ordStx? : Option Syntax) : CommandElabM Term := do
  let some stx := ordStx? | return ← `(none)
  let some raw := parseStrLitArg? stx | throwErrorAt stx "`orderBy` must be a string column name (e.g. `orderBy = \"id\"` or `orderBy = \"-version\"`)"
  let (colName, isDesc) := if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true) else (raw, false)
  let colInfo ← findDbCol stx tbl colName (fun c t => s!"`orderBy` references unknown column `{c}` on table `{t}`")
  if colInfo.encKey?.isSome then throwErrorAt stx s!"cannot `orderBy` encrypted column `{tbl.tableName}.{colName}` (AES-256-GCM uses randomized nonces)"
  let dirT ← if isDesc then `(Qed.Server.Db.SqlOrderDir.desc) else `(Qed.Server.Db.SqlOrderDir.asc)
  `(some ($(← mkSqlIdentTerm stx colName), $dirT))

private def parseAggColArg (tbl : DbTableInfo) (colStx : Syntax) : CommandElabM DbColumnInfo := do
  let u := unwrapParens1 colStx; let errMsg := "aggregate column selector must be a column name string (e.g. `\"stock\"`) or `r => r.col`"
  let colName ←
    if let some s := parseStrLitArg? colStx then pure s
    else if u.getKind == ``qedLam1 then
      let b := u.getArg 0; let rName := if b.isIdent then b.getId.eraseMacroScopes.toString else ""
      match extractDottedChain? (u.getArg 2) with | some [rv, col] => if rv == rName then pure col else throwErrorAt colStx errMsg | _ => throwErrorAt colStx errMsg
    else throwErrorAt colStx errMsg
  let colInfo ← findDbCol colStx tbl colName
  if colInfo.encKey?.isSome then throwErrorAt colStx s!"cannot compute SQL aggregate on encrypted column `{tbl.tableName}.{colName}`"
  return colInfo

variable [MonadLiftT CommandElabM M]

private def isBoolLitStx (s : Syntax) : Bool :=
  let u := unwrapParens1 s
  u.getKind == ``qedIdent && ((u.getArg 0).getId.eraseMacroScopes == `true || (u.getArg 0).getId.eraseMacroScopes == `false)

private def extractDirectRowCol? (rowVar : String) (tbl : DbTableInfo) (s : Syntax) : Option String :=
  match extractDottedChain? (unwrapParens1 s) with
  | some [rv, col] => if rv == rowVar && tbl.columns.any (·.name == col) then some col else none
  | _ => none

@[noinline, nospecialize]
private partial def lowerRowSqlExpr (lowerVal : Syntax → M Term) (tbl : DbTableInfo) (rowVar : String) (stx : Syntax) : M Term := do
  let u := unwrapParens1 stx; let k := u.getKind
  if !stxMentionsVar rowVar u then
    if k == ``qedIdent then
      match (u.getArg 0).getId.eraseMacroScopes with
      | `true => return ← `(Qed.Server.Db.SqlExpr.litTrue) | `false => return ← `(Qed.Server.Db.SqlExpr.litFalse) | _ => pure ()
    return ← `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $(← lowerVal u)))
  let checkNotEnc (colInfo : DbColumnInfo) (col : String) : M Unit :=
    if colInfo.encKey?.isSome then
      throwErrorAt u s!"cannot reference encrypted column `{tbl.tableName}.{col}` inside SQL `where` or row-dependent `set` expression (AES-256-GCM uses randomized nonces)"
    else pure ()
  match extractDottedChain? u with
  | some [rv, col] =>
      if rv == rowVar then
        let colInfo ← findDbCol u tbl col; checkNotEnc colInfo col
        return ← `(Qed.Server.Db.SqlExpr.col $(← liftM (mkSqlIdentTerm u col)))
  | some [rv, col, "length"] =>
      if rv == rowVar then
        if let some colInfo := tbl.columns.find? (·.name == col) then
          checkNotEnc colInfo col
          return ← `(Qed.Server.Db.SqlExpr.strLen (Qed.Server.Db.SqlExpr.col $(← liftM (mkSqlIdentTerm u col))))
  | _ => pure ()
  let sub := lowerRowSqlExpr lowerVal tbl rowVar
  let lowerTypedParam (colName : String) (valStx : Syntax) : M Term := do
    if isBoolLitStx valStx then sub valStx
    else mkTypedSqlParamTerm (mkIdentFrom valStx tbl.rowTypeConst) (mkIdentFrom valStx (Name.mkSimple colName)) (← lowerVal valStx)
  if k == ``qedProj then
    let fld := (u.getArg 2).getId.eraseMacroScopes.toString
    if fld == "length" then `(Qed.Server.Db.SqlExpr.strLen $(← sub (u.getArg 0))) else throwErrorAt u s!"unsupported row projection `.{fld}` inside SQL query expression"
  else if let some (_, op) := sqlBinOps.find? (·.1 == k) then `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← sub (u.getArg 0)) $(← sub (u.getArg 2)))
  else if k == ``qedNot then `(Qed.Server.Db.SqlExpr.not $(← sub (u.getArg 1)))
  else if k == ``qedCmp then
    let mut lhs := u.getArg 0; let mut cs : Array Term := #[]
    for lk in (u.getArg 1).getArgs do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1
      let rhsNone := (unwrapParens1 rhs).getKind == ``qedIdent && ((unwrapParens1 rhs).getArg 0).getId.eraseMacroScopes == `none
      let c ← if rhsNone && (opStr == "==" || opStr == "!=") then
          let l ← sub lhs; if opStr == "==" then `(Qed.Server.Db.SqlExpr.isNull $l) else `(Qed.Server.Db.SqlExpr.isNotNull $l)
        else
          let some (_, op) := sqlCmpOps.find? (·.1 == opStr) | throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}`"
          let lowerSide (side other : Syntax) := match extractDirectRowCol? rowVar tbl other with
            | some col => if !stxMentionsVar rowVar side then lowerTypedParam col side else sub side
            | none => sub side
          `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← lowerSide lhs rhs) $(← lowerSide rhs lhs))
      cs := cs.push c; lhs := rhs
    match cs.toList with | [] => `(Qed.Server.Db.SqlExpr.litTrue) | c :: rs => rs.foldlM (init := c) fun a x => `(Qed.Server.Db.SqlExpr.binOp .and $a $x)
  else if k == ``qedCall then
    if let some (recv, meth, args) := matchMethodCall? u then
      if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
        let arg := args[0]!.getArg 0
        if meth == "contains" && !stxMentionsVar rowVar recv && stxMentionsVar rowVar arg then
          return ← `(Qed.Server.Db.SqlExpr.inList $(← sub arg) (Qed.Server.Db.ToSqlList.toSqlList $(← lowerVal recv)))
        match meth with
        | "startsWith" => return ← `(Qed.Server.Db.SqlExpr.startsWith $(← sub recv) $(← sub arg))
        | "contains"   => return ← `(Qed.Server.Db.SqlExpr.contains $(← sub recv) $(← sub arg))
        | "endsWith"   => return ← `(Qed.Server.Db.SqlExpr.like $(← sub recv) (Qed.Server.Db.SqlExpr.param (Qed.Server.Db.endsWithLikeVal $(← lowerVal arg))))
        | "like"       => return ← `(Qed.Server.Db.SqlExpr.like $(← sub recv) $(← sub arg))
        | _ => pure ()
    throwErrorAt u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"
  else throwErrorAt u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, arithmetic, `.length`, `.startsWith`, `.contains`, `xs.contains(r.col)`, or bound variables)"

private def parseWhereArg (lowerVal : Syntax → M Term) (lowerValWithLocal : String → Syntax → M Term)
    (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax) : M (Term × Term × Option (String × Syntax)) := do
  let some wRaw := whereStx? | return (← `(fun (_ : $rowTyId) => true), ← `(Qed.Server.Db.SqlExpr.litTrue), none)
  let u := unwrapParens1 wRaw
  if u.getKind != ``qedLam1 then throwErrorAt wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`"
  let b := u.getArg 0; let rId : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
  let rName := rId.getId.eraseMacroScopes.toString; let body := u.getArg 2
  return (← `(fun ($rId:ident : $rowTyId) => ($(← lowerValWithLocal rName body) : Bool)), ← lowerRowSqlExpr lowerVal tbl rName body, some (rName, body))

private def parseQueryWindow (tbl : DbTableInfo) (lowerVal : Syntax → M Term) (findNamed : String → Option Syntax) : M (Term × Term × Term) := do
  let optNat (s? : Option Syntax) : M Term := match s? with | none => `(none) | some s => do `(some ($(← lowerVal s) : Nat))
  return (← liftM (parseOrderByArg tbl (findNamed "orderBy")), ← optNat (findNamed "limit"), ← optNat (findNamed "offset"))

@[noinline, nospecialize]
def lowerDbCall (lowerVal : Syntax → M Term) (lowerValWithLocal : String → Syntax → M Term)
    (fnName : String) (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String)
    (rawArgs : Array Syntax) (txIdTerm? : Option Term := none) (wrapField : Term → M Term := pure) : M (Term × Bool) := do
  let cfgId := mkIdentFrom stx dbInfo.configConst
  let txOptT : Term ← match txIdTerm? with | some tid => `(some $tid) | none => `(none)
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then throwErrorAt stx "`ensureSchema()` takes no arguments"
      return (← `($(mkIdentFrom stx dbInfo.ensureSchemaConst)), true)
  | [_, tblName, opName] =>
      let tbl ← findDbTable stx dbInfo tblName
      let tid (t : DbTableInfo) (s : Name) := mkIdentFrom stx (t.rowTypeConst ++ s)
      let (rowTyId, rowInvId, readPolId, ctxId) := (mkIdentFrom stx tbl.rowTypeConst, tid tbl `RowInv, tid tbl `ReadPolicy, mkIdent `ctx)
      let (tblSqlId, allColsT) ← liftM (mkTblSqlParts stx tbl)
      let mkEncReadT : M Term := do let es ← liftM (mkTblEncRead tbl); `([$[$es:term],*])
      let (posArgs, namedArgs) ← splitCallArgs "database" rawArgs (allowWhere := true)
      let findNamed := findNamedArg? namedArgs
      let whereArg? := (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => posArgs[0]?
      let opQual := s!"{fnName} → {dbInfo.shortName}.{tbl.tableName}.{opName}"
      let readPolKind := s!"read policy `{dbInfo.shortName}.{tbl.tableName}.read`"
      let mkReadPolHint (t : DbTableInfo) (clause := "`where = r => ...`") (desc := "the table's") :=
        mkPolHint t.readPolicyLabel s!"Check {clause} against {desc} `policy read`." s!"Ensure {clause} (together with `requires` / `if` guards) implies"
      let mkPolCall (fn : Name) (qT predT polId pf : Term) : M Term := `($(mkIdent fn) $cfgId $qT $rowInvId $predT $polId $ctxId $pf $txOptT)

      if opName == "select" || opName == "findOne" || opName == "count" then
        let (predT, sqlW, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let pf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        if opName == "count" then return (← mkPolCall `Qed.Server.Db.dbCount (← `(Qed.Server.Db.SqlQuery.count $tblSqlId $sqlW)) predT readPolId pf, false)
        let (ordT, limT, offT, fn) ← if opName == "select" then let (o, l, f) ← parseQueryWindow tbl lowerVal findNamed; pure (o, l, f, `Qed.Server.Db.dbSelect)
          else pure (← liftM (parseOrderByArg tbl (findNamed "orderBy")), ← `(some 1), ← `(none), `Qed.Server.Db.dbFindOne)
        let qT ← `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsT $sqlW $ordT $limT $offT)
        return (← `($(mkIdent fn) $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $predT $readPolId $ctxId $pf $txOptT $(← mkEncReadT)), false)

      else if opName == "sum" || opName == "min" || opName == "max" then
        let some colStx := (findNamed "col").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` requires a column selector (e.g. `\"{tbl.columns[0]?.map (·.name) |>.getD "col"}\"` or `col = \"...\"`)"
        let colInfo ← liftM (parseAggColArg tbl colStx)
        let (predT, sqlW, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId ((findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => if (findNamed "col").isSome then posArgs[0]? else posArgs[1]?)
        let pf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        let aggOp := mkIdent <| match opName with | "sum" => `Qed.Server.Db.SqlAggOp.sum | "min" => `Qed.Server.Db.SqlAggOp.min | _ => `Qed.Server.Db.SqlAggOp.max
        let qT ← `(Qed.Server.Db.SqlQuery.aggregate $aggOp $tblSqlId $(← liftM (mkSqlIdentTerm colStx colInfo.name)) $sqlW)
        if opName == "sum" then return (← mkPolCall (if colInfo.isNat then `Qed.Server.Db.dbSumNat else `Qed.Server.Db.dbSumInt) qT predT readPolId pf, false)
        return (← `(Qed.Server.Db.dbAggOpt $cfgId $qT (fun (_r : $rowTyId) => _r.$(mkIdentFrom colStx (Name.mkSimple colInfo.name))) $rowInvId $predT $readPolId $ctxId $pf $txOptT), false)

      else if opName == "join" then
        let some rStx := (findNamed "table").orElse fun _ => (findNamed "with").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.join` requires a target table name (e.g. `join(\"books\", where = ...)` )"
        let uRt := unwrapParens1 rStx
        let rName ← if let some s := parseStrLitArg? rStx then pure s else if uRt.getKind == ``qedIdent then pure (uRt.getArg 0).getId.eraseMacroScopes.toString else throwErrorAt rStx "`join` target table must be a string table name (e.g. `\"books\"`)"
        let rightTbl ← findDbTable rStx dbInfo rName
        let onCol? ← (findNamed "on").mapM fun o => match parseStrLitArg? o with | some s => pure s | none => throwErrorAt o "`on` must be a string column name"
        let some (lCol, rCol) := (tbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) => if rt == rightTbl.tableName && onCol?.all (· == c.name) then some (c.name, rc) else none).orElse fun _ =>
            rightTbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) => if rt == tbl.tableName && onCol?.all (· == rc) then some (rc, c.name) else none
          | throwErrorAt stx s!"cannot `join` `{tbl.tableName}` with `{rightTbl.tableName}`: no `references` foreign key links these tables"
        let rRowTyId := mkIdentFrom stx rightTbl.rowTypeConst; let (rTblSqlId, rAllColsT) ← liftM (mkTblSqlParts stx rightTbl)
        let (lPredT, lSqlW, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId (findNamed "where")
        let (rPredT, rSqlW, _) ← parseWhereArg lowerVal lowerValWithLocal rightTbl rRowTyId (findNamed "rightWhere")
        let (ordT, limT, offT) ← parseQueryWindow tbl lowerVal findNamed
        let qT ← `(Qed.Server.Db.SqlQuery.joinSelect $tblSqlId $rTblSqlId $allColsT $rAllColsT $(← liftM (mkSqlIdentTerm stx lCol)) $(← liftM (mkSqlIdentTerm stx rCol)) $lSqlW $rSqlW $ordT $limT $offT)
        let lPf ← mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        let rPf ← mkDbProveTac #[tid rightTbl `RowInv, tid rightTbl `ReadPolicy] s!"read policy `{dbInfo.shortName}.{rightTbl.tableName}.read` (joined table)" opQual (mkReadPolHint rightTbl "`rightWhere = r => ...`" "the joined table's")
        let joinEncElems := (← liftM (mkTblEncRead tbl)) ++ (← liftM (mkTblEncRead rightTbl tbl.columns.size))
        let joinEncReadT : Term ← `([$[$joinEncElems:term],*])
        return (← `(Qed.Server.Db.dbJoinSelect $cfgId $qT $(Syntax.mkNumLit (toString tbl.columns.size))
            $(tid tbl `decodeRow) $(tid rightTbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound)
            $(tid rightTbl `RowInv) $(tid rightTbl `rowInvBool) $(tid rightTbl `rowInvBool_sound)
            $lPredT $rPredT (fun (_l : $rowTyId) => _l.$(mkIdentFrom stx (Name.mkSimple lCol))) (fun (_r : $rRowTyId) => _r.$(mkIdentFrom stx (Name.mkSimple rCol)))
            $readPolId $(tid rightTbl `ReadPolicy) $ctxId $lPf $rPf $txOptT $joinEncReadT), false)

      else if opName == "delete" then
        let (predT, sqlW, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let delPolId := tid tbl `DeletePolicy
        let pf ← mkDbProveTac #[rowInvId, delPolId] s!"delete policy `{dbInfo.shortName}.{tbl.tableName}.delete`" opQual
          (mkPolHint tbl.deletePolicyLabel "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`." "Ensure `where = r => ...` implies")
        return (← mkPolCall `Qed.Server.Db.dbDelete (← `(Qed.Server.Db.SqlQuery.delete $tblSqlId $sqlW [])) predT delPolId pf, true)

      else if opName == "insert" || opName == "upsert" then
        let hasColNamed (nm : String) := tbl.columns.any (·.name == nm)
        let isConflictWhere (s : Syntax) := (unwrapParens1 s).getKind == ``qedLam1 || !hasColNamed "where"
        let onArg? := if opName == "upsert" then
            (findNamed "conflict").orElse fun _ => if !hasColNamed "on" then findNamed "on" else none
          else none
        let conflictWhereStx? := if opName == "upsert" then (findNamed "where").filter isConflictWhere else none
        let rowNamedArgs := if opName == "upsert" then
            namedArgs.filter fun (k, s) => !(k == "conflict" || (k == "on" && !hasColNamed "on") || (k == "where" && isConflictWhere s))
          else namedArgs
        let rowTerm ← if posArgs.size == 1 && rowNamedArgs.isEmpty then lowerVal posArgs[0]!
          else if posArgs.isEmpty && !rowNamedArgs.isEmpty then
            for (k, _) in rowNamedArgs do let _ ← findDbCol stx tbl k (fun c t => s!"unknown column `{c}` in `{dbInfo.shortName}.{t}.{opName}`")
            let findRowNamed := findNamedArg? rowNamedArgs
            let (fIds, fVals) := (← tbl.columns.mapM fun col => do
              let fId := mkIdentFrom stx (Name.mkSimple col.name)
              match findRowNamed col.name with
              | some v => return (fId, ← wrapField (← lowerVal v))
              | none => if col.isNullable then return (fId, ← `(none)) else throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` is missing required column `{col.name}`").unzip
            `({ $[$fIds:ident := $fVals:term],* : $rowTyId })
          else throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` expects named column arguments (`col = val, ...`) or a single `{dbInfo.shortName}.{tbl.tableName}` row value"
        let (rowVar, insPolId) := (mkIdent `_insRow, tid tbl `InsertPolicy)
        let pairTs ← tbl.columns.mapM fun col => do `(($(← liftM (mkSqlIdentTerm stx col.name)), Qed.Server.Db.ToSql.toSql (($rowVar).$(mkIdentFrom stx (Name.mkSimple col.name)))))
        let invPf ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
        let insPolPf ← mkDbProveTac #[insPolId] s!"insert policy `{dbInfo.shortName}.{tbl.tableName}.insert`" opQual (mkPolHint tbl.insertPolicyLabel "Ensure inserted row satisfies the table's `policy insert` / `policy write`." "Ensure inserted row satisfies")
        if opName == "insert" then
          return (← `(let $rowVar:ident : $rowTyId := $rowTerm; Qed.Server.Db.dbInsert $cfgId (Qed.Server.Db.SqlQuery.insert $tblSqlId [$[$pairTs:term],*] []) $rowVar $rowInvId $insPolId $ctxId $invPf $insPolPf $txOptT $(← liftM (mkTblEncWriteTerm tbl))), true)
        else
          let conflictCols : Array DbColumnInfo ← match onArg? with
            | some oStx =>
                let rawNames : Array (Syntax × String) ←
                  if let some cName := parseStrLitArg? oStx then pure #[(oStx, cName)]
                  else
                    let uo := unwrapParens1 oStx
                    if uo.getKind == ``qedArrLit then
                      let elems := (uo.getArg 1).getSepArgs
                      if elems.isEmpty then throwErrorAt oStx "`upsert` conflict target `on`/`conflict` cannot be empty"
                      elems.mapM fun el => do
                        let some cn := parseStrLitArg? el | throwErrorAt el "`upsert` conflict target `on`/`conflict` elements must be column name strings (e.g. `on = [\"orgId\", \"slug\"]`)"
                        pure (el, cn)
                    else throwErrorAt oStx "`upsert` conflict target `on`/`conflict` must be a column name string or list of column name strings (e.g. `on = \"id\"` or `on = [\"a\", \"b\"]`)"
                let cis ← rawNames.mapM fun (ref, cn) => findDbCol ref tbl cn
                if cis.size == 1 then
                  unless cis[0]!.isPrimaryKey || cis[0]!.isUnique do
                    throwErrorAt rawNames[0]!.1 s!"`upsert` conflict column `{tbl.tableName}.{cis[0]!.name}` must be `primary_key` or `unique`"
                pure cis
            | none =>
                let some pkCol := tbl.columns.find? (·.isPrimaryKey) | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.upsert` requires a `primary_key` column or explicit `on = \"<unique_col>\"`"
                pure #[pkCol]
          for cc in conflictCols do
            if cc.encKey?.isSome then throwErrorAt stx s!"cannot `upsert` on encrypted column `{tbl.tableName}.{cc.name}`"
          let conflictNames := conflictCols.map (·.name)
          let conflictColTs ← conflictCols.mapM fun cc => liftM (mkSqlIdentTerm stx cc.name)
          let updCols := tbl.columns.filter fun c => !c.isPrimaryKey && !c.isImmutable && !conflictNames.contains c.name
          let updColTs ← updCols.mapM fun c => liftM (mkSqlIdentTerm stx c.name)
          let (conflictPredT, conflictSqlW, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId conflictWhereStx?
          let conflictSqlOptT ← if conflictWhereStx?.isSome then `(some $conflictSqlW) else `(none)
          let (updPolId, transInvId) := (tid tbl `UpdatePolicy, tid tbl `TransInv)
          let updHint := mkPolHint tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
          let updPolNewPf ← mkDbProveTac #[updPolId] s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual updHint
          let updPolOldPf ← mkDbProveTac #[rowInvId, updPolId] s!"upsert conflict update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual updHint
          let transPf ← mkDbProveTac #[rowInvId, transInvId] s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`" opQual "Ensure the upserted row satisfies all `old(...)` and `transition` invariants against any conflicting row."
          return (← `(let $rowVar:ident : $rowTyId := $rowTerm; Qed.Server.Db.dbUpsert $cfgId
              (Qed.Server.Db.SqlQuery.upsert $tblSqlId [$[$pairTs:term],*] [$[$conflictColTs:term],*] [$[$updColTs:term],*] $conflictSqlOptT $allColsT)
              $rowVar $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $transInvId $conflictPredT
              $insPolId $updPolId $ctxId $invPf $insPolPf $updPolNewPf $updPolOldPf $transPf $txOptT $(← liftM (mkTblEncWriteTerm tbl)) $(← mkEncReadT)), true)

      else if opName == "update" || opName == "updateOne" then
        let some setRaw := findNamed "set" | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` requires `set = r => \{ col = expr, ... }`"
        let (predT, sqlW, whereInfo?) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let uSet := unwrapParens1 setRaw
        let (setRowVar, recStx) : Ident × Syntax ←
          if uSet.getKind == ``qedLam1 then let b := uSet.getArg 0; pure (if b.isIdent then ⟨b⟩ else mkIdent `_row, unwrapParens1 (uSet.getArg 2))
          else if uSet.getKind == ``qedRecLit then pure (mkIdent `_row, uSet)
          else throwErrorAt setRaw "`set` must be `r => \{ col = expr, ... }` or `\{ col = expr, ... }`"
        if recStx.getKind != ``qedRecLit then throwErrorAt recStx "`set` body must be a record update `\{ col = expr, ... }`"
        let setFields := (recStx.getArg 2).getSepArgs
        if setFields.isEmpty then throwErrorAt recStx "`set` must update at least one column"
        let (setRowName, postRowVar) := (setRowVar.getId.eraseMacroScopes.toString, mkIdent `_postRow)
        let mut setColNames : Array String := #[]; let mut leanFIds : Array Ident := #[]; let mut leanFVals : Array Term := #[]
        let mut sqlSetPairs : Array Term := #[]; let mut postChecks : Array Term := #[]
        for sf in setFields do
          let colId : Ident := ⟨sf.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString; let valStx := sf.getArg 2
          let colInfo ← findDbCol colId tbl colName
          if colInfo.isImmutable then throwErrorAt colId s!"cannot update `immutable` column `{dbInfo.shortName}.{tbl.tableName}.{colName}` in `{fnName}`"
          if colInfo.encKey?.isSome && stxMentionsVar setRowName valStx then
            throwErrorAt valStx s!"cannot update encrypted column `{dbInfo.shortName}.{tbl.tableName}.{colName}` using a row-dependent SQL expression"
          setColNames := setColNames.push colName; let fId := mkIdentFrom colId (Name.mkSimple colName)
          leanFIds := leanFIds.push fId; leanFVals := leanFVals.push (← wrapField (← lowerValWithLocal setRowName valStx))
          let sqlValT ← if !stxMentionsVar setRowName valStx && !isBoolLitStx valStx then
              mkTypedSqlParamTerm rowTyId fId (← wrapField (← lowerVal valStx))
            else lowerRowSqlExpr lowerVal tbl setRowName valStx
          sqlSetPairs := sqlSetPairs.push (← `(($(← liftM (mkSqlIdentTerm colId colName)), $sqlValT)))
          if !stxMentionsVar setRowName valStx then postChecks := postChecks.push (← `(($postRowVar.$fId == $(← wrapField (← lowerVal valStx)))))
        if let some (wRowName, wBody) := whereInfo? then
          let colNames := tbl.columns.map (·.name)
          for conj in splitAndStx wBody do
            let touched := stxCollectRowCols wRowName colNames conj
            if !touched.isEmpty && touched.all (!setColNames.contains ·) then
              postChecks := postChecks.push (← `((fun ($(mkIdent (Name.mkSimple wRowName)):ident : $rowTyId) => ($(← lowerValWithLocal wRowName conj) : Bool)) $postRowVar))
        let postPredT ← `(fun ($postRowVar:ident : $rowTyId) => $(← mkBoolConj postChecks))
        let setFnT ← `(fun ($setRowVar:ident : $rowTyId) => { $setRowVar with $[$leanFIds:ident := $leanFVals:term],* })
        let qT ← `(Qed.Server.Db.SqlQuery.update $tblSqlId [$[$sqlSetPairs:term],*] $sqlW $allColsT)
        let (updPolId, transInvId) := (tid tbl `UpdatePolicy, tid tbl `TransInv)
        let polHint := mkPolHint tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
        let polOldPf ← mkDbProveTac #[rowInvId, updPolId] s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual polHint
        let polNewPf ← mkDbProveTac #[rowInvId, updPolId] s!"post-update policy `{dbInfo.shortName}.{tbl.tableName}.update` (anti-hijack)" opQual polHint
        let invPf ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`."
        let transPf ← mkDbProveTac #[rowInvId, transInvId] s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`" opQual "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants."
        return (← `($(mkIdent (if opName == "updateOne" then `Qed.Server.Db.dbUpdateOne else `Qed.Server.Db.dbUpdate))
            $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $transInvId
            $predT $setFnT $postPredT $updPolId $ctxId $polOldPf $polNewPf $invPf $transPf $txOptT $(← liftM (mkTblEncWriteTerm tbl)) $(← mkEncReadT)), true)

      else throwErrorAt stx s!"unknown database table method `{opName}` on `{dbInfo.shortName}.{tbl.tableName}` (expected `select`, `findOne`, `count`, `sum`, `min`, `max`, `join`, `insert`, `upsert`, `update`, `updateOne`, or `delete`)"
  | _ => throwErrorAt stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`"

end QueryHelpers
end Qed.Server.Db
