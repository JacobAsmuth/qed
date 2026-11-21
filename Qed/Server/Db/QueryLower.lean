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
    match extractDottedChain? (u.getArg 0) with
    | some pre => some (pre ++ [(u.getArg 2).getId.eraseMacroScopes.toString])
    | none     => none
  else
    none

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
  | some [rv, col] =>
      if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ =>
      stx.getArgs.foldl (init := #[]) fun acc child =>
        let sub := stxCollectRowCols rowVar colNames child
        sub.foldl (init := acc) fun a c => if a.contains c then a else a.push c

private partial def splitAndStx (stx : Lean.Syntax) : Array Lean.Syntax :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedAnd then splitAndStx (u.getArg 0) ++ splitAndStx (u.getArg 2)
  else #[u]

open Lean Elab Command in
private def mkSqlIdentT (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}`"
  let lit := Syntax.mkStrLit raw
  `(Qed.Server.Db.SqlIdent.mk $lit (by decide))

open Lean Elab Command in
private partial def lowerRowSqlExpr {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    (lowerVal : Syntax → M Term)
    (tbl : DbTableInfo) (rowVar : String) (stx : Syntax) : M Term := do
  let colNames := tbl.columns.map (·.name)
  let u := unwrapParens1 stx
  let k := u.getKind
  -- If expression does not mention `rowVar` at all, bind it as a runtime SQL parameter!
  if !stxMentionsVar rowVar u then
    if k == ``qedIdent then
      let s := (u.getArg 0).getId.eraseMacroScopes.toString
      if s == "true" then return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.litTrue))
      else if s == "false" then return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.litFalse))
    let vTerm ← lowerVal u
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $vTerm)))
  -- Direct column projection `r.col`
  match extractDottedChain? u with
  | some [rv, col] =>
      if rv == rowVar then
        unless colNames.contains col do
          let hint := Qed.Diag.didYouMean col colNames.toList
          liftM (show CommandElabM Unit from
            throwErrorAt u s!"table `{tbl.tableName}` has no column `{col}`{hint}")
        let cId ← liftM (mkSqlIdentT u col)
        return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.col $cId))
  | some [rv, col, "length"] =>
      if rv == rowVar && colNames.contains col then
        let cId ← liftM (mkSqlIdentT u col)
        return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.strLen (Qed.Server.Db.SqlExpr.col $cId)))
  | _ => pure ()
  -- Compound expressions referencing `rowVar`
  if k == ``qedProj then
    let fld := (u.getArg 2).getId.eraseMacroScopes.toString
    if fld == "length" then
      let inner ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
      return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.strLen $inner))
    else
      liftM (show CommandElabM Term from
        throwErrorAt u s!"unsupported row projection `.{fld}` inside SQL query expression")
  else if k == ``qedAdd then
    let l ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
    let r ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 2)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .add $l $r))
  else if k == ``qedSub then
    let l ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
    let r ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 2)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .sub $l $r))
  else if k == ``qedMul then
    let l ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
    let r ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 2)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .mul $l $r))
  else if k == ``qedNot then
    let inner ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 1)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.not $inner))
  else if k == ``qedAnd then
    let l ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
    let r ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 2)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .and $l $r))
  else if k == ``qedOr then
    let l ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 0)
    let r ← lowerRowSqlExpr lowerVal tbl rowVar (u.getArg 2)
    return ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .or $l $r))
  else if k == ``qedCmp then
    let links := (u.getArg 1).getArgs
    let mut lhsStx := u.getArg 0
    let mut clauses : Array Term := #[]
    for lk in links do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := lk.getArg 1
      let isRhsNone := (unwrapParens1 rhsStx).getKind == ``qedIdent &&
        ((unwrapParens1 rhsStx).getArg 0).getId.eraseMacroScopes == `none
      let c ←
        if isRhsNone && (opStr == "==" || opStr == "!=") then
          let l ← lowerRowSqlExpr lowerVal tbl rowVar lhsStx
          if opStr == "==" then
            liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.isNull $l))
          else
            liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.isNotNull $l))
        else
          let l ← lowerRowSqlExpr lowerVal tbl rowVar lhsStx
          let r ← lowerRowSqlExpr lowerVal tbl rowVar rhsStx
          let opT ← match opStr with
            | "==" => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.eq))
            | "!=" => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.ne))
            | "<"  => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.lt))
            | "<=" => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.le))
            | ">"  => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.gt))
            | ">=" => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlBinOp.ge))
            | _    => liftM (show CommandElabM Term from
                throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}`")
          liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp $opT $l $r))
      clauses := clauses.push c
      lhsStx := rhsStx
    match clauses.toList with
    | [] => liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.litTrue))
    | c :: rest =>
        rest.foldlM (init := c) fun acc x =>
          liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.binOp .and $acc $x))
  else
    let sn := stxSnippet u
    liftM (show CommandElabM Term from
      throwErrorAt u s!"unsupported expression `{sn}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, arithmetic, `.length`, or bound variables)")

open Lean Elab Command in
private def parseWhereArg {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    (lowerVal : Syntax → M Term)
    (lowerValWithLocal : String → Syntax → M Term)
    (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax) :
    M (Term × Term × Option (String × Syntax)) := do
  match whereStx? with
  | none =>
      let predT ← liftM (show CommandElabM Term from `(fun (_ : $rowTyId) => true))
      let sqlT  ← liftM (show CommandElabM Term from `(Qed.Server.Db.SqlExpr.litTrue))
      return (predT, sqlT, none)
  | some wRaw =>
      let u := unwrapParens1 wRaw
      if u.getKind != ``qedLam1 then
        liftM (show CommandElabM Unit from
          throwErrorAt wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`")
      let binderStx := u.getArg 0
      let rId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_row
      let rName := rId.getId.eraseMacroScopes.toString
      let bodyStx := u.getArg 2
      let leanBody ← lowerValWithLocal rName bodyStx
      let predT ← liftM (show CommandElabM Term from `(fun ($rId:ident : $rowTyId) => ($leanBody : Bool)))
      let sqlT  ← lowerRowSqlExpr lowerVal tbl rName bodyStx
      return (predT, sqlT, some (rName, bodyStx))

open Lean Elab Command in
private def extractCallArgs (rawArgs : Array Syntax) :
    CommandElabM (Array Syntax × Array (String × Syntax)) := do
  let mut pos : Array Syntax := #[]
  let mut named : Array (String × Syntax) := #[]
  for a in rawArgs do
    let k := a.getKind
    if k == ``qedCallArgPos then
      pos := pos.push (a.getArg 0)
    else if k == ``qedCallArgWhere then
      named := named.push ("where", a.getArg 2)
    else if k == ``qedCallArgNamed then
      let nm := (a.getArg 0).getId.eraseMacroScopes.toString
      named := named.push (nm, a.getArg 2)
    else
      throwErrorAt a "unexpected argument in database call"
  return (pos, named)

open Lean Elab Command in
private def parseOrderByArg (tbl : DbTableInfo) (ordStx? : Option Syntax) : CommandElabM Term := do
  match ordStx? with
  | none => `(none)
  | some stx =>
      let u := unwrapParens1 stx
      if u.getKind != ``qedLitStr then
        throwErrorAt stx "`order_by` must be a string column name (e.g. `order_by = \"id\"` or `order_by = \"-version\"`)"
      let raw := (⟨(u.getArg 0)⟩ : TSyntax `str).getString
      let (colName, isDesc) :=
        if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true)
        else (raw, false)
      let colNames := tbl.columns.map (·.name)
      unless colNames.contains colName do
        let hint := Qed.Diag.didYouMean colName colNames.toList
        throwErrorAt stx s!"`order_by` references unknown column `{colName}` on table `{tbl.tableName}`{hint}"
      let cId ← mkSqlIdentT stx colName
      let dirT ← if isDesc then `(Qed.Server.Db.SqlOrderDir.desc) else `(Qed.Server.Db.SqlOrderDir.asc)
      `(some ($cId, $dirT))

open Lean Elab Command in
/-- Main lowering entrypoint invoked from `Qed.Server.Lower.lowerSrvCallHook` whenever a server
    function invokes `db.<table>.<op>(...)` or `db.ensureSchema()`.
    Returns `(loweredTerm, isWriteOp)`. -/
def lowerDbCall {M : Type → Type} [Monad M] [MonadLiftT CommandElabM M]
    (lowerVal : Syntax → M Term)
    (lowerValWithLocal : String → Syntax → M Term)
    (fnName : String)
    (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String) (rawArgs : Array Syntax) :
    M (Term × Bool) := do
  let cfgId := mkIdentFrom stx dbInfo.configConst
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then
        liftM (show CommandElabM Unit from throwErrorAt stx "`ensureSchema()` takes no arguments")
      let ensureId := mkIdentFrom stx dbInfo.ensureSchemaConst
      return (← liftM (show CommandElabM Term from `($ensureId)), true)
  | [_, tblName, opName] =>
      let some tbl := dbInfo.tables.find? (·.tableName == tblName)
        | let avail := (dbInfo.tables.map (·.tableName)).toList
          let hint := Qed.Diag.didYouMean tblName avail
          liftM (show CommandElabM (Term × Bool) from
            throwErrorAt stx s!"database `{dbInfo.shortName}` has no table `{tblName}`{hint}")
      let rowTyId     := mkIdentFrom stx tbl.rowTypeConst
      let rowInvId    := mkIdentFrom stx tbl.rowInvConst
      let rowInvBId   := mkIdentFrom stx tbl.rowInvBoolConst
      let rowInvSId   := mkIdentFrom stx tbl.rowInvSoundConst
      let transInvId  := mkIdentFrom stx tbl.transInvConst
      let readPolId   := mkIdentFrom stx tbl.readPolicyConst
      let insPolId    := mkIdentFrom stx tbl.insertPolicyConst
      let updPolId    := mkIdentFrom stx tbl.updatePolicyConst
      let delPolId    := mkIdentFrom stx tbl.deletePolicyConst
      let decRowId    := mkIdentFrom stx tbl.decodeRowConst
      let tblSqlId    ← liftM (mkSqlIdentT stx tbl.tableName)
      let allColSqlIds ← liftM (tbl.columns.mapM fun c => mkSqlIdentT stx c.name)
      let allColsListT ← liftM (show CommandElabM Term from `([$[$allColSqlIds:term],*]))
      let ctxId := mkIdent `ctx
      let (posArgs, namedArgs) ← liftM (extractCallArgs rawArgs)
      let findNamed (k : String) : Option Syntax := (namedArgs.find? (·.1 == k)).map Prod.snd
      let whereArg? : Option Syntax :=
        (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => posArgs[0]?
      let opQual := s!"{fnName} → {dbInfo.shortName}.{tbl.tableName}.{opName}"

      if opName == "select" || opName == "findOne" || opName == "count" then
        let (predT, sqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let polKindLit := Syntax.mkStrLit s!"read policy `{dbInfo.shortName}.{tbl.tableName}.read`"
        let opLit := Syntax.mkStrLit opQual
        let hintMsg :=
          if tbl.readPolicyLabel.isEmpty then
            "Check the `where = r => ...` clause against the table's `policy read`."
          else
            s!"Ensure `where = r => ...` (together with `requires` / `if` guards) implies `{tbl.readPolicyLabel}`."
        let hintLit := Syntax.mkStrLit hintMsg
        if opName == "select" then
          let ordT ← liftM (parseOrderByArg tbl (findNamed "order_by"))
          let limT : Term ← match findNamed "limit" with
            | none => liftM (show CommandElabM Term from `(none))
            | some lStx =>
                let lv ← lowerVal lStx
                liftM (show CommandElabM Term from `(some ($lv : Nat)))
          let qT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsListT $sqlWhereT $ordT $limT))
          let callT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.dbSelect $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId
                $predT $readPolId $ctxId (by qedDbProve [$rowInvId, $readPolId] $polKindLit $opLit $hintLit)))
          return (callT, false)
        else if opName == "findOne" then
          let ordT ← liftM (parseOrderByArg tbl (findNamed "order_by"))
          let qT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsListT $sqlWhereT $ordT (some 1)))
          let callT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.dbFindOne $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId
                $predT $readPolId $ctxId (by qedDbProve [$rowInvId, $readPolId] $polKindLit $opLit $hintLit)))
          return (callT, false)
        else -- count
          let qT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.SqlQuery.count $tblSqlId $sqlWhereT))
          let callT ← liftM (show CommandElabM Term from
            `(Qed.Server.Db.dbCount $cfgId $qT $rowInvId $predT $readPolId $ctxId
                (by qedDbProve [$rowInvId, $readPolId] $polKindLit $opLit $hintLit)))
          return (callT, false)

      else if opName == "delete" then
        let (predT, sqlWhereT, _) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let polKindLit := Syntax.mkStrLit s!"delete policy `{dbInfo.shortName}.{tbl.tableName}.delete`"
        let opLit := Syntax.mkStrLit opQual
        let hintMsg :=
          if tbl.deletePolicyLabel.isEmpty then
            "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`."
          else
            s!"Ensure `where = r => ...` implies `{tbl.deletePolicyLabel}`."
        let hintLit := Syntax.mkStrLit hintMsg
        let qT ← liftM (show CommandElabM Term from
          `(Qed.Server.Db.SqlQuery.delete $tblSqlId $sqlWhereT []))
        let callT ← liftM (show CommandElabM Term from
          `(Qed.Server.Db.dbDelete $cfgId $qT $rowInvId $predT $delPolId $ctxId
              (by qedDbProve [$rowInvId, $delPolId] $polKindLit $opLit $hintLit)))
        return (callT, true)

      else if opName == "insert" then
        let rowTerm : Term ←
          if posArgs.size == 1 && namedArgs.isEmpty then
            lowerVal posArgs[0]!
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
                    fieldVals := fieldVals.push (← liftM (show CommandElabM Term from `(none)))
                  else
                    liftM (show CommandElabM Unit from
                      throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.insert` is missing required column `{col.name}`")
            for (k, _) in namedArgs do
              unless tbl.columns.any (·.name == k) do
                let hint := Qed.Diag.didYouMean k (tbl.columns.map (·.name)).toList
                liftM (show CommandElabM Unit from
                  throwErrorAt stx s!"unknown column `{k}` in `{dbInfo.shortName}.{tbl.tableName}.insert`{hint}")
            liftM (show CommandElabM Term from `({ $[$fieldIds:ident := $fieldVals:term],* : $rowTyId }))
          else
            liftM (show CommandElabM Term from
              throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.insert` expects named column arguments (`col = val, ...`) or a single `{dbInfo.shortName}.{tbl.tableName}` row value")
        let rowVar := mkIdent `_insRow
        let pairTs ← liftM <| tbl.columns.mapM fun col => do
          let cId ← mkSqlIdentT stx col.name
          let fId := mkIdentFrom stx (Name.mkSimple col.name)
          `(($cId, Qed.Server.Db.ToSql.toSql (($rowVar).$fId)))
        let invKindLit := Syntax.mkStrLit s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`"
        let polKindLit := Syntax.mkStrLit s!"insert policy `{dbInfo.shortName}.{tbl.tableName}.insert`"
        let opLit := Syntax.mkStrLit opQual
        let invHintLit := Syntax.mkStrLit "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
        let polHintLit := Syntax.mkStrLit (
          if tbl.insertPolicyLabel.isEmpty then "Ensure inserted row satisfies the table's `policy insert` / `policy write`."
          else s!"Ensure inserted row satisfies `{tbl.insertPolicyLabel}`.")
        let callT ← liftM (show CommandElabM Term from `(
          let $rowVar:ident : $rowTyId := $rowTerm
          Qed.Server.Db.dbInsert $cfgId
            (Qed.Server.Db.SqlQuery.insert $tblSqlId [$[$pairTs:term],*] [])
            $rowVar $rowInvId $insPolId $ctxId
            (by qedDbProve [$rowInvId] $invKindLit $opLit $invHintLit)
            (by qedDbProve [$insPolId] $polKindLit $opLit $polHintLit)))
        return (callT, true)

      else if opName == "update" || opName == "updateOne" then
        let some setRaw := findNamed "set"
          | let msg := "`" ++ dbInfo.shortName ++ "." ++ tbl.tableName ++ "." ++ opName ++ "` requires `set = r => { col = expr, ... }`"
            liftM (show CommandElabM (Term × Bool) from throwErrorAt stx "{msg}")
        let (predT, sqlWhereT, whereInfo?) ← parseWhereArg lowerVal lowerValWithLocal tbl rowTyId whereArg?
        let uSet := unwrapParens1 setRaw
        let (setRowVar, recStx) : (Ident × Syntax) ←
          if uSet.getKind == ``qedLam1 then
            let b := uSet.getArg 0
            let rId : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
            pure (rId, unwrapParens1 (uSet.getArg 2))
          else if uSet.getKind == ``qedRecLit then
            pure (mkIdent `_row, uSet)
          else
            let msg := "`set` must be `r => { col = expr, ... }` or `{ col = expr, ... }`"
            liftM (show CommandElabM (Ident × Syntax) from throwErrorAt setRaw "{msg}")
        if recStx.getKind != ``qedRecLit then
          let msg := "`set` body must be a record update `{ col = expr, ... }`"
          liftM (show CommandElabM Unit from throwErrorAt recStx "{msg}")
        let setFields := (recStx.getArg 2).getSepArgs
        if setFields.isEmpty then
          liftM (show CommandElabM Unit from
            throwErrorAt recStx "`set` must update at least one column")
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
              liftM (show CommandElabM Unit from
                throwErrorAt colId s!"table `{tbl.tableName}` has no column `{colName}`{hint}")
          if colInfo.isImmutable then
            liftM (show CommandElabM Unit from
              throwErrorAt colId s!"cannot update `immutable` column `{dbInfo.shortName}.{tbl.tableName}.{colName}` in `{fnName}`")
          setColNames := setColNames.push colName
          let leanV ← lowerValWithLocal setRowName valStx
          let sqlE ← lowerRowSqlExpr lowerVal tbl setRowName valStx
          let cSqlId ← liftM (mkSqlIdentT colId colName)
          leanFieldIds := leanFieldIds.push (mkIdentFrom colId (Name.mkSimple colName))
          leanFieldVals := leanFieldVals.push leanV
          sqlSetPairs := sqlSetPairs.push (← liftM (show CommandElabM Term from `(($cSqlId, $sqlE))))
          -- If the updated value doesn't depend on old row `r`, zero-trust verify `newRow.col == val`!
          if !stxMentionsVar setRowName valStx then
            let fId := mkIdentFrom colId (Name.mkSimple colName)
            let valNoRow ← lowerVal valStx
            postChecks := postChecks.push (← liftM (show CommandElabM Term from `(($postRowVar.$fId == $valNoRow))))

        -- Preserve `where` conjuncts that only reference columns NOT modified by `set`!
        if let some (wRowName, wBodyStx) := whereInfo? then
          let colNames := tbl.columns.map (·.name)
          for conj in splitAndStx wBodyStx do
            let touchedCols := stxCollectRowCols wRowName colNames conj
            if !touchedCols.isEmpty && touchedCols.all fun c => !setColNames.contains c then
              let wRenamed ← lowerValWithLocal wRowName conj
              let wRowId := mkIdent (Name.mkSimple wRowName)
              postChecks := postChecks.push (← liftM (show CommandElabM Term from
                `((fun ($wRowId:ident : $rowTyId) => ($wRenamed : Bool)) $postRowVar)))

        let postPredT : Term ← match postChecks.toList with
          | [] => liftM (show CommandElabM Term from `(fun (_ : $rowTyId) => true))
          | c :: rest => do
              let conj ← rest.foldlM (init := c) fun acc x =>
                liftM (show CommandElabM Term from `($acc && $x))
              liftM (show CommandElabM Term from `(fun ($postRowVar:ident : $rowTyId) => $conj))

        let setFnT ← liftM (show CommandElabM Term from
          `(fun ($setRowVar:ident : $rowTyId) => { $setRowVar with $[$leanFieldIds:ident := $leanFieldVals:term],* }))
        let qT ← liftM (show CommandElabM Term from
          `(Qed.Server.Db.SqlQuery.update $tblSqlId [$[$sqlSetPairs:term],*] $sqlWhereT $allColsListT))
        let opLit := Syntax.mkStrLit opQual
        let polOldLit := Syntax.mkStrLit s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`"
        let polNewLit := Syntax.mkStrLit s!"post-update policy `{dbInfo.shortName}.{tbl.tableName}.update` (anti-hijack)"
        let invLit    := Syntax.mkStrLit s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`"
        let transLit  := Syntax.mkStrLit s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`"
        let polHintLit := Syntax.mkStrLit (
          if tbl.updatePolicyLabel.isEmpty then "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`."
          else s!"Ensure `where = r => ...` implies `{tbl.updatePolicyLabel}`.")
        let invHintLit := Syntax.mkStrLit "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`."
        let transHintLit := Syntax.mkStrLit "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants."
        let fnId := if opName == "updateOne" then mkIdent `Qed.Server.Db.dbUpdateOne else mkIdent `Qed.Server.Db.dbUpdate
        let callT ← liftM (show CommandElabM Term from
          `($fnId $cfgId $qT $decRowId $rowInvId $rowInvBId $rowInvSId $transInvId
              $predT $setFnT $postPredT $updPolId $ctxId
              (by qedDbProve [$rowInvId, $updPolId] $polOldLit $opLit $polHintLit)
              (by qedDbProve [$rowInvId, $updPolId] $polNewLit $opLit $polHintLit)
              (by qedDbProve [$rowInvId] $invLit $opLit $invHintLit)
              (by qedDbProve [$rowInvId, $transInvId] $transLit $opLit $transHintLit)))
        return (callT, true)

      else
        liftM (show CommandElabM (Term × Bool) from
          throwErrorAt stx s!"unknown database table method `{opName}` on `{dbInfo.shortName}.{tbl.tableName}` (expected `select`, `findOne`, `count`, `insert`, `update`, `updateOne`, or `delete`)")
  | _ =>
      liftM (show CommandElabM (Term × Bool) from
        throwErrorAt stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`")

end Qed.Server.Db
