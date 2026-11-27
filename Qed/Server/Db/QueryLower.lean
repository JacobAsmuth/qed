import Lean
import Qed.Lang
import Qed.Diag
import Qed.Verify.Core
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime

namespace Qed.Server.Db
open Qed.Lang

/-! ## Dual Lean + Parameterized SQL Query Lowering for `server` `use db : <Database>` -/

def sqlCmpOps : Array (String × Lean.Name) := #[
  ("==", `Qed.Server.Db.SqlBinOp.eq), ("!=", `Qed.Server.Db.SqlBinOp.ne), ("<", `Qed.Server.Db.SqlBinOp.lt),
  ("<=", `Qed.Server.Db.SqlBinOp.le), (">", `Qed.Server.Db.SqlBinOp.gt), (">=", `Qed.Server.Db.SqlBinOp.ge)]

open Lean Elab Command in
@[noinline] def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  `(Qed.Server.Db.SqlIdent.mk $(Syntax.mkStrLit raw) rfl)

open Lean in
@[noinline, nospecialize]
def mkTypedSqlParamTerm {M : Type → Type} [Monad M] [MonadQuotation M] (rowTyId fId : Ident) (valT : Term) : M Term :=
  `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.toSqlLike (fun (_r : $rowTyId) => _r.$fId) $valT))

open Lean Elab Command in
@[noinline] def mkEncColSpecTerm (tableName colName : String) (ek : DbEncKeyInfo) : CommandElabM Term := do
  let prevTs ← ek.prevKeys.toArray.mapM fun (k, fb?) => `(($(Syntax.mkStrLit k), $(quote fb?)))
  `({ keyEnv := $(Syntax.mkStrLit ek.keyEnv), fallback? := $(quote ek.fallback?), aad := ($(Syntax.mkStrLit s!"{tableName}.{colName}") : String).toUTF8, isBytes := $(quote ek.isBytes), prevKeys := [$[$prevTs:term],*] : Qed.Server.Db.EncColSpec })

syntax (name := qedDbProveTac) "qedDbProve" "[" ident,* "]" str str str : tactic

open Lean Meta Elab Tactic in
@[noinline, tactic qedDbProveTac]
def elabQedDbProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  let simpNames := Qed.Verify.Core.dbBaseSimpNames.push ``eq_self
  let simprocs := #[``Qed.Server.qedReduceStrLen]
  -- Pass 1: Keep user pure `let` bindings opaque (`zetaDelta := false`), only expanding `_insRow`,
  -- so `whnf` never unfolds string/helper internals on symbolic inputs.
  let okOpaque ← Qed.Verify.Core.tryRestoreM false id do
    let g0 ← getMainGoal
    let g1 ← g0.withContext do
      let mut fvs : Array FVarId := #[]
      for ld in (← getLCtx) do
        if ld.isLet && ld.userName.eraseMacroScopes == `_insRow then fvs := fvs.push ld.fvarId
      if fvs.isEmpty then pure g0 else g0.replaceTargetDefEq (← Meta.zetaDeltaFVars (← instantiateMVars (← g0.getType)) fvs)
    replaceMainGoal [g1]
    Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs
      (simpCfg := { zetaDelta := false }) (harvestFacts := true) (scanLCtxValues := false) (clearErrorsOnFail := true)
  if okOpaque then return
  if !(← Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs (harvestFacts := true)) then
    Qed.Diag.throwUnsolvedGoals
      m!"Database {(⟨stx.getArg 4⟩ : TSyntax `str).getString} failed in `{(⟨stx.getArg 5⟩ : TSyntax `str).getString}`:"
      m!"\n\nHint: {(⟨stx.getArg 6⟩ : TSyntax `str).getString}"
      (ref? := some stx) (stripPrefixes := ["_row", "_old", "_new", "r"]) (bulletPrefix := "  • must prove: ")
      (goals? := some [(← getUnsolvedGoals).headD (← getMainGoal)])

private partial def stxCollectRowCols (rowVar : String) (colNames : Array String) (stx : Lean.Syntax) : Array String :=
  match extractDottedChain? stx with
  | some [rv, col] => if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ => stx.getArgs.foldl (init := #[]) fun acc ch => (stxCollectRowCols rowVar colNames ch).foldl pushUnique acc

def sqlBinOps : Array (Lean.Name × Lean.Name) := #[
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub),
  (``qedMul, `Qed.Server.Db.SqlBinOp.mul), (``qedAnd, `Qed.Server.Db.SqlBinOp.and), (``qedOr, `Qed.Server.Db.SqlBinOp.or)]

section QueryHelpers
open Lean Elab Command
variable {M : Type → Type} [Monad M] [MonadQuotation M] [MonadError M]

@[noinline, nospecialize] private def mkDbProveTac (unfolds : Array Ident) (kind op hint : String) : M Term :=
  `(by qedDbProve [$[$unfolds],*] $(Syntax.mkStrLit kind) $(Syntax.mkStrLit op) $(Syntax.mkStrLit hint))

@[noinline, nospecialize] private def findDbTable (ref : Syntax) (dbInfo : DatabaseInfo) (tblName : String) : M DbTableInfo := do
  let some tbl := dbInfo.tables.find? (·.tableName == tblName)
    | throwErrorAt ref s!"database `{dbInfo.shortName}` has no table `{tblName}`{Qed.Diag.didYouMean tblName (dbInfo.tables.map (·.tableName)).toList}"
  return tbl

@[noinline, nospecialize] private def findDbCol (ref : Syntax) (tbl : DbTableInfo) (colName : String)
    (fmtErr : String → String → String := fun c t => s!"table `{t}` has no column `{c}`") : M DbColumnInfo := do
  let some colInfo := tbl.columns.find? (·.name == colName)
    | throwErrorAt ref s!"{fmtErr colName tbl.tableName}{Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList}"
  return colInfo

private def parseStrLitArg? (stx : Syntax) : Option String :=
  let u := unwrapParens1 stx; if u.getKind == ``qedLitStr then some (⟨u.getArg 0⟩ : TSyntax `str).getString else none

private def mkPolHint (label fallback pfx : String) : String := if label.isEmpty then fallback else s!"{pfx} `{label}`."

@[noinline] private def mkTblSqlParts (stx : Syntax) (tbl : DbTableInfo) : CommandElabM (Term × Term) := do
  let colSqlIds ← tbl.columns.mapM fun c => mkSqlIdentTerm stx c.name
  return (← mkSqlIdentTerm stx tbl.tableName, ← `([$[$colSqlIds:term],*]))

@[noinline] def mkColsEncPairs (tableName : String) (cols : Array (String × Option DbEncKeyInfo))
    (mkKey : String → Nat → Term) : CommandElabM (Array Term) := do
  let mut out : Array Term := #[]
  for ((colName, encKey?), i) in cols.zipIdx do
    if let some ek := encKey? then
      let sp ← mkEncColSpecTerm tableName colName ek
      out := out.push (← `(($(mkKey colName i), $sp)))
  return out

@[noinline] private def mkTblEncRead (tbl : DbTableInfo) (colOffset : Nat := 0) : CommandElabM (Array Term) :=
  mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun _ i => Syntax.mkNumLit (toString (colOffset + i))

@[noinline] private def mkTblEncWriteTerm (tbl : DbTableInfo) : CommandElabM Term := do
  let es ← mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun c _ => Syntax.mkStrLit c
  `([$[$es:term],*])

@[noinline] private def parseOrderByArg (tbl : DbTableInfo) (ordStx? : Option Syntax) : CommandElabM Term := do
  let some stx := ordStx? | return ← `(none)
  let some raw := parseStrLitArg? stx | throwErrorAt stx "`orderBy` must be a string column name (e.g. `orderBy = \"id\"` or `orderBy = \"-version\"`)"
  let (colName, isDesc) := if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true) else (raw, false)
  let colInfo ← findDbCol stx tbl colName (fun c t => s!"`orderBy` references unknown column `{c}` on table `{t}`")
  if colInfo.encKey?.isSome then throwErrorAt stx s!"cannot `orderBy` encrypted column `{tbl.tableName}.{colName}` (AES-256-GCM uses randomized nonces)"
  let dirT ← if isDesc then `(Qed.Server.Db.SqlOrderDir.desc) else `(Qed.Server.Db.SqlOrderDir.asc)
  `(some ($(← mkSqlIdentTerm stx colName), $dirT))

@[noinline] private def parseAggColArg (tbl : DbTableInfo) (colStx : Syntax) : CommandElabM DbColumnInfo := do
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

private def isNoneIdentStx (s : Syntax) : Bool :=
  let u := unwrapParens1 s
  u.getKind == ``qedIdent && (u.getArg 0).getId.eraseMacroScopes == `none

private def extractSomeArg? (s : Syntax) : Option Syntax :=
  let u := unwrapParens1 s
  if u.getKind == ``qedCall then
    let c := u.getArg 0; let args := (u.getArg 2).getSepArgs
    if c.getKind == ``qedIdent && (c.getArg 0).getId.eraseMacroScopes == `some &&
       args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      some (args[0]!.getArg 0)
    else none
  else none

private partial def rewriteSnapTables (snapId : Ident) (tblNames : Array String) (stx : Syntax) : Syntax :=
  if stx.getKind == ``qedAnyIn then
    let tgt := unwrapParens1 (stx.getArg 3)
    let newTgt :=
      if tgt.getKind == ``qedIdent then
        let id := tgt.getArg 0
        if tblNames.contains id.getId.eraseMacroScopes.toString then
          let info := SourceInfo.fromRef tgt
          Syntax.node info ``qedProj #[Syntax.node info ``qedIdent #[snapId.raw], Syntax.atom info ".", id]
        else stx.getArg 3
      else stx.getArg 3
    (stx.setArg 3 newTgt).setArg 5 (rewriteSnapTables snapId tblNames (stx.getArg 5))
  else match stx with
    | .node info k args => .node info k (args.map (rewriteSnapTables snapId tblNames))
    | other => other

private def extractDirectScopedCol? (scopes : Array (String × DbTableInfo × String)) (s : Syntax) : Option (DbTableInfo × String) :=
  match extractDottedChain? (unwrapParens1 s) with
  | some [rv, col] =>
      scopes.reverse.findSome? fun (v, tbl, _) =>
        if v == rv && tbl.columns.any (·.name == col) then some (tbl, col) else none
  | some [col] =>
      scopes.reverse.findSome? fun (v, tbl, _) =>
        if v.isEmpty && tbl.columns.any (·.name == col) then some (tbl, col) else none
  | _ => none

@[noinline, nospecialize]
partial def lowerRowSqlExpr (lowerValWithLocals : Array String → Syntax → M Term) (dbInfo : DatabaseInfo)
    (scopes : Array (String × DbTableInfo × String)) (stx : Syntax) : M Term := do
  let lowerVal := lowerValWithLocals #[]
  let u := unwrapParens1 stx; let k := u.getKind
  let mentionsScope (s : Syntax) : Bool :=
    scopes.any (fun (v, tbl, _) => if v.isEmpty then tbl.columns.any (fun c => stxMentionsVar c.name s) else stxMentionsVar v s) ||
    stxAny (·.getKind == ``qedAnyIn) s
  if k == ``qedAnyIn then
    let aliasId : Ident := ⟨u.getArg 1⟩; let aliasStr := aliasId.getId.eraseMacroScopes.toString
    unless isSafeSqlIdent aliasStr do throwErrorAt aliasId s!"invalid SQL alias `{aliasStr}` in `any {aliasStr} in ...`"
    if scopes.any (·.1 == aliasStr) then
      throwErrorAt aliasId s!"alias `{aliasStr}` in `any {aliasStr} in ...` shadows an outer row/table variable"
    let tgt := unwrapParens1 (u.getArg 3)
    unless tgt.getKind == ``qedIdent do
      throwErrorAt tgt "cross-table `any <alias> in <table>:` expects a sibling table name from the same `database`"
    let subTblName := (tgt.getArg 0).getId.eraseMacroScopes.toString
    let subTbl ← findDbTable tgt dbInfo subTblName
    let bodySql ← lowerRowSqlExpr lowerValWithLocals dbInfo (scopes.push (aliasStr, subTbl, aliasStr)) (u.getArg 5)
    return ← `(Qed.Server.Db.SqlExpr.existsSubquery $(← liftM (mkSqlIdentTerm tgt subTbl.tableName)) $(← liftM (mkSqlIdentTerm aliasId aliasStr)) $bodySql)
  if !mentionsScope u then
    if k == ``qedIdent then
      match (u.getArg 0).getId.eraseMacroScopes with
      | `true => return ← `(Qed.Server.Db.SqlExpr.litTrue) | `false => return ← `(Qed.Server.Db.SqlExpr.litFalse) | _ => pure ()
    return ← `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $(← lowerVal u)))
  let checkNotEnc (stbl : DbTableInfo) (colInfo : DbColumnInfo) (col : String) : M Unit :=
    if colInfo.encKey?.isSome then
      throwErrorAt u s!"cannot reference encrypted column `{stbl.tableName}.{col}` inside SQL `where` or row-dependent `set` expression (AES-256-GCM uses randomized nonces)"
    else pure ()
  let mkColSql (sqlQual col : String) : M Term := do
    if scopes.size > 1 then
      `(Qed.Server.Db.SqlExpr.qualCol $(← liftM (mkSqlIdentTerm u sqlQual)) $(← liftM (mkSqlIdentTerm u col)))
    else
      `(Qed.Server.Db.SqlExpr.col $(← liftM (mkSqlIdentTerm u col)))
  match extractDottedChain? u with
  | some [rv, col] =>
      if let some (_, stbl, sqlQual) := scopes.reverse.find? (·.1 == rv) then
        let colInfo ← findDbCol u stbl col; checkNotEnc stbl colInfo col
        return ← mkColSql sqlQual col
      else if col == "length" then
        if let some (_, stbl, sqlQual) := scopes.reverse.find? (·.1.isEmpty) then
          if let some colInfo := stbl.columns.find? (·.name == rv) then
            checkNotEnc stbl colInfo rv
            return ← `(Qed.Server.Db.SqlExpr.strLen $(← mkColSql sqlQual rv))
  | some [col] =>
      if let some (_, stbl, sqlQual) := scopes.reverse.find? (·.1.isEmpty) then
        if let some colInfo := stbl.columns.find? (·.name == col) then
          checkNotEnc stbl colInfo col
          return ← mkColSql sqlQual col
  | some [rv, col, "length"] =>
      if let some (_, stbl, sqlQual) := scopes.reverse.find? (·.1 == rv) then
        if let some colInfo := stbl.columns.find? (·.name == col) then
          checkNotEnc stbl colInfo col
          return ← `(Qed.Server.Db.SqlExpr.strLen $(← mkColSql sqlQual col))
  | _ => pure ()
  let sub := lowerRowSqlExpr lowerValWithLocals dbInfo scopes
  let lowerTypedParam (stbl : DbTableInfo) (colName : String) (valStx : Syntax) : M Term := do
    if isBoolLitStx valStx then sub valStx
    else mkTypedSqlParamTerm (mkIdentFrom valStx stbl.rowTypeConst) (mkIdentFrom valStx (Name.mkSimple colName)) (← lowerVal valStx)
  let lowerSide (side other : Syntax) : M Term :=
    match extractDirectScopedCol? scopes other with
    | some (stbl, col) => if !mentionsScope side then lowerTypedParam stbl col side else sub side
    | none => sub side
  if k == ``qedProj then
    let fld := (u.getArg 2).getId.eraseMacroScopes.toString
    if fld == "length" then `(Qed.Server.Db.SqlExpr.strLen $(← sub (u.getArg 0))) else throwErrorAt u s!"unsupported row projection `.{fld}` inside SQL query expression"
  else if let some (_, op) := sqlBinOps.find? (·.1 == k) then `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← sub (u.getArg 0)) $(← sub (u.getArg 2)))
  else if k == ``qedNot then `(Qed.Server.Db.SqlExpr.not $(← sub (u.getArg 1)))
  else if k == ``qedCmp then
    let mut lhs := u.getArg 0; let mut cs : Array Term := #[]
    for lk in (u.getArg 1).getArgs do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1
      let c ←
        if (isNoneIdentStx rhs || isNoneIdentStx lhs) && (opStr == "==" || opStr == "!=") then
          let target := if isNoneIdentStx rhs then lhs else rhs
          let l ← sub target; if opStr == "==" then `(Qed.Server.Db.SqlExpr.isNull $l) else `(Qed.Server.Db.SqlExpr.isNotNull $l)
        else if opStr == "in" || opStr == "not in" then
          if !mentionsScope rhs then
            let base ← `(Qed.Server.Db.SqlExpr.inList $(← sub lhs) (Qed.Server.Db.ToSqlList.toSqlList $(← lowerVal rhs)))
            if opStr == "not in" then `(Qed.Server.Db.SqlExpr.not $base) else pure base
          else throwErrorAt lk s!"SQL `{opStr}` requires a collection value on the right-hand side"
        else if opStr == "==" || opStr == "!=" then
          let isNe := opStr == "!="
          let lowerSomeCmp (inner other : Syntax) (swap : Bool) : M Term := do
            if !mentionsScope other then
              `(Qed.Server.Db.sqlEqSome $(← sub inner) $(← lowerVal other) $(quote isNe))
            else
              let (inSql, oSql) := (← sub inner, ← sub other)
              let (a, b) := if swap then (oSql, inSql) else (inSql, oSql)
              if !isNe then `(Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.eq $a $b)
              else `(Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.or (Qed.Server.Db.SqlExpr.isNull $oSql) (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.ne $a $b))
          match extractSomeArg? lhs, extractSomeArg? rhs with
          | some lI, some rI =>
              let op := mkIdent (if isNe then `Qed.Server.Db.SqlBinOp.ne else `Qed.Server.Db.SqlBinOp.eq)
              `(Qed.Server.Db.SqlExpr.binOp $op $(← lowerSide lI rI) $(← lowerSide rI lI))
          | some lI, none => lowerSomeCmp lI rhs false
          | none, some rI => lowerSomeCmp rI lhs true
          | none, none =>
              let op := mkIdent (if isNe then `Qed.Server.Db.SqlBinOp.ne else `Qed.Server.Db.SqlBinOp.eq)
              `(Qed.Server.Db.SqlExpr.binOp $op $(← lowerSide lhs rhs) $(← lowerSide rhs lhs))
        else
          let some (_, op) := sqlCmpOps.find? (·.1 == opStr) | throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}`"
          `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $(← lowerSide lhs rhs) $(← lowerSide rhs lhs))
      cs := cs.push c; lhs := rhs
    match cs.toList with | [] => `(Qed.Server.Db.SqlExpr.litTrue) | c :: rs => rs.foldlM (init := c) fun a x => `(Qed.Server.Db.SqlExpr.binOp .and $a $x)
  else if k == ``qedExprIf || k == ``qedTernary then
    let (cI, tI, eI) := if k == ``qedTernary then (2, 0, 3) else (1, 3, 4)
    let eOpt := u.getArg eI
    if eOpt.getNumArgs == 0 then
      throwErrorAt u "conditional `if` inside SQL `where`/`set` clause requires an `else` branch"
    let condStx := u.getArg cI; let thenStx := u.getArg tI; let elseStx := eOpt.getArg (eOpt.getNumArgs - 1)
    if !mentionsScope condStx then
      let cT ← lowerVal condStx; let tSql ← sub thenStx; let eSql ← sub elseStx
      `(if ($cT : Bool) then $tSql else $eSql)
    else
      let cSql ← sub condStx; let tSql ← sub thenStx; let eSql ← sub elseStx
      `(Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.or
          (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.and $cSql $tSql)
          (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.and (Qed.Server.Db.SqlExpr.not $cSql) $eSql))
  else if k == ``qedExprIfLet then
    let scrutStx := u.getArg 4; let eOpt := u.getArg 7
    if eOpt.getNumArgs == 0 then
      throwErrorAt u "conditional `if let` inside SQL `where` clause requires an `else:` branch"
    if mentionsScope scrutStx then
      throwErrorAt scrutStx "`if let` scrutinee inside SQL `where` cannot depend on a row column; match an outer `Option` variable instead"
    let patT ← liftM (m := CommandElabM) (liftMacroM (lowerQedPat (u.getArg 2)))
    let scrutT ← lowerVal scrutStx
    let patLocals := (collectQedPatIds (u.getArg 2)).map (·.toString)
    let thenSql ← lowerRowSqlExpr (fun locs e => lowerValWithLocals (patLocals ++ locs) e) dbInfo scopes (u.getArg 6)
    let elseSql ← sub (eOpt.getArg (eOpt.getNumArgs - 1))
    `(match $scrutT:term with | $patT:term => $thenSql | _ => $elseSql)
  else if k == ``qedCall then
    if let some (recv, meth, args) := matchMethodCall? u then
      if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
        let arg := args[0]!.getArg 0
        if meth == "contains" && !mentionsScope recv && mentionsScope arg then
          return ← `(Qed.Server.Db.SqlExpr.inList $(← sub arg) (Qed.Server.Db.ToSqlList.toSqlList $(← lowerVal recv)))
        match meth with
        | "startsWith" => return ← `(Qed.Server.Db.SqlExpr.startsWith $(← sub recv) $(← sub arg))
        | "contains"   => return ← `(Qed.Server.Db.SqlExpr.contains $(← sub recv) $(← sub arg))
        | "endsWith"   => return ← `(Qed.Server.Db.SqlExpr.like $(← sub recv) (Qed.Server.Db.SqlExpr.param (Qed.Server.Db.endsWithLikeVal $(← lowerVal arg))))
        | "like"       => return ← `(Qed.Server.Db.SqlExpr.like $(← sub recv) $(← sub arg))
        | _ => pure ()
    throwErrorAt u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"
  else throwErrorAt u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, `any m in tbl:`, `in`, arithmetic, `.length`, `.startsWith`, `.contains`, `xs.contains(r.col)`, or bound variables)"

@[noinline, nospecialize]
private def parseWhereArg (lowerValWithLocals : Array String → Syntax → M Term)
    (dbInfo : DatabaseInfo) (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax)
    (needCross : Bool := false) : M (Term × Term × Option (String × Syntax) × Bool) := do
  let isCross := needCross || whereStx?.any (stxAny (·.getKind == ``qedAnyIn))
  let snapTyId? ← if isCross then
      let some snapConst := dbInfo.snapTypeConst?
        | throwErrorAt (whereStx?.getD rowTyId.raw) s!"cross-table `any ... in ...` requires a multi-table `database` (`{dbInfo.shortName}` has no `Snap` type)"
      pure (some (mkIdent snapConst))
    else pure none
  let some wRaw := whereStx? | do
    let triv ← match snapTyId? with
      | some sTy => `(fun (_ : $sTy) (_ : $rowTyId) => true)
      | none     => `(fun (_ : $rowTyId) => true)
    return (triv, ← `(Qed.Server.Db.SqlExpr.litTrue), none, isCross)
  let u := unwrapParens1 wRaw
  if u.getKind != ``qedLam1 then throwErrorAt wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`"
  let b := u.getArg 0; let rId : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
  let rName := rId.getId.eraseMacroScopes.toString; let body := u.getArg 2
  let sqlW ← lowerRowSqlExpr lowerValWithLocals dbInfo #[(rName, tbl, tbl.tableName)] body
  let predT ← match snapTyId? with
    | some sTy =>
        let snapId := mkIdent `_dbSnap
        let rewritten := rewriteSnapTables snapId (dbInfo.tables.map (·.tableName)) body
        `(fun ($snapId:ident : $sTy) ($rId:ident : $rowTyId) => ($(← lowerValWithLocals #[rName, "_dbSnap"] rewritten) : Bool))
    | none => `(fun ($rId:ident : $rowTyId) => ($(← lowerValWithLocals #[rName] body) : Bool))
  return (predT, sqlW, some (rName, body), isCross)

@[noinline, nospecialize]
private def parseQueryWindow (tbl : DbTableInfo) (lowerVal : Syntax → M Term) (findNamed : String → Option Syntax) : M (Term × Term × Term) := do
  let optNat (s? : Option Syntax) : M Term := match s? with | none => `(none) | some s => do `(some ($(← lowerVal s) : Nat))
  return (← liftM (parseOrderByArg tbl (findNamed "orderBy")), ← optNat (findNamed "limit"), ← optNat (findNamed "offset"))

@[noinline, nospecialize]
def lowerDbCall (lowerVal : Syntax → M Term) (lowerValWithLocals : Array String → Syntax → M Term)
    (fnName : String) (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String)
    (rawArgs : Array Syntax) (txIdTerm? : Option Term := none) (wrapField : Term → M Term := pure)
    (ctxTerm? : Option Term := none) : M (Term × Bool) := do
  let cfgId := mkIdentFrom stx dbInfo.configConst
  let txOptT : Term ← match txIdTerm? with | some tid => `(some $tid) | none => `(none)
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then throwErrorAt stx "`ensureSchema()` takes no arguments"
      return (← `($(mkIdentFrom stx dbInfo.ensureSchemaConst)), true)
  | [_, tblName, opName] =>
      let tbl ← findDbTable stx dbInfo tblName
      let tid (t : DbTableInfo) (s : Name) := mkIdentFrom stx (t.rowTypeConst ++ s)
      let (rowTyId, rowInvId, readPolId) := (mkIdentFrom stx tbl.rowTypeConst, tid tbl `RowInv, tid tbl `ReadPolicy)
      let ctxId : Term := ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩
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
      let snapTyId? : Option Ident := dbInfo.snapTypeConst?.map (mkIdentFrom stx)
      let mkCrossPolProof (predT : Term) (polId : Ident) (hasCrossPol : Bool) (kind hint : String) : M Term := do
        let some snapTyId := snapTyId? | throwErrorAt stx s!"internal error: missing `Snap` type for database `{dbInfo.shortName}`"
        let polApp ← if hasCrossPol then `($polId _dbSnap $ctxId _r) else `($polId $ctxId _r)
        let pf ← mkDbProveTac #[rowInvId, polId] kind opQual hint
        `(($pf : ∀ (_dbSnap : $snapTyId) (_r : $rowTyId), $rowInvId _r → $predT _dbSnap _r = true → $polApp))

      if opName == "select" || opName == "findOne" || opName == "count" || opName == "selectMeta" || opName == "findOneMeta" then
        let (predT, sqlW, _, isCross) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId whereArg? tbl.hasCrossReadPolicy
        let pf ← if isCross then mkCrossPolProof predT readPolId tbl.hasCrossReadPolicy readPolKind (mkReadPolHint tbl)
                 else mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        if opName == "count" then
          let qT ← `(Qed.Server.Db.SqlQuery.count $tblSqlId $sqlW)
          return (← if isCross then `(Qed.Server.Db.dbCountP $cfgId $qT $pf $txOptT) else mkPolCall `Qed.Server.Db.dbCount qT predT readPolId pf, false)
        let isOne := opName == "findOne" || opName == "findOneMeta"
        let (ordT, limT, offT) ← if !isOne then parseQueryWindow tbl lowerVal findNamed
          else pure (← liftM (parseOrderByArg tbl (findNamed "orderBy")), ← `(some 1), ← `(none))
        let mkProjCall (colsT decT encT : Term) : M Term := do
          let qT ← `(Qed.Server.Db.SqlQuery.select $tblSqlId $colsT $sqlW $ordT $limT $offT)
          let fn := mkIdent <| match isCross, isOne with
            | true, false => `Qed.Server.Db.dbSelectProjP | true, true => `Qed.Server.Db.dbFindOneProjP
            | false, false => `Qed.Server.Db.dbSelectProj | false, true => `Qed.Server.Db.dbFindOneProj
          if isCross then `($fn $cfgId $qT $decT $pf $txOptT $encT)
          else `($fn $cfgId $qT $decT $rowInvId $predT $readPolId $ctxId $pf $txOptT $encT)
        if opName == "selectMeta" || opName == "findOneMeta" then
          unless tbl.hasMeta do
            throwErrorAt stx s!"`{opName}` is only available on tables with both encrypted and non-encrypted columns (`{dbInfo.shortName}.{tbl.tableName}` can use `{if isOne then "findOne" else "select"}` directly)"
          return (← mkProjCall (tid tbl `metaColumns) (tid tbl `decodeMetaRow) (← `([])), false)
        if let some colsStx := findNamed "columns" then
          let uCols := unwrapParens1 colsStx
          unless uCols.getKind == ``qedArrLit do
            throwErrorAt colsStx "`columns` must be a non-empty array of string column names (e.g. `columns = [\"id\", \"title\"]`)"
          let rawColStxs := (uCols.getArg 1).getSepArgs
          if rawColStxs.isEmpty then throwErrorAt colsStx "`columns = [...]` must specify at least one column"
          let mut projCols : Array (Syntax × DbColumnInfo) := #[]; let mut seenCols : Array String := #[]
          for cs in rawColStxs do
            let some cn := parseStrLitArg? cs | throwErrorAt cs "`columns` entries must be string literal column names"
            let some ci := tbl.columns.find? (·.name == cn) | throwErrorAt cs s!"unknown column `{cn}` on table `{tbl.tableName}`"
            if seenCols.contains cn then throwErrorAt cs s!"duplicate column `{cn}` in `columns = [...]`"
            seenCols := seenCols.push cn; projCols := projCols.push (cs, ci)
          let projColIdTs ← liftM <| projCols.mapM fun (cs, ci) => mkSqlIdentTerm cs ci.name
          let projEncTs ← liftM <| mkColsEncPairs tbl.tableName (projCols.map fun (_, ci) => (ci.name, ci.encKey?)) fun _ idx => Syntax.mkNumLit (toString idx)
          let valsVar := mkIdent `_pvals
          let pBindIds : Array Ident := projCols.zipIdx.map fun (_, i) => mkIdent (Name.mkSimple s!"_pc{i}")
          let pDecStmts ← projCols.zipIdx.mapM fun ((cs, ci), idx) => do
            let fId := mkIdentFrom cs (Name.mkSimple ci.name)
            `(match ($valsVar)[$(Syntax.mkNumLit (toString idx))]? with
              | some _v => Qed.Server.Db.fromSqlOfField (fun (_r : $rowTyId) => _r.$fId) _v
              | none => Except.error ("missing column `" ++ $(Syntax.mkStrLit ci.name) ++ "` in database row"))
          let pRetVal ← buildTupleVal (pBindIds.map (⟨·.raw⟩))
          let decFnT ← `(fun ($valsVar:ident : Qed.Server.Db.DbRow) => do
            $[let $pBindIds:ident ← $pDecStmts:term]*
            return $pRetVal)
          return (← mkProjCall (← `([$[$projColIdTs:term],*])) decFnT (← `([$[$projEncTs:term],*])), false)
        let qT ← `(Qed.Server.Db.SqlQuery.select $tblSqlId $allColsT $sqlW $ordT $limT $offT)
        let fn := mkIdent <| match isCross, isOne with
          | true, false => `Qed.Server.Db.dbSelectP | true, true => `Qed.Server.Db.dbFindOneP
          | false, false => `Qed.Server.Db.dbSelect | false, true => `Qed.Server.Db.dbFindOne
        return (← if isCross then `($fn $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $pf $txOptT $(← mkEncReadT))
                  else `($fn $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $predT $readPolId $ctxId $pf $txOptT $(← mkEncReadT)), false)

      else if opName == "sum" || opName == "min" || opName == "max" then
        let some colStx := (findNamed "col").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` requires a column selector (e.g. `\"{tbl.columns[0]?.map (·.name) |>.getD "col"}\"` or `col = \"...\"`)"
        let colInfo ← liftM (parseAggColArg tbl colStx)
        let aggWhere? := (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => if (findNamed "col").isSome then posArgs[0]? else posArgs[1]?
        let (predT, sqlW, _, isCross) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId aggWhere? tbl.hasCrossReadPolicy
        let pf ← if isCross then mkCrossPolProof predT readPolId tbl.hasCrossReadPolicy readPolKind (mkReadPolHint tbl)
                 else mkDbProveTac #[rowInvId, readPolId] readPolKind opQual (mkReadPolHint tbl)
        let aggOp := mkIdent <| match opName with | "sum" => `Qed.Server.Db.SqlAggOp.sum | "min" => `Qed.Server.Db.SqlAggOp.min | _ => `Qed.Server.Db.SqlAggOp.max
        let qT ← `(Qed.Server.Db.SqlQuery.aggregate $aggOp $tblSqlId $(← liftM (mkSqlIdentTerm colStx colInfo.name)) $sqlW)
        if opName == "sum" then
          return (← if isCross then `($(mkIdent (if colInfo.isNat then `Qed.Server.Db.dbSumNatP else `Qed.Server.Db.dbSumIntP)) $cfgId $qT $pf $txOptT)
                    else mkPolCall (if colInfo.isNat then `Qed.Server.Db.dbSumNat else `Qed.Server.Db.dbSumInt) qT predT readPolId pf, false)
        let projT ← `(fun (_r : $rowTyId) => _r.$(mkIdentFrom colStx (Name.mkSimple colInfo.name)))
        return (← if isCross then `(Qed.Server.Db.dbAggOptP $cfgId $qT $projT $pf $txOptT)
                  else `(Qed.Server.Db.dbAggOpt $cfgId $qT $projT $rowInvId $predT $readPolId $ctxId $pf $txOptT), false)

      else if opName == "join" then
        let some rStx := (findNamed "table").orElse fun _ => (findNamed "with").orElse fun _ => posArgs[0]?
          | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.join` requires a target table name (e.g. `join(\"books\", where = ...)` )"
        let uRt := unwrapParens1 rStx
        let rName ← if let some s := parseStrLitArg? rStx then pure s else if uRt.getKind == ``qedIdent then pure (uRt.getArg 0).getId.eraseMacroScopes.toString else throwErrorAt rStx "`join` target table must be a string table name (e.g. `\"books\"`)"
        let rightTbl ← findDbTable rStx dbInfo rName
        if tbl.hasCrossReadPolicy || rightTbl.hasCrossReadPolicy ||
           (findNamed "where").any (stxAny (·.getKind == ``qedAnyIn)) ||
           (findNamed "rightWhere").any (stxAny (·.getKind == ``qedAnyIn)) then
          throwErrorAt stx "cross-table `any ... in ...:` predicates/policies are not supported inside `.join(...)`; query the table directly with `any ... in ...:` in `where`"
        let onCol? ← (findNamed "on").mapM fun o => match parseStrLitArg? o with | some s => pure s | none => throwErrorAt o "`on` must be a string column name"
        let some (lCol, rCol) := (tbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) => if rt == rightTbl.tableName && onCol?.all (· == c.name) then some (c.name, rc) else none).orElse fun _ =>
            rightTbl.columns.findSome? fun c => c.refs?.bind fun (rt, rc) => if rt == tbl.tableName && onCol?.all (· == rc) then some (rc, c.name) else none
          | throwErrorAt stx s!"cannot `join` `{tbl.tableName}` with `{rightTbl.tableName}`: no `references` foreign key links these tables"
        let rRowTyId := mkIdentFrom stx rightTbl.rowTypeConst; let (rTblSqlId, rAllColsT) ← liftM (mkTblSqlParts stx rightTbl)
        let (lPredT, lSqlW, _, _) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId (findNamed "where")
        let (rPredT, rSqlW, _, _) ← parseWhereArg lowerValWithLocals dbInfo rightTbl rRowTyId (findNamed "rightWhere")
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
        let (predT, sqlW, _, isCross) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId whereArg? tbl.hasCrossDeletePolicy
        let delPolId := tid tbl `DeletePolicy
        let delKind := s!"delete policy `{dbInfo.shortName}.{tbl.tableName}.delete`"
        let delHint := mkPolHint tbl.deletePolicyLabel "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`." "Ensure `where = r => ...` implies"
        let qT ← `(Qed.Server.Db.SqlQuery.delete $tblSqlId $sqlW [])
        if isCross then
          let pf ← mkCrossPolProof predT delPolId tbl.hasCrossDeletePolicy delKind delHint
          return (← `(Qed.Server.Db.dbDeleteP $cfgId $qT $pf $txOptT), true)
        let pf ← mkDbProveTac #[rowInvId, delPolId] delKind opQual delHint
        return (← mkPolCall `Qed.Server.Db.dbDelete qT predT delPolId pf, true)

      else if opName == "insert" || opName == "insertOrIgnore" || opName == "upsert" then
        let hasColNamed (nm : String) := tbl.columns.any (·.name == nm)
        let isConflictWhere (s : Syntax) := (unwrapParens1 s).getKind == ``qedLam1 || !hasColNamed "where"
        let allowsConflictArg := opName == "upsert" || opName == "insertOrIgnore"
        let onArg? := if allowsConflictArg then
            (findNamed "conflict").orElse fun _ => if !hasColNamed "on" then findNamed "on" else none
          else none
        let conflictWhereStx? := if opName == "upsert" then (findNamed "where").filter isConflictWhere else none
        let rowNamedArgs := if allowsConflictArg then
            namedArgs.filter fun (k, s) => !(k == "conflict" || (k == "on" && !hasColNamed "on") || (opName == "upsert" && k == "where" && isConflictWhere s))
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
        let insPolArg : Term ← if tbl.hasCrossInsertPolicy then
            let some snapTyId := snapTyId? | throwErrorAt stx s!"internal error: missing `Snap` type for database `{dbInfo.shortName}`"
            `(fun (_c : Qed.Server.RequestCtx) (_r : $rowTyId) => ∀ (_dbSnap : $snapTyId), $insPolId _dbSnap _c _r)
          else pure (insPolId : Term)
        let pairTs ← tbl.columns.mapM fun col => do `(($(← liftM (mkSqlIdentTerm stx col.name)), Qed.Server.Db.ToSql.toSql (($rowVar).$(mkIdentFrom stx (Name.mkSimple col.name)))))
        let invPf ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
        let insPolPf ← mkDbProveTac #[insPolId] s!"insert policy `{dbInfo.shortName}.{tbl.tableName}.insert`" opQual (mkPolHint tbl.insertPolicyLabel "Ensure inserted row satisfies the table's `policy insert` / `policy write`." "Ensure inserted row satisfies")
        let parseConflictCols (reqTarget : Bool) : M (Array DbColumnInfo) := do
          let cis ← match onArg? with
            | some oStx =>
                let rawNames : Array (Syntax × String) ←
                  if let some cName := parseStrLitArg? oStx then pure #[(oStx, cName)]
                  else
                    let uo := unwrapParens1 oStx
                    if uo.getKind == ``qedArrLit then
                      let elems := (uo.getArg 1).getSepArgs
                      if elems.isEmpty then throwErrorAt oStx s!"`{opName}` conflict target `on`/`conflict` cannot be empty"
                      elems.mapM fun el => do
                        let some cn := parseStrLitArg? el | throwErrorAt el s!"`{opName}` conflict target `on`/`conflict` elements must be column name strings (e.g. `on = [\"orgId\", \"slug\"]`)"
                        pure (el, cn)
                    else throwErrorAt oStx s!"`{opName}` conflict target `on`/`conflict` must be a column name string or list of column name strings (e.g. `on = \"id\"` or `on = [\"a\", \"b\"]`)"
                let cis ← rawNames.mapM fun (ref, cn) => findDbCol ref tbl cn
                if cis.size == 1 then
                  unless cis[0]!.isPrimaryKey || cis[0]!.isUnique do
                    throwErrorAt rawNames[0]!.1 s!"`{opName}` conflict column `{tbl.tableName}.{cis[0]!.name}` must be `primary_key` or `unique`"
                pure cis
            | none =>
                if !reqTarget then pure #[]
                else
                  let some pkCol := tbl.columns.find? (·.isPrimaryKey) | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.upsert` requires a `primary_key` column or explicit `on = \"<unique_col>\"`"
                  pure #[pkCol]
          for cc in cis do
            if cc.encKey?.isSome then throwErrorAt stx s!"cannot `{opName}` on encrypted column `{tbl.tableName}.{cc.name}`"
          return cis
        if opName == "insert" then
          return (← `(let $rowVar:ident : $rowTyId := $rowTerm; Qed.Server.Db.dbInsert $cfgId (Qed.Server.Db.SqlQuery.insert $tblSqlId [$[$pairTs:term],*] []) $rowVar $rowInvId $insPolArg $ctxId $invPf $insPolPf $txOptT $(← liftM (mkTblEncWriteTerm tbl))), true)
        else if opName == "insertOrIgnore" then
          let conflictCols ← parseConflictCols false
          let conflictColTs ← conflictCols.mapM fun cc => liftM (mkSqlIdentTerm stx cc.name)
          let retColTs ← match tbl.columns[0]? with | some c0 => pure #[← liftM (mkSqlIdentTerm stx c0.name)] | none => pure #[]
          return (← `(let $rowVar:ident : $rowTyId := $rowTerm; Qed.Server.Db.dbInsertOrIgnore $cfgId (Qed.Server.Db.SqlQuery.insertOrIgnore $tblSqlId [$[$pairTs:term],*] [$[$conflictColTs:term],*] [$[$retColTs:term],*]) $rowVar $rowInvId $insPolArg $ctxId $invPf $insPolPf $txOptT $(← liftM (mkTblEncWriteTerm tbl))), true)
        else
          if tbl.hasCrossUpdatePolicy || conflictWhereStx?.any (stxAny (·.getKind == ``qedAnyIn)) then
            throwErrorAt stx "cross-table `any ... in ...:` is not supported in `.upsert(...)`; use `insertOrIgnore` + `updateOne` inside `transaction`"
          let conflictCols ← parseConflictCols true
          let conflictNames := conflictCols.map (·.name)
          let conflictColTs ← conflictCols.mapM fun cc => liftM (mkSqlIdentTerm stx cc.name)
          let updCols := tbl.columns.filter fun c => !c.isPrimaryKey && !c.isImmutable && !conflictNames.contains c.name
          let updColTs ← updCols.mapM fun c => liftM (mkSqlIdentTerm stx c.name)
          let (conflictPredT, conflictSqlW, _, _) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId conflictWhereStx?
          let conflictSqlOptT ← if conflictWhereStx?.isSome then `(some $conflictSqlW) else `(none)
          let (updPolId, transInvId) := (tid tbl `UpdatePolicy, tid tbl `TransInv)
          let updHint := mkPolHint tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
          let updPolNewPf ← mkDbProveTac #[updPolId] s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual updHint
          let updPolOldPf ← mkDbProveTac #[rowInvId, updPolId] s!"upsert conflict update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual updHint
          let transPf ← mkDbProveTac #[rowInvId, transInvId] s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`" opQual "Ensure the upserted row satisfies all `old(...)` and `transition` invariants against any conflicting row."
          return (← `(let $rowVar:ident : $rowTyId := $rowTerm; Qed.Server.Db.dbUpsert $cfgId
              (Qed.Server.Db.SqlQuery.upsert $tblSqlId [$[$pairTs:term],*] [$[$conflictColTs:term],*] [$[$updColTs:term],*] $conflictSqlOptT $allColsT)
              $rowVar $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $transInvId $conflictPredT
              $insPolArg $updPolId $ctxId $invPf $insPolPf $updPolNewPf $updPolOldPf $transPf $txOptT $(← liftM (mkTblEncWriteTerm tbl)) $(← mkEncReadT)), true)

      else if opName == "update" || opName == "updateOne" then
        let some setRaw := findNamed "set" | throwErrorAt stx s!"`{dbInfo.shortName}.{tbl.tableName}.{opName}` requires `set = r => \{ col = expr, ... }`"
        let (predT, sqlW, whereInfo?, isCross) ← parseWhereArg lowerValWithLocals dbInfo tbl rowTyId whereArg? tbl.hasCrossUpdatePolicy
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
        let mut sqlSetPairs : Array Term := #[]; let mut postChecks : Array Term := #[]; let mut underflowChecks : Array (Ident × Term × Term) := #[]
        for sf in setFields do
          let colId : Ident := ⟨sf.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
          let setOp := (sf.getArg 1).getAtomVal; let valStx := sf.getArg 2
          let colInfo ← findDbCol colId tbl colName
          if colInfo.isImmutable then throwErrorAt colId s!"cannot update `immutable` column `{dbInfo.shortName}.{tbl.tableName}.{colName}` in `{fnName}`"
          setColNames := setColNames.push colName; let fId := mkIdentFrom colId (Name.mkSimple colName)
          let colSqlId ← liftM (mkSqlIdentTerm colId colName)
          if setOp == "+=" || setOp == "-=" then
            if colInfo.encKey?.isSome then
              throwErrorAt valStx s!"cannot update encrypted column `{dbInfo.shortName}.{tbl.tableName}.{colName}` using `{setOp}`"
            if !(colInfo.isNat || colInfo.isInt) || colInfo.isNullable then
              throwErrorAt colId s!"atomic `{setOp}` requires a non-null integer (`Nat` or `Int`) column, but `{tbl.tableName}.{colName}` is not"
            let deltaT ← wrapField (← lowerValWithLocals #[setRowName] valStx)
            let deltaSqlT ← if !stxMentionsVar setRowName valStx && !isBoolLitStx valStx then
                mkTypedSqlParamTerm rowTyId fId (← wrapField (← lowerVal valStx))
              else lowerRowSqlExpr lowerValWithLocals dbInfo #[(setRowName, tbl, tbl.tableName)] valStx
            leanFIds := leanFIds.push fId
            if setOp == "+=" then
              leanFVals := leanFVals.push (← `(($setRowVar.$fId + $deltaT)))
              sqlSetPairs := sqlSetPairs.push (← `(($colSqlId, Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.add (Qed.Server.Db.SqlExpr.col $colSqlId) $deltaSqlT)))
            else
              leanFVals := leanFVals.push (← `(($setRowVar.$fId - $deltaT)))
              sqlSetPairs := sqlSetPairs.push (← `(($colSqlId, Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.sub (Qed.Server.Db.SqlExpr.col $colSqlId) $deltaSqlT)))
              if colInfo.isNat then
                let ufPf ← mkDbProveTac #[rowInvId] s!"Nat non-underflow for `{tbl.tableName}.{colName} -= ...`" opQual s!"Guard the update in `where = r => r.{colName} >= ...` so SQL subtraction cannot go negative."
                underflowChecks := underflowChecks.push (fId, deltaT, ufPf)
          else
            if colInfo.encKey?.isSome && stxMentionsVar setRowName valStx then
              throwErrorAt valStx s!"cannot update encrypted column `{dbInfo.shortName}.{tbl.tableName}.{colName}` using a row-dependent SQL expression"
            leanFIds := leanFIds.push fId; leanFVals := leanFVals.push (← wrapField (← lowerValWithLocals #[setRowName] valStx))
            let sqlValT ← if !stxMentionsVar setRowName valStx && !isBoolLitStx valStx then
                mkTypedSqlParamTerm rowTyId fId (← wrapField (← lowerVal valStx))
              else lowerRowSqlExpr lowerValWithLocals dbInfo #[(setRowName, tbl, tbl.tableName)] valStx
            sqlSetPairs := sqlSetPairs.push (← `(($colSqlId, $sqlValT)))
            if !stxMentionsVar setRowName valStx && !isCross then postChecks := postChecks.push (← `(($postRowVar.$fId == $(← wrapField (← lowerVal valStx)))))
        if !isCross then
          if let some (wRowName, wBody) := whereInfo? then
            let colNames := tbl.columns.map (·.name)
            for conj in splitAndStx wBody do
              let touched := stxCollectRowCols wRowName colNames conj
              if !touched.isEmpty && touched.all (!setColNames.contains ·) then
                postChecks := postChecks.push (← `((fun ($(mkIdent (Name.mkSimple wRowName)):ident : $rowTyId) => ($(← lowerValWithLocals #[wRowName] conj) : Bool)) $postRowVar))
        let setFnT ← `(fun ($setRowVar:ident : $rowTyId) => { $setRowVar with $[$leanFIds:ident := $leanFVals:term],* })
        let qT ← `(Qed.Server.Db.SqlQuery.update $tblSqlId [$[$sqlSetPairs:term],*] $sqlW $allColsT)
        let (updPolId, transInvId) := (tid tbl `UpdatePolicy, tid tbl `TransInv)
        let polHint := mkPolHint tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
        let polOldPf ← mkDbProveTac #[rowInvId, updPolId] s!"update policy `{dbInfo.shortName}.{tbl.tableName}.update`" opQual polHint
        let polNewPf ← mkDbProveTac #[rowInvId, updPolId] s!"post-update policy `{dbInfo.shortName}.{tbl.tableName}.update` (anti-hijack)" opQual polHint
        let invPf ← mkDbProveTac #[rowInvId] s!"table constraint `{dbInfo.shortName}.{tbl.tableName}.RowInv`" opQual "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`."
        let transPf ← mkDbProveTac #[rowInvId, transInvId] s!"transition/monotonicity invariant `{dbInfo.shortName}.{tbl.tableName}.TransInv`" opQual "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants."
        let baseCall ← if isCross then do
            let some snapTyId := snapTyId? | throwErrorAt stx s!"internal error: missing `Snap` type for database `{dbInfo.shortName}`"
            let polOldApp ← if tbl.hasCrossUpdatePolicy then `($updPolId _dbSnap $ctxId _r) else `($updPolId $ctxId _r)
            let polNewApp ← if tbl.hasCrossUpdatePolicy then `($updPolId _dbSnap $ctxId ($setFnT _r)) else `($updPolId $ctxId ($setFnT _r))
            let hAll ← `(And.intro
              ($polOldPf : ∀ (_dbSnap : $snapTyId) (_r : $rowTyId), $rowInvId _r → $predT _dbSnap _r = true → $polOldApp)
              (And.intro
                ($polNewPf : ∀ (_dbSnap : $snapTyId) (_r : $rowTyId), $rowInvId _r → $predT _dbSnap _r = true → $polNewApp)
                (And.intro
                  ($invPf : ∀ (_dbSnap : $snapTyId) (_r : $rowTyId), $rowInvId _r → $predT _dbSnap _r = true → $rowInvId ($setFnT _r))
                  ($transPf : ∀ (_dbSnap : $snapTyId) (_r : $rowTyId), $rowInvId _r → $predT _dbSnap _r = true → $transInvId _r ($setFnT _r)))))
            `($(mkIdent (if opName == "updateOne" then `Qed.Server.Db.dbUpdateOneP else `Qed.Server.Db.dbUpdateP))
              $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound)
              $hAll $txOptT $(← liftM (mkTblEncWriteTerm tbl)) $(← mkEncReadT))
          else do
            let postPredT ← `(fun ($postRowVar:ident : $rowTyId) => $(← mkBoolConj postChecks))
            `($(mkIdent (if opName == "updateOne" then `Qed.Server.Db.dbUpdateOne else `Qed.Server.Db.dbUpdate))
              $cfgId $qT $(tid tbl `decodeRow) $rowInvId $(tid tbl `rowInvBool) $(tid tbl `rowInvBool_sound) $transInvId
              $predT $setFnT $postPredT $updPolId $ctxId $polOldPf $polNewPf $invPf $transPf $txOptT $(← liftM (mkTblEncWriteTerm tbl)) $(← mkEncReadT))
        let guardedCall ← underflowChecks.foldrM (init := baseCall) fun (fId, deltaT, ufPf) acc => do
          if isCross then
            let some snapTyId := snapTyId? | throwErrorAt stx s!"internal error: missing `Snap` type for database `{dbInfo.shortName}`"
            `(have _ : ∀ (_dbSnap : $snapTyId) ($setRowVar:ident : $rowTyId), $rowInvId $setRowVar → $predT _dbSnap $setRowVar = true → $deltaT ≤ ($setRowVar).$fId := $ufPf; $acc)
          else
            `(have _ : ∀ ($setRowVar:ident : $rowTyId), $rowInvId $setRowVar → $predT $setRowVar = true → $deltaT ≤ ($setRowVar).$fId := $ufPf; $acc)
        return (guardedCall, true)

      else throwErrorAt stx s!"unknown database table method `{opName}` on `{dbInfo.shortName}.{tbl.tableName}` (expected `select`, `findOne`, `count`, `sum`, `min`, `max`, `join`, `insert`, `insertOrIgnore`, `upsert`, `update`, `updateOne`, or `delete`)"
  | _ => throwErrorAt stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`"

end QueryHelpers
end Qed.Server.Db
