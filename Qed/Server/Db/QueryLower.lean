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

syntax (name := qedDbProveTac) "qedDbProve" "[" ident,* "]" str str str : tactic

def sqlCmpOps : Array (String × Lean.Name) := #[
  ("==", `Qed.Server.Db.SqlBinOp.eq), ("!=", `Qed.Server.Db.SqlBinOp.ne), ("<", `Qed.Server.Db.SqlBinOp.lt),
  ("<=", `Qed.Server.Db.SqlBinOp.le), (">", `Qed.Server.Db.SqlBinOp.gt), (">=", `Qed.Server.Db.SqlBinOp.ge)]

def sqlBinOps : Array (Lean.Name × Lean.Name) := #[
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub),
  (``qedMul, `Qed.Server.Db.SqlBinOp.mul), (``qedAnd, `Qed.Server.Db.SqlBinOp.and), (``qedOr, `Qed.Server.Db.SqlBinOp.or)]

private def sqlStrMethods : Array (String × Lean.Name) := #[
  ("startsWith", `Qed.Server.Db.SqlExpr.startsWith), ("contains", `Qed.Server.Db.SqlExpr.contains), ("like", `Qed.Server.Db.SqlExpr.like)]

section PureBuilders
open Lean

@[noinline] def getPureQuotCtx : Lean.Elab.Command.CommandElabM PureQuotCtx := runPureQuot read
@[inline] def runQuot {α : Type} (qctx : PureQuotCtx) (k : PureQuotM α) : α := k.run qctx

@[noinline] def mkSqlIdentTermPure (raw : String) : PureQuotM Term :=
  `(Qed.Server.Db.SqlIdent.mk $(Syntax.mkStrLit raw) rfl)

@[noinline] def mkTypedSqlParamTerm (rowTyId fId : Ident) (valT : Term) : PureQuotM Term :=
  `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.toSqlLike (fun (_r : $rowTyId) => _r.$fId) $valT))

@[noinline] def mkEncColSpecTerm (tableName colName : String) (ek : DbEncKeyInfo) : PureQuotM Term := do
  let prevTs ← ek.prevKeys.toArray.mapM fun (k, fb?) => `(($(Syntax.mkStrLit k), $(quote fb?)))
  `({ keyEnv := $(Syntax.mkStrLit ek.keyEnv), fallback? := $(quote ek.fallback?), aad := ($(Syntax.mkStrLit s!"{tableName}.{colName}") : String).toUTF8, isBytes := $(quote ek.isBytes), prevKeys := [$[$prevTs:term],*] : Qed.Server.Db.EncColSpec })

@[noinline] def mkColsEncPairs (tableName : String) (cols : Array (String × Option DbEncKeyInfo)) (mkKey : String → Nat → Term) : PureQuotM (Array Term) := do
  let mut out : Array Term := #[]
  for ((colName, encKey?), i) in cols.zipIdx do
    if let some ek := encKey? then out := out.push (← `(($(mkKey colName i), $(← mkEncColSpecTerm tableName colName ek))))
  return out

@[noinline] def mkDecodeRowBody (valsVar : Ident) (colDecs : Array (Ident × String × Term)) (retTerm : Term) : PureQuotM Term := do
  let bindIds := colDecs.map (·.1)
  let decStmts ← colDecs.zipIdx.mapM fun ((_, colName, decFn), idx) =>
    `(match ($valsVar)[$(Syntax.mkNumLit (toString idx))]? with
      | some _v => $decFn _v | none => Except.error ("missing column `" ++ $(Syntax.mkStrLit colName) ++ "` in database row"))
  `(do
    $[let $bindIds:ident ← $decStmts:term]*
    return $retTerm)

@[noinline] private def mkDbProveTac (unfolds : Array Ident) (kind op hint : String) : PureQuotM Term :=
  `(by qedDbProve [$[$unfolds],*] $(Syntax.mkStrLit kind) $(Syntax.mkStrLit op) $(Syntax.mkStrLit hint))

@[noinline] private def mkTblSqlPartsPure (tbl : DbTableInfo) : PureQuotM (Term × Term) := do
  let colSqlIds ← tbl.columns.mapM fun c => mkSqlIdentTermPure c.name
  return (← mkSqlIdentTermPure tbl.tableName, ← `([$[$colSqlIds:term],*]))

@[noinline] private def mkTblEncReadPure (tbl : DbTableInfo) (colOffset : Nat := 0) : PureQuotM (Array Term) :=
  mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun _ i => Syntax.mkNumLit (toString (colOffset + i))

@[noinline] private def mkTblEncReadListPure (tbl : DbTableInfo) : PureQuotM Term := do
  let es ← mkTblEncReadPure tbl; `([$[$es:term],*])

@[noinline] private def mkTblEncWritePure (tbl : DbTableInfo) : PureQuotM Term := do
  let es ← mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun c _ => Syntax.mkStrLit c
  `([$[$es:term],*])

@[noinline] private def mkColSqlPure (isMulti : Bool) (sqlQual col : String) (asLen : Bool := false) : PureQuotM Term := do
  let base ← if isMulti then `(Qed.Server.Db.SqlExpr.qualCol $(← mkSqlIdentTermPure sqlQual) $(← mkSqlIdentTermPure col))
    else `(Qed.Server.Db.SqlExpr.col $(← mkSqlIdentTermPure col))
  if asLen then `(Qed.Server.Db.SqlExpr.strLen $base) else pure base

@[noinline] private def mkSqlBinOpPure (op : Name) (l r : Term) : PureQuotM Term := `(Qed.Server.Db.SqlExpr.binOp $(mkIdent op) $l $r)

@[noinline] private def mkSqlAndChainPure : List Term → PureQuotM Term
  | [] => `(Qed.Server.Db.SqlExpr.litTrue)
  | c :: rs => rs.foldlM (init := c) fun a x => `(Qed.Server.Db.SqlExpr.binOp .and $a $x)

end PureBuilders

private partial def stxCollectRowCols (rowVar : String) (colNames : Array String) (stx : Lean.Syntax) : Array String :=
  match extractDottedChain? stx with
  | some [rv, col] => if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ => stx.getArgs.foldl (init := #[]) fun acc ch => (stxCollectRowCols rowVar colNames ch).foldl pushUnique acc

section QueryHelpers
open Lean Elab Command

@[noinline] def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  return (mkSqlIdentTermPure raw).run (← getPureQuotCtx)

@[noinline] private def findDbTable (ref : Syntax) (dbInfo : DatabaseInfo) (tblName : String) : CommandElabM DbTableInfo := do
  let some tbl := dbInfo.tables.find? (·.tableName == tblName)
    | throwErrorAt ref s!"database `{dbInfo.shortName}` has no table `{tblName}`{Qed.Diag.didYouMean tblName (dbInfo.tables.map (·.tableName)).toList}"
  return tbl

@[noinline] private def findDbCol (ref : Syntax) (tbl : DbTableInfo) (colName : String)
    (fmtErr : String → String → String := fun c t => s!"table `{t}` has no column `{c}`") : CommandElabM DbColumnInfo := do
  let some colInfo := tbl.columns.find? (·.name == colName)
    | throwErrorAt ref s!"{fmtErr colName tbl.tableName}{Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList}"
  return colInfo

private def parseStrLitArg? (stx : Syntax) : Option String :=
  let u := unwrapParens1 stx; if u.getKind == ``qedLitStr then some (⟨u.getArg 0⟩ : TSyntax `str).getString else none

private def mkPolHint (label fallback pfx : String) : String := if label.isEmpty then fallback else s!"{pfx} `{label}`."

private def isIdentNamed (s : Syntax) (p : Name → Bool) : Bool :=
  let u := unwrapParens1 s; u.getKind == ``qedIdent && p (u.getArg 0).getId.eraseMacroScopes

private def isBoolLitStx (s : Syntax) : Bool := isIdentNamed s fun n => n == `true || n == `false
private def isNoneIdentStx (s : Syntax) : Bool := isIdentNamed s (· == `none)

private def extractSomeArg? (s : Syntax) : Option Syntax :=
  let u := unwrapParens1 s
  if u.getKind == ``qedCall then
    let c := u.getArg 0; let args := (u.getArg 2).getSepArgs
    if c.getKind == ``qedIdent && (c.getArg 0).getId.eraseMacroScopes == `some && args.size == 1 && args[0]!.getKind == ``qedCallArgPos then some (args[0]!.getArg 0) else none
  else none

private partial def rewriteSnapTables (snapId : Ident) (tblNames : Array String) (stx : Syntax) : Syntax :=
  if stx.getKind == ``qedAnyIn then
    let tgt := unwrapParens1 (stx.getArg 3)
    let newTgt := if tgt.getKind == ``qedIdent && tblNames.contains (tgt.getArg 0).getId.eraseMacroScopes.toString then
        let info := SourceInfo.fromRef tgt
        Syntax.node info ``qedProj #[Syntax.node info ``qedIdent #[snapId.raw], Syntax.atom info ".", tgt.getArg 0]
      else stx.getArg 3
    (stx.setArg 3 newTgt).setArg 5 (rewriteSnapTables snapId tblNames (stx.getArg 5))
  else match stx with | .node info k args => .node info k (args.map (rewriteSnapTables snapId tblNames)) | other => other

private def extractDirectScopedCol? (scopes : Array (String × DbTableInfo × String)) (s : Syntax) : Option (DbTableInfo × String) :=
  match extractDottedChain? (unwrapParens1 s) with
  | some [rv, col] => scopes.reverse.findSome? fun (v, tbl, _) => if v == rv && tbl.columns.any (·.name == col) then some (tbl, col) else none
  | some [col] => scopes.reverse.findSome? fun (v, tbl, _) => if v.isEmpty && tbl.columns.any (·.name == col) then some (tbl, col) else none
  | _ => none

@[noinline] private def parseOrderByArg (qctx : PureQuotCtx) (tbl : DbTableInfo) (ordStx? : Option Syntax) : CommandElabM Term := do
  let some stx := ordStx? | return runQuot qctx `(none)
  let some raw := parseStrLitArg? stx | throwErrorAt stx "`orderBy` must be a string column name (e.g. `orderBy = \"id\"` or `orderBy = \"-version\"`)"
  let (colName, isDesc) := if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true) else (raw, false)
  let colInfo ← findDbCol stx tbl colName (fun c t => s!"`orderBy` references unknown column `{c}` on table `{t}`")
  if colInfo.encKey?.isSome then throwErrorAt stx s!"cannot `orderBy` encrypted column `{tbl.tableName}.{colName}` (AES-256-GCM uses randomized nonces)"
  return runQuot qctx do `(some ($(← mkSqlIdentTermPure colName), $(mkIdent (if isDesc then `Qed.Server.Db.SqlOrderDir.desc else `Qed.Server.Db.SqlOrderDir.asc))))

@[noinline] private def parseAggColArg (tbl : DbTableInfo) (colStx : Syntax) : CommandElabM DbColumnInfo := do
  let u := unwrapParens1 colStx; let errMsg := "aggregate column selector must be a column name string (e.g. `\"stock\"`) or `r => r.col`"
  let colName ← if let some s := parseStrLitArg? colStx then pure s
    else if u.getKind == ``qedLam1 then
      let b := u.getArg 0; let rName := if b.isIdent then b.getId.eraseMacroScopes.toString else ""
      match extractDottedChain? (u.getArg 2) with | some [rv, col] => if rv == rName then pure col else throwErrorAt colStx errMsg | _ => throwErrorAt colStx errMsg
    else throwErrorAt colStx errMsg
  let colInfo ← findDbCol colStx tbl colName
  if colInfo.encKey?.isSome then throwErrorAt colStx s!"cannot compute SQL aggregate on encrypted column `{tbl.tableName}.{colName}`"
  return colInfo

@[noinline] private def lowerRowSqlCol? (qctx : PureQuotCtx) (scopes : Array (String × DbTableInfo × String)) (u : Syntax) : CommandElabM (Option Term) := do
  let emit (stbl : DbTableInfo) (colInfo : DbColumnInfo) (sqlQual col : String) (asLen : Bool) : CommandElabM (Option Term) := do
    if colInfo.encKey?.isSome then
      throwErrorAt u s!"cannot reference encrypted column `{stbl.tableName}.{col}` inside SQL `where` or row-dependent `set` expression (AES-256-GCM uses randomized nonces)"
    return some (runQuot qctx (mkColSqlPure (scopes.size > 1) sqlQual col asLen))
  let lookup (p : String → Bool) (col : String) (asLen : Bool) : CommandElabM (Option Term) := do
    if let some (_, stbl, sqlQual) := scopes.reverse.find? (p ·.1) then
      if let some colInfo := stbl.columns.find? (·.name == col) then return ← emit stbl colInfo sqlQual col asLen
    return none
  match extractDottedChain? u with
  | some [rv, col] =>
      if let some (_, stbl, sqlQual) := scopes.reverse.find? (·.1 == rv) then
        emit stbl (← findDbCol u stbl col) sqlQual col false
      else if col == "length" then lookup (·.isEmpty) rv true else pure none
  | some [col] => lookup (·.isEmpty) col false
  | some [rv, col, "length"] => lookup (· == rv) col true
  | _ => pure none

@[noinline] private def lowerRowSqlMethod (qctx : PureQuotCtx) (mentionsScope : Syntax → Bool)
    (lowerVal sub : Syntax → CommandElabM Term) (u : Syntax) : CommandElabM Term := do
  if let some (recv, meth, args) := matchMethodCall? u then
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      let arg := args[0]!.getArg 0
      if meth == "contains" && !mentionsScope recv && mentionsScope arg then
        let (aSql, rVal) := (← sub arg, ← lowerVal recv)
        return runQuot qctx `(Qed.Server.Db.SqlExpr.inList $aSql (Qed.Server.Db.ToSqlList.toSqlList $rVal))
      if meth == "endsWith" then
        let (r, a) := (← sub recv, ← lowerVal arg)
        return runQuot qctx `(Qed.Server.Db.SqlExpr.like $r (Qed.Server.Db.SqlExpr.param (Qed.Server.Db.endsWithLikeVal $a)))
      if let some (_, ctor) := sqlStrMethods.find? (·.1 == meth) then
        let (r, a) := (← sub recv, ← sub arg)
        return runQuot qctx `($(mkIdent ctor) $r $a)
  throwErrorAt u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"

@[noinline] private def lowerRowSqlCmp (qctx : PureQuotCtx) (mentionsScope : Syntax → Bool)
    (lowerVal sub : Syntax → CommandElabM Term) (lowerSide : Syntax → Syntax → CommandElabM Term) (u : Syntax) : CommandElabM Term := do
  let mut lhs := u.getArg 0; let mut cs : Array Term := #[]
  for lk in (u.getArg 1).getArgs do
    let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1
    let c ←
      if (isNoneIdentStx rhs || isNoneIdentStx lhs) && (opStr == "==" || opStr == "!=") then
        let l ← sub (if isNoneIdentStx rhs then lhs else rhs)
        pure <| runQuot qctx `($(mkIdent (if opStr == "==" then `Qed.Server.Db.SqlExpr.isNull else `Qed.Server.Db.SqlExpr.isNotNull)) $l)
      else if opStr == "in" || opStr == "not in" then
        if !mentionsScope rhs then
          let (l, r) := (← sub lhs, ← lowerVal rhs)
          pure <| runQuot qctx do
            let base ← `(Qed.Server.Db.SqlExpr.inList $l (Qed.Server.Db.ToSqlList.toSqlList $r))
            if opStr == "not in" then `(Qed.Server.Db.SqlExpr.not $base) else pure base
        else throwErrorAt lk s!"SQL `{opStr}` requires a collection value on the right-hand side"
      else if opStr == "==" || opStr == "!=" then
        let isNe := opStr == "!="
        let lowerSomeCmp (inner other : Syntax) (swap : Bool) : CommandElabM Term := do
          if !mentionsScope other then return runQuot qctx `(Qed.Server.Db.sqlEqSome $(← sub inner) $(← lowerVal other) $(quote isNe))
          let (inSql, oSql) := (← sub inner, ← sub other); let (a, b) := if swap then (oSql, inSql) else (inSql, oSql)
          return runQuot qctx (if !isNe then mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.eq a b
            else `(Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.or (Qed.Server.Db.SqlExpr.isNull $oSql) (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.ne $a $b)))
        let mkEqBin (a b : Syntax) : CommandElabM Term := do
          let (la, rb) := (← lowerSide a b, ← lowerSide b a)
          return runQuot qctx (mkSqlBinOpPure (if isNe then `Qed.Server.Db.SqlBinOp.ne else `Qed.Server.Db.SqlBinOp.eq) la rb)
        match extractSomeArg? lhs, extractSomeArg? rhs with
        | some lI, some rI => mkEqBin lI rI | some lI, none => lowerSomeCmp lI rhs false | none, some rI => lowerSomeCmp rI lhs true | none, none => mkEqBin lhs rhs
      else
        let some (_, op) := sqlCmpOps.find? (·.1 == opStr) | throwErrorAt lk s!"unsupported SQL comparison operator `{opStr}`"
        pure <| runQuot qctx (mkSqlBinOpPure op (← lowerSide lhs rhs) (← lowerSide rhs lhs))
    cs := cs.push c; lhs := rhs
  return runQuot qctx (mkSqlAndChainPure cs.toList)

@[noinline] private partial def lowerRowSqlExprGo (qctx : PureQuotCtx) (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (dbInfo : DatabaseInfo) (scopes : Array (String × DbTableInfo × String)) (stx : Syntax) : CommandElabM Term := do
  let lowerVal := lowerValWithLocals #[]; let u := unwrapParens1 stx; let k := u.getKind
  let mentionsScope (s : Syntax) : Bool :=
    scopes.any (fun (v, tbl, _) => if v.isEmpty then tbl.columns.any (fun c => stxMentionsVar c.name s) else stxMentionsVar v s) || stxAny (·.getKind == ``qedAnyIn) s
  if k == ``qedAnyIn then
    let aliasId : Ident := ⟨u.getArg 1⟩; let aliasStr := aliasId.getId.eraseMacroScopes.toString
    unless isSafeSqlIdent aliasStr do throwErrorAt aliasId s!"invalid SQL alias `{aliasStr}` in `any {aliasStr} in ...`"
    if scopes.any (·.1 == aliasStr) then throwErrorAt aliasId s!"alias `{aliasStr}` in `any {aliasStr} in ...` shadows an outer row/table variable"
    let tgt := unwrapParens1 (u.getArg 3)
    unless tgt.getKind == ``qedIdent do throwErrorAt tgt "cross-table `any <alias> in <table>:` expects a sibling table name from the same `database`"
    let subTbl ← findDbTable tgt dbInfo (tgt.getArg 0).getId.eraseMacroScopes.toString
    let bodySql ← lowerRowSqlExprGo qctx lowerValWithLocals dbInfo (scopes.push (aliasStr, subTbl, aliasStr)) (u.getArg 5)
    return runQuot qctx `(Qed.Server.Db.SqlExpr.existsSubquery $(← mkSqlIdentTerm tgt subTbl.tableName) $(← mkSqlIdentTerm aliasId aliasStr) $bodySql)
  if !mentionsScope u then
    if k == ``qedIdent then match (u.getArg 0).getId.eraseMacroScopes with
      | `true => return runQuot qctx `(Qed.Server.Db.SqlExpr.litTrue) | `false => return runQuot qctx `(Qed.Server.Db.SqlExpr.litFalse) | _ => pure ()
    return runQuot qctx `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.ToSql.toSql $(← lowerVal u)))
  if let some colT ← lowerRowSqlCol? qctx scopes u then return colT
  let sub := lowerRowSqlExprGo qctx lowerValWithLocals dbInfo scopes
  let lowerSide (side other : Syntax) : CommandElabM Term :=
    match extractDirectScopedCol? scopes other with
    | some (stbl, col) =>
        if !mentionsScope side && !isBoolLitStx side then do
          return runQuot qctx (mkTypedSqlParamTerm (mkIdentFrom side stbl.rowTypeConst) (mkIdentFrom side (Name.mkSimple col)) (← lowerVal side))
        else sub side
    | none => sub side
  if k == ``qedProj then
    let fld := (u.getArg 2).getId.eraseMacroScopes.toString
    if fld == "length" then return runQuot qctx `(Qed.Server.Db.SqlExpr.strLen $(← sub (u.getArg 0)))
    else throwErrorAt u s!"unsupported row projection `.{fld}` inside SQL query expression"
  else if let some (_, op) := sqlBinOps.find? (·.1 == k) then return runQuot qctx (mkSqlBinOpPure op (← sub (u.getArg 0)) (← sub (u.getArg 2)))
  else if k == ``qedNot then return runQuot qctx `(Qed.Server.Db.SqlExpr.not $(← sub (u.getArg 1)))
  else if k == ``qedCmp then lowerRowSqlCmp qctx mentionsScope lowerVal sub lowerSide u
  else if k == ``qedExprIf || k == ``qedTernary then
    let (cI, tI, eI) := if k == ``qedTernary then (2, 0, 3) else (1, 3, 4); let eOpt := u.getArg eI
    if eOpt.getNumArgs == 0 then throwErrorAt u "conditional `if` inside SQL `where`/`set` clause requires an `else` branch"
    let (condStx, thenStx, elseStx) := (u.getArg cI, u.getArg tI, eOpt.getArg (eOpt.getNumArgs - 1))
    if !mentionsScope condStx then
      let (cT, tSql, eSql) := (← lowerVal condStx, ← sub thenStx, ← sub elseStx)
      return runQuot qctx `(if ($cT : Bool) then $tSql else $eSql)
    else
      let (cSql, tSql, eSql) := (← sub condStx, ← sub thenStx, ← sub elseStx)
      return runQuot qctx `(Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.or
        (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.and $cSql $tSql)
        (Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.and (Qed.Server.Db.SqlExpr.not $cSql) $eSql))
  else if k == ``qedExprIfLet then
    let scrutStx := u.getArg 4; let eOpt := u.getArg 7
    if eOpt.getNumArgs == 0 then throwErrorAt u "conditional `if let` inside SQL `where` clause requires an `else:` branch"
    if mentionsScope scrutStx then throwErrorAt scrutStx "`if let` scrutinee inside SQL `where` cannot depend on a row column; match an outer `Option` variable instead"
    let patT ← liftMacroM (lowerQedPat (u.getArg 2)); let scrutT ← lowerVal scrutStx
    let patLocals := (collectQedPatIds (u.getArg 2)).map (·.toString)
    let thenSql ← lowerRowSqlExprGo qctx (fun locs e => lowerValWithLocals (patLocals ++ locs) e) dbInfo scopes (u.getArg 6)
    return runQuot qctx `(match $scrutT:term with | $patT:term => $thenSql | _ => $(← sub (eOpt.getArg (eOpt.getNumArgs - 1))))
  else if k == ``qedCall then lowerRowSqlMethod qctx mentionsScope lowerVal sub u
  else throwErrorAt u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, `any m in tbl:`, `in`, arithmetic, `.length`, `.startsWith`, `.contains`, `xs.contains(r.col)`, or bound variables)"

def lowerRowSqlExpr (lowerValWithLocals : Array String → Syntax → CommandElabM Term) (dbInfo : DatabaseInfo)
    (scopes : Array (String × DbTableInfo × String)) (stx : Syntax) : CommandElabM Term := do
  lowerRowSqlExprGo (← getPureQuotCtx) lowerValWithLocals dbInfo scopes stx

@[noinline] private def parseWhereArg (qctx : PureQuotCtx) (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (dbInfo : DatabaseInfo) (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax)
    (needCross : Bool := false) : CommandElabM (Term × Term × Option (String × Syntax) × Bool) := do
  let isCross := needCross || whereStx?.any (stxAny (·.getKind == ``qedAnyIn))
  let snapTyId? ← if isCross then
      let some snapConst := dbInfo.snapTypeConst? | throwErrorAt (whereStx?.getD rowTyId.raw) s!"cross-table `any ... in ...` requires a multi-table `database` (`{dbInfo.shortName}` has no `Snap` type)"
      pure (some (mkIdent snapConst))
    else pure none
  let some wRaw := whereStx? | return runQuot qctx do
    let triv ← match snapTyId? with | some sTy => `(fun (_ : $sTy) (_ : $rowTyId) => true) | none => `(fun (_ : $rowTyId) => true)
    return (triv, ← `(Qed.Server.Db.SqlExpr.litTrue), none, isCross)
  let u := unwrapParens1 wRaw
  if u.getKind != ``qedLam1 then throwErrorAt wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`"
  let b := u.getArg 0; let rId : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
  let rName := rId.getId.eraseMacroScopes.toString; let body := u.getArg 2
  let sqlW ← lowerRowSqlExprGo qctx lowerValWithLocals dbInfo #[(rName, tbl, tbl.tableName)] body
  let predT ← match snapTyId? with
    | some sTy =>
        let snapId := mkIdent `_dbSnap
        let bVal ← lowerValWithLocals #[rName, "_dbSnap"] (rewriteSnapTables snapId (dbInfo.tables.map (·.tableName)) body)
        pure <| runQuot qctx `(fun ($snapId:ident : $sTy) ($rId:ident : $rowTyId) => ($bVal : Bool))
    | none => pure <| runQuot qctx `(fun ($rId:ident : $rowTyId) => ($(← lowerValWithLocals #[rName] body) : Bool))
  return (predT, sqlW, some (rName, body), isCross)

@[noinline] private def parseQueryWindow (qctx : PureQuotCtx) (tbl : DbTableInfo) (lowerVal : Syntax → CommandElabM Term)
    (findNamed : String → Option Syntax) : CommandElabM (Term × Term × Term) := do
  let optNat (s? : Option Syntax) : CommandElabM Term := match s? with
    | none => pure <| runQuot qctx `(none) | some s => do pure <| runQuot qctx `(some ($(← lowerVal s) : Nat))
  return (← parseOrderByArg qctx tbl (findNamed "orderBy"), ← optNat (findNamed "limit"), ← optNat (findNamed "offset"))

private structure DbCallCtx where
  qctx : PureQuotCtx
  lowerValWithLocals : Array String → Syntax → CommandElabM Term
  fnName : String
  dbInfo : DatabaseInfo
  stx : Syntax
  tbl : DbTableInfo
  opName : String
  opQual : String
  cfgId : Ident
  txOptT : Term
  ctxId : Term
  rowTyId : Ident
  rowInvId : Ident
  readPolId : Ident
  tblSqlId : Term
  allColsT : Term
  snapTyId? : Option Ident
  posArgs : Array Syntax
  namedArgs : Array (String × Syntax)
  whereArg? : Option Syntax
  wrapField : Term → PureQuotM Term

private def DbCallCtx.q {α : Type} (c : DbCallCtx) (k : PureQuotM α) : α := k.run c.qctx
private def DbCallCtx.tid (c : DbCallCtx) (t : DbTableInfo) (s : Name) : Ident := mkIdentFrom c.stx (t.rowTypeConst ++ s)
private def DbCallCtx.lowerVal (c : DbCallCtx) (s : Syntax) : CommandElabM Term := c.lowerValWithLocals #[] s
private def DbCallCtx.findNamed (c : DbCallCtx) (k : String) : Option Syntax := findNamedArg? c.namedArgs k
private def DbCallCtx.qualName (c : DbCallCtx) : String := s!"{c.dbInfo.shortName}.{c.tbl.tableName}"
private def DbCallCtx.readPolKind (c : DbCallCtx) : String := s!"read policy `{c.qualName}.read`"
private def DbCallCtx.readPolHint (c : DbCallCtx) (t : DbTableInfo := c.tbl) (clause := "`where = r => ...`") (desc := "the table's") : String :=
  mkPolHint t.readPolicyLabel s!"Check {clause} against {desc} `policy read`." s!"Ensure {clause} (together with `requires` / `if` guards) implies"
private def DbCallCtx.parseWhere (c : DbCallCtx) (whereStx? : Option Syntax := c.whereArg?) (needCross := false)
    (tbl : DbTableInfo := c.tbl) (rowTyId : Ident := c.rowTyId) : CommandElabM (Term × Term × Option (String × Syntax) × Bool) :=
  parseWhereArg c.qctx c.lowerValWithLocals c.dbInfo tbl rowTyId whereStx? needCross

@[noinline] private def mkRowProof (c : DbCallCtx) (isCross : Bool) (predT : Term) (unfolds : Array Ident)
    (kind hint : String) (mkRhs : Ident → PureQuotM Term) (rowVar : Ident := mkIdent `r) : CommandElabM Term := do
  if isCross && c.snapTyId?.isNone then throwErrorAt c.stx s!"internal error: missing `Snap` type for database `{c.dbInfo.shortName}`"
  return c.q do
    let pf ← mkDbProveTac unfolds kind c.opQual hint; let rhs ← mkRhs rowVar
    if isCross then `(($pf : ∀ (_dbSnap : $(c.snapTyId?.get!)) ($rowVar:ident : $(c.rowTyId)), $(c.rowInvId) $rowVar → $predT _dbSnap $rowVar = true → $rhs))
    else `(($pf : ∀ ($rowVar:ident : $(c.rowTyId)), $(c.rowInvId) $rowVar → $predT $rowVar = true → $rhs))

@[noinline] private def mkPolProof (c : DbCallCtx) (isCross hasCrossPol : Bool) (predT : Term) (polId : Ident) (kind hint : String) : CommandElabM Term :=
  mkRowProof c isCross predT #[c.rowInvId, polId] kind hint fun r =>
    if isCross && hasCrossPol then `($polId _dbSnap $(c.ctxId) $r) else `($polId $(c.ctxId) $r)

@[noinline] private def mkRowRunCallPure (c : DbCallCtx) (isOne : Bool) (qT proofT runPredT errLit encWriteT : Term) : PureQuotM Term := do
  let encReadT ← mkTblEncReadListPure c.tbl
  `($(mkIdent (if isOne then `Qed.Server.Db.dbRunOneRow else `Qed.Server.Db.dbRunRows))
    $(c.cfgId) $qT $(c.tid c.tbl `decodeRow) $(c.rowInvId) $(c.tid c.tbl `rowInvBool) $(c.tid c.tbl `rowInvBool_sound)
    $proofT $runPredT $errLit $(c.txOptT) $encWriteT $encReadT)

@[noinline] private def lowerDbSelect (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossReadPolicy)
  let pf ← mkPolProof c isCross c.tbl.hasCrossReadPolicy predT c.readPolId c.readPolKind c.readPolHint
  if c.opName == "count" then
    return (c.q `(Qed.Server.Db.dbCount $(c.cfgId) (Qed.Server.Db.SqlQuery.count $(c.tblSqlId) $sqlW) $pf $(c.txOptT)), false)
  let isOne := c.opName == "findOne" || c.opName == "findOneMeta"
  let (ordT, limT, offT) ← if !isOne then parseQueryWindow c.qctx c.tbl c.lowerVal c.findNamed
    else pure (← parseOrderByArg c.qctx c.tbl (c.findNamed "orderBy"), c.q `(some 1), c.q `(none))
  let mkProjCall (colsT decT encT : Term) : Term := c.q do
    let qT ← `(Qed.Server.Db.SqlQuery.select $(c.tblSqlId) $colsT $sqlW $ordT $limT $offT)
    `($(mkIdent (if isOne then `Qed.Server.Db.dbFindOneProj else `Qed.Server.Db.dbSelectProj)) $(c.cfgId) $qT $decT $pf $(c.txOptT) $encT)
  if c.opName == "selectMeta" || c.opName == "findOneMeta" then
    unless c.tbl.hasMeta do
      throwErrorAt c.stx s!"`{c.opName}` is only available on tables with both encrypted and non-encrypted columns (`{c.qualName}` can use `{if isOne then "findOne" else "select"}` directly)"
    return (mkProjCall (c.tid c.tbl `metaColumns) (c.tid c.tbl `decodeMetaRow) (c.q `([])), false)
  if let some colsStx := c.findNamed "columns" then
    let uCols := unwrapParens1 colsStx
    unless uCols.getKind == ``qedArrLit do throwErrorAt colsStx "`columns` must be a non-empty array of string column names (e.g. `columns = [\"id\", \"title\"]`)"
    let rawColStxs := (uCols.getArg 1).getSepArgs
    if rawColStxs.isEmpty then throwErrorAt colsStx "`columns = [...]` must specify at least one column"
    let mut projCols : Array (Syntax × DbColumnInfo) := #[]; let mut seenCols : Array String := #[]
    for cs in rawColStxs do
      let some cn := parseStrLitArg? cs | throwErrorAt cs "`columns` entries must be string literal column names"
      let some ci := c.tbl.columns.find? (·.name == cn) | throwErrorAt cs s!"unknown column `{cn}` on table `{c.tbl.tableName}`"
      if seenCols.contains cn then throwErrorAt cs s!"duplicate column `{cn}` in `columns = [...]`"
      seenCols := seenCols.push cn; projCols := projCols.push (cs, ci)
    let (colsT, decFnT, encT) := c.q do
      let projColIdTs ← projCols.mapM fun (_, ci) => mkSqlIdentTermPure ci.name
      let projEncTs ← mkColsEncPairs c.tbl.tableName (projCols.map fun (_, ci) => (ci.name, ci.encKey?)) fun _ idx => Syntax.mkNumLit (toString idx)
      let colDecs ← projCols.zipIdx.mapM fun ((cs, ci), idx) => do
        return (mkIdent (Name.mkSimple s!"_pc{idx}"), ci.name, ← `(Qed.Server.Db.fromSqlOfField (fun (_r : $(c.rowTyId)) => _r.$(mkIdentFrom cs (Name.mkSimple ci.name)))))
      let pvalsId := mkIdent `_pvals
      let body ← mkDecodeRowBody pvalsId colDecs (← buildTupleVal (colDecs.map fun (id, _, _) => (⟨id.raw⟩ : Term)))
      return (← `([$[$projColIdTs:term],*]), ← `(fun ($pvalsId:ident : Qed.Server.Db.DbRow) => $body), ← `([$[$projEncTs:term],*]))
    return (mkProjCall colsT decFnT encT, false)
  return (c.q do
    let qT ← `(Qed.Server.Db.SqlQuery.select $(c.tblSqlId) $(c.allColsT) $sqlW $ordT $limT $offT)
    let runPredT ← if isCross then `(fun (_ : $(c.rowTyId)) => true) else pure predT
    let errLit := Syntax.mkStrLit (if isCross then "database row violated verified table invariant" else "database row violated verified table invariant or query predicate")
    mkRowRunCallPure c isOne qT pf runPredT errLit (← `([])), false)

@[noinline] private def lowerDbAgg (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some colStx := (c.findNamed "col").orElse fun _ => c.posArgs[0]?
    | throwErrorAt c.stx s!"`{c.qualName}.{c.opName}` requires a column selector (e.g. `\"{c.tbl.columns[0]?.map (·.name) |>.getD "col"}\"` or `col = \"...\"`)"
  let colInfo ← parseAggColArg c.tbl colStx
  let aggWhere? := (c.findNamed "where").orElse fun _ => (c.findNamed "filter").orElse fun _ => if (c.findNamed "col").isSome then c.posArgs[0]? else c.posArgs[1]?
  let (predT, sqlW, _, isCross) ← c.parseWhere aggWhere? c.tbl.hasCrossReadPolicy
  let pf ← mkPolProof c isCross c.tbl.hasCrossReadPolicy predT c.readPolId c.readPolKind c.readPolHint
  return (c.q do
    let aggOp := mkIdent <| match c.opName with | "sum" => `Qed.Server.Db.SqlAggOp.sum | "min" => `Qed.Server.Db.SqlAggOp.min | _ => `Qed.Server.Db.SqlAggOp.max
    let qT ← `(Qed.Server.Db.SqlQuery.aggregate $aggOp $(c.tblSqlId) $(← mkSqlIdentTermPure colInfo.name) $sqlW)
    if c.opName == "sum" then `($(mkIdent (if colInfo.isNat then `Qed.Server.Db.dbSumNat else `Qed.Server.Db.dbSumInt)) $(c.cfgId) $qT $pf $(c.txOptT))
    else `(Qed.Server.Db.dbAggOpt $(c.cfgId) $qT (fun (_r : $(c.rowTyId)) => _r.$(mkIdentFrom colStx (Name.mkSimple colInfo.name))) $pf $(c.txOptT)), false)

@[noinline] private def lowerDbJoin (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some rStx := (c.findNamed "table").orElse fun _ => (c.findNamed "with").orElse fun _ => c.posArgs[0]?
    | throwErrorAt c.stx s!"`{c.qualName}.join` requires a target table name (e.g. `join(\"books\", where = ...)` )"
  let uRt := unwrapParens1 rStx
  let rName ← if let some s := parseStrLitArg? rStx then pure s
    else if uRt.getKind == ``qedIdent then pure (uRt.getArg 0).getId.eraseMacroScopes.toString
    else throwErrorAt rStx "`join` target table must be a string table name (e.g. `\"books\"`)"
  let rightTbl ← findDbTable rStx c.dbInfo rName
  if c.tbl.hasCrossReadPolicy || rightTbl.hasCrossReadPolicy ||
     (c.findNamed "where").any (stxAny (·.getKind == ``qedAnyIn)) || (c.findNamed "rightWhere").any (stxAny (·.getKind == ``qedAnyIn)) then
    throwErrorAt c.stx "cross-table `any ... in ...:` predicates/policies are not supported inside `.join(...)`; query the table directly with `any ... in ...:` in `where`"
  let onCol? ← (c.findNamed "on").mapM fun o => match parseStrLitArg? o with | some s => pure s | none => throwErrorAt o "`on` must be a string column name"
  let some (lCol, rCol) := (c.tbl.columns.findSome? fun col => col.refs?.bind fun (rt, rc) => if rt == rightTbl.tableName && onCol?.all (· == col.name) then some (col.name, rc) else none).orElse fun _ =>
      rightTbl.columns.findSome? fun col => col.refs?.bind fun (rt, rc) => if rt == c.tbl.tableName && onCol?.all (· == rc) then some (rc, col.name) else none
    | throwErrorAt c.stx s!"cannot `join` `{c.tbl.tableName}` with `{rightTbl.tableName}`: no `references` foreign key links these tables"
  let rRowTyId := mkIdentFrom c.stx rightTbl.rowTypeConst
  let (lPredT, lSqlW, _, _) ← c.parseWhere (c.findNamed "where")
  let (rPredT, rSqlW, _, _) ← c.parseWhere (c.findNamed "rightWhere") false rightTbl rRowTyId
  let (ordT, limT, offT) ← parseQueryWindow c.qctx c.tbl c.lowerVal c.findNamed
  return (c.q do
    let (rTblSqlId, rAllColsT) ← mkTblSqlPartsPure rightTbl
    let qT ← `(Qed.Server.Db.SqlQuery.joinSelect $(c.tblSqlId) $rTblSqlId $(c.allColsT) $rAllColsT $(← mkSqlIdentTermPure lCol) $(← mkSqlIdentTermPure rCol) $lSqlW $rSqlW $ordT $limT $offT)
    let lPf ← mkDbProveTac #[c.rowInvId, c.readPolId] c.readPolKind c.opQual c.readPolHint
    let rPf ← mkDbProveTac #[c.tid rightTbl `RowInv, c.tid rightTbl `ReadPolicy] s!"read policy `{c.dbInfo.shortName}.{rightTbl.tableName}.read` (joined table)" c.opQual (c.readPolHint rightTbl "`rightWhere = r => ...`" "the joined table's")
    let joinEncElems := (← mkTblEncReadPure c.tbl) ++ (← mkTblEncReadPure rightTbl c.tbl.columns.size)
    `(Qed.Server.Db.dbJoinSelect $(c.cfgId) $qT $(Syntax.mkNumLit (toString c.tbl.columns.size))
        $(c.tid c.tbl `decodeRow) $(c.tid rightTbl `decodeRow) $(c.rowInvId) $(c.tid c.tbl `rowInvBool) $(c.tid c.tbl `rowInvBool_sound)
        $(c.tid rightTbl `RowInv) $(c.tid rightTbl `rowInvBool) $(c.tid rightTbl `rowInvBool_sound)
        $lPredT $rPredT (fun (_l : $(c.rowTyId)) => _l.$(mkIdentFrom c.stx (Name.mkSimple lCol))) (fun (_r : $rRowTyId) => _r.$(mkIdentFrom c.stx (Name.mkSimple rCol)))
        $(c.readPolId) $(c.tid rightTbl `ReadPolicy) $(c.ctxId) $lPf $rPf $(c.txOptT) [$[$joinEncElems:term],*]), false)

@[noinline] private def parseConflictCols (c : DbCallCtx) (onArg? : Option Syntax) (reqTarget : Bool) : CommandElabM (Array DbColumnInfo) := do
  let cis ← match onArg? with
    | some oStx =>
        let rawNames : Array (Syntax × String) ← if let some cName := parseStrLitArg? oStx then pure #[(oStx, cName)]
          else
            let uo := unwrapParens1 oStx
            if uo.getKind == ``qedArrLit then
              let elems := (uo.getArg 1).getSepArgs
              if elems.isEmpty then throwErrorAt oStx s!"`{c.opName}` conflict target `on`/`conflict` cannot be empty"
              elems.mapM fun el => do
                let some cn := parseStrLitArg? el | throwErrorAt el s!"`{c.opName}` conflict target `on`/`conflict` elements must be column name strings (e.g. `on = [\"orgId\", \"slug\"]`)"
                pure (el, cn)
            else throwErrorAt oStx s!"`{c.opName}` conflict target `on`/`conflict` must be a column name string or list of column name strings (e.g. `on = \"id\"` or `on = [\"a\", \"b\"]`)"
        let cis ← rawNames.mapM fun (ref, cn) => findDbCol ref c.tbl cn
        if cis.size == 1 && !(cis[0]!.isPrimaryKey || cis[0]!.isUnique) then
          throwErrorAt rawNames[0]!.1 s!"`{c.opName}` conflict column `{c.tbl.tableName}.{cis[0]!.name}` must be `primary_key` or `unique`"
        pure cis
    | none =>
        if !reqTarget then pure #[]
        else
          let some pkCol := c.tbl.columns.find? (·.isPrimaryKey) | throwErrorAt c.stx s!"`{c.qualName}.upsert` requires a `primary_key` column or explicit `on = \"<unique_col>\"`"
          pure #[pkCol]
  for cc in cis do if cc.encKey?.isSome then throwErrorAt c.stx s!"cannot `{c.opName}` on encrypted column `{c.tbl.tableName}.{cc.name}`"
  return cis

@[noinline] private def mkWriteCallPure (c : DbCallCtx) (rowTerm : Term) (conflictCols : Array DbColumnInfo)
    (conflictW? : Option (Term × Term)) (hasConflictWhere : Bool) : PureQuotM Term := do
  let (rowVar, insPolId) := (mkIdent `_insRow, c.tid c.tbl `InsertPolicy)
  let insPolArg : Term ← if c.tbl.hasCrossInsertPolicy then `(fun (_c : Qed.Server.RequestCtx) (_r : $(c.rowTyId)) => ∀ (_dbSnap : $(c.snapTyId?.get!)), $insPolId _dbSnap _c _r) else pure (insPolId : Term)
  let pairTs ← c.tbl.columns.mapM fun col => do `(($(← mkSqlIdentTermPure col.name), Qed.Server.Db.ToSql.toSql (($rowVar).$(mkIdentFrom c.stx (Name.mkSimple col.name)))))
  let invPf ← mkDbProveTac #[c.rowInvId] s!"table constraint `{c.qualName}.RowInv`" c.opQual "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
  let insPolPf ← mkDbProveTac #[insPolId] s!"insert policy `{c.qualName}.insert`" c.opQual (mkPolHint c.tbl.insertPolicyLabel "Ensure inserted row satisfies the table's `policy insert` / `policy write`." "Ensure inserted row satisfies")
  let encWriteT ← mkTblEncWritePure c.tbl
  if c.opName == "insert" then
    `(let $rowVar:ident : $(c.rowTyId) := $rowTerm; Qed.Server.Db.dbInsert $(c.cfgId) (Qed.Server.Db.SqlQuery.insert $(c.tblSqlId) [$[$pairTs:term],*] []) $rowVar $(c.rowInvId) $insPolArg $(c.ctxId) $invPf $insPolPf $(c.txOptT) $encWriteT)
  else if c.opName == "insertOrIgnore" then
    let conflictColTs ← conflictCols.mapM fun cc => mkSqlIdentTermPure cc.name
    let retColTs ← match c.tbl.columns[0]? with | some c0 => pure #[← mkSqlIdentTermPure c0.name] | none => pure #[]
    `(let $rowVar:ident : $(c.rowTyId) := $rowTerm; Qed.Server.Db.dbInsertOrIgnore $(c.cfgId) (Qed.Server.Db.SqlQuery.insertOrIgnore $(c.tblSqlId) [$[$pairTs:term],*] [$[$conflictColTs:term],*] [$[$retColTs:term],*]) $rowVar $(c.rowInvId) $insPolArg $(c.ctxId) $invPf $insPolPf $(c.txOptT) $encWriteT)
  else
    let some (conflictPredT, conflictSqlW) := conflictW? | unreachable!
    let conflictNames := conflictCols.map (·.name)
    let conflictColTs ← conflictCols.mapM fun cc => mkSqlIdentTermPure cc.name
    let updColTs ← (c.tbl.columns.filter fun col => !col.isPrimaryKey && !col.isImmutable && !conflictNames.contains col.name).mapM fun col => mkSqlIdentTermPure col.name
    let conflictSqlOptT ← if hasConflictWhere then `(some $conflictSqlW) else `(none)
    let (updPolId, transInvId) := (c.tid c.tbl `UpdatePolicy, c.tid c.tbl `TransInv)
    let updHint := mkPolHint c.tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
    let updPolNewPf ← mkDbProveTac #[updPolId] s!"update policy `{c.qualName}.update`" c.opQual updHint
    let updPolOldPf ← mkDbProveTac #[c.rowInvId, updPolId] s!"upsert conflict update policy `{c.qualName}.update`" c.opQual updHint
    let transPf ← mkDbProveTac #[c.rowInvId, transInvId] s!"transition/monotonicity invariant `{c.qualName}.TransInv`" c.opQual "Ensure the upserted row satisfies all `old(...)` and `transition` invariants against any conflicting row."
    `(let $rowVar:ident : $(c.rowTyId) := $rowTerm; Qed.Server.Db.dbUpsert $(c.cfgId)
        (Qed.Server.Db.SqlQuery.upsert $(c.tblSqlId) [$[$pairTs:term],*] [$[$conflictColTs:term],*] [$[$updColTs:term],*] $conflictSqlOptT $(c.allColsT))
        $rowVar $(c.tid c.tbl `decodeRow) $(c.rowInvId) $(c.tid c.tbl `rowInvBool) $(c.tid c.tbl `rowInvBool_sound) $transInvId $conflictPredT
        $insPolArg $updPolId $(c.ctxId) $invPf $insPolPf $updPolNewPf $updPolOldPf $transPf $(c.txOptT) $encWriteT $(← mkTblEncReadListPure c.tbl))

@[noinline] private def lowerDbWrite (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  if c.opName == "delete" then
    let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossDeletePolicy)
    let delHint := mkPolHint c.tbl.deletePolicyLabel "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`." "Ensure `where = r => ...` implies"
    let pf ← mkPolProof c isCross c.tbl.hasCrossDeletePolicy predT (c.tid c.tbl `DeletePolicy) s!"delete policy `{c.qualName}.delete`" delHint
    return (c.q `(Qed.Server.Db.dbDelete $(c.cfgId) (Qed.Server.Db.SqlQuery.delete $(c.tblSqlId) $sqlW []) $pf $(c.txOptT)), true)
  let hasCol (nm : String) := c.tbl.columns.any (·.name == nm)
  let isConflictWhere (s : Syntax) := (unwrapParens1 s).getKind == ``qedLam1 || !hasCol "where"
  let allowsConflict := c.opName == "upsert" || c.opName == "insertOrIgnore"
  let onArg? := if allowsConflict then (c.findNamed "conflict").orElse fun _ => if !hasCol "on" then c.findNamed "on" else none else none
  let conflictWhereStx? := if c.opName == "upsert" then (c.findNamed "where").filter isConflictWhere else none
  let rowNamedArgs := if allowsConflict then
      c.namedArgs.filter fun (k, s) => !(k == "conflict" || (k == "on" && !hasCol "on") || (c.opName == "upsert" && k == "where" && isConflictWhere s))
    else c.namedArgs
  let rowTerm ← if c.posArgs.size == 1 && rowNamedArgs.isEmpty then c.lowerVal c.posArgs[0]!
    else if c.posArgs.isEmpty && !rowNamedArgs.isEmpty then
      for (k, _) in rowNamedArgs do let _ ← findDbCol c.stx c.tbl k (fun col t => s!"unknown column `{col}` in `{c.dbInfo.shortName}.{t}.{c.opName}`")
      let findRowNamed := findNamedArg? rowNamedArgs
      let (fIds, fVals) := (← c.tbl.columns.mapM fun col => do
        let fId := mkIdentFrom c.stx (Name.mkSimple col.name)
        match findRowNamed col.name with
        | some v => return (fId, c.q (c.wrapField (← c.lowerVal v)))
        | none => if col.isNullable then return (fId, c.q `(none)) else throwErrorAt c.stx s!"`{c.qualName}.{c.opName}` is missing required column `{col.name}`").unzip
      pure <| c.q `({ $[$fIds:ident := $fVals:term],* : $(c.rowTyId) })
    else throwErrorAt c.stx s!"`{c.qualName}.{c.opName}` expects named column arguments (`col = val, ...`) or a single `{c.qualName}` row value"
  if c.tbl.hasCrossInsertPolicy && c.snapTyId?.isNone then throwErrorAt c.stx s!"internal error: missing `Snap` type for database `{c.dbInfo.shortName}`"
  let (conflictCols, conflictW?) ← if c.opName == "insert" then pure (#[], none)
    else if c.opName == "insertOrIgnore" then pure (← parseConflictCols c onArg? false, none)
    else
      if c.tbl.hasCrossUpdatePolicy || conflictWhereStx?.any (stxAny (·.getKind == ``qedAnyIn)) then
        throwErrorAt c.stx "cross-table `any ... in ...:` is not supported in `.upsert(...)`; use `insertOrIgnore` + `updateOne` inside `transaction`"
      let cis ← parseConflictCols c onArg? true
      let (cp, cw, _, _) ← c.parseWhere conflictWhereStx?
      pure (cis, some (cp, cw))
  return (c.q (mkWriteCallPure c rowTerm conflictCols conflictW? conflictWhereStx?.isSome), true)

@[noinline] private def lowerDbUpdateField (c : DbCallCtx) (setRowVar postRowVar : Ident) (setRowName : String) (isCross : Bool) (sf : Syntax) :
    CommandElabM (String × Ident × Term × Term × Option Term × Option (String × Ident × Term)) := do
  let colId : Ident := ⟨sf.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
  let setOp := (sf.getArg 1).getAtomVal; let valStx := sf.getArg 2; let colInfo ← findDbCol colId c.tbl colName
  if colInfo.isImmutable then throwErrorAt colId s!"cannot update `immutable` column `{c.qualName}.{colName}` in `{c.fnName}`"
  let fId := mkIdentFrom colId (Name.mkSimple colName); let colSqlId := c.q (mkSqlIdentTermPure colName)
  let valMentionsRow := stxMentionsVar setRowName valStx
  let lowerSetSql (wrappedVal : Term) : CommandElabM Term :=
    if !valMentionsRow && !isBoolLitStx valStx then pure <| c.q (mkTypedSqlParamTerm c.rowTyId fId wrappedVal)
    else lowerRowSqlExprGo c.qctx c.lowerValWithLocals c.dbInfo #[(setRowName, c.tbl, c.tbl.tableName)] valStx
  if setOp == "+=" || setOp == "-=" then
    if colInfo.encKey?.isSome then throwErrorAt valStx s!"cannot update encrypted column `{c.qualName}.{colName}` using `{setOp}`"
    if !(colInfo.isNat || colInfo.isInt) || colInfo.isNullable then
      throwErrorAt colId s!"atomic `{setOp}` requires a non-null integer (`Nat` or `Int`) column, but `{c.tbl.tableName}.{colName}` is not"
    let deltaT := c.q (c.wrapField (← c.lowerValWithLocals #[setRowName] valStx)); let deltaSqlT ← lowerSetSql deltaT
    let (lv, sp) := c.q do
      if setOp == "+=" then return (← `(($setRowVar.$fId + $deltaT)), ← `(($colSqlId, Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.add (Qed.Server.Db.SqlExpr.col $colSqlId) $deltaSqlT)))
      else return (← `(($setRowVar.$fId - $deltaT)), ← `(($colSqlId, Qed.Server.Db.SqlExpr.binOp Qed.Server.Db.SqlBinOp.sub (Qed.Server.Db.SqlExpr.col $colSqlId) $deltaSqlT)))
    return (colName, fId, lv, sp, none, if setOp == "-=" && colInfo.isNat then some (colName, fId, deltaT) else none)
  else
    if colInfo.encKey?.isSome && valMentionsRow then
      throwErrorAt valStx s!"cannot update encrypted column `{c.qualName}.{colName}` using a row-dependent SQL expression"
    let rhsVal := c.q (c.wrapField (← c.lowerValWithLocals #[setRowName] valStx)); let sqlValT ← lowerSetSql rhsVal
    let (sp, post?) := c.q do
      return (← `(($colSqlId, $sqlValT)), ← if !valMentionsRow && !isCross then some <$> `(($postRowVar.$fId == $rhsVal)) else pure none)
    return (colName, fId, rhsVal, sp, post?, none)

@[noinline] private def lowerDbUpdate (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some setRaw := c.findNamed "set" | throwErrorAt c.stx s!"`{c.qualName}.{c.opName}` requires `set = r => \{ col = expr, ... }`"
  let (predT, sqlW, whereInfo?, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossUpdatePolicy)
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
  let mut sqlSetPairs : Array Term := #[]; let mut postChecks : Array Term := #[]; let mut underflows : Array (String × Ident × Term) := #[]
  for sf in setFields do
    let (cn, fId, lv, sp, post?, uf?) ← lowerDbUpdateField c setRowVar postRowVar setRowName isCross sf
    setColNames := setColNames.push cn; leanFIds := leanFIds.push fId; leanFVals := leanFVals.push lv; sqlSetPairs := sqlSetPairs.push sp
    if let some p := post? then postChecks := postChecks.push p
    if let some u := uf? then underflows := underflows.push u
  if !isCross then if let some (wRowName, wBody) := whereInfo? then
    let colNames := c.tbl.columns.map (·.name)
    for conj in splitAndStx wBody do
      let touched := stxCollectRowCols wRowName colNames conj
      if !touched.isEmpty && touched.all (!setColNames.contains ·) then
        postChecks := postChecks.push (c.q `((fun ($(mkIdent (Name.mkSimple wRowName)):ident : $(c.rowTyId)) => ($(← c.lowerValWithLocals #[wRowName] conj) : Bool)) $postRowVar))
  let setFnT := c.q `(fun ($setRowVar:ident : $(c.rowTyId)) => { $setRowVar with $[$leanFIds:ident := $leanFVals:term],* })
  let (updPolId, transInvId) := (c.tid c.tbl `UpdatePolicy, c.tid c.tbl `TransInv)
  let polHint := mkPolHint c.tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
  let polOldPf ← mkPolProof c isCross c.tbl.hasCrossUpdatePolicy predT updPolId s!"update policy `{c.qualName}.update`" polHint
  let polNewPf ← mkRowProof c isCross predT #[c.rowInvId, updPolId] s!"post-update policy `{c.qualName}.update` (anti-hijack)" polHint fun r =>
    if isCross && c.tbl.hasCrossUpdatePolicy then `($updPolId _dbSnap $(c.ctxId) ($setFnT $r)) else `($updPolId $(c.ctxId) ($setFnT $r))
  let invPf ← mkRowProof c isCross predT #[c.rowInvId] s!"table constraint `{c.qualName}.RowInv`" "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`." fun r => `($(c.rowInvId) ($setFnT $r))
  let transPf ← mkRowProof c isCross predT #[c.rowInvId, transInvId] s!"transition/monotonicity invariant `{c.qualName}.TransInv`" "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants." fun r => `($transInvId $r ($setFnT $r))
  let ufPfs ← underflows.mapM fun (cn, fId, deltaT) =>
    mkRowProof c isCross predT #[c.rowInvId] s!"Nat non-underflow for `{c.tbl.tableName}.{cn} -= ...`"
      s!"Guard the update in `where = r => r.{cn} >= ...` so SQL subtraction cannot go negative." (fun r => `($deltaT ≤ $r.$fId)) setRowVar
  return (c.q do
    let qT ← `(Qed.Server.Db.SqlQuery.update $(c.tblSqlId) [$[$sqlSetPairs:term],*] $sqlW $(c.allColsT))
    let hAll ← `(And.intro $polOldPf (And.intro $polNewPf (And.intro $invPf $transPf)))
    let runPredT ← if isCross then `(fun (_ : $(c.rowTyId)) => true) else `(fun ($postRowVar:ident : $(c.rowTyId)) => $(← mkBoolConj postChecks))
    let isOne := c.opName == "updateOne"
    let errLit := Syntax.mkStrLit (if isCross then "updated database row violated verified table invariant" else if isOne then "updated database row violated verified table invariant or postcondition" else "database row violated verified table invariant or query predicate")
    let baseCall ← mkRowRunCallPure c isOne qT hAll runPredT errLit (← mkTblEncWritePure c.tbl)
    ufPfs.foldrM (init := baseCall) fun pf acc => `(have _ := $pf; $acc), true)

@[noinline] def lowerDbCall (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (fnName : String) (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String)
    (rawArgs : Array Syntax) (txIdTerm? : Option Term := none) (wrapField : Term → PureQuotM Term := pure)
    (ctxTerm? : Option Term := none) : CommandElabM (Term × Bool) := do
  let qctx ← getPureQuotCtx; let cfgId := mkIdentFrom stx dbInfo.configConst
  let txOptT : Term := runQuot qctx (match txIdTerm? with | some tid => `(some $tid) | none => `(none))
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then throwErrorAt stx "`ensureSchema()` takes no arguments"
      return (runQuot qctx `($(mkIdentFrom stx dbInfo.ensureSchemaConst)), true)
  | [_, tblName, opName] =>
      let tbl ← findDbTable stx dbInfo tblName
      let (tblSqlId, allColsT) := runQuot qctx (mkTblSqlPartsPure tbl)
      let (posArgs, namedArgs) ← splitCallArgs "database" rawArgs (allowWhere := true)
      let findNamed := findNamedArg? namedArgs
      let c : DbCallCtx := {
        qctx, lowerValWithLocals, fnName, dbInfo, stx, tbl, opName,
        opQual := s!"{fnName} → {dbInfo.shortName}.{tbl.tableName}.{opName}",
        cfgId, txOptT, ctxId := ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩,
        rowTyId := mkIdentFrom stx tbl.rowTypeConst, rowInvId := mkIdentFrom stx (tbl.rowTypeConst ++ `RowInv),
        readPolId := mkIdentFrom stx (tbl.rowTypeConst ++ `ReadPolicy), tblSqlId, allColsT,
        snapTyId? := dbInfo.snapTypeConst?.map (mkIdentFrom stx), posArgs, namedArgs,
        whereArg? := (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => posArgs[0]?, wrapField }
      match opName with
      | "select" | "findOne" | "count" | "selectMeta" | "findOneMeta" => lowerDbSelect c
      | "sum" | "min" | "max" => lowerDbAgg c
      | "join" => lowerDbJoin c
      | "delete" | "insert" | "insertOrIgnore" | "upsert" => lowerDbWrite c
      | "update" | "updateOne" => lowerDbUpdate c
      | _ => throwErrorAt stx s!"unknown database table method `{opName}` on `{c.qualName}` (expected `select`, `findOne`, `count`, `sum`, `min`, `max`, `join`, `insert`, `insertOrIgnore`, `upsert`, `update`, `updateOne`, or `delete`)"
  | _ => throwErrorAt stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`"

end QueryHelpers
end Qed.Server.Db
