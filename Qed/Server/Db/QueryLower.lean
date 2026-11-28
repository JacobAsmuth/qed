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

private def sqlCmpSpecs : Array (String × Lean.Name × String) := #[
  ("==", `Qed.Server.Db.SqlBinOp.eq, "="),  ("!=", `Qed.Server.Db.SqlBinOp.ne, "<>"),
  ("<",  `Qed.Server.Db.SqlBinOp.lt, "<"),  ("<=", `Qed.Server.Db.SqlBinOp.le, "<="),
  (">",  `Qed.Server.Db.SqlBinOp.gt, ">"),  (">=", `Qed.Server.Db.SqlBinOp.ge, ">=")]

def matchSqlCmpOp? (opStr : String) : Option (Lean.Name × String) :=
  (sqlCmpSpecs.find? (·.1 == opStr)).map fun (_, opNm, sqlOp) => (opNm, sqlOp)

private def sqlBinOps : Array (Lean.Name × Lean.Name) := #[
  (``qedAdd, `Qed.Server.Db.SqlBinOp.add), (``qedSub, `Qed.Server.Db.SqlBinOp.sub),
  (``qedMul, `Qed.Server.Db.SqlBinOp.mul), (``qedAnd, `Qed.Server.Db.SqlBinOp.and), (``qedOr, `Qed.Server.Db.SqlBinOp.or)]

private def sqlStrMethods : Array (String × Lean.Name) := #[
  ("startsWith", `Qed.Server.Db.SqlExpr.startsWith), ("contains", `Qed.Server.Db.SqlExpr.contains), ("like", `Qed.Server.Db.SqlExpr.like)]

def isIdentNamed (s : Lean.Syntax) (p : Lean.Name → Bool) : Bool :=
  let u := unwrapParens1 s; u.getKind == ``qedIdent && p (u.getArg 0).getId.eraseMacroScopes

def isNoneIdent? (s : Lean.Syntax) : Bool := isIdentNamed s (· == `none)

def extractSomeCall? (s : Lean.Syntax) : Option Lean.Syntax :=
  let u := unwrapParens1 s
  if u.getKind == ``qedCall then
    let c := u.getArg 0; let args := (u.getArg 2).getSepArgs
    if c.getKind == ``qedIdent && (c.getArg 0).getId.eraseMacroScopes == `some && args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      some (args[0]!.getArg 0)
    else none
  else none

/-- Match a row column or `.length` reference (`col`, `rv.col`, `col.length`, `rv.col.length`). -/
def matchRowColRef? (hasScope hasUnqualCol : String → Bool) (u : Lean.Syntax) : Option (Option String × String × Bool) :=
  match extractDottedChain? (unwrapParens1 u) with
  | some [rv, col] => if hasScope rv then some (some rv, col, false) else if col == "length" && hasUnqualCol rv then some (none, rv, true) else none
  | some [col] => if hasUnqualCol col then some (none, col, false) else none
  | some [rv, col, "length"] => if hasScope rv then some (some rv, col, true) else none
  | _ => none

section PureBuilders
open Lean

@[noinline] def mkAppC (fn : Name) (args : Array Term) : PureQuotM Term := mkAppTermsPure (mkCIdent fn) args
@[noinline] def mkListTerm (ts : Array Term) : PureQuotM Term := if ts.isEmpty then pure (mkCIdent `List.nil) else `([$[$ts:term],*])
@[noinline] def mkOptTerm : Option Term → PureQuotM Term | none => pure (mkCIdent `Option.none) | some t => mkAppC `Option.some #[t]
@[noinline] def mkPairTerm (a b : Term) : PureQuotM Term := mkAppC `Prod.mk #[a, b]
@[noinline] def mkFieldProjLam (tyId fId : Ident) : PureQuotM Term := `(fun (_r : $tyId) => _r.$fId)
@[noinline] def mkSqlIdentTermPure (raw : String) : PureQuotM Term := mkAppC `Qed.Server.Db.SqlIdent.mk #[Syntax.mkStrLit raw, mkCIdent `rfl]

@[noinline] def mkTypedSqlParamTerm (rowTyId fId : Ident) (valT : Term) : PureQuotM Term := do
  mkAppC `Qed.Server.Db.SqlExpr.param #[← mkAppC `Qed.Server.Db.toSqlLike #[← mkFieldProjLam rowTyId fId, valT]]

@[noinline] def mkEncColSpecTerm (tableName colName : String) (ek : DbEncKeyInfo) : PureQuotM Term := do
  let prevTs ← Lang.mapPQ ek.prevKeys.toArray fun (k, fb?) => mkPairTerm (Syntax.mkStrLit k) (quote fb?)
  mkAppC `Qed.Server.Db.EncColSpec.mk #[Syntax.mkStrLit ek.keyEnv, quote ek.fallback?,
    ← mkAppC `String.toUTF8 #[Syntax.mkStrLit s!"{tableName}.{colName}"], quote ek.isBytes, ← mkListTerm prevTs]

@[noinline] def mkColsEncPairs (tableName : String) (cols : Array (String × Option DbEncKeyInfo)) (mkKey : String → Nat → Term) : PureQuotM (Array Term) := do
  return (← Lang.foldlPQ cols (#[], 0) fun (out, i) (colName, encKey?) => do
    match encKey? with
    | some ek => return (out.push (← mkPairTerm (mkKey colName i) (← mkEncColSpecTerm tableName colName ek)), i + 1)
    | none => return (out, i + 1)).1

@[noinline] def mkDecodeRowBody (valsVar : Ident) (colDecs : Array (Ident × String × Term)) (retTerm : Term) : PureQuotM Term := do
  let bindIds := colDecs.map (·.1)
  let decStmts ← Lang.mapIdxPQ colDecs fun (_, colName, decFn) idx =>
    `(match ($valsVar)[$(Syntax.mkNumLit (toString idx))]? with
      | some _v => $decFn _v | none => Except.error ("missing column `" ++ $(Syntax.mkStrLit colName) ++ "` in database row"))
  `(do
    $[let $bindIds:ident ← $decStmts:term]*
    return $retTerm)

@[noinline] private def mkDbProveTac (unfolds : Array Ident) (kind op hint : String) : PureQuotM Term :=
  `(by qedDbProve [$[$unfolds],*] $(Syntax.mkStrLit kind) $(Syntax.mkStrLit op) $(Syntax.mkStrLit hint))

@[noinline] private def mkTblSqlPartsPure (tbl : DbTableInfo) : PureQuotM (Term × Term) := do
  return (← mkSqlIdentTermPure tbl.tableName, ← mkListTerm (← Lang.mapPQ tbl.columns fun c => mkSqlIdentTermPure c.name))

@[noinline] private def mkTblEncReadPure (tbl : DbTableInfo) (colOffset : Nat := 0) : PureQuotM (Array Term) :=
  mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun _ i => Syntax.mkNumLit (toString (colOffset + i))

@[noinline] private def mkTblEncWritePure (tbl : DbTableInfo) : PureQuotM Term := do
  mkListTerm (← mkColsEncPairs tbl.tableName (tbl.columns.map fun c => (c.name, c.encKey?)) fun c _ => Syntax.mkStrLit c)

@[noinline] private def mkSqlBinOpPure (op : Name) (l r : Term) : PureQuotM Term :=
  mkAppC `Qed.Server.Db.SqlExpr.binOp #[mkCIdent op, l, r]

@[noinline] private def mkSqlAndChainPure (cs : Array Term) : PureQuotM Term :=
  if h : 0 < cs.size then Lang.foldlPQ (cs.extract 1 cs.size) cs[0] (mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.and)
  else pure (mkCIdent `Qed.Server.Db.SqlExpr.litTrue)

end PureBuilders

private partial def stxCollectRowCols (rowVar : String) (colNames : Array String) (stx : Lean.Syntax) : Array String :=
  match extractDottedChain? stx with
  | some [rv, col] => if rv == rowVar && colNames.contains col then #[col] else #[]
  | _ => stx.getArgs.foldl (init := #[]) fun acc ch => (stxCollectRowCols rowVar colNames ch).foldl pushUnique acc

section QueryHelpers
open Lean Elab Command

@[noinline] def mkDbErr {α : Type} (ref : Syntax) (msg : String) : CommandElabM α := throwErrorAt ref msg

@[noinline] def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    mkDbErr ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  return (← Lang.getPureQuotCtxCmd).runPure (mkSqlIdentTermPure raw)

@[noinline] private def findDbTable (ref : Syntax) (dbInfo : DatabaseInfo) (tblName : String) : CommandElabM DbTableInfo := do
  let some tbl := dbInfo.tables.find? (·.tableName == tblName)
    | mkDbErr ref s!"database `{dbInfo.shortName}` has no table `{tblName}`{Qed.Diag.didYouMean tblName (dbInfo.tables.map (·.tableName)).toList}"
  return tbl

@[noinline] def findDbCol (ref : Syntax) (tbl : DbTableInfo) (colName : String)
    (fmtErr : String → String → String := fun c t => s!"table `{t}` has no column `{c}`") : CommandElabM DbColumnInfo := do
  let some colInfo := tbl.columns.find? (·.name == colName)
    | mkDbErr ref s!"{fmtErr colName tbl.tableName}{Qed.Diag.didYouMean colName (tbl.columns.map (·.name)).toList}"
  return colInfo

private def parseStrLitArg? (stx : Syntax) : Option String :=
  let u := unwrapParens1 stx; if u.getKind == ``qedLitStr then some (⟨u.getArg 0⟩ : TSyntax `str).getString else none

private def mkPolHint (label fallback pfx : String) : String := if label.isEmpty then fallback else s!"{pfx} `{label}`."

@[noinline] private def parseColNameList (tbl : DbTableInfo) (stx : Syntax) (label : String)
    (allowSingleStr : Bool) (forbidDup : Bool := false) (forbidEnc : Bool := false)
    (fmtErr : String → String → String := fun c t => s!"table `{t}` has no column `{c}`") : CommandElabM (Array (Syntax × DbColumnInfo)) := do
  let rawItems ←
    if allowSingleStr && (parseStrLitArg? stx).isSome then pure #[stx]
    else
      let u := unwrapParens1 stx
      unless u.getKind == ``qedArrLit do
        mkDbErr stx (if allowSingleStr then s!"{label} must be a column name string or list of column name strings (e.g. `\"id\"` or `[\"a\", \"b\"]`)"
          else s!"{label} must be a non-empty array of string column names (e.g. `[\"id\", \"title\"]`)")
      let elems := (u.getArg 1).getSepArgs
      if elems.isEmpty then mkDbErr stx s!"{label} must specify at least one column"
      pure elems
  return (← Lang.foldlCmd rawItems (#[], (#[] : Array String)) fun (out, seen) cs => do
    let some cn := parseStrLitArg? cs | mkDbErr cs s!"{label} entries must be string literal column names"
    let ci ← findDbCol cs tbl cn fmtErr
    if forbidDup && seen.contains cn then mkDbErr cs s!"duplicate column `{cn}` in {label}"
    if forbidEnc && ci.encKey?.isSome then mkDbErr cs s!"cannot use encrypted column `{tbl.tableName}.{cn}` in {label}"
    return (out.push (cs, ci), seen.push cn)).1

@[noinline] def parseDbSetItems (tbl : DbTableInfo) (items : Array Syntax) (ctxLabel : String)
    (allowCompoundOp : Bool) (forbidPk : Bool := false) (forbidImmutable : Bool := false)
    (forbidEncAll : Bool := false) (colQualPfx : String := "") : CommandElabM (Array (Ident × DbColumnInfo × String × Syntax)) :=
  Lang.mapCmd items fun item => do
    let colId : Ident := ⟨item.getArg 0⟩; let colName := colId.getId.eraseMacroScopes.toString
    let setOp := if allowCompoundOp then ((item.getArg 1).reprint.getD "=").trimAscii.toString else "="
    let col ← findDbCol colId tbl colName (fun c t => s!"{ctxLabel} references unknown column `{c}` on table `{t}`")
    if forbidPk && col.isPrimaryKey then mkDbErr colId s!"{ctxLabel} cannot modify `primary_key` column `{colName}`"
    if forbidImmutable && col.isImmutable then mkDbErr colId s!"cannot update `immutable` column `{colQualPfx}{colName}` in {ctxLabel}"
    if forbidEncAll && col.encKey?.isSome then mkDbErr colId s!"{ctxLabel} cannot modify encrypted column `{colName}`"
    return (colId, col, setOp, item.getArg 2)

private def mkQedParen (info : SourceInfo) (inner : Syntax) : Syntax :=
  Syntax.node info ``qedParen #[Syntax.atom info "(", Syntax.node info `null #[inner], Syntax.atom info ")"]

private def maybeQedParen (stx : Syntax) : Syntax :=
  let k := stx.getKind
  if k == ``qedIdent || k == ``qedProj || k == ``qedLitNum || k == ``qedLitStr || k == ``qedDotIdent || k == ``qedParen then stx
  else mkQedParen (SourceInfo.fromRef stx) stx

private partial def substDbFnBody (substMap : Std.HashMap String Syntax) (aliasMap : Std.HashMap String String)
    (counter : Nat) (stx : Syntax) : Syntax × Nat :=
  let k := stx.getKind
  if k == ``qedAnyIn then
    let aliasId := stx.getArg 1
    if aliasId.isIdent then
      let aliasStr := aliasId.getId.eraseMacroScopes.toString
      let fresh := s!"{aliasStr}_f{counter}"
      let (body', c') := substDbFnBody (substMap.erase aliasStr) (aliasMap.insert aliasStr fresh) (counter + 1) (stx.getArg 5)
      ((stx.setArg 1 (mkIdentFrom aliasId (Name.mkSimple fresh))).setArg 5 body', c')
    else (stx, counter)
  else if k == ``qedIdent then
    let id := stx.getArg 0
    if id.isIdent then
      match id.getId.eraseMacroScopes.components with
      | root :: rest =>
          let rs := root.toString
          if let some fresh := aliasMap[rs]? then
            let nm := rest.foldl (fun n c => Name.mkStr n c.toString) (Name.mkSimple fresh)
            (stx.setArg 0 (mkIdentFrom id nm), counter)
          else if let some argStx := substMap[rs]? then
            let info := SourceInfo.fromRef id
            let out := rest.foldl (fun acc f => Syntax.node info ``qedProj #[acc, Syntax.atom info ".", mkIdentFrom id f]) argStx
            (out, counter)
          else (stx, counter)
      | [] => (stx, counter)
    else (stx, counter)
  else if k == ``qedProj then
    let (b', c') := substDbFnBody substMap aliasMap counter (stx.getArg 0)
    (stx.setArg 0 b', c')
  else match stx with
    | .node info kind args =>
        let (out, c') := args.foldl (init := (Array.mkEmpty args.size, counter)) fun (acc, c) ch =>
          let (ch', c1) := substDbFnBody substMap aliasMap c ch
          (acc.push ch', c1)
        (.node info kind out, c')
    | other => (other, counter)

@[noinline] partial def expandDbFnsInStx (fns : Array DbFnInfo) (allowedPrefixes : Array String)
    (stx : Syntax) (counter : Nat := 1) (fuel : Nat := 32) : CommandElabM (Syntax × Nat) := do
  if fns.isEmpty then return (stx, counter)
  if stx.getKind == ``qedCall then
    let callee := stx.getArg 0; let rawArgs := (stx.getArg 2).getSepArgs
    let matchedFn? : Option DbFnInfo := match extractDottedChain? callee with
      | some [fnName] => fns.find? (·.name == fnName)
      | some [pfx, fnName] => if allowedPrefixes.contains pfx then fns.find? (·.name == fnName) else none
      | _ => none
    if let some fnInfo := matchedFn? then
      if fuel == 0 then mkDbErr stx s!"recursive or deeply nested `database` `fn {fnInfo.name}` expansion limit exceeded"
      if rawArgs.size != fnInfo.params.size then
        mkDbErr stx s!"database `fn {fnInfo.name}` expects {fnInfo.params.size} argument(s), got {rawArgs.size}"
      let (substMap, c1) ← Lang.foldlCmd (Array.range rawArgs.size) (({} : Std.HashMap String Syntax), counter) fun (sm, c) i => do
        let arg := rawArgs[i]!
        unless arg.getKind == ``qedCallArgPos do
          mkDbErr arg s!"database `fn {fnInfo.name}` only accepts positional arguments"
        let (argExp, c') ← expandDbFnsInStx fns allowedPrefixes (arg.getArg 0) c (fuel - 1)
        return (sm.insert fnInfo.params[i]! (maybeQedParen argExp), c')
      let (instBody, c2) := substDbFnBody substMap {} c1 fnInfo.bodyStx
      let (expBody, c3) ← expandDbFnsInStx fns allowedPrefixes instBody c2 (fuel - 1)
      return (maybeQedParen expBody, c3)
  match stx with
  | .node info kind args =>
      let (out, c') ← Lang.foldlCmd args (Array.mkEmpty args.size, counter) fun (acc, c) ch => do
        let (ch', c1) ← expandDbFnsInStx fns allowedPrefixes ch c fuel
        return (acc.push ch', c1)
      return (.node info kind out, c')
  | other => return (other, counter)

private partial def isExactRowColRef (rName col : String) (s : Syntax) : Bool :=
  match extractDottedChain? s with
  | some [rv, cn] => rv == rName && cn == col
  | _ => match extractSomeCall? s with | some inner => isExactRowColRef rName col inner | none => false

private def isExactEqOnCol (rName col : String) (conj : Syntax) : Bool :=
  let u := unwrapParens1 conj
  if u.getKind != ``qedCmp then false
  else
    let links := (u.getArg 1).getArgs
    if links.size != 1 then false
    else
      let lk := links[0]!
      if ((lk.getArg 0).reprint.getD "").trimAscii.toString != "==" then false
      else
        let (lhs, rhs) := (u.getArg 0, lk.getArg 1)
        let isPureOuter (s : Syntax) : Bool := !stxMentionsVar rName s && !stxAny (·.getKind == ``qedAnyIn) s && !isNoneIdent? s
        (isExactRowColRef rName col lhs && isPureOuter rhs) || (isExactRowColRef rName col rhs && isPureOuter lhs)

private def whereInfoSatisfiesByCols (whereInfo? : Option (String × Syntax)) (byCols : Array String) : Bool :=
  match whereInfo? with
  | none => false
  | some (rName, wBody) =>
      let conjs := splitAndStx wBody
      byCols.all fun col => conjs.any (isExactEqOnCol rName col)

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
  let some stx := ordStx? | return mkCIdent `Option.none
  let some raw := parseStrLitArg? stx | mkDbErr stx "`orderBy` must be a string column name (e.g. `orderBy = \"id\"` or `orderBy = \"-version\"`)"
  let (colName, isDesc) := if raw.startsWith "-" then (String.ofList (raw.toList.drop 1), true) else (raw, false)
  let colInfo ← findDbCol stx tbl colName (fun c t => s!"`orderBy` references unknown column `{c}` on table `{t}`")
  if colInfo.encKey?.isSome then mkDbErr stx s!"cannot `orderBy` encrypted column `{tbl.tableName}.{colName}` (AES-256-GCM uses randomized nonces)"
  return qctx.runPure do mkOptTerm (some (← mkPairTerm (← mkSqlIdentTermPure colName) (mkCIdent (if isDesc then `Qed.Server.Db.SqlOrderDir.desc else `Qed.Server.Db.SqlOrderDir.asc))))

@[noinline] private def parseAggColArg (tbl : DbTableInfo) (colStx : Syntax) : CommandElabM DbColumnInfo := do
  let u := unwrapParens1 colStx; let errMsg := "aggregate column selector must be a column name string (e.g. `\"stock\"`) or `r => r.col`"
  let colName ← if let some s := parseStrLitArg? colStx then pure s
    else if u.getKind == ``qedLam1 then
      let b := u.getArg 0; let rName := if b.isIdent then b.getId.eraseMacroScopes.toString else ""
      match extractDottedChain? (u.getArg 2) with | some [rv, col] => if rv == rName then pure col else mkDbErr colStx errMsg | _ => mkDbErr colStx errMsg
    else mkDbErr colStx errMsg
  let colInfo ← findDbCol colStx tbl colName
  if colInfo.encKey?.isSome then mkDbErr colStx s!"cannot compute SQL aggregate on encrypted column `{tbl.tableName}.{colName}`"
  return colInfo

@[noinline] private def lowerRowSqlCol? (qctx : PureQuotCtx) (scopes : Array (String × DbTableInfo × String)) (u : Syntax) : CommandElabM (Option Term) := do
  let rev := scopes.reverse; let findUnqual? := rev.find? (·.1.isEmpty)
  let some (scope?, col, asLen) := matchRowColRef? (fun rv => rev.any (·.1 == rv)) (fun c => findUnqual?.any fun (_, t, _) => t.columns.any (·.name == c)) u | return none
  let scopeHit? : Option (String × DbTableInfo × String) := match scope? with | some rv => rev.find? (·.1 == rv) | none => findUnqual?
  let some (_, stbl, sqlQual) := scopeHit? | return none
  let colInfo ← match scope?, asLen with
    | some _, false => findDbCol u stbl col
    | _, _ => match stbl.columns.find? (·.name == col) with | some ci => pure ci | none => return none
  if colInfo.encKey?.isSome then
    mkDbErr u s!"cannot reference encrypted column `{stbl.tableName}.{col}` inside SQL `where` or row-dependent `set` expression (AES-256-GCM uses randomized nonces)"
  return some <| qctx.runPure do
    let base ← if scopes.size > 1 then mkAppC `Qed.Server.Db.SqlExpr.qualCol #[← mkSqlIdentTermPure sqlQual, ← mkSqlIdentTermPure col]
      else mkAppC `Qed.Server.Db.SqlExpr.col #[← mkSqlIdentTermPure col]
    if asLen then mkAppC `Qed.Server.Db.SqlExpr.strLen #[base] else pure base

@[noinline] private def lowerRowSqlMethod (qctx : PureQuotCtx) (mentionsScope : Syntax → Bool)
    (lowerVal sub : Syntax → CommandElabM Term) (u : Syntax) : CommandElabM Term := do
  if let some (recv, meth, args) := matchMethodCall? u then
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      let arg := args[0]!.getArg 0
      if meth == "contains" && !mentionsScope recv && mentionsScope arg then
        let (aSql, rVal) := (← sub arg, ← lowerVal recv)
        return qctx.runPure do mkAppC `Qed.Server.Db.SqlExpr.inList #[aSql, ← mkAppC `Qed.Server.Db.ToSqlList.toSqlList #[rVal]]
      if meth == "endsWith" then
        let (r, a) := (← sub recv, ← lowerVal arg)
        return qctx.runPure do mkAppC `Qed.Server.Db.SqlExpr.like #[r, ← mkAppC `Qed.Server.Db.SqlExpr.param #[← mkAppC `Qed.Server.Db.endsWithLikeVal #[a]]]
      if let some (_, ctor) := sqlStrMethods.find? (·.1 == meth) then
        return qctx.runPure (mkAppC ctor #[← sub recv, ← sub arg])
  mkDbErr u s!"unsupported call `{stxSnippet u}` in SQL `where`/`set` clause"

@[noinline] private def lowerRowSqlCmp (qctx : PureQuotCtx) (mentionsScope : Syntax → Bool)
    (lowerVal sub : Syntax → CommandElabM Term) (lowerSide : Syntax → Syntax → CommandElabM Term) (u : Syntax) : CommandElabM Term := do
  let (_, cs) ← Lang.foldlCmd (u.getArg 1).getArgs (u.getArg 0, #[]) fun (lhs, cs) lk => do
    let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString; let rhs := lk.getArg 1
    let c ←
      if (isNoneIdent? rhs || isNoneIdent? lhs) && (opStr == "==" || opStr == "!=") then
        pure <| qctx.runPure (mkAppC (if opStr == "==" then `Qed.Server.Db.SqlExpr.isNull else `Qed.Server.Db.SqlExpr.isNotNull) #[← sub (if isNoneIdent? rhs then lhs else rhs)])
      else if opStr == "in" || opStr == "not in" then
        if !mentionsScope rhs then
          let (l, r) := (← sub lhs, ← lowerVal rhs)
          pure <| qctx.runPure do
            let base ← mkAppC `Qed.Server.Db.SqlExpr.inList #[l, ← mkAppC `Qed.Server.Db.ToSqlList.toSqlList #[r]]
            if opStr == "not in" then mkAppC `Qed.Server.Db.SqlExpr.not #[base] else pure base
        else mkDbErr lk s!"SQL `{opStr}` requires a collection value on the right-hand side"
      else if opStr == "==" || opStr == "!=" then
        let isNe := opStr == "!="
        let lowerSomeCmp (inner other : Syntax) (swap : Bool) : CommandElabM Term := do
          if !mentionsScope other then
            return qctx.runPure (mkAppC `Qed.Server.Db.sqlEqSome #[← sub inner, ← lowerVal other, quote isNe])
          let (inSql, oSql) := (← sub inner, ← sub other); let (a, b) := if swap then (oSql, inSql) else (inSql, oSql)
          return qctx.runPure do
            if !isNe then mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.eq a b
            else mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.or (← mkAppC `Qed.Server.Db.SqlExpr.isNull #[oSql]) (← mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.ne a b)
        let mkEqBin (a b : Syntax) : CommandElabM Term := do
          return qctx.runPure (mkSqlBinOpPure (if isNe then `Qed.Server.Db.SqlBinOp.ne else `Qed.Server.Db.SqlBinOp.eq) (← lowerSide a b) (← lowerSide b a))
        match extractSomeCall? lhs, extractSomeCall? rhs with
        | some lI, some rI => mkEqBin lI rI | some lI, none => lowerSomeCmp lI rhs false | none, some rI => lowerSomeCmp rI lhs true | none, none => mkEqBin lhs rhs
      else
        let some (op, _) := matchSqlCmpOp? opStr | mkDbErr lk s!"unsupported SQL comparison operator `{opStr}`"
        pure <| qctx.runPure (mkSqlBinOpPure op (← lowerSide lhs rhs) (← lowerSide rhs lhs))
    return (rhs, cs.push c)
  return qctx.runPure (mkSqlAndChainPure cs)

@[noinline] private partial def lowerRowSqlExprGo (qctx : PureQuotCtx) (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (dbInfo : DatabaseInfo) (scopes : Array (String × DbTableInfo × String)) (stx : Syntax) (outerVar? : Option String := none) : CommandElabM Term := do
  let lowerVal := lowerValWithLocals #[]; let u := unwrapParens1 stx; let k := u.getKind
  let mentionsScope (s : Syntax) : Bool :=
    scopes.any (fun (v, tbl, _) => if v.isEmpty then tbl.columns.any (fun c => stxMentionsVar c.name s) else stxMentionsVar v s) || stxAny (·.getKind == ``qedAnyIn) s
  if k == ``qedAnyIn then
    unless (u.getArg 1).isIdent do mkDbErr (u.getArg 1) "cross-table `any <alias> in <table>:` expects a plain table alias identifier"
    let aliasId : Ident := ⟨u.getArg 1⟩; let aliasStr := aliasId.getId.eraseMacroScopes.toString
    unless isSafeSqlIdent aliasStr do mkDbErr aliasId s!"invalid SQL alias `{aliasStr}` in `any {aliasStr} in ...`"
    if scopes.any (·.1 == aliasStr) || outerVar? == some aliasStr then mkDbErr aliasId s!"alias `{aliasStr}` in `any {aliasStr} in ...` shadows an outer row/table variable"
    let tgt := unwrapParens1 (u.getArg 3)
    unless tgt.getKind == ``qedIdent do mkDbErr tgt "cross-table `any <alias> in <table>:` expects a sibling table name from the same `database`"
    let subTbl ← findDbTable tgt dbInfo (tgt.getArg 0).getId.eraseMacroScopes.toString
    let bodySql ← lowerRowSqlExprGo qctx lowerValWithLocals dbInfo (scopes.push (aliasStr, subTbl, aliasStr)) (u.getArg 5) outerVar?
    return qctx.runPure (mkAppC `Qed.Server.Db.SqlExpr.existsSubquery #[← mkSqlIdentTerm tgt subTbl.tableName, ← mkSqlIdentTerm aliasId aliasStr, bodySql])
  if !mentionsScope u then
    if k == ``qedIdent then match (u.getArg 0).getId.eraseMacroScopes with
      | `true => return mkCIdent `Qed.Server.Db.SqlExpr.litTrue | `false => return mkCIdent `Qed.Server.Db.SqlExpr.litFalse | _ => pure ()
    let vT ← lowerVal u
    return qctx.runPure do mkAppC `Qed.Server.Db.SqlExpr.param #[← mkAppC `Qed.Server.Db.ToSql.toSql #[vT]]
  if let some colT ← lowerRowSqlCol? qctx scopes u then return colT
  let sub (e : Syntax) := lowerRowSqlExprGo qctx lowerValWithLocals dbInfo scopes e outerVar?
  let lowerSide (side other : Syntax) : CommandElabM Term :=
    match extractDirectScopedCol? scopes other with
    | some (stbl, col) =>
        if !mentionsScope side && !isIdentNamed side (fun n => n == `true || n == `false) then do
          return qctx.runPure (mkTypedSqlParamTerm (mkIdentFrom side stbl.rowTypeConst) (mkIdentFrom side (Name.mkSimple col)) (← lowerVal side))
        else sub side
    | none => sub side
  if k == ``qedProj then
    if (u.getArg 2).isIdent && (u.getArg 2).getId.eraseMacroScopes == `length then
      return qctx.runPure (mkAppC `Qed.Server.Db.SqlExpr.strLen #[← sub (u.getArg 0)])
    else mkDbErr u s!"unsupported row projection `.{stxSnippet (u.getArg 2)}` inside SQL query expression"
  else if let some (_, op) := sqlBinOps.find? (·.1 == k) then return qctx.runPure (mkSqlBinOpPure op (← sub (u.getArg 0)) (← sub (u.getArg 2)))
  else if k == ``qedNot then return qctx.runPure (mkAppC `Qed.Server.Db.SqlExpr.not #[← sub (u.getArg 1)])
  else if k == ``qedCmp then lowerRowSqlCmp qctx mentionsScope lowerVal sub lowerSide u
  else if k == ``qedExprIf || k == ``qedTernary then
    let (cI, tI, elseStx?) := if k == ``qedTernary then (2, 0, extractOptElseExpr? (u.getArg 3))
      else (1, 3, desugarExprElifs? (u.getArg 4).getArgs (u.getArg 5))
    let some elseStx := elseStx? | mkDbErr u "conditional `if` inside SQL `where`/`set` clause requires an `else` branch"
    let (condStx, thenStx) := (u.getArg cI, u.getArg tI)
    if !mentionsScope condStx then
      let (cT, tSql, eSql) := (← lowerVal condStx, ← sub thenStx, ← sub elseStx)
      return qctx.runPure `(if ($cT : Bool) then $tSql else $eSql)
    else
      let (cSql, tSql, eSql) := (← sub condStx, ← sub thenStx, ← sub elseStx)
      return qctx.runPure do
        mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.or (← mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.and cSql tSql)
          (← mkSqlBinOpPure `Qed.Server.Db.SqlBinOp.and (← mkAppC `Qed.Server.Db.SqlExpr.not #[cSql]) eSql)
  else if k == ``qedExprIfLet then
    let scrutStx := u.getArg 4
    let some elseStx := desugarExprElifs? (u.getArg 7).getArgs (u.getArg 8) | mkDbErr u "conditional `if let` inside SQL `where` clause requires an `else:` branch"
    if mentionsScope scrutStx then mkDbErr scrutStx "`if let` scrutinee inside SQL `where` cannot depend on a row column; match an outer `Option` variable instead"
    let patT ← liftMacroM (lowerQedPat (u.getArg 2)); let scrutT ← lowerVal scrutStx
    let patLocals := (collectQedPatIds (u.getArg 2)).map (·.toString)
    let thenSql ← lowerRowSqlExprGo qctx (fun locs e => lowerValWithLocals (patLocals ++ locs) e) dbInfo scopes (u.getArg 6) outerVar?
    return qctx.runPure `(match $scrutT:term with | $patT:term => $thenSql | _ => $(← sub elseStx))
  else if k == ``qedCall then lowerRowSqlMethod qctx mentionsScope lowerVal sub u
  else mkDbErr u s!"unsupported expression `{stxSnippet u}` in SQL `where`/`set` clause (use row columns, comparisons, `and`/`or`/`not`, `any m in tbl:`, `in`, arithmetic, `.length`, `.startsWith`, `.contains`, `xs.contains(r.col)`, or bound variables)"

def lowerRowSqlExpr (lowerValWithLocals : Array String → Syntax → CommandElabM Term) (dbInfo : DatabaseInfo)
    (scopes : Array (String × DbTableInfo × String)) (stx : Syntax) : CommandElabM Term := do
  lowerRowSqlExprGo (← Lang.getPureQuotCtxCmd) lowerValWithLocals dbInfo scopes stx

@[noinline] private def parseWhereArg (qctx : PureQuotCtx) (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (dbInfo : DatabaseInfo) (dbAlias : String) (tbl : DbTableInfo) (rowTyId : Ident) (whereStx? : Option Syntax)
    (needCross : Bool := false) : CommandElabM (Term × Term × Option (String × Syntax) × Bool) := do
  let prefixes := #[dbAlias, dbInfo.shortName]
  let some wRaw := whereStx? | do
    let snapTyId? ← if needCross then
        let some snapConst := dbInfo.snapTypeConst? | mkDbErr rowTyId.raw s!"cross-table `any ... in ...` requires a multi-table `database` (`{dbInfo.shortName}` has no `Snap` type)"
        pure (some (mkIdent snapConst))
      else pure none
    return (qctx.runPure do
      match snapTyId? with | some sTy => `(fun (_ : $sTy) (_ : $rowTyId) => true) | none => `(fun (_ : $rowTyId) => true),
      mkCIdent `Qed.Server.Db.SqlExpr.litTrue, none, needCross)
  let u := unwrapParens1 wRaw
  if u.getKind != ``qedLam1 then mkDbErr wRaw "database `where` clause must be a row lambda, e.g. `where = r => r.id == noteId and r.ownerId == uid`"
  let b := u.getArg 0; let rId : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
  let rName := rId.getId.eraseMacroScopes.toString
  let (body, _) ← expandDbFnsInStx dbInfo.fns prefixes (u.getArg 2)
  let isCross := needCross || stxAny (·.getKind == ``qedAnyIn) body
  let snapTyId? ← if isCross then
      let some snapConst := dbInfo.snapTypeConst? | mkDbErr wRaw s!"cross-table `any ... in ...` requires a multi-table `database` (`{dbInfo.shortName}` has no `Snap` type)"
      pure (some (mkIdent snapConst))
    else pure none
  let sqlW ← lowerRowSqlExprGo qctx lowerValWithLocals dbInfo #[(rName, tbl, tbl.tableName)] body
  let predT ← match snapTyId? with
    | some sTy =>
        let snapId := mkIdent `_dbSnap
        let bVal ← lowerValWithLocals #[rName, "_dbSnap"] (rewriteSnapTables snapId (dbInfo.tables.map (·.tableName)) body)
        pure <| qctx.runPure `(fun ($snapId:ident : $sTy) ($rId:ident : $rowTyId) => ($bVal : Bool))
    | none => pure <| qctx.runPure `(fun ($rId:ident : $rowTyId) => ($(← lowerValWithLocals #[rName] body) : Bool))
  return (predT, sqlW, some (rName, body), isCross)

@[noinline] private def parseQueryWindow (qctx : PureQuotCtx) (tbl : DbTableInfo) (lowerVal : Syntax → CommandElabM Term)
    (findNamed : String → Option Syntax) : CommandElabM (Term × Term × Term) := do
  let optNat (s? : Option Syntax) : CommandElabM Term := match s? with
    | none => pure (mkCIdent `Option.none)
    | some s => do let v ← lowerVal s; pure <| qctx.runPure do mkOptTerm (some (← `(($v : Nat))))
  return (← parseOrderByArg qctx tbl (findNamed "orderBy"), ← optNat (findNamed "limit"), ← optNat (findNamed "offset"))

private structure DbCallCtx where
  qctx : PureQuotCtx
  lowerValWithLocals : Array String → Syntax → CommandElabM Term
  fnName : String
  dbAlias : String
  opName : String
  opQual : String
  dbInfo : DatabaseInfo
  stx : Syntax
  tbl : DbTableInfo
  cfgId : Ident
  rowTyId : Ident
  rowInvId : Ident
  readPolId : Ident
  txOptT : Term
  ctxId : Term
  tblSqlId : Term
  allColsT : Term
  snapTyId? : Option Ident
  posArgs : Array Syntax
  namedArgs : Array (String × Syntax)
  whereArg? : Option Syntax
  wrapField : Term → PureQuotM Term

private def DbCallCtx.q {α : Type} (c : DbCallCtx) (k : PureQuotM α) : α := c.qctx.runPure k
private def DbCallCtx.tid (c : DbCallCtx) (t : DbTableInfo) (s : Name) : Ident := mkIdentFrom c.stx (t.rowTypeConst ++ s)
private def DbCallCtx.lowerVal (c : DbCallCtx) (s : Syntax) : CommandElabM Term := c.lowerValWithLocals #[] s
private def DbCallCtx.findNamed (c : DbCallCtx) (k : String) : Option Syntax := findNamedArg? c.namedArgs k
private def DbCallCtx.qualName (c : DbCallCtx) : String := s!"{c.dbInfo.shortName}.{c.tbl.tableName}"
private def DbCallCtx.readPolKind (c : DbCallCtx) : String := s!"read policy `{c.qualName}.read`"
private def DbCallCtx.readPolHint (c : DbCallCtx) (t : DbTableInfo := c.tbl) (clause := "`where = r => ...`") (desc := "the table's") : String :=
  mkPolHint t.readPolicyLabel s!"Check {clause} against {desc} `policy read`." s!"Ensure {clause} (together with `requires` / `if` guards) implies"
private def DbCallCtx.parseWhere (c : DbCallCtx) (whereStx? : Option Syntax := c.whereArg?) (needCross := false)
    (tbl : DbTableInfo := c.tbl) (rowTyId : Ident := c.rowTyId) : CommandElabM (Term × Term × Option (String × Syntax) × Bool) :=
  parseWhereArg c.qctx c.lowerValWithLocals c.dbInfo c.dbAlias tbl rowTyId whereStx? needCross

@[noinline] private def mkRowProof (c : DbCallCtx) (isCross : Bool) (predT : Term) (unfolds : Array Ident)
    (kind hint : String) (mkRhs : Ident → PureQuotM Term) (rowVar : Ident := mkIdent `r) : CommandElabM Term := do
  if isCross && c.snapTyId?.isNone then mkDbErr c.stx s!"internal error: missing `Snap` type for database `{c.dbInfo.shortName}`"
  return c.q do
    let pf ← mkDbProveTac unfolds kind c.opQual hint; let rhs ← mkRhs rowVar; let snapVar := mkIdent `_dbSnap
    if isCross then `(($pf : ∀ ($snapVar:ident : $(c.snapTyId?.get!)) ($rowVar:ident : $(c.rowTyId)), $(c.rowInvId) $rowVar → $predT $snapVar $rowVar = true → $rhs))
    else `(($pf : ∀ ($rowVar:ident : $(c.rowTyId)), $(c.rowInvId) $rowVar → $predT $rowVar = true → $rhs))

@[noinline] private def mkPolProof (c : DbCallCtx) (isCross hasCrossPol : Bool) (predT : Term) (polId : Ident) (kind hint : String) : CommandElabM Term :=
  mkRowProof c isCross predT #[c.rowInvId, polId] kind hint fun r =>
    mkAppTermsPure polId (if isCross && hasCrossPol then #[mkIdent `_dbSnap, c.ctxId, r] else #[c.ctxId, r])

@[noinline] private def mkRowRunCallPure (c : DbCallCtx) (isOne : Bool) (qT proofT runPredT errLit encWriteT : Term) : PureQuotM Term := do
  mkAppC (if isOne then `Qed.Server.Db.dbRunOneRow else `Qed.Server.Db.dbRunRows)
    #[c.cfgId, qT, c.tid c.tbl `decodeRow, c.rowInvId, c.tid c.tbl `rowInvBool, c.tid c.tbl `rowInvBool_sound,
      proofT, runPredT, errLit, c.txOptT, encWriteT, ← mkListTerm (← mkTblEncReadPure c.tbl)]

@[noinline] private def lowerDbSelect (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  if c.opName == "count" then
    let (polId, hasCrossPol, polKind, polHint) :=
      if c.tbl.hasCountPolicy then
        (c.tid c.tbl `CountPolicy, c.tbl.hasCrossCountPolicy, s!"count policy `{c.qualName}.count`",
          mkPolHint c.tbl.countPolicyLabel "Check `where = r => ...` against the table's `policy count`." "Ensure `where = r => ...` (together with `requires` / `if` guards) implies")
      else (c.readPolId, c.tbl.hasCrossReadPolicy, c.readPolKind, c.readPolHint)
    let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := hasCrossPol)
    let pf ← mkPolProof c isCross hasCrossPol predT polId polKind polHint
    return (c.q do mkAppC `Qed.Server.Db.dbCount #[c.cfgId, ← mkAppC `Qed.Server.Db.SqlQuery.count #[c.tblSqlId, sqlW], pf, c.txOptT], false)
  let isOne := c.opName == "findOne" || c.opName == "findOneMeta"
  let (ordT, limT, offT) ← if !isOne then parseQueryWindow c.qctx c.tbl c.lowerVal c.findNamed
    else pure (← parseOrderByArg c.qctx c.tbl (c.findNamed "orderBy"), c.q (mkOptTerm (some (Syntax.mkNumLit "1"))), mkCIdent `Option.none)
  let mkProjCall (sqlW pf colsT decT encT : Term) : Term := c.q do
    let qT ← mkAppC `Qed.Server.Db.SqlQuery.select #[c.tblSqlId, colsT, sqlW, ordT, limT, offT]
    mkAppC (if isOne then `Qed.Server.Db.dbFindOneProj else `Qed.Server.Db.dbSelectProj) #[c.cfgId, qT, decT, pf, c.txOptT, encT]
  if c.opName == "selectMeta" || c.opName == "findOneMeta" then
    unless c.tbl.hasMeta do
      mkDbErr c.stx s!"`{c.opName}` is only available on tables with both encrypted and non-encrypted columns (`{c.qualName}` can use `{if isOne then "findOne" else "select"}` directly)"
    let (polId, hasCrossPol, polKind, polHint) :=
      if c.tbl.hasReadMetaPolicy then
        (c.tid c.tbl `ReadMetaPolicy, c.tbl.hasCrossReadMetaPolicy, s!"read_meta policy `{c.qualName}.read_meta`",
          mkPolHint c.tbl.readMetaPolicyLabel "Check `where = r => ...` against the table's `policy read_meta`." "Ensure `where = r => ...` (together with `requires` / `if` guards) implies")
      else (c.readPolId, c.tbl.hasCrossReadPolicy, c.readPolKind, c.readPolHint)
    let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := hasCrossPol)
    let pf ← mkPolProof c isCross hasCrossPol predT polId polKind polHint
    return (mkProjCall sqlW pf (c.tid c.tbl `metaColumns) (c.tid c.tbl `decodeMetaRow) (mkCIdent `List.nil), false)
  if let some colsStx := c.findNamed "columns" then
    let projCols ← parseColNameList c.tbl colsStx "`columns`" false (forbidDup := true) (fmtErr := fun col t => s!"unknown column `{col}` on table `{t}`")
    let projNames := projCols.map (·.2.name)
    let candColPols := c.tbl.colReadPolicies.filter fun cp => projNames.all (cp.cols.contains ·)
    let needCross := c.tbl.hasCrossReadPolicy || candColPols.any (·.hasCross)
    let (predT, sqlW, whereInfo?, isCross) ← c.parseWhere (needCross := needCross)
    let matchingColPols := candColPols.filter fun cp => cp.byCols.isEmpty || (isOne && whereInfoSatisfiesByCols whereInfo? cp.byCols)
    let pf ← if matchingColPols.isEmpty then
        let byHint := if candColPols.any (!·.byCols.isEmpty) then
            " Note: `policy read(...) by ...` requires `findOne` with an exact top-level `r.<col> == <val>` filter."
          else ""
        mkPolProof c isCross c.tbl.hasCrossReadPolicy predT c.readPolId c.readPolKind (c.readPolHint ++ byHint)
      else
        let unfolds := #[c.rowInvId, c.readPolId] ++ matchingColPols.map (mkIdentFrom c.stx ·.policyConst)
        let extraLabels := String.intercalate " or " (matchingColPols.toList.map fun cp => cp.label)
        let colHint := s!"{c.readPolHint} (or column read policy `{extraLabels}`)."
        mkRowProof c isCross predT unfolds c.readPolKind colHint fun r => do
          let base ← mkAppTermsPure c.readPolId (if isCross && c.tbl.hasCrossReadPolicy then #[mkIdent `_dbSnap, c.ctxId, r] else #[c.ctxId, r])
          Lang.foldlPQ matchingColPols base fun acc cp => do
            let cpId := mkIdentFrom c.stx cp.policyConst
            let cpApp ← mkAppTermsPure cpId (if isCross && cp.hasCross then #[mkIdent `_dbSnap, c.ctxId, r] else #[c.ctxId, r])
            `($acc ∨ $cpApp)
    let (colsT, decFnT, encT) := c.q do
      let projColIdTs ← Lang.mapPQ projCols fun (_, ci) => mkSqlIdentTermPure ci.name
      let projEncTs ← mkColsEncPairs c.tbl.tableName (projCols.map fun (_, ci) => (ci.name, ci.encKey?)) fun _ idx => Syntax.mkNumLit (toString idx)
      let colDecs ← Lang.mapIdxPQ projCols fun (cs, ci) idx => do
        return (mkIdent (Name.mkSimple s!"_pc{idx}"), ci.name, ← mkAppC `Qed.Server.Db.fromSqlOfField #[← mkFieldProjLam c.rowTyId (mkIdentFrom cs (Name.mkSimple ci.name))])
      let pvalsId := mkIdent `_pvals
      let body ← mkDecodeRowBody pvalsId colDecs (← buildTupleVal (colDecs.map fun (id, _, _) => (⟨id.raw⟩ : Term)))
      return (← mkListTerm projColIdTs, ← `(fun ($pvalsId:ident : Qed.Server.Db.DbRow) => $body), ← mkListTerm projEncTs)
    return (mkProjCall sqlW pf colsT decFnT encT, false)
  let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossReadPolicy)
  let pf ← mkPolProof c isCross c.tbl.hasCrossReadPolicy predT c.readPolId c.readPolKind c.readPolHint
  return (c.q do
    let qT ← mkAppC `Qed.Server.Db.SqlQuery.select #[c.tblSqlId, c.allColsT, sqlW, ordT, limT, offT]
    let runPredT ← if isCross then `(fun (_ : $(c.rowTyId)) => true) else pure predT
    let errLit := Syntax.mkStrLit (if isCross then "database row violated verified table invariant" else "database row violated verified table invariant or query predicate")
    mkRowRunCallPure c isOne qT pf runPredT errLit (mkCIdent `List.nil), false)

@[noinline] private def lowerDbAgg (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some colStx := (c.findNamed "col").orElse fun _ => c.posArgs[0]?
    | mkDbErr c.stx s!"`{c.qualName}.{c.opName}` requires a column selector (e.g. `\"{c.tbl.columns[0]?.map (·.name) |>.getD "col"}\"` or `col = \"...\"`)"
  let colInfo ← parseAggColArg c.tbl colStx
  let aggWhere? := (c.findNamed "where").orElse fun _ => (c.findNamed "filter").orElse fun _ => if (c.findNamed "col").isSome then c.posArgs[0]? else c.posArgs[1]?
  let (predT, sqlW, _, isCross) ← c.parseWhere aggWhere? c.tbl.hasCrossReadPolicy
  let pf ← mkPolProof c isCross c.tbl.hasCrossReadPolicy predT c.readPolId c.readPolKind c.readPolHint
  return (c.q do
    let aggOp := mkCIdent <| match c.opName with | "sum" => `Qed.Server.Db.SqlAggOp.sum | "min" => `Qed.Server.Db.SqlAggOp.min | _ => `Qed.Server.Db.SqlAggOp.max
    let qT ← mkAppC `Qed.Server.Db.SqlQuery.aggregate #[aggOp, c.tblSqlId, ← mkSqlIdentTermPure colInfo.name, sqlW]
    if c.opName == "sum" then mkAppC (if colInfo.isNat then `Qed.Server.Db.dbSumNat else `Qed.Server.Db.dbSumInt) #[c.cfgId, qT, pf, c.txOptT]
    else mkAppC `Qed.Server.Db.dbAggOpt #[c.cfgId, qT, ← mkFieldProjLam c.rowTyId (mkIdentFrom colStx (Name.mkSimple colInfo.name)), pf, c.txOptT], false)

@[noinline] private def lowerDbJoin (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some rStx := (c.findNamed "table").orElse fun _ => (c.findNamed "with").orElse fun _ => c.posArgs[0]?
    | mkDbErr c.stx s!"`{c.qualName}.join` requires a target table name (e.g. `join(\"books\", where = ...)` )"
  let uRt := unwrapParens1 rStx
  let rName ← if let some s := parseStrLitArg? rStx then pure s
    else if uRt.getKind == ``qedIdent then pure (uRt.getArg 0).getId.eraseMacroScopes.toString
    else mkDbErr rStx "`join` target table must be a string table name (e.g. `\"books\"`)"
  let rightTbl ← findDbTable rStx c.dbInfo rName
  if c.tbl.hasCrossReadPolicy || rightTbl.hasCrossReadPolicy ||
     (c.findNamed "where").any (stxAny (·.getKind == ``qedAnyIn)) || (c.findNamed "rightWhere").any (stxAny (·.getKind == ``qedAnyIn)) then
    mkDbErr c.stx "cross-table `any ... in ...:` predicates/policies are not supported inside `.join(...)`; query the table directly with `any ... in ...:` in `where`"
  let onCol? ← match c.findNamed "on" with
    | none => pure none | some o => match parseStrLitArg? o with | some s => pure (some s) | none => mkDbErr o "`on` must be a string column name"
  let some (lCol, rCol) := (c.tbl.columns.findSome? fun col => col.refs?.bind fun (rt, rc) => if rt == rightTbl.tableName && onCol?.all (· == col.name) then some (col.name, rc) else none).orElse fun _ =>
      rightTbl.columns.findSome? fun col => col.refs?.bind fun (rt, rc) => if rt == c.tbl.tableName && onCol?.all (· == rc) then some (rc, col.name) else none
    | mkDbErr c.stx s!"cannot `join` `{c.tbl.tableName}` with `{rightTbl.tableName}`: no `references` foreign key links these tables"
  let rRowTyId := mkIdentFrom c.stx rightTbl.rowTypeConst
  let (lPredT, lSqlW, _, _) ← c.parseWhere (c.findNamed "where")
  let (rPredT, rSqlW, _, _) ← c.parseWhere (c.findNamed "rightWhere") false rightTbl rRowTyId
  let (ordT, limT, offT) ← parseQueryWindow c.qctx c.tbl c.lowerVal c.findNamed
  return (c.q do
    let (rTblSqlId, rAllColsT) ← mkTblSqlPartsPure rightTbl
    let qT ← mkAppC `Qed.Server.Db.SqlQuery.joinSelect #[c.tblSqlId, rTblSqlId, c.allColsT, rAllColsT, ← mkSqlIdentTermPure lCol, ← mkSqlIdentTermPure rCol, lSqlW, rSqlW, ordT, limT, offT]
    let lPf ← mkDbProveTac #[c.rowInvId, c.readPolId] c.readPolKind c.opQual c.readPolHint
    let rPf ← mkDbProveTac #[c.tid rightTbl `RowInv, c.tid rightTbl `ReadPolicy] s!"read policy `{c.dbInfo.shortName}.{rightTbl.tableName}.read` (joined table)" c.opQual (c.readPolHint rightTbl "`rightWhere = r => ...`" "the joined table's")
    let joinEncT ← mkListTerm ((← mkTblEncReadPure c.tbl) ++ (← mkTblEncReadPure rightTbl c.tbl.columns.size))
    mkAppC `Qed.Server.Db.dbJoinSelect #[c.cfgId, qT, Syntax.mkNumLit (toString c.tbl.columns.size),
      c.tid c.tbl `decodeRow, c.tid rightTbl `decodeRow, c.rowInvId, c.tid c.tbl `rowInvBool, c.tid c.tbl `rowInvBool_sound,
      c.tid rightTbl `RowInv, c.tid rightTbl `rowInvBool, c.tid rightTbl `rowInvBool_sound,
      lPredT, rPredT, ← mkFieldProjLam c.rowTyId (mkIdentFrom c.stx (Name.mkSimple lCol)), ← mkFieldProjLam rRowTyId (mkIdentFrom c.stx (Name.mkSimple rCol)),
      c.readPolId, c.tid rightTbl `ReadPolicy, c.ctxId, lPf, rPf, c.txOptT, joinEncT], false)

@[noinline] private def parseConflictCols (c : DbCallCtx) (onArg? : Option Syntax) (reqTarget : Bool) : CommandElabM (Array DbColumnInfo) := do
  match onArg? with
  | some oStx =>
      let parsed ← parseColNameList c.tbl oStx s!"`{c.opName}` conflict target `on`/`conflict`" true (forbidEnc := true)
      if parsed.size == 1 && !(parsed[0]!.2.isPrimaryKey || parsed[0]!.2.isUnique) then
        mkDbErr parsed[0]!.1 s!"`{c.opName}` conflict column `{c.tbl.tableName}.{parsed[0]!.2.name}` must be `primary_key` or `unique`"
      return parsed.map Prod.snd
  | none =>
      if !reqTarget then return #[]
      let some pkCol := c.tbl.columns.find? (·.isPrimaryKey) | mkDbErr c.stx s!"`{c.qualName}.upsert` requires a `primary_key` column or explicit `on = \"<unique_col>\"`"
      if pkCol.encKey?.isSome then mkDbErr c.stx s!"cannot `{c.opName}` on encrypted column `{c.tbl.tableName}.{pkCol.name}`"
      return #[pkCol]

@[noinline] private def parseInsertGuardArg (c : DbCallCtx) (rowVar : Ident) (guardStx : Syntax) :
    CommandElabM (Term × Term × Bool) := do
  let u := unwrapParens1 guardStx
  let (rId?, rName?, rawBody) :=
    if u.getKind == ``qedLam1 then
      let b := u.getArg 0; let id : Ident := if b.isIdent then ⟨b⟩ else mkIdent `_row
      (some id, some (id.getId.eraseMacroScopes.toString), u.getArg 2)
    else (none, none, u)
  let (body, _) ← expandDbFnsInStx c.dbInfo.fns #[c.dbAlias, c.dbInfo.shortName] rawBody
  let isCross := c.tbl.hasCrossInsertPolicy || stxAny (·.getKind == ``qedAnyIn) body
  let snapTyId? ← if isCross then
      let some snapConst := c.dbInfo.snapTypeConst? | mkDbErr guardStx s!"cross-table `any ... in ...` requires a multi-table `database` (`{c.dbInfo.shortName}` has no `Snap` type)"
      pure (some (mkIdent snapConst))
    else pure none
  let lowerValWithRow := match rName? with
    | some rn => fun locs e => c.lowerValWithLocals (#[rn] ++ locs) e
    | none => c.lowerValWithLocals
  let sqlRaw ← lowerRowSqlExprGo c.qctx lowerValWithRow c.dbInfo #[] body rName?
  let sqlW := match rId? with
    | some rId => c.q `(let $rId:ident : $(c.rowTyId) := $rowVar; $sqlRaw)
    | none => sqlRaw
  let rLocs := rName?.elim #[] (#[·]); let rBind : Ident := rId?.getD (mkIdent `_row)
  let predT ← match snapTyId? with
    | some sTy =>
        let snapId := mkIdent `_dbSnap
        let bVal ← c.lowerValWithLocals (rLocs.push "_dbSnap") (rewriteSnapTables snapId (c.dbInfo.tables.map (·.tableName)) body)
        pure <| c.q `(fun ($snapId:ident : $sTy) ($rBind:ident : $(c.rowTyId)) => ($bVal : Bool))
    | none =>
        let bVal ← c.lowerValWithLocals rLocs body
        pure <| c.q `(fun ($rBind:ident : $(c.rowTyId)) => ($bVal : Bool))
  return (predT, sqlW, isCross)

@[noinline] private def mkWriteCallPure (c : DbCallCtx) (rowVar : Ident) (rowTerm : Term) (conflictCols : Array DbColumnInfo)
    (insertGuard? : Option (Term × Term × Bool)) (conflictW? : Option (Term × Term)) (hasConflictWhere : Bool) : PureQuotM Term := do
  let insPolId := c.tid c.tbl `InsertPolicy
  let insPolArg : Term ← if c.tbl.hasCrossInsertPolicy then `(fun (_c : Qed.Server.RequestCtx) (_r : $(c.rowTyId)) => ∀ (_dbSnap : $(c.snapTyId?.get!)), $insPolId _dbSnap _c _r) else pure (insPolId : Term)
  let pairTs ← mkListTerm (← Lang.mapPQ c.tbl.columns fun col => do
    mkPairTerm (← mkSqlIdentTermPure col.name) (← mkAppC `Qed.Server.Db.ToSql.toSql #[← `(($rowVar).$(mkIdentFrom c.stx (Name.mkSimple col.name)))]))
  let conflictColTs ← mkListTerm (← Lang.mapPQ conflictCols fun cc => mkSqlIdentTermPure cc.name)
  let invPf ← mkDbProveTac #[c.rowInvId] s!"table constraint `{c.qualName}.RowInv`" c.opQual "Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds."
  let insPolHintBase := mkPolHint c.tbl.insertPolicyLabel "Ensure inserted row satisfies the table's `policy insert` / `policy write`."
    (if insertGuard?.isSome then "Ensure `where = r => ...` implies" else "Ensure inserted row satisfies")
  let insPolHint := if insertGuard?.isNone && c.tbl.hasCrossInsertPolicy then
      insPolHintBase ++ (if c.opName == "upsert" then " For cross-table insert policies, use `insertOrIgnore(where = r => ...)` + `updateOne` inside `transaction`."
        else " For cross-table insert policies, pass `where = r => any ... in ...:` to verify the policy atomically at insert time.")
    else insPolHintBase
  let insPolUnfolds := if insertGuard?.isSome then #[c.rowInvId, insPolId] else #[insPolId]
  let insPolTac ← mkDbProveTac insPolUnfolds s!"insert policy `{c.qualName}.insert`" c.opQual insPolHint
  let encWriteT ← mkTblEncWritePure c.tbl
  let callT ←
    if c.opName == "insert" || c.opName == "insertOrIgnore" then
      let isIgn := c.opName == "insertOrIgnore"
      let hasGuard := insertGuard?.isSome
      let snapVar := mkIdent `_dbSnap
      let insPolGoal ← match insertGuard? with
        | some (gPredT, _, isCrossG) =>
            let rhs ← mkAppTermsPure insPolId (if c.tbl.hasCrossInsertPolicy then #[snapVar, c.ctxId, rowVar] else #[c.ctxId, rowVar])
            if isCrossG then `(∀ ($snapVar:ident : $(c.snapTyId?.get!)), $(c.rowInvId) $rowVar → $gPredT $snapVar $rowVar = true → $rhs)
            else `($(c.rowInvId) $rowVar → $gPredT $rowVar = true → $rhs)
        | none =>
            if c.tbl.hasCrossInsertPolicy then `(∀ ($snapVar:ident : $(c.snapTyId?.get!)), $insPolId $snapVar $(c.ctxId) $rowVar)
            else mkAppTermsPure insPolId #[c.ctxId, rowVar]
      let insPolPf ← `(($insPolTac : $insPolGoal))
      let guardOptT ← mkOptTerm (insertGuard?.map fun (_, sqlW, _) => sqlW)
      let colTypeTs : Term ← match insertGuard? with
        | none => pure (mkCIdent `List.nil : Term)
        | some _ => mkListTerm (← Lang.mapPQ c.tbl.columns fun col => pure <| (mkCIdent <|
            if col.isNat || col.isInt then `Qed.Server.Db.SqlColType.int
            else if col.isBool then `Qed.Server.Db.SqlColType.bool
            else if col.isBytes then `Qed.Server.Db.SqlColType.bytes
            else `Qed.Server.Db.SqlColType.text : Term))
      let firstColRetTs : Term ← if isIgn || hasGuard then
          mkListTerm (← match c.tbl.columns[0]? with | some c0 => pure #[← mkSqlIdentTermPure c0.name] | none => pure #[])
        else pure (mkCIdent `List.nil : Term)
      if !isIgn then
        let qT ← mkAppC `Qed.Server.Db.SqlQuery.insert #[c.tblSqlId, pairTs, firstColRetTs, guardOptT, colTypeTs]
        mkAppC `Qed.Server.Db.dbInsert #[c.cfgId, qT, rowVar, c.rowInvId, invPf, insPolPf, c.txOptT, encWriteT, quote hasGuard]
      else
        let qT ← mkAppC `Qed.Server.Db.SqlQuery.insertOrIgnore #[c.tblSqlId, pairTs, conflictColTs, firstColRetTs, guardOptT, colTypeTs]
        mkAppC `Qed.Server.Db.dbInsertOrIgnore #[c.cfgId, qT, rowVar, c.rowInvId, invPf, insPolPf, c.txOptT, encWriteT]
    else
      let some (conflictPredT, conflictSqlW) := conflictW? | unreachable!
      let conflictNames := conflictCols.map (·.name)
      let updColTs ← mkListTerm (← Lang.foldlPQ c.tbl.columns #[] fun acc col =>
        if !col.isPrimaryKey && !col.isImmutable && !conflictNames.contains col.name then return acc.push (← mkSqlIdentTermPure col.name) else pure acc)
      let (updPolId, transInvId) := (c.tid c.tbl `UpdatePolicy, c.tid c.tbl `TransInv)
      let updHint := mkPolHint c.tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
      let updPolNewPf ← mkDbProveTac #[updPolId] s!"update policy `{c.qualName}.update`" c.opQual updHint
      let updPolOldPf ← mkDbProveTac #[c.rowInvId, updPolId] s!"upsert conflict update policy `{c.qualName}.update`" c.opQual updHint
      let transPf ← mkDbProveTac #[c.rowInvId, transInvId] s!"transition/monotonicity invariant `{c.qualName}.TransInv`" c.opQual "Ensure the upserted row satisfies all `old(...)` and `transition` invariants against any conflicting row."
      let qT ← mkAppC `Qed.Server.Db.SqlQuery.upsert #[c.tblSqlId, pairTs, conflictColTs, updColTs, ← mkOptTerm (if hasConflictWhere then some conflictSqlW else none), c.allColsT]
      mkAppC `Qed.Server.Db.dbUpsert #[c.cfgId, qT, rowVar, c.tid c.tbl `decodeRow, c.rowInvId, c.tid c.tbl `rowInvBool, c.tid c.tbl `rowInvBool_sound,
        transInvId, conflictPredT, insPolArg, updPolId, c.ctxId, invPf, insPolTac, updPolNewPf, updPolOldPf, transPf, c.txOptT, encWriteT, ← mkListTerm (← mkTblEncReadPure c.tbl)]
  `(let $rowVar:ident : $(c.rowTyId) := $rowTerm; $callT)

@[noinline] private def lowerDbWrite (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  if c.opName == "delete" then
    let (predT, sqlW, _, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossDeletePolicy)
    let delHint := mkPolHint c.tbl.deletePolicyLabel "Check the `where = r => ...` clause against the table's `policy delete` / `policy write`." "Ensure `where = r => ...` implies"
    let pf ← mkPolProof c isCross c.tbl.hasCrossDeletePolicy predT (c.tid c.tbl `DeletePolicy) s!"delete policy `{c.qualName}.delete`" delHint
    return (c.q do mkAppC `Qed.Server.Db.dbDelete #[c.cfgId, ← mkAppC `Qed.Server.Db.SqlQuery.delete #[c.tblSqlId, sqlW, mkCIdent `List.nil], pf, c.txOptT], true)
  let hasCol (nm : String) := c.tbl.columns.any (·.name == nm)
  let isClauseWhere (s : Syntax) := (unwrapParens1 s).getKind == ``qedLam1 || !hasCol "where"
  let allowsConflict := c.opName == "upsert" || c.opName == "insertOrIgnore"
  let onArg? := if allowsConflict then (c.findNamed "conflict").orElse fun _ => if !hasCol "on" then c.findNamed "on" else none else none
  let whereStx? := (c.findNamed "where").filter isClauseWhere
  let rowNamedArgs := c.namedArgs.filter fun (k, s) =>
    !((allowsConflict && (k == "conflict" || (k == "on" && !hasCol "on"))) || (k == "where" && isClauseWhere s))
  let rowTerm ← if c.posArgs.size == 1 && rowNamedArgs.isEmpty then c.lowerVal c.posArgs[0]!
    else if c.posArgs.isEmpty && !rowNamedArgs.isEmpty then
      Lang.foldlCmd rowNamedArgs () fun _ (k, _) => discard <| findDbCol c.stx c.tbl k (fun col t => s!"unknown column `{col}` in `{c.dbInfo.shortName}.{t}.{c.opName}`")
      let findRowNamed := findNamedArg? rowNamedArgs
      let (fIds, fVals) := (← Lang.mapCmd c.tbl.columns fun col => do
        let fId := mkIdentFrom c.stx (Name.mkSimple col.name)
        match findRowNamed col.name with
        | some v => return (fId, c.q (c.wrapField (← c.lowerVal v)))
        | none => if col.isNullable then return (fId, mkCIdent `Option.none) else mkDbErr c.stx s!"`{c.qualName}.{c.opName}` is missing required column `{col.name}`").unzip
      pure <| c.q `({ $[$fIds:ident := $fVals:term],* : $(c.rowTyId) })
    else mkDbErr c.stx s!"`{c.qualName}.{c.opName}` expects named column arguments (`col = val, ...`) or a single `{c.qualName}` row value"
  if c.tbl.hasCrossInsertPolicy && c.snapTyId?.isNone then mkDbErr c.stx s!"internal error: missing `Snap` type for database `{c.dbInfo.shortName}`"
  let rowVar := mkIdent `_insRow
  let (conflictCols, insertGuard?, conflictW?) ← if c.opName == "insert" || c.opName == "insertOrIgnore" then do
      let cis ← if c.opName == "insertOrIgnore" then parseConflictCols c onArg? false else pure #[]
      pure (cis, ← whereStx?.mapM (parseInsertGuardArg c rowVar), none)
    else
      if c.tbl.hasCrossUpdatePolicy || c.tbl.hasTwoStateUpdatePolicy || whereStx?.any (stxAny (·.getKind == ``qedAnyIn)) then
        mkDbErr c.stx "cross-table `any ... in ...:` or two-state `old(...)` in `policy update` is not supported in `.upsert(...)`; use `insertOrIgnore` + `updateOne` inside `transaction`"
      let cis ← parseConflictCols c onArg? true
      let (cp, cw, _, _) ← c.parseWhere whereStx?
      pure (cis, none, some (cp, cw))
  return (c.q (mkWriteCallPure c rowVar rowTerm conflictCols insertGuard? conflictW? whereStx?.isSome), true)

private structure UpdateFieldAcc where
  colNames : Array String := #[]
  leanFIds : Array Ident := #[]
  leanFVals : Array Term := #[]
  sqlPairs : Array Term := #[]
  postChecks : Array Term := #[]
  underflows : Array (String × Ident × Term) := #[]

@[noinline] private def lowerDbUpdateField (c : DbCallCtx) (setRowVar postRowVar : Ident) (setRowName : String) (isCross : Bool)
    (acc : UpdateFieldAcc) (item : Ident × DbColumnInfo × String × Syntax) : CommandElabM UpdateFieldAcc := do
  let (colId, colInfo, setOp, valStx) := item; let colName := colInfo.name
  let fId := mkIdentFrom colId (Name.mkSimple colName); let colSqlId := c.q (mkSqlIdentTermPure colName)
  let valMentionsRow := stxMentionsVar setRowName valStx
  let lowerSetSql (wrappedVal : Term) : CommandElabM Term :=
    if !valMentionsRow && !isIdentNamed valStx (fun n => n == `true || n == `false) then pure <| c.q (mkTypedSqlParamTerm c.rowTyId fId wrappedVal)
    else lowerRowSqlExprGo c.qctx c.lowerValWithLocals c.dbInfo #[(setRowName, c.tbl, c.tbl.tableName)] valStx
  let (lv, sp, post?, uf?) ←
    if setOp == "+=" || setOp == "-=" || setOp == "*=" then
      if colInfo.encKey?.isSome then mkDbErr valStx s!"cannot update encrypted column `{c.qualName}.{colName}` using `{setOp}`"
      if !(colInfo.isNat || colInfo.isInt) || colInfo.isNullable then
        mkDbErr colId s!"atomic `{setOp}` requires a non-null integer (`Nat` or `Int`) column, but `{c.tbl.tableName}.{colName}` is not"
      let deltaT := c.q (c.wrapField (← c.lowerValWithLocals #[setRowName] valStx)); let deltaSqlT ← lowerSetSql deltaT
      let sqlBinOp := if setOp == "+=" then `Qed.Server.Db.SqlBinOp.add else if setOp == "-=" then `Qed.Server.Db.SqlBinOp.sub else `Qed.Server.Db.SqlBinOp.mul
      let (lv, sp) := c.q do
        let sqlE ← mkSqlBinOpPure sqlBinOp (← mkAppC `Qed.Server.Db.SqlExpr.col #[colSqlId]) deltaSqlT
        let leanE ← if setOp == "+=" then `(($setRowVar.$fId + $deltaT)) else if setOp == "-=" then `(($setRowVar.$fId - $deltaT)) else `(($setRowVar.$fId * $deltaT))
        return (leanE, ← mkPairTerm colSqlId sqlE)
      pure (lv, sp, none, if setOp == "-=" && colInfo.isNat then some (colName, fId, deltaT) else none)
    else if setOp != "=" then
      mkDbErr valStx s!"unsupported compound assignment `{setOp}` in database `set` (supported: `=`, `+=`, `-=`, `*=`)"
    else
      if colInfo.encKey?.isSome && valMentionsRow then
        mkDbErr valStx s!"cannot update encrypted column `{c.qualName}.{colName}` using a row-dependent SQL expression"
      let rhsVal := c.q (c.wrapField (← c.lowerValWithLocals #[setRowName] valStx)); let sqlValT ← lowerSetSql rhsVal
      let (sp, post?) := c.q do
        return (← mkPairTerm colSqlId sqlValT, ← if !valMentionsRow && !isCross then some <$> `(($postRowVar.$fId == $rhsVal)) else pure none)
      pure (rhsVal, sp, post?, none)
  return {
    colNames := acc.colNames.push colName, leanFIds := acc.leanFIds.push fId, leanFVals := acc.leanFVals.push lv,
    sqlPairs := acc.sqlPairs.push sp, postChecks := post?.elim acc.postChecks acc.postChecks.push, underflows := uf?.elim acc.underflows acc.underflows.push }

@[noinline] private def lowerDbUpdate (c : DbCallCtx) : CommandElabM (Term × Bool) := do
  let some setRaw := c.findNamed "set" | mkDbErr c.stx s!"`{c.qualName}.{c.opName}` requires `set = r => \{ col = expr, ... }`"
  let (predT, sqlW, whereInfo?, isCross) ← c.parseWhere (needCross := c.tbl.hasCrossUpdatePolicy)
  let uSet := unwrapParens1 setRaw
  let (setRowVar, recStx) : Ident × Syntax ←
    if uSet.getKind == ``qedLam1 then let b := uSet.getArg 0; pure (if b.isIdent then ⟨b⟩ else mkIdent `_row, unwrapParens1 (uSet.getArg 2))
    else if uSet.getKind == ``qedRecLit then pure (mkIdent `_row, uSet)
    else mkDbErr setRaw "`set` must be `r => { col = expr, ... }` or `{ col = expr, ... }`"
  if recStx.getKind != ``qedRecLit then mkDbErr recStx "`set` body must be a record update `{ col = expr, ... }`"
  let setFields := (recStx.getArg 2).getSepArgs
  if setFields.isEmpty then mkDbErr recStx "`set` must update at least one column"
  let parsedSet ← parseDbSetItems c.tbl setFields s!"`{c.fnName}`" true (forbidImmutable := true) (colQualPfx := s!"{c.qualName}.")
  let (setRowName, postRowVar) := (setRowVar.getId.eraseMacroScopes.toString, mkIdent `_postRow)
  let acc ← Lang.foldlCmd parsedSet {} (lowerDbUpdateField c setRowVar postRowVar setRowName isCross)
  let postChecks ← match isCross, whereInfo? with
    | false, some (wRowName, wBody) =>
        let colNames := c.tbl.columns.map (·.name)
        Lang.foldlCmd (splitAndStx wBody) acc.postChecks fun pcs conj => do
          let touched := stxCollectRowCols wRowName colNames conj
          if !touched.isEmpty && touched.all (!acc.colNames.contains ·) then
            return pcs.push (c.q `((fun ($(mkIdent (Name.mkSimple wRowName)):ident : $(c.rowTyId)) => ($(← c.lowerValWithLocals #[wRowName] conj) : Bool)) $postRowVar))
          else return pcs
    | _, _ => pure acc.postChecks
  let (leanFIds, leanFVals, sqlPairs) := (acc.leanFIds, acc.leanFVals, acc.sqlPairs)
  let setFnT := c.q `(fun ($setRowVar:ident : $(c.rowTyId)) => { $setRowVar with $[$leanFIds:ident := $leanFVals:term],* })
  let (updPolId, transInvId) := (c.tid c.tbl `UpdatePolicy, c.tid c.tbl `TransInv)
  let polHint := mkPolHint c.tbl.updatePolicyLabel "Ensure `where = r => ...` satisfies the table's `policy update` / `policy write`." "Ensure `where = r => ...` implies"
  let polPf ← if c.tbl.hasTwoStateUpdatePolicy then
      mkRowProof c isCross predT #[c.rowInvId, updPolId] s!"update policy `{c.qualName}.update`" polHint fun r => do
        let sr ← mkAppTermsPure setFnT #[r]
        mkAppTermsPure updPolId (if isCross && c.tbl.hasCrossUpdatePolicy then #[mkIdent `_dbSnap, c.ctxId, r, sr] else #[c.ctxId, r, sr])
    else do
      let polOldPf ← mkPolProof c isCross c.tbl.hasCrossUpdatePolicy predT updPolId s!"update policy `{c.qualName}.update`" polHint
      let polNewPf ← mkRowProof c isCross predT #[c.rowInvId, updPolId] s!"post-update policy `{c.qualName}.update` (anti-hijack)" polHint fun r => do
        let sr ← mkAppTermsPure setFnT #[r]
        mkAppTermsPure updPolId (if isCross && c.tbl.hasCrossUpdatePolicy then #[mkIdent `_dbSnap, c.ctxId, sr] else #[c.ctxId, sr])
      pure <| c.q (mkAppC ``And.intro #[polOldPf, polNewPf])
  let invPf ← mkRowProof c isCross predT #[c.rowInvId] s!"table constraint `{c.qualName}.RowInv`" "Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`." fun r => do mkAppTermsPure c.rowInvId #[← mkAppTermsPure setFnT #[r]]
  let transPf ← mkRowProof c isCross predT #[c.rowInvId, transInvId] s!"transition/monotonicity invariant `{c.qualName}.TransInv`" "Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants." fun r => do mkAppTermsPure transInvId #[r, ← mkAppTermsPure setFnT #[r]]
  let ufPfs ← Lang.mapCmd acc.underflows fun (cn, fId, deltaT) =>
    mkRowProof c isCross predT #[c.rowInvId] s!"Nat non-underflow for `{c.tbl.tableName}.{cn} -= ...`"
      s!"Guard the update in `where = r => r.{cn} >= ...` so SQL subtraction cannot go negative." (fun r => `($deltaT ≤ $r.$fId)) setRowVar
  return (c.q do
    let qT ← mkAppC `Qed.Server.Db.SqlQuery.update #[c.tblSqlId, ← mkListTerm sqlPairs, sqlW, c.allColsT]
    let hAll ← mkAppC ``And.intro #[polPf, ← mkAppC ``And.intro #[invPf, transPf]]
    let runPredT ← if isCross then `(fun (_ : $(c.rowTyId)) => true) else `(fun ($postRowVar:ident : $(c.rowTyId)) => $(← mkBoolConj postChecks))
    let isOne := c.opName == "updateOne"
    let errLit := Syntax.mkStrLit (if isCross then "updated database row violated verified table invariant" else if isOne then "updated database row violated verified table invariant or postcondition" else "database row violated verified table invariant or query predicate")
    let baseCall ← mkRowRunCallPure c isOne qT hAll runPredT errLit (← mkTblEncWritePure c.tbl)
    Lang.foldrPQ ufPfs baseCall fun pf acc => `(have _ := $pf; $acc), true)

@[noinline] def lowerDbCall (lowerValWithLocals : Array String → Syntax → CommandElabM Term)
    (fnName : String) (dbInfo : DatabaseInfo) (stx : Syntax) (chain : List String)
    (rawArgs : Array Syntax) (txIdTerm? : Option Term := none) (wrapField : Term → PureQuotM Term := pure)
    (ctxTerm? : Option Term := none) : CommandElabM (Term × Bool) := do
  let qctx ← Lang.getPureQuotCtxCmd; let cfgId := mkIdentFrom stx dbInfo.configConst
  let txOptT : Term := qctx.runPure (mkOptTerm txIdTerm?)
  match chain with
  | [_, "ensureSchema"] =>
      if !rawArgs.isEmpty then mkDbErr stx "`ensureSchema()` takes no arguments"
      return (mkIdentFrom stx dbInfo.ensureSchemaConst, true)
  | [dbAlias, tblName, opName] =>
      let tbl ← findDbTable stx dbInfo tblName; let (tblSqlId, allColsT) := qctx.runPure (mkTblSqlPartsPure tbl)
      let (posArgs, namedArgs) ← splitCallArgs "database" rawArgs (allowWhere := true); let findNamed := findNamedArg? namedArgs
      let c : DbCallCtx := {
        qctx, lowerValWithLocals, fnName, dbAlias, dbInfo, stx, tbl, opName, opQual := s!"{fnName} → {dbInfo.shortName}.{tbl.tableName}.{opName}",
        cfgId, txOptT, ctxId := ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩,
        rowTyId := mkIdentFrom stx tbl.rowTypeConst, rowInvId := mkIdentFrom stx (tbl.rowTypeConst ++ `RowInv),
        readPolId := mkIdentFrom stx (tbl.rowTypeConst ++ `ReadPolicy), tblSqlId, allColsT,
        snapTyId? := dbInfo.snapTypeConst?.map (mkIdentFrom stx), posArgs, namedArgs,
        whereArg? := (findNamed "where").orElse fun _ => (findNamed "filter").orElse fun _ => posArgs[0]?, wrapField }
      match opName with
      | "select" | "findOne" | "count" | "selectMeta" | "findOneMeta" => lowerDbSelect c
      | "sum" | "min" | "max" => lowerDbAgg c | "join" => lowerDbJoin c
      | "delete" | "insert" | "insertOrIgnore" | "upsert" => lowerDbWrite c
      | "update" | "updateOne" => lowerDbUpdate c
      | _ => mkDbErr stx s!"unknown database table method `{opName}` on `{c.qualName}` (expected `select`, `findOne`, `count`, `sum`, `min`, `max`, `join`, `insert`, `insertOrIgnore`, `upsert`, `update`, `updateOne`, or `delete`)"
  | _ => mkDbErr stx s!"invalid database call; expected `<db>.<table>.<op>(...)` or `<db>.ensureSchema()`"

end QueryHelpers
end Qed.Server.Db
