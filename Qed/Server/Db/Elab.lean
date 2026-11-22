import Lean
import Qed.Lang
import Qed.Schema.Registry
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Db.Core
import Qed.Server.Db.Runtime
import Qed.Server.Db.Syntax

namespace Qed.Server.Db
open Qed.Lang

/-! ## `database` Command Elaborator
    Compiles `database <Name>:` blocks into:
    - Verified table row structures with `ToJson`/`FromJson`/`ToProto`/`FromProto`/`LawfulProto`
    - Kernel-reducible `RowInv`, `rowInvBool`, `rowInvBool_sound`, `TransInv`, and
      `ReadPolicy`/`InsertPolicy`/`UpdatePolicy`/`DeletePolicy` predicates
    - Zero-trust `decodeRow` decoders
    - SQL DDL (`CREATE TABLE` + `CHECK` + `UNIQUE` + `FOREIGN KEY` + `INDEX`) and Postgres RLS DDL
    - Driver-agnostic `DbConfig` & `ensureSchema`
    - Persistent `databaseRegistry` metadata for `server` `use db : <Name>` lowering -/

private structure ParsedCol where
  ref          : Lean.Syntax
  ident        : Lean.Ident
  colName      : String
  tyTerm       : Lean.Term
  sqlColType   : SqlColType
  isNullable   : Bool
  isNat        : Bool
  isBytes      : Bool
  isPrimaryKey : Bool
  isImmutable  : Bool
  isUnique     : Bool
  refs?        : Option (Lean.Ident × Lean.Ident)
  whereExprs   : Array Lean.Syntax

private structure ParsedTable where
  ref           : Lean.Syntax
  ident         : Lean.Ident
  tableName     : String
  cols          : Array ParsedCol
  readPols      : Array Lean.Syntax
  insertPols    : Array Lean.Syntax
  updatePols    : Array Lean.Syntax
  deletePols    : Array Lean.Syntax
  singleInvs    : Array Lean.Syntax
  transInvs     : Array Lean.Syntax -- two-state `old(...)` exprs
  transChains   : Array (Lean.Syntax × Array (Array Lean.Syntax)) -- (targetExpr, chains of exprs)
  indexes       : Array (Array Lean.Ident)

open Lean Elab Command in
private def parseEndpointSpec (stx : Syntax) :
    CommandElabM (Term × Array String) := do
  let k := stx.getKind
  let secsRef ← IO.mkRef (#[] : Array String)
  let optStrLit : Option String → CommandElabM Term
    | some d => `(some $(Syntax.mkStrLit d))
    | none   => `(none)
  let readRef (s : Syntax) (recordSec := true) (onlyIfNoDefault := false) : CommandElabM (Term × Term) := do
    let er ← parseQedEnvRef "database" s
    if recordSec && er.isSecret && (!onlyIfNoDefault || er.default?.isNone) then
      secsRef.modify (·.push er.envKey)
    return (Syntax.mkStrLit er.envKey, ← optStrLit er.default?)
  let epT : Term ←
    if k == ``dbEpUrl then
      `(Qed.Server.Db.DbEndpoint.urlEnv $((← readRef (stx.getArg 1)).1))
    else if k == ``dbEpPostgres then
      `(Qed.Server.Db.DbEndpoint.postgresEnv $((← readRef (stx.getArg 1)).1))
    else if k == ``dbEpSqliteLit then
      `(Qed.Server.Db.DbEndpoint.sqlitePath $(Syntax.mkStrLit (⟨stx.getArg 1⟩ : TSyntax `str).getString))
    else if k == ``dbEpSqliteEnv then
      let (keyT, defT) ← readRef (stx.getArg 1) (onlyIfNoDefault := true)
      `(Qed.Server.Db.DbEndpoint.sqliteEnv $keyT $defT)
    else if k == ``dbEpD1 then
      let (accK, accD) ← readRef (stx.getArg 3) (recordSec := false)
      let (dbK, dbD)   ← readRef (stx.getArg 7) (recordSec := false)
      let (tokK, _)    ← readRef (stx.getArg 11)
      `(Qed.Server.Db.DbEndpoint.cloudflareD1 $accK $accD $dbK $dbD $tokK)
    else if k == ``dbEpTurso then
      let (uK, _)   ← readRef (stx.getArg 3)
      let (tokK, _) ← readRef (stx.getArg 7)
      `(Qed.Server.Db.DbEndpoint.turso $uK $tokK)
    else if k == ``dbEpHttp then
      let (uK, _) ← readRef (stx.getArg 3)
      let tokOpt := stx.getArg 4
      let tokT ← if tokOpt.getNumArgs == 4 then `(some $((← readRef (tokOpt.getArg 3)).1)) else `(none)
      `(Qed.Server.Db.DbEndpoint.httpSql $uK $tokT)
    else
      throwErrorAt stx "unexpected database endpoint specification"
  return (epT, ← secsRef.get)

private def inferSqlColType (pty : LoweredQedType) : SqlColType × Bool × Bool × Bool :=
  let base := pty.baseName
  let isNullable := pty.isOption
  if base == `Nat then (.int, isNullable, true, false)
  else if base == `Int then (.int, isNullable, false, false)
  else if base == `Bool then (.bool, isNullable, false, false)
  else if base == `Bytes || base == `ByteArray then (.bytes, isNullable, false, true)
  else (.text, isNullable, false, false)

open Lean Elab Command in
private partial def lowerDbExpr (colNames : Array String) (rowVar : Ident)
    (oldVar? : Option Ident) (ctxVar? : Option Ident) (asProp : Bool) (stx : Syntax) :
    CommandElabM Term := do
  let fail (ref : Syntax) (msg : String) : CommandElabM Term := throwErrorAt ref msg
  let hooks : LowerHooks CommandElabM := { LowerHooks.mkDefault fail with
    lowerIdent := fun ref id mode => do
      let comps := id.getId.eraseMacroScopes.components
      let foldProjs (base : Term) (rest : List Name) : CommandElabM Term :=
        rest.foldlM (init := base) fun acc f => `(($acc).$(mkIdentFrom ref f):ident)
      let t ← match comps with
        | [] => throwErrorAt ref "empty identifier in database predicate"
        | root :: rest =>
            let rs := root.toString
            if rest.isEmpty && rs == "true" then if mode == .propInv then `(True) else `(true)
            else if rest.isEmpty && rs == "false" then if mode == .propInv then `(False) else `(false)
            else if rest.isEmpty && rs == "none" then `(Option.none)
            else if rs == "row" then foldProjs ⟨rowVar.raw⟩ rest
            else if rs == "ctx" then
              let some cv := ctxVar?
                | throwErrorAt ref "`ctx` is only in scope inside `policy ... requires ...`"
              foldProjs ⟨cv.raw⟩ rest
            else if colNames.contains rs then foldProjs (← `($rowVar.$(mkIdentFrom ref root))) rest
            else pure ⟨id.raw⟩
      if mode == .propInv && comps != [`true] && comps != [`false] then `(qedAsProp($t)) else pure t
    lowerProj := fun _ base field mode => do
      let t ← `($base.$field)
      if mode == .propInv then `(qedAsProp($t)) else pure t
    lowerIndex := fun ref _ _ _ => fail ref "indexing is not supported in database predicates"
    lowerCall := fun ref callee rawArgs mode go => do
      if callee.getKind == ``qedIdent then
        let nm := (callee.getArg 0).getId.eraseMacroScopes
        if nm == `old then
          let some ov := oldVar?
            | throwErrorAt ref "`old(...)` is only allowed inside two-state table `invariant` clauses"
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
            throwErrorAt ref "`old(...)` expects a single expression argument"
          return some (← lowerDbExpr colNames ov none ctxVar? (mode == .propInv) (rawArgs[0]!.getArg 0))
        else if nm == `some then
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
            throwErrorAt ref "`some(...)` expects a single argument"
          return some (← `(Option.some $(← go .val (rawArgs[0]!.getArg 0))))
      return none
  }
  lowerQedExpr hooks (if asProp then .propInv else .val) stx

/-- Best-effort static SQL predicate renderer for column `CHECK (...)` (`forRls := false`)
    and Postgres RLS `USING (...)` (`forRls := true`) expressions. -/
private partial def renderSqlPred? (colNames : Array String) (forRls : Bool) (stx : Lean.Syntax) : Option String :=
  let recR := renderSqlPred? colNames forRls
  let k := stx.getKind
  if !forRls && k == ``qedLitNum then
    some (toString (⟨(stx.getArg 0)⟩ : Lean.TSyntax `num).getNat)
  else if forRls && k == ``qedCall then
    let callee := stx.getArg 0
    let rawArgs := (stx.getArg 2).getSepArgs
    if callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `some &&
       rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos then
      recR (rawArgs[0]!.getArg 0)
    else none
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs
    if args.size == 1 then (recR args[0]!).map fun s => "(" ++ s ++ ")" else none
  else if k == ``qedIdent || k == ``qedProj then
    match extractDottedChain? stx with
    | some [s] =>
        if colNames.contains s then some ("\"" ++ s ++ "\"")
        else if s == "true" then some (if forRls then "TRUE" else "1")
        else if s == "false" then some (if forRls then "FALSE" else "0")
        else none
    | some ["row", col] => if colNames.contains col then some ("\"" ++ col ++ "\"") else none
    | some ["ctx", "userId"] => if forRls then some "current_setting('qed.user_id', true)" else none
    | some [col, "length"] | some ["row", col, "length"] =>
        if !forRls && colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | _ =>
        if !forRls && k == ``qedProj && (stx.getArg 2).getId.eraseMacroScopes == `length then
          (recR (stx.getArg 0)).map fun s => "LENGTH(" ++ s ++ ")"
        else none
  else if k == ``qedAnd || k == ``qedOr then do
    let l ← recR (stx.getArg 0)
    let r ← recR (stx.getArg 2)
    return "(" ++ l ++ (if k == ``qedAnd then " AND " else " OR ") ++ r ++ ")"
  else if !forRls && k == ``qedNot then
    (recR (stx.getArg 1)).map fun s => "(NOT " ++ s ++ ")"
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs
    if links.isEmpty || (forRls && links.size != 1) then none
    let mapOp : String → Option String
      | "==" => some "=" | "!=" => some "<>" | "<=" => some "<="
      | ">=" => some ">=" | "<" => some "<" | ">" => some ">" | _ => none
    let mut lhsStx := stx.getArg 0
    let mut parts : Array String := #[]
    for lk in links do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := lk.getArg 1
      let l ← recR lhsStx
      let part ←
        if forRls && opStr == "!=" && rhsStx.getKind == ``qedIdent &&
           (rhsStx.getArg 0).getId.eraseMacroScopes == `none then
          some s!"({l} IS NOT NULL AND {l} <> '')"
        else do
          let sqlOp ← mapOp opStr
          let r ← recR rhsStx
          some (if forRls then s!"({l} {sqlOp} {r})" else s!"{l} {sqlOp} {r}")
      parts := parts.push part
      lhsStx := rhsStx
    some (String.intercalate " AND " parts.toList)
  else none

open Lean Elab Command in
private def elabTableProtoAndJson (rowTypeId : Ident) (cols : Array ParsedCol) : CommandElabM Unit := do
  let specs : Array Qed.StructFieldSpec := cols.map fun c =>
    { ident := c.ident, wireKey := c.colName, valTy := c.tyTerm }
  for cmd in (← Qed.mkStructJsonCmds rowTypeId specs { emitNamedDefs := false }) ++
             (← Qed.mkStructProtoCmds rowTypeId specs { emitBytesCodec := false, emitLawful := true }) do
    elabCommand cmd

open Lean Elab Command in
@[command_elab databaseCmd]
def elabDatabaseCmd : CommandElab := fun stx => do
  let dbIdent : Ident := ⟨(stx.getArg 1)⟩
  let dbName := dbIdent.getId
  let currNs ← getCurrNamespace
  let fullDbName := currNs ++ dbName
  let clauses := (stx.getArg 3).getArgs

  let mut primaryEp? : Option Term := none
  let mut devEp?     : Option Term := none
  let mut secrets    : Array String := #[]
  let mut tables     : Array ParsedTable := #[]

  for c in clauses do
    let k := c.getKind
    if k == ``dbPrimaryEpClause then
      if primaryEp?.isSome then
        throwErrorAt c s!"duplicate endpoint specification in `database {dbName}`"
      let (epT, secs) ← parseEndpointSpec (c.getArg 0)
      primaryEp? := some epT
      for s in secs do
        if !secrets.contains s then secrets := secrets.push s
    else if k == ``dbDevEpClause then
      if devEp?.isSome then
        throwErrorAt c s!"duplicate `dev` endpoint fallback in `database {dbName}`"
      let (epT, _) ← parseEndpointSpec (c.getArg 1)
      devEp? := some epT
    else if k == ``dbTableClauseTop then
      let tIdent : Ident := ⟨(c.getArg 1)⟩
      let tName := tIdent.getId.eraseMacroScopes.toString
      if !isSafeSqlIdent tName then
        throwErrorAt tIdent s!"invalid SQL table name `{tName}`"
      if tables.any (·.tableName == tName) then
        throwErrorAt tIdent s!"duplicate `table {tName}` in `database {dbName}`"
      let subClauses := (c.getArg 3).getArgs
      let mut cols : Array ParsedCol := #[]
      let mut readPols : Array Syntax := #[]
      let mut insertPols : Array Syntax := #[]
      let mut updatePols : Array Syntax := #[]
      let mut deletePols : Array Syntax := #[]
      let mut singleInvs : Array Syntax := #[]
      let mut transInvs : Array Syntax := #[]
      let mut transChains : Array (Syntax × Array (Array Syntax)) := #[]
      let mut indexes : Array (Array Ident) := #[]

      for sc in subClauses do
        let sk := sc.getKind
        if sk == ``dbTableColClause then
          let colId : Ident := ⟨(sc.getArg 0)⟩
          let colName := colId.getId.eraseMacroScopes.toString
          if !isSafeSqlIdent colName then
            throwErrorAt colId s!"invalid SQL column name `{colName}`"
          if cols.any (·.colName == colName) then
            throwErrorAt colId s!"duplicate column `{colName}` in `table {tName}`"
          let pty ← liftMacroM <| lowerSrvType (sc.getArg 2) (allowFallible := false) s!"column `{colName}`"
          let tyTerm := pty.term
          let (sqlColType, isNullable, isNat, isBytes) := inferSqlColType pty
          let mods := (sc.getArg 3).getArgs
          let mut isPk := false
          let mut isImm := false
          let mut isUniq := false
          let mut refs? : Option (Ident × Ident) := none
          for m in mods do
            let mk := m.getKind
            if mk == ``dbModPk then isPk := true
            else if mk == ``dbModImmutable then isImm := true
            else if mk == ``dbModUnique then isUniq := true
            else if mk == ``dbModRefs then
              refs? := some (⟨(m.getArg 1)⟩, ⟨(m.getArg 3)⟩)
          let whereOpt := sc.getArg 4
          let whereExprs := if whereOpt.getNumArgs == 2 then (whereOpt.getArg 1).getSepArgs else #[]
          cols := cols.push {
            ref := sc, ident := colId, colName, tyTerm, sqlColType,
            isNullable, isNat, isBytes, isPrimaryKey := isPk, isImmutable := isImm,
            isUnique := isUniq, refs?, whereExprs
          }
        else if sk == ``dbTablePolicyClause then
          let ops := (sc.getArg 1).getSepArgs
          let exprs := (sc.getArg 3).getSepArgs
          for opNode in ops do
            let opName := (opNode.getArg 0).getId.eraseMacroScopes
            if opName == `read then readPols := readPols ++ exprs
            else if opName == `insert then insertPols := insertPols ++ exprs
            else if opName == `update then updatePols := updatePols ++ exprs
            else if opName == `delete then deletePols := deletePols ++ exprs
            else if opName == `write then
              insertPols := insertPols ++ exprs
              updatePols := updatePols ++ exprs
              deletePols := deletePols ++ exprs
        else if sk == ``dbTableTransInvClause then
          let targetExpr := sc.getArg 4
          let rawChains := (sc.getArg 6).getSepArgs
          let chains := rawChains.map fun ch => (ch.getArg 0).getSepArgs
          for ch in chains do
            if ch.size < 2 then
              throwErrorAt sc "`transition` invariant expects at least one `a -> b` transition arrow"
          transChains := transChains.push (targetExpr, chains)
        else if sk == ``dbTableInvClause then
          let exprs := (sc.getArg 3).getSepArgs
          for e in exprs do
            if Qed.Server.exprCallsOld e then transInvs := transInvs.push e
            else singleInvs := singleInvs.push e
        else if sk == ``dbTableIndexClause then
          let idxs := (sc.getArg 2).getSepArgs.map fun s => (⟨s⟩ : Ident)
          indexes := indexes.push idxs
        else
          throwErrorAt sc s!"unexpected clause in `table {tName}`"

      if cols.isEmpty then
        throwErrorAt tIdent s!"`table {tName}` must declare at least one column"
      tables := tables.push {
        ref := c, ident := tIdent, tableName := tName, cols,
        readPols, insertPols, updatePols, deletePols,
        singleInvs, transInvs, transChains, indexes
      }
    else
      throwErrorAt c s!"unexpected clause in `database {dbName}`"

  let some primaryEp := primaryEp?
    | throwErrorAt dbIdent s!"`database {dbName}` must specify an endpoint (e.g. `url secret(\"DATABASE_URL\")`, `postgres ...`, `sqlite ...`, `d1 ...`, `turso ...`, or `http ...`)"
  if tables.isEmpty then
    throwErrorAt dbIdent s!"`database {dbName}` must declare at least one `table`"

  -- Validate foreign keys and indexes against declared tables/columns
  for t in tables do
    let colNames := t.cols.map (·.colName)
    for col in t.cols do
      if let some (refTblId, refColId) := col.refs? then
        let rt := refTblId.getId.eraseMacroScopes.toString
        let rc := refColId.getId.eraseMacroScopes.toString
        let some targetTbl := tables.find? (·.tableName == rt)
          | throwErrorAt refTblId s!"table `{t.tableName}` column `{col.colName}` references unknown table `{rt}` in `database {dbName}`"
        unless targetTbl.cols.any (·.colName == rc) do
          throwErrorAt refColId s!"table `{t.tableName}` column `{col.colName}` references unknown column `{rt}.{rc}`"
    for idxCols in t.indexes do
      for ic in idxCols do
        let cn := ic.getId.eraseMacroScopes.toString
        unless colNames.contains cn do
          throwErrorAt ic s!"index on `table {t.tableName}` references unknown column `{cn}`"

  -- Marker for client-isolation verification (`Js.VerifyEnv.isDatabaseOwner`)
  let markerId := mkIdentFrom dbIdent (dbName ++ `_qed_database_marker)
  elabCommand (← `(command| def $markerId : Unit := ()))

  let mut tableInfos : Array DbTableInfo := #[]
  let mut tableSchemaTerms : Array Term := #[]

  for t in tables do
    let rowTypeName := dbName ++ t.ident.getId
    let fullRowTypeName := fullDbName ++ t.ident.getId
    let rowTypeId := mkIdentFrom t.ident rowTypeName
    let colNames := t.cols.map (·.colName)
    let fIds := t.cols.map (·.ident)
    let fTys := t.cols.map (·.tyTerm)
    let hasBytes := t.cols.any (·.isBytes)

    -- 1. Row structure + ToJson / FromJson / ToProto / FromProto / LawfulProto
    let derives := if hasBytes then #[mkIdent `Inhabited, mkIdent `DecidableEq]
      else #[mkIdent `Inhabited, mkIdent `DecidableEq, mkIdent `Repr]
    elabCommand (← `(command|
      structure $rowTypeId where
        $[$fIds:ident : $fTys:term]*
      deriving $[$derives:ident],*))
    elabTableProtoAndJson rowTypeId t.cols

    -- 2. Single-row invariant (`RowInv`, `rowInvBool`, `rowInvBool_sound`)
    let rowVar := mkIdent `_row
    let mut rowInvProps : Array Term := #[]
    let mut rowInvBools : Array Term := #[]
    for w in t.cols.flatMap (·.whereExprs) ++ t.singleInvs do
      rowInvProps := rowInvProps.push (← lowerDbExpr colNames rowVar none none true w)
      rowInvBools := rowInvBools.push (← lowerDbExpr colNames rowVar none none false w)

    let rowInvPropTerm ← Qed.mkConjBody rowInvProps (ascribeProp := false)
    let rowInvBoolTerm ← match rowInvBools.toList with
      | [] => `(true)
      | b :: rest => rest.foldlM (init := b) fun acc x => `($acc && $x)

    let rowInvId := mkIdentFrom t.ident (rowTypeName ++ `RowInv)
    let rowInvBoolId := mkIdentFrom t.ident (rowTypeName ++ `rowInvBool)
    let rowInvSoundId := mkIdentFrom t.ident (rowTypeName ++ `rowInvBool_sound)
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      @[simp] abbrev $rowInvId ($rowVar:ident : $rowTypeId) : Prop := $rowInvPropTerm))
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $rowInvBoolId ($rowVar:ident : $rowTypeId) : Bool := $rowInvBoolTerm))
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      theorem $rowInvSoundId ($rowVar:ident : $rowTypeId) (h : $rowInvBoolId $rowVar = true) :
          $rowInvId $rowVar := by
        unfold $rowInvBoolId at h
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                   beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Qed.Lang.QedVal.val_id] at h
        try exact trivial
        try exact h
        try simp_all))

    -- 3. Two-state & transition invariant (`TransInv`)
    let oldVar := mkIdent `_old
    let mut transProps : Array Term := #[]
    for ti in t.transInvs do
      transProps := transProps.push (← lowerDbExpr colNames rowVar (some oldVar) none true ti)
    for (tgtStx, chains) in t.transChains do
      let oldTgt ← lowerDbExpr colNames oldVar none none false tgtStx
      let newTgt ← lowerDbExpr colNames rowVar none none false tgtStx
      let mut disj ← `($newTgt = $oldTgt)
      for ch in chains do
        for i in [0 : ch.size - 1] do
          let aT ← lowerDbExpr colNames rowVar none none false ch[i]!
          let bT ← lowerDbExpr colNames rowVar none none false ch[i + 1]!
          disj ← `($disj ∨ ($oldTgt = $aT ∧ $newTgt = $bT))
      transProps := transProps.push disj

    let transInvTerm ← Qed.mkConjBody transProps (ascribeProp := false)
    let transInvId := mkIdentFrom t.ident (rowTypeName ++ `TransInv)
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      @[simp] abbrev $transInvId ($oldVar:ident $rowVar:ident : $rowTypeId) : Prop := $transInvTerm))

    -- 4. Row-Level Authorization Policies (`ReadPolicy`, `InsertPolicy`, `UpdatePolicy`, `DeletePolicy`)
    let ctxVar := mkIdent `_ctx
    let mkPolDef (polSuffix : Name) (polExprs : Array Syntax) : CommandElabM (Ident × String) := do
      let mut ps : Array Term := #[]
      let mut lbls : Array String := #[]
      for pe in polExprs do
        ps := ps.push (← lowerDbExpr colNames rowVar none (some ctxVar) true pe)
        lbls := lbls.push ((pe.reprint.getD "policy").trimAscii.toString)
      let conj ← Qed.mkConjBody ps (ascribeProp := false)
      let pid := mkIdentFrom t.ident (rowTypeName ++ polSuffix)
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $pid ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj))
      return (pid, String.intercalate " and " lbls.toList)

    let (_, readPolLbl) ← mkPolDef `ReadPolicy t.readPols
    let (_, insertPolLbl) ← mkPolDef `InsertPolicy t.insertPols
    let (_, updatePolLbl) ← mkPolDef `UpdatePolicy t.updatePols
    let (_, deletePolLbl) ← mkPolDef `DeletePolicy t.deletePols

    -- 5. Zero-trust SQL row decoder (`decodeRow`)
    let valsVar := mkIdent `_vals
    let decId := mkIdentFrom t.ident (rowTypeName ++ `decodeRow)
    let colDecStmts ← t.cols.zipIdx.mapM fun (col, idx) => do
      let idxLit := Syntax.mkNumLit (toString idx)
      let fTy := col.tyTerm
      let cLit := Syntax.mkStrLit col.colName
      `(match ($valsVar)[$idxLit]? with
        | some _v => Qed.Server.Db.FromSql.fromSql (α := $fTy) _v
        | none    => Except.error ("missing column `" ++ $cLit ++ "` in database row"))
    let fVals2 := fIds
    elabCommand (← `(command|
      def $decId ($valsVar:ident : Qed.Server.Db.DbRow) : Except String $rowTypeId := do
        $[let $fIds:ident ← $colDecStmts:term]*
        return { $[$fIds:ident := $fVals2:ident],* }))

    -- 6. TableSchema metadata + DDL / Postgres RLS
    let optSqlStr (parts : Array String) : CommandElabM Term :=
      if parts.isEmpty then `(none)
      else `(some $(Syntax.mkStrLit (String.intercalate " AND " parts.toList)))
    let tblSqlId ← mkSqlIdentTerm t.ident t.tableName
    let colSchemaTerms ← t.cols.mapM fun col => do
      let cSqlId ← mkSqlIdentTerm col.ident col.colName
      let cTyT : Term := mkIdent <| match col.sqlColType with
        | .text  => `Qed.Server.Db.SqlColType.text  | .int   => `Qed.Server.Db.SqlColType.int
        | .bool  => `Qed.Server.Db.SqlColType.bool  | .bytes => `Qed.Server.Db.SqlColType.bytes
      let refT : Term ← match col.refs? with
        | some (rt, rc) =>
            `(some ($(← mkSqlIdentTerm rt rt.getId.eraseMacroScopes.toString), $(← mkSqlIdentTerm rc rc.getId.eraseMacroScopes.toString)))
        | none => `(none)
      let chkParts := (if col.isNat && !col.isNullable then #["\"" ++ col.colName ++ "\" >= 0"] else #[]) ++
        col.whereExprs.filterMap (renderSqlPred? colNames false)
      `({ name := $cSqlId, colType := $cTyT, nullable := $(quote col.isNullable),
          isPrimaryKey := $(quote col.isPrimaryKey), isUnique := $(quote col.isUnique),
          isImmutable := $(quote col.isImmutable), references? := $refT, checkSql? := $(← optSqlStr chkParts)
          : Qed.Server.Db.ColumnSchema })
    let idxTerms ← t.indexes.mapM fun idxs => do
      let ids ← idxs.mapM fun ic => mkSqlIdentTerm ic ic.getId.eraseMacroScopes.toString
      `([$[$ids:term],*])
    let rlsReadT ← optSqlStr (t.readPols.filterMap (renderSqlPred? colNames true))
    let rlsWriteT ← optSqlStr (t.updatePols.filterMap (renderSqlPred? colNames true))

    let schemaId := mkIdentFrom t.ident (rowTypeName ++ `schema)
    elabCommand (← `(command|
      def $schemaId : Qed.Server.Db.TableSchema := {
        name      := $tblSqlId
        columns   := [$[$colSchemaTerms:term],*]
        indexes   := [$[$idxTerms:term],*]
        rlsRead?  := $rlsReadT
        rlsWrite? := $rlsWriteT
      }))
    tableSchemaTerms := tableSchemaTerms.push (← `($schemaId))

    tableInfos := tableInfos.push {
      tableName         := t.tableName
      rowTypeConst      := fullRowTypeName
      rowInvConst       := fullRowTypeName ++ `RowInv
      rowInvBoolConst   := fullRowTypeName ++ `rowInvBool
      rowInvSoundConst  := fullRowTypeName ++ `rowInvBool_sound
      transInvConst     := fullRowTypeName ++ `TransInv
      readPolicyConst   := fullRowTypeName ++ `ReadPolicy
      insertPolicyConst := fullRowTypeName ++ `InsertPolicy
      updatePolicyConst := fullRowTypeName ++ `UpdatePolicy
      deletePolicyConst := fullRowTypeName ++ `DeletePolicy
      decodeRowConst    := fullRowTypeName ++ `decodeRow
      columns           := t.cols.map fun c => {
        name := c.colName, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable,
        isUnique := c.isUnique, isNullable := c.isNullable, isNat := c.isNat,
        refs? := c.refs?.map fun (rt, rc) => (rt.getId.eraseMacroScopes.toString, rc.getId.eraseMacroScopes.toString)
      }
      hasReadPolicy     := !t.readPols.isEmpty
      hasInsertPolicy   := !t.insertPols.isEmpty
      hasUpdatePolicy   := !t.updatePols.isEmpty
      hasDeletePolicy   := !t.deletePols.isEmpty
      hasTransInv       := !t.transInvs.isEmpty || !t.transChains.isEmpty
      readPolicyLabel   := readPolLbl
      insertPolicyLabel := insertPolLbl
      updatePolicyLabel := updatePolLbl
      deletePolicyLabel := deletePolLbl
    }

  -- Database-level config, DDL, RLS DDL, secrets, and `ensureSchema`
  let dbShort := dbName.toString
  let devEpTerm ← match devEp? with | some dt => `(some $dt) | none => `(none)
  let (configId, ddlId, rlsDdlId, secretsId, ensureId, safeEnsureId, mId) :=
    (mkIdentFrom dbIdent (dbName ++ `config), mkIdentFrom dbIdent (dbName ++ `ddl),
     mkIdentFrom dbIdent (dbName ++ `rlsDdl), mkIdentFrom dbIdent (dbName ++ `secrets),
     mkIdentFrom dbIdent (dbName ++ `ensureSchema), mkIdentFrom dbIdent (dbName ++ `instSafeIOEnsureSchema), mkIdent `m)
  let secLits := secrets.map Syntax.mkStrLit
  for cmd in #[
    ← `(command| def $secretsId : Array String := #[$[$secLits:term],*]),
    ← `(command| def $configId : Qed.Server.Db.DbConfig := {
        name := $(Syntax.mkStrLit dbShort), endpoint := $primaryEp,
        devFallback? := $devEpTerm, tables := [$[$tableSchemaTerms:term],*] }),
    ← `(command| def $ddlId (dialect : Qed.Server.Db.SqlDialect := .postgres) : String :=
        Qed.Server.Db.renderDatabaseDdl dialect ($configId).tables),
    ← `(command| def $rlsDdlId : String := Qed.Server.Db.renderDatabaseRlsDdl ($configId).tables),
    ← `(command| def $ensureId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] :
        $mId (Except Qed.Server.ApiError Unit) := Qed.Server.MonadServer.dbExecDdl $configId),
    ← `(command| instance $safeEnsureId:ident {_σ : Type} :
        Qed.Server.SafeIO (@$ensureId (Qed.Server.ThreadProg _σ) _ _) where
          noAtomic := .io (.dbExecDdl $configId) _ .pure)
  ] do elabCommand cmd

  modifyEnv fun env => databaseRegistry.addEntry env {
    dbName            := fullDbName
    shortName         := dbShort
    configConst       := fullDbName ++ `config
    ensureSchemaConst := fullDbName ++ `ensureSchema
    secrets           := secrets
    hasDevFallback    := devEp?.isSome
    tables            := tableInfos
  }

end Qed.Server.Db
