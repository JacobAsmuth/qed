import Lean
import Qed.Lang
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

private structure ParsedEnvRef where
  isSecret : Bool
  envKey   : String
  default? : Option String

private structure ParsedCol where
  ref          : Lean.Syntax
  ident        : Lean.Ident
  colName      : String
  ty           : ParsedSrvType
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
private def parseEnvRef (stx : Syntax) : CommandElabM ParsedEnvRef := do
  let kwId := (stx.getArg 0).getId.eraseMacroScopes
  let isSecret := kwId == `secret
  let envKey := (⟨(stx.getArg 2)⟩ : TSyntax `str).getString
  let defOpt := stx.getArg 4
  let def? := if defOpt.getNumArgs == 2 then some ((⟨(defOpt.getArg 1)⟩ : TSyntax `str).getString) else none
  if envKey.isEmpty then
    throwErrorAt stx "database environment variable name must not be empty"
  return { isSecret, envKey, default? := def? }

open Lean Elab Command in
private def parseEndpointSpec (stx : Syntax) :
    CommandElabM (Term × Array String) := do
  let k := stx.getKind
  let mut secs : Array String := #[]
  if k == ``dbEpUrl then
    let er ← parseEnvRef (stx.getArg 1)
    if er.isSecret then secs := secs.push er.envKey
    let kLit := Syntax.mkStrLit er.envKey
    return (← `(Qed.Server.Db.DbEndpoint.urlEnv $kLit), secs)
  else if k == ``dbEpPostgres then
    let er ← parseEnvRef (stx.getArg 1)
    if er.isSecret then secs := secs.push er.envKey
    let kLit := Syntax.mkStrLit er.envKey
    return (← `(Qed.Server.Db.DbEndpoint.postgresEnv $kLit), secs)
  else if k == ``dbEpSqliteLit then
    let pStr := (⟨(stx.getArg 1)⟩ : TSyntax `str).getString
    let pLit := Syntax.mkStrLit pStr
    return (← `(Qed.Server.Db.DbEndpoint.sqlitePath $pLit), secs)
  else if k == ``dbEpSqliteEnv then
    let er ← parseEnvRef (stx.getArg 1)
    if er.isSecret && er.default?.isNone then secs := secs.push er.envKey
    let kLit := Syntax.mkStrLit er.envKey
    let defTerm ← match er.default? with
      | some d => let dLit := Syntax.mkStrLit d; `(some $dLit)
      | none   => `(none)
    return (← `(Qed.Server.Db.DbEndpoint.sqliteEnv $kLit $defTerm), secs)
  else if k == ``dbEpD1 then
    let acc ← parseEnvRef (stx.getArg 3)
    let db  ← parseEnvRef (stx.getArg 7)
    let tok ← parseEnvRef (stx.getArg 11)
    if tok.isSecret then secs := secs.push tok.envKey
    let accKey := Syntax.mkStrLit acc.envKey
    let accDef ← match acc.default? with | some d => `(some $(Syntax.mkStrLit d)) | none => `(none)
    let dbKey := Syntax.mkStrLit db.envKey
    let dbDef ← match db.default? with | some d => `(some $(Syntax.mkStrLit d)) | none => `(none)
    let tokKey := Syntax.mkStrLit tok.envKey
    return (← `(Qed.Server.Db.DbEndpoint.cloudflareD1 $accKey $accDef $dbKey $dbDef $tokKey), secs)
  else if k == ``dbEpTurso then
    let u   ← parseEnvRef (stx.getArg 3)
    let tok ← parseEnvRef (stx.getArg 7)
    if u.isSecret then secs := secs.push u.envKey
    if tok.isSecret then secs := secs.push tok.envKey
    return (← `(Qed.Server.Db.DbEndpoint.turso $(Syntax.mkStrLit u.envKey) $(Syntax.mkStrLit tok.envKey)), secs)
  else if k == ``dbEpHttp then
    let u ← parseEnvRef (stx.getArg 3)
    if u.isSecret then secs := secs.push u.envKey
    let tokOpt := stx.getArg 4
    let tokTerm ← if tokOpt.getNumArgs == 4 then do
      let tok ← parseEnvRef (tokOpt.getArg 3)
      if tok.isSecret then secs := secs.push tok.envKey
      `(some $(Syntax.mkStrLit tok.envKey))
    else `(none)
    return (← `(Qed.Server.Db.DbEndpoint.httpSql $(Syntax.mkStrLit u.envKey) $tokTerm), secs)
  else
    throwErrorAt stx "unexpected database endpoint specification"

private def inferSqlColType (pty : ParsedSrvType) : SqlColType × Bool × Bool × Bool :=
  let base := pty.baseIdent.getId.eraseMacroScopes
  let isNullable := pty.mods.back? == some .option
  if base == `Nat then (.int, isNullable, true, false)
  else if base == `Int then (.int, isNullable, false, false)
  else if base == `Bool then (.bool, isNullable, false, false)
  else if base == `Bytes || base == `ByteArray then (.bytes, isNullable, false, true)
  else (.text, isNullable, false, false)

private partial def dbExprUsesOld (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``qedCall then
    let callee := stx.getArg 0
    if callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `old then true
    else stx.getArgs.any dbExprUsesOld
  else stx.getArgs.any dbExprUsesOld

open Lean Elab Command in
private partial def lowerDbExpr (colNames : Array String) (rowVar : Ident)
    (oldVar? : Option Ident) (ctxVar? : Option Ident) (asProp : Bool) (stx : Syntax) :
    CommandElabM Term := do
  let k := stx.getKind
  let recL (s : Syntax) (p : Bool := asProp) := lowerDbExpr colNames rowVar oldVar? ctxVar? p s
  if k == ``qedLitNum then
    let n : TSyntax `num := ⟨(stx.getArg 0)⟩
    return ⟨n.raw⟩
  else if k == ``qedLitStr then
    let s : TSyntax `str := ⟨(stx.getArg 0)⟩
    return ⟨s.raw⟩
  else if k == ``qedLitChar then
    let c : TSyntax `char := ⟨(stx.getArg 0)⟩
    return ⟨c.raw⟩
  else if k == ``qedDotIdent then
    let ctor : Ident := ⟨(stx.getArg 1)⟩
    `(.$ctor)
  else if k == ``qedIdent then
    let id : Ident := ⟨(stx.getArg 0)⟩
    let comps := id.getId.eraseMacroScopes.components
    let foldProjs (base : Term) (rest : List Name) : CommandElabM Term :=
      rest.foldlM (init := base) fun acc f => do
        let fId := mkIdentFrom stx f
        `(($acc).$fId:ident)
    match comps with
    | [] => throwErrorAt stx "empty identifier in database predicate"
    | [single] =>
        let s := single.toString
        if s == "true" then if asProp then `(True) else `(true)
        else if s == "false" then if asProp then `(False) else `(false)
        else if s == "none" then `(Option.none)
        else if s == "row" then return ⟨rowVar.raw⟩
        else if s == "ctx" then
          match ctxVar? with
          | some cv => return ⟨cv.raw⟩
          | none    => throwErrorAt stx "`ctx` is only in scope inside `policy ... requires ...`"
        else if colNames.contains s then
          let fId := mkIdentFrom stx single
          `($rowVar.$fId)
        else
          return ⟨id.raw⟩
    | root :: rest =>
        let rs := root.toString
        if rs == "row" then
          foldProjs ⟨rowVar.raw⟩ rest
        else if rs == "ctx" then
          match ctxVar? with
          | some cv => foldProjs ⟨cv.raw⟩ rest
          | none    => throwErrorAt stx "`ctx` is only in scope inside `policy ... requires ...`"
        else if colNames.contains rs then
          let fId := mkIdentFrom stx root
          foldProjs (← `($rowVar.$fId)) rest
        else
          return ⟨id.raw⟩
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs
    if args.size == 1 then recL args[0]! asProp
    else throwErrorAt stx "unsupported tuple in database predicate"
  else if k == ``qedProj then
    let base := stx.getArg 0
    let field : Ident := ⟨(stx.getArg 2)⟩
    let bTerm ← recL base false
    `($bTerm.$field)
  else if k == ``qedNeg then
    let inner ← recL (stx.getArg 1) false
    `(-$inner)
  else if k == ``qedAdd then
    `($(← recL (stx.getArg 0) false) + $(← recL (stx.getArg 2) false))
  else if k == ``qedSub then
    `($(← recL (stx.getArg 0) false) - $(← recL (stx.getArg 2) false))
  else if k == ``qedMul then
    `($(← recL (stx.getArg 0) false) * $(← recL (stx.getArg 2) false))
  else if k == ``qedDiv then
    `($(← recL (stx.getArg 0) false) / $(← recL (stx.getArg 2) false))
  else if k == ``qedMod then
    `($(← recL (stx.getArg 0) false) % $(← recL (stx.getArg 2) false))
  else if k == ``qedNot then
    if asProp then `(¬ $(← recL (stx.getArg 1) true))
    else `(! $(← recL (stx.getArg 1) false))
  else if k == ``qedAnd then
    if asProp then `($(← recL (stx.getArg 0) true) ∧ $(← recL (stx.getArg 2) true))
    else `($(← recL (stx.getArg 0) false) && $(← recL (stx.getArg 2) false))
  else if k == ``qedOr then
    if asProp then `($(← recL (stx.getArg 0) true) ∨ $(← recL (stx.getArg 2) true))
    else `($(← recL (stx.getArg 0) false) || $(← recL (stx.getArg 2) false))
  else if k == ``qedImp then
    if asProp then `($(← recL (stx.getArg 0) true) → $(← recL (stx.getArg 2) true))
    else `((! $(← recL (stx.getArg 0) false)) || $(← recL (stx.getArg 2) false))
  else if k == ``qedCmp then
    let links := (stx.getArg 1).getArgs
    let mut lhsStx := stx.getArg 0
    let mut clauses : Array Term := #[]
    for lk in links do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := lk.getArg 1
      let l ← recL lhsStx false
      let r ← recL rhsStx false
      let c ←
        if asProp then
          match opStr with
          | "==" => `($l = $r)
          | "!=" => `($l ≠ $r)
          | "<=" => `($l ≤ $r)
          | ">=" => `($l ≥ $r)
          | "<"  => `($l < $r)
          | ">"  => `($l > $r)
          | _ => throwErrorAt lk s!"unsupported comparison `{opStr}` in database predicate"
        else
          match opStr with
          | "==" => `($l == $r)
          | "!=" => `($l != $r)
          | "<=" => `(decide ($l ≤ $r))
          | ">=" => `(decide ($l ≥ $r))
          | "<"  => `(decide ($l < $r))
          | ">"  => `(decide ($l > $r))
          | _ => throwErrorAt lk s!"unsupported comparison `{opStr}` in database predicate"
      clauses := clauses.push c
      lhsStx := rhsStx
    match clauses.toList with
    | [] => if asProp then `(True) else `(true)
    | c :: rest =>
        rest.foldlM (init := c) fun acc x =>
          if asProp then `($acc ∧ $x) else `($acc && $x)
  else if k == ``qedCall then
    let callee := stx.getArg 0
    let rawArgs := (stx.getArg 2).getSepArgs
    if callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `old then
      let some ov := oldVar?
        | throwErrorAt stx "`old(...)` is only allowed inside two-state table `invariant` clauses"
      if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
        throwErrorAt stx "`old(...)` expects a single expression argument"
      lowerDbExpr colNames ov none ctxVar? asProp (rawArgs[0]!.getArg 0)
    else if callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `some then
      if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
        throwErrorAt stx "`some(...)` expects a single argument"
      `(Option.some $(← recL (rawArgs[0]!.getArg 0) false))
    else
      let fnT ← recL callee false
      let argTs ← rawArgs.mapM fun a => do
        if a.getKind != ``qedCallArgPos then
          throwErrorAt a "unexpected named argument in database expression"
        recL (a.getArg 0) false
      let appT ← argTs.foldlM (init := fnT) fun acc a => `($acc $a)
      if asProp then `(qedAsProp($appT)) else return appT
  else
    let sn := stxSnippet stx
    throwErrorAt stx s!"unsupported expression `{sn}` in `database` predicate"

/-- Best-effort static SQL `CHECK (...)` expression renderer for column `where` clauses. -/
private partial def renderCheckSql? (colNames : Array String) (stx : Lean.Syntax) : Option String :=
  let k := stx.getKind
  if k == ``qedLitNum then
    let n : Lean.TSyntax `num := ⟨(stx.getArg 0)⟩
    some (toString n.getNat)
  else if k == ``qedIdent then
    let comps := (stx.getArg 0).getId.eraseMacroScopes.components.map (·.toString)
    match comps with
    | [s] =>
        if colNames.contains s then some ("\"" ++ s ++ "\"")
        else if s == "true" then some "1"
        else if s == "false" then some "0"
        else none
    | [col, "length"] =>
        if colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | ["row", col] =>
        if colNames.contains col then some ("\"" ++ col ++ "\"") else none
    | ["row", col, "length"] =>
        if colNames.contains col then some ("LENGTH(\"" ++ col ++ "\")") else none
    | _ => none
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs
    if args.size == 1 then (renderCheckSql? colNames args[0]!).map fun s => "(" ++ s ++ ")" else none
  else if k == ``qedProj then
    let field := (stx.getArg 2).getId.eraseMacroScopes.toString
    if field == "length" then
      (renderCheckSql? colNames (stx.getArg 0)).map fun s => "LENGTH(" ++ s ++ ")"
    else if (stx.getArg 0).getKind == ``qedIdent &&
            ((stx.getArg 0).getArg 0).getId.eraseMacroScopes == `row &&
            colNames.contains field then
      some ("\"" ++ field ++ "\"")
    else none
  else if k == ``qedAnd then do
    let l ← renderCheckSql? colNames (stx.getArg 0)
    let r ← renderCheckSql? colNames (stx.getArg 2)
    return "(" ++ l ++ " AND " ++ r ++ ")"
  else if k == ``qedOr then do
    let l ← renderCheckSql? colNames (stx.getArg 0)
    let r ← renderCheckSql? colNames (stx.getArg 2)
    return "(" ++ l ++ " OR " ++ r ++ ")"
  else if k == ``qedNot then
    (renderCheckSql? colNames (stx.getArg 1)).map fun s => "(NOT " ++ s ++ ")"
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs
    let mut lhsStx := stx.getArg 0
    let mut parts : Array String := #[]
    for lk in links do
      let opStr := ((lk.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := lk.getArg 1
      let sqlOp ← match opStr with
        | "==" => some "=" | "!=" => some "<>" | "<=" => some "<="
        | ">=" => some ">=" | "<" => some "<" | ">" => some ">"
        | _ => none
      let l ← renderCheckSql? colNames lhsStx
      let r ← renderCheckSql? colNames rhsStx
      parts := parts.push s!"{l} {sqlOp} {r}"
      lhsStx := rhsStx
    if parts.isEmpty then none
    else some (String.intercalate " AND " parts.toList)
  else none

/-- Best-effort Postgres RLS `USING (...)` expression renderer for `policy ... requires ...`. -/
private partial def renderRlsSql? (colNames : Array String) (stx : Lean.Syntax) : Option String :=
  let k := stx.getKind
  if k == ``qedProj then
    let b := stx.getArg 0
    let f := (stx.getArg 2).getId.eraseMacroScopes.toString
    if b.getKind == ``qedIdent && (b.getArg 0).getId.eraseMacroScopes == `ctx && f == "userId" then
      some "current_setting('qed.user_id', true)"
    else if b.getKind == ``qedIdent && (b.getArg 0).getId.eraseMacroScopes == `row && colNames.contains f then
      some ("\"" ++ f ++ "\"")
    else none
  else if k == ``qedCall then
    let callee := stx.getArg 0
    let rawArgs := (stx.getArg 2).getSepArgs
    if callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `some &&
       rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos then
      renderRlsSql? colNames (rawArgs[0]!.getArg 0)
    else none
  else if k == ``qedIdent then
    let comps := (stx.getArg 0).getId.eraseMacroScopes.components.map (·.toString)
    match comps with
    | [s] =>
        if colNames.contains s then some ("\"" ++ s ++ "\"")
        else if s == "true" then some "TRUE"
        else if s == "false" then some "FALSE"
        else none
    | ["ctx", "userId"] => some "current_setting('qed.user_id', true)"
    | ["row", col] =>
        if colNames.contains col then some ("\"" ++ col ++ "\"") else none
    | _ => none
  else if k == ``qedParen then
    let args := (stx.getArg 1).getSepArgs
    if args.size == 1 then (renderRlsSql? colNames args[0]!).map fun s => "(" ++ s ++ ")" else none
  else if k == ``qedAnd then do
    let l ← renderRlsSql? colNames (stx.getArg 0)
    let r ← renderRlsSql? colNames (stx.getArg 2)
    return "(" ++ l ++ " AND " ++ r ++ ")"
  else if k == ``qedOr then do
    let l ← renderRlsSql? colNames (stx.getArg 0)
    let r ← renderRlsSql? colNames (stx.getArg 2)
    return "(" ++ l ++ " OR " ++ r ++ ")"
  else if k == ``qedCmp then do
    let links := (stx.getArg 1).getArgs
    if links.size != 1 then none
    else
      let opStr := ((links[0]!.getArg 0).reprint.getD "").trimAscii.toString
      let rhsStx := links[0]!.getArg 1
      let lhsStx := stx.getArg 0
      if opStr == "!=" && rhsStx.getKind == ``qedIdent && (rhsStx.getArg 0).getId.eraseMacroScopes == `none then
        let l ← renderRlsSql? colNames lhsStx
        some s!"({l} IS NOT NULL AND {l} <> '')"
      else
        let sqlOp ← match opStr with
          | "==" => some "=" | "!=" => some "<>" | "<=" => some "<="
          | ">=" => some ">=" | "<" => some "<" | ">" => some ">"
          | _ => none
        let l ← renderRlsSql? colNames lhsStx
        let r ← renderRlsSql? colNames rhsStx
        some s!"({l} {sqlOp} {r})"
  else none

open Lean Elab Command in
private def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  let lit := Syntax.mkStrLit raw
  `(Qed.Server.Db.SqlIdent.mk $lit (by decide))

open Lean Elab Command in
private def elabTableProtoAndJson (rowTypeId : Ident) (rowTypeName : Name)
    (cols : Array ParsedCol) : CommandElabM Unit := do
  let xId := mkIdent `x
  let jId := mkIdent `j
  let fsId := mkIdent `fs
  let fIds := cols.map (·.ident)
  let fTys := cols.map (·.tyTerm)
  let fLits := cols.map fun c => Syntax.mkStrLit c.colName

  -- `ToJson` & `FromJson`
  let jsonPairs ← cols.mapM fun c => do
    let fId := c.ident
    let kLit := Syntax.mkStrLit c.colName
    `(($kLit, Qed.ToJson.toJson ($xId.$fId)))
  let jsonDecs ← cols.mapM fun c => do
    let kLit := Syntax.mkStrLit c.colName
    let fTy := c.tyTerm
    `(Qed.FromJsonField.fromField (α := $fTy) $jId $kLit)
  let toJsonInstId := mkIdent (rowTypeName ++ `instToJson)
  let fromJsonInstId := mkIdent (rowTypeName ++ `instFromJson)
  elabCommand (← `(command|
    instance $toJsonInstId:ident : Qed.ToJson $rowTypeId where
      toJson $xId:ident := Qed.Json.obj [$[$jsonPairs:term],*]))
  let fVals := fIds
  elabCommand (← `(command|
    instance $fromJsonInstId:ident : Qed.FromJson $rowTypeId where
      fromJson $jId:ident := do
        $[let $fIds:ident ← $jsonDecs:term]*
        return { $[$fIds:ident := $fVals:ident],* }))

  -- `ToProto` & `FromProto` & `LawfulProto`
  let nFields := cols.size
  let toId := mkIdent (rowTypeName ++ `toProtoFields)
  let fromId := mkIdent (rowTypeName ++ `fromProtoFields)
  let emptyList ← `(term| ([] : List (Nat × Qed.Proto.WireVal)))
  let mut tails : Array Term := Array.replicate (nFields + 1) emptyList
  let mut tagsPosPf ← `(term| (fun (_ : Nat × Qed.Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  for revIdx in [0:nFields] do
    let i := nFields - 1 - revIdx
    let iLit := Syntax.mkNumLit (toString i)
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let fId := fIds[i]!
    let rd ← `($xId.$fId)
    tails := tails.set! i (← `(term| Qed.ToProtoField.encodeProtoField $kLit $rd ++ $(tails[i + 1]!)))
    tagsPosPf ← `(term| Qed.Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $iLit) $rd $tagsPosPf)
  let protoBody := tails[0]!

  let protoDecs ← (List.range nFields).toArray.mapM fun i => do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let fTy := fTys[i]!
    `(Qed.FromProtoField.decodeProtoField (α := $fTy) $kLit $fsId)

  let mut pIdents : Array Ident := #[]
  let mut pHaveTacs : Array (TSyntax `tactic) := #[]
  for i in [0:nFields] do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let fTy := fTys[i]!
    let fId := fIds[i]!
    let rd ← `($xId.$fId)
    let mut gtPf ← `(term| Qed.Proto.allTagsGt_nil $kLit)
    for revAfter in [0 : nFields - 1 - i] do
      let j := nFields - 1 - revAfter
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (j - i - 1))
      let fjId := fIds[j]!
      let rdj ← `($xId.$fjId)
      gtPf ← `(term| Qed.Proto.allTagsGt_encodeAppend (Nat.lt_of_sub_eq_succ (rfl : $jLit - $kLit = Nat.succ $diffPredLit)) $rdj $gtPf)
    let mut rawEq ← `(term| Qed.Proto.decodeProtoField_hit $kLit $rd $(tails[i + 1]!) $gtPf)
    for revBefore in [0:i] do
      let j := i - 1 - revBefore
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (i - j - 1))
      let fjId := fIds[j]!
      let rdj ← `($xId.$fjId)
      rawEq ← `(term| Eq.trans (Qed.Proto.decodeProtoField_skip (α := $fTy) (Nat.ne_of_lt (Nat.lt_of_sub_eq_succ (rfl : $kLit - $jLit = Nat.succ $diffPredLit))) $rdj $(tails[j + 1]!)) $rawEq)
    let hId := mkIdent (Name.mkSimple s!"_hp{i}")
    pIdents := pIdents.push hId
    pHaveTacs := pHaveTacs.push (← `(tactic| have $hId:ident := $rawEq))

  let toProtoInstId := mkIdent (rowTypeName ++ `instToProto)
  let fromProtoInstId := mkIdent (rowTypeName ++ `instFromProto)
  let lawfulProtoInstId := mkIdent (rowTypeName ++ `instLawfulProto)
  let fromProtoThmId := mkIdent (rowTypeName ++ `_fromProto_toProto)
  let _ := fLits
  elabCommand (← `(command|
    def $toId ($xId:ident : $rowTypeId) : List (Nat × Qed.Proto.WireVal) := $protoBody))
  elabCommand (← `(command|
    def $fromId ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $rowTypeId := do
      $[let $fIds:ident ← $protoDecs:term]*
      return { $[$fIds:ident := $fVals:ident],* }))
  elabCommand (← `(command|
    instance $toProtoInstId:ident : Qed.ToProto $rowTypeId := .ofFields $toId))
  elabCommand (← `(command|
    instance $fromProtoInstId:ident : Qed.FromProto $rowTypeId := .ofFields $fromId))
  elabCommand (← `(command|
    private theorem $fromProtoThmId ($xId:ident : $rowTypeId) : $fromId ($toId $xId) = Except.ok $xId := by
      $[$pHaveTacs:tactic]*
      unfold $fromId $toId
      simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]))
  elabCommand (← `(command|
    instance $lawfulProtoInstId:ident : Qed.LawfulProto $rowTypeId :=
      .ofFields $toId $fromId (fun $xId => $tagsPosPf) $fromProtoThmId))

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
          let pty ← liftMacroM <| ParsedSrvType.parse (sc.getArg 2)
          liftMacroM <| pty.validate (allowFallible := false) s!"column `{colName}`"
          let tyTerm ← liftMacroM pty.toPayloadTerm
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
            ref := sc, ident := colId, colName, ty := pty, tyTerm, sqlColType,
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
            if dbExprUsesOld e then transInvs := transInvs.push e
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
    if hasBytes then
      elabCommand (← `(command|
        structure $rowTypeId where
          $[$fIds:ident : $fTys:term]*
        deriving Inhabited, DecidableEq))
    else
      elabCommand (← `(command|
        structure $rowTypeId where
          $[$fIds:ident : $fTys:term]*
        deriving Inhabited, DecidableEq, Repr))
    elabTableProtoAndJson rowTypeId rowTypeName t.cols

    -- 2. Single-row invariant (`RowInv`, `rowInvBool`, `rowInvBool_sound`)
    let rowVar := mkIdent `_row
    let mut rowInvProps : Array Term := #[]
    let mut rowInvBools : Array Term := #[]
    for col in t.cols do
      for w in col.whereExprs do
        rowInvProps := rowInvProps.push (← lowerDbExpr colNames rowVar none none true w)
        rowInvBools := rowInvBools.push (← lowerDbExpr colNames rowVar none none false w)
    for inv in t.singleInvs do
      rowInvProps := rowInvProps.push (← lowerDbExpr colNames rowVar none none true inv)
      rowInvBools := rowInvBools.push (← lowerDbExpr colNames rowVar none none false inv)

    let rowInvPropTerm ← buildPropConj rowInvProps
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
                   beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at h
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

    let transInvTerm ← buildPropConj transProps
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
      let conj ← buildPropConj ps
      let pid := mkIdentFrom t.ident (rowTypeName ++ polSuffix)
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $pid ($ctxVar:ident : Qed.Server.RequestCtx) ($rowVar:ident : $rowTypeId) : Prop := $conj))
      return (pid, String.intercalate " and " lbls.toList)

    let (readPolId, readPolLbl) ← mkPolDef `ReadPolicy t.readPols
    let (insertPolId, insertPolLbl) ← mkPolDef `InsertPolicy t.insertPols
    let (updatePolId, updatePolLbl) ← mkPolDef `UpdatePolicy t.updatePols
    let (deletePolId, deletePolLbl) ← mkPolDef `DeletePolicy t.deletePols

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
    let tblSqlId ← mkSqlIdentTerm t.ident t.tableName
    let colSchemaTerms ← t.cols.mapM fun col => do
      let cSqlId ← mkSqlIdentTerm col.ident col.colName
      let cTyT : Term ← match col.sqlColType with
        | .text  => `(Qed.Server.Db.SqlColType.text)
        | .int   => `(Qed.Server.Db.SqlColType.int)
        | .bool  => `(Qed.Server.Db.SqlColType.bool)
        | .bytes => `(Qed.Server.Db.SqlColType.bytes)
      let nn := quote col.isNullable
      let pk := quote col.isPrimaryKey
      let uq := quote col.isUnique
      let im := quote col.isImmutable
      let refT : Term ← match col.refs? with
        | some (rt, rc) =>
            let rtId ← mkSqlIdentTerm rt rt.getId.eraseMacroScopes.toString
            let rcId ← mkSqlIdentTerm rc rc.getId.eraseMacroScopes.toString
            `(some ($rtId, $rcId))
        | none => `(none)
      let mut chkParts : Array String := #[]
      if col.isNat && !col.isNullable then
        chkParts := chkParts.push ("\"" ++ col.colName ++ "\" >= 0")
      for w in col.whereExprs do
        if let some s := renderCheckSql? colNames w then
          chkParts := chkParts.push s
      let chkT : Term ←
        if chkParts.isEmpty then `(none)
        else `(some $(Syntax.mkStrLit (String.intercalate " AND " chkParts.toList)))
      `({ name := $cSqlId, colType := $cTyT, nullable := $nn, isPrimaryKey := $pk,
          isUnique := $uq, isImmutable := $im, references? := $refT, checkSql? := $chkT
          : Qed.Server.Db.ColumnSchema })
    let idxTerms ← t.indexes.mapM fun idxs => do
      let ids ← idxs.mapM fun ic => mkSqlIdentTerm ic ic.getId.eraseMacroScopes.toString
      `([$[$ids:term],*])
    let rlsReadParts := t.readPols.filterMap (renderRlsSql? colNames)
    let rlsWriteParts := t.updatePols.filterMap (renderRlsSql? colNames)
    let rlsReadT ← if rlsReadParts.isEmpty then `(none) else `(some $(Syntax.mkStrLit (String.intercalate " AND " rlsReadParts.toList)))
    let rlsWriteT ← if rlsWriteParts.isEmpty then `(none) else `(some $(Syntax.mkStrLit (String.intercalate " AND " rlsWriteParts.toList)))

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

    let _ := (readPolId, insertPolId, updatePolId, deletePolId)
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
      schemaConst       := fullRowTypeName ++ `schema
      columns           := t.cols.map fun c => {
        name := c.colName, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable,
        isUnique := c.isUnique, isNullable := c.isNullable, isNat := c.isNat, isBytes := c.isBytes,
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
  let dbShortLit := Syntax.mkStrLit dbShort
  let devEpTerm ← match devEp? with
    | some dt => `(some $dt)
    | none    => `(none)
  let configId := mkIdentFrom dbIdent (dbName ++ `config)
  let ddlId := mkIdentFrom dbIdent (dbName ++ `ddl)
  let rlsDdlId := mkIdentFrom dbIdent (dbName ++ `rlsDdl)
  let secretsId := mkIdentFrom dbIdent (dbName ++ `secrets)
  let ensureId := mkIdentFrom dbIdent (dbName ++ `ensureSchema)
  let secLits := secrets.map Syntax.mkStrLit
  elabCommand (← `(command|
    def $secretsId : Array String := #[$[$secLits:term],*]))
  elabCommand (← `(command|
    def $configId : Qed.Server.Db.DbConfig := {
      name         := $dbShortLit
      endpoint     := $primaryEp
      devFallback? := $devEpTerm
      tables       := [$[$tableSchemaTerms:term],*]
    }))
  elabCommand (← `(command|
    def $ddlId (dialect : Qed.Server.Db.SqlDialect := .postgres) : String :=
      Qed.Server.Db.renderDatabaseDdl dialect ($configId).tables))
  elabCommand (← `(command|
    def $rlsDdlId : String :=
      Qed.Server.Db.renderDatabaseRlsDdl ($configId).tables))
  let mId := mkIdent `m
  elabCommand (← `(command|
    def $ensureId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] :
        $mId (Except Qed.Server.ApiError Unit) :=
      Qed.Server.MonadServer.dbExecDdl $configId))
  let safeEnsureId := mkIdentFrom dbIdent (dbName ++ `instSafeIOEnsureSchema)
  elabCommand (← `(command|
    instance $safeEnsureId:ident {_σ : Type} : Qed.Server.SafeIO (@$ensureId (Qed.Server.ThreadProg _σ) _ _) where
      noAtomic := .io (.dbExecDdl $configId) _ .pure))

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
