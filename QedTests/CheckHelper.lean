import Qed

abbrev strHas := Qed.Str.containsBytes
abbrev strHasAll := Qed.Str.containsAllBytes
abbrev strHasNone := Qed.Str.containsNoneBytes

open Lean in
elab "rollback_env " cmd:command : command => withoutModifyingEnv (Elab.Command.elabCommand cmd)

@[noinline] private def wrapExpectErr (msg : Lean.TSyntax `str) (cmd : Lean.TSyntax `command) : Lean.MacroM (Lean.TSyntax `command) :=
  let doc : Lean.TSyntax `Lean.Parser.Command.docComment :=
    .mk (.node .none ``Lean.Parser.Command.docComment #[Lean.mkAtom "/--", .node .none ``Lean.Parser.Command.commentBody #[Lean.mkAtom msg.getString, Lean.mkAtom "-/"]])
  `($doc:docComment #guard_msgs (error, drop warning, substring := true) in rollback_env $cmd)

macro "expect_err " msg:str " in " cmd:command : command => wrapExpectErr msg cmd

macro "check_decls " "[" ids:ident,* "]" : command => do
  `(example : True := by $[$(← ids.getElems.mapM fun id => `(tactic| have _ := @$id)):tactic];* ; trivial)

@[noinline] private def spliceNode (base : Lean.TSyntax `command) (pred : Lean.Syntax → Bool) (items : Array Lean.Syntax) : Lean.MacroM (Lean.TSyntax `command) :=
  return ⟨← base.raw.replaceM fun stx =>
    if stx.isOfKind `null && stx.getNumArgs == 1 && pred (stx.getArg 0) then pure (some (Lean.Syntax.node .none `null items)) else pure none⟩

@[noinline] private def spliceStmts (base : Lean.TSyntax `command) (s0 : Lean.TSyntax `qedStmt) (ss : Array (Lean.TSyntax `qedStmt)) : Lean.MacroM (Lean.TSyntax `command) :=
  spliceNode base (· == s0.raw) (ss.map (·.raw))

macro "bad_a11y " rule:ident " : " v:qedExpr : command => do
  let msg := Lean.Syntax.mkStrLit s!"Accessibility invariant `BadA11y.ok` failed in `BadA11y.view`:\n  • `{rule.getId}` does not hold in every state"
  wrapExpectErr msg (← `(command|
    component $(Lean.mkIdent `BadA11y):ident:
      state $(Lean.mkIdent `x):ident : $(Lean.mkIdent `Nat):ident = 0
      view: $v
      invariant $(Lean.mkIdent `ok):ident: $(← `(qedExpr| $rule:ident))))

syntax withPosition("bad_style " str ident (" extends " ident)? (" [" ident "]")? " : " (colGt cssBlockItem)+) : command
macro_rules
  | `(bad_style $msg:str $nm:ident $[extends $p:ident]? $[[$k:ident]]? : $[$its:cssBlockItem]*
    ) => do
    wrapExpectErr msg (← match p, k.map (·.getId) with
      | some base, _ => `(command|
        style $nm:ident extends $base:ident:
          $[$its:cssBlockItem]*
        )
      | none, some `strict => `(command|
        style $nm:ident strict_tokens:
          $[$its:cssBlockItem]*
        )
      | none, some `contrast => `(command|
        style $nm:ident contrast >= 4.5:
          $[$its:cssBlockItem]*
        )
      | _, _ => `(command|
        style $nm:ident:
          $[$its:cssBlockItem]*
        ))

syntax "bad_deploy " str ident ident (" : " sepBy1(deployClause, " | "))? : command
macro_rules | `(bad_deploy $msg:str $nm:ident $appNm:ident $[: $[$cs:deployClause]|*]?) => do
  wrapExpectErr msg (← `(command|
    deploy $nm:ident:
      app $appNm:ident
      $[$(cs.getD #[]):deployClause]*))

macro "bad_fs " msg:str nm:ident srv:ident cli:ident : command => do
  wrapExpectErr msg (← `(command|
    fullstack $nm:ident:
      server $srv:ident
      client $cli:ident
      title "Bad"))

macro "bad_ext " msg:str nm:ident " : " cs:sepBy1(extClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    external $nm:ident:
      $[$cs:extClause]*))
macro "bad_svc " msg:str nm:ident " : " cs:sepBy1(srvClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    service $nm:ident:
      $[$cs:srvClause]*))
syntax "bad_srv " str ("[" ident "] ")? ident " : " sepBy1(srvClause, " | ") : command
macro_rules | `(bad_srv $msg:str $[[$k:ident]]? $nm:ident : $[$cs:srvClause]|*) => do
  wrapExpectErr msg (← if k.any (·.getId == `stateless) then `(command|
    server stateless $nm:ident:
      $[$cs:srvClause]*) else `(command|
    server $nm:ident:
      $[$cs:srvClause]*))

macro "bad_db_tbl " msg:str nm:ident tbl:ident " : " cs:sepBy1(dbTableClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    database $nm:ident:
      sqlite ".qed/bad.db"
      table $tbl:ident:
        $[$cs:dbTableClause]*))

macro "bad_db_def " msg:str nm:ident " : " cs:sepBy1(dbClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    database $nm:ident:
      sqlite ".qed/bad.db"
      $[$cs:dbClause]*))

macro "bad_db_raw " msg:str nm:ident " : " cs:sepBy1(dbClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    database $nm:ident:
      $[$cs:dbClause]*))

syntax "bad_fn " str ident "(" sepBy(ident " : " qedType, ",") ")" " -> " qedType (" | " sepBy1(qedFnContract, " | "))? " : " sepBy1(qedStmt, " | ") : command
macro_rules
  | `(bad_fn $msg:str $nm:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType $[| $[$cs:qedFnContract]|*]? : $[$ss:qedStmt]|*) => do
      let (s0, req0) := (ss[0]!, ← `(qedFnContract| requires true))
      let base ← `(command|
        fn $nm:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType:
          $req0:qedFnContract
          $s0:qedStmt)
      let b1 ← spliceNode base (· == req0.raw) ((cs.getD #[]).map (·.raw))
      wrapExpectErr msg (← spliceStmts b1 s0 ss)

macro "bad_db " msg:str dbNm:ident " : " cs:sepBy1(srvClause, " | ") : command => do
  wrapExpectErr msg (← `(command|
    server $(Lean.mkIdent `BadDbSrv):ident:
      use $(Lean.mkIdent `db):ident : $dbNm:ident
      $[$cs:srvClause]*))

macro "bad_db1 " msg:str dbNm:ident fn:ident "(" p:ident ":" pt:qedType ")" " -> " ret:qedType " : " body:qedStmt : command => do
  wrapExpectErr msg (← `(command|
    server $(Lean.mkIdent `BadDbSrv):ident:
      use $(Lean.mkIdent `db):ident : $dbNm:ident
      rpc $fn:ident($p:ident : $pt:qedType) -> $ret:qedType:
        requires ($(Lean.mkIdent `ctx):ident).userId != $(Lean.mkIdent `none):ident
        $body:qedStmt))

syntax "bad_db_auth " str ident (" [" ident "]")? ident "(" sepBy(ident " : " qedType, ",") ")" " -> " qedType (" | " sepBy1(qedExpr, ","))? " : " sepBy1(qedStmt, " | ") : command
macro_rules
  | `(bad_db_auth $msg:str $dbNm:ident $[[$ro:ident]]? $fn:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType $[| $[$reqs:qedExpr],*]? : $[$ss:qedStmt]|*) => do
      let (s0, allReqs) := (ss[0]!, #[← `(qedExpr| $(Lean.mkIdent `auth):ident)] ++ reqs.getD #[])
      let base ← if ro.any (·.getId == `ro) then `(command|
        server $(Lean.mkIdent `BadDbSrv):ident:
          use $(Lean.mkIdent `db):ident : $dbNm:ident
          read_only rpc $fn:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType:
            requires $[$allReqs:qedExpr],*
            $s0:qedStmt)
      else `(command|
        server $(Lean.mkIdent `BadDbSrv):ident:
          use $(Lean.mkIdent `db):ident : $dbNm:ident
          rpc $fn:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType:
            requires $[$allReqs:qedExpr],*
            $s0:qedStmt)
      wrapExpectErr msg (← spliceStmts base s0 ss)

macro "bad_comp_view " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " viewE:qedExpr : command => do
  wrapExpectErr msg (← `(command|
    component $nm:ident:
      state $st:ident : $ty:qedType = $v:qedExpr
      view: $viewE:qedExpr))

macro "bad_comp_act " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " act:ident " : " ss:sepBy1(qedStmt, ";") : command => do
  wrapExpectErr msg (← `(command|
    component $nm:ident:
      state $st:ident : $ty:qedType = $v:qedExpr
      action $act:ident: $[$ss:qedStmt];*
      view: <span>{$st:ident}</span>))

syntax "bad_comp_inv " str ident ident " : " qedType " = " qedExpr " | " ident " : " qedExpr " | " ident " : " sepBy1(qedStmt, " | ") : command
macro_rules
  | `(bad_comp_inv $msg:str $nm:ident $st:ident : $ty:qedType = $v:qedExpr | $inv:ident : $invE:qedExpr | $act:ident : $[$ss:qedStmt]|*) => do
      let s0 := ss[0]!
      let base ← `(command|
        component $nm:ident:
          state $st:ident : $ty:qedType = $v:qedExpr
          invariant $inv:ident: $invE:qedExpr
          action $act:ident:
            $s0:qedStmt
          view: <span>{$st:ident}</span>)
      wrapExpectErr msg (← spliceStmts base s0 ss)

syntax "bad_comp_query " str ident ident " = " ident "(" sepBy(qedExpr, ",") ")" (" if " qedExpr)? : command
macro_rules
  | `(bad_comp_query $msg:str $nm:ident $qn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?) => do
      wrapExpectErr msg (← `(command|
        component $nm:ident:
          session $(Lean.mkIdent `user):ident
          query $qn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?
          view: <span>ok</span>))

syntax "bad_comp_sub " str ident ident " = " ident "(" sepBy(qedExpr, ",") ")" (" if " qedExpr)? (" | " ident " : " qedStmt)? : command
macro_rules
  | `(bad_comp_sub $msg:str $nm:ident $sn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]? $[| $a:ident : $s:qedStmt]?) => do
      let act := a.getD (Lean.mkIdent `_unused)
      let st ← match s with | some st => pure st | none => `(qedStmt| pass)
      let base ← `(command|
        component $nm:ident:
          session $(Lean.mkIdent `user):ident
          subscribe $sn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?:
            on_message(_): pass
          action $act:ident: $st:qedStmt
          view: <span>ok</span>)
      wrapExpectErr msg (← if a.isSome then pure base else spliceNode base (·.isOfKind `Qed.compActionClause) #[])

macro "bad_comp_sess " msg:str nm:ident " : " s:qedStmt : command => do
  wrapExpectErr msg (← `(command|
    component $nm:ident:
      session $(Lean.mkIdent `user):ident
      action $(Lean.mkIdent `go):ident: $s:qedStmt
      view: <span>ok</span>))

syntax "bad_spec_act " str ident (" : " sepBy1(qedStmt, " | ")) : command
macro_rules
  | `(bad_spec_act $msg:str $nm:ident : $[$ss:qedStmt]|*) => do
      let (rem, s0) := (Lean.mkIdent `remaining, ss[0]!)
      let base ← `(command|
        component $nm:ident:
          session $(Lean.mkIdent `user):ident
          state $rem:ident : $(Lean.mkIdent `Nat):ident = 10
          action $(Lean.mkIdent `buy):ident:
            $s0:qedStmt
          view: <span>{$rem:ident}</span>)
      wrapExpectErr msg (← spliceStmts base s0 ss)

section RawBadCmds
open Lean Parser Qed.Lang
@[command_parser] def badSchemaCmd : Parser := leading_parser opaqueP ("bad_schema " >> strLit >> ident >> " : " >> sepBy1 Qed.schemaItemP " | ")
@[command_parser] def badRecCmd    : Parser := leading_parser opaqueP ("bad_rec "    >> strLit >> ident >> " : " >> sepBy1 Qed.recordItemP " | ")
@[command_parser] def badEnumCmd   : Parser := leading_parser opaqueP ("bad_enum "   >> strLit >> ident >> " : " >> sepBy1 Qed.enumVariantP " | ")
@[command_parser] def badCompCmd   : Parser := leading_parser opaqueP ("bad_comp "   >> strLit >> ident >> " : " >> sepBy1 Qed.compClause " | " >> " | view: " >> categoryParser `qedExpr 0 >> optional (" | " >> sepBy1 Qed.compInvAny " | "))

@[noinline] private def expandSimpleBad (kind : Name) (mkBase : TSyntax `ident → MacroM (TSyntax `command)) : Macro := fun stx => do
  wrapExpectErr ⟨stx.getArg 1⟩ (← spliceNode (← mkBase ⟨stx.getArg 2⟩) (·.isOfKind kind) (stx.getArg 4).getSepArgs)

@[macro badSchemaCmd] def expandBadSchema : Macro := expandSimpleBad `Qed.schemaField fun nm => `(command|
  schema $nm:ident:
    _d : Nat)
@[macro badRecCmd]    def expandBadRec    : Macro := expandSimpleBad `Qed.recordField fun nm => `(command|
  record $nm:ident:
    _d : Nat)
@[macro badEnumCmd]   def expandBadEnum   : Macro := expandSimpleBad `Qed.enumVariant fun nm => `(command|
  enum $nm:ident:
    _d)

@[macro badCompCmd] def expandBadComp : Macro := fun stx => do
  let (cls, v, invOpt) := ((stx.getArg 4).getSepArgs, ⟨stx.getArg 6⟩, stx.getArg 7)
  let invs := if invOpt.getNumArgs == 2 then (invOpt.getArg 1).getSepArgs else #[]
  let base ← `(command|
    component $(⟨stx.getArg 2⟩):ident:
      state _d : Nat = 0
      view: $v:qedExpr
      invariant _i: true)
  wrapExpectErr ⟨stx.getArg 1⟩ (← spliceNode (← spliceNode base (·.isOfKind `Qed.compFieldClause) cls) (·.isOfKind `Qed.compInvariantClause) invs)
end RawBadCmds
