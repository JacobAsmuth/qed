import Qed

abbrev strHas := Qed.Str.containsBytes
abbrev strHasAll := Qed.Str.containsAllBytes
abbrev strHasNone := Qed.Str.containsNoneBytes

open Lean in
elab "rollback_env " cmd:command : command => withoutModifyingEnv (Elab.Command.elabCommand cmd)

macro "expect_err " msg:str " in " cmd:command : command =>
  let doc : Lean.TSyntax `Lean.Parser.Command.docComment :=
    .mk (.node .none ``Lean.Parser.Command.docComment #[Lean.mkAtom "/--",
      .node .none ``Lean.Parser.Command.commentBody #[Lean.mkAtom msg.getString, Lean.mkAtom "-/"]])
  `($doc:docComment #guard_msgs (error, drop warning, substring := true) in rollback_env $cmd)

macro "check_decls " "[" ids:ident,* "]" : command => do
  let haves ← ids.getElems.mapM fun id => `(tactic| have _ := @$id)
  `(example : True := by $[$haves:tactic];* ; trivial)

macro "bad_a11y " rule:ident " : " v:qedExpr : command => do
  let msg := Lean.Syntax.mkStrLit s!"Accessibility invariant `BadA11y.ok` failed in `BadA11y.view`:\n  • `{rule.getId}` does not hold in every state"
  let nm := Lean.mkIdent `BadA11y; let x := Lean.mkIdent `x; let nat := Lean.mkIdent `Nat; let ok := Lean.mkIdent `ok; let r ← `(qedExpr| $rule:ident)
  `(expect_err $msg in
    component $nm:ident:
      state $x:ident : $nat:ident = 0
      view: $v
      invariant $ok:ident: $r)
macro "bad_style " msg:str nm:ident " : " it:cssBlockItem : command =>
  `(expect_err $msg in
    style $nm:ident:
      $it:cssBlockItem
  )
macro "bad_style_strict " msg:str nm:ident " : " it:cssBlockItem : command =>
  `(expect_err $msg in
    style $nm:ident strict_tokens:
      $it:cssBlockItem
  )
syntax withPosition("bad_style_contrast " str ident " : " (colGt cssBlockItem)+) : command
macro_rules
  | `(bad_style_contrast $msg:str $nm:ident :
        $[$its:cssBlockItem]*
    ) =>
    `(expect_err $msg in
      style $nm:ident contrast >= 4.5:
        $[$its:cssBlockItem]*
    )
macro "bad_deploy " msg:str nm:ident appNm:ident : command => `(expect_err $msg in
  deploy $nm:ident:
    app $appNm:ident)
macro "bad_deploy1 " msg:str nm:ident appNm:ident " : " cs:sepBy1(deployClause, " | ") : command => `(expect_err $msg in
  deploy $nm:ident:
    app $appNm:ident
    $[$cs:deployClause]*)
macro "bad_fs " msg:str nm:ident srv:ident cli:ident : command => `(expect_err $msg in
  fullstack $nm:ident:
    server $srv:ident
    client $cli:ident
    title "Bad")
macro "bad_ext " msg:str nm:ident " : " cs:sepBy1(extClause, " | ") : command =>
  `(expect_err $msg in
    external $nm:ident:
      $[$cs:extClause]*)
macro "bad_svc " msg:str nm:ident " : " cs:sepBy1(srvClause, " | ") : command =>
  `(expect_err $msg in
    service $nm:ident:
      $[$cs:srvClause]*)
macro "bad_db_tbl " msg:str nm:ident tbl:ident " : " cs:sepBy1(dbTableClause, " | ") : command =>
  `(expect_err $msg in
    database $nm:ident:
      sqlite ".qed/bad.db"
      table $tbl:ident:
        $[$cs:dbTableClause]*)
macro "bad_db_def " msg:str nm:ident " : " cs:sepBy1(dbClause, " | ") : command =>
  `(expect_err $msg in
    database $nm:ident:
      sqlite ".qed/bad.db"
      $[$cs:dbClause]*)
private def spliceStmts (base : Lean.TSyntax `command) (s0 : Lean.TSyntax `qedStmt) (ss : Array (Lean.TSyntax `qedStmt)) : Lean.MacroM (Lean.TSyntax `command) :=
  return ⟨← base.raw.replaceM fun stx =>
    if stx.isOfKind `null && stx.getNumArgs == 1 && stx.getArg 0 == s0.raw then
      pure (some (Lean.Syntax.node .none `null (ss.map (·.raw))))
    else pure none⟩

syntax "bad_fn " str ident "(" sepBy(ident " : " qedType, ",") ")" " -> " qedType (" | " qedFnContract)? " : " sepBy1(qedStmt, " | ") : command
macro_rules
  | `(bad_fn $msg:str $nm:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType $[| $c:qedFnContract]? : $[$ss:qedStmt]|*) => do
      let s0 := ss[0]!
      let base ← match c with
        | some ctr =>
          `(command|
            fn $nm:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType:
              $ctr:qedFnContract
              $s0:qedStmt)
        | none =>
          `(command|
            fn $nm:ident($[$ps:ident : $ts:qedType],*) -> $ret:qedType:
              $s0:qedStmt)
      let fnStx ← spliceStmts base s0 ss
      `(expect_err $msg in $fnStx:command)
macro "bad_db " msg:str dbNm:ident " : " fn:srvClause : command => do
  let nm := Lean.mkIdent `BadDbSrv; let d := Lean.mkIdent `db
  `(expect_err $msg in
    server $nm:ident:
      use $d:ident : $dbNm:ident
      $fn:srvClause)
macro "bad_db1 " msg:str dbNm:ident fn:ident "(" p:ident ":" pt:qedType ")" " -> " ret:qedType " : " body:qedStmt : command => do
  let nm := Lean.mkIdent `BadDbSrv; let d := Lean.mkIdent `db; let ctx := Lean.mkIdent `ctx; let noneI := Lean.mkIdent `none
  `(expect_err $msg in
    server $nm:ident:
      use $d:ident : $dbNm:ident
      rpc $fn:ident($p:ident : $pt:qedType) -> $ret:qedType:
        requires ($ctx:ident).userId != $noneI:ident
        $body:qedStmt)
macro "bad_srv1 " msg:str nm:ident " : " fn:srvClause : command => `(expect_err $msg in
  server $nm:ident:
    $fn:srvClause)
macro "bad_srv_st " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " fn:srvClause : command => `(expect_err $msg in
  server $nm:ident:
    state $st:ident : $ty:qedType = $v:qedExpr
    $fn:srvClause)
macro "bad_srv_inv " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " inv:ident " : " invE:qedExpr " | " fn:srvClause : command => `(expect_err $msg in
  server $nm:ident:
    state $st:ident : $ty:qedType = $v:qedExpr
    invariant $inv:ident: $invE:qedExpr
    $fn:srvClause)
macro "bad_comp_view " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " viewE:qedExpr : command => `(expect_err $msg in
  component $nm:ident:
    state $st:ident : $ty:qedType = $v:qedExpr
    view: $viewE:qedExpr)
macro "bad_comp_act " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " act:ident " : " ss:sepBy1(qedStmt, ";") : command => `(expect_err $msg in
  component $nm:ident:
    state $st:ident : $ty:qedType = $v:qedExpr
    action $act:ident: $[$ss:qedStmt];*
    view: <span>{$st:ident}</span>)
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
      let cStx ← spliceStmts base s0 ss
      `(expect_err $msg in $cStx:command)
syntax "bad_comp_query " str ident ident " = " ident "(" sepBy(qedExpr, ",") ")" (" if " qedExpr)? : command
macro_rules
  | `(bad_comp_query $msg:str $nm:ident $qn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?) => do
      let u := Lean.mkIdent `user
      `(expect_err $msg in
        component $nm:ident:
          session $u:ident
          query $qn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?
          view: <span>ok</span>)
syntax "bad_comp_sub " str ident ident " = " ident "(" sepBy(qedExpr, ",") ")" (" if " qedExpr)? (" | " ident " : " qedStmt)? : command
macro_rules
  | `(bad_comp_sub $msg:str $nm:ident $sn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]? $[| $a:ident : $s:qedStmt]?) => do
      let u := Lean.mkIdent `user
      match a, s with
      | some act, some stmt =>
        `(expect_err $msg in
          component $nm:ident:
            session $u:ident
            subscribe $sn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?:
              on_message(_): pass
            action $act:ident: $stmt:qedStmt
            view: <span>ok</span>)
      | _, _ =>
        `(expect_err $msg in
          component $nm:ident:
            session $u:ident
            subscribe $sn:ident = $fn:ident($[$args:qedExpr],*) $[if $c:qedExpr]?:
              on_message(_): pass
            view: <span>ok</span>)
macro "bad_comp_sess " msg:str nm:ident " : " s:qedStmt : command => do
  let u := Lean.mkIdent `user; let go := Lean.mkIdent `go
  `(expect_err $msg in
    component $nm:ident:
      session $u:ident
      action $go:ident: $s:qedStmt
      view: <span>ok</span>)
macro "bad_spec_act " msg:str nm:ident " : " s:qedStmt : command => do
  let u := Lean.mkIdent `user; let rem := Lean.mkIdent `remaining; let nat := Lean.mkIdent `Nat; let buy := Lean.mkIdent `buy
  `(expect_err $msg in
    component $nm:ident:
      session $u:ident
      state $rem:ident : $nat:ident = 10
      action $buy:ident: $s:qedStmt
      view: <span>{$rem:ident}</span>)
