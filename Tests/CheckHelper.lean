import Qed

open Lean in
elab "rollback_env " cmd:command : command => withoutModifyingEnv (Elab.Command.elabCommand cmd)

macro "expect_err " msg:str " in " cmd:command : command =>
  let doc : Lean.TSyntax `Lean.Parser.Command.docComment :=
    .mk (.node .none ``Lean.Parser.Command.docComment #[Lean.mkAtom "/--",
      .node .none ``Lean.Parser.Command.commentBody #[Lean.mkAtom msg.getString, Lean.mkAtom "-/"]])
  `($doc:docComment #guard_msgs (error, drop warning, substring := true) in rollback_env $cmd)

macro "bad_a11y " rule:ident " : " v:qedExpr : command => do
  let msg := Lean.Syntax.mkStrLit s!"Accessibility invariant `BadA11y.ok` failed in `BadA11y.view`:\n  • `{rule.getId}` does not hold in every state"
  let nm := Lean.mkIdent `BadA11y; let x := Lean.mkIdent `x; let nat := Lean.mkIdent `Nat; let ok := Lean.mkIdent `ok; let r ← `(qedExpr| $rule:ident)
  `(expect_err $msg in
    component $nm:ident:
      state $x:ident : $nat:ident = 0
      view: $v
      invariant $ok:ident: $r)
macro "bad_style " msg:str nm:ident " : " its:cssBlockItem+ : command =>
  `(expect_err $msg in
    style $nm:ident:
      $[$its:cssBlockItem]*
  )
macro "bad_style_strict " msg:str nm:ident " : " its:cssBlockItem+ : command =>
  `(expect_err $msg in
    style $nm:ident strict_tokens:
      $[$its:cssBlockItem]*
  )
macro "bad_deploy " msg:str nm:ident appNm:ident : command => `(expect_err $msg in
  deploy $nm:ident:
    app $appNm:ident)
macro "bad_deploy1 " msg:str nm:ident appNm:ident " : " c:deployClause : command => `(expect_err $msg in
  deploy $nm:ident:
    app $appNm:ident
    $c:deployClause)
macro "bad_fs " msg:str nm:ident srv:ident cli:ident : command => `(expect_err $msg in
  fullstack $nm:ident:
    server $srv:ident
    client $cli:ident
    title "Bad")
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
      def $fn:ident($p:ident : $pt:qedType) -> $ret:qedType:
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
macro "bad_comp_act " msg:str nm:ident st:ident " : " ty:qedType " = " v:qedExpr " | " act:ident " : " s:qedStmt : command => `(expect_err $msg in
  component $nm:ident:
    state $st:ident : $ty:qedType = $v:qedExpr
    action $act:ident: $s:qedStmt
    view: <span>{$st:ident}</span>)
macro "bad_comp_sess " msg:str nm:ident " : " s:qedStmt : command => do
  let u := Lean.mkIdent `user; let go := Lean.mkIdent `go
  `(expect_err $msg in
    component $nm:ident:
      session $u:ident
      action $go:ident: $s:qedStmt
      view: <span>ok</span>)
macro "bad_spec_act " msg:str nm:ident " : " s:qedStmt : command => do
  let u := Lean.mkIdent `user; let rem := Lean.mkIdent `remaining; let nat := Lean.mkIdent `Nat; let buy := Lean.mkIdent `buy; let inv := Lean.mkIdent `validRemaining
  `(expect_err $msg in
    component $nm:ident:
      session $u:ident
      state $rem:ident : $nat:ident = 10
      invariant $inv:ident: $rem:ident <= 10000
      action $buy:ident: $s:qedStmt
      view: <span>{$rem:ident}</span>)
