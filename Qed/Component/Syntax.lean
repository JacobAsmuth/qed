import Qed.Collection
import Qed.Style.Syntax
import Qed.Jsx
import Qed.Lang
import Lean

namespace Qed

/-! ## Persistent Component Registry (`componentRegistry`) -/

inductive CompMountKind | pureView | stateful deriving Inhabited, BEq
structure CompEventSig where mk :: (name : Lean.Name) (arity : Nat) deriving Inhabited

structure ComponentInfo where mk ::
  (fullName : Lean.Name) (kind : CompMountKind) (hasProps : Bool)
  (propNames slotNames bindNames : Array Lean.Name) (hasChildren : Bool) (events : Array CompEventSig)
  (hasOut hasEffects hasStart : Bool := false) (mountable : Bool := true) (hasLocalDef : Bool := false)
  (hasQueries hasSubscriptions hasSession : Bool := false)
  (rootTag? : Option String) (usedRpcs usedChannels : Array (String × String) := #[])
deriving Inhabited

initialize componentRegistry : Lean.SimplePersistentEnvExtension ComponentInfo (Lean.NameMap ComponentInfo) ← Qed.Diag.mkNameMapExt (·.fullName)
initialize failedComponentRegistry : Lean.SimplePersistentEnvExtension Lean.Name (Lean.NameMap Lean.Name) ← Qed.Diag.mkNameMapExt id

open Lean in
def lookupComponent? (cName : Name) : CoreM (Option ComponentInfo) := do
  return Qed.Diag.lookupNameMapExt? componentRegistry (← getEnv) (← getCurrNamespace) (← getOpenDecls) cName (some `view)

open Lean in
def isFailedComponent (cName : Name) : CoreM Bool := do
  return (Qed.Diag.lookupNameMapExt? failedComponentRegistry (← getEnv) (← getCurrNamespace) (← getOpenDecls) cName).isSome

/-! ## Component Surface Syntax (Sharing `Qed.Lang` Expressions, Statements & Types) -/

section CompParsers
open Lean Parser Qed.Lang

private abbrev pExpr (p : Nat := 0) : Parser := categoryParser `qedExpr p
private abbrev pType : Parser := withPosition (categoryParser `qedType 0)
private abbrev pPat  : Parser := categoryParser `qedPat 0
@[noinline] private def pNode (k : Name) (p : Parser) : Parser := node k (withPosition p)
@[noinline] private def kwNode (k kw : Name) (p : Parser) : Parser := node k (withPosition (atomic (identEq kw) >> p))
private def compParam     : Parser := node `Qed.componentParam (ident >> ":" >> pType)
private def compParamsOpt : Parser := optional (checkLineEq >> "(" >> sepBy compParam "," >> ")")
def compIfLet             : Parser := node `Qed.compIfLet (atomic (symbol "let" >> pPat >> "=") >> pExpr >> optional ("," >> sepBy1 pExpr ","))
private def compIfCond    : Parser := node `Qed.compIfCond (atomic (symbol "if") >> (compIfLet <|> sepBy1 pExpr ","))
private def compInvName   : Parser := node `Qed.compInvName (ident >> ":")
def compForEachInvClause : Parser := pNode `Qed.compForEachInvClause (
  atomic ("invariant " >> compInvName >> pExpr >> kw "for_each" >> ident) >>
  optional (kw "holds_in" >> identEq `view) >> optional (kw "using" >> ident) >> optional (":=" >> termParser))
def compInvariantClause : Parser := pNode `Qed.compInvariantClause (
  "invariant " >> compInvName >> sepBy1 pExpr "," >>
  optional (kw "holds_in" >> identEq `view >> optional (kw "assuming" >> pExpr)) >>
  optional (kw "using" >> "[" >> sepBy termParser "," >> "]") >>
  optional ((checkColGt <|> checkLineEq) >> pNode `Qed.compInvProveClause (
    atomic (identEq `prove >> ":") >> checkColGt "expected indented `case <action>:` proofs" >>
    many1Indent (pNode `Qed.compInvProveCase (atomic (kw "case") >> sepBy1 ident "," >> ":" >> checkColGt "expected indented proof tactics" >> Parser.Tactic.tacticSeq)))) >>
  optional (":=" >> termParser))
private def compExRecord : Parser := node `Qed.compExRecord ("{" >> sepBy (node `Qed.compExAssign (ident >> "=" >> pExpr)) "," >> "}")
def compExampleClause : Parser := pNode `Qed.compExampleClause (
  atomic (symbol "example" >> ident) >>
  optional (checkNoWsBefore "" >> "(" >> sepBy1 compParam "," >> ")") >>
  optional (node `Qed.compExWithProps (atomic (symbol "with" >> identEq `props) >> (compExRecord <|> ("=" >> pExpr)))) >>
  optional (node `Qed.compExFrom (atomic (symbol "from") >> (compExRecord <|> pExpr))) >>
  optional (symbol "where" >> sepBy1 pExpr ",") >>
  ":" >> sepBy1 (
    node `Qed.compExOnReply (atomic (identEq `on >> ident >> "=>") >> (
      node `Qed.compExReplyOk (atomic (identEq `ok) >> checkNoWsBefore "" >> "(" >> pExpr >> ")") <|>
      node `Qed.compExReplyErr (atomic (identEq `error) >> checkNoWsBefore "" >> "(" >> pExpr >> ")") <|>
      node `Qed.compExReplyDomain (atomic (identEq `err) >> checkNoWsBefore "" >> "(" >> "." >> checkNoWsBefore "" >> ident >> optional ("," >> pExpr) >> ")"))) <|>
    pExpr 55) "," >> "->" >> pExpr >>
  optional (node `Qed.compExEmits (atomic (identEq `emits) >> pExpr)) >>
  optional (":=" >> kw "by" >> Parser.Tactic.tacticSeq))

private def compHeadDirective : Parser :=
  kwNode `Qed.compHeadTitle `title pExpr <|> kwNode `Qed.compHeadDescription `description pExpr <|>
  kwNode `Qed.compHeadCanonical `canonical pExpr <|> kwNode `Qed.compHeadStatus `status pExpr <|>
  pNode `Qed.compHeadMeta (atomic (symbol "meta") >> pExpr >> "," >> pExpr) <|>
  kwNode `Qed.compHeadRedirect `redirect (pExpr >> optional ("," >> identEq `status >> "=" >> pExpr))

def compInvAny : Parser := compForEachInvClause <|> compInvariantClause <|> compExampleClause
def compClause : Parser :=
  kwNode `Qed.compSessionClause `session (ident >> optional (":" >> pType)) <|>
  pNode `Qed.compFieldClause (
    (atomic (identEq `state) <|> atomic (identEq `ephemeral) <|> atomic (identEq `prop) <|> atomic (identEq `bind) <|> atomic (identEq `collection)) >>
    ident >> optional (":" >> pType) >> optional ("=" >> pExpr)) <|>
  kwNode `Qed.compKeyClause `key ident <|>
  kwNode `Qed.compEventClause `event (ident >> compParamsOpt) <|>
  kwNode `Qed.compStartClause `start ((checkLineEq <|> checkColGt) >> pExpr) <|>
  kwNode `Qed.compRouteClause `route (optional ident >> ":" >> pType >> "=" >> pExpr >> optional (":" >> many1 (checkColGt >> qedStmtCase))) <|>
  pNode `Qed.compPortOutClause (atomic (identEq `port >> ident >> ":") >> pType) <|>
  pNode `Qed.compPortInClause (atomic (identEq `port >> ident >> "(") >> ident >> ":" >> pType >> ")" >> ":" >> qedSuite) <|>
  pNode `Qed.compRpcQueryClause (atomic (identEq `query >> ident >> optional (":" >> pType) >> "=") >> ident >> "(" >> sepBy pExpr "," >> ")" >> optional compIfCond) <|>
  pNode `Qed.compSubscribeClause (
    atomic (identEq `subscribe >> ident >> "=") >> ident >> "(" >> sepBy pExpr "," >> ")" >> optional compIfCond >>
    optional (":" >> checkColGt "expected indented `subscribe` handlers" >> many1Indent (
      pNode `Qed.compSubReconnect (atomic (kw "reconnect") >> pExpr) <|>
      kwNode `Qed.compSubOnJoin `on_join (optional (checkLineEq >> "(" >> qedBinder >> ")") >> ":" >> qedSuite) <|>
      kwNode `Qed.compSubOnMsg `on_message ("(" >> qedBinder >> ")" >> ":" >> qedSuite) <|>
      kwNode `Qed.compSubOnStatus `on_status ("(" >> qedBinder >> ")" >> ":" >> qedSuite)))) <|>
  pNode `Qed.compStyleClause (
    "style " >> ident >> optional Qed.StyleDsl.styleExtendsClause >> optional Qed.StyleDsl.styleStrictClause >>
    optional Qed.StyleDsl.styleContrastClause >> ":" >> many1 (checkColGt >> categoryParser `cssBlockItem 0)) <|>
  kwNode `Qed.compStylesheetClause `stylesheet strLit <|>
  pNode `Qed.compThemeClause ("theme " >> ident) <|>
  pNode `Qed.compHeadClause (
    atomic (identEq `head >> ":") >> checkColGt "expected indented `head` directives" >>
    many1Indent (pNode `Qed.compHeadCase (atomic (kw "case") >> qedCasePats >> ":" >> checkColGt "expected indented `head` directives" >> many1Indent compHeadDirective) <|> compHeadDirective)) <|>
  kwNode `Qed.compFnClause `fn (ident >> compParamsOpt >> optional (" -> " >> pType) >> ":" >> qedSuite) <|>
  kwNode `Qed.compActionClause `action (ident >> compParamsOpt >> ":" >> qedSuite) <|>
  compInvAny

@[command_parser] def componentCmd : Parser := opaqueP (node `Qed.componentCmd (
  optional Command.docComment >>
  withPosition ("component " >> ident >> ":" >> many (checkColGt >> compClause) >>
    checkColGt >> identEq `view >> ":" >> (checkLineEq <|> checkColGt) >> pExpr >> many (checkColGt >> compInvAny))))

end CompParsers

/-! ## Shared Syntax & JSX Helpers -/

section CompElab
open Lean Elab Command Qed.Lang

abbrev CmdStx      := TSyntax `command
abbrev MatchAltStx := TSyntax ``Lean.Parser.Term.matchAltExpr
abbrev BinderStx   := TSyntax `Lean.Parser.Term.bracketedBinder

structure OutArm where mk :: (ctor : Name) (arity : Nat) (handler : Term)

def bindSetName (f : Name) : Name := Name.mkSimple s!"set_{f}"
def setStxArg (n : Syntax) (i : Nat) (v : Syntax) : Syntax := Syntax.node n.getHeadInfo n.getKind (n.getArgs.set! i v)
def isPlaceholder (stx : Syntax) : Bool := let u := unwrapParens1 stx; u.getKind == ``qedPlaceholder || (u.reprint.getD "").trimmed == "_"
def atomStr : Syntax → String := Qed.Jsx.tokenVal
def mentionsIdent (stx : Syntax) (n : Name) : Bool := stxAny (fun | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes | _ => false) stx
def hasFreeIdent (target : Name) (stx : Syntax) : Bool := Qed.Lang.stxMentionsVar target.toString stx
def isEventEmitExpr (eventNames : Array Name) (exprStx : Syntax) : Bool :=
  match matchIdentMethodCall? exprStx with | some (id, "emit", _) => eventNames.contains id.getId.eraseMacroScopes | _ => false
def isAwaitStmt (s : Syntax) : Bool :=
  let k := s.getKind
  (k == ``qedStmtLet && (unwrapParens1 (s.getArg 4)).getKind == ``qedAwait) || (k == ``qedStmtAssign && (unwrapParens1 (s.getArg 2)).getKind == ``qedAwait)
def isCollMutExpr (e : Syntax) : Bool := (matchPushCall? e).isSome || (matchRemoveCall? e).isSome
def unpackBindProp (nm : String) (v : Term) : PureQuotM (Option (String × Term × Term)) := do
  if nm.startsWith "bind:" then return some ((nm.drop 5).toString, ← `(($v).1), ← `(($v).2)) else return none
def isPlainCallTo (names : Array Name) (exprStx : Syntax) : Bool :=
  let u := unwrapParens1 exprStx
  u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && names.contains (((u.getArg 0).getArg 0).getId.eraseMacroScopes)
def matchInvalidateCall? (exprStx : Syntax) : Option (Array Syntax) :=
  let u := unwrapParens1 exprStx
  if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `invalidate then
    some (u.getArg 2).getSepArgs
  else none
def hasEffectStmt (eventNames : Array Name) (stx : Syntax) (pureMutFns : Array Name := #[]) : Bool :=
  stxAny (fun s => (s.getKind == ``qedStmtExpr && !isCollMutExpr (s.getArg 0) && !isEventEmitExpr eventNames (s.getArg 0) && !isPlainCallTo pureMutFns (s.getArg 0)) || isAwaitStmt s) stx
def hasReturnStmt (stx : Syntax) : Bool := stxAny (·.getKind == ``qedStmtReturn) stx
def lowerTypeStx (stx : Syntax) : CommandElabM Term := liftMacroM (return (← lowerQedType stx false).1)
def lowerOptType (optNode : Syntax) : CommandElabM (Option Term) := if optNode.getNumArgs == 2 then some <$> lowerTypeStx (optNode.getArg 1) else pure none
def parseParamList (optNode : Syntax) : CommandElabM (Array (Ident × Term)) :=
  if optNode.getNumArgs == 3 then Lang.mapCmd (optNode.getArg 1).getSepArgs fun p => return (⟨p.getArg 0⟩, ← lowerTypeStx (p.getArg 2)) else pure #[]
def getErrorCount : CommandElabM Nat := return (← get).messages.toList.filter (·.severity == .error) |>.length

def matchNamedAttr? (a : Syntax) : Option (Syntax × String × Syntax) :=
  if a.getKind == ``Qed.Jsx.attrNamed then some (a.getArg 0, atomStr (a.getArg 0), a.getArg 1) else none
def attrNamed (nm : String) (a : Syntax) : Bool := (matchNamedAttr? a).any (·.2.1 == nm)
def matchAttrValExpr? (a : Syntax) : Option (Syntax × String × Syntax) := do
  let (ref, nm, valNode) ← matchNamedAttr? a; guard (valNode.getNumArgs == 2 && (valNode.getArg 1).getKind == ``Qed.Jsx.attrValExpr); return (ref, nm, valNode)

def splitCompProps (propNodes : Array Syntax) (specials : List String) :
    Array (Syntax × String × Term) × Std.HashMap String (Syntax × Term) := Id.run do
  let mut rest : Array (Syntax × String × Term) := #[]; let mut spec : Std.HashMap String (Syntax × Term) := {}
  for p in propNodes do
    let ref := p.getArg 0; let nm := (⟨ref⟩ : TSyntax `str).getString; let v : Term := ⟨p.getArg 2⟩
    if specials.contains nm then spec := spec.insert nm (ref, v) else rest := rest.push (ref, nm, v)
  return (rest, spec)

def qedSpecDispatchKind : Name := `Qed.specDispatchMarker
def mkSpecDispatchMarker (info : SourceInfo) (idx : Nat) : Syntax := Syntax.node info qedSpecDispatchKind #[Syntax.mkNumLit (toString idx)]
def matchSpecDispatchMarker? (st : Syntax) : Option Nat := if st.getKind == qedSpecDispatchKind then some (⟨st.getArg 0⟩ : TSyntax `num).getNat else none

def staticRootTag? (body : Syntax) : Option String :=
  if body.getKind == ``Qed.Jsx.qedExprJsx || body.getKind == ``Qed.Jsx.jsxTerm then
    let el := body.getArg 0
    if el.getKind == ``Qed.Jsx.selfClosing || el.getKind == ``Qed.Jsx.withChildren then
      let tag := atomStr (el.getArg 1); if !tag.isEmpty && !tag.front.isUpper then some tag else none
    else none
  else none

def mkJsxAttrValNode (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrValExpr #[Syntax.atom .none "{", Qed.Lang.mkRawExpr val, Syntax.atom .none "}"]
def mkJsxAttrExpr (name : String) (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrNamed #[Syntax.node .none `Qed.Jsx.jsxName #[Syntax.atom .none name], Syntax.node .none nullKind #[Syntax.atom .none "=", mkJsxAttrValNode val]]
def rebuildJsxEl (stx : Syntax) (attrs : Array Syntax) (kids? : Option Syntax) : Syntax :=
  let info := stx.getHeadInfo; let aNode := Syntax.node info nullKind attrs
  match kids? with
  | none    => Syntax.node info stx.getKind #[stx.getArg 0, stx.getArg 1, aNode, stx.getArg 3]
  | some kn => Syntax.node info stx.getKind #[stx.getArg 0, stx.getArg 1, aNode, stx.getArg 3, kn, stx.getArg 5, stx.getArg 6]

inductive ClassifiedCompProp where
  | bindProp (name : Name) (valTerm setTerm : Term)
  | eventProp (arm : OutArm)
  | dataProp (name : Name) (valTerm : Term)

def classifyCompPropPure (evSigs : Array CompEventSig) (nm : String) (v : Term) : PureQuotM ClassifiedCompProp := do
  if let some (bStr, v1, v2) ← unpackBindProp nm v then return .bindProp (Name.mkSimple bStr) v1 v2
  else if let some sig := evSigs.find? (·.name.toString == nm) then return .eventProp (.mk sig.name sig.arity v)
  else return .dataProp (Name.mkSimple nm) v

@[noinline] def mkOutMatchTermPure (baseName : Name) (totalCtors : Nat) (arms : Array OutArm) (outVar : Ident) : PureQuotM Term := do
  let mut alts ← Lang.mapPQ arms fun arm => do
    let patTerms : Array Term := (Array.range arm.arity).map fun i => ⟨(mkIdent (Name.mkSimple s!"_a{i}")).raw⟩
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (baseName ++ `Out ++ arm.ctor)) $patTerms* => some ($(← Qed.Lang.mkAppTermsPure arm.handler patTerms)))
  if arms.size < totalCtors then alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
  `(match $outVar:ident with $[$alts:matchAlt]*)

end CompElab
end Qed
