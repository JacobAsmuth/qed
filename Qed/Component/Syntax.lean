import Qed.Component.Core
import Qed.Style.Syntax
import Qed.Jsx
import Qed.Lang
import Lean

namespace Qed

/-! ## Persistent Component Registry (`componentRegistry`) -/

inductive CompMountKind | pureView | stateful deriving Inhabited, BEq, Repr

structure CompEventSig where
  name  : Lean.Name
  arity : Nat
deriving Inhabited, Repr

structure ComponentInfo where
  fullName    : Lean.Name
  kind        : CompMountKind
  hasProps    : Bool
  propNames   : Array Lean.Name
  slotNames   : Array Lean.Name
  bindNames   : Array Lean.Name
  hasChildren : Bool
  events      : Array CompEventSig
  hasOut      : Bool := false
  hasEffects  : Bool := false
  hasStart    : Bool := false
  mountable   : Bool := true
  hasLocalDef  : Bool := false
  rootTag?     : Option String
  usedRpcs     : Array (String × String) := #[]
  usedChannels : Array (String × String) := #[]
deriving Inhabited

initialize componentRegistry :
    Lean.SimplePersistentEnvExtension ComponentInfo (Lean.NameMap ComponentInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

open Lean in
def lookupComponent? (cName : Name) : CoreM (Option ComponentInfo) := do
  return Qed.Diag.lookupNameMapExt? componentRegistry (← getEnv) (← getCurrNamespace) (← getOpenDecls) cName (some `view)

/-! ## Component Surface Syntax (Sharing `Qed.Lang` Expressions, Statements & Types) -/

section CompParsers
open Lean Parser Qed.Lang

private def compParam : Parser :=
  node `Qed.componentParam (ident >> ":" >> categoryParser `qedType 0)

private def compParamsOpt : Parser :=
  optional (checkLineEq >> "(" >> sepBy1 compParam "," >> ")")

def compFieldClause : Parser := leading_parser
  withPosition (
    (atomic (identEq `state) <|> atomic (identEq `ephemeral) <|>
     atomic (identEq `prop) <|> atomic (identEq `bind) <|>
     atomic (identEq `collection)) >>
    ident >> optional (":" >> categoryParser `qedType 0) >> optional ("=" >> categoryParser `qedExpr 0))

def compKeyClause      : Parser := leading_parser withPosition (atomic (identEq `key) >> ident)
def compEventClause    : Parser := leading_parser
  withPosition (atomic (identEq `event) >> ident >> compParamsOpt)
def compSessionClause  : Parser := leading_parser
  withPosition (atomic (identEq `session) >> ident >> optional (":" >> categoryParser `qedType 0))
def compStartClause    : Parser := leading_parser
  withPosition (atomic (identEq `start) >> (checkLineEq <|> checkColGt) >> categoryParser `qedExpr 0)
def compRouteClause    : Parser := leading_parser
  withPosition (
    atomic (identEq `route) >> optional ident >> ":" >> categoryParser `qedType 0 >> "=" >>
    categoryParser `qedExpr 0 >>
    optional (":" >> many1 (checkColGt >> qedStmtCase)))
def compPortOutClause  : Parser := leading_parser
  withPosition (atomic (identEq `port >> ident >> ":") >> categoryParser `qedType 0)

def compIfLet : Parser := leading_parser
  atomic (symbol "let" >> categoryParser `qedPat 0 >> "=") >> categoryParser `qedExpr 0 >>
  optional ("," >> sepBy1 (categoryParser `qedExpr 0) ",")

def compIfCond : Parser := leading_parser
  atomic (symbol "if") >> (compIfLet <|> sepBy1 (categoryParser `qedExpr 0) ",")

def compPortInClause   : Parser := leading_parser
  withPosition (
    atomic (identEq `port >> ident >> "(") >> ident >> ":" >> categoryParser `qedType 0 >> ")" >>
    ":" >> qedSuite)

def compRpcQueryClause : Parser := leading_parser
  withPosition (
    atomic (identEq `query >> ident >> optional (":" >> categoryParser `qedType 0) >> "=") >>
    ident >> "(" >> sepBy (categoryParser `qedExpr 0) "," >> ")" >>
    optional compIfCond)

def compSubReconnect : Parser :=
  node `Qed.compSubReconnect (withPosition (atomic (kw "reconnect") >> categoryParser `qedExpr 0))

def compSubOnJoin : Parser :=
  node `Qed.compSubOnJoin (withPosition (atomic (identEq `on_join) >> optional (checkLineEq >> "(" >> qedBinder >> ")") >> ":" >> qedSuite))

private def compSubHandler1 (kind kw : Name) : Parser :=
  node kind (withPosition (atomic (identEq kw) >> "(" >> qedBinder >> ")" >> ":" >> qedSuite))

def compSubOnMsg : Parser := compSubHandler1 `Qed.compSubOnMsg `on_message
def compSubOnStatus : Parser := compSubHandler1 `Qed.compSubOnStatus `on_status

def compSubHandler : Parser :=
  compSubReconnect <|> compSubOnJoin <|> compSubOnMsg <|> compSubOnStatus

def compSubscribeClause : Parser := leading_parser
  withPosition (
    atomic (identEq `subscribe >> ident >> "=") >>
    ident >> "(" >> sepBy (categoryParser `qedExpr 0) "," >> ")" >>
    optional compIfCond >>
    optional (":" >> checkColGt "expected indented `subscribe` handlers" >> many1Indent compSubHandler))

def compActionClause   : Parser := leading_parser
  withPosition (
    atomic (identEq `action) >> ident >> compParamsOpt >> ":" >> qedSuite)

def compInvName : Parser := leading_parser ident >> ":"

def compForEachInvClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> compInvName >> categoryParser `qedExpr 0 >> kw "for_each" >> ident) >>
    optional (kw "holds_in" >> identEq `view) >>
    optional (kw "using" >> ident) >>
    optional (":=" >> termParser))

def compInvariantClause : Parser := leading_parser
  withPosition (
    "invariant " >> compInvName >> sepBy1 (categoryParser `qedExpr 0) "," >>
    optional (kw "holds_in" >> identEq `view >> optional (kw "assuming" >> categoryParser `qedExpr 0)) >>
    optional (kw "using" >> "[" >> sepBy termParser "," >> "]") >>
    optional (":=" >> termParser))

def compStyleClause : Parser := leading_parser
  withPosition (
    "style " >>
    ident >>
    optional Qed.StyleDsl.styleExtendsClause >>
    optional Qed.StyleDsl.styleStrictClause >>
    ":" >>
    many1 (checkColGt >> categoryParser `cssBlockItem 0))

def compStylesheetClause : Parser := leading_parser
  withPosition (atomic (identEq `stylesheet) >> strLit)

def compThemeClause : Parser := leading_parser
  withPosition ("theme " >> ident)

private def compHeadDir1 (kind kw : Name) : Parser :=
  node kind (withPosition (atomic (identEq kw) >> categoryParser `qedExpr 0))

def compHeadDirective : Parser :=
  compHeadDir1 `Qed.compHeadTitle `title <|>
  compHeadDir1 `Qed.compHeadDescription `description <|>
  compHeadDir1 `Qed.compHeadCanonical `canonical <|>
  node `Qed.compHeadMeta (withPosition (atomic (symbol "meta") >> categoryParser `qedExpr 0 >> "," >> categoryParser `qedExpr 0)) <|>
  compHeadDir1 `Qed.compHeadStatus `status <|>
  node `Qed.compHeadRedirect (withPosition (atomic (identEq `redirect) >> categoryParser `qedExpr 0 >>
    optional ("," >> identEq `status >> "=" >> categoryParser `qedExpr 0)))

def compHeadCase : Parser :=
  node `Qed.compHeadCase (withPosition (
    atomic (kw "case") >> sepBy1 (categoryParser `qedPat 0) "," >> ":" >>
    checkColGt "expected indented `head` directives" >>
    many1Indent compHeadDirective))

def compHeadItem : Parser := compHeadCase <|> compHeadDirective

def compHeadClause : Parser := leading_parser
  withPosition (
    atomic (identEq `head >> ":") >>
    checkColGt "expected indented `head` directives" >>
    many1Indent compHeadItem)

def compExampleClause : Parser := leading_parser
  withPosition (
    atomic (symbol "example" >> ident) >>
    optional (checkNoWsBefore "" >> "(" >> sepBy1 compParam "," >> ")") >>
    optional (symbol "where" >> sepBy1 (categoryParser `qedExpr 0) ",") >>
    ":" >>
    sepBy1 (categoryParser `qedExpr 55) "," >>
    "->" >>
    categoryParser `qedExpr 0 >>
    optional (":=" >> kw "by" >> Parser.Tactic.tacticSeq))

def compInvAny : Parser :=
  compForEachInvClause <|> compInvariantClause <|> compExampleClause

def compClause : Parser :=
  compSessionClause <|> compFieldClause <|> compKeyClause <|>
  compEventClause <|> compStartClause <|> compRouteClause <|>
  compPortOutClause <|> compPortInClause <|> compRpcQueryClause <|>
  compSubscribeClause <|> compStyleClause <|> compStylesheetClause <|> compThemeClause <|>
  compHeadClause <|> compActionClause <|> compInvAny

@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "component " >> ident >> ":" >>
    many (checkColGt >> compClause) >>
    checkColGt >> identEq `view >> ":" >> (checkLineEq <|> checkColGt) >> categoryParser `qedExpr 0 >>
    many (checkColGt >> compInvAny))

end CompParsers

/-! ## Shared Syntax & JSX Helpers -/

section CompElab
open Lean Elab Command Qed.Lang

structure OutArm where
  ctor    : Name
  arity   : Nat
  handler : Term

def isPlaceholder (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedPlaceholder || (u.reprint.getD "").trimmed == "_"

def atomStr : Syntax → String := Qed.Jsx.tokenVal

def mentionsIdent (stx : Syntax) (n : Name) : Bool :=
  stxAny (fun | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes | _ => false) stx

/-- True when `target` appears as a free identifier (or root of `target.field`) in `stx`,
    ignoring field projections (`x.target`), named-arg/record keys, JSX attribute names, and local binders. -/
partial def hasFreeIdent (target : Name) (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    target.isPrefixOf (stx.getArg 0).getId.eraseMacroScopes
  else if k == ``qedProj then
    hasFreeIdent target (stx.getArg 0)
  else if k == `Qed.Lang.recField || k == ``qedCallArgNamed then
    hasFreeIdent target (stx.getArg 2)
  else if k == ``qedLam1 then
    let b := stx.getArg 0
    if b.isIdent && b.getId.eraseMacroScopes == target then false
    else hasFreeIdent target (stx.getArg 2)
  else if k == ``qedLamN then
    let ps := (stx.getArg 1).getSepArgs
    let bound := ps.any fun p => let b := p.getArg 0; b.isIdent && b.getId.eraseMacroScopes == target
    if bound then false else hasFreeIdent target (stx.getArg 4)
  else if k == ``qedExprFor then
    let b := stx.getArg 1
    let boundIds := Qed.Lang.collectQedPatIds b
    hasFreeIdent target (stx.getArg 3) ||
      (!boundIds.contains target && hasFreeIdent target (stx.getArg 5))
  else if k == ``Qed.Jsx.attrNamed then
    hasFreeIdent target (stx.getArg 1)
  else
    stx.getArgs.any (hasFreeIdent target)

def isEventEmitExpr (eventNames : Array Name) (exprStx : Syntax) : Bool :=
  match matchIdentMethodCall? exprStx with
  | some (id, "emit", _) => eventNames.contains id.getId.eraseMacroScopes
  | _ => false

def isAwaitStmt (s : Syntax) : Bool :=
  let k := s.getKind
  (k == ``qedStmtLet && (unwrapParens1 (s.getArg 4)).getKind == ``qedAwait) ||
  (k == ``qedStmtAssign && (unwrapParens1 (s.getArg 2)).getKind == ``qedAwait)

def isCollMutExpr (e : Syntax) : Bool :=
  (matchPushCall? e).isSome || (matchRemoveCall? e).isSome

def pushUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

def unpackBindProp (nm : String) (v : Term) : MacroM (Option (String × Term × Term)) := do
  if nm.startsWith "bind:" then return some ((nm.drop 5).toString, ← `(($v).1), ← `(($v).2))
  else return none

def hasEffectStmt (eventNames : Array Name) (stx : Syntax) : Bool :=
  stxAny (fun s =>
    (s.getKind == ``qedStmtExpr && !isCollMutExpr (s.getArg 0) && !isEventEmitExpr eventNames (s.getArg 0)) ||
    isAwaitStmt s) stx

def hasReturnStmt (stx : Syntax) : Bool :=
  stxAny (·.getKind == ``qedStmtReturn) stx

def lowerTypeStx (stx : Syntax) : CommandElabM Term :=
  liftMacroM (return (← lowerQedType stx false).1)

def lowerOptType (optNode : Syntax) : CommandElabM (Option Term) :=
  if optNode.getNumArgs == 2 then some <$> lowerTypeStx (optNode.getArg 1) else pure none

def parseParamList (optNode : Syntax) : CommandElabM (Array (Ident × Term)) :=
  if optNode.getNumArgs == 3 then
    (optNode.getArg 1).getSepArgs.mapM fun p => return (⟨p.getArg 0⟩, ← lowerTypeStx (p.getArg 2))
  else pure #[]

def getErrorCount : CommandElabM Nat := do
  return (← get).messages.toList.filter (·.severity == .error) |>.length

def matchNamedAttr? (a : Syntax) : Option (Syntax × String × Syntax) :=
  if a.getKind == ``Qed.Jsx.attrNamed then some (a.getArg 0, atomStr (a.getArg 0), a.getArg 1) else none

def matchAttrValExpr? (a : Syntax) : Option (Syntax × String × Syntax) := do
  let (ref, nm, valNode) ← matchNamedAttr? a
  guard (valNode.getNumArgs == 2 && (valNode.getArg 1).getKind == ``Qed.Jsx.attrValExpr)
  return (ref, nm, valNode)

def splitCompProps (propNodes : Array Syntax) (specials : List String) :
    Array (Syntax × String × Term) × Std.HashMap String (Syntax × Term) := Id.run do
  let mut rest : Array (Syntax × String × Term) := #[]
  let mut spec : Std.HashMap String (Syntax × Term) := {}
  for p in propNodes do
    let ref := p.getArg 0
    let nm := (⟨ref⟩ : TSyntax `str).getString
    let v : Term := ⟨p.getArg 2⟩
    if specials.contains nm then spec := spec.insert nm (ref, v)
    else rest := rest.push (ref, nm, v)
  return (rest, spec)

def qedSpecDispatchKind : Name := `Qed.specDispatchMarker

def mkSpecDispatchMarker (info : SourceInfo) (idx : Nat) : Syntax :=
  Syntax.node info qedSpecDispatchKind #[Syntax.mkNumLit (toString idx)]

def matchSpecDispatchMarker? (st : Syntax) : Option Nat :=
  if st.getKind == qedSpecDispatchKind then some (⟨st.getArg 0⟩ : TSyntax `num).getNat else none

def staticRootTag? (body : Syntax) : Option String :=
  if body.getKind == ``Qed.Jsx.qedExprJsx || body.getKind == ``Qed.Jsx.jsxTerm then
    let el := (body.getArg 0)
    if el.getKind == ``Qed.Jsx.selfClosing || el.getKind == ``Qed.Jsx.withChildren then
      let tag := atomStr (el.getArg 1)
      if !tag.isEmpty && !tag.front.isUpper then some tag else none
    else none
  else none

def mkJsxAttrValNode (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrValExpr
    #[Syntax.atom .none "{", Qed.Lang.mkRawExpr val, Syntax.atom .none "}"]

def mkJsxAttrExpr (name : String) (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrNamed
    #[Syntax.node .none `Qed.Jsx.jsxName #[Syntax.atom .none name],
      Syntax.node .none nullKind #[Syntax.atom .none "=", mkJsxAttrValNode val]]

def rebuildJsxEl (stx : Syntax) (attrs : Array Syntax) (kids? : Option Syntax) : Syntax :=
  let aNode := Syntax.node .none nullKind attrs
  match kids? with
  | none    => Syntax.node .none stx.getKind #[(stx.getArg 0), (stx.getArg 1), aNode, (stx.getArg 3)]
  | some kn => Syntax.node .none stx.getKind #[(stx.getArg 0), (stx.getArg 1), aNode, (stx.getArg 3), kn, (stx.getArg 5), (stx.getArg 6)]

def mkOutMatchTerm (baseName : Name) (totalCtors : Nat) (arms : Array OutArm) (outVar : Ident) :
    MacroM Term := do
  let mut alts ← arms.mapM fun arm => do
    let oCtor := mkIdent (baseName ++ `Out ++ arm.ctor)
    let argIds := (List.range arm.arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_a{i}")
    let patTerms : Array Term := argIds.map (⟨·.raw⟩)
    let callH ← Qed.Lang.mkAppTerms arm.handler patTerms
    `(Lean.Parser.Term.matchAltExpr| | $oCtor $patTerms* => some ($callH))
  if arms.size < totalCtors then
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
  `(match $outVar:ident with $[$alts:matchAlt]*)

end CompElab
end Qed
