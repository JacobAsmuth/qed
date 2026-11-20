import Qed.Component.Core
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
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.fullName info) acc) {}
    addEntryFn := fun m info => m.insert info.fullName info
  }

open Lean in
def lookupComponent? (cName : Name) : CoreM (Option ComponentInfo) := do
  let env ← getEnv
  let reg := componentRegistry.getState env
  let ns ← getCurrNamespace
  if let some info := reg.find? (ns ++ cName) then return some info
  if let some info := reg.find? cName then return some info
  for (fullView, _) in ResolveName.resolveGlobalName env {} ns (← getOpenDecls) (cName ++ `view) do
    if let some info := reg.find? fullView.getPrefix then return some info
  return none

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

def compSubOnMsg : Parser :=
  node `Qed.compSubOnMsg (withPosition (atomic (identEq `on_message) >> "(" >> qedBinder >> ")" >> ":" >> qedSuite))

def compSubOnStatus : Parser :=
  node `Qed.compSubOnStatus (withPosition (atomic (identEq `on_status) >> "(" >> qedBinder >> ")" >> ":" >> qedSuite))

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

def compInvAny : Parser := compForEachInvClause <|> compInvariantClause

def compClause : Parser :=
  compSessionClause <|> compFieldClause <|> compKeyClause <|>
  compEventClause <|> compStartClause <|> compRouteClause <|>
  compPortOutClause <|> compPortInClause <|> compRpcQueryClause <|>
  compSubscribeClause <|> compStyleClause <|> compStylesheetClause <|> compThemeClause <|>
  compActionClause <|> compInvAny

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
def asTerm (s : Syntax) : Term := ⟨s⟩

partial def mentionsIdent (stx : Syntax) (n : Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

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
    hasFreeIdent target (stx.getArg 3) ||
      (!(b.isIdent && b.getId.eraseMacroScopes == target) && hasFreeIdent target (stx.getArg 5))
  else if k == ``Qed.Jsx.attrNamed then
    hasFreeIdent target (stx.getArg 1)
  else
    stx.getArgs.any (hasFreeIdent target)

def unpackSeq (seqStx : Syntax) : Array Syntax :=
  Qed.Lang.suiteStmts seqStx

def isEventEmitExpr (eventNames : Array Name) (exprStx : Syntax) : Bool :=
  match matchIdentMethodCall? exprStx with
  | some (id, "emit", _) => eventNames.contains id.getId.eraseMacroScopes
  | _ => false

partial def hasEffectStmt (eventNames : Array Name) (stx : Syntax) : Bool :=
  let k := stx.getKind
  (k == ``qedStmtExpr && (matchPushCall? (stx.getArg 0)).isNone && !isEventEmitExpr eventNames (stx.getArg 0)) ||
  (k == ``qedStmtLet && (unwrapParens1 (stx.getArg 4)).getKind == ``qedAwait) ||
  (k == ``qedStmtAssign && (unwrapParens1 (stx.getArg 2)).getKind == ``qedAwait) ||
  stx.getArgs.any (hasEffectStmt eventNames)

partial def hasReturnStmt (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``qedStmtReturn || stx.getArgs.any hasReturnStmt

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
    let callH ← argIds.foldlM (init := arm.handler) fun acc id => `($acc $id:ident)
    `(Lean.Parser.Term.matchAltExpr| | $oCtor $patTerms* => some ($callH))
  if arms.size < totalCtors then
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
  `(match $outVar:ident with $[$alts:matchAlt]*)

end CompElab
end Qed
