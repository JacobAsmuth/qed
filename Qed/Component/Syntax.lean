import Qed.Component.Core
import Qed.Jsx
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
  hasLocalDef : Bool := false
  rootTag?    : Option String
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

/-! ## Component & App Surface Syntax -/

declare_syntax_cat compStmt

section CompParsers
open Lean Parser

private def sendKw : Parser :=
  nonReservedSymbol "send" (includeIdent := true)

private def actionParam : Parser :=
  node `Qed.componentActionParam ("(" >> ident >> " : " >> termParser >> ")")

@[term_parser] def sendTerm := leading_parser:maxPrec sendKw >> termParser maxPrec

@[term_parser] def fieldSetterTerm := leading_parser:maxPrec
  atomic ("(" >> Parser.ident >> " := ") >> symbol "·" >> ")"

@[macro sendTerm] def expandSendTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx "`send …` is the component output; it only has meaning inside a `component … view =>` body"
@[macro fieldSetterTerm] def expandFieldSetterOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx "`(field := ·)` is a component field setter; it only has meaning inside a `component` body"

def compStmtSeq : Parser :=
  node `Qed.compStmtSeq
    (checkColGt >> categoryParser `compStmt 0 >>
     many (atomic (optional "," >> checkColGt >> categoryParser `compStmt 0)))

def compMatchAlt : Parser := leading_parser
  withPosition ("| " >> sepBy1 termParser "," >> " => " >> compStmtSeq)

@[compStmt_parser] def actionNoopStmt : Parser := leading_parser withPosition (atomic ("(" >> ")"))
@[compStmt_parser] def actionReturnStmt : Parser := leading_parser withPosition (atomic (symbol "return"))
@[compStmt_parser] def actionLetStmt : Parser := leading_parser
  withPosition ("let " >> ident >> optional (" : " >> termParser) >> " := " >> termParser)
@[compStmt_parser] def actionPerformStmt : Parser := leading_parser
  withPosition (atomic (nonReservedSymbol "perform" (includeIdent := true)) >> checkColGt >> termParser)
@[compStmt_parser] def actionSendStmt : Parser := leading_parser
  withPosition (atomic sendKw >> checkColGt >> termParser)
@[compStmt_parser] def actionIfLetStmt : Parser := leading_parser
  withPosition (atomic ("if " >> "let ") >> termParser >> " := " >> termParser >> " then " >>
                compStmtSeq >> optional (atomic (checkColGe >> "else ") >> compStmtSeq))
@[compStmt_parser] def actionIfStmt : Parser := leading_parser
  withPosition ("if " >> notFollowedBy (symbol "let") "let" >>
                optional (atomic (ident >> " : ")) >> termParser >> " then " >>
                compStmtSeq >> optional (atomic (checkColGe >> "else ") >> compStmtSeq))
@[compStmt_parser] def actionMatchStmt : Parser := leading_parser
  withPosition ("match " >> sepBy1 termParser "," >> " with" >> many1 (checkColGe >> compMatchAlt))
@[compStmt_parser] def actionAssignStmt : Parser := leading_parser
  withPosition (atomic (ident >> (symbol ":=" <|> symbol "+=" <|> symbol "-=")) >> termParser)

def compFieldClause : Parser := leading_parser
  withPosition (
    (atomic (identEq `state) <|> atomic (identEq `ephemeral) <|>
     atomic (identEq `prop) <|> atomic (identEq `bind) <|>
     atomic (identEq `slot) <|> atomic (identEq `collection)) >>
    ident >> optional (" : " >> termParser) >> optional (" := " >> termParser))
def compChildrenClause : Parser := leading_parser withPosition (atomic (identEq `children))
def compKeyClause      : Parser := leading_parser withPosition (atomic (identEq `key) >> ident)
def compEventClause    : Parser := leading_parser
  withPosition (atomic (identEq `event) >> ident >> many actionParam)
def compStartClause    : Parser := leading_parser
  withPosition (atomic (identEq `start) >> checkColGt >> termParser)
def compRouteClause    : Parser := leading_parser
  withPosition (atomic (identEq `route) >> optional ident >> " : " >> termParser >> " := " >> termParser >>
                many (checkColGt >> compMatchAlt))
def compPortOutClause  : Parser := leading_parser
  withPosition (atomic (identEq `port >> ident >> " : ") >> termParser)
def compPortInClause   : Parser := leading_parser
  withPosition (atomic (identEq `port >> ident >> "(") >> ident >> " : " >> termParser >> ")" >>
                optional (atomic (identEq `when) >> termParser) >> " => " >> compStmtSeq)
def compQueryClause    : Parser := leading_parser
  withPosition (
    atomic (identEq `query >> ident >> " : ") >> withPosition termParser >>
    checkColGt >>
    withPosition (identEq `key >> " := " >> withPosition termParser >>
                  checkColGe >> identEq `url >> " := " >> withPosition termParser))
def compActionClause   : Parser := leading_parser
  withPosition (atomic (identEq `action) >> ident >> many actionParam >>
                optional (atomic (identEq `when) >> termParser) >> " => " >> compStmtSeq)
def compInvName : Parser := leading_parser ident >> " : "
def compForEachInvClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> optional (atomic compInvName) >> termParser >> " for_each " >> ident) >>
    optional (" holds_in " >> identEq `view) >>
    optional (" using " >> ident) >>
    optional (" := " >> termParser))
def compInvariantClause : Parser := leading_parser
  withPosition (
    "invariant " >> optional (atomic compInvName) >> sepBy1 termParser "," >>
    optional (" holds_in " >> identEq `view >> optional (" assuming " >> termParser maxPrec)) >>
    optional (" using " >> "[" >> sepBy termParser "," >> "]") >>
    optional (" := " >> termParser))
def compInvAny : Parser := compForEachInvClause <|> compInvariantClause

def compClause : Parser :=
  compFieldClause <|> compChildrenClause <|> compKeyClause <|>
  compEventClause <|> compStartClause <|> compRouteClause <|>
  compPortOutClause <|> compPortInClause <|> compQueryClause <|>
  compActionClause <|> compInvAny

@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "component " >>
    ident >> " where " >>
    many (checkColGt >> compClause) >>
    checkColGt >> identEq `view >> " => " >> checkColGt >> termParser >>
    many (checkColGt >> compInvAny))

end CompParsers

/-! ## Shared Syntax & JSX Helpers -/

section CompElab
open Lean Elab Command

structure OutArm where
  ctor    : Name
  arity   : Nat
  handler : Term

def isCdot (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.cdot || (stx.reprint.getD "").trimmed == "·"

def atomStr : Syntax → String := Qed.Jsx.tokenVal
def asTerm (s : Syntax) : Term := ⟨s⟩

partial def mentionsIdent (stx : Syntax) (n : Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

def unpackSeq (seqStx : Syntax) : Array Syntax :=
  if seqStx.getKind == `Qed.compStmtSeq then
    #[seqStx[0]] ++ seqStx[1].getArgs.map fun m => m[m.getNumArgs - 1]!
  else #[seqStx]

partial def hasPerformNode (stx : Syntax) : Bool :=
  stx.getKind == ``actionPerformStmt || stx.getArgs.any hasPerformNode

partial def hasReturnStmt (stx : Syntax) : Bool :=
  stx.getKind == ``actionReturnStmt || stx.getArgs.any hasReturnStmt

def staticRootTag? (body : Syntax) : Option String :=
  if body.getKind == ``Qed.Jsx.jsxTerm then
    let el := body[0]
    if el.getKind == ``Qed.Jsx.selfClosing || el.getKind == ``Qed.Jsx.withChildren then
      let tag := atomStr el[1]
      if !tag.isEmpty && !tag.front.isUpper then some tag else none
    else none
  else none

def mkJsxAttrValNode (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrValExpr
    #[Syntax.atom .none "{", Syntax.node .none ``Qed.Jsx.jsxTermExpr #[val.raw], Syntax.atom .none "}"]

def mkJsxAttrExpr (name : String) (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrNamed
    #[Syntax.node .none `Qed.Jsx.jsxName #[Syntax.atom .none name],
      Syntax.node .none nullKind #[Syntax.atom .none "=", mkJsxAttrValNode val]]

def rebuildJsxEl (stx : Syntax) (attrs : Array Syntax) (kids? : Option Syntax) : Syntax :=
  let aNode := Syntax.node .none nullKind attrs
  match kids? with
  | none    => Syntax.node .none stx.getKind #[stx[0], stx[1], aNode, stx[3]]
  | some kn => Syntax.node .none stx.getKind #[stx[0], stx[1], aNode, stx[3], kn, stx[5], stx[6]]

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
