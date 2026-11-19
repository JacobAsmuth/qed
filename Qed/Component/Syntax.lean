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
     atomic (identEq `slot) <|> atomic (identEq `collection)) >>
    ident >> optional (":" >> categoryParser `qedType 0) >> optional ("=" >> categoryParser `qedExpr 0))

def compChildrenClause : Parser := leading_parser withPosition (atomic (identEq `children))
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

def compWhenLet : Parser := leading_parser
  atomic (symbol "let" >> categoryParser `qedPat 0 >> "=") >> categoryParser `qedExpr 0 >>
  optional ("," >> sepBy1 (categoryParser `qedExpr 0) ",")

def compWhen : Parser := leading_parser
  atomic (kw "when") >> (compWhenLet <|> sepBy1 (categoryParser `qedExpr 0) ",")

def compPortInClause   : Parser := leading_parser
  withPosition (
    atomic (identEq `port >> ident >> "(") >> ident >> ":" >> categoryParser `qedType 0 >> ")" >>
    optional compWhen >> ":" >> qedSuite)

def compRpcQueryClause : Parser := leading_parser
  withPosition (
    atomic (identEq `query >> ident >> optional (":" >> categoryParser `qedType 0) >> "=") >>
    ident >> "(" >> sepBy (categoryParser `qedExpr 0) "," >> ")" >>
    optional compWhen)

def compQueryClause    : Parser := leading_parser
  withPosition (
    atomic (identEq `query >> ident >> ":") >> categoryParser `qedType 0 >> ":" >>
    checkColGt >>
    withPosition (identEq `key >> "=" >> categoryParser `qedExpr 0 >>
                  checkColGe >> identEq `url >> "=" >> categoryParser `qedExpr 0))

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
    optional compWhen >>
    optional (":" >> checkColGt "expected indented `subscribe` handlers" >> many1Indent compSubHandler))

def compActionClause   : Parser := leading_parser
  withPosition (
    atomic (identEq `action) >> ident >> compParamsOpt >>
    optional compWhen >> ":" >> qedSuite)

def compInvName : Parser := leading_parser ident >> ":"

def compForEachInvClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> optional (atomic compInvName) >> categoryParser `qedExpr 0 >> kw "for_each" >> ident) >>
    optional (kw "holds_in" >> identEq `view) >>
    optional (kw "using" >> ident) >>
    optional (":=" >> termParser))

def compInvariantClause : Parser := leading_parser
  withPosition (
    "invariant " >> optional (atomic compInvName) >> sepBy1 (categoryParser `qedExpr 0) "," >>
    optional (kw "holds_in" >> identEq `view >> optional (kw "assuming" >> categoryParser `qedExpr 0)) >>
    optional (kw "using" >> "[" >> sepBy termParser "," >> "]") >>
    optional (":=" >> termParser))

def compStyleClause : Parser := leading_parser
  withPosition (
    atomic (identEq `style >> notFollowedBy (symbol ":=") "':='") >>
    ident >>
    optional Qed.StyleDsl.styleExtendsClause >>
    optional Qed.StyleDsl.styleStrictClause >>
    ":" >>
    many1 (checkColGt >> categoryParser `cssBlockItem 0))

def compStylesheetClause : Parser := leading_parser
  withPosition (atomic (identEq `stylesheet) >> strLit)

def compThemeClause : Parser := leading_parser
  withPosition (atomic (identEq `theme) >> ident)

def compInvAny : Parser := compForEachInvClause <|> compInvariantClause

def compClause : Parser :=
  compSessionClause <|> compFieldClause <|> compChildrenClause <|> compKeyClause <|>
  compEventClause <|> compStartClause <|> compRouteClause <|>
  compPortOutClause <|> compPortInClause <|> compRpcQueryClause <|> compQueryClause <|>
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

def isCdot (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCdot || u.getKind == ``Lean.Parser.Term.cdot || (u.reprint.getD "").trimmed == "·"

def atomStr : Syntax → String := Qed.Jsx.tokenVal
def asTerm (s : Syntax) : Term := ⟨s⟩

partial def mentionsIdent (stx : Syntax) (n : Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

def unpackSeq (seqStx : Syntax) : Array Syntax :=
  Qed.Lang.suiteStmts seqStx

partial def hasPerformNode (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``qedStmtPerform ||
  (k == ``qedStmtLet && (unwrapParens1 (stx.getArg 4)).getKind == ``qedAwait) ||
  (k == ``qedStmtAssign && (unwrapParens1 (stx.getArg 2)).getKind == ``qedAwait) ||
  stx.getArgs.any hasPerformNode

partial def hasReturnStmt (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``qedStmtReturn || k == ``qedStmtEnsure || stx.getArgs.any hasReturnStmt

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
