import Lean
import Qed.Notation
import Qed.View

namespace Qed.Jsx
open Lean Parser PrettyPrinter

def jsxTextFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := takeWhile1Fn (fun ch => ch != '<' && ch != '{' && ch != '}') "JSX text" c s
  if s.hasError then s else mkNodeToken `Qed.Jsx.jsxText startPos true c s

def jsxText : Parser where
  fn := jsxTextFn

@[combinator_formatter Qed.Jsx.jsxText]
def jsxText.formatter : Formatter := Formatter.visitAtom `Qed.Jsx.jsxText
@[combinator_parenthesizer Qed.Jsx.jsxText]
def jsxText.parenthesizer : Parenthesizer := Parenthesizer.visitToken

def jsxNameFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := takeWhile1Fn (fun ch => ch.isAlphanum || ch == '-' || ch == '_' || ch == '.')
    "tag or attribute name" c s
  if s.hasError then s else mkNodeToken `Qed.Jsx.jsxName startPos true c s

def jsxName : Parser where
  fn := jsxNameFn

@[combinator_formatter Qed.Jsx.jsxName]
def jsxName.formatter : Formatter := Formatter.visitAtom `Qed.Jsx.jsxName
@[combinator_parenthesizer Qed.Jsx.jsxName]
def jsxName.parenthesizer : Parenthesizer := Parenthesizer.visitToken

declare_syntax_cat jsxElement
declare_syntax_cat jsxAttr

syntax jsxAttrVal := str <|> ("{" term "}")

syntax (name := attrNamed)  jsxName ("=" jsxAttrVal)? : jsxAttr
syntax (name := attrSplice) "{" term "}" : jsxAttr

-- Ordered `<|>` (not a syntax category) so `jsxText` runs before tokenizing non-token chars like `•`.
syntax jsxChild := jsxText <|> ("{" term "}") <|> jsxElement

syntax (name := selfClosing)  "<" jsxName jsxAttr* "/>" : jsxElement
syntax (name := withChildren) "<" jsxName jsxAttr* ">" jsxChild* "</" jsxName ">" : jsxElement

syntax:max (name := jsxTerm) atomic(jsxElement) : term

private def tokenVal : Syntax → String
  | .node _ _ #[.atom _ v] => v
  | .atom _ v              => v
  | _                      => ""

private def trailingWs (stx : Syntax) : String :=
  match stx.getTailInfo with
  | .original _ _ trail _ => trail.toString
  | _                     => ""

private def collapseRun (run : String) (edge : Bool) : String :=
  if run.isEmpty then "" else if edge && run.contains '\n' then "" else " "

private def normalizeText (lead : String) (raw : String) : String :=
  let s := lead ++ raw
  let chars := s.toList
  let rec go (cs : List Char) (acc : List Char) (run : List Char) (atStart : Bool) : List Char :=
    match cs with
    | [] => acc ++ (collapseRun (String.ofList run) true).toList
    | ch :: rest =>
        if ch.isWhitespace then go rest acc (run ++ [ch]) atStart
        else
          let sep := collapseRun (String.ofList run) atStart
          go rest (acc ++ sep.toList ++ [ch]) [] false
  String.ofList (go chars [] [] true)

private def helperAttrs : List String :=
  ["value", "placeholder", "name", "href", "src", "alt", "title", "style", "key",
   "role", "rawHtml", "onClick", "onInput", "onChange", "onCheck", "onKeydown",
   "onKeyup", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown",
   "onMouseUp", "disabled", "required", "checked", "readOnly"]

private def flagAttrs : List String := ["disabled", "required", "checked", "readOnly"]

private def attrHelper? (n : String) : Option Name :=
  if n == "class" then some (Name.mkStr2 "Qed" "cls")
  else if n == "type" then some (Name.mkStr2 "Qed" "type'")
  else if helperAttrs.contains n then some (Name.mkStr2 "Qed" n)
  else none

mutual

partial def expandJsxIn (stx : Syntax) : MacroM Syntax := do
  if stx.getKind == ``jsxTerm then
    elementToTerm stx[0]
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM expandJsxIn)
    | other                => return other

partial def attrToTerm (stx : Syntax) : MacroM Term := do
  if stx.getKind == ``attrSplice then
    return ⟨← expandJsxIn stx[1]⟩
  let name := tokenVal stx[0]
  let valNode := stx[1]
  if valNode.getNumArgs == 0 then
    if flagAttrs.contains name then
      return ⟨← `($(mkCIdent (Name.mkStr2 "Qed" name)) true)⟩
    else
      return ⟨← `(Qed.attr $(Syntax.mkStrLit name) "")⟩
  else
    let inner := valNode[1][0]
    let vT : Term ←
      if inner.isOfKind strLitKind then pure ⟨inner⟩
      else pure ⟨← expandJsxIn inner[1]⟩
    match attrHelper? name with
    | some h => return ⟨← `($(mkCIdent h) $vT)⟩
    | none   => return ⟨← `(Qed.attr $(Syntax.mkStrLit name) $vT)⟩

partial def isMapCall (stx : Syntax) : Bool :=
  let s := if stx.getKind == ``Lean.Parser.Term.paren && stx.getNumArgs == 3
    then stx[1] else stx
  if s.getKind == ``Lean.Parser.Term.app && s.getNumArgs == 2 then
    match s[0] with
    | .ident _ _ n _ =>
        match n.eraseMacroScopes with
        | .str _ name => (name == "map" && s[1].getNumArgs == 1) || name == "each"
        | _ => false
    | _ => false
  else false

partial def childrenToTerm (opener : Syntax) (kids : Array Syntax) : MacroM Term := do
  let isText (k : Syntax) : Bool := k[0].getKind == `Qed.Jsx.jsxText
  let isElement (k : Syntax) : Bool :=
    k[0].getKind == ``selfClosing || k[0].getKind == ``withChildren
  if kids.size == 1 && !isText kids[0]! && !isElement kids[0]! then
    let t ← expandJsxIn kids[0]![0][1]
    if isMapCall t then return ⟨← `((($(⟨t⟩)).toList))⟩
    else return ⟨← `([$(⟨t⟩):term])⟩
  let mut out : Array Term := #[]
  let mut prev := opener
  for k in kids do
    if isText k then
      let s := normalizeText (trailingWs prev) (tokenVal k[0])
      if !s.isEmpty then out := out.push ⟨Syntax.mkStrLit s⟩
    else
      let gap := trailingWs prev
      if !gap.isEmpty && !gap.contains '\n' && (prev == opener || !isText prev) then
        out := out.push ⟨Syntax.mkStrLit " "⟩
      if isElement k then
        out := out.push (← elementToTerm k[0])
      else
        out := out.push ⟨← expandJsxIn k[0][1]⟩
    prev := k
  `([$out,*])

partial def componentToTerm (stx : Syntax) (tag : String)
    (attrStxs : Array Syntax) (kids : Array Syntax) : MacroM Term := do
  let cName := (tag.splitOn ".").foldl Name.str Name.anonymous
  let cId (sub : Name) : Term := ⟨mkIdent (cName ++ sub)⟩
  unless kids.isEmpty do
    Macro.throwErrorAt stx s!"<{tag}>: a component tag renders the component's own view, \
      so it takes no children; write it self-closing (<{tag} …/>)"
  let mut props    : Array (Syntax × String × Term) := #[]
  let mut key?     : Option Term := none
  let mut state?   : Option Term := none
  let mut initial? : Option Term := none
  let mut onMsg?   : Option Term := none
  let mut onEmit?  : Option Term := none
  for a in attrStxs do
    if a.getKind == ``attrSplice then
      Macro.throwErrorAt a s!"<{tag}>: a component tag takes props (field=\{…}, key, \
        onEmit, state, onMsg); a spliced attribute belongs on an HTML element"
    let name := tokenVal a[0]
    let valNode := a[1]
    let v : Term ←
      if valNode.getNumArgs == 0 then `(Bool.true)
      else
        let inner := valNode[1][0]
        if inner.isOfKind strLitKind then pure ⟨inner⟩
        else pure ⟨← expandJsxIn inner[1]⟩
    match name with
    | "key"     => key? := some v
    | "state"   => state? := some v
    | "initial" => initial? := some v
    | "onMsg"   => onMsg? := some v
    | "onEmit"  => onEmit? := some v
    | _         => props := props.push (a[0], name, v)
  match state? with
  | some st =>
      if initial?.isSome then
        Macro.throwErrorAt stx "`initial` seeds local state; it cannot accompany `state`"
      if onEmit?.isSome then
        Macro.throwErrorAt stx s!"<{tag} state=\{…}>: a parent-owned component routes \
          every event through onMsg, it has no separate emit channel"
      match onMsg? with
      | none =>
          Macro.throwErrorAt stx s!"<{tag} state=\{…}> needs onMsg=\{…}: the parent Msg \
            constructor `(k : String) (msg : {tag}.Msg)` its events route through"
      | some route =>
          let fids := props.map fun (_, n, _) => mkIdent (Name.mkSimple n)
          let vals := props.map fun (_, _, v) => v
          let p ← `(({ $[$fids:ident := $vals],* } : $(cId `Props)))
          match key? with
          | some k => `($(cId `renderTag) $p $route $st (toString $k))
          | none   => `($(cId `renderTag) $p $route $st)
  | none =>
      if onMsg?.isSome then
        Macro.throwErrorAt stx s!"<{tag}>: onMsg routes a parent-owned row; bind one with \
          state=\{…}, or receive outputs with onEmit=\{…}"
      let keyT : Term ← match key? with
        | some k => `(toString $k)
        | none   => pure ⟨Syntax.mkStrLit s!"@{(stx.getPos?.map (·.byteIdx)).getD 0}"⟩
      let mountBase : Term ← match onEmit? with
        | some h => `($(cId `mountWith) $keyT (fun out => $h out))
        | none   => `($(cId `mount) $keyT)
      -- Unresolved `mkIdent`: `Qed.Component` / `Qed.Runtime` sit above `Qed.Jsx` in the import graph.
      let mountBase ← match initial? with
        | none => pure mountBase
        | some seed => `($(mkIdent `Qed.Attr.localInit) $mountBase ($seed : $(cId `State)))
      let fids := props.map fun (_, n, _) => mkIdent (Name.mkSimple n)
      let vals := props.map fun (_, _, v) => v
      let values ← `(({ $[$fids:ident := $vals],* } : $(cId `Props)))
      let mountT ← `($(mkIdent `Qed.Attr.localProps) $mountBase $values)
      `(Qed.el "div" [Qed.key $keyT, $mountT] [])

partial def elementToTerm (stx : Syntax) : MacroM Term := do
  if stx.getKind == ``selfClosing then
    let tag := tokenVal stx[1]
    if !tag.isEmpty && tag.front.isUpper then
      return ← componentToTerm stx tag stx[2].getArgs #[]
    let attrs ← stx[2].getArgs.mapM attrToTerm
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] [])
  else if stx.getKind == ``withChildren then
    let tag := tokenVal stx[1]
    let closeTag := tokenVal stx[6]
    if tag != closeTag then
      Macro.throwErrorAt stx[6] s!"mismatched closing tag: expected </{tag}>, found </{closeTag}>"
    if !tag.isEmpty && tag.front.isUpper then
      return ← componentToTerm stx tag stx[2].getArgs stx[4].getArgs
    let attrs ← stx[2].getArgs.mapM attrToTerm
    let kids ← childrenToTerm stx[3] stx[4].getArgs
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] $kids)
  else
    Macro.throwUnsupported

end

@[macro jsxTerm] def expandJsxTerm : Macro := fun stx => do
  return (← elementToTerm stx[0])

private partial def hasJsx : Syntax → Bool
  | .node _ kind args => kind == ``jsxTerm || args.any hasJsx
  | _                 => false

-- Declared after `Qed.View`'s `macro_rules` so JSX expands before `view%` lifts the body.
macro_rules
  | `(view% fun $m:ident => $body) => do
      if !hasJsx body then Macro.throwUnsupported
      let body' : Term := ⟨← expandJsxIn body⟩
      `(view% fun $m => $body')

end Qed.Jsx
