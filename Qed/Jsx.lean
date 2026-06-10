/-
  Qed.Jsx: the JSX view syntax.

  This is the one way to write an element. `<div class="x" onClick={.tap}>…</div>`
  is *pure sugar*: every element expands to `Qed.el "tag" [attrs] [children]`, so
  using it costs nothing in guarantees, and the `view%` lift (see `Qed.View`) sees
  the expanded form and keeps its fine-grained update paths.

  Shapes:
    <div class="counter"> … </div>            -- string attribute
    <button onClick={.increment}>+</button>   -- term attribute (events, anything typed)
    <input value={m.draft} disabled/>         -- self-closing; bare flag = `true`
    <span {if on then a else b}>…</span>      -- a spliced `Attr` term
    <li>{m.count}</li>                        -- a spliced child (value or Html)
    <ul>{m.rows.map fun r => <li key={r.id}>…</li>}</ul>  -- a keyed list

  Text runs are literal. Whitespace normalizes the JSX way: runs collapse to one
  space, and a run containing a newline at a text edge disappears (so indentation
  never renders). `{`, `}` and `<` cannot appear in a text run; splice them
  (`{"{"}`). An unknown attribute name becomes `attr "name" value`, so any
  attribute (`data-*`, `aria-*`, SVG geometry) is reachable inline.

  The whole element parses atomically: if `<` does not begin a well-formed
  element the parser backtracks, so comparisons (`a < b`) are unaffected.
-/
import Lean
import Qed.Notation
import Qed.View

namespace Qed.Jsx
open Lean Parser PrettyPrinter

/-! ### Token-level parsers

`jsxText` (a raw character run) and `jsxName` (a tag/attribute name, which may be a
Lean keyword like `section` or contain hyphens like `data-role`) cannot be ordinary
`ident`/token parsers, so they consume characters directly. -/

/-- A run of literal JSX text: everything up to the next `<`, `{` or `}`. -/
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

/-- A tag or attribute name: letters, digits, `-`, `_` (so `section`, `my-widget`,
    `aria-label` all parse, none of which an `ident` accepts). -/
def jsxNameFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := takeWhile1Fn (fun ch => ch.isAlphanum || ch == '-' || ch == '_')
    "tag or attribute name" c s
  if s.hasError then s else mkNodeToken `Qed.Jsx.jsxName startPos true c s

def jsxName : Parser where
  fn := jsxNameFn

@[combinator_formatter Qed.Jsx.jsxName]
def jsxName.formatter : Formatter := Formatter.visitAtom `Qed.Jsx.jsxName
@[combinator_parenthesizer Qed.Jsx.jsxName]
def jsxName.parenthesizer : Parenthesizer := Parenthesizer.visitToken

/-! ### Grammar -/

declare_syntax_cat jsxElement
declare_syntax_cat jsxAttr

/-- An attribute value: a string literal or a spliced term. -/
syntax jsxAttrVal := str <|> ("{" term "}")

syntax (name := attrNamed)  jsxName ("=" jsxAttrVal)? : jsxAttr
syntax (name := attrSplice) "{" term "}" : jsxAttr

/-- A child: a text run, a spliced term, or a nested element. An ordered `<|>`
    (not a syntax category) so the raw text parser is tried without tokenizing
    first; a category dispatch would choke on text starting with a non-token
    character (`−`, `•`, …). -/
syntax jsxChild := jsxText <|> ("{" term "}") <|> jsxElement

syntax (name := selfClosing)  "<" jsxName jsxAttr* "/>" : jsxElement
syntax (name := withChildren) "<" jsxName jsxAttr* ">" jsxChild* "</" jsxName ">" : jsxElement

/-- A JSX element is a term. `atomic` so a failed parse backtracks: `a < b`
    stays a comparison. -/
syntax:max (name := jsxTerm) atomic(jsxElement) : term

/-! ### Expansion -/

/-- The string under a `jsxText`/`jsxName` token node. -/
private def tokenVal : Syntax → String
  | .node _ _ #[.atom _ v] => v
  | .atom _ v              => v
  | _                      => ""

/-- The trailing whitespace captured after `stx`'s last token (`""` if none). -/
private def trailingWs (stx : Syntax) : String :=
  match stx.getTailInfo with
  | .original _ _ trail _ => trail.toString
  | _                     => ""

/-- Collapse a whitespace run: a run containing a newline at the edge of a text node
    vanishes (indentation never renders); any other run is one space. -/
private def collapseRun (run : String) (edge : Bool) : String :=
  if run.isEmpty then "" else if edge && run.contains '\n' then "" else " "

/-- Normalize a JSX text run (with `lead`, the whitespace the tokenizer attached to
    the previous token, restored in front). -/
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

/-- Attribute names that map to a typed helper in `Qed.Notation` (applied to the value). -/
private def helperAttrs : List String :=
  ["value", "placeholder", "name", "href", "src", "alt", "title", "style", "key",
   "role", "rawHtml", "onClick", "onInput", "onChange", "onCheck", "onKeydown",
   "onKeyup", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown",
   "onMouseUp", "disabled", "required", "checked", "readOnly"]

/-- Boolean-flag helpers: a bare `<input disabled/>` becomes `disabled true`. -/
private def flagAttrs : List String := ["disabled", "required", "checked", "readOnly"]

/-- The helper a JSX attribute name expands through, if any (`class` → `cls`,
    `type` → `type'`, helpers by their own name). -/
private def attrHelper? (n : String) : Option Name :=
  if n == "class" then some (Name.mkStr2 "Qed" "cls")
  else if n == "type" then some (Name.mkStr2 "Qed" "type'")
  else if helperAttrs.contains n then some (Name.mkStr2 "Qed" n)
  else none

mutual

/-- Expand every JSX element inside an arbitrary term (bottom-up), so a spliced
    `{…}` containing more JSX is fully reduced. Used directly by the `view%`
    pre-pass; in plain terms the `jsxTerm` macro reaches the same code. -/
partial def expandJsxIn (stx : Syntax) : MacroM Syntax := do
  if stx.getKind == ``jsxTerm then
    elementToTerm stx[0]
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM expandJsxIn)
    | other                => return other

/-- One attribute node → an `Attr` term. -/
partial def attrToTerm (stx : Syntax) : MacroM Term := do
  if stx.getKind == ``attrSplice then
    return ⟨← expandJsxIn stx[1]⟩
  -- attrNamed: jsxName ("=" jsxAttrVal)?
  let name := tokenVal stx[0]
  let valNode := stx[1]
  if valNode.getNumArgs == 0 then
    -- bare flag: a known boolean helper gets `true`; anything else is an empty-valued attr
    if flagAttrs.contains name then
      return ⟨← `($(mkCIdent (Name.mkStr2 "Qed" name)) true)⟩
    else
      return ⟨← `(Qed.attr $(Syntax.mkStrLit name) "")⟩
  else
    -- valNode = null["=", jsxAttrVal]; jsxAttrVal = strLit | group("{" term "}")
    let inner := valNode[1][0]
    let vT : Term ←
      if inner.isOfKind strLitKind then pure ⟨inner⟩
      else pure ⟨← expandJsxIn inner[1]⟩
    match attrHelper? name with
    | some h => return ⟨← `($(mkCIdent h) $vT)⟩
    | none   => return ⟨← `(Qed.attr $(Syntax.mkStrLit name) $vT)⟩

/-- Is this term syntactically `xs.map (fun x => …)` (one argument)? If so a lone
    spliced child is passed straight through as the children, the shape the
    `view%` lift turns into a fine-grained keyed list. -/
partial def isMapCall (stx : Syntax) : Bool :=
  let s := if stx.getKind == ``Lean.Parser.Term.paren && stx.getNumArgs == 3
    then stx[1] else stx
  if s.getKind == ``Lean.Parser.Term.app && s.getNumArgs == 2 then
    match s[0] with
    | .ident _ _ n _ =>
        (match n.eraseMacroScopes with | .str _ s => s == "map" | _ => false)
        && s[1].getNumArgs == 1
    | _ => false
  else false

/-- The children of an element → the children argument of `el`. Each child node is
    `jsxChild[ jsxText | group("{" term "}") | jsxElement ]`. -/
partial def childrenToTerm (opener : Syntax) (kids : Array Syntax) : MacroM Term := do
  let isText (k : Syntax) : Bool := k[0].getKind == `Qed.Jsx.jsxText
  let isElement (k : Syntax) : Bool :=
    k[0].getKind == ``selfClosing || k[0].getKind == ``withChildren
  -- A single spliced `.map` child becomes the children list itself (the keyed-list
  -- shape): `.toList` pins the element type so the row elaborates against the
  -- parent's `msg`, and the `view%` lift sees through it (`asMap?`).
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
      -- whitespace between two non-text children renders as one space, unless it
      -- contains a newline (the JSX rule: indentation never renders)
      let gap := trailingWs prev
      if !gap.isEmpty && !gap.contains '\n' && (prev == opener || !isText prev) then
        out := out.push ⟨Syntax.mkStrLit " "⟩
      if isElement k then
        out := out.push (← elementToTerm k[0])
      else
        out := out.push ⟨← expandJsxIn k[0][1]⟩
    prev := k
  `([$out,*])

/-- One JSX element → `Qed.el "tag" [attrs] children`. -/
partial def elementToTerm (stx : Syntax) : MacroM Term := do
  if stx.getKind == ``selfClosing then
    let tag := tokenVal stx[1]
    let attrs ← stx[2].getArgs.mapM attrToTerm
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] [])
  else if stx.getKind == ``withChildren then
    let tag := tokenVal stx[1]
    let closeTag := tokenVal stx[6]
    if tag != closeTag then
      Macro.throwErrorAt stx[6] s!"mismatched closing tag: expected </{tag}>, found </{closeTag}>"
    let attrs ← stx[2].getArgs.mapM attrToTerm
    let kids ← childrenToTerm stx[3] stx[4].getArgs
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] $kids)
  else
    Macro.throwUnsupported

end

/-- A JSX element in term position expands in place. -/
@[macro jsxTerm] def expandJsxTerm : Macro := fun stx => do
  return (← elementToTerm stx[0])

/-- Does this syntax contain any JSX? -/
private partial def hasJsx : Syntax → Bool
  | .node _ kind args => kind == ``jsxTerm || args.any hasJsx
  | _                 => false

/-- The `view%` pre-pass: expand all JSX in the body *before* the fine-grained lift
    runs, so the lift sees the `el "tag" [attrs] [kids]` shapes it decomposes into
    value updates, signals and keyed lists. Declared after `Qed.View`'s rule, so it
    is tried first; with no JSX present it defers to the original. -/
macro_rules
  | `(view% fun $m:ident => $body) => do
      if !hasJsx body then Macro.throwUnsupported
      let body' : Term := ⟨← expandJsxIn body⟩
      `(view% fun $m => $body')

end Qed.Jsx
