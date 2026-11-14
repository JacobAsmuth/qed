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
declare_syntax_cat jsxAttrVal
declare_syntax_cat jsxExpr

syntax (name := jsxIfLet)
  atomic("if " "let ") term " := " term " then " jsxExpr (" else " jsxExpr)? : jsxExpr
syntax (name := jsxIf)
  "if " (atomic(ident " : "))? term " then " jsxExpr (" else " jsxExpr)? : jsxExpr
@[jsxExpr_parser] def jsxTermExpr : Parser := leading_parser
  notFollowedBy (symbol "if") "if" >> termParser

def jsxAssignOp : Parser := symbol ":=" <|> symbol "+=" <|> symbol "-="
def jsxAssignItem : Parser := node `Qed.Jsx.jsxAssignItem (ident >> jsxAssignOp >> termParser)

@[jsxAttrVal_parser] def attrValStr : Parser := leading_parser strLit
@[jsxAttrVal_parser] def attrValAssign : Parser := leading_parser
  "{" >> atomic (ident >> jsxAssignOp) >> termParser >>
  many (atomic (", " >> jsxAssignItem)) >>
  optional (atomic (", " >> nonReservedSymbol "send" (includeIdent := true)) >> termParser) >> "}"
@[jsxAttrVal_parser] def attrValExpr : Parser := leading_parser "{" >> categoryParser `jsxExpr 0 >> "}"

syntax (name := attrNamed)  jsxName ("=" jsxAttrVal)? : jsxAttr
syntax (name := attrSplice) "{" jsxExpr "}" : jsxAttr

-- Ordered `<|>` (not a syntax category) so `jsxText` runs before tokenizing non-token chars like `•`.
syntax jsxChild := jsxText <|> ("{" jsxExpr "}") <|> jsxElement

syntax (name := jsxFragment)  atomic("<" ">") jsxChild* "</" ">" : jsxElement
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
  ["value", "placeholder", "name", "href", "src", "action", "alt", "title", "style", "key",
   "role", "onClick", "onInput", "onChange", "onCheck", "onKeydown",
   "onKeyup", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown",
   "onMouseUp", "disabled", "required", "checked", "readOnly"]

private def flagAttrs : List String := ["disabled", "required", "checked", "readOnly"]

private def attrHelper? (n : String) : Option Name :=
  if n == "class" then some (Name.mkStr2 "Qed" "cls")
  else if n == "type" then some (Name.mkStr2 "Qed" "type'")
  else if helperAttrs.contains n then some (Name.mkStr2 "Qed" n)
  else none

private def childCtxOfRootTag (tag : String) : HtmlCtx :=
  match stepHtmlCtx {} tag with
  | some ctx => ctx
  | none =>
      if tag == "optgroup" then { mode := .optgroup }
      else if tag == "option" then { mode := .option }
      else if tag == "colgroup" then { mode := .colgroup }
      else if tag == "thead" || tag == "tbody" || tag == "tfoot" then { mode := .tableSection }
      else if tag == "tr" then { mode := .tableRow }
      else {}

private def checkSafeAttrName (ref : Syntax) (name : String) : MacroM Unit := do
  unless isSafeAttrName name do
    if hasOnPrefix (name.toList.map asciiLowerChar) then
      Macro.throwErrorAt ref
        s!"inline event attribute `{name}` is forbidden; use Qed's typed event handlers (`onClick`, `onInput`, `on \"{name.drop 2}\" …`, …)"
    else if asciiLower name == "srcdoc" then
      Macro.throwErrorAt ref "`srcdoc` is forbidden in Qed views (iframe raw-HTML execution sink)"
    else
      Macro.throwErrorAt ref s!"invalid HTML attribute name `{name}`"

private def isJsxTextKid (k : Syntax) : Bool := k[0].getKind == `Qed.Jsx.jsxText

private def isJsxElementKid (k : Syntax) : Bool :=
  k[0].getKind == ``selfClosing || k[0].getKind == ``withChildren || k[0].getKind == ``jsxFragment

private def validateHtmlTag (ref : Syntax) (tag : String) (parentCtx? : Option (String × HtmlCtx)) :
    MacroM HtmlCtx := do
  if !isSafeTagName tag then
    Macro.throwErrorAt ref s!"invalid HTML tag name `<{tag}>`"
  if isForbiddenTag tag then
    Macro.throwErrorAt ref s!"<{tag}> is forbidden in Qed views (untrusted script/plugin execution sink)"
  match parentCtx? with
  | none => pure (childCtxOfRootTag tag)
  | some (parentTag, ctx) =>
      match stepHtmlCtx ctx tag with
      | some nextCtx => pure nextCtx
      | none =>
          Macro.throwErrorAt ref
            s!"invalid HTML5 nesting: <{tag}> is not allowed inside <{parentTag}> (browsers rewrite this tree during HTML parsing, causing hydration mismatch)"

private inductive KidPart where
  | single (t : Term)
  | many   (t : Term)

private def unpackPair? (t : Term) : Option (Term × Term) :=
  match t with
  | `(($a:term, $b:term)) => some (a, b)
  | _                     => none

private def isCheckboxAttrs (attrStxs : Array Syntax) : Bool :=
  attrStxs.any fun a =>
    a.getKind == ``attrNamed && tokenVal a[0] == "type" &&
      a[1].getNumArgs == 2 && a[1][1].getKind == ``attrValStr &&
      a[1][1][0].isStrLit? == some "checkbox"

mutual

partial def expandJsxIn (stx : Syntax) : MacroM Syntax := do
  if stx.getKind == ``jsxTerm then
    elementToTerm none stx[0]
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM expandJsxIn)
    | other                => return other

partial def expandJsxExpr (parentCtx? : Option (String × HtmlCtx)) (fallback : MacroM Term)
    (stx : Syntax) : MacroM (Term × Bool) := do
  if stx.getKind == ``jsxTermExpr then
    let raw := stx[0]
    if raw.getKind == ``jsxTerm && raw[0].getKind == ``jsxFragment then
      let listT ← childrenToTerm parentCtx? raw[0][1] raw[0][2].getArgs
      return (listT, true)
    if raw.getKind == ``jsxTerm then
      return (← elementToTerm parentCtx? raw[0], false)
    let exp ← expandJsxIn raw
    return (⟨exp⟩, isMapCall exp)
  else if stx.getKind == ``jsxIfLet then
    let pat   : Term := ⟨← expandJsxIn stx[2]⟩
    let scrut : Term := ⟨← expandJsxIn stx[4]⟩
    let (tT, isListT) ← expandJsxExpr parentCtx? fallback stx[6]
    if stx[7].getNumArgs == 2 then
      let (eT, isListE) ← expandJsxExpr parentCtx? fallback stx[7][1]
      return (← `(if let $pat := $scrut then $tT else $eT), isListT || isListE)
    else
      let defE ← if isListT then `([]) else fallback
      return (← `(if let $pat := $scrut then $tT else $defE), isListT)
  else if stx.getKind == ``jsxIf then
    let hasH := stx[1].getNumArgs > 0
    let cond : Term := ⟨← expandJsxIn stx[2]⟩
    let (tT, isListT) ← expandJsxExpr parentCtx? fallback stx[4]
    let (eT, isListE) ←
      if stx[5].getNumArgs == 2 then
        expandJsxExpr parentCtx? fallback stx[5][1]
      else do
        let defE ← if isListT then `([]) else fallback
        pure (defE, isListT)
    let res ← if hasH then
      let hId : Ident := ⟨stx[1][0][0]⟩
      `(if $hId:ident : $cond then $tT else $eT)
    else
      `(if $cond then $tT else $eT)
    return (res, isListT || isListE)
  else
    let exp ← expandJsxIn stx
    return (⟨exp⟩, isMapCall exp)

partial def expandAttrVal (valNode : Syntax) (fallback : MacroM Term) : MacroM Term := do
  let inner := valNode[1]
  if inner.getKind == ``attrValStr then
    return ⟨inner[0]⟩
  else if inner.getKind == ``attrValAssign then
    Macro.throwErrorAt inner
      "`field := …` / `+=` / `-=` mutates component state; it only has meaning inside a `component … view =>` body"
  else if inner.getKind == ``attrValExpr then
    return (← expandJsxExpr none fallback inner[1]).1
  else
    Macro.throwUnsupported

partial def attrsToTerms (rawAttrs : Array Syntax) (tag : String := "") : MacroM (Array Term) := do
  let isCheck := isCheckboxAttrs rawAttrs
  let textEvt := if tag == "select" then ``Qed.onChange else ``Qed.onInput
  let mut out : Array Term := #[]
  for stx in rawAttrs do
    if stx.getKind == ``attrSplice then
      let (t, _) ← expandJsxExpr none (`(Qed.Attr.empty)) stx[1]
      out := out.push t
    else
      let name := tokenVal stx[0]
      let valNode := stx[1]
      if name == "bind" then
        if valNode.getNumArgs == 0 then
          Macro.throwErrorAt stx "`bind` requires `{field}` (in a component) or `{(value, onEdit)}`"
        let vT ← expandAttrVal valNode (`(""))
        if vT.raw.isIdent then
          Macro.throwErrorAt vT
            s!"`bind=\{{vT.raw.getId}}` shorthands state binding inside a `component`; in an explicit `ui` view, pass `bind=\{({vT.raw.getId}, .edit)}`"
        match unpackPair? vT with
        | some (valE, setE) =>
            if isCheck then
              out := out.push (← `(Qed.checked $valE))
              out := out.push (← `(Qed.onCheck $setE))
            else
              out := out.push (← `(Qed.value $valE))
              out := out.push (← `($(mkCIdent textEvt) $setE))
        | none =>
            if isCheck then
              out := out.push (← `(Qed.checked ($vT).1))
              out := out.push (← `(Qed.onCheck ($vT).2))
            else
              out := out.push (← `(Qed.value ($vT).1))
              out := out.push (← `($(mkCIdent textEvt) ($vT).2))
      else if valNode.getNumArgs == 0 then
        if flagAttrs.contains name then
          out := out.push (← `($(mkCIdent (Name.mkStr2 "Qed" name)) true))
        else
          checkSafeAttrName stx[0] name
          if isUrlAttrName name then
            Macro.throwErrorAt stx[0] s!"URL attribute `{name}` requires a typed `Router` or `Url` value"
          out := out.push (← `(Qed.attr $(Syntax.mkStrLit name) ""))
      else
        let vT ← expandAttrVal valNode (`(""))
        match attrHelper? name with
        | some h => out := out.push (← `($(mkCIdent h) $vT))
        | none   =>
            checkSafeAttrName stx[0] name
            if isUrlAttrName name then
              out := out.push (← `(Qed.attr $(Syntax.mkStrLit name) (Qed.ToHref.toHref $vT)))
            else
              out := out.push (← `(Qed.attr $(Syntax.mkStrLit name) $vT))
  return out

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

partial def collectKidParts (parentCtx? : Option (String × HtmlCtx)) (opener : Syntax)
    (kids : Array Syntax) : MacroM (Array KidPart) := do
  let mut parts : Array KidPart := #[]
  let mut prev := opener
  for k in kids do
    if isJsxTextKid k then
      let s := normalizeText (trailingWs prev) (tokenVal k[0])
      if !s.isEmpty then
        if let some (ptag, pctx) := parentCtx? then
          if !validTextIn pctx s then
            Macro.throwErrorAt k[0]
              s!"invalid HTML5 text content inside <{ptag}>"
        parts := parts.push (.single ⟨Syntax.mkStrLit s⟩)
    else
      let gap := trailingWs prev
      if !gap.isEmpty && !gap.contains '\n' && (prev == opener || !isJsxTextKid prev) then
        let keepGap := match parentCtx? with
          | some (_, pctx) => validTextIn pctx " "
          | none           => true
        if keepGap then
          parts := parts.push (.single ⟨Syntax.mkStrLit " "⟩)
      if isJsxElementKid k then
        let el := k[0]
        if el.getKind == ``jsxFragment then
          parts := parts ++ (← collectKidParts parentCtx? el[1] el[2].getArgs)
        else
          parts := parts.push (.single (← elementToTerm parentCtx? el))
      else
        let (t, isList) ← expandJsxExpr parentCtx? (`(Qed.Html.text "")) k[0][1]
        if isMapCall t.raw then
          parts := parts.push (.many (← `(($t).toList)))
        else if isList then
          parts := parts.push (.many t)
        else
          parts := parts.push (.single t)
    prev := k
  return parts

partial def childrenToTerm (parentCtx? : Option (String × HtmlCtx)) (opener : Syntax)
    (kids : Array Syntax) : MacroM Term := do
  if kids.size == 1 && !isJsxTextKid kids[0]! && !isJsxElementKid kids[0]! then
    let (t, isList) ← expandJsxExpr parentCtx? (`(Qed.Html.text "")) kids[0]![0][1]
    if isMapCall t.raw then return ⟨← `(($t).toList)⟩
    else if isList then return t
    else return ⟨← `([$t])⟩
  let parts ← collectKidParts parentCtx? opener kids
  if !parts.any (fun | .many _ => true | .single _ => false) then
    let singles := parts.filterMap fun | .single t => some t | .many _ => none
    return ← `([$singles,*])
  let mut lists : Array Term := #[]
  let mut cur : Array Term := #[]
  for p in parts do
    match p with
    | .single t => cur := cur.push t
    | .many lt  =>
        if !cur.isEmpty then
          lists := lists.push (← `([$cur,*]))
          cur := #[]
        lists := lists.push lt
  if !cur.isEmpty then
    lists := lists.push (← `([$cur,*]))
  match lists.toList with
  | []      => `([])
  | l :: ls => ls.foldlM (init := l) fun acc x => `($acc ++ $x)

partial def componentToTerm (parentCtx? : Option (String × HtmlCtx)) (stx : Syntax) (tag : String)
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
      else expandAttrVal valNode (`(""))
    match name with
    | "key"     => key? := some v
    | "state"   => state? := some v
    | "initial" => initial? := some v
    | "onMsg"   => onMsg? := some v
    | "onEmit"  => onEmit? := some v
    | _         => props := props.push (a[0], name, v)
  let fids := props.map fun (_, n, _) => mkIdent (Name.mkSimple n)
  let vals := props.map fun (_, _, v) => v
  let propValues ← `(({ $[$fids:ident := $vals],* } : $(cId `Props)))
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
          match key? with
          | some k => `($(cId `renderTag) $propValues $route $st (toString $k))
          | none   => `($(cId `renderTag) $propValues $route $st)
  | none =>
      if onMsg?.isSome then
        Macro.throwErrorAt stx s!"<{tag}>: onMsg routes a parent-owned row; bind one with \
          state=\{…}, or receive outputs with onEmit=\{…}"
      -- Local component mounts emit `<div data-qed-local="..."></div>`; validate `div` in parentCtx!
      discard <| validateHtmlTag stx[1] "div" parentCtx?
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
      let mountT ← `($(mkIdent `Qed.Attr.localProps) $mountBase $propValues)
      `(Qed.el "div" [Qed.key $keyT, $mountT] [])

partial def elementToTerm (parentCtx? : Option (String × HtmlCtx)) (stx : Syntax) : MacroM Term := do
  if stx.getKind == ``jsxFragment then
    childrenToTerm parentCtx? stx[1] stx[2].getArgs
  else if stx.getKind == ``selfClosing then
    let tag := tokenVal stx[1]
    if !tag.isEmpty && tag.front.isUpper then
      return ← componentToTerm parentCtx? stx tag stx[2].getArgs #[]
    discard <| validateHtmlTag stx[1] tag parentCtx?
    let attrs ← attrsToTerms stx[2].getArgs tag
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] [])
  else if stx.getKind == ``withChildren then
    let tag := tokenVal stx[1]
    let closeTag := tokenVal stx[6]
    if tag != closeTag then
      Macro.throwErrorAt stx[6] s!"mismatched closing tag: expected </{tag}>, found </{closeTag}>"
    if !tag.isEmpty && tag.front.isUpper then
      return ← componentToTerm parentCtx? stx tag stx[2].getArgs stx[4].getArgs
    if isVoidTag tag then
      Macro.throwErrorAt stx s!"<{tag}> is an HTML5 void element and cannot have children; write it self-closing (<{tag} …/>)"
    let childCtx ← validateHtmlTag stx[1] tag parentCtx?
    let attrs ← attrsToTerms stx[2].getArgs tag
    let kids ← childrenToTerm (some (tag, childCtx)) stx[3] stx[4].getArgs
    `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] $kids)
  else
    Macro.throwUnsupported

end

@[macro jsxTerm] def expandJsxTerm : Macro := fun stx => do
  return (← elementToTerm none stx[0])

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
