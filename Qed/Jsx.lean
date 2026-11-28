import Qed.Diag
import Lean
import Qed.Lang
import Qed.Notation
import Qed.View.Core

namespace Qed.Jsx
open Lean Parser PrettyPrinter Qed.Lang

private def mkTokenParserFn (kind : Name) (pred : Char → Bool) (desc : String) : ParserFn := fun c s =>
  let startPos := s.pos; let s := takeWhile1Fn pred desc c s
  if s.hasError then s else mkNodeToken kind startPos true c s

def jsxText : Parser := { fn := mkTokenParserFn `Qed.Jsx.jsxText (fun ch => ch != '<' && ch != '{' && ch != '}') "JSX text" }
def jsxName : Parser := { fn := mkTokenParserFn `Qed.Jsx.jsxName (fun ch => ch.isAlphanum || ch == '-' || ch == '_' || ch == '.' || ch == ':') "tag or attribute name" }

declare_syntax_cat jsxElement
declare_syntax_cat jsxAttr
declare_syntax_cat jsxAttrVal

@[qedExpr_parser] def qedExprJsx : Parser := opaqueP (leadingNode `Qed.Jsx.qedExprJsx maxPrec (atomic (categoryParser `jsxElement 0)))
def jsxAssignOp   : Parser := Qed.Lang.qedAssignOp
def jsxAssignItem : Parser := node `Qed.Jsx.jsxAssignItem (ident >> jsxAssignOp >> categoryParser `qedExpr 0)

@[jsxAttrVal_parser] def attrValStr    : Parser := opaqueP (leadingNode `Qed.Jsx.attrValStr maxPrec strLit)
@[jsxAttrVal_parser] def attrValAssign : Parser := opaqueP (leadingNode `Qed.Jsx.attrValAssign maxPrec (
  "{" >> atomic (ident >> jsxAssignOp) >> categoryParser `qedExpr 0 >>
  many (atomic (";" >> jsxAssignItem)) >> optional (atomic (";" >> categoryParser `qedExpr 0)) >> "}"))
@[jsxAttrVal_parser] def attrValExpr   : Parser := opaqueP (leadingNode `Qed.Jsx.attrValExpr maxPrec (withPosition ("{" >> categoryParser `qedExpr 0 >> "}")))

@[jsxAttr_parser] def attrNamed  : Parser := opaqueP (leadingNode `Qed.Jsx.attrNamed maxPrec (jsxName >> optional ("=" >> categoryParser `jsxAttrVal 0)))
@[jsxAttr_parser] def attrSplice : Parser := opaqueP (leadingNode `Qed.Jsx.attrSplice maxPrec (withPosition ("{" >> categoryParser `qedExpr 0 >> "}")))
-- Ordered `<|>` (not a syntax category) so `jsxText` runs before tokenizing non-token chars like `•`.
def jsxChild : Parser := node `Qed.Jsx.jsxChild (jsxText <|> group (withPosition ("{" >> categoryParser `qedExpr 0 >> "}")) <|> categoryParser `jsxElement 0)
@[jsxElement_parser] def jsxFragment  : Parser := opaqueP (leadingNode `Qed.Jsx.jsxFragment maxPrec (atomic ("<" >> ">") >> many jsxChild >> "</" >> ">"))
@[jsxElement_parser] def selfClosing  : Parser := opaqueP (leadingNode `Qed.Jsx.selfClosing maxPrec ("<" >> jsxName >> many (categoryParser `jsxAttr 0) >> "/>"))
@[jsxElement_parser] def withChildren : Parser := opaqueP (leadingNode `Qed.Jsx.withChildren maxPrec ("<" >> jsxName >> many (categoryParser `jsxAttr 0) >> ">" >> many jsxChild >> "</" >> jsxName >> ">"))
@[term_parser] def jsxTerm : Parser := opaqueP (leadingNode `Qed.Jsx.jsxTerm maxPrec (atomic (categoryParser `jsxElement 0)))
syntax qedCompProp := str "=" term
syntax (name := qedCompTerm) "qedComp%" str str num "[" qedCompProp,* "]" term : term
syntax (name := qedCheckUrlValTerm) "qedCheckUrlVal%" str term:max : term

open Lean Meta Elab Term in
@[noinline, term_elab qedCheckUrlValTerm] def elabQedCheckUrlVal : TermElab := fun stx expectedType? => do
  let attrName := (⟨stx.getArg 1⟩ : TSyntax `str).getString
  let e ← elabTerm (stx.getArg 2) expectedType?; synthesizeSyntheticMVars (postpone := .yes)
  let ty ← instantiateMVars (← inferType e)
  unless ty.hasMVar do
    if (← trySynthInstance (← mkAppM ``Qed.ToHref #[ty])) matches .none then
      throwErrorAt (stx.getArg 2) m!"URL attribute `{attrName}` requires a typed `Router` route or `Url`, got `{← Meta.ppExpr ty}` (raw strings are disallowed to prevent XSS).\nPass a route value (e.g. `{attrName}=\{Route.home}`), a validated literal (`{attrName}=\{url(\"/path\")}`), or parse dynamic strings with `Url.parse?`."
  return e

def tokenVal : Syntax → String | .node _ _ #[.atom _ v] | .atom _ v => v | _ => ""
private def trailingWs (stx : Syntax) : String := match stx.getTailInfo with | .original _ _ trail _ => trail.toString | _ => ""

private def normalizeText (lead raw : String) : String :=
  let sep (run : List Char) (edge : Bool) : List Char := if run.isEmpty || (edge && run.contains '\n') then [] else [' ']
  let rec go : List Char → List Char → List Char → Bool → List Char
    | [], acc, run, _ => acc ++ sep run true
    | ch :: rest, acc, run, atStart => if ch.isWhitespace then go rest acc (ch :: run) atStart else go rest (acc ++ sep run atStart ++ [ch]) [] false
  String.ofList (go (lead ++ raw).toList [] [] true)

private def helperAttrs : List String :=
  "value placeholder name href src action alt title style key role ariaRole onClick onInput onChange onCheck onKeydown onKeyup onSubmit onBlur onFocus onDoubleClick onMouseDown onMouseUp disabled required checked readOnly".splitOn " "
private def flagAttrs : List String := ["disabled", "required", "checked", "readOnly"]
private def attrHelper? : String → Option Name
  | "class" => some `Qed.cls | "type" => some `Qed.type'
  | n => if helperAttrs.contains n then some (Name.mkStr2 "Qed" n) else none

def childCtxOfRootTag (tag : String) : HtmlCtx := match stepHtmlCtx {} tag with
  | some ctx => ctx
  | none => match tag with
      | "optgroup" => { mode := .optgroup } | "option" => { mode := .option } | "colgroup" => { mode := .colgroup }
      | "tr" => { mode := .tableRow } | "thead" | "tbody" | "tfoot" => { mode := .tableSection } | _ => {}

def ctxOfPath (path : String) : Option (String × HtmlCtx) := match path.splitOn "/" with
  | [] | [""] => none
  | root :: rest => rest.foldlM (fun (_, c) t => (t, ·) <$> stepHtmlCtx c t) (root, childCtxOfRootTag root)

private def checkSafeAttrName (ref : Syntax) (name : String) : MacroM Unit := do
  unless isSafeAttrName name do
    if hasOnPrefix (name.toList.map asciiLowerChar) then
      Macro.throwErrorAt ref s!"inline event attribute `{name}` is forbidden; use Qed's typed event handlers (`onClick`, `onInput`, `on \"{name.drop 2}\" …`, …)"
    else if asciiLower name == "srcdoc" then Macro.throwErrorAt ref "`srcdoc` is forbidden in Qed views (iframe raw-HTML execution sink)"
    else Macro.throwErrorAt ref s!"invalid HTML attribute name `{name}`: attribute names must be non-empty ASCII without whitespace, quotes, `<`, `>`, `/`, or `=`"

private def isJsxTextKid (k : Syntax) : Bool := (k.getArg 0).getKind == `Qed.Jsx.jsxText
private def isJsxElementKid (k : Syntax) : Bool := [``selfClosing, ``withChildren, ``jsxFragment].contains (k.getArg 0).getKind

private def validateHtmlTag (ref : Syntax) (tag : String) (parentCtx? : Option (String × HtmlCtx)) : MacroM HtmlCtx := do
  if !isSafeTagName tag then Macro.throwErrorAt ref s!"invalid HTML tag name `<{tag}>`: HTML tags must start with a lowercase ASCII letter and contain only letters, digits, or `-`"
  if isForbiddenTag tag then Macro.throwErrorAt ref s!"<{tag}> is forbidden in Qed views (untrusted script/plugin execution sink)"
  match parentCtx? with
  | none => pure (childCtxOfRootTag tag)
  | some (parentTag, ctx) => match stepHtmlCtx ctx tag with
      | some nextCtx => pure nextCtx
      | none => Macro.throwErrorAt ref s!"invalid HTML5 nesting: <{tag}> is not allowed inside <{parentTag}> (browsers rewrite this tree during HTML parsing, causing hydration mismatch)"

private inductive KidPart where | single (t : Term) | many (t : Term) deriving Nonempty

private def isCheckboxAttrs (attrStxs : Array Syntax) : Bool := attrStxs.any fun a =>
  a.getKind == ``attrNamed && tokenVal (a.getArg 0) == "type" && (a.getArg 1).getNumArgs == 2 &&
  ((a.getArg 1).getArg 1).getKind == ``attrValStr && (((a.getArg 1).getArg 1).getArg 0).isStrLit? == some "checkbox"

@[noinline] private def mkBindAttrsPure (isCheck : Bool) (textEvt : Name) (vT : Term) : PureQuotM (Array Term) := do
  let (valE, setE) ← match vT with | `(($a:term, $b:term)) => pure (a, b) | _ => pure (← `(($vT).1), ← `(($vT).2))
  pure #[← `($(mkCIdent (if isCheck then ``Qed.checked else ``Qed.value)) $valE), ← `($(mkCIdent (if isCheck then ``Qed.onCheck else textEvt)) $setE)]

@[noinline] private def mkKidListsPure (parts : Array KidPart) : PureQuotM Term := do
  let (lists, cur) ← Lang.foldlPQ parts (#[], #[]) fun (ls, cur) p => match p with
    | .single t => pure (ls, cur.push t)
    | .many lt  => if cur.isEmpty then pure (ls.push lt, #[]) else do pure ((ls.push (← `([$cur,*]))).push lt, #[])
  let lists ← if cur.isEmpty then pure lists else do pure (lists.push (← `([$cur,*])))
  if lists.isEmpty then `([]) else Lang.foldlPQ (lists.extract 1 lists.size) lists[0]! fun acc x => `($acc ++ $x)

@[noinline] private def mkAwaitCallPure (ofT singleKid : Term) (asId? errId? : Option Ident) (attrs : Std.HashMap String Term) : PureQuotM Term := do
  let readyT ← match asId? with | some b => `(fun $b:ident => $singleKid) | none => pure singleKid
  let failT ← match attrs["failed"]?, errId? with
    | none, _ => `((fun (e : String) => Qed.Html.text e))
    | some f, some b => `(fun ($b:ident : String) => $f)
    | some f, none =>
        let isEl := f.raw.getKind == ``qedCompTerm || (f.raw.getKind == ``Lean.Parser.Term.app && ((f.raw.getArg 0).getId == ``Qed.el || (f.raw.getArg 0).getKind == ``qedCompTerm))
        if isEl then `((fun (_ : String) => $f)) else pure f
  `($(mkIdent `Qed.Resource.awaitView) $ofT $readyT $(← attrs["loading"]?.getDM `(Qed.Html.text "Loading…")) $failT $(← attrs["idle"]?.getDM `(Qed.Html.empty)))

private def isMapCall (stx : Syntax) : Bool :=
  let s := if stx.getKind == ``Lean.Parser.Term.paren && stx.getNumArgs == 3 then stx.getArg 1 else stx
  s.getKind == ``Lean.Parser.Term.app && s.getNumArgs == 2 && (s.getArg 1).getNumArgs == 1 &&
  match s.getArg 0 with | .ident _ _ n _ => (match n.eraseMacroScopes with | .str _ "map" => true | _ => false) | _ => false

private partial def isListJsxExpr (stx : Syntax) : Bool :=
  match stx.getKind with
  | ``qedExprJsx => (stx.getArg 0).getKind == ``jsxFragment
  | ``Qed.Lang.qedRawTerm => isMapCall (stx.getArg 1)
  | ``Qed.Lang.qedParen => (stx.getArg 1).getSepArgs.size == 1 && isListJsxExpr (stx.getArg 1).getSepArgs[0]!
  | ``Qed.Lang.qedIdent => (stx.getArg 0).getId.eraseMacroScopes == `children
  | ``Qed.Lang.qedTernary => isListJsxExpr (stx.getArg 0) || (extractOptElseExpr? (stx.getArg 3)).any isListJsxExpr
  | ``Qed.Lang.qedExprLet => isListJsxExpr (stx.getArg 6)
  | ``Qed.Lang.qedExprIf => isListJsxExpr (stx.getArg 3) || (desugarExprElifs? (stx.getArg 4).getArgs (stx.getArg 5)).any isListJsxExpr
  | ``Qed.Lang.qedExprIfLet => isListJsxExpr (stx.getArg 6) || (desugarExprElifs? (stx.getArg 7).getArgs (stx.getArg 8)).any isListJsxExpr
  | ``Qed.Lang.qedExprMatch => (stx.getArg 3).getArgs.any fun c => isListJsxExpr (c.getArg 3)
  | ``Qed.Lang.qedCall => (stx.getArg 0).getKind == ``Qed.Lang.qedProj && ((stx.getArg 0).getArg 2).isIdent && ((stx.getArg 0).getArg 2).getId.eraseMacroScopes == `map
  | ``Qed.Lang.qedExprFor => true
  | _ => false

mutual
@[noinline] partial def expandJsxExpr (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (fallback : MacroM Term) (stx : Syntax) : MacroM (Term × Bool) := do
  let hooks : LowerHooks MacroM := { LowerHooks.mkDefault Macro.throwErrorAt with
    lowerJsx := fun j _ => do
      if j.getKind == ``qedExprJsx then elementToTerm pPath parentCtx? (j.getArg 0)
      else let sn := stxSnippet j; Macro.throwErrorAt j s!"unsupported JSX expression{if sn.isEmpty then s!"({j.getKind})" else s!" `{sn}`"}"
    lowerType := fun s => return (← lowerQedType s false).1, lowerPat := lowerQedPat, allowOptElse := true
    optElseFallback := fun thenStx thenT => if isListJsxExpr thenStx || isMapCall thenT.raw then `([]) else fallback
    wrapForMap := fun bodyStx bodyT mapT => if isListJsxExpr bodyStx || isMapCall bodyT.raw then `(($mapT).flatten) else pure mapT }
  let exp ← lowerQedExpr hooks .val stx
  return (exp, isListJsxExpr stx || isMapCall exp.raw)

@[noinline] partial def expandAttrVal (valNode : Syntax) (fallback : MacroM Term) : MacroM Term := do
  let inner := valNode.getArg 1
  match inner.getKind with
  | ``attrValStr => pure ⟨inner.getArg 0⟩
  | ``attrValAssign => Macro.throwErrorAt inner "`field = …` / `+=` / `-=` mutates component state; it only has meaning inside a `component … view:` body"
  | ``attrValExpr => return (← expandJsxExpr "" none fallback (inner.getArg 1)).1
  | _ => Macro.throwUnsupported

@[noinline] private partial def expandOneAttr (isCheck : Bool) (textEvt : Name) (stx : Syntax) : MacroM (Array Term) := withRef stx do
  if stx.getKind == ``attrSplice then return #[(← expandJsxExpr "" none (`(Qed.Attr.empty)) (stx.getArg 1)).1]
  let (name, valNode) := (tokenVal (stx.getArg 0), stx.getArg 1); let isUrl := isUrlAttrName name
  if name == "bind" then
    if valNode.getNumArgs == 0 then Macro.throwErrorAt stx "`bind` requires `{field}` (in a component) or `{(value, onEdit)}`"
    let vT ← expandAttrVal valNode (`(""))
    if vT.raw.isIdent then Macro.throwErrorAt vT s!"`bind=\{{vT.raw.getId}}` shorthands state binding inside a `component`; outside a `component` view, pass `bind=\{({vT.raw.getId}, onEdit)}`"
    return ← runPQMacro (mkBindAttrsPure isCheck textEvt vT)
  if valNode.getNumArgs == 0 then
    if flagAttrs.contains name then return #[← runPQMacro `($(mkCIdent (Name.mkStr2 "Qed" name)) true)]
    checkSafeAttrName (stx.getArg 0) name
    if isUrl then Macro.throwErrorAt (stx.getArg 0) s!"URL attribute `{name}` requires a value (a `Router` route or `Url`, e.g. `{name}=\{Route.home}` or `{name}=\{url(\"/path\")}`)"
    return #[← runPQMacro `(Qed.attr $(Syntax.mkStrLit name) "")]
  if isUrl && (valNode.getArg 1).getKind == ``attrValStr then
    let raw := (⟨(valNode.getArg 1).getArg 0⟩ : TSyntax `str).getString
    Macro.throwErrorAt ((valNode.getArg 1).getArg 0) s!"URL attribute `{name}` cannot take raw string literal `\"{raw}\"` (raw strings are disallowed to prevent XSS and broken links).\nPass a typed `Router` route or a compile-time checked literal: `{name}=\{url(\"{raw}\")}`."
  let vT ← expandAttrVal valNode (`("")); let h? := attrHelper? name
  if h?.isNone then checkSafeAttrName (stx.getArg 0) name
  return #[← runPQMacro do
    let vChecked ← if isUrl then withRef (valNode.getArg 1) `(qedCheckUrlVal% $(Syntax.mkStrLit name) ($vT)) else pure vT
    match h? with
    | some h => `($(mkCIdent h) $vChecked)
    | none => if isUrl then `(Qed.attr $(Syntax.mkStrLit name) (Qed.ToHref.toHref $vChecked)) else `(Qed.attr $(Syntax.mkStrLit name) $vT)]

@[noinline] partial def attrsToTerms (rawAttrs : Array Syntax) (tag : String := "") : MacroM (Array Term) := do
  let (isCheck, textEvt) := (isCheckboxAttrs rawAttrs, if tag == "select" then ``Qed.onChange else ``Qed.onInput)
  return (← mapArrM rawAttrs (expandOneAttr isCheck textEvt)).flatten

private partial def expandKidExpr (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (exprStx : Syntax) : MacroM KidPart := do
  let (t, isList) ← expandJsxExpr pPath parentCtx? (`(Qed.Html.text "")) exprStx
  if isMapCall t.raw then return .many (← runPQMacro `(($t).toList)) else return if isList then .many t else .single t

@[noinline] partial def collectKidParts (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (opener : Syntax) (kids : Array Syntax) : MacroM (Array KidPart) := do
  let mut parts : Array KidPart := #[]; let mut prev := opener
  for k in kids do
    if isJsxTextKid k then
      let s := normalizeText (trailingWs prev) (tokenVal (k.getArg 0))
      if !s.isEmpty then
        if let some (ptag, pctx) := parentCtx? then
          if !validTextIn pctx s then
            Macro.throwErrorAt (k.getArg 0) s!"invalid HTML5 text content `\"{s}\"` inside <{ptag}>: <{ptag}> does not allow raw text children (browsers hoist text outside <{ptag}> during HTML parsing, causing hydration mismatch)"
        parts := parts.push (.single ⟨Syntax.mkStrLit s⟩)
    else
      let gap := trailingWs prev
      if !gap.isEmpty && !gap.contains '\n' && (prev == opener || !isJsxTextKid prev) && (parentCtx?.map (fun (_, c) => validTextIn c " ") |>.getD true) then
        parts := parts.push (.single ⟨Syntax.mkStrLit " "⟩)
      if isJsxElementKid k then
        let el := k.getArg 0
        if el.getKind == ``jsxFragment then parts := parts ++ (← collectKidParts pPath parentCtx? (el.getArg 1) (el.getArg 2).getArgs)
        else parts := parts.push (.single (← elementToTerm pPath parentCtx? el))
      else parts := parts.push (← expandKidExpr pPath parentCtx? ((k.getArg 0).getArg 1))
    prev := k
  return parts

@[noinline] partial def childrenToTerm (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (opener : Syntax) (kids : Array Syntax) : MacroM Term := do
  if kids.size == 1 && !isJsxTextKid kids[0]! && !isJsxElementKid kids[0]! then
    match ← expandKidExpr pPath parentCtx? kids[0]![0][1] with | .many t => return t | .single t => return ← runPQMacro `([$t])
  runPQMacro (mkKidListsPure (← collectKidParts pPath parentCtx? opener kids))

@[noinline] partial def expandAwaitTag (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (stx opener : Syntax) (attrStxs kids : Array Syntax) : MacroM Term := withRef stx do
  let valid := ["of", "as", "err", "loading", "failed", "idle"]
  let parseVar (attrNm : String) (v : Term) : MacroM Ident :=
    if v.raw.isIdent then pure ⟨v.raw⟩ else if let some s := v.raw.isStrLit? then pure (mkIdentFrom v (Name.mkSimple s))
    else Macro.throwErrorAt v s!"`{attrNm}` expects a variable name (`{attrNm}=\{val}` or `{attrNm}=\"val\"`)"
  let mut attrs : Std.HashMap String Term := {}
  for a in attrStxs do
    if a.getKind == ``attrSplice then Macro.throwErrorAt a "<Await> does not accept spliced HTML attributes"
    let name := tokenVal (a.getArg 0)
    unless valid.contains name do Macro.throwErrorAt (a.getArg 0) s!"<Await>: unknown attribute `{name}`{Qed.Diag.didYouMean name valid} (expected: {String.intercalate ", " valid})"
    if (a.getArg 1).getNumArgs == 0 then Macro.throwErrorAt a s!"<Await>: `{name}` requires a value"
    attrs := attrs.insert name (← expandAttrVal (a.getArg 1) (`("")))
  let some ofT := attrs["of"]? | Macro.throwErrorAt stx "<Await> requires `of={resource}`"
  let (asId?, errId?) := (← attrs["as"]?.mapM (parseVar "as"), ← attrs["err"]?.mapM (parseVar "err"))
  if errId?.isSome && !attrs.contains "failed" then Macro.throwErrorAt stx "<Await>: `err={…}` requires a `failed={…}` view"
  let #[.single singleKid] ← collectKidParts pPath parentCtx? opener kids | Macro.throwErrorAt stx "<Await> expects a single child element (with `as={val}`) or a lambda `{val => ...}`"
  runPQMacro (mkAwaitCallPure ofT singleKid asId? errId? attrs)

@[noinline] partial def componentToTerm (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (stx opener : Syntax) (tag : String) (attrStxs kids : Array Syntax) : MacroM Term := withRef stx do
  if tag == "Await" then return ← expandAwaitTag pPath parentCtx? stx opener attrStxs kids
  let propVals ← mapArrM attrStxs fun a => do
    if a.getKind == ``attrSplice then
      Macro.throwErrorAt a s!"<{tag}>: component tags do not accept spliced attributes (`\{...}`); pass named props (`prop=\{...}`) instead, or apply styles/attributes on an HTML element inside `{tag}`"
    let v : Term ← if (a.getArg 1).getNumArgs == 0 then runPQMacro `(Bool.true) else expandAttrVal (a.getArg 1) (`(""))
    pure (Syntax.mkStrLit (tokenVal (a.getArg 0)) (info := (a.getArg 0).getHeadInfo), v)
  let kidsT ← if kids.isEmpty then runPQMacro `([]) else childrenToTerm "" none opener kids
  runPQMacro do
    let compProps ← Lang.mapPQ propVals fun (nameLit, v) => `(qedCompProp| $nameLit:str = $v)
    `(qedComp% $(Syntax.mkStrLit tag) $(Syntax.mkStrLit pPath) $(Syntax.mkNumLit (toString ((stx.getPos?.map (·.byteIdx)).getD 0))) [$[$compProps],*] $kidsT)

@[noinline] partial def elementToTerm (pPath : String) (parentCtx? : Option (String × HtmlCtx)) (stx : Syntax) : MacroM Term := withRef stx do
  if stx.getKind == ``jsxFragment then childrenToTerm pPath parentCtx? (stx.getArg 1) (stx.getArg 2).getArgs
  else if stx.getKind == ``selfClosing || stx.getKind == ``withChildren then
    let hasKids := stx.getKind == ``withChildren; let tag := tokenVal (stx.getArg 1)
    if hasKids then
      let closeTag := tokenVal (stx.getArg 6)
      if tag != closeTag then Macro.throwErrorAt (stx.getArg 6) s!"mismatched closing tag: expected </{tag}>, found </{closeTag}>"
    if !tag.isEmpty && tag.front.isUpper then
      return ← componentToTerm pPath parentCtx? stx (if hasKids then stx.getArg 3 else stx.getArg 1) tag (stx.getArg 2).getArgs (if hasKids then (stx.getArg 4).getArgs else #[])
    if hasKids && isVoidTag tag then Macro.throwErrorAt stx s!"<{tag}> is an HTML5 void element and cannot have children; write it self-closing (<{tag} …/>)"
    let childCtx ← validateHtmlTag (stx.getArg 1) tag parentCtx?
    let attrs ← attrsToTerms (stx.getArg 2).getArgs tag
    let kids ← if hasKids then childrenToTerm (if pPath.isEmpty then tag else pPath ++ "/" ++ tag) (some (tag, childCtx)) (stx.getArg 3) (stx.getArg 4).getArgs else runPQMacro `([])
    runPQMacro `(Qed.el $(Syntax.mkStrLit tag) [$attrs,*] $kids)
  else Macro.throwUnsupported
end

partial def expandJsxIn (stx : Syntax) : MacroM Syntax := do
  if stx.getKind == ``jsxTerm then elementToTerm "" none (stx.getArg 0)
  else match stx with | .node info kind args => return .node info kind (← mapArrM args expandJsxIn) | other => return other

@[macro jsxTerm] def expandJsxTerm : Macro := fun stx => do return (← elementToTerm "" none (stx.getArg 0))

@[term_parser] def qedUrlLit : Parser := opaqueP (leadingNode `Qed.Jsx.qedUrlLit maxPrec (atomic (kw "url" >> checkNoWsBefore "" >> "(") >> strLit >> ")"))
@[macro qedUrlLit] def expandQedUrlLit : Macro := fun stx => do
  let s : TSyntax `str := ⟨stx.getArg 2⟩
  if !Qed.isSafeUrl s.getString then
    Macro.throwErrorAt s s!"unsafe URL literal `{s.getString}`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters"
  runPQMacro `(Qed.Url.mk $s (by decide))

end Qed.Jsx
