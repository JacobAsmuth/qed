import Lean
import Qed.Diag
import Qed.Style.Core
import Qed.Style.Contrast

namespace Qed.StyleDsl
open Lean Parser Elab Command Term Meta

/-! ## Persistent Compile-Time CSS Registries -/

structure StyleMetaInfo where
  fullName   : Name
  items      : List Qed.Item
  usedTokens : List String
  extraRules : List String
  themes     : List Name := []
deriving Inhabited

initialize styleMetaRegistry :
    SimplePersistentEnvExtension StyleMetaInfo (NameMap StyleMetaInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

structure TokenMetaInfo where
  fullName   : Name
  cssName    : String
  kind       : String -- "color" | "len" | "num" | "font" | "time" | "any"
  themeName? : Option Name := none
  themeRule? : Option String := none
deriving Inhabited

initialize tokenMetaRegistry :
    SimplePersistentEnvExtension TokenMetaInfo (NameMap TokenMetaInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

structure KeyframesMetaInfo where
  fullName : Name
  kfName   : String
  rule     : String
deriving Inhabited

initialize keyframesMetaRegistry :
    SimplePersistentEnvExtension KeyframesMetaInfo (NameMap KeyframesMetaInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

structure ThemeMetaInfo where
  fullName      : Name
  styleConst    : Name
  themeConst    : Name
  renderedRule  : String
  definedTokens : List String
  darkTokens    : List String
deriving Inhabited

initialize themeMetaRegistry :
    SimplePersistentEnvExtension ThemeMetaInfo (NameMap ThemeMetaInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

/-! ## Custom Non-Polluting CSS Line Parsers -/

private def scanCssLine (input : String) : Nat → String.Pos.Raw → Bool → Char → Bool → String.Pos.Raw
  | 0, pos, _, _, _ => pos
  | fuel + 1, pos, inStr, quote, escaped =>
      if pos.atEnd input then pos
      else
        let ch := pos.get input
        if ch == '\n' || ch == '\r' then pos
        else if inStr then
          if escaped then scanCssLine input fuel (pos.next input) true quote false
          else if ch == '\\' then scanCssLine input fuel (pos.next input) true quote true
          else if ch == quote then scanCssLine input fuel (pos.next input) false quote false
          else scanCssLine input fuel (pos.next input) true quote false
        else if ch == '"' || ch == '\'' then
          scanCssLine input fuel (pos.next input) true ch false
        else if ch == '-' && !((pos.next input).atEnd input) && (pos.next input).get input == '-' then
          let after1 := pos.next input
          let after2 := after1.next input
          let isComment := after2.atEnd input || (after2.get input).isWhitespace
          if isComment then pos
          else scanCssLine input fuel after2 false quote false
        else
          scanCssLine input fuel (pos.next input) false quote false

private def skipToEol (input : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, pos => pos
  | fuel + 1, pos =>
      if pos.atEnd input then pos
      else
        let ch := pos.get input
        if ch == '\n' || ch == '\r' then pos
        else skipToEol input fuel (pos.next input)

private def takeRestOfLineFn (kind : Name) (mustEndWithColon : Bool) : ParserFn := fun c s =>
  let input := c.inputString
  let startPos := s.pos
  let fuel := input.utf8ByteSize - startPos.byteIdx + 1
  let endPos := scanCssLine input fuel startPos false '"' false
  let raw := String.Pos.Raw.extract input startPos endPos
  let trimmed := raw.trimmed
  if trimmed.isEmpty then
    s.mkError "CSS declaration or nested block"
  else
    let endsColon := trimmed.endsWith ":"
    if endsColon != mustEndWithColon then
      s.mkError (if mustEndWithColon then "CSS block header ending with ':'" else "CSS declaration")
    else
      let stopPos := skipToEol input (input.utf8ByteSize - endPos.byteIdx + 1) endPos
      let s1 := s.setPos endPos
      let s2 := mkNodeToken kind startPos true c s1
      let s3 := s2.setPos stopPos
      whitespace c s3

def cssBlockHeader : Parser where
  fn := takeRestOfLineFn `Qed.StyleDsl.cssBlockHeader true

def cssDeclLine : Parser where
  fn := takeRestOfLineFn `Qed.StyleDsl.cssDeclLine false

@[combinator_formatter Qed.StyleDsl.cssBlockHeader]
def cssBlockHeader.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom `Qed.StyleDsl.cssBlockHeader
@[combinator_parenthesizer Qed.StyleDsl.cssBlockHeader]
def cssBlockHeader.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter Qed.StyleDsl.cssDeclLine]
def cssDeclLine.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom `Qed.StyleDsl.cssDeclLine
@[combinator_parenthesizer Qed.StyleDsl.cssDeclLine]
def cssDeclLine.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

declare_syntax_cat cssBlockItem

@[cssBlockItem_parser] def cssNestedBlock : Parser := leading_parser
  withPosition (cssBlockHeader >> many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[cssBlockItem_parser] def cssSimpleDecl : Parser := leading_parser
  cssDeclLine

def styleExtendsClause : Parser := leading_parser
  atomic (symbol "extends") >> sepBy1 Parser.ident ","

def styleStrictClause : Parser := leading_parser
  atomic (identEq `strict_tokens)

@[command_parser] def styleCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "style " >>
    Parser.ident >>
    optional styleExtendsClause >>
    optional styleStrictClause >>
    ":" >>
    many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[command_parser] def keyframesCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "keyframes " >>
    Parser.ident >> ":" >>
    many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[command_parser] def themeCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "theme " >>
    Parser.ident >> ":" >>
    many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[command_parser] def verifyThemeCmd : Parser := leading_parser
  "verify_theme " >> Parser.ident >> symbol "for" >> termParser

/-! ## CSS Property & Value Validation Engine -/

private def knownCssProps : List String := [
  -- Box & Layout
  "display", "position", "inset", "top", "right", "bottom", "left", "z-index",
  "box-sizing", "width", "height", "min-width", "max-width", "min-height", "max-height",
  "aspect-ratio", "overflow", "overflow-x", "overflow-y", "visibility", "opacity",
  "isolation", "float", "clear", "content", "vertical-align", "object-fit", "object-position",
  -- Spacing
  "margin", "margin-top", "margin-right", "margin-bottom", "margin-left",
  "margin-inline", "margin-block", "margin-inline-start", "margin-inline-end",
  "padding", "padding-top", "padding-right", "padding-bottom", "padding-left",
  "padding-inline", "padding-block", "padding-inline-start", "padding-inline-end",
  -- Flexbox & Grid
  "flex", "flex-direction", "flex-wrap", "flex-flow", "flex-grow", "flex-shrink", "flex-basis",
  "justify-content", "justify-items", "justify-self",
  "align-items", "align-content", "align-self", "place-items", "place-content", "place-self",
  "order", "gap", "row-gap", "column-gap",
  "grid", "grid-template", "grid-template-columns", "grid-template-rows", "grid-template-areas",
  "grid-column", "grid-row", "grid-area", "grid-auto-flow", "grid-auto-columns", "grid-auto-rows",
  -- Typography
  "color", "font", "font-family", "font-size", "font-weight", "font-style", "font-variant",
  "line-height", "letter-spacing", "word-spacing", "text-align", "text-decoration",
  "text-decoration-color", "text-decoration-thickness", "text-underline-offset",
  "text-transform", "text-overflow", "text-indent", "text-shadow", "white-space",
  "word-break", "overflow-wrap", "hyphens", "tab-size",
  -- Backgrounds, Borders & Effects
  "background", "background-color", "background-image", "background-position",
  "background-size", "background-repeat", "background-clip", "background-origin",
  "border", "border-top", "border-right", "border-bottom", "border-left",
  "border-width", "border-style", "border-color",
  "border-top-width", "border-right-width", "border-bottom-width", "border-left-width",
  "border-top-color", "border-right-color", "border-bottom-color", "border-left-color",
  "border-radius", "border-top-left-radius", "border-top-right-radius",
  "border-bottom-left-radius", "border-bottom-right-radius", "border-collapse", "border-spacing",
  "outline", "outline-width", "outline-style", "outline-color", "outline-offset",
  "box-shadow", "filter", "backdrop-filter", "mix-blend-mode", "clip-path", "mask", "mask-image",
  -- Transform, Transition & Animation
  "transform", "transform-origin", "perspective", "rotate", "scale", "translate",
  "transition", "transition-property", "transition-duration", "transition-timing-function", "transition-delay",
  "animation", "animation-name", "animation-duration", "animation-timing-function",
  "animation-delay", "animation-iteration-count", "animation-direction", "animation-fill-mode",
  "animation-play-state", "will-change",
  -- Interactivity, Lists, Tables, SVG & Scroll
  "cursor", "pointer-events", "user-select", "resize", "appearance", "touch-action",
  "accent-color", "caret-color", "list-style", "list-style-type", "list-style-position",
  "table-layout", "caption-side", "empty-cells",
  "fill", "stroke", "stroke-width", "stroke-linecap", "stroke-linejoin", "stroke-dasharray",
  "scroll-behavior", "scroll-margin", "scroll-padding", "scroll-snap-type", "scroll-snap-align",
  "overscroll-behavior", "container-type", "container-name", "container"
]

private def commonGlobalKw : List String := ["inherit", "initial", "unset", "revert", "revert-layer"]

private def enumPropValues : String → Option (List String)
  | "display"         => some ["flex", "inline-flex", "grid", "inline-grid", "block", "inline", "inline-block", "table", "table-row", "table-cell", "flow-root", "contents", "none", "list-item"]
  | "position"        => some ["static", "relative", "absolute", "fixed", "sticky"]
  | "text-align"      => some ["left", "right", "center", "justify", "start", "end"]
  | "flex-direction"  => some ["row", "column", "row-reverse", "column-reverse"]
  | "flex-wrap"       => some ["nowrap", "wrap", "wrap-reverse"]
  | "justify-content" => some ["flex-start", "flex-end", "start", "end", "center", "space-between", "space-around", "space-evenly", "stretch", "normal"]
  | "align-items"     => some ["flex-start", "flex-end", "start", "end", "center", "stretch", "baseline", "normal"]
  | "align-self"      => some ["auto", "flex-start", "flex-end", "start", "end", "center", "stretch", "baseline"]
  | "justify-self"    => some ["auto", "start", "end", "center", "stretch"]
  | "box-sizing"      => some ["content-box", "border-box"]
  | "cursor"          => some ["auto", "default", "pointer", "not-allowed", "text", "move", "grab", "grabbing", "wait", "progress", "help", "crosshair", "zoom-in", "zoom-out", "col-resize", "row-resize", "ew-resize", "ns-resize", "none"]
  | "overflow" | "overflow-x" | "overflow-y" => some ["visible", "hidden", "clip", "scroll", "auto"]
  | "white-space"     => some ["normal", "nowrap", "pre", "pre-wrap", "pre-line", "break-spaces"]
  | "object-fit"      => some ["fill", "contain", "cover", "none", "scale-down"]
  | "pointer-events"  => some ["auto", "none", "all"]
  | "user-select"     => some ["auto", "none", "text", "all", "contain"]
  | "visibility"      => some ["visible", "hidden", "collapse"]
  | "font-style"      => some ["normal", "italic", "oblique"]
  | "text-transform"  => some ["none", "capitalize", "uppercase", "lowercase", "full-width"]
  | "text-overflow"   => some ["clip", "ellipsis"]
  | "word-break"      => some ["normal", "break-all", "keep-all", "break-word"]
  | "scroll-behavior" => some ["auto", "smooth"]
  | "border-style"    => some ["solid", "dashed", "dotted", "double", "groove", "ridge", "inset", "outset", "none", "hidden"]
  | _                 => none

private def colorProps : List String := [
  "color", "background-color", "border-color",
  "border-top-color", "border-right-color", "border-bottom-color", "border-left-color",
  "outline-color", "text-decoration-color", "fill", "stroke", "accent-color", "caret-color"
]

private def lengthProps : List String := [
  "width", "height", "min-width", "max-width", "min-height", "max-height",
  "padding", "padding-top", "padding-right", "padding-bottom", "padding-left",
  "padding-inline", "padding-block", "padding-inline-start", "padding-inline-end",
  "margin", "margin-top", "margin-right", "margin-bottom", "margin-left",
  "margin-inline", "margin-block", "margin-inline-start", "margin-inline-end",
  "inset", "top", "right", "bottom", "left", "gap", "row-gap", "column-gap",
  "font-size", "border-radius", "border-width", "outline-offset", "letter-spacing", "flex-basis"
]

private def borderShorthandProps : List String := [
  "border", "border-top", "border-right", "border-bottom", "border-left", "outline"
]

private def namedCssColors : List String := [
  "transparent", "currentcolor", "currentColor", "black", "white", "red", "green", "blue",
  "yellow", "orange", "purple", "pink", "gray", "grey", "cyan", "magenta", "navy", "teal",
  "maroon", "olive", "silver", "lime", "aqua", "fuchsia", "indigo", "violet", "gold", "coral",
  "crimson", "salmon", "tomato", "khaki", "plum", "orchid", "tan", "beige", "ivory", "linen",
  "snow", "azure", "mintcream", "honeydew", "lavender", "aliceblue", "whitesmoke", "gainsboro",
  "lightgray", "lightgrey", "darkgray", "darkgrey", "dimgray", "dimgrey", "slategray", "slategrey",
  "none"
]

private def validUnits : List String := [
  "px", "rem", "em", "%", "vh", "vw", "dvh", "svh", "lvh", "dvw", "svw", "lvw",
  "fr", "ch", "ex", "vmin", "vmax", "pt", "cm", "mm", "in", "cqw", "cqh", "cqi", "cqb"
]

private def validTimeUnits : List String := ["ms", "s"]

private def isNumericString (s : String) : Bool :=
  let cs := match s.toList with | '-' :: r | '+' :: r => r | r => r
  let (intPart, rest) := cs.span Char.isDigit
  match rest with
  | [] => !intPart.isEmpty
  | '.' :: fracPart => !fracPart.isEmpty && fracPart.all Char.isDigit
  | _ => false

private def parseNumberWithUnit (tok : String) : Option (String × String) :=
  let cs := tok.toList
  let (sign, rest0) := match cs with
    | '-' :: r => ("-", r)
    | '+' :: r => ("", r)
    | r        => ("", r)
  let (d1, rest1) := rest0.span Char.isDigit
  let (numCs, unitCs) := match rest1 with
    | '.' :: r2 =>
        let (d2, u) := r2.span Char.isDigit
        if d2.isEmpty then (d1, '.' :: r2) else (d1 ++ '.' :: d2, u)
    | _ => (d1, rest1)
  if numCs.isEmpty then none
  else some (sign ++ String.ofList numCs, String.ofList unitCs)

private def isValidLenAtom (tok : String) : Bool :=
  tok == "0" || tok == "auto" || tok == "none" ||
  tok == "fit-content" || tok == "min-content" || tok == "max-content" ||
  commonGlobalKw.contains tok ||
  tok.startsWith "var(" || tok.startsWith "calc(" || tok.startsWith "clamp(" ||
  tok.startsWith "min(" || tok.startsWith "max(" ||
  match parseNumberWithUnit tok with
  | some (_, u) => !u.isEmpty && validUnits.contains u
  | none        => false

private def isValidTimeAtom (tok : String) : Bool :=
  tok == "0" || tok.startsWith "var(" ||
  match parseNumberWithUnit tok with
  | some (_, u) => validTimeUnits.contains u
  | none        => false

private def splitTopLevel (sep : Char) (s : String) : List String :=
  let rec go (cs : List Char) (depth : Nat) (inStr : Bool) (q : Char) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] =>
        let t := (String.ofList cur.reverse).trimmed
        (if t.isEmpty then acc else t :: acc).reverse
    | c :: rest =>
        if inStr then
          go rest depth (c != q) q (c :: cur) acc
        else if c == '"' || c == '\'' then
          go rest depth true c (c :: cur) acc
        else if c == '(' then
          go rest (depth + 1) false q (c :: cur) acc
        else if c == ')' then
          go rest (depth - 1) false q (c :: cur) acc
        else if depth == 0 && (if sep == ' ' then c.isWhitespace else c == sep) then
          let t := (String.ofList cur.reverse).trimmed
          go rest 0 false q [] (if t.isEmpty then acc else t :: acc)
        else
          go rest depth false q (c :: cur) acc
  go s.toList 0 false '"' [] []

private def parseFuncCall? (tok : String) : Option (String × String) :=
  let cs := tok.toList
  let (fnCs, rest) := cs.span (fun c => c.isAlphanum || c == '-' || c == '_')
  if fnCs.isEmpty then none
  else
    match rest with
    | '(' :: inner =>
        match inner.reverse with
        | ')' :: revArgs => some (String.ofList fnCs, (String.ofList revArgs.reverse).trimmed)
        | _ => none
    | _ => none

private def validateRgbArgs (fnName argsStr : String) : Except String (Option (Nat × Nat × Nat)) := do
  let parts :=
    let byComma := splitTopLevel ',' argsStr
    if byComma.length > 1 then byComma else splitTopLevel ' ' (argsStr.replace "/" " ")
  let need := if fnName == "rgba" then 4 else 3
  if parts.length < 3 || parts.length > 4 then
    throw s!"`{fnName}({argsStr})` expects {need} arguments"
  let mut chs : Array Nat := #[]
  for i in [0:3] do
    let p := parts[i]!
    if p.startsWith "var(" then return none
    match p.toNat? with
    | some n =>
        if n > 255 then
          throw s!"`{fnName}({argsStr})`: channel value `{n}` is out of range (must be 0..255)"
        chs := chs.push n
    | none =>
        throw s!"`{fnName}({argsStr})`: expected integer channel 0..255, got `{p}`"
  if parts.length == 4 then
    let aStr := parts[3]!
    if aStr.startsWith "var(" then return none
    if !isNumericString aStr && !(aStr.endsWith "%" && isNumericString (String.ofList (aStr.toList.dropLast))) then
      throw s!"`{fnName}({argsStr})`: invalid alpha value `{aStr}`"
    if aStr == "1" || aStr == "1.0" || aStr == "100%" then
      return some (chs[0]!, chs[1]!, chs[2]!)
    else
      return none
  return some (chs[0]!, chs[1]!, chs[2]!)

private def validateColorLiteral (tok : String) : Except String (Option (Nat × Nat × Nat)) := do
  if tok.startsWith "#" then
    if !Qed.isValidHexColor tok then
      throw s!"invalid hex color `{tok}` (expected 3, 4, 6, or 8 hex digits, e.g. `#06c` or `#2563eb`)"
    return Qed.parseHexRgb? tok
  else if namedCssColors.contains tok || commonGlobalKw.contains tok then
    if tok == "white" then return some (255, 255, 255)
    else if tok == "black" then return some (0, 0, 0)
    else return none
  else if tok.startsWith "var(" then
    return none
  else if let some (fn, args) := parseFuncCall? tok then
    match fn with
    | "rgb" | "rgba" => validateRgbArgs fn args
    | "hsl" | "hsla" | "oklch" | "oklab" | "lab" | "lch" | "color-mix" | "light-dark" => return none
    | _ => throw s!"unknown color function `{fn}(...)` in `{tok}`"
  else
    throw s!"invalid CSS color value `{tok}`"

/-! ## Environment Resolution for Tokens, Styles, Themes & Keyframes -/

def resolveInRegistry {α : Type} (reg : NameMap α) (env : Environment)
    (currNs : Name) (openDecls : List OpenDecl) (rawName : String) : Option α :=
  let nm := rawName.toName
  if let some v := reg.find? (currNs ++ nm) then some v
  else if let some v := reg.find? nm then some v
  else
    let fromOpen := openDecls.findSome? fun
      | .simple ns _ => reg.find? (ns ++ nm)
      | .explicit id declName => if id == nm then reg.find? declName else none
    match fromOpen with
    | some v => some v
    | none =>
        -- Check `env` global resolution as fallback
        (ResolveName.resolveGlobalName env {} currNs openDecls nm).findSome? fun (full, _) =>
          reg.find? full

private def isIdentLike (tok : String) : Bool :=
  match tok.toList with
  | [] => false
  | c :: rest => (c.isAlpha || c == '_') && rest.all (fun ch => ch.isAlphanum || ch == '_' || ch == '.')

private structure ResolvedCssValue where
  cssText    : String
  usedTokens : List String := []
  extraRules : List String := []
  themes     : List Name := []

private def checkTokenKindForProp (ref : Syntax) (prop : String) (tokInfo : TokenMetaInfo) : CoreM Unit := do
  if tokInfo.kind == "any" then return
  if colorProps.contains prop && tokInfo.kind != "color" then
    throwErrorAt ref s!"type mismatch in CSS `{prop}`: token `{tokInfo.fullName}` has kind `{tokInfo.kind}`, expected `color`"
  if lengthProps.contains prop && tokInfo.kind != "len" then
    throwErrorAt ref s!"type mismatch in CSS `{prop}`: token `{tokInfo.fullName}` has kind `{tokInfo.kind}`, expected `len`"
  if (prop == "font-weight" || prop == "line-height" || prop == "opacity" || prop == "z-index") && tokInfo.kind != "num" then
    throwErrorAt ref s!"type mismatch in CSS `{prop}`: token `{tokInfo.fullName}` has kind `{tokInfo.kind}`, expected `num`"
  if prop == "animation-duration" && tokInfo.kind != "time" then
    throwErrorAt ref s!"type mismatch in CSS `{prop}`: token `{tokInfo.fullName}` has kind `{tokInfo.kind}`, expected `time`"

private def checkStrictTokensForProp (ref : Syntax) (p : String) (resolvedAtoms : List String) : CoreM Unit := do
  for a in resolvedAtoms do
    if colorProps.contains p then
      let allowed := a.startsWith "var(" || a == "transparent" || a == "currentColor" ||
                     a == "currentcolor" || commonGlobalKw.contains a
      unless allowed do
        throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"
    if lengthProps.contains p then
      let allowed := a.startsWith "var(" || a == "0" || a == "auto" || a == "none" ||
                     a == "100%" || commonGlobalKw.contains a
      unless allowed do
        throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw length `{a}` is disallowed; use a `theme` length token instead"
    if borderShorthandProps.contains p then
      if a.startsWith "#" || a.startsWith "rgb(" || a.startsWith "rgba(" || a.startsWith "hsl(" || a.startsWith "oklch(" then
        throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"

private def validatePropValue (ref : Syntax) (p resolvedVal : String) (resolvedAtoms : List String) : CoreM Unit := do
  if let some allowed := enumPropValues p then
    for a in resolvedAtoms do
      unless allowed.contains a || commonGlobalKw.contains a || a.startsWith "var(" do
        throwErrorAt ref s!"invalid value `{a}` for CSS property `{p}` (expected one of: {String.intercalate ", " allowed})"
  else if colorProps.contains p then
    if resolvedAtoms.length != 1 then
      throwErrorAt ref s!"CSS color property `{p}` expects a single color value, got `{resolvedVal}`"
    match validateColorLiteral resolvedAtoms.head! with
    | .ok _ => pure ()
    | .error msg => throwErrorAt ref s!"in `{p}`: {msg}"
  else if lengthProps.contains p then
    for a in resolvedAtoms do
      unless isValidLenAtom a do
        throwErrorAt ref s!"invalid length `{a}` for CSS property `{p}` (use a unit like `px`, `rem`, `em`, `%`, `vh`, `vw`, `0`, `auto`, `calc(...)`, or a `len` token)"
  else if borderShorthandProps.contains p then
    if resolvedAtoms == ["none"] || resolvedAtoms == ["0"] || resolvedAtoms.all (fun a => commonGlobalKw.contains a || a.startsWith "var(") then
      pure ()
    else if resolvedAtoms.length == 3 then
      let w := resolvedAtoms[0]!; let s := resolvedAtoms[1]!; let c := resolvedAtoms[2]!
      unless isValidLenAtom w do
        throwErrorAt ref s!"in `{p}`: invalid border width `{w}`"
      unless ["solid", "dashed", "dotted", "double", "groove", "ridge", "inset", "outset", "none", "hidden"].contains s || s.startsWith "var(" do
        throwErrorAt ref s!"in `{p}`: invalid border style `{s}`"
      match validateColorLiteral c with
      | .ok _ => pure ()
      | .error msg => throwErrorAt ref s!"in `{p}`: {msg}"
    else
      throwErrorAt ref s!"`{p}` expects `none`, `0`, or `<width> <style> <color>` (e.g. `1px solid #ddd`), got `{resolvedVal}`"
  else if p == "animation-duration" || p == "transition-duration" then
    for a in resolvedAtoms do
      unless isValidTimeAtom a do
        throwErrorAt ref s!"invalid duration `{a}` for `{p}` (expected e.g. `200ms` or `0.3s`)"
  else
    -- Still validate any inline `#hex` or `rgb(...)` embedded in shorthand properties like `box-shadow` or `background`
    for a in resolvedAtoms do
      if a.startsWith "#" && !Qed.isValidHexColor a then
        throwErrorAt ref s!"in `{p}`: invalid hex color `{a}`"
      if let some (fn, args) := parseFuncCall? a then
        if fn == "rgb" || fn == "rgba" then
          match validateRgbArgs fn args with
          | .ok _ => pure ()
          | .error msg => throwErrorAt ref s!"in `{p}`: {msg}"

private def resolveAndValidateDecl (ref : Syntax) (env : Environment) (currNs : Name)
    (openDecls : List OpenDecl) (strictTokens : Bool) (prop rawVal : String) :
    CoreM ResolvedCssValue := do
  let p := prop.trimmed
  let vRaw := rawVal.trimmed
  let v := if vRaw.endsWith ";" then (String.ofList vRaw.toList.dropLast).trimmed else vRaw
  if p.isEmpty then throwErrorAt ref "empty CSS property name"
  if v.isEmpty then throwErrorAt ref s!"missing value for CSS property `{p}`"
  let isCustomProp := p.startsWith "--"
  if !isCustomProp && !knownCssProps.contains p then
    throwErrorAt ref s!"unknown CSS property `{p}`{Qed.Diag.didYouMean p knownCssProps}"
  let tokReg := tokenMetaRegistry.getState env
  let kfReg  := keyframesMetaRegistry.getState env
  let atoms := splitTopLevel ' ' v
  let mut outAtoms : Array String := #[]
  let mut usedToks : List String := []
  let mut extraRules : List String := []
  let mut usedThemes : List Name := []
  for a in atoms do
    if isIdentLike a then
      if let some tInfo := resolveInRegistry tokReg env currNs openDecls a then
        checkTokenKindForProp ref p tInfo
        outAtoms := outAtoms.push s!"var(--{tInfo.cssName})"
        usedToks := usedToks ++ [tInfo.cssName]
        if let some thNm := tInfo.themeName? then
          unless usedThemes.contains thNm do usedThemes := usedThemes ++ [thNm]
      else if (p == "animation" || p == "animation-name") then
        if let some kfInfo := resolveInRegistry kfReg env currNs openDecls a then
          outAtoms := outAtoms.push kfInfo.kfName
          unless extraRules.contains kfInfo.rule do extraRules := extraRules ++ [kfInfo.rule]
        else
          outAtoms := outAtoms.push a
      else
        outAtoms := outAtoms.push a
    else
      outAtoms := outAtoms.push a
  let resolvedVal := String.intercalate " " outAtoms.toList
  let resolvedAtoms := outAtoms.toList
  if strictTokens && !isCustomProp then
    checkStrictTokensForProp ref p resolvedAtoms
  if !isCustomProp then
    validatePropValue ref p resolvedVal resolvedAtoms
  let extraTokens := Qed.extractVarNames resolvedVal
  return {
    cssText    := resolvedVal
    usedTokens := usedToks ++ extraTokens
    extraRules
    themes     := usedThemes
  }

/-! ## Lowering Parsed CSS Blocks to `List Item` -/

private def atomText (stx : Syntax) : String :=
  match stx with
  | .node _ _ #[.atom _ v] => v
  | .atom _ v              => v
  | _                      => ""

private def splitFirstColon (s : String) : Option (String × String) :=
  let cs := s.toList
  let (lhs, rhs) := cs.span (· != ':')
  match rhs with
  | ':' :: rest => some ((String.ofList lhs).trimmed, (String.ofList rest).trimmed)
  | _ => none

private structure CompiledCssBlock where
  items      : List Qed.Item
  usedTokens : List String
  extraRules : List String
  themes     : List Name

private partial def compileCssBlockItems (env : Environment) (currNs : Name)
    (openDecls : List OpenDecl) (strictTokens : Bool) (stxs : Array Syntax) :
    CoreM CompiledCssBlock := do
  let mut items : List Qed.Item := []
  let mut toks  : List String := []
  let mut rules : List String := []
  let mut thms  : List Name := []
  for stx in stxs do
    if stx.getKind == ``cssNestedBlock then
      let rawHdr := (atomText (stx.getArg 0)).trimmed
      let sel := (String.ofList rawHdr.toList.dropLast).trimmed
      if sel.isEmpty then throwErrorAt (stx.getArg 0) "empty nested CSS selector"
      let sub ← compileCssBlockItems env currNs openDecls strictTokens (stx.getArg 1).getArgs
      items := items ++ [.nest sel sub.items]
      toks  := toks ++ sub.usedTokens
      rules := rules ++ sub.extraRules
      for t in sub.themes do unless thms.contains t do thms := thms ++ [t]
    else if stx.getKind == ``cssSimpleDecl then
      let line := (atomText (stx.getArg 0)).trimmed
      let some (p, v) := splitFirstColon line
        | throwErrorAt (stx.getArg 0) s!"expected CSS declaration `property: value`, got `{line}`"
      let res ← resolveAndValidateDecl (stx.getArg 0) env currNs openDecls strictTokens p v
      items := items ++ [.decl p.trimmed res.cssText]
      toks  := toks ++ res.usedTokens
      rules := rules ++ res.extraRules
      for t in res.themes do unless thms.contains t do thms := thms ++ [t]
    else
      throwErrorAt stx s!"unexpected syntax in CSS block ({stx.getKind})"
  return { items, usedTokens := Qed.dedupStrings toks, extraRules := Qed.dedupStrings rules, themes := thms }

private partial def quoteItem : Qed.Item → MacroM Term
  | .decl p v => `(Qed.Item.decl $(Syntax.mkStrLit p) $(Syntax.mkStrLit v))
  | .nest sel body => do
      let bTerms ← body.toArray.mapM quoteItem
      `(Qed.Item.nest $(Syntax.mkStrLit sel) [$[$bTerms],*])

private def quoteStringList (xs : List String) : MacroM Term := do
  let lits := xs.toArray.map Syntax.mkStrLit
  `([$[$lits:str],*])

private def quoteStyleLiteral (s : Qed.Style) : MacroM Term := do
  let itemTerms ← s.items.toArray.mapM quoteItem
  let tokList   ← quoteStringList s.usedTokens
  let extraList ← quoteStringList s.extraRules
  let isGlob : Term ← if s.isGlobal then `(Bool.true) else `(Bool.false)
  `({ className  := $(Syntax.mkStrLit s.className)
      raw        := $(Syntax.mkStrLit s.raw)
      items      := [$[$itemTerms],*]
      usedTokens := $tokList
      extraRules := $extraList
      isGlobal   := $isGlob : Qed.Style })

/-! ## `style <name> [extends ...] [strict_tokens]:` Elaborator -/

def elabStyleDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (nameId : Ident) (extendsIds : Array Ident) (strictTokens : Bool)
    (bodyStxs : Array Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let currNs ← getCurrNamespace
  let openDecls := (← getScope).openDecls
  let compiled ← liftCoreM <| compileCssBlockItems env currNs openDecls strictTokens bodyStxs
  let styleReg := styleMetaRegistry.getState env
  let shortLabel := nameId.getId.getString!
  let fullName := currNs ++ nameId.getId
  let mut baseMetas : Array StyleMetaInfo := #[]
  for bId in extendsIds do
    let some bm := resolveInRegistry styleReg env currNs openDecls bId.getId.toString
      | throwErrorAt bId s!"unknown style `{bId.getId}` in `extends` (declare it with `style {bId.getId}:`)"
    baseMetas := baseMetas.push bm
  let mergedItems := baseMetas.foldl (fun acc bm => Qed.Item.mergeItems acc bm.items) []
  let finalItems  := Qed.Item.mergeItems mergedItems compiled.items
  let rawCss      := Qed.Item.renderList finalItems
  let clean       := Qed.sanitizeCssIdent shortLabel
  let cls         := if clean.isEmpty then s!"qed-{Qed.shortHexHash (Qed.cssHash rawCss)}"
                     else s!"qed-{clean}-{Qed.shortHexHash (Qed.cssHash rawCss)}"
  let allToks  := Qed.dedupStrings ((baseMetas.foldl (fun acc bm => acc ++ bm.usedTokens) []) ++ compiled.usedTokens ++ Qed.collectItemTokens finalItems)
  let allExtra := Qed.dedupStrings ((baseMetas.foldl (fun acc bm => acc ++ bm.extraRules) []) ++ compiled.extraRules)
  let allThemes := baseMetas.foldl (fun acc bm => bm.themes.foldl (fun a t => if a.contains t then a else a ++ [t]) acc) compiled.themes
  let baked : Qed.Style := {
    className := cls, raw := rawCss, items := finalItems,
    usedTokens := allToks, extraRules := allExtra, isGlobal := false
  }
  let valTerm ← liftMacroM <| quoteStyleLiteral baked
  elabCommand (← `(command| $[$doc?:docComment]? def $nameId : Qed.Style := $valTerm))
  modifyEnv fun e => styleMetaRegistry.addEntry e {
    fullName, items := finalItems, usedTokens := allToks, extraRules := allExtra, themes := allThemes
  }

@[command_elab styleCmd] def elabStyleCmd : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if (stx.getArg 0).getNumArgs == 1 then some ⟨((stx.getArg 0).getArg 0)⟩ else none
  let nameId : Ident := ⟨(stx.getArg 2)⟩
  let extendsIds : Array Ident :=
    if (stx.getArg 3).getNumArgs == 1 then (((stx.getArg 3).getArg 0).getArg 1).getSepArgs.map (⟨·⟩) else #[]
  let strictTokens := (stx.getArg 4).getNumArgs == 1
  let bodyStxs := (stx.getArg 6).getArgs
  elabStyleDef doc? nameId extendsIds strictTokens bodyStxs

/-! ## `keyframes <name>:` Elaborator -/

@[command_elab keyframesCmd] def elabKeyframesCmd : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if (stx.getArg 0).getNumArgs == 1 then some ⟨((stx.getArg 0).getArg 0)⟩ else none
  let nameId : Ident := ⟨(stx.getArg 2)⟩
  let kfName := Qed.sanitizeCssIdent nameId.getId.getString!
  let env ← getEnv
  let currNs ← getCurrNamespace
  let openDecls := (← getScope).openDecls
  let mut steps : List (String × List Qed.Item) := []
  for stepStx in (stx.getArg 4).getArgs do
    unless stepStx.getKind == ``cssNestedBlock do
      throwErrorAt stepStx "expected keyframe stop (`from:`, `to:`, or `50%:`)"
    let rawHdr := (atomText (stepStx.getArg 0)).trimmed
    let stopSel := (String.ofList rawHdr.toList.dropLast).trimmed
    let compiled ← liftCoreM <| compileCssBlockItems env currNs openDecls false (stepStx.getArg 1).getArgs
    steps := steps ++ [(stopSel, compiled.items)]
  let kf : Qed.Keyframes := { name := kfName, steps }
  let stepTerms ← liftMacroM <| steps.toArray.mapM fun (sel, body) => do
    let bTerms ← body.toArray.mapM quoteItem
    `(($(Syntax.mkStrLit sel), [$[$bTerms],*]))
  elabCommand (← `(command| $[$doc?:docComment]? def $nameId : Qed.Keyframes :=
    Qed.keyframes $(Syntax.mkStrLit kfName) [$[$stepTerms],*]))
  let fullName := currNs ++ nameId.getId
  modifyEnv fun e => keyframesMetaRegistry.addEntry e {
    fullName, kfName, rule := kf.rule
  }

/-! ## `theme <Name>:` Elaborator (Typed Tokens + Dark Mode + Resets + WCAG Contrast Proofs!) -/

private structure ThemeTokEntry where
  ref      : Syntax
  ident    : String
  cssName  : String
  kind     : String -- "color" | "len" | "num" | "font" | "time"
  lightCss : String
  lightRgb : Option (Nat × Nat × Nat) := none
  darkCss? : Option String := none
  darkRgb? : Option (Nat × Nat × Nat) := none
deriving Inhabited

private structure ThemeContrastInv where
  ref      : Syntax
  invName  : String
  fgName   : String
  bgName   : String
  minX100  : Nat

private def parseTokenLine (ref : Syntax) (line : String) : CoreM (String × String × String) := do
  -- Format: `<kind> <name> = <value>`
  let cs := line.toList
  let (lhs, rhs) := cs.span (· != '=')
  match rhs with
  | '=' :: rest =>
      let val := (String.ofList rest).trimmed
      let lhsToks := splitTopLevel ' ' (String.ofList lhs)
      match lhsToks with
      | [kind, nm] =>
          unless ["color", "len", "num", "font", "time"].contains kind do
            throwErrorAt ref s!"unknown theme token kind `{kind}` (expected `color`, `len`, `num`, `font`, or `time`)"
          unless isIdentLike nm && !nm.contains '.' do
            throwErrorAt ref s!"invalid theme token name `{nm}`"
          if val.isEmpty then throwErrorAt ref s!"missing value for token `{nm}`"
          return (kind, nm, val)
      | _ =>
          throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"
  | _ =>
      throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"

private def parseDecimalX100 (s : String) : Option Nat :=
  let t := s.trimmed
  match t.splitOn "." with
  | [w] => w.toNat?.map (· * 100)
  | [w, f] => do
      let wn ← w.toNat?
      let fcs := f.toList
      if fcs.isEmpty || !fcs.all Char.isDigit then none
      else if fcs.length == 1 then
        let fn ← f.toNat?
        some (wn * 100 + fn * 10)
      else
        let fn ← (String.ofList (fcs.take 2)).toNat?
        some (wn * 100 + fn)
  | _ => none

private def parseContrastInvLine (ref : Syntax) (line : String) : CoreM ThemeContrastInv := do
  -- Format: `invariant <name>: contrast(<fg>, <bg>) >= <ratio>`
  let some (lhs, rhs) := splitFirstColon line
    | throwErrorAt ref s!"expected `invariant <name>: contrast(fg, bg) >= <ratio>`, got `{line}`"
  let lhsParts := splitTopLevel ' ' lhs
  let invName ← match lhsParts with
    | ["invariant", nm] => pure nm
    | _ => throwErrorAt ref s!"expected `invariant <name>: ...`, got `{lhs}`"
  let rhsParts := rhs.splitOn ">="
  let (callStr, threshStr) ← match rhsParts with
    | [c, t] => pure (c.trimmed, t.trimmed)
    | _ => throwErrorAt ref s!"expected `contrast(fg, bg) >= <ratio>`, got `{rhs}`"
  let some (fn, argsStr) := parseFuncCall? callStr
    | throwErrorAt ref s!"expected `contrast(fg, bg)`, got `{callStr}`"
  unless fn == "contrast" do
    throwErrorAt ref s!"expected `contrast(fg, bg)` in theme invariant, got `{fn}(...)`"
  let args := splitTopLevel ',' argsStr
  let (fgName, bgName) ← match args with
    | [a, b] => pure (a.trimmed, b.trimmed)
    | _ => throwErrorAt ref s!"`contrast(...)` expects 2 token names, got `{argsStr}`"
  let some minX100 := parseDecimalX100 threshStr
    | throwErrorAt ref s!"invalid contrast threshold `{threshStr}` (expected e.g. `4.5`, `3.0`, or `7.0`)"
  return { ref, invName, fgName, bgName, minX100 }

private def validateThemeVal (ref : Syntax) (kind val : String) : CoreM (String × Option (Nat × Nat × Nat)) := do
  match kind with
  | "color" =>
      match validateColorLiteral val with
      | .ok rgb? => return (val, rgb?)
      | .error msg => throwErrorAt ref s!"invalid theme color value: {msg}"
  | "len" =>
      unless isValidLenAtom val do
        throwErrorAt ref s!"invalid theme length value `{val}`"
      return (val, none)
  | "num" =>
      unless isNumericString val do
        throwErrorAt ref s!"invalid theme numeric value `{val}`"
      return (val, none)
  | "time" =>
      unless isValidTimeAtom val do
        throwErrorAt ref s!"invalid theme time value `{val}`"
      return (val, none)
  | "font" =>
      let clean := if val.startsWith "\"" && val.endsWith "\"" && val.length >= 2 then
        String.ofList (val.toList.drop 1 |>.dropLast)
      else val
      return (clean, none)
  | _ => throwErrorAt ref s!"unknown token kind `{kind}`"

private def toKebabCase (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | c :: cs =>
        if c.isUpper then '-' :: c.toLower :: go cs
        else if c == '_' then '-' :: go cs
        else c :: go cs
  match go s.toList with
  | '-' :: rest => String.ofList rest
  | cs          => String.ofList cs

private def quoteOptColor (cssStr : String) (rgb? : Option (Nat × Nat × Nat)) : MacroM Term := do
  match rgb? with
  | some (r, g, b) =>
      `(some ({ raw := $(Syntax.mkStrLit cssStr), rgb? := some ($(Syntax.mkNumLit (toString r)), $(Syntax.mkNumLit (toString g)), $(Syntax.mkNumLit (toString b))) } : Qed.Color))
  | none =>
      `(some ({ raw := $(Syntax.mkStrLit cssStr), rgb? := none } : Qed.Color))

private def emitThemeTokens (themeNm fullThemeName : Name) (thStyleRaw : String)
    (entries : Array ThemeTokEntry) : CommandElabM Unit := do
  for e in entries do
    let tokId := mkIdentFrom e.ref (themeNm ++ Name.mkSimple e.ident)
    let cssLit := Syntax.mkStrLit e.cssName
    let mkOptRaw (ty : Term) (val? : Option String) : MacroM Term := match val? with
      | some s => `(some ({ raw := $(Syntax.mkStrLit s) } : $ty))
      | none   => `(none)
    let (tyTerm, lTerm, dTerm) ← match e.kind with
      | "color" =>
          let l ← liftMacroM <| quoteOptColor e.lightCss e.lightRgb
          let d ← match e.darkCss? with
            | some dc => liftMacroM <| quoteOptColor dc e.darkRgb?
            | none    => `(none)
          pure (← `(Qed.Color), l, d)
      | "len" | "num" | "time" =>
          let ty ← match e.kind with
            | "len" => `(Qed.Len) | "num" => `(Qed.CssNum) | _ => `(Qed.Time)
          pure (ty, ← liftMacroM <| mkOptRaw ty (some e.lightCss), ← liftMacroM <| mkOptRaw ty e.darkCss?)
      | _ =>
          let d ← match e.darkCss? with | some dc => `(some $(Syntax.mkStrLit dc)) | none => `(none)
          pure (← `(String), ← `(some $(Syntax.mkStrLit e.lightCss)), d)
    elabCommand (← `(command| def $tokId : Qed.TypedToken $tyTerm :=
      { name := $cssLit, lightVal := $lTerm, darkVal := $dTerm }))
    modifyEnv fun env' => tokenMetaRegistry.addEntry env' {
      fullName := fullThemeName ++ Name.mkSimple e.ident, cssName := e.cssName
      kind := e.kind, themeName? := some fullThemeName, themeRule? := some thStyleRaw
    }

private def emitThemeContrastInvs (themeNm : Name) (entries : Array ThemeTokEntry)
    (invs : Array ThemeContrastInv) : CommandElabM Unit := do
  for inv in invs do
    let some fgE := entries.find? (·.ident == inv.fgName)
      | throwErrorAt inv.ref s!"unknown token `{inv.fgName}` in contrast invariant `{inv.invName}`"
    let some bgE := entries.find? (·.ident == inv.bgName)
      | throwErrorAt inv.ref s!"unknown token `{inv.bgName}` in contrast invariant `{inv.invName}`"
    unless fgE.kind == "color" && bgE.kind == "color" do
      throwErrorAt inv.ref s!"`contrast({inv.fgName}, {inv.bgName})` requires two `color` tokens"
    let lightRatio := Qed.Color.contrastX100 ⟨fgE.lightCss, fgE.lightRgb⟩ ⟨bgE.lightCss, bgE.lightRgb⟩
    if lightRatio < inv.minX100 then
      throwErrorAt inv.ref s!"WCAG contrast invariant `{inv.invName}` failed in light mode: contrast({inv.fgName}={fgE.lightCss}, {inv.bgName}={bgE.lightCss}) is {Qed.formatContrastX100 lightRatio}, required >= {Qed.formatContrastX100 inv.minX100}"
    if fgE.darkCss?.isSome || bgE.darkCss?.isSome then
      let darkFg : Qed.Color := ⟨fgE.darkCss?.getD fgE.lightCss, fgE.darkRgb?.orElse (fun _ => fgE.lightRgb)⟩
      let darkBg : Qed.Color := ⟨bgE.darkCss?.getD bgE.lightCss, bgE.darkRgb?.orElse (fun _ => bgE.lightRgb)⟩
      let darkRatio := Qed.Color.contrastX100 darkFg darkBg
      if darkRatio < inv.minX100 then
        throwErrorAt inv.ref s!"WCAG contrast invariant `{inv.invName}` failed in dark mode: contrast({inv.fgName}={darkFg.raw}, {inv.bgName}={darkBg.raw}) is {Qed.formatContrastX100 darkRatio}, required >= {Qed.formatContrastX100 inv.minX100}"
    let invId := mkIdentFrom inv.ref (themeNm ++ Name.mkSimple inv.invName)
    let fgId  := mkIdentFrom inv.ref (themeNm ++ Name.mkSimple inv.fgName)
    let bgId  := mkIdentFrom inv.ref (themeNm ++ Name.mkSimple inv.bgName)
    elabCommand (← `(command|
      theorem $invId : Qed.TypedToken.wcagCheck $fgId $bgId $(Syntax.mkNumLit (toString inv.minX100)) = true := by decide))

@[command_elab themeCmd] def elabThemeCmd : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if (stx.getArg 0).getNumArgs == 1 then some ⟨((stx.getArg 0).getArg 0)⟩ else none
  let themeId : Ident := ⟨(stx.getArg 2)⟩
  let themeNm := themeId.getId
  let env ← getEnv
  let currNs ← getCurrNamespace
  let openDecls := (← getScope).openDecls
  let mut entries : Array ThemeTokEntry := #[]
  let mut resets  : List Qed.Item := []
  let mut invs    : Array ThemeContrastInv := #[]
  for itemStx in (stx.getArg 4).getArgs do
    if itemStx.getKind == ``cssSimpleDecl then
      let line := (atomText (itemStx.getArg 0)).trimmed
      if line.startsWith "invariant " then
        invs := invs.push (← liftCoreM <| parseContrastInvLine (itemStx.getArg 0) line)
      else
        let (kind, nm, rawVal) ← liftCoreM <| parseTokenLine (itemStx.getArg 0) line
        if entries.any (·.ident == nm) then
          throwErrorAt (itemStx.getArg 0) s!"duplicate token `{nm}` in theme `{themeNm}`"
        let (cleanVal, rgb?) ← liftCoreM <| validateThemeVal (itemStx.getArg 0) kind rawVal
        entries := entries.push {
          ref := (itemStx.getArg 0), ident := nm, cssName := toKebabCase nm,
          kind, lightCss := cleanVal, lightRgb := rgb?
        }
    else if itemStx.getKind == ``cssNestedBlock then
      let rawHdr := (atomText (itemStx.getArg 0)).trimmed
      let hdr := (String.ofList rawHdr.toList.dropLast).trimmed
      if hdr == "dark" then
        for dStx in (itemStx.getArg 1).getArgs do
          unless dStx.getKind == ``cssSimpleDecl do
            throwErrorAt dStx "expected `<kind> <name> = <value>` inside `dark:`"
          let (kind, nm, rawVal) ← liftCoreM <| parseTokenLine (dStx.getArg 0) (atomText (dStx.getArg 0)).trimmed
          let some idx := entries.findIdx? (·.ident == nm)
            | throwErrorAt (dStx.getArg 0) s!"dark override for unknown token `{nm}` (declare it in light mode first)"
          let prev := entries[idx]!
          unless prev.kind == kind do
            throwErrorAt (dStx.getArg 0) s!"dark override kind mismatch for `{nm}`: declared as `{prev.kind}`, overridden as `{kind}`"
          let (cleanVal, rgb?) ← liftCoreM <| validateThemeVal (dStx.getArg 0) kind rawVal
          entries := entries.set! idx { prev with darkCss? := some cleanVal, darkRgb? := rgb? }
      else if hdr.startsWith "reset " then
        let sel := (String.ofList (hdr.toList.drop 6)).trimmed
        let compiled ← liftCoreM <| compileCssBlockItems env currNs openDecls false (itemStx.getArg 1).getArgs
        resets := resets ++ [.nest sel compiled.items]
      else
        throwErrorAt (itemStx.getArg 0) s!"unknown section `{hdr}:` in `theme` (expected `dark:` or `reset <selector>:`)"
  let lightDecls : List Qed.Item := entries.toList.map fun e => .decl ("--" ++ e.cssName) e.lightCss
  let darkEntries := entries.toList.filter (·.darkCss?.isSome)
  let darkDecls : List Qed.Item := darkEntries.map fun e => .decl ("--" ++ e.cssName) (e.darkCss?.getD "")
  let defToks : List String := entries.toList.map (·.cssName)
  let darkToks : List String := darkEntries.map (·.cssName)
  let thVal : Qed.Theme := {
    name := themeNm.getString!, lightDecls, darkDecls, resets,
    definedTokens := defToks, darkTokens := darkToks
  }
  let thStyle := thVal.asStyle
  let fullThemeName := currNs ++ themeNm
  emitThemeTokens themeNm fullThemeName thStyle.raw entries
  let lDeclTerms ← liftMacroM <| lightDecls.toArray.mapM quoteItem
  let dDeclTerms ← liftMacroM <| darkDecls.toArray.mapM quoteItem
  let rTerms     ← liftMacroM <| resets.toArray.mapM quoteItem
  let defTokList ← liftMacroM <| quoteStringList defToks
  let drkTokList ← liftMacroM <| quoteStringList darkToks
  let themeConstId := mkIdentFrom themeId (themeNm ++ `theme)
  let styleConstId := mkIdentFrom themeId (themeNm ++ `style)
  elabCommand (← `(command| $[$doc?:docComment]? def $themeConstId : Qed.Theme :=
    { name          := $(Syntax.mkStrLit thVal.name)
      lightDecls    := [$[$lDeclTerms],*]
      darkDecls     := [$[$dDeclTerms],*]
      resets        := [$[$rTerms],*]
      definedTokens := $defTokList
      darkTokens    := $drkTokList }))
  let styleLit ← liftMacroM <| quoteStyleLiteral thStyle
  elabCommand (← `(command| def $styleConstId : Qed.Style := $styleLit))
  emitThemeContrastInvs themeNm entries invs
  modifyEnv fun env' => themeMetaRegistry.addEntry env' {
    fullName := fullThemeName, styleConst := fullThemeName ++ `style
    themeConst := fullThemeName ++ `theme, renderedRule := thStyle.raw
    definedTokens := defToks, darkTokens := darkToks
  }

/-! ## `verify_theme <Theme> for <app>` Command (Kernel Proof of Token Completeness) -/

private def decodeNatExpr? : Nat → Expr → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
      match e.consumeMData with
      | .lit (.natVal n) => some n
      | .const ``Nat.zero _ => some 0
      | .app (.const ``Nat.succ _) a => (decodeNatExpr? fuel a).map (· + 1)
      | .app (.app (.app (.const ``OfNat.ofNat _) _) n) _ => decodeNatExpr? fuel n
      | _ => none

private def decodeUInt8Expr? : Nat → Expr → Option UInt8
  | 0, _ => none
  | fuel + 1, e =>
      let e := e.consumeMData
      if let some n := decodeNatExpr? fuel e then some n.toUInt8
      else
        let (fn, args) := e.getAppFnArgs
        if fn == ``Fin.mk && args.size ≥ 2 then decodeUInt8Expr? fuel args[1]!
        else if fn == ``BitVec.ofFin && args.size ≥ 2 then decodeUInt8Expr? fuel args[1]!
        else if (fn == `UInt8.ofBitVec || fn == ``UInt8.ofNat || fn == ``BitVec.ofNat) && args.size ≥ 1 then
          decodeUInt8Expr? fuel args[args.size - 1]!
        else if args.size == 1 then decodeUInt8Expr? fuel args[0]!
        else none

private def decodeExprList? : Nat → Expr → Option (List Expr)
  | 0, _ => none
  | fuel + 1, e =>
      let e := e.consumeMData
      let (fn, args) := e.getAppFnArgs
      if fn == ``List.nil then some []
      else if fn == ``List.cons && args.size >= 2 then do
        let h := args[args.size - 2]!
        let t ← decodeExprList? fuel args[args.size - 1]!
        some (h :: t)
      else none

private def decodeReducedStr? : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, e =>
      let e := e.consumeMData
      match e with
      | .lit (.strVal s) => some s
      | _ =>
          let args := e.getAppArgs
          if args.isEmpty then none
          else
            match decodeExprList? 4096 e with
            | some elems => do
                let bytes ← elems.mapM (decodeUInt8Expr? 64)
                String.fromUTF8? (ByteArray.mk bytes.toArray)
            | none => args.findSome? (decodeReducedStr? fuel)

private def decodeReducedStrList? (e : Expr) : Option (List String) := do
  let elems ← decodeExprList? 4096 e
  elems.mapM (decodeReducedStr? 64)

@[command_elab verifyThemeCmd] def elabVerifyThemeCmd : CommandElab := fun stx => do
  let thId : Ident := ⟨(stx.getArg 1)⟩
  let target : Term := ⟨(stx.getArg 3)⟩
  let env ← getEnv
  let currNs ← getCurrNamespace
  let openDecls := (← getScope).openDecls
  let some thInfo := resolveInRegistry (themeMetaRegistry.getState env) env currNs openDecls thId.getId.toString
    | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
  let thConst := mkIdentFrom thId thInfo.themeConst
  -- Determine whether target is an `App` (use `.styles`) or already a `List Style`
  let stylesTerm : Term ← liftTermElabM do
    let e ← elabTerm target none
    synthesizeSyntheticMVarsNoPostponing
    let ty ← whnf (← instantiateMVars (← inferType e))
    if ty.isAppOf `Qed.App then
      return (← `(($target).styles))
    else
      return target
  -- Run kernel proof and produce actionable error listing missing tokens if it fails
  let savedMsgs := (← get).messages
  modify fun s => { s with messages := {} }
  let ok ← try
    elabCommand (← `(command|
      example : ($thConst).coversAll ($stylesTerm) = true := by decide))
    pure (!(← get).messages.hasErrors)
  catch _ => pure false
  if ok then
    let newMsgs := (← get).messages
    modify fun s => { s with messages := savedMsgs ++ newMsgs }
  else
    modify fun s => { s with messages := savedMsgs }
    let missingStr ← liftTermElabM do
      try
        let expr ← elabTerm (← `(($thConst).missingTokens ($stylesTerm))) none
        let red ← Meta.reduce expr (skipProofs := true) (skipTypes := true)
        match decodeReducedStrList? red with
        | some xs => return "[" ++ String.intercalate ", " (xs.map fun s => s!"\"{s}\"") ++ "]"
        | none    => return (← Meta.ppExpr red).pretty
      catch _ => return "(unknown)"
    let targetLabel := (target.raw.reprint.getD "target").trimmed
    throwErrorAt stx s!"theme `{thId.getId}` does not define all CSS tokens used by `{targetLabel}`.\n  Missing tokens: {missingStr}\nAdd them to `theme {thId.getId}:`."

end Qed.StyleDsl
