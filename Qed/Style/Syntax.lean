import Lean
import Qed.Diag
import Qed.Style.Core
import Qed.Style.Contrast

namespace Qed.StyleDsl
open Lean Parser Elab Command Term Meta

/-! ## Persistent Compile-Time CSS Registries -/

structure StyleMetaInfo     where mk :: (fullName : Name) (items : List Qed.Item) (usedTokens extraRules : List String) (themes : List Name := []) deriving Inhabited
structure TokenMetaInfo     where mk :: (fullName : Name) (cssName kind : String) (themeName? : Option Name := none) deriving Inhabited
structure KeyframesMetaInfo where mk :: (fullName : Name) (kfName rule : String) deriving Inhabited
structure ThemeMetaInfo     where mk :: (fullName styleConst themeConst : Name) deriving Inhabited

initialize styleMetaRegistry     : SimplePersistentEnvExtension StyleMetaInfo     (NameMap StyleMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)
initialize tokenMetaRegistry     : SimplePersistentEnvExtension TokenMetaInfo     (NameMap TokenMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)
initialize keyframesMetaRegistry : SimplePersistentEnvExtension KeyframesMetaInfo (NameMap KeyframesMetaInfo) ← Qed.Diag.mkNameMapExt (·.fullName)
initialize themeMetaRegistry     : SimplePersistentEnvExtension ThemeMetaInfo     (NameMap ThemeMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)

/-! ## Custom Non-Polluting CSS Line Parsers -/

private def scanCssLine (input : String) : Nat → String.Pos.Raw → Bool → Char → Bool → String.Pos.Raw
  | 0, pos, _, _, _ => pos
  | fuel + 1, pos, inStr, q, esc =>
      if pos.atEnd input then pos else
      let ch := pos.get input; let nxt := pos.next input
      if ch == '\n' || ch == '\r' then pos
      else if inStr then scanCssLine input fuel nxt (if esc then true else if ch == '\\' then true else ch != q) q (!esc && ch == '\\')
      else if ch == '"' || ch == '\'' then scanCssLine input fuel nxt true ch false
      else if ch == '-' && !nxt.atEnd input && nxt.get input == '-' then
        let a2 := nxt.next input; if a2.atEnd input || (a2.get input).isWhitespace then pos else scanCssLine input fuel a2 false q false
      else scanCssLine input fuel nxt false q false

private def skipToEol (input : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, pos => pos | fuel + 1, pos => if pos.atEnd input || pos.get input == '\n' || pos.get input == '\r' then pos else skipToEol input fuel (pos.next input)

private def takeRestOfLineFn (kind : Name) (mustColon : Bool) : ParserFn := fun c s =>
  let input := c.inputString; let startPos := s.pos
  let endPos := scanCssLine input (input.utf8ByteSize - startPos.byteIdx + 1) startPos false '"' false
  let trimmed := (String.Pos.Raw.extract input startPos endPos).trimmed
  if trimmed.isEmpty then s.mkError "CSS declaration or nested block"
  else if trimmed.endsWith ":" != mustColon then s.mkError (if mustColon then "CSS block header ending with ':'" else "CSS declaration")
  else whitespace c ((mkNodeToken kind startPos true c (s.setPos endPos)).setPos (skipToEol input (input.utf8ByteSize - endPos.byteIdx + 1) endPos))

local macro "def_css_line_parser " id:Parser.ident mustColon:term : command => do
  let full := Name.mkStr3 "Qed" "StyleDsl" id.getId.toString
  `(def $id : Parser := { fn := takeRestOfLineFn $(quote full) $mustColon }
    @[combinator_formatter $(mkIdent full)] def $(mkIdent (id.getId ++ `formatter)) : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom $(quote full)
    @[combinator_parenthesizer $(mkIdent full)] def $(mkIdent (id.getId ++ `parenthesizer)) : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken)

def_css_line_parser cssBlockHeader true
def_css_line_parser cssDeclLine false

declare_syntax_cat cssBlockItem
@[cssBlockItem_parser] def cssNestedBlock : Parser := leading_parser withPosition (cssBlockHeader >> many1 (checkColGt >> categoryParser `cssBlockItem 0))
@[cssBlockItem_parser] def cssSimpleDecl  : Parser := leading_parser cssDeclLine

def styleExtendsClause  : Parser := leading_parser atomic (symbol "extends") >> sepBy1 Parser.ident ","
def styleStrictClause   : Parser := leading_parser atomic (identEq `strict_tokens)
def styleContrastBgP    : Parser := strLit <|> Parser.ident
def styleContrastRatioP : Parser := scientificLit <|> numLit
def styleContrastClause : Parser := leading_parser
  atomic (identEq `contrast >> ">=") >> styleContrastRatioP >> optional (atomic (identEq `on) >> styleContrastBgP)

private def cssCmd (kw : String) (extra : Parser := skip) : Parser :=
  optional Command.docComment >> withPosition (symbol kw >> Parser.ident >> extra >> ":" >> many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[command_parser] def styleCmd       : Parser := leading_parser cssCmd "style " (optional styleExtendsClause >> optional styleStrictClause >> optional styleContrastClause)
@[command_parser] def keyframesCmd   : Parser := leading_parser cssCmd "keyframes "
@[command_parser] def themeCmd       : Parser := leading_parser cssCmd "theme "
@[command_parser] def verifyThemeCmd : Parser := leading_parser "verify_theme " >> Parser.ident >> symbol "for" >> termParser
@[command_parser] def verifyContrastCmd : Parser := leading_parser
  "verify_contrast " >> ">=" >> styleContrastRatioP >> symbol "for" >> termParser maxPrec >>
  optional (atomic (symbol "with") >> Parser.ident) >>
  optional (atomic (identEq `on) >> styleContrastBgP)

/-! ## CSS Property & Value Validation Engine -/

private inductive CssPropKind where | color | len | border | num | time | any | enum (vals : List String)
private def ws (s : String) : List String := s.splitOn " "
private def commonGlobalKw  : List String := ws "inherit initial unset revert revert-layer"
private def borderStyleVals : List String := ws "solid dashed dotted double groove ridge inset outset none hidden"
private def isGlobalOrVar (a : String) : Bool := a.startsWith "var(" || commonGlobalKw.contains a

private def cssPropMap : Std.HashMap String CssPropKind := Id.run do
  let mut m : Std.HashMap String CssPropKind := {}
  for (k, props) in [
    (.color,  "color background-color border-color border-top-color border-right-color border-bottom-color border-left-color outline-color text-decoration-color fill stroke accent-color caret-color"),
    (.len,    "width height min-width max-width min-height max-height padding padding-top padding-right padding-bottom padding-left padding-inline padding-block padding-inline-start padding-inline-end margin margin-top margin-right margin-bottom margin-left margin-inline margin-block margin-inline-start margin-inline-end inset top right bottom left gap row-gap column-gap font-size border-radius border-width outline-offset letter-spacing flex-basis"),
    (.border, "border border-top border-right border-bottom border-left outline"),
    (.num,    "font-weight line-height opacity z-index"), (.time, "animation-duration transition-duration"),
    (.any,    "aspect-ratio isolation float clear content vertical-align object-position flex flex-flow flex-grow flex-shrink justify-items align-content place-items place-content place-self order grid grid-template grid-template-columns grid-template-rows grid-template-areas grid-column grid-row grid-area grid-auto-flow grid-auto-columns grid-auto-rows font font-family font-variant word-spacing text-decoration text-decoration-thickness text-underline-offset text-indent text-shadow overflow-wrap hyphens tab-size background background-image background-position background-size background-repeat background-clip background-origin border-top-width border-right-width border-bottom-width border-left-width border-top-left-radius border-top-right-radius border-bottom-left-radius border-bottom-right-radius border-collapse border-spacing outline-width outline-style box-shadow filter backdrop-filter mix-blend-mode clip-path mask mask-image transform transform-origin perspective rotate scale translate transition transition-property transition-timing-function transition-delay animation animation-name animation-timing-function animation-delay animation-iteration-count animation-direction animation-fill-mode animation-play-state will-change resize appearance touch-action list-style list-style-type list-style-position table-layout caption-side empty-cells stroke-width stroke-linecap stroke-linejoin stroke-dasharray scroll-margin scroll-padding scroll-snap-type scroll-snap-align overscroll-behavior container-type container-name container")
  ] do for p in ws props do m := m.insert p k
  let ov := "visible hidden clip scroll auto"
  for (p, vs) in [
    ("display", "flex inline-flex grid inline-grid block inline inline-block table table-row table-cell flow-root contents none list-item"),
    ("position", "static relative absolute fixed sticky"), ("text-align", "left right center justify start end"),
    ("flex-direction", "row column row-reverse column-reverse"), ("flex-wrap", "nowrap wrap wrap-reverse"),
    ("justify-content", "flex-start flex-end start end center space-between space-around space-evenly stretch normal"),
    ("align-items", "flex-start flex-end start end center stretch baseline normal"),
    ("align-self", "auto flex-start flex-end start end center stretch baseline"), ("justify-self", "auto start end center stretch"),
    ("box-sizing", "content-box border-box"), ("scroll-behavior", "auto smooth"),
    ("cursor", "auto default pointer not-allowed text move grab grabbing wait progress help crosshair zoom-in zoom-out col-resize row-resize ew-resize ns-resize none"),
    ("overflow", ov), ("overflow-x", ov), ("overflow-y", ov), ("white-space", "normal nowrap pre pre-wrap pre-line break-spaces"),
    ("object-fit", "fill contain cover none scale-down"), ("pointer-events", "auto none all"), ("user-select", "auto none text all contain"),
    ("visibility", "visible hidden collapse"), ("font-style", "normal italic oblique"), ("text-overflow", "clip ellipsis"),
    ("text-transform", "none capitalize uppercase lowercase full-width"), ("word-break", "normal break-all keep-all break-word")
  ] do m := m.insert p (.enum (ws vs))
  return m.insert "border-style" (.enum borderStyleVals)

private def knownCssProps  : List String := cssPropMap.keys
private def namedCssColors : List String := ws "transparent currentcolor currentColor black white red green blue yellow orange purple pink gray grey cyan magenta navy teal maroon olive silver lime aqua fuchsia indigo violet gold coral crimson salmon tomato khaki plum orchid tan beige ivory linen snow azure mintcream honeydew lavender aliceblue whitesmoke gainsboro lightgray lightgrey darkgray darkgrey dimgray dimgrey slategray slategrey none"
private def validUnits     : List String := ws "px rem em % vh vw dvh svh lvh dvw svw lvw fr ch ex vmin vmax pt cm mm in cqw cqh cqi cqb"

private def parseNumberWithUnit (tok : String) : Option (String × String) :=
  let (sign, r0) := match tok.toList with | '-' :: r => ("-", r) | '+' :: r => ("", r) | r => ("", r)
  let (d1, r1) := r0.span Char.isDigit
  let (numCs, unitCs) := match r1 with
    | '.' :: r2 => let (d2, u) := r2.span Char.isDigit; if d2.isEmpty then (d1, '.' :: r2) else (d1 ++ '.' :: d2, u) | _ => (d1, r1)
  if numCs.isEmpty then none else some (sign ++ String.ofList numCs, String.ofList unitCs)

private def isNumericString (s : String) : Bool := (parseNumberWithUnit s).any (·.2.isEmpty)
private def isValidLenAtom (tok : String) : Bool :=
  isGlobalOrVar tok || ["0", "auto", "none", "fit-content", "min-content", "max-content"].contains tok ||
  ["calc(", "clamp(", "min(", "max("].any (tok.startsWith ·) || (parseNumberWithUnit tok).any fun (_, u) => !u.isEmpty && validUnits.contains u
private def isValidTimeAtom (tok : String) : Bool :=
  tok == "0" || tok.startsWith "var(" || (parseNumberWithUnit tok).any fun (_, u) => u == "ms" || u == "s"

private def splitTopLevel (sep : Char) (s : String) : List String :=
  let flush (cur : List Char) (acc : List String) := let t := (String.ofList cur.reverse).trimmed; if t.isEmpty then acc else t :: acc
  let rec go : List Char → Nat → Bool → Char → List Char → List String → List String
    | [], _, _, _, cur, acc => (flush cur acc).reverse
    | c :: rest, d, true, q, cur, acc => go rest d (c != q) q (c :: cur) acc
    | c :: rest, d, false, q, cur, acc =>
        if c == '"' || c == '\'' then go rest d true c (c :: cur) acc
        else if c == '(' then go rest (d + 1) false q (c :: cur) acc
        else if c == ')' then go rest (d - 1) false q (c :: cur) acc
        else if d == 0 && (if sep == ' ' then c.isWhitespace else c == sep) then go rest 0 false q [] (flush cur acc)
        else go rest d false q (c :: cur) acc
  go s.toList 0 false '"' [] []

private def parseFuncCall? (tok : String) : Option (String × String) :=
  let (fnCs, rest) := tok.toList.span fun c => c.isAlphanum || c == '-' || c == '_'
  match fnCs, rest with
  | _ :: _, '(' :: inner => match inner.reverse with | ')' :: revArgs => some (String.ofList fnCs, (String.ofList revArgs.reverse).trimmed) | _ => none
  | _, _ => none

private def validateRgbArgs (fnName argsStr : String) : Except String (Option (Nat × Nat × Nat)) := do
  let byComma := splitTopLevel ',' argsStr
  let parts := if byComma.length > 1 then byComma else splitTopLevel ' ' (argsStr.replace "/" " ")
  if parts.length < 3 || parts.length > 4 then throw s!"`{fnName}({argsStr})` expects {if fnName == "rgba" then 4 else 3} arguments"
  let mut chs : Array Nat := #[]
  for i in [0:3] do
    let p := parts[i]!; if p.startsWith "var(" then return none
    let some n := p.toNat? | throw s!"`{fnName}({argsStr})`: expected integer channel 0..255, got `{p}`"
    if n > 255 then throw s!"`{fnName}({argsStr})`: channel value `{n}` is out of range (must be 0..255)"
    chs := chs.push n
  if parts.length == 4 then
    let aStr := parts[3]!; if aStr.startsWith "var(" then return none
    if !isNumericString aStr && !(aStr.endsWith "%" && isNumericString (String.ofList aStr.toList.dropLast)) then throw s!"`{fnName}({argsStr})`: invalid alpha value `{aStr}`"
    if aStr != "1" && aStr != "1.0" && aStr != "100%" then return none
  return some (chs[0]!, chs[1]!, chs[2]!)

private def validateColorLiteral (tok : String) : Except String (Option (Nat × Nat × Nat)) := do
  if tok.startsWith "#" then
    if !Qed.isValidHexColor tok then throw s!"invalid hex color `{tok}` (expected 3, 4, 6, or 8 hex digits, e.g. `#06c` or `#2563eb`)"
    return Qed.parseHexRgb? tok
  else if namedCssColors.contains tok || commonGlobalKw.contains tok then
    return if tok == "white" then some (255, 255, 255) else if tok == "black" then some (0, 0, 0) else none
  else if tok.startsWith "var(" then return none
  else if let some (fn, args) := parseFuncCall? tok then match fn with
    | "rgb" | "rgba" => validateRgbArgs fn args
    | "hsl" | "hsla" | "oklch" | "oklab" | "lab" | "lch" | "color-mix" | "light-dark" => return none
    | _ => throw s!"unknown color function `{fn}(...)` in `{tok}`"
  else throw s!"invalid CSS color value `{tok}`"

/-! ## Environment Resolution for Tokens, Styles, Themes & Keyframes -/

def resolveInRegistry {α : Type} (reg : NameMap α) (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (rawName : String) : Option α :=
  Qed.Diag.lookupNameMap? reg env currNs openDecls rawName.toName

private def isIdentLike (tok : String) : Bool :=
  match tok.toList with | c :: rest => (c.isAlpha || c == '_') && rest.all fun ch => ch.isAlphanum || ch == '_' || ch == '.' | [] => false

private structure ResolvedCssValue where mk :: (cssText : String) (usedTokens extraRules : List String := []) (themes : List Name := [])

private def checkStrictAndValidate (ref : Syntax) (strict : Bool) (p resolvedVal : String) (kind : CssPropKind) (atoms : List String) : CoreM Unit := do
  let checkOrThrow {α : Type} : Except String α → CoreM Unit | .ok _ => pure () | .error msg => throwErrorAt ref s!"in `{p}`: {msg}"
  if strict then for a in atoms do match kind with
    | .color  => unless isGlobalOrVar a || ["transparent", "currentColor", "currentcolor"].contains a do throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"
    | .len    => unless isGlobalOrVar a || ["0", "auto", "none", "100%"].contains a do throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw length `{a}` is disallowed; use a `theme` length token instead"
    | .border => if ["#", "rgb(", "rgba(", "hsl(", "oklch("].any (a.startsWith ·) then throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"
    | _ => pure ()
  match kind with
  | .enum allowed => for a in atoms do unless allowed.contains a || isGlobalOrVar a do throwErrorAt ref s!"invalid value `{a}` for CSS property `{p}` (expected one of: {String.intercalate ", " allowed})"
  | .color =>
      if atoms.length != 1 then throwErrorAt ref s!"CSS color property `{p}` expects a single color value, got `{resolvedVal}`"
      checkOrThrow (validateColorLiteral atoms.head!)
  | .len => for a in atoms do unless isValidLenAtom a do throwErrorAt ref s!"invalid length `{a}` for CSS property `{p}` (use a unit like `px`, `rem`, `em`, `%`, `vh`, `vw`, `0`, `auto`, `calc(...)`, or a `len` token)"
  | .border =>
      if atoms == ["none"] || atoms == ["0"] || atoms.all isGlobalOrVar then pure ()
      else if let [w, s, c] := atoms then
        unless isValidLenAtom w do throwErrorAt ref s!"in `{p}`: invalid border width `{w}`"
        unless borderStyleVals.contains s || s.startsWith "var(" do throwErrorAt ref s!"in `{p}`: invalid border style `{s}`"
        checkOrThrow (validateColorLiteral c)
      else throwErrorAt ref s!"`{p}` expects `none`, `0`, or `<width> <style> <color>` (e.g. `1px solid #ddd`), got `{resolvedVal}`"
  | .time => for a in atoms do unless isValidTimeAtom a do throwErrorAt ref s!"invalid duration `{a}` for `{p}` (expected e.g. `200ms` or `0.3s`)"
  | .num | .any => for a in atoms do
      if a.startsWith "#" && !Qed.isValidHexColor a then throwErrorAt ref s!"in `{p}`: invalid hex color `{a}`"
      if let some (fn, args) := parseFuncCall? a then if fn == "rgb" || fn == "rgba" then checkOrThrow (validateRgbArgs fn args)

private def resolveAndValidateDecl (ref : Syntax) (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (strictTokens : Bool) (prop rawVal : String) : CoreM ResolvedCssValue := do
  let p := prop.trimmed; let vRaw := rawVal.trimmed
  let v := if vRaw.endsWith ";" then (String.ofList vRaw.toList.dropLast).trimmed else vRaw
  if p.isEmpty then throwErrorAt ref "empty CSS property name"
  if v.isEmpty then throwErrorAt ref s!"missing value for CSS property `{p}`"
  let isCustom := p.startsWith "--"
  let propKind ← if isCustom then pure CssPropKind.any else match cssPropMap[p]? with | some k => pure k | none => throwErrorAt ref s!"unknown CSS property `{p}`{Qed.Diag.didYouMean p knownCssProps}"
  let (tokReg, kfReg) := (tokenMetaRegistry.getState env, keyframesMetaRegistry.getState env)
  let mut outAtoms : Array String := #[]; let mut usedToks : List String := []; let mut extraRules : List String := []; let mut usedThemes : List Name := []
  for a in splitTopLevel ' ' v do
    if isIdentLike a then
      if let some tInfo := resolveInRegistry tokReg env currNs openDecls a then
        if tInfo.kind != "any" then
          let exp? := match propKind with | .color => some "color" | .len => some "len" | .num => some "num" | .time => some "time" | _ => none
          if let some exp := exp? then if tInfo.kind != exp then throwErrorAt ref s!"type mismatch in CSS `{p}`: token `{tInfo.fullName}` has kind `{tInfo.kind}`, expected `{exp}`"
        outAtoms := outAtoms.push s!"var(--{tInfo.cssName})"; usedToks := usedToks ++ [tInfo.cssName]
        if let some thNm := tInfo.themeName? then usedThemes := (usedThemes ++ [thNm]).eraseDups
        continue
      if p == "animation" || p == "animation-name" then
        if let some kfInfo := resolveInRegistry kfReg env currNs openDecls a then
          outAtoms := outAtoms.push kfInfo.kfName; extraRules := (extraRules ++ [kfInfo.rule]).eraseDups; continue
    outAtoms := outAtoms.push a
  let resolvedAtoms := outAtoms.toList; let resolvedVal := String.intercalate " " resolvedAtoms
  if !isCustom then checkStrictAndValidate ref strictTokens p resolvedVal propKind resolvedAtoms
  return .mk resolvedVal (usedToks ++ Qed.extractVarNames resolvedVal) extraRules usedThemes

/-! ## Lowering Parsed CSS Blocks & Quoting Literals -/

private def atomText : Syntax → String | .node _ _ #[.atom _ v] | .atom _ v => v | _ => ""
private def stripTrailingColon (stx : Syntax) : String := (String.ofList (atomText stx).trimmed.toList.dropLast).trimmed
private def optDocComment (stx : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) := if (stx.getArg 0).getNumArgs == 1 then some ⟨(stx.getArg 0).getArg 0⟩ else none
private def getCssScope : CommandElabM (Environment × Name × List OpenDecl) := return (← getEnv, ← getCurrNamespace, (← getScope).openDecls)

private def splitFirstChar (sep : Char) (s : String) : Option (String × String) :=
  let (lhs, rhs) := s.toList.span (· != sep)
  match rhs with | c :: rest => if c == sep then some ((String.ofList lhs).trimmed, (String.ofList rest).trimmed) else none | _ => none

private structure CompiledCssBlock where mk :: (items : List Qed.Item) (usedTokens extraRules : List String) (themes : List Name)

private partial def compileCssBlockItems (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (strictTokens : Bool) (stxs : Array Syntax) : CoreM CompiledCssBlock := do
  let mut items : List Qed.Item := []; let mut toks : List String := []; let mut rules : List String := []; let mut thms : List Name := []
  let mut seenProps : Array String := #[]
  for stx in stxs do
    let (item, t, r, th) ←
      if stx.getKind == ``cssNestedBlock then
        let sel := stripTrailingColon (stx.getArg 0); if sel.isEmpty then throwErrorAt (stx.getArg 0) "empty nested CSS selector"
        let sub ← compileCssBlockItems env currNs openDecls strictTokens (stx.getArg 1).getArgs
        pure (.nest sel sub.items, sub.usedTokens, sub.extraRules, sub.themes)
      else if stx.getKind == ``cssSimpleDecl then
        let line := (atomText (stx.getArg 0)).trimmed
        let some (p, v) := splitFirstChar ':' line | throwErrorAt (stx.getArg 0) s!"expected CSS declaration `property: value`, got `{line}`"
        let propKey := p.trimmed
        if seenProps.contains propKey then
          throwErrorAt (stx.getArg 0) s!"duplicate CSS property `{propKey}` in the same style block (remove the redundant declaration)"
        seenProps := seenProps.push propKey
        let res ← resolveAndValidateDecl (stx.getArg 0) env currNs openDecls strictTokens p v
        pure (.decl propKey res.cssText, res.usedTokens, res.extraRules, res.themes)
      else throwErrorAt stx s!"unexpected syntax in CSS block ({stx.getKind})"
    items := items ++ [item]; toks := toks ++ t; rules := rules ++ r; thms := (thms ++ th).eraseDups
  return .mk items toks.eraseDups rules.eraseDups thms

private partial def quoteItem : Qed.Item → MacroM Term
  | .decl p v => `(Qed.Item.decl $(quote p) $(quote v))
  | .nest sel body => do `(Qed.Item.nest $(quote sel) [$(← body.toArray.mapM quoteItem),*])
private def quoteItems (items : List Qed.Item) : MacroM Term := do `([$(← items.toArray.mapM quoteItem),*])
private def quoteRgbOpt : Option (Nat × Nat × Nat) → MacroM Term
  | none => `(none)
  | some (r, g, b) => `(some ($(quote r), $(quote g), $(quote b)))

private def quoteThemeColorEntry (e : Qed.ThemeColorEntry) : MacroM Term := do
  `({ cssName := $(quote e.cssName), lightRgb := ($(quote e.lightRgb.1), $(quote e.lightRgb.2.1), $(quote e.lightRgb.2.2)),
      darkRgb? := $(← quoteRgbOpt e.darkRgb?) : Qed.ThemeColorEntry })

private def quoteThemePalette (ps : List Qed.ThemeColorEntry) : MacroM Term := do
  `([$(← ps.toArray.mapM quoteThemeColorEntry),*])

private def quoteStyleColorCheck (c : Qed.StyleColorCheck) : MacroM Term := do
  `({ scope := $(quote c.scope), fgCss := $(quote c.fgCss), bgCss := $(quote c.bgCss),
      fgRgb? := $(← quoteRgbOpt c.fgRgb?), bgRgb? := $(← quoteRgbOpt c.bgRgb?),
      fgTok? := $(quote c.fgTok?), bgTok? := $(quote c.bgTok?), forcedDark := $(quote c.forcedDark) : Qed.StyleColorCheck })

private def quoteFallbackBgOpt : Option Qed.ContrastFallbackBg → MacroM Term
  | none => `(none)
  | some fb => do `(some ({ css := $(quote fb.css), rgb? := $(← quoteRgbOpt fb.rgb?), tok? := $(quote fb.tok?) : Qed.ContrastFallbackBg }))

private def quoteStyleLiteral (s : Qed.Style) : MacroM Term := do
  `({ className := $(quote s.className), raw := $(quote s.raw), items := $(← quoteItems s.items),
      usedTokens := $(quote s.usedTokens), extraRules := $(quote s.extraRules), isGlobal := $(quote s.isGlobal),
      colorChecks := [$(← s.colorChecks.toArray.mapM quoteStyleColorCheck),*],
      themePalette := $(← quoteThemePalette s.themePalette) : Qed.Style })

/-! ## `style`, `keyframes`, `theme`, `verify_theme`, and `verify_contrast` Elaborators -/

private def parseDecimalX100 (s : String) : Option Nat := match s.trimmed.splitOn "." with
  | [w] => w.toNat?.map (· * 100)
  | [w, f] => do let wn ← w.toNat?; let fcs := f.toList; guard (!fcs.isEmpty && fcs.all Char.isDigit)
                 some (wn * 100 + (← if fcs.length == 1 then f.toNat?.map (· * 10) else (String.ofList (fcs.take 2)).toNat?))
  | _ => none

private def parseContrastRatioStx (stx : Syntax) : CoreM Nat := do
  let raw := (stx.reprint.getD "").trimmed
  let some n := parseDecimalX100 raw | throwErrorAt stx s!"invalid WCAG contrast threshold `{raw}` (expected e.g. `4.5`, `3.0`, or `7.0`)"
  return n

private def resolveContrastBgStx (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (bgStx : Syntax) : CoreM (Qed.ContrastFallbackBg × Option Name) := do
  if let some s := bgStx.isStrLit? then
    match validateColorLiteral s.trimmed with
    | .ok (some rgb) => return ({ css := s.trimmed, rgb? := some rgb, tok? := none }, none)
    | .ok none => throwErrorAt bgStx s!"`on \"{s}\"` must be an opaque hex, `rgb(...)`, `white`, or `black` color so contrast can be verified"
    | .error msg => throwErrorAt bgStx s!"in `on`: {msg}"
  else
    let idStr := bgStx.getId.eraseMacroScopes.toString
    let some tInfo := resolveInRegistry (tokenMetaRegistry.getState env) env currNs openDecls idStr
      | throwErrorAt bgStx s!"unknown color token `{idStr}` in `on {idStr}`"
    unless tInfo.kind == "color" do
      throwErrorAt bgStx s!"token `{tInfo.fullName}` has kind `{tInfo.kind}`, expected `color` in `on {idStr}`"
    return ({ css := s!"var(--{tInfo.cssName})", rgb? := none, tok? := some tInfo.cssName }, tInfo.themeName?)

private def mkThemePaletteTerm (env : Environment) (themeNames : List Name) : MacroM Term := do
  let thReg := themeMetaRegistry.getState env
  let thConsts := themeNames.eraseDups.filterMap fun nm => (thReg.find? nm).map (·.themeConst)
  match thConsts with
  | [] => `(([] : List Qed.ThemeColorEntry))
  | c :: rest => rest.foldlM (init := ← `($(mkIdent c).colorPalette)) fun acc n => do `($acc ++ $(mkIdent n).colorPalette)

private def resolveStylesTargetTerm (target : Term) : CommandElabM Term := liftTermElabM do
  let e ← elabTerm target none; synthesizeSyntheticMVarsNoPostponing
  if (← whnf (← instantiateMVars (← inferType e))).isAppOf `Qed.App then `(($target).styles) else pure target

private def checkContrastEval (ref : Syntax) (minX100 : Nat) (violsTerm : Term) : CommandElabM Unit := do
  let errStr : String ← liftTermElabM do
    try Lean.Meta.reduceEval (← elabTerm (← `(Qed.formatContrastViolations $(quote minX100) $violsTerm)) none)
    catch _ => pure ""
  unless errStr.isEmpty do throwErrorAt ref errStr

def elabStyleDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (nameId : Ident) (extendsIds : Array Ident)
    (strictTokens : Bool) (bodyStxs : Array Syntax) (contrastOpt? : Option Syntax := none) : CommandElabM Unit := do
  let (env, currNs, openDecls) ← getCssScope; let compiled ← liftCoreM <| compileCssBlockItems env currNs openDecls strictTokens bodyStxs
  let styleReg := styleMetaRegistry.getState env
  let baseMetas : Array StyleMetaInfo ← extendsIds.mapM fun bId => do
    let some bm := resolveInRegistry styleReg env currNs openDecls bId.getId.toString | throwErrorAt bId s!"unknown style `{bId.getId}` in `extends` (declare it with `style {bId.getId}:`)"
    pure bm
  let finalItems := Qed.Item.mergeItems (baseMetas.foldl (fun acc bm => Qed.Item.mergeItems acc bm.items) []) compiled.items
  let (rawCss, clean) := (Qed.Item.renderList finalItems, Qed.sanitizeCssIdent nameId.getId.getString!)
  let cls := s!"qed-{if clean.isEmpty then "" else clean ++ "-"}{Qed.shortHexHash (Qed.cssHash rawCss)}"
  let allToks  := (baseMetas.toList.flatMap (·.usedTokens) ++ compiled.usedTokens ++ Qed.collectItemTokens finalItems).eraseDups
  let allExtra := (baseMetas.toList.flatMap (·.extraRules) ++ compiled.extraRules).eraseDups
  let allThemes := (compiled.themes ++ baseMetas.toList.flatMap (·.themes)).eraseDups
  let colorChecks := Qed.collectStyleColorChecks none none false "" finalItems
  let baked : Qed.Style := { className := cls, raw := rawCss, items := finalItems, usedTokens := allToks, extraRules := allExtra, colorChecks }
  elabCommand (← `(command| $[$doc?:docComment]? def $nameId : Qed.Style := $(← liftMacroM <| quoteStyleLiteral baked)))
  modifyEnv fun e => styleMetaRegistry.addEntry e (.mk (currNs ++ nameId.getId) finalItems allToks allExtra allThemes)
  if let some cStx := contrastOpt? then
    let minX100 ← liftCoreM <| parseContrastRatioStx (cStx.getArg 2)
    let (bgOpt?, extraTheme?) ← if (cStx.getArg 3).getNumArgs == 2 then do
        let (bg, th?) ← liftCoreM <| resolveContrastBgStx env currNs openDecls ((cStx.getArg 3).getArg 1)
        pure (some bg, th?)
      else pure (none, none)
    unless baked.hasContrastPair bgOpt? do
      throwErrorAt cStx s!"`contrast >= {Qed.formatContrastX100 minX100}` on style `{nameId.getId}` requires both `color` and `background-color` (or `on <bg>`)."
    let themes := match extraTheme? with | some th => (allThemes ++ [th]).eraseDups | none => allThemes
    let palTerm ← liftMacroM <| mkThemePaletteTerm env themes
    let bgTerm ← liftMacroM <| quoteFallbackBgOpt bgOpt?
    checkContrastEval cStx minX100 (← `(Qed.Style.contrastViolations $(quote minX100) $palTerm $bgTerm $nameId))
    let thmId := mkIdentFrom cStx (nameId.getId.appendAfter "_contrast")
    elabCommand (← `(command| theorem $thmId : Qed.Style.checkContrast $(quote minX100) $palTerm $bgTerm $nameId = true := by decide))

def extractStyleExtends (optStx : Syntax) : Array Ident := if optStx.getNumArgs == 1 then ((optStx.getArg 0).getArg 1).getSepArgs.map (⟨·⟩) else #[]
def extractOptChild (optStx : Syntax) : Option Syntax := if optStx.getNumArgs == 1 then some (optStx.getArg 0) else none

@[command_elab styleCmd] def elabStyleCmd : CommandElab := fun stx =>
  elabStyleDef (optDocComment stx) ⟨stx.getArg 2⟩ (extractStyleExtends (stx.getArg 3)) ((stx.getArg 4).getNumArgs == 1) (stx.getArg 7).getArgs (extractOptChild (stx.getArg 5))

@[command_elab keyframesCmd] def elabKeyframesCmd : CommandElab := fun stx => do
  let nameId : Ident := ⟨stx.getArg 2⟩; let kfName := Qed.sanitizeCssIdent nameId.getId.getString!; let (env, currNs, openDecls) ← getCssScope
  let steps ← (stx.getArg 4).getArgs.toList.mapM fun stepStx => do
    unless stepStx.getKind == ``cssNestedBlock do throwErrorAt stepStx "expected keyframe stop (`from:`, `to:`, or `50%:`)"
    pure (stripTrailingColon (stepStx.getArg 0), (← liftCoreM <| compileCssBlockItems env currNs openDecls false (stepStx.getArg 1).getArgs).items)
  let stepTerms ← liftMacroM <| steps.toArray.mapM fun (sel, body) => do `(($(quote sel), $(← quoteItems body)))
  elabCommand (← `(command| $[$(optDocComment stx):docComment]? def $nameId : Qed.Keyframes := Qed.keyframes $(quote kfName) [$[$stepTerms],*]))
  modifyEnv fun e => keyframesMetaRegistry.addEntry e (.mk (currNs ++ nameId.getId) kfName ({ name := kfName, steps } : Qed.Keyframes).rule)

private structure ThemeTokEntry where mk ::
  (ref : Syntax) (ident cssName kind lightCss : String) (lightRgb : Option (Nat × Nat × Nat) := none)
  (darkCss? : Option String := none) (darkRgb? : Option (Nat × Nat × Nat) := none)
deriving Inhabited

private structure ThemeContrastInv where mk :: (ref : Syntax) (invName fgName bgName : String) (minX100 : Nat)

private def parseAndValidateTokenLine (ref : Syntax) (line : String) : CoreM (String × String × String × Option (Nat × Nat × Nat)) := do
  let some (lhs, val) := splitFirstChar '=' line | throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"
  let [kind, nm] := splitTopLevel ' ' lhs | throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"
  unless ["color", "len", "num", "font", "time"].contains kind do throwErrorAt ref s!"unknown theme token kind `{kind}` (expected `color`, `len`, `num`, `font`, or `time`)"
  unless isIdentLike nm && !nm.contains '.' do throwErrorAt ref s!"invalid theme token name `{nm}`"
  if val.isEmpty then throwErrorAt ref s!"missing value for token `{nm}`"
  let (cleanVal, rgb?) ← match kind with
    | "color" => match validateColorLiteral val with | .ok rgb? => pure (val, rgb?) | .error msg => throwErrorAt ref s!"invalid theme color value: {msg}"
    | "len"   => if !isValidLenAtom val then throwErrorAt ref s!"invalid theme length value `{val}`" else pure (val, none)
    | "num"   => if !isNumericString val then throwErrorAt ref s!"invalid theme numeric value `{val}`" else pure (val, none)
    | "time"  => if !isValidTimeAtom val then throwErrorAt ref s!"invalid theme time value `{val}`" else pure (val, none)
    | _       => pure (if val.startsWith "\"" && val.endsWith "\"" && val.length >= 2 then String.ofList (val.toList.drop 1 |>.dropLast) else val, none)
  return (kind, nm, cleanVal, rgb?)

private def parseContrastInvLine (ref : Syntax) (line : String) : CoreM ThemeContrastInv := do
  let some (lhs, rhs) := splitFirstChar ':' line | throwErrorAt ref s!"expected `invariant <name>: contrast(fg, bg) >= <ratio>`, got `{line}`"
  let ["invariant", invName] := splitTopLevel ' ' lhs | throwErrorAt ref s!"expected `invariant <name>: ...`, got `{lhs}`"
  let [c, t] := rhs.splitOn ">=" | throwErrorAt ref s!"expected `contrast(fg, bg) >= <ratio>`, got `{rhs}`"
  let some (fn, argsStr) := parseFuncCall? c.trimmed | throwErrorAt ref s!"expected `contrast(fg, bg)`, got `{c.trimmed}`"
  unless fn == "contrast" do throwErrorAt ref s!"expected `contrast(fg, bg)` in theme invariant, got `{fn}(...)`"
  let [fgName, bgName] := (splitTopLevel ',' argsStr).map String.trimmed | throwErrorAt ref s!"`contrast(...)` expects 2 token names, got `{argsStr}`"
  let some minX100 := parseDecimalX100 t.trimmed | throwErrorAt ref s!"invalid contrast threshold `{t.trimmed}` (expected e.g. `4.5`, `3.0`, or `7.0`)"
  return .mk ref invName fgName bgName minX100

private def toKebabCase (s : String) : String :=
  let cs := s.toList.flatMap fun c => if c.isUpper then ['-', c.toLower] else if c == '_' then ['-'] else [c]
  String.ofList (match cs with | '-' :: r => r | _ => cs)

private def emitThemeTokens (themeNm fullThemeName : Name) (entries : Array ThemeTokEntry) : CommandElabM Unit := do
  let quoteOpt (ty? : Option Term) (css? : Option String) (rgb? : Option (Nat × Nat × Nat) := none) : MacroM Term := match css?, ty? with
    | none, _ => `(none) | some s, some ty => `(some ({ raw := $(quote s) } : $ty))
    | some s, none => do let rT ← match rgb? with | some (r, g, b) => `(some ($(quote r), $(quote g), $(quote b))) | none => `(none)
                         `(some ({ raw := $(quote s), rgb? := $rT } : Qed.Color))
  for e in entries do
    let tokId := mkIdentFrom e.ref (themeNm ++ Name.mkSimple e.ident)
    let (tyTerm, lTerm, dTerm) ← match e.kind with
      | "color" => pure (← `(Qed.Color), ← liftMacroM <| quoteOpt none (some e.lightCss) e.lightRgb, ← liftMacroM <| quoteOpt none e.darkCss? e.darkRgb?)
      | "len" | "num" | "time" =>
          let ty ← match e.kind with | "len" => `(Qed.Len) | "num" => `(Qed.CssNum) | _ => `(Qed.Time)
          pure (ty, ← liftMacroM <| quoteOpt (some ty) (some e.lightCss), ← liftMacroM <| quoteOpt (some ty) e.darkCss?)
      | _ => pure (← `(String), ← `(some $(quote e.lightCss)), ← `(($(quote e.darkCss?) : Option String)))
    elabCommand (← `(command| def $tokId : Qed.TypedToken $tyTerm := { name := $(quote e.cssName), lightVal := $lTerm, darkVal := $dTerm }))
    modifyEnv fun env' => tokenMetaRegistry.addEntry env' (.mk (fullThemeName ++ Name.mkSimple e.ident) e.cssName e.kind (some fullThemeName))

private def emitThemeContrastInvs (themeNm : Name) (entries : Array ThemeTokEntry) (invs : Array ThemeContrastInv) : CommandElabM Unit := do
  for inv in invs do
    let findTok (nm : String) : CommandElabM ThemeTokEntry :=
      match entries.find? (·.ident == nm) with
      | some e => pure e
      | none => throwErrorAt inv.ref s!"unknown token `{nm}` in contrast invariant `{inv.invName}`"
    let (fgE, bgE) := (← findTok inv.fgName, ← findTok inv.bgName)
    unless fgE.kind == "color" && bgE.kind == "color" do throwErrorAt inv.ref s!"`contrast({inv.fgName}, {inv.bgName})` requires two `color` tokens"
    let checkMode (mode : String) (fg bg : Qed.Color) : CommandElabM Unit := do
      let ratio := Qed.Color.contrastX100 fg bg
      if ratio < inv.minX100 then throwErrorAt inv.ref s!"WCAG contrast invariant `{inv.invName}` failed in {mode} mode: contrast({inv.fgName}={fg.raw}, {inv.bgName}={bg.raw}) is {Qed.formatContrastX100 ratio}, required >= {Qed.formatContrastX100 inv.minX100}"
    checkMode "light" ⟨fgE.lightCss, fgE.lightRgb⟩ ⟨bgE.lightCss, bgE.lightRgb⟩
    if fgE.darkCss?.isSome || bgE.darkCss?.isSome then
      checkMode "dark" ⟨fgE.darkCss?.getD fgE.lightCss, fgE.darkRgb?.orElse fun _ => fgE.lightRgb⟩ ⟨bgE.darkCss?.getD bgE.lightCss, bgE.darkRgb?.orElse fun _ => bgE.lightRgb⟩
    let mkId (nm : String) := mkIdentFrom inv.ref (themeNm ++ Name.mkSimple nm)
    elabCommand (← `(command| theorem $(mkId inv.invName) : Qed.TypedToken.wcagCheck $(mkId inv.fgName) $(mkId inv.bgName) $(quote inv.minX100) = true := by decide))

@[command_elab themeCmd] def elabThemeCmd : CommandElab := fun stx => do
  let themeId : Ident := ⟨stx.getArg 2⟩; let themeNm := themeId.getId; let (env, currNs, openDecls) ← getCssScope
  let mut entries : Array ThemeTokEntry := #[]; let mut resets : List Qed.Item := []; let mut invs : Array ThemeContrastInv := #[]
  for itemStx in (stx.getArg 4).getArgs do
    if itemStx.getKind == ``cssSimpleDecl then
      let line := (atomText (itemStx.getArg 0)).trimmed
      if line.startsWith "invariant " then invs := invs.push (← liftCoreM <| parseContrastInvLine (itemStx.getArg 0) line)
      else
        let (kind, nm, cleanVal, rgb?) ← liftCoreM <| parseAndValidateTokenLine (itemStx.getArg 0) line
        if entries.any (·.ident == nm) then throwErrorAt (itemStx.getArg 0) s!"duplicate token `{nm}` in theme `{themeNm}`"
        entries := entries.push (.mk (itemStx.getArg 0) nm (toKebabCase nm) kind cleanVal rgb? none none)
    else if itemStx.getKind == ``cssNestedBlock then
      let hdr := stripTrailingColon (itemStx.getArg 0)
      if hdr == "dark" then
        for dStx in (itemStx.getArg 1).getArgs do
          unless dStx.getKind == ``cssSimpleDecl do throwErrorAt dStx "expected `<kind> <name> = <value>` inside `dark:`"
          let (kind, nm, cleanVal, rgb?) ← liftCoreM <| parseAndValidateTokenLine (dStx.getArg 0) (atomText (dStx.getArg 0)).trimmed
          let some idx := entries.findIdx? (·.ident == nm) | throwErrorAt (dStx.getArg 0) s!"dark override for unknown token `{nm}` (declare it in light mode first)"
          let prev := entries[idx]!
          unless prev.kind == kind do throwErrorAt (dStx.getArg 0) s!"dark override kind mismatch for `{nm}`: declared as `{prev.kind}`, overridden as `{kind}`"
          entries := entries.set! idx { prev with darkCss? := some cleanVal, darkRgb? := rgb? }
      else if hdr.startsWith "reset " then
        let compiled ← liftCoreM <| compileCssBlockItems env currNs openDecls false (itemStx.getArg 1).getArgs
        resets := resets ++ [.nest (String.ofList (hdr.toList.drop 6)).trimmed compiled.items]
      else throwErrorAt (itemStx.getArg 0) s!"unknown section `{hdr}:` in `theme` (expected `dark:` or `reset <selector>:`)"
  let darkEntries := entries.toList.filter (·.darkCss?.isSome)
  let (lightDecls, darkDecls) := (entries.toList.map fun e => Qed.Item.decl ("--" ++ e.cssName) e.lightCss, darkEntries.map fun e => Qed.Item.decl ("--" ++ e.cssName) (e.darkCss?.getD ""))
  let (defToks, darkToks) := (entries.toList.map (·.cssName), darkEntries.map (·.cssName))
  let colorPalette : List Qed.ThemeColorEntry := entries.toList.filterMap fun e =>
    if e.kind == "color" then e.lightRgb.map fun l => { cssName := e.cssName, lightRgb := l, darkRgb? := e.darkRgb? } else none
  let thVal : Qed.Theme := .mk themeNm.getString! lightDecls darkDecls resets defToks darkToks colorPalette; let fullThemeName := currNs ++ themeNm
  emitThemeTokens themeNm fullThemeName entries
  let themeLit ← liftMacroM do `({ name := $(quote thVal.name), lightDecls := $(← quoteItems lightDecls), darkDecls := $(← quoteItems darkDecls), resets := $(← quoteItems resets), definedTokens := $(quote defToks), darkTokens := $(quote darkToks), colorPalette := $(← quoteThemePalette colorPalette) })
  elabCommand (← `(command| $[$(optDocComment stx):docComment]? def $(mkIdentFrom themeId (themeNm ++ `theme)) : Qed.Theme := $themeLit))
  elabCommand (← `(command| def $(mkIdentFrom themeId (themeNm ++ `style)) : Qed.Style := $(← liftMacroM <| quoteStyleLiteral thVal.asStyle)))
  emitThemeContrastInvs themeNm entries invs
  modifyEnv fun env' => themeMetaRegistry.addEntry env' (.mk fullThemeName (fullThemeName ++ `style) (fullThemeName ++ `theme))

@[command_elab verifyThemeCmd] def elabVerifyThemeCmd : CommandElab := fun stx => do
  let (thId, target) : Ident × Term := (⟨stx.getArg 1⟩, ⟨stx.getArg 3⟩); let (env, currNs, openDecls) ← getCssScope
  let some thInfo := resolveInRegistry (themeMetaRegistry.getState env) env currNs openDecls thId.getId.toString | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
  let thConst := mkIdentFrom thId thInfo.themeConst
  let stylesTerm ← resolveStylesTargetTerm target
  let savedMsgs := (← get).messages; modify fun s => { s with messages := {} }
  let ok ← try elabCommand (← `(command| example : ($thConst).coversAll ($stylesTerm) = true := by decide)); pure (!(← get).messages.hasErrors) catch _ => pure false
  let newMsgs := (← get).messages; modify fun s => { s with messages := if ok then savedMsgs ++ newMsgs else savedMsgs }
  if !ok then
    let missingStr ← liftTermElabM do
      try let xs : List String ← Lean.Meta.reduceEval (← elabTerm (← `(($thConst).missingTokens ($stylesTerm))) none)
          return "[" ++ String.intercalate ", " (xs.map fun s => s!"\"{s}\"") ++ "]"
      catch _ => return "(unknown)"
    throwErrorAt stx s!"theme `{thId.getId}` does not define all CSS tokens used by `{(target.raw.reprint.getD "target").trimmed}`.\n  Missing tokens: {missingStr}\nAdd them to `theme {thId.getId}:`."

@[noinline, command_elab verifyContrastCmd] def elabVerifyContrastCmd : CommandElab := fun stx => do
  let minX100 ← liftCoreM <| parseContrastRatioStx (stx.getArg 2)
  let target : Term := ⟨stx.getArg 4⟩
  let (env, currNs, openDecls) ← getCssScope
  let mut themeNames : List Name := []
  if (stx.getArg 5).getNumArgs == 2 then
    let thId : Ident := ⟨(stx.getArg 5).getArg 1⟩
    let some thInfo := resolveInRegistry (themeMetaRegistry.getState env) env currNs openDecls thId.getId.toString
      | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
    themeNames := themeNames ++ [thInfo.fullName]
  let bgOpt? ← if (stx.getArg 6).getNumArgs == 2 then do
      let (bg, th?) ← liftCoreM <| resolveContrastBgStx env currNs openDecls ((stx.getArg 6).getArg 1)
      if let some th := th? then themeNames := themeNames ++ [th]
      pure (some bg)
    else pure none
  let stylesTerm ← resolveStylesTargetTerm target
  let palTerm ← liftMacroM <| mkThemePaletteTerm env themeNames
  let bgTerm ← liftMacroM <| quoteFallbackBgOpt bgOpt?
  checkContrastEval stx minX100 (← `(Qed.findStylesContrastViolations $(quote minX100) $palTerm $bgTerm ($stylesTerm)))
  elabCommand (← `(command| example : Qed.checkStylesContrast $(quote minX100) $palTerm $bgTerm ($stylesTerm) = true := by decide))

end Qed.StyleDsl
