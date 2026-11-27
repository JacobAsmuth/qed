import Lean
import Qed.Diag
import Qed.Style.Core
import Qed.Style.Contrast

namespace Qed.StyleDsl
open Lean Parser Elab Command Term Meta

structure StyleMetaInfo     where mk :: (fullName : Name) (items : List Qed.Item) (usedTokens extraRules : List String) (themes : List Name := []) deriving Inhabited
structure TokenMetaInfo     where mk :: (fullName : Name) (cssName kind : String) (themeName? : Option Name := none) deriving Inhabited
structure KeyframesMetaInfo where mk :: (fullName : Name) (kfName rule : String) deriving Inhabited
structure ThemeMetaInfo     where mk :: (fullName styleConst themeConst : Name) deriving Inhabited

initialize styleMetaRegistry     : SimplePersistentEnvExtension StyleMetaInfo     (NameMap StyleMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)
initialize tokenMetaRegistry     : SimplePersistentEnvExtension TokenMetaInfo     (NameMap TokenMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)
initialize keyframesMetaRegistry : SimplePersistentEnvExtension KeyframesMetaInfo (NameMap KeyframesMetaInfo) ← Qed.Diag.mkNameMapExt (·.fullName)
initialize themeMetaRegistry     : SimplePersistentEnvExtension ThemeMetaInfo     (NameMap ThemeMetaInfo)     ← Qed.Diag.mkNameMapExt (·.fullName)

private def scanCssLine (input : String) : Nat → String.Pos.Raw → Bool → Char → Bool → String.Pos.Raw
  | 0, pos, _, _, _ => pos
  | fuel + 1, pos, inStr, q, esc =>
      if pos.atEnd input then pos else
      let ch := pos.get input; let nxt := pos.next input
      if ch == '\n' || ch == '\r' then pos
      else if inStr then scanCssLine input fuel nxt (esc || ch == '\\' || ch != q) q (!esc && ch == '\\')
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

def cssBlockHeader : Parser := { fn := takeRestOfLineFn `Qed.StyleDsl.cssBlockHeader true }
@[combinator_formatter Qed.StyleDsl.cssBlockHeader] def cssBlockHeader.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom `Qed.StyleDsl.cssBlockHeader
@[combinator_parenthesizer Qed.StyleDsl.cssBlockHeader] def cssBlockHeader.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken
def cssDeclLine : Parser := { fn := takeRestOfLineFn `Qed.StyleDsl.cssDeclLine false }
@[combinator_formatter Qed.StyleDsl.cssDeclLine] def cssDeclLine.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom `Qed.StyleDsl.cssDeclLine
@[combinator_parenthesizer Qed.StyleDsl.cssDeclLine] def cssDeclLine.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

declare_syntax_cat cssBlockItem
@[cssBlockItem_parser] def cssNestedBlock : Parser := leading_parser withPosition (cssBlockHeader >> many1 (checkColGt >> categoryParser `cssBlockItem 0))
@[cssBlockItem_parser] def cssSimpleDecl  : Parser := leading_parser cssDeclLine

def styleExtendsClause  : Parser := leading_parser atomic (symbol "extends") >> sepBy1 Parser.ident ","
def styleStrictClause   : Parser := leading_parser atomic (identEq `strict_tokens)
def styleContrastBgP    : Parser := strLit <|> Parser.ident
def styleContrastRatioP : Parser := scientificLit <|> numLit
def styleContrastClause : Parser := leading_parser atomic (identEq `contrast >> ">=") >> styleContrastRatioP >> optional (atomic (identEq `on) >> styleContrastBgP)

private def cssCmd (kw : String) (extra : Parser := skip) : Parser :=
  optional Command.docComment >> withPosition (symbol kw >> Parser.ident >> extra >> ":" >> many1 (checkColGt >> categoryParser `cssBlockItem 0))

@[command_parser] def styleCmd       : Parser := leading_parser cssCmd "style " (optional styleExtendsClause >> optional styleStrictClause >> optional styleContrastClause)
@[command_parser] def keyframesCmd   : Parser := leading_parser cssCmd "keyframes "
@[command_parser] def themeCmd       : Parser := leading_parser cssCmd "theme "
@[command_parser] def verifyThemeCmd : Parser := leading_parser "verify_theme " >> Parser.ident >> symbol "for" >> termParser
@[command_parser] def verifyContrastCmd : Parser := leading_parser
  "verify_contrast " >> ">=" >> styleContrastRatioP >> symbol "for" >> termParser maxPrec >>
  optional (atomic (symbol "with") >> Parser.ident) >> optional (atomic (identEq `on) >> styleContrastBgP)

private inductive CssPropKind where | color | len | border | num | time | any | enum (vals : List String)
private def ws (s : String) : List String := s.splitOn " "
private def commonGlobalKw  : List String := ws "inherit initial unset revert revert-layer"
private def borderStyleVals : List String := ws "solid dashed dotted double groove ridge inset outset none hidden"
private def isGlobalOrVar (a : String) : Bool := a.startsWith "var(" || commonGlobalKw.contains a

private def cssPropMap : Std.HashMap String CssPropKind :=
  let ov := "visible hidden clip scroll auto"
  let m1 := [
    (.color,  "color background-color border-color border-top-color border-right-color border-bottom-color border-left-color outline-color text-decoration-color fill stroke accent-color caret-color"),
    (.len,    "width height min-width max-width min-height max-height padding padding-top padding-right padding-bottom padding-left padding-inline padding-block padding-inline-start padding-inline-end margin margin-top margin-right margin-bottom margin-left margin-inline margin-block margin-inline-start margin-inline-end inset top right bottom left gap row-gap column-gap font-size border-radius border-width outline-offset letter-spacing flex-basis"),
    (.border, "border border-top border-right border-bottom border-left outline"),
    (.num,    "font-weight line-height opacity z-index"), (.time, "animation-duration transition-duration"),
    (.any,    "aspect-ratio isolation float clear content vertical-align object-position flex flex-flow flex-grow flex-shrink justify-items align-content place-items place-content place-self order grid grid-template grid-template-columns grid-template-rows grid-template-areas grid-column grid-row grid-area grid-auto-flow grid-auto-columns grid-auto-rows font font-family font-variant word-spacing text-decoration text-decoration-thickness text-underline-offset text-indent text-shadow overflow-wrap hyphens tab-size background background-image background-position background-size background-repeat background-clip background-origin border-top-width border-right-width border-bottom-width border-left-width border-top-left-radius border-top-right-radius border-bottom-left-radius border-bottom-right-radius border-collapse border-spacing outline-width outline-style box-shadow filter backdrop-filter mix-blend-mode clip-path mask mask-image transform transform-origin perspective rotate scale translate transition transition-property transition-timing-function transition-delay animation animation-name animation-timing-function animation-delay animation-iteration-count animation-direction animation-fill-mode animation-play-state will-change resize appearance touch-action list-style list-style-type list-style-position table-layout caption-side empty-cells stroke-width stroke-linecap stroke-linejoin stroke-dasharray scroll-margin scroll-padding scroll-snap-type scroll-snap-align overscroll-behavior container-type container-name container")
  ].foldl (init := ({} : Std.HashMap String CssPropKind)) fun m (k, ps) => (ws ps).foldl (fun acc p => acc.insert p k) m
  let m2 := [
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
  ].foldl (init := m1) fun m (p, vs) => m.insert p (.enum (ws vs))
  m2.insert "border-style" (.enum borderStyleVals)

private def knownCssProps  : List String := cssPropMap.keys
private def namedCssColors : List String := ws "transparent currentcolor currentColor black white red green blue yellow orange purple pink gray grey cyan magenta navy teal maroon olive silver lime aqua fuchsia indigo violet gold coral crimson salmon tomato khaki plum orchid tan beige ivory linen snow azure mintcream honeydew lavender aliceblue whitesmoke gainsboro lightgray lightgrey darkgray darkgrey dimgray dimgrey slategray slategrey none"
private def validUnits     : List String := ws "px rem em % vh vw dvh svh lvh dvw svw lvw fr ch ex vmin vmax pt cm mm in cqw cqh cqi cqb"

private def isValidLenAtom (tok : String) : Bool :=
  isGlobalOrVar tok || ["0", "auto", "none", "fit-content", "min-content", "max-content"].contains tok ||
  ["calc(", "clamp(", "min(", "max("].any (tok.startsWith ·) || (Qed.parseNumberWithUnit tok).any fun (_, u) => !u.isEmpty && validUnits.contains u
private def isValidTimeAtom (tok : String) : Bool :=
  tok == "0" || tok.startsWith "var(" || (Qed.parseNumberWithUnit tok).any fun (_, u) => u == "ms" || u == "s"

private def validateColorLiteral (tok : String) : Except String (Option (Nat × Nat × Nat)) := do
  if tok.startsWith "#" then
    if !Qed.isValidHexColor tok then throw s!"invalid hex color `{tok}` (expected 3, 4, 6, or 8 hex digits, e.g. `#06c` or `#2563eb`)"
    return Qed.parseHexRgb? tok
  else if namedCssColors.contains tok || commonGlobalKw.contains tok then return Qed.parseCssColorRgb? tok
  else if tok.startsWith "var(" then return none
  else if let some (fn, args) := Qed.parseFuncCall? tok then match fn with
    | "rgb" | "rgba" => Qed.validateRgbArgs fn args
    | "hsl" | "hsla" | "oklch" | "oklab" | "lab" | "lch" | "color-mix" | "light-dark" => return none
    | _ => throw s!"unknown color function `{fn}(...)` in `{tok}`"
  else throw s!"invalid CSS color value `{tok}`"

def resolveInRegistry {α : Type} (reg : NameMap α) (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (rawName : String) : Option α :=
  Qed.Diag.lookupNameMap? reg env currNs openDecls rawName.toName
private def isIdentLike (tok : String) : Bool :=
  match tok.toList with | c :: rest => (c.isAlpha || c == '_') && rest.all fun ch => ch.isAlphanum || ch == '_' || ch == '.' | [] => false
private structure ResolvedCssValue where mk :: (cssText : String) (usedTokens extraRules : List String := []) (themes : List Name := [])

@[noinline] private def checkAtoms (f : String → CoreM Unit) : List String → CoreM Unit | [] => pure () | a :: rest => do f a; checkAtoms f rest

@[noinline] private def checkStrictAndValidate (ref : Syntax) (strict : Bool) (p resolvedVal : String) (kind : CssPropKind) (atoms : List String) : CoreM Unit := do
  let checkOrThrow {α : Type} : Except String α → CoreM Unit | .ok _ => pure () | .error msg => throwErrorAt ref s!"in `{p}`: {msg}"
  if strict then checkAtoms (fun a => do match kind with
    | .color  => unless isGlobalOrVar a || ["transparent", "currentColor", "currentcolor"].contains a do throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"
    | .len    => unless isGlobalOrVar a || ["0", "auto", "none", "100%"].contains a do throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw length `{a}` is disallowed; use a `theme` length token instead"
    | .border => if ["#", "rgb(", "rgba(", "hsl(", "oklch("].any (a.startsWith ·) then throwErrorAt ref s!"`strict_tokens` violation on `{p}`: raw color `{a}` is disallowed; use a `theme` color token instead"
    | _ => pure ()) atoms
  match kind with
  | .enum allowed => checkAtoms (fun a => unless allowed.contains a || isGlobalOrVar a do throwErrorAt ref s!"invalid value `{a}` for CSS property `{p}` (expected one of: {String.intercalate ", " allowed})") atoms
  | .color => if atoms.length != 1 then throwErrorAt ref s!"CSS color property `{p}` expects a single color value, got `{resolvedVal}`" else checkOrThrow (validateColorLiteral atoms.head!)
  | .len => checkAtoms (fun a => unless isValidLenAtom a do throwErrorAt ref s!"invalid length `{a}` for CSS property `{p}` (use a unit like `px`, `rem`, `em`, `%`, `vh`, `vw`, `0`, `auto`, `calc(...)`, or a `len` token)") atoms
  | .border =>
      if atoms == ["none"] || atoms == ["0"] || atoms.all isGlobalOrVar then pure ()
      else if let [w, s, c] := atoms then
        unless isValidLenAtom w do throwErrorAt ref s!"in `{p}`: invalid border width `{w}`"
        unless borderStyleVals.contains s || s.startsWith "var(" do throwErrorAt ref s!"in `{p}`: invalid border style `{s}`"
        checkOrThrow (validateColorLiteral c)
      else throwErrorAt ref s!"`{p}` expects `none`, `0`, or `<width> <style> <color>` (e.g. `1px solid #ddd`), got `{resolvedVal}`"
  | .time => checkAtoms (fun a => unless isValidTimeAtom a do throwErrorAt ref s!"invalid duration `{a}` for `{p}` (expected e.g. `200ms` or `0.3s`)") atoms
  | .num | .any => checkAtoms (fun a => do
      if a.startsWith "#" && !Qed.isValidHexColor a then throwErrorAt ref s!"in `{p}`: invalid hex color `{a}`"
      if let some (fn, args) := Qed.parseFuncCall? a then if fn == "rgb" || fn == "rgba" then checkOrThrow (Qed.validateRgbArgs fn args)) atoms

@[noinline] private def resolveOneAtom (ref : Syntax) (env : Environment) (currNs : Name) (openDecls : List OpenDecl)
    (tokReg : NameMap TokenMetaInfo) (kfReg : NameMap KeyframesMetaInfo) (p : String) (propKind : CssPropKind) (a : String) : CoreM (String × List String × List String × List Name) := do
  if isIdentLike a then
    if let some tInfo := resolveInRegistry tokReg env currNs openDecls a then
      if tInfo.kind != "any" then
        if let some exp := match propKind with | .color => some "color" | .len => some "len" | .num => some "num" | .time => some "time" | _ => none then
          if tInfo.kind != exp then throwErrorAt ref s!"type mismatch in CSS `{p}`: token `{tInfo.fullName}` has kind `{tInfo.kind}`, expected `{exp}`"
      return (s!"var(--{tInfo.cssName})", [tInfo.cssName], [], tInfo.themeName?.toList)
    if p == "animation" || p == "animation-name" then
      if let some kfInfo := resolveInRegistry kfReg env currNs openDecls a then return (kfInfo.kfName, [], [kfInfo.rule], [])
  return (a, [], [], [])

@[noinline] private def resolveAndValidateDecl (ref : Syntax) (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (strictTokens : Bool) (prop rawVal : String) : CoreM ResolvedCssValue := do
  let p := prop.trimmed; let vRaw := rawVal.trimmed
  let v := if vRaw.endsWith ";" then (String.ofList vRaw.toList.dropLast).trimmed else vRaw
  if p.isEmpty then throwErrorAt ref "empty CSS property name"
  if v.isEmpty then throwErrorAt ref s!"missing value for CSS property `{p}`"
  let isCustom := p.startsWith "--"
  let propKind ← if isCustom then pure CssPropKind.any else match cssPropMap[p]? with | some k => pure k | none => throwErrorAt ref s!"unknown CSS property `{p}`{Qed.Diag.didYouMean p knownCssProps}"
  let (tokReg, kfReg) := (tokenMetaRegistry.getState env, keyframesMetaRegistry.getState env)
  let (outs, usedToks, extraRules, usedThemes) ← (Qed.splitTopLevel ' ' v).foldlM (init := (#[], [], [], [])) fun (outs, ts, rs, ths) a => do
    let (outA, t, r, th) ← resolveOneAtom ref env currNs openDecls tokReg kfReg p propKind a
    return (outs.push outA, ts ++ t, rs ++ r, ths ++ th)
  let resolvedAtoms := outs.toList; let resolvedVal := String.intercalate " " resolvedAtoms
  if !isCustom then checkStrictAndValidate ref strictTokens p resolvedVal propKind resolvedAtoms
  return .mk resolvedVal (usedToks ++ Qed.extractVarNames resolvedVal) extraRules.eraseDups usedThemes.eraseDups

private def atomText : Syntax → String | .node _ _ #[.atom _ v] | .atom _ v => v | _ => ""
private def stripTrailingColon (stx : Syntax) : String := (String.ofList (atomText stx).trimmed.toList.dropLast).trimmed
private def optDocComment (stx : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) := if (stx.getArg 0).getNumArgs == 1 then some ⟨(stx.getArg 0).getArg 0⟩ else none
private def getCssScope : CommandElabM (Environment × Name × List OpenDecl) := return (← getEnv, ← getCurrNamespace, (← getScope).openDecls)
private def splitFirstChar (sep : Char) (s : String) : Option (String × String) :=
  let (lhs, rhs) := s.toList.span (· != sep); match rhs with | c :: rest => if c == sep then some ((String.ofList lhs).trimmed, (String.ofList rest).trimmed) else none | _ => none
private structure CompiledCssBlock where mk :: (items : List Qed.Item) (usedTokens extraRules : List String) (themes : List Name)

mutual
  @[noinline] private partial def compileCssBlockItem (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (strictTokens : Bool)
      (seenProps : Array String) (stx : Syntax) : CoreM (Array String × Qed.Item × List String × List String × List Name) := do
    if stx.getKind == ``cssNestedBlock then
      let sel := stripTrailingColon (stx.getArg 0); if sel.isEmpty then throwErrorAt (stx.getArg 0) "empty nested CSS selector"
      let sub ← compileCssBlockItems env currNs openDecls strictTokens (stx.getArg 1).getArgs
      return (seenProps, .nest sel sub.items, sub.usedTokens, sub.extraRules, sub.themes)
    else if stx.getKind == ``cssSimpleDecl then
      let line := (atomText (stx.getArg 0)).trimmed
      let some (p, v) := splitFirstChar ':' line | throwErrorAt (stx.getArg 0) s!"expected CSS declaration `property: value`, got `{line}`"
      let propKey := p.trimmed
      if seenProps.contains propKey then throwErrorAt (stx.getArg 0) s!"duplicate CSS property `{propKey}` in the same style block (remove the redundant declaration)"
      let res ← resolveAndValidateDecl (stx.getArg 0) env currNs openDecls strictTokens p v
      return (seenProps.push propKey, .decl propKey res.cssText, res.usedTokens, res.extraRules, res.themes)
    else throwErrorAt stx s!"unexpected syntax in CSS block ({stx.getKind})"
  @[noinline] private partial def compileCssBlockItems (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (strictTokens : Bool) (stxs : Array Syntax) : CoreM CompiledCssBlock := do
    let (_, items, toks, rules, thms) ← stxs.toList.foldlM (init := (#[], #[], [], [], [])) fun (seen, its, ts, rs, ths) stx => do
      let (seen', it, t, r, th) ← compileCssBlockItem env currNs openDecls strictTokens seen stx
      return (seen', its.push it, ts ++ t, rs ++ r, ths ++ th)
    return .mk items.toList toks.eraseDups rules.eraseDups thms.eraseDups
end

private def toChunkedStrExpr (s : String) : Expr :=
  let rec go : Nat → List Char → Expr
    | 0, cs => toExpr (String.ofList cs)
    | fuel + 1, cs => match cs.drop 48 with | [] => toExpr (String.ofList cs) | rest => mkApp2 (mkConst ``String.append) (toExpr (String.ofList (cs.take 48))) (go fuel rest)
  if s.length ≤ 48 then toExpr s else go (s.length / 48 + 1) s.toList

private def toListExpr (ty : Expr) (xs : List Expr) : Expr := xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) (mkApp (mkConst ``List.nil [Level.zero]) ty)
private def toOptExpr (ty : Expr) : Option Expr → Expr | none => mkApp (mkConst ``Option.none [Level.zero]) ty | some e => mkApp2 (mkConst ``Option.some [Level.zero]) ty e
mutual
  private def toItemExpr : Qed.Item → Expr
    | .decl p v => mkApp2 (mkConst ``Qed.Item.decl) (toExpr p) (toExpr v)
    | .nest sel body => mkApp2 (mkConst ``Qed.Item.nest) (toExpr sel) (toItemListExpr body)
  private def toItemListExpr : List Qed.Item → Expr
    | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Qed.Item)
    | i :: is => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Qed.Item) (toItemExpr i) (toItemListExpr is)
end
private def toThemeColorEntryExpr (e : Qed.ThemeColorEntry) : Expr := mkApp3 (mkConst ``Qed.ThemeColorEntry.mk) (toExpr e.cssName) (toExpr e.lightRgb) (toExpr e.darkRgb?)
private def toStyleColorCheckExpr (c : Qed.StyleColorCheck) : Expr :=
  mkAppN (mkConst ``Qed.StyleColorCheck.mk) #[toExpr c.scope, toExpr c.fgCss, toExpr c.bgCss, toExpr c.fgRgb?, toExpr c.bgRgb?, toExpr c.fgTok?, toExpr c.bgTok?, toExpr c.forcedDark]
private def toFallbackBgOptExpr (fb? : Option Qed.ContrastFallbackBg) : Expr :=
  toOptExpr (mkConst ``Qed.ContrastFallbackBg) (fb?.map fun fb => mkApp3 (mkConst ``Qed.ContrastFallbackBg.mk) (toExpr fb.css) (toExpr fb.rgb?) (toExpr fb.tok?))
private def toStyleExpr (s : Qed.Style) : Expr :=
  mkAppN (mkConst ``Qed.Style.mk) #[toExpr s.className, toChunkedStrExpr s.raw, toItemListExpr s.items,
    toExpr s.usedTokens, toExpr s.extraRules, toExpr s.isGlobal, toListExpr (mkConst ``Qed.StyleColorCheck) (s.colorChecks.map toStyleColorCheckExpr),
    toListExpr (mkConst ``Qed.ThemeColorEntry) (s.themePalette.map toThemeColorEntryExpr)]
private def toThemeExpr (t : Qed.Theme) : Expr :=
  mkAppN (mkConst ``Qed.Theme.mk) #[toExpr t.name, toItemListExpr t.lightDecls, toItemListExpr t.darkDecls,
    toItemListExpr t.resets, toExpr t.definedTokens, toExpr t.darkTokens, toListExpr (mkConst ``Qed.ThemeColorEntry) (t.colorPalette.map toThemeColorEntryExpr)]
private def toKeyframesExpr (kf : Qed.Keyframes) : Expr :=
  let itemListTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``Qed.Item)
  let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) itemListTy
  mkApp2 (mkConst ``Qed.Keyframes.mk) (toExpr kf.name) (toListExpr pairTy (kf.steps.map fun (sel, body) =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) itemListTy (toExpr sel) (toItemListExpr body)))

private def rflBoolTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
private def mkBoolEqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e (mkConst ``Bool.true)

@[noinline] private def addClosedDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (nameId : Ident) (ty val : Expr) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ nameId.getId
  liftTermElabM do
    addAndCompile (.defnDecl { name := declName, levelParams := [], type := ty, value := val, hints := .regular 0, safety := .safe })
    enableRealizationsForConst declName; addDeclarationRangesFromSyntax declName nameId; addDocString' declName Syntax.missing doc?

@[noinline] private def addBoolTrueThm (ref : Syntax) (declName : Name) (boolExpr : Expr) : CommandElabM Unit := liftTermElabM do
  addDecl (.thmDecl { name := declName, levelParams := [], type := mkBoolEqTrue boolExpr, value := rflBoolTrue })
  addDeclarationRangesFromSyntax declName ref

private def checkBoolTrueKernel (e : Expr) : MetaM Bool := do
  match Kernel.isDefEq (← getEnv) (← getLCtx) e (mkConst ``Bool.true) with
  | .ok true => pure true
  | _ => isDefEq e (mkConst ``Bool.true)

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
    let some tInfo := resolveInRegistry (tokenMetaRegistry.getState env) env currNs openDecls idStr | throwErrorAt bgStx s!"unknown color token `{idStr}` in `on {idStr}`"
    unless tInfo.kind == "color" do throwErrorAt bgStx s!"token `{tInfo.fullName}` has kind `{tInfo.kind}`, expected `color` in `on {idStr}`"
    return ({ css := s!"var(--{tInfo.cssName})", rgb? := none, tok? := some tInfo.cssName }, tInfo.themeName?)

private def mkThemePaletteExpr (env : Environment) (themeNames : List Name) : Expr :=
  let entryTy := Lean.mkConst ``Qed.ThemeColorEntry
  let thConsts := themeNames.eraseDups.filterMap fun nm => ((themeMetaRegistry.getState env).find? nm).map (·.themeConst)
  match thConsts with
  | [] => mkApp (Lean.mkConst ``List.nil [Level.zero]) entryTy
  | c :: rest => rest.foldl (init := mkApp (Lean.mkConst ``Qed.Theme.colorPalette) (Lean.mkConst c)) fun acc n =>
      mkApp3 (Lean.mkConst ``List.append [Level.zero]) entryTy acc (mkApp (Lean.mkConst ``Qed.Theme.colorPalette) (Lean.mkConst n))

@[noinline] private def resolveStylesTargetExpr (target : Term) : CommandElabM Expr := liftTermElabM do
  let e ← elabTerm target none; synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if (← whnf (← inferType e)).isAppOf `Qed.App then mkProjection e `styles else pure e

@[noinline] private partial def reduceEvalStr (e : Expr) : MetaM String := do
  match ← whnf e with
  | .lit (.strVal s) => return s
  | w =>
      if w.isAppOfArity ``String.ofByteArray 2 then
        let rec evalBytes (b : Expr) : MetaM ByteArray := do
          let b := b.consumeMData; let a := b.getAppArgs
          if b.isAppOfArity ``HAppend.hAppend 6 then return (← evalBytes a[4]!) ++ (← evalBytes a[5]!)
          if b.isAppOfArity ``ByteArray.append 2 then return (← evalBytes a[0]!) ++ (← evalBytes a[1]!)
          if b.isAppOfArity ``String.toByteArray 1 || b.isAppOfArity ``String.toUTF8 1 then return (← reduceEvalStr b.appArg!).toUTF8
          throwError "failed to evaluate ByteArray"
        return String.fromUTF8! (← evalBytes w.getAppArgs[0]!)
      Lean.Meta.reduceEval w

@[noinline] private partial def reduceEvalViolations (e : Expr) : MetaM (List Qed.ContrastViolation) := do
  let w ← whnf e; if w.isAppOfArity ``List.nil 1 then return []
  if w.isAppOfArity ``List.cons 3 then
    let a := w.getAppArgs; let v ← whnf a[1]!
    if v.isAppOfArity ``Qed.ContrastViolation.mk 5 then
      let f := v.getAppArgs
      return { styleName := ← reduceEvalStr f[0]!, scope := ← reduceEvalStr f[1]!, fgCss := ← reduceEvalStr f[2]!, bgCss := ← reduceEvalStr f[3]!, ratioX100 := ← Lean.Meta.reduceEval f[4]! } :: (← reduceEvalViolations a[2]!)
  throwError "expected List ContrastViolation"

@[noinline] private def runContrastVerify (ref : Syntax) (minX100 : Nat) (violsExpr checkExpr : Expr) (thmName? : Option Name) : CommandElabM Unit := do
  let errStr ← liftTermElabM do try return Qed.formatContrastViolations minX100 (← reduceEvalViolations violsExpr) catch _ => pure ""
  unless errStr.isEmpty do throwErrorAt ref errStr
  match thmName? with
  | some nm => addBoolTrueThm ref nm checkExpr
  | none => unless ← liftTermElabM (checkBoolTrueKernel checkExpr) do throwErrorAt ref s!"WCAG contrast check failed (required >= {Qed.formatContrastX100 minX100})"

private def lookupThemeInfo (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (thId : Ident) : CoreM ThemeMetaInfo := do
  let some info := resolveInRegistry (themeMetaRegistry.getState env) env currNs openDecls thId.getId.toString | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
  return info

private def resolveOptContrastBg (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (optStx : Syntax) : CoreM (Option Qed.ContrastFallbackBg × Option Name) := do
  if optStx.getNumArgs == 2 then let (bg, th?) ← resolveContrastBgStx env currNs openDecls (optStx.getArg 1); return (some bg, th?)
  return (none, none)

@[noinline] def elabStyleDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (nameId : Ident) (extendsIds : Array Ident)
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
  let baked : Qed.Style := { className := cls, raw := rawCss, items := finalItems, usedTokens := allToks, extraRules := allExtra, colorChecks := Qed.collectStyleColorChecks none none false "" finalItems }
  let styleDecl := currNs ++ nameId.getId
  addClosedDef doc? nameId (mkConst ``Qed.Style) (toStyleExpr baked)
  modifyEnv fun e => styleMetaRegistry.addEntry e (.mk styleDecl finalItems allToks allExtra allThemes)
  if let some cStx := contrastOpt? then
    let minX100 ← liftCoreM <| parseContrastRatioStx (cStx.getArg 2)
    let (bgOpt?, extraTheme?) ← liftCoreM <| resolveOptContrastBg env currNs openDecls (cStx.getArg 3)
    unless baked.hasContrastPair bgOpt? do throwErrorAt cStx s!"`contrast >= {Qed.formatContrastX100 minX100}` on style `{nameId.getId}` requires both `color` and `background-color` (or `on <bg>`)."
    let (palE, bgE, styleE, minE) := (mkThemePaletteExpr env (allThemes ++ extraTheme?.toList).eraseDups, toFallbackBgOptExpr bgOpt?, Lean.mkConst styleDecl, toExpr minX100)
    runContrastVerify cStx minX100 (mkApp4 (mkConst ``Qed.Style.contrastViolations) minE palE bgE styleE) (mkApp4 (mkConst ``Qed.Style.checkContrast) minE palE bgE styleE) (some (styleDecl.appendAfter "_contrast"))

def extractStyleExtends (optStx : Syntax) : Array Ident := if optStx.getNumArgs == 1 then ((optStx.getArg 0).getArg 1).getSepArgs.map (⟨·⟩) else #[]
def extractOptChild (optStx : Syntax) : Option Syntax := if optStx.getNumArgs == 1 then some (optStx.getArg 0) else none

@[noinline, command_elab styleCmd] def elabStyleCmd : CommandElab := fun stx =>
  elabStyleDef (optDocComment stx) ⟨stx.getArg 2⟩ (extractStyleExtends (stx.getArg 3)) ((stx.getArg 4).getNumArgs == 1) (stx.getArg 7).getArgs (extractOptChild (stx.getArg 5))

@[noinline, command_elab keyframesCmd] def elabKeyframesCmd : CommandElab := fun stx => do
  let nameId : Ident := ⟨stx.getArg 2⟩; let kfName := Qed.sanitizeCssIdent nameId.getId.getString!; let (env, currNs, openDecls) ← getCssScope
  let steps ← (stx.getArg 4).getArgs.toList.mapM fun stepStx => do
    unless stepStx.getKind == ``cssNestedBlock do throwErrorAt stepStx "expected keyframe stop (`from:`, `to:`, or `50%:`)"
    return (stripTrailingColon (stepStx.getArg 0), (← liftCoreM <| compileCssBlockItems env currNs openDecls false (stepStx.getArg 1).getArgs).items)
  let kf : Qed.Keyframes := { name := kfName, steps }
  addClosedDef (optDocComment stx) nameId (mkConst ``Qed.Keyframes) (toKeyframesExpr kf)
  modifyEnv fun e => keyframesMetaRegistry.addEntry e (.mk (currNs ++ nameId.getId) kfName kf.rule)

private structure ThemeTokEntry where mk ::
  (ref : Syntax) (ident cssName kind lightCss : String) (lightRgb : Option (Nat × Nat × Nat) := none) (darkCss? : Option String := none) (darkRgb? : Option (Nat × Nat × Nat) := none)
deriving Inhabited
private structure ThemeContrastInv where mk :: (ref : Syntax) (invName fgName bgName : String) (minX100 : Nat)

private def parseAndValidateTokenLine (ref : Syntax) (line : String) : CoreM (String × String × String × Option (Nat × Nat × Nat)) := do
  let some (lhs, val) := splitFirstChar '=' line | throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"
  let [kind, nm] := Qed.splitTopLevel ' ' lhs | throwErrorAt ref s!"expected `<kind> <name> = <value>` in `theme`, got `{line}`"
  unless ["color", "len", "num", "font", "time"].contains kind do throwErrorAt ref s!"unknown theme token kind `{kind}` (expected `color`, `len`, `num`, `font`, or `time`)"
  unless isIdentLike nm && !nm.contains '.' do throwErrorAt ref s!"invalid theme token name `{nm}`"
  if val.isEmpty then throwErrorAt ref s!"missing value for token `{nm}`"
  let (cleanVal, rgb?) ← match kind with
    | "color" => match validateColorLiteral val with | .ok rgb? => pure (val, rgb?) | .error msg => throwErrorAt ref s!"invalid theme color value: {msg}"
    | "len"   => if !isValidLenAtom val then throwErrorAt ref s!"invalid theme length value `{val}`" else pure (val, none)
    | "num"   => if !Qed.isNumericString val then throwErrorAt ref s!"invalid theme numeric value `{val}`" else pure (val, none)
    | "time"  => if !isValidTimeAtom val then throwErrorAt ref s!"invalid theme time value `{val}`" else pure (val, none)
    | _       => pure (if val.startsWith "\"" && val.endsWith "\"" && val.length >= 2 then String.ofList (val.toList.drop 1 |>.dropLast) else val, none)
  return (kind, nm, cleanVal, rgb?)

private def parseContrastInvLine (ref : Syntax) (line : String) : CoreM ThemeContrastInv := do
  let some (lhs, rhs) := splitFirstChar ':' line | throwErrorAt ref s!"expected `invariant <name>: contrast(fg, bg) >= <ratio>`, got `{line}`"
  let ["invariant", invName] := Qed.splitTopLevel ' ' lhs | throwErrorAt ref s!"expected `invariant <name>: ...`, got `{lhs}`"
  let [c, t] := rhs.splitOn ">=" | throwErrorAt ref s!"expected `contrast(fg, bg) >= <ratio>`, got `{rhs}`"
  let some (fn, argsStr) := Qed.parseFuncCall? c.trimmed | throwErrorAt ref s!"expected `contrast(fg, bg)`, got `{c.trimmed}`"
  unless fn == "contrast" do throwErrorAt ref s!"expected `contrast(fg, bg)` in theme invariant, got `{fn}(...)`"
  let [fgName, bgName] := (Qed.splitTopLevel ',' argsStr).map String.trimmed | throwErrorAt ref s!"`contrast(...)` expects 2 token names, got `{argsStr}`"
  let some minX100 := parseDecimalX100 t.trimmed | throwErrorAt ref s!"invalid contrast threshold `{t.trimmed}` (expected e.g. `4.5`, `3.0`, or `7.0`)"
  return .mk ref invName fgName bgName minX100

private def toKebabCase (s : String) : String :=
  let cs := s.toList.flatMap fun c => if c.isUpper then ['-', c.toLower] else if c == '_' then ['-'] else [c]
  String.ofList (match cs with | '-' :: r => r | _ => cs)

@[noinline] private def emitOneThemeToken (themeNm fullThemeName : Name) (e : ThemeTokEntry) : CommandElabM Unit := do
  let (tyE, mkVal) : Expr × (String → Option (Nat × Nat × Nat) → Expr) := match e.kind with
    | "color" => (mkConst ``Qed.Color, fun s rgb? => mkApp2 (mkConst ``Qed.Color.mk) (toExpr s) (toExpr rgb?))
    | "len"   => (mkConst ``Qed.Len, fun s _ => mkApp (mkConst ``Qed.Len.mk) (toExpr s))
    | "num"   => (mkConst ``Qed.CssNum, fun s _ => mkApp (mkConst ``Qed.CssNum.mk) (toExpr s))
    | "time"  => (mkConst ``Qed.Time, fun s _ => mkApp (mkConst ``Qed.Time.mk) (toExpr s))
    | _       => (mkConst ``String, fun s _ => toExpr s)
  let valE := mkApp4 (mkConst ``Qed.TypedToken.mk) tyE (toExpr e.cssName) (toOptExpr tyE (some (mkVal e.lightCss e.lightRgb))) (toOptExpr tyE (e.darkCss?.map (mkVal · e.darkRgb?)))
  addClosedDef none (mkIdentFrom e.ref (themeNm ++ Name.mkSimple e.ident)) (mkApp (mkConst ``Qed.TypedToken) tyE) valE
  modifyEnv fun env' => tokenMetaRegistry.addEntry env' (.mk (fullThemeName ++ Name.mkSimple e.ident) e.cssName e.kind (some fullThemeName))

@[noinline] private def emitOneThemeContrastInv (fullThemeName : Name) (entries : Array ThemeTokEntry) (inv : ThemeContrastInv) : CommandElabM Unit := do
  let findTok (nm : String) : CommandElabM ThemeTokEntry := match entries.find? (·.ident == nm) with | some e => pure e | none => throwErrorAt inv.ref s!"unknown token `{nm}` in contrast invariant `{inv.invName}`"
  let (fgE, bgE) := (← findTok inv.fgName, ← findTok inv.bgName)
  unless fgE.kind == "color" && bgE.kind == "color" do throwErrorAt inv.ref s!"`contrast({inv.fgName}, {inv.bgName})` requires two `color` tokens"
  let checkMode (mode : String) (fg bg : Qed.Color) : CommandElabM Unit := do
    let ratio := Qed.Color.contrastX100 fg bg
    if ratio < inv.minX100 then throwErrorAt inv.ref s!"WCAG contrast invariant `{inv.invName}` failed in {mode} mode: contrast({inv.fgName}={fg.raw}, {inv.bgName}={bg.raw}) is {Qed.formatContrastX100 ratio}, required >= {Qed.formatContrastX100 inv.minX100}"
  checkMode "light" ⟨fgE.lightCss, fgE.lightRgb⟩ ⟨bgE.lightCss, bgE.lightRgb⟩
  if fgE.darkCss?.isSome || bgE.darkCss?.isSome then
    checkMode "dark" ⟨fgE.darkCss?.getD fgE.lightCss, fgE.darkRgb?.orElse fun _ => fgE.lightRgb⟩ ⟨bgE.darkCss?.getD bgE.lightCss, bgE.darkRgb?.orElse fun _ => bgE.lightRgb⟩
  addBoolTrueThm inv.ref (fullThemeName ++ Name.mkSimple inv.invName)
    (mkApp3 (mkConst ``Qed.TypedToken.wcagCheck) (mkConst (fullThemeName ++ Name.mkSimple inv.fgName)) (mkConst (fullThemeName ++ Name.mkSimple inv.bgName)) (toExpr inv.minX100))

@[noinline] private def processDarkItem (entries : Array ThemeTokEntry) (dStx : Syntax) : CoreM (Array ThemeTokEntry) := do
  unless dStx.getKind == ``cssSimpleDecl do throwErrorAt dStx "expected `<kind> <name> = <value>` inside `dark:`"
  let (kind, nm, cleanVal, rgb?) ← parseAndValidateTokenLine (dStx.getArg 0) (atomText (dStx.getArg 0)).trimmed
  let some idx := entries.findIdx? (·.ident == nm) | throwErrorAt (dStx.getArg 0) s!"dark override for unknown token `{nm}` (declare it in light mode first)"
  let prev := entries[idx]!
  unless prev.kind == kind do throwErrorAt (dStx.getArg 0) s!"dark override kind mismatch for `{nm}`: declared as `{prev.kind}`, overridden as `{kind}`"
  return entries.set! idx { prev with darkCss? := some cleanVal, darkRgb? := rgb? }

@[noinline] private def processThemeItem (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (themeNm : Name)
    (entries : Array ThemeTokEntry) (resets : List Qed.Item) (invs : Array ThemeContrastInv) (itemStx : Syntax) : CoreM (Array ThemeTokEntry × List Qed.Item × Array ThemeContrastInv) := do
  if itemStx.getKind == ``cssSimpleDecl then
    let line := (atomText (itemStx.getArg 0)).trimmed
    if line.startsWith "invariant " then return (entries, resets, invs.push (← parseContrastInvLine (itemStx.getArg 0) line))
    let (kind, nm, cleanVal, rgb?) ← parseAndValidateTokenLine (itemStx.getArg 0) line
    if entries.any (·.ident == nm) then throwErrorAt (itemStx.getArg 0) s!"duplicate token `{nm}` in theme `{themeNm}`"
    return (entries.push (.mk (itemStx.getArg 0) nm (toKebabCase nm) kind cleanVal rgb? none none), resets, invs)
  else if itemStx.getKind == ``cssNestedBlock then
    let hdr := stripTrailingColon (itemStx.getArg 0)
    if hdr == "dark" then return (← (itemStx.getArg 1).getArgs.toList.foldlM processDarkItem entries, resets, invs)
    else if hdr.startsWith "reset " then
      let compiled ← compileCssBlockItems env currNs openDecls false (itemStx.getArg 1).getArgs
      return (entries, resets ++ [.nest (String.ofList (hdr.toList.drop 6)).trimmed compiled.items], invs)
    else throwErrorAt (itemStx.getArg 0) s!"unknown section `{hdr}:` in `theme` (expected `dark:` or `reset <selector>:`)"
  else return (entries, resets, invs)

@[noinline, command_elab themeCmd] def elabThemeCmd : CommandElab := fun stx => do
  let themeId : Ident := ⟨stx.getArg 2⟩; let themeNm := themeId.getId; let (env, currNs, openDecls) ← getCssScope
  let (entries, resets, invs) ← liftCoreM <| (stx.getArg 4).getArgs.toList.foldlM (init := (#[], [], #[])) fun (es, rs, ivs) it => processThemeItem env currNs openDecls themeNm es rs ivs it
  let darkEntries := entries.toList.filter (·.darkCss?.isSome)
  let (lightDecls, darkDecls) := (entries.toList.map fun e => Qed.Item.decl ("--" ++ e.cssName) e.lightCss, darkEntries.map fun e => Qed.Item.decl ("--" ++ e.cssName) (e.darkCss?.getD ""))
  let colorPalette := entries.toList.filterMap fun e => if e.kind == "color" then e.lightRgb.map fun l => { cssName := e.cssName, lightRgb := l, darkRgb? := e.darkRgb? } else none
  let thVal : Qed.Theme := .mk themeNm.getString! lightDecls darkDecls resets (entries.toList.map (·.cssName)) (darkEntries.map (·.cssName)) colorPalette
  let fullThemeName := currNs ++ themeNm
  entries.toList.forM (emitOneThemeToken themeNm fullThemeName)
  addClosedDef (optDocComment stx) (mkIdentFrom themeId (themeNm ++ `theme)) (mkConst ``Qed.Theme) (toThemeExpr thVal)
  addClosedDef none (mkIdentFrom themeId (themeNm ++ `style)) (mkConst ``Qed.Style) (toStyleExpr thVal.asStyle)
  invs.toList.forM (emitOneThemeContrastInv fullThemeName entries)
  modifyEnv fun env' => themeMetaRegistry.addEntry env' (.mk fullThemeName (fullThemeName ++ `style) (fullThemeName ++ `theme))

@[noinline] private partial def reduceEvalStrList (e : Expr) : MetaM (List String) := do
  let w ← whnf e
  if w.isAppOfArity ``List.nil 1 then return []
  if w.isAppOfArity ``List.cons 3 then let a := w.getAppArgs; return (← reduceEvalStr a[1]!) :: (← reduceEvalStrList a[2]!)
  throwError "expected List String"

@[noinline, command_elab verifyThemeCmd] def elabVerifyThemeCmd : CommandElab := fun stx => do
  let (thId, target) : Ident × Term := (⟨stx.getArg 1⟩, ⟨stx.getArg 3⟩); let (env, currNs, openDecls) ← getCssScope
  let thInfo ← liftCoreM <| lookupThemeInfo env currNs openDecls thId
  let stylesExpr ← resolveStylesTargetExpr target; let thExpr := Lean.mkConst thInfo.themeConst
  unless ← liftTermElabM (checkBoolTrueKernel (mkApp2 (mkConst ``Qed.Theme.coversAll) thExpr stylesExpr)) do
    let missingStr ← liftTermElabM do
      try return "[" ++ String.intercalate ", " ((← reduceEvalStrList (mkApp2 (mkConst ``Qed.Theme.missingTokens) thExpr stylesExpr)).map fun s => s!"\"{s}\"") ++ "]"
      catch _ => return "(unknown)"
    throwErrorAt stx s!"theme `{thId.getId}` does not define all CSS tokens used by `{(target.raw.unsetTrailing.reprint.getD "target").trimmed}`.\n  Missing tokens: {missingStr}\nAdd them to `theme {thId.getId}:`."

@[noinline, command_elab verifyContrastCmd] def elabVerifyContrastCmd : CommandElab := fun stx => do
  let minX100 ← liftCoreM <| parseContrastRatioStx (stx.getArg 2); let (env, currNs, openDecls) ← getCssScope
  let themeNames0 ← if (stx.getArg 5).getNumArgs == 2 then do pure [(← liftCoreM <| lookupThemeInfo env currNs openDecls ⟨(stx.getArg 5).getArg 1⟩).fullName] else pure []
  let (bgOpt?, extraTh?) ← liftCoreM <| resolveOptContrastBg env currNs openDecls (stx.getArg 6)
  let (stylesE, palE, bgE, minE) := (← resolveStylesTargetExpr ⟨stx.getArg 4⟩, mkThemePaletteExpr env (themeNames0 ++ extraTh?.toList), toFallbackBgOptExpr bgOpt?, toExpr minX100)
  runContrastVerify stx minX100 (mkApp4 (mkConst ``Qed.findStylesContrastViolations) minE palE bgE stylesE) (mkApp4 (mkConst ``Qed.checkStylesContrast) minE palE bgE stylesE) none

end Qed.StyleDsl
