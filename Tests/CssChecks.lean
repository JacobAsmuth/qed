import Qed.Lang
import Qed.Html
import Qed.Notation
import Qed.Render
import Qed.Runtime
import Qed.Invariant
import Qed.Json
import Qed.Router
import Qed.Component
import Qed.Jsx
import Qed.Ssr
import Qed.Style

open Qed

namespace CssChecks

/-! ## 1. First-class `theme` with Typed Tokens, Dark Mode, Resets & WCAG Contrast Proofs -/

theme AppTheme:
  color brand   = #0055aa
  color surface = #ffffff
  color text    = #111827
  color muted   = #4b5563
  len   spaceSm = 0.5rem
  len   spaceMd = 1rem
  len   radius  = 8px
  num   lineH   = 1.5
  font  sans    = system-ui, sans-serif
  time  fast    = 150ms

  dark:
    color brand   = #60a5fa
    color surface = #111827
    color text    = #f9fafb
    color muted   = #d1d5db

  reset *:
    box-sizing: border-box
    margin: 0

  invariant textReadable:  contrast(text, surface) >= 4.5
  invariant brandReadable: contrast(brand, surface) >= 4.5
  invariant mutedReadable: contrast(muted, surface) >= 4.5

#guard AppTheme.theme.definedTokens.contains "brand"
#guard AppTheme.theme.definedTokens.contains "space-md"
#guard AppTheme.theme.darkComplete == true
#guard AppTheme.style.isGlobal == true
#guard AppTheme.style.raw.contains ":root {"
#guard AppTheme.style.raw.contains "@media (prefers-color-scheme: dark)"
#guard AppTheme.style.raw.contains "[data-theme=\"dark\"]"
#guard AppTheme.style.raw.contains ":where(*) { box-sizing: border-box; margin: 0; }"

-- WCAG contrast checks fail at compile time with exact ratio diagnostics
/-- error: WCAG contrast invariant `badContrast` failed in light mode: contrast(fg=#777777, bg=#ffffff) is 4.47:1, required >= 4.50:1 -/
#guard_msgs in
theme BadLightTheme:
  color fg = #777777
  color bg = #ffffff
  invariant badContrast: contrast(fg, bg) >= 4.5

/-- error: WCAG contrast invariant `badDark` failed in dark mode: contrast(fg=#222222, bg=#111111) is 1.18:1, required >= 4.50:1 -/
#guard_msgs in
theme BadDarkTheme:
  color fg = #111111
  color bg = #ffffff
  dark:
    color fg = #222222
    color bg = #111111
  invariant badDark: contrast(fg, bg) >= 4.5

/-! ## 2. First-class `keyframes` -/

keyframes fadeIn:
  from:
    opacity: 0
    transform: translateY(4px)
  to:
    opacity: 1
    transform: translateY(0)

#guard fadeIn.rule == "@keyframes fadeIn { from { opacity: 0; transform: translateY(4px); } to { opacity: 1; transform: translateY(0); } }"

/-! ## 3. First-class `style` DSL, Nesting, Option A `extends`, & `strict_tokens` -/

style baseBtn:
  display: inline-flex
  align-items: center
  padding: AppTheme.spaceSm AppTheme.spaceMd
  border-radius: AppTheme.radius
  border: 1px solid #d1d5db
  cursor: pointer
  font-family: AppTheme.sans
  &:hover:
    opacity: 0.9
  &:focus-visible:
    outline: 2px solid AppTheme.brand

style primaryBtn extends baseBtn:
  background-color: AppTheme.brand
  color: #ffffff
  border: 1px solid AppTheme.brand
  animation: fadeIn 200ms ease-out
  &:hover:
    opacity: 1
    transform: translateY(-1px)
  @media (max-width: 600px):
    width: 100%

style strictCard strict_tokens:
  padding: AppTheme.spaceMd
  background-color: AppTheme.surface
  color: AppTheme.text
  border-radius: AppTheme.radius
  margin: 0 auto
  max-width: 100%

-- Readable dev class names
#guard baseBtn.className.startsWith "qed-baseBtn-"
#guard primaryBtn.className.startsWith "qed-primaryBtn-"
-- Deterministic Option A merge: `border` overridden, `&:hover` merged recursively
#guard primaryBtn.raw.contains "background-color: var(--brand);"
#guard primaryBtn.raw.contains "border: 1px solid var(--brand);"
#guard !primaryBtn.raw.contains "#d1d5db"
#guard primaryBtn.raw.contains "&:hover { opacity: 1; transform: translateY(-1px); }"
#guard primaryBtn.raw.contains "@media (max-width: 600px) { width: 100%; }"
-- Keyframes auto-attached to `extraRules`
#guard primaryBtn.extraRules.any (·.contains "@keyframes fadeIn")
-- Token references tracked on Style
#guard primaryBtn.usedTokens.contains "brand"
#guard primaryBtn.usedTokens.contains "space-md"

-- Compile-time CSS validation error checks
/-- error: unknown CSS property `border-raduis` (did you mean `border-radius`?) -/
#guard_msgs in
style badPropTypo:
  border-raduis: 8px

/-- error: type mismatch in CSS `padding`: token `CssChecks.AppTheme.brand` has kind `color`, expected `len` -/
#guard_msgs in
style badTokenType:
  padding: AppTheme.brand

/-- error: in `color`: invalid hex color `#xyz` (expected 3, 4, 6, or 8 hex digits, e.g. `#06c` or `#2563eb`) -/
#guard_msgs in
style badHexLit:
  color: #xyz

/-- error: in `color`: `rgb(300, 0, 0)`: channel value `300` is out of range (must be 0..255) -/
#guard_msgs in
style badRgbLit:
  color: rgb(300, 0, 0)

/-- error: `strict_tokens` violation on `color`: raw color `#ffffff` is disallowed; use a `theme` color token instead -/
#guard_msgs in
style badStrictColor strict_tokens:
  color: #ffffff

/-- error: `strict_tokens` violation on `padding`: raw length `12px` is disallowed; use a `theme` length token instead -/
#guard_msgs in
style badStrictLen strict_tokens:
  padding: 12px

/-! ## 4. Typed Enums, Modern Units, Safe Dynamic Inline Styles & `renderTheme` At-Rules -/

def modernCombinatorStyle : Style := css [
  boxSizing .borderBox,
  display .inlineFlex,
  flexWrap .wrap,
  cursor .pointer,
  overflow .hidden,
  textDecoration .underline,
  whiteSpace .nowrap,
  minHeight (dvh 100),
  maxWidth (ch 65),
  width (clamp (rem 20) (vw 50) (rem 45)),
  color (oklch 0.6 0.15 250),
  backgroundColor (rgb8 255 255 255),
  hover [ opacity 0.85 ],
  focusVisible [ outline (px 2) .solid AppTheme.brand ],
  dark [ backgroundColor (hex "111827") ]
]

#guard modernCombinatorStyle.raw.contains "box-sizing: border-box;"
#guard modernCombinatorStyle.raw.contains "min-height: 100dvh;"
#guard modernCombinatorStyle.raw.contains "clamp(20rem, 50vw, 45rem)"
#guard modernCombinatorStyle.raw.contains "&:hover { opacity: 0.85; }"
#guard modernCombinatorStyle.raw.contains "@media (prefers-color-scheme: dark)"

-- `renderTheme` no longer wraps `@media` / `@keyframes` in `:where(...)`
#guard !(renderTheme [media "(prefers-color-scheme: dark)" [color (hex "fff")]]).contains ":where("
#guard (renderTheme [media "(prefers-color-scheme: dark)" [color (hex "fff")]]).contains "@media (prefers-color-scheme: dark)"

-- Safe dynamic inline styles sanitize `<`, `>`, quotes, and `/*`
#guard !(inlineStyleStr [background "red\" onclick=\"x\"/*evil*/</style>"]).contains "<"
#guard !(inlineStyleStr [background "red\" onclick=\"x\"/*evil*/</style>"]).contains "\""
#guard !(inlineStyleStr [background "red\" onclick=\"x\"/*evil*/</style>"]).contains "/*"

-- Parameterized style helper (now discovered by `Registry.lean`!)
def badgeStyle (bg : Color) : Style :=
  cssNamed "badge" [ backgroundColor bg, color .white, padding (px 2) (px 8), borderRadius (px 999) ]

/-! ## 5. Component-Colocated `style`, `stylesheet`, Inline `css:`, Discovery & Invariants -/

component StyledCard:
  prop title : String
  style wrapper:
    padding: AppTheme.spaceMd
    background-color: AppTheme.surface
    color: AppTheme.text
    border-radius: AppTheme.radius
  view:
    <article {wrapper}>
      <h2>{title}</h2>
    </article>

component StyledShowcase:
  stylesheet "app.css"
  state active   : Bool = false
  state progress : Nat  = 40

  style shell:
    max-width: 40rem
    margin: 2rem auto
    font-family: AppTheme.sans
    line-height: AppTheme.lineH

  style pill extends baseBtn:
    border-radius: 999px

  style pillActive extends pill:
    background-color: AppTheme.brand
    color: #ffffff

  action toggle: active = not active

  invariant activeValid: roleHasOneOf("toggle", [pillActive, pill])
  invariant exclusive:   noConflictingStyles([pillActive, pill])

  view:
    <div {shell}>
      <StyledCard title="Verified CSS"/>
      <button role="toggle" {pillActive if active else pill} onClick={.toggle}>Toggle</button>
      <span {badgeStyle(hex("0055aa"))}>Parameterized</span>
      <div {css: padding: 0.5rem; margin-top: 1rem}
           {inlineStyle([width(pct(progress))])}
           {styleVars([cssVar(AppTheme.brand, hex("0055aa"))])}>
        Progress: {progress}%
      </div>
    </div>

-- Verify auto-discovery collected: AppTheme.style, StyledCard.wrapper, shell, pill, pillActive,
-- parameterized `badgeStyle (hex "0055aa")`, AND inline `{css: padding: 0.5rem; margin-top: 1rem}`!
#guard (renderStyleSheet StyledShowcase.app.styles).contains ":root {"
#guard (renderStyleSheet StyledShowcase.app.styles).contains "@media (prefers-color-scheme: dark)"
#guard (renderStyleSheet StyledShowcase.app.styles).contains StyledCard.wrapper.className
#guard (renderStyleSheet StyledShowcase.app.styles).contains StyledShowcase.shell.className
#guard (renderStyleSheet StyledShowcase.app.styles).contains StyledShowcase.pillActive.className
#guard (renderStyleSheet StyledShowcase.app.styles).contains "border-radius: 999px;"
#guard (renderStyleSheet StyledShowcase.app.styles).contains "padding: 0.5rem; margin-top: 1rem;"
-- External stylesheet linked in SSR HTML `<head>`
#guard StyledShowcase.app.stylesheets == ["/app.css"]
#guard (renderDocument "Demo" "" (stylesheets := StyledShowcase.app.stylesheets)).contains "<link rel=\"stylesheet\" href=\"/app.css\">"
#guard (StyledShowcase.app.ssrStep "/" "Demo" "/qed.js" "").contains "/app.css"

/-! ## 6. Kernel-Verified Theme Completeness (`verify_theme`) -/

verify_theme AppTheme for StyledShowcase.app

-- Missing token fails `verify_theme` with the exact missing token name!
def orphanTok : Token := token "does-not-exist"
def orphanStyle : Style := css [ color orphanTok ]

/-- error: theme `AppTheme` does not define all CSS tokens used by `[orphanStyle]`.
  Missing tokens: ["does-not-exist"]
Add them to `theme AppTheme:`. -/
#guard_msgs in
verify_theme AppTheme for [orphanStyle]

end CssChecks
