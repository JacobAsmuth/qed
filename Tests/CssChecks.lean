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

#guard ["brand", "space-md"].all AppTheme.theme.definedTokens.contains &&
  AppTheme.theme.darkComplete && AppTheme.style.isGlobal &&
  let css := AppTheme.style.raw
  [":root {", "@media (prefers-color-scheme: dark)", "[data-theme=\"dark\"]",
   ":where(*) { box-sizing: border-box; margin: 0; }"].all (css.contains ·)

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

-- Readable dev class names, Option A merge, auto-attached keyframes & token tracking
#guard baseBtn.className.startsWith "qed-baseBtn-" && primaryBtn.className.startsWith "qed-primaryBtn-" &&
  let css := primaryBtn.raw
  (["background-color: var(--brand);", "border: 1px solid var(--brand);",
    "&:hover { opacity: 1; transform: translateY(-1px); }",
    "@media (max-width: 600px) { width: 100%; }"].all (css.contains ·)) &&
  !css.contains "#d1d5db" &&
  primaryBtn.extraRules.any (·.contains "@keyframes fadeIn") &&
  ["brand", "space-md"].all primaryBtn.usedTokens.contains

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

/-! ## 4. Modern CSS Features, Safe Dynamic Inline Styles & `Theme.render` At-Rules -/

style modernStyle:
  box-sizing: border-box
  display: inline-flex
  flex-wrap: wrap
  cursor: pointer
  overflow: hidden
  text-decoration: underline
  white-space: nowrap
  min-height: 100dvh
  max-width: 65ch
  width: clamp(20rem, 50vw, 45rem)
  color: oklch(0.6 0.15 250)
  background-color: rgb(255, 255, 255)
  &:hover:
    opacity: 0.85
  &:focus-visible:
    outline: 2px solid AppTheme.brand
  @media (prefers-color-scheme: dark):
    background-color: #111827

#guard let css := modernStyle.raw
  ["box-sizing: border-box;", "min-height: 100dvh;", "clamp(20rem, 50vw, 45rem)",
   "&:hover { opacity: 0.85; }", "@media (prefers-color-scheme: dark)"].all (css.contains ·)

-- Extending an undeclared style fails at compile time
/-- error: unknown style `noSuchStyle` in `extends` (declare it with `style noSuchStyle:`) -/
#guard_msgs in
style badExtends extends noSuchStyle:
  color: #ffffff

-- `renderThemeRule` does not wrap `@media` / `@keyframes` in `:where(...)`
#guard let r := renderThemeRule (.nest "@media (prefers-color-scheme: dark)" [color (hex "fff")])
  !r.contains ":where(" && r.contains "@media (prefers-color-scheme: dark)"

-- Safe dynamic inline styles sanitize `<`, `>`, quotes, and `/*`
#guard let s := inlineStyleStr [background "red\" onclick=\"x\"/*evil*/</style>"]
  ["<", "\"", "/*"].all (!s.contains ·)

/-! ## 5. Component-Colocated `style`, `stylesheet`, Discovery & Invariants -/

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

  style progressBox:
    padding: 0.5rem
    margin-top: 1rem

  action toggle: active = not active

  invariant activeValid: roleHasOneOf("toggle", [pillActive, pill])
  invariant exclusive:   noConflictingStyles([pillActive, pill])

  view:
    <div {shell}>
      <StyledCard title="Verified CSS"/>
      <button role="toggle" {pillActive if active else pill} onClick={.toggle}>Toggle</button>
      <div {progressBox}
           {inlineStyle([width(pct(progress))])}
           {styleVars([cssVar(AppTheme.brand, hex("0055aa"))])}>
        Progress: {progress}%
      </div>
    </div>

-- Verify auto-discovery collected: AppTheme.style, StyledCard.wrapper, shell, pill, pillActive, progressBox
#guard let css := renderStyleSheet StyledShowcase.app.styles
  [":root {", "@media (prefers-color-scheme: dark)", StyledCard.wrapper.className,
   StyledShowcase.shell.className, StyledShowcase.pillActive.className,
   "border-radius: 999px;", "padding: 0.5rem; margin-top: 1rem;"].all (css.contains ·)
-- External stylesheet linked in SSR HTML `<head>`
#guard StyledShowcase.app.stylesheets == ["/app.css"]
#guard (renderDocument "Demo" "" (stylesheets := StyledShowcase.app.stylesheets)).contains "<link rel=\"stylesheet\" href=\"/app.css\">"
#guard (StyledShowcase.app.ssrStep "/" "Demo" "/qed.js" "").contains "/app.css"

/-! ## 6. Kernel-Verified Theme Completeness (`verify_theme`) -/

verify_theme AppTheme for StyledShowcase.app

-- Missing token fails `verify_theme` with the exact missing token name!
theme OtherTheme:
  color doesNotExist = #123456

style orphanStyle:
  color: OtherTheme.doesNotExist

/-- error: theme `AppTheme` does not define all CSS tokens used by `[orphanStyle]`.
  Missing tokens: ["does-not-exist"]
Add them to `theme AppTheme:`. -/
#guard_msgs in
verify_theme AppTheme for [orphanStyle]

end CssChecks
