import Qed
import QedTests.CheckHelper
open Qed

namespace CssChecks
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
example : (["brand", "space-md"].all AppTheme.theme.definedTokens.contains && AppTheme.theme.darkComplete && AppTheme.style.isGlobal &&
  [":root {", "@media (prefers-color-scheme: dark)", "[data-theme=\"dark\"]", ":where(*) { box-sizing: border-box; margin: 0; }"].all (Qed.Str.contains AppTheme.style.raw ·)) = true := by decide +kernel
expect_err "WCAG contrast invariant `badContrast` failed in light mode: contrast(fg=#777777, bg=#ffffff) is 4.47:1, required >= 4.50:1" in
theme BadLightTheme:
  color fg = #777777
  color bg = #ffffff
  invariant badContrast: contrast(fg, bg) >= 4.5
expect_err "WCAG contrast invariant `badDark` failed in dark mode: contrast(fg=#222222, bg=#111111) is 1.18:1, required >= 4.50:1" in
theme BadDarkTheme:
  color fg = #111111
  color bg = #ffffff
  dark:
    color fg = #222222
    color bg = #111111
  invariant badDark: contrast(fg, bg) >= 4.5
keyframes fadeIn:
  from:
    opacity: 0
    transform: translateY(4px)
  to:
    opacity: 1
    transform: translateY(0)
example : fadeIn.rule = "@keyframes fadeIn { from { opacity: 0; transform: translateY(4px); } to { opacity: 1; transform: translateY(0); } }" := by decide +kernel
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
example : (Qed.Str.startsWith baseBtn.className "qed-baseBtn-" && Qed.Str.startsWith primaryBtn.className "qed-primaryBtn-" &&
  ["background-color: var(--brand);", "border: 1px solid var(--brand);", "&:hover { opacity: 1; transform: translateY(-1px); }",
   "@media (max-width: 600px) { width: 100%; }"].all (Qed.Str.contains primaryBtn.raw ·) &&
  !Qed.Str.contains primaryBtn.raw "#d1d5db" && primaryBtn.extraRules.any (Qed.Str.contains · "@keyframes fadeIn") &&
  ["brand", "space-md"].all primaryBtn.usedTokens.contains) = true := by decide +kernel
bad_style "unknown CSS property `border-raduis` (did you mean `border-radius`?)" badPropTypo : border-raduis: 8px
bad_style "type mismatch in CSS `padding`: token `CssChecks.AppTheme.brand` has kind `color`, expected `len`" badTokenType : padding: AppTheme.brand
bad_style "in `color`: invalid hex color `#xyz`" badHexLit : color: #xyz
bad_style "in `color`: `rgb(300, 0, 0)`: channel value `300` is out of range (must be 0..255)" badRgbLit : color: rgb(300, 0, 0)
bad_style_strict "`strict_tokens` violation on `color`: raw color `#ffffff` is disallowed" badStrictColor : color: #ffffff
bad_style_strict "`strict_tokens` violation on `padding`: raw length `12px` is disallowed" badStrictLen : padding: 12px
style modernStyle:
  box-sizing: border-box
  flex-wrap: wrap
  overflow: hidden
  text-decoration: underline
  white-space: nowrap
  min-height: 100dvh
  max-width: 65ch
  width: clamp(20rem, 50vw, 45rem)
  color: oklch(0.6 0.15 250)
  background-color: rgb(255, 255, 255)
  @media (prefers-color-scheme: dark):
    background-color: #111827
example : (["box-sizing: border-box;", "min-height: 100dvh;", "clamp(20rem, 50vw, 45rem)",
   "oklch(0.6 0.15 250)", "@media (prefers-color-scheme: dark)"].all (Qed.Str.contains modernStyle.raw ·)) = true := by decide +kernel
expect_err "unknown style `noSuchStyle` in `extends`" in
style badExtends extends noSuchStyle:
  color: #ffffff
example : (let r := renderThemeRule (.nest "@media (prefers-color-scheme: dark)" [color (hex "fff")])
  !Qed.Str.contains r ":where(" && Qed.Str.contains r "@media (prefers-color-scheme: dark)" &&
  ["<", "\"", "/*"].all (!Qed.Str.contains (inlineStyleStr [background "red\" onclick=\"x\"/*evil*/</style>"]) ·)) = true := by decide +kernel
component StyledCard:
  prop title : String
  style wrapper:
    padding: AppTheme.spaceMd
    background-color: AppTheme.surface
    color: AppTheme.text
    border-radius: AppTheme.radius
  view: <article {wrapper}><h2>{title}</h2></article>
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
  view: <div {shell}><StyledCard title="Verified CSS"/><button role="toggle" {pillActive if active else pill} onClick={.toggle}>Toggle</button><div {progressBox} {inlineStyle([width(pct(progress))])} {styleVars([cssVar(AppTheme.brand, hex("0055aa"))])}>Progress: {progress}%</div></div>
example : (let css := renderStyleSheet StyledShowcase.app.styles
  [":root {", "@media (prefers-color-scheme: dark)", StyledCard.wrapper.className, StyledShowcase.shell.className,
   StyledShowcase.pillActive.className, "border-radius: 999px;", "padding: 0.5rem; margin-top: 1rem;"].all (Qed.Str.contains css ·) &&
  StyledShowcase.app.stylesheets == ["/app.css"] &&
  Qed.Str.contains (renderDocument "Demo" "" (stylesheets := StyledShowcase.app.stylesheets)) "<link rel=\"stylesheet\" href=\"/app.css\">" &&
  Qed.Str.contains (StyledShowcase.app.ssrStep "/" "Demo" "/qed.js" "") "/app.css") = true := by decide +kernel
verify_theme AppTheme for StyledShowcase.app
theme OtherTheme:
  color doesNotExist = #123456
style orphanStyle:
  color: OtherTheme.doesNotExist
expect_err "theme `AppTheme` does not define all CSS tokens used by `[orphanStyle]`.\n  Missing tokens: [\"does-not-exist\"]" in
verify_theme AppTheme for [orphanStyle]

-- ── Style & Stylesheet WCAG Contrast Verification ──
style goodContrastBtn extends baseBtn contrast >= 4.5:
  color: #ffffff
  background-color: #15694b
  &:hover:
    background-color: #0d4a34

style goodThemedCard contrast >= 4.5:
  color: AppTheme.text
  background-color: AppTheme.surface

style goodFgOnlyLabel contrast >= 4.5 on AppTheme.surface:
  color: AppTheme.muted

style goodRgbPill contrast >= 4.5:
  color: rgb(255, 255, 255)
  background-color: rgb(20, 21, 24)

component ContrastCard:
  style body contrast >= 4.5:
    color: AppTheme.text
    background-color: AppTheme.surface
  view: <div {body}>Readable</div>

example := (goodContrastBtn_contrast, goodThemedCard_contrast, goodFgOnlyLabel_contrast, goodRgbPill_contrast, ContrastCard.body_contrast)

verify_contrast >= 4.5 for StyledShowcase.app with AppTheme
verify_contrast >= 4.5 for [goodContrastBtn, goodThemedCard, goodRgbPill, primaryBtn, strictCard] with AppTheme
verify_contrast >= 4.5 for [goodFgOnlyLabel] with AppTheme on AppTheme.surface

expect_err "WCAG contrast check failed (required >= 4.50:1):\n  • style `qed-lowContrastBtn-" in
style lowContrastBtn contrast >= 4.5:
  color: #888888
  background-color: #ffffff

expect_err "WCAG contrast check failed (required >= 4.50:1):\n  • style `qed-badHoverContrast-" in
style badHoverContrast contrast >= 4.5:
  color: #ffffff
  background-color: #141518
  &:hover:
    background-color: #cccccc

theme SplitContrastTheme:
  color ink = #111827
  color bg  = #ffffff
  dark:
    color ink = #222222
    color bg  = #111111

expect_err "(dark): color `var(--ink)` on background-color `var(--bg)` is 1.18:1" in
style badDarkModeBtn contrast >= 4.5:
  color: SplitContrastTheme.ink
  background-color: SplitContrastTheme.bg

expect_err "`contrast >= 4.50:1` on style `fgOnlyMissingBg` requires both `color` and `background-color` (or `on <bg>`)." in
style fgOnlyMissingBg contrast >= 4.5:
  color: #141518

style badVerifyBtn:
  color: #999999
  background-color: #ffffff

expect_err "is 2.84:1" in
verify_contrast >= 4.5 for [goodContrastBtn, badVerifyBtn]

end CssChecks
