# Styling & Verified CSS

Qed provides a first-class, compile-time-verified CSS DSL that matches the indentation style of `component`, `schema`, `router`, and `server`—while compiling down to zero-runtime baked `Style` literals, build-time extracted `styles.css`, and Lean kernel proofs for CSS safety, theme completeness, and WCAG contrast.

## 1. First-class `style` blocks

Write scoped CSS using native CSS syntax with indentation nesting for pseudo-classes, pseudo-elements, and at-rules like `@media`, `@container`, and `@supports`:

```lean
style card:
  padding: 1rem 1.25rem
  border: 1px solid #ddd
  border-radius: 8px
  &:hover:
    border-color: AppTheme.brand
  @media (max-width: 600px):
    padding: 0.75rem
```

Every `style` block is validated at compile time:
- Unknown CSS properties fail with "did you mean" suggestions, such as `border-raduis` → `border-radius`.
- Keyword properties like `display`, `position`, `cursor`, `overflow`, and `box-sizing`, hex colors `#rgb`/`#rrggbb`, `rgb(0..255, …)`, lengths in `px`, `rem`, `em`, `%`, `dvh`, `clamp(…)`, and `calc(…)`, and typed design tokens are checked before any code runs.
- Each `style` bakes its scoped class name `qed-card-<hash>` and rendered CSS string at elaboration time—zero runtime hashing in JS.

### Deterministic composition with `extends`

Compose styles deterministically without cascade-order surprises:

```lean
style baseBtn:
  display: inline-flex
  padding: 0.5rem 1rem
  border: 1px solid #d1d5db
  border-radius: 8px
  cursor: pointer
  &:hover:
    opacity: 0.9

style primaryBtn extends baseBtn:
  background-color: AppTheme.brand
  color: #ffffff
  border: 1px solid AppTheme.brand
  &:hover:
    opacity: 1
    transform: translateY(-1px)
```

`extends` merges declarations and matching nested selectors recursively at compile time into a single scoped class, so later declarations always override earlier ones regardless of import order.

### Component-colocated styles, `theme`, and external `stylesheet`s

Declare styles directly inside a `component` alongside its state, invariants, and `view`:

```lean
component BookCard:
  prop book : Book
  stylesheet "app.css"
  style card:
    padding: AppTheme.spaceMd
    background-color: AppTheme.surface
    border-radius: AppTheme.radius
  view:
    <article {card}>
      <h2>{book.title}</h2>
    </article>
```

Every top-level or component-colocated `style` block referenced by your app is automatically discovered and included in `app.styles`.

## 2. Typed `theme` & WCAG contrast proofs

Define typed design tokens—`color`, `len`, `num`, `font`, and `time`—dark-mode overrides via `@media (prefers-color-scheme: dark)` and `[data-theme="dark"]`, element resets, and kernel-verified WCAG 2.1 contrast invariants in one place:

```lean
theme AppTheme:
  color brand   = #0055aa
  color surface = #ffffff
  color text    = #111827
  len   spaceMd = 1rem
  num   lineH   = 1.5
  font  sans    = system-ui, sans-serif

  dark:
    color brand   = #60a5fa
    color surface = #111827
    color text    = #f9fafb

  reset *:
    box-sizing: border-box
    margin: 0

  invariant readable:      contrast(text, surface) >= 4.5
  invariant brandReadable: contrast(brand, surface) >= 4.5
```

- **Type-safe tokens:** Using a `color` token in `padding:` is a compile error.
- **Automatic `<head>` injection:** Any component referencing `AppTheme.*` automatically includes `AppTheme.style` in its stylesheet, emitted into `<head>` on SSR and `styles.css` on build.
- **Light + dark WCAG proofs:** `contrast(fg, bg) >= 4.5` proves WCAG 2.1 contrast in Lean's kernel across *both* light and dark modes, reporting the exact ratio on failure.

## 3. `keyframes`

```lean
keyframes fadeIn:
  from:
    opacity: 0
    transform: translateY(4px)
  to:
    opacity: 1
    transform: translateY(0)
```

Referencing `fadeIn` in `animation: fadeIn 200ms ease-out` automatically bundles `@keyframes fadeIn { ... }` into the stylesheet.

## 4. Safe dynamic inline styles & CSS variables

For state-driven values like progress widths or dynamic CSS variables, use sanitized `inlineStyle` and `styleVars`, proved free of `<`, `>`, `"`, `'`, and `/*`:

```lean
<div {inlineStyle([width(pct(progress))])}
     {styleVars([cssVar(AppTheme.brand, hex("0055aa"))])}/>
```

## 5. Verification checks

- **Theme completeness with `verify_theme`:** Prove every `var(--...)` referenced by any style in an app is defined by the theme:
  ```lean
  verify_theme AppTheme for MyApp.app
  ```
- **Token-only enforcement with `strict_tokens`:** Reject raw color and non-zero length literals inside a `style` block:
  ```lean
  style panel strict_tokens:
    padding: AppTheme.spaceMd
    background-color: AppTheme.surface
    color: AppTheme.text
  ```
- **View styling invariants:** Combine `roleHasOneOf`, `roleHasAll`, `tagHas`, `roleLacks`, `tagLacks`, `exactlyOne`, `exactlyOneOf`, and `noConflictingStyles` inside any `component`.
- **Build-time CSS extraction:** `qed build` and `qed dev` extract static CSS into `styles.css` linked in `index.html` with zero FOUC and copy declared local `stylesheet` files automatically, while SSR inlines `<style id="qed-styles">` in `<head>` for zero-RTT first paint.
