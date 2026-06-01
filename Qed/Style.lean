/-
  Qed.Style — scoped, collision-free styles co-located with the code that uses them.

  A `Style` is a hashed class name plus a CSS body. You define it next to the component,
  reference it on an element like any attribute, and emit one stylesheet:

      def card : Style := css "
        padding: 16px; border-radius: 8px; background: var(--surface);
        &:hover { transform: translateY(-2px) }"

      div [card] [ … ]                 -- `card` coerces to its class attribute
      styleSheet [card, button, …]      -- once in your view: emits one <style>

  The class name is a hash of the CSS, so identical styles dedup and names can never
  collide across modules. A `&` in the body refers to the class via native CSS nesting
  (`.qed-… { &:hover { … } }`). Because a style is referenced by its Lean *binding*
  (`card`), a typo is a compile error — not a silently-dead class string.

  Pure data: a `Style` is a value, `styleSheet` is an ordinary `Html` node. CSS *property*
  typos are not yet caught (the body is an opaque string); that's a later, typed-DSL step.
-/
import Qed.Notation

namespace Qed

/-- A scoped style: a generated class name and the CSS declaration body it stands for. -/
structure Style where
  className : String
  raw       : String
deriving Inhabited

/-- Define a scoped style from a CSS declaration body. (Named `css` since `style` is the
    inline-`style`-attribute helper in `Qed.Notation`.) -/
def css (body : String) : Style := { className := s!"qed-{String.hash body}", raw := body }

/-- A style is usable wherever an attribute is — it applies its class. -/
instance : Coe Style (Attr msg) := ⟨fun s => .cls s.className⟩

/-- One CSS rule: `.qed-… { <body> }` (the body keeps any `&`-nesting). -/
private def Style.rule (s : Style) : String := "." ++ s.className ++ " { " ++ s.raw ++ " }"

/-- Collect styles into one `<style>` element, deduping by class name. Drop this once in
    your view (e.g. at the top of the root element's children). -/
def styleSheet (styles : List Style) : Html msg :=
  let seen := styles.foldl
    (fun acc s => if acc.any (·.className == s.className) then acc else acc ++ [s]) []
  el "style" [] [Html.text (String.intercalate "\n" (seen.map Style.rule))]

end Qed
