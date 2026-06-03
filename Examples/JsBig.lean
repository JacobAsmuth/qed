import Qed
open Qed
namespace JsBig
private def li (i : Nat) : Html Unit := Html.element "li" [] [Html.text (toString i)]
/-- Render a list of n items — stresses the per-child recursion in render. -/
def bigRender (n : Nat) : Nat :=
  (Html.render (Html.element "ul" [] ((List.range n).map li))).length
end JsBig
