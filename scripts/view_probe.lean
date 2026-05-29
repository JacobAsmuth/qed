import Qed
open Qed

-- escaping (was the XSS hole in the deleted renderer)
#eval (div [] ["<script>alert(1)</script>"] : Html Unit).render
-- boolean flag: true present, false absent
#eval (button [disabled true] "x"  : Html Unit).render
#eval (button [disabled false] "x" : Html Unit).render
-- class merge + duplicate-key last-wins
#eval (div [cls "a", cls "b", attr "id" "x", attr "id" "y"] [] : Html Unit).render
-- string coercions: bare string child list, and lone string children
#eval (span [cls "c"] [toString (7 : Nat)] : Html Unit).render
#eval (button [onClick ()] "Save" : Html Unit).render
