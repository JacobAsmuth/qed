/-
  Qed — a formally-verified web frontend framework in Lean 4.

  Importing `Qed` brings the whole framework into scope: the typed virtual DOM,
  the readable view notation, The-Elm-Architecture runtime, and the automatic
  invariant machinery.
-/
import Qed.Html
import Qed.Notation
import Qed.Render
import Qed.Runtime
import Qed.Diff
import Qed.Invariant
import Qed.Json
import Qed.Router
import Qed.Date
import Qed.Schema
import Qed.Component
import Qed.ForEach
import Qed.View
import Qed.Resource
import Qed.Style
-- Note: `Qed.Dom` and `Qed.Driver` are intentionally NOT re-exported here. They
-- reference the browser-only DOM externs, so pure app modules (which `import Qed`)
-- stay free of them (and link natively for SSR). Browser entry points import
-- `Qed.Driver` explicitly (see `Examples/Web.lean`).
