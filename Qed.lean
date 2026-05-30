/-
  Qed — a formally-verified web frontend framework in Lean 4.

  Importing `Qed` brings the whole framework into scope: the typed virtual DOM,
  the readable view notation, The-Elm-Architecture runtime, and the automatic
  invariant machinery.
-/
import Qed.Html
import Qed.Notation
import Qed.Runtime
import Qed.Diff
import Qed.Invariant
import Qed.Json
import Qed.Router
import Qed.Date
import Qed.Form
import Qed.Component
-- Note: `Qed.Dom` and `Qed.Driver` are intentionally NOT re-exported here. They
-- reference the browser-only DOM externs, so pure app modules (which `import Qed`)
-- stay free of them and link on the native target. WASM entry points import
-- `Qed.Driver` explicitly (see `Examples/Web.lean`).
