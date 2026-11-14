import Qed.Runtime.App
import Qed.Json.Basic

namespace Qed

mutual
  def renderWithLocals {m : Type} (locals : List LocalDef) : Nat → Html m → String
    | 0, _ => ""
    | _ + 1, .text s => escapeHtml s
    | fuel + 1, .element tag attrs children =>
        let local? := attrs.findSome? (fun | .localCell _ comp init p _ => some (comp, init, p) | _ => none)
        match local? with
        | some (comp, init?, p) =>
            let attrStr := (renderAttrs #[] (normalizeAttrs attrs)).1
            let childStr := match locals.find? (fun d : LocalDef => d.id == comp) with
              | some ldef =>
                  renderWithLocals locals fuel (ldef.viewForProps p (init?.getD ldef.init))
              | none => ""
            s!"<{tag}{attrStr}>{childStr}</{tag}>"
        | none =>
            (renderElement (fun hs => (renderWithLocalsChildren locals fuel "" children, hs)) #[] tag attrs children).1

  def renderWithLocalsChildren {m : Type} (locals : List LocalDef) (fuel : Nat) (acc : String) :
      List (Html m) → String
    | []      => acc
    | c :: cs => renderWithLocalsChildren locals fuel (acc ++ renderWithLocals locals fuel c) cs
end

def Html.renderWith (locals : List LocalDef) (h : Html msg) (fuel : Nat := 64) : String :=
  renderWithLocals locals fuel h

def App.renderModel (app : App Model Msg) (m : Model) : String :=
  Html.renderWith app.locals (app.view m)

def App.renderInitial (app : App Model Msg) : String :=
  app.renderModel app.init.1

def safeScriptSrc (script : String) : String :=
  if isSafeUrl script then escapeHtml script else "/qed.js"

/-- The `src="..."` payload emitted for `<script type="module">` is unconditionally free of
    `<`, `>`, `"`, and `'`, and only accepts `isSafeUrl` targets (defaulting to `"/qed.js"`). -/
theorem safeScriptSrc_no_markup_or_quote (script : String) :
    ∀ c ∈ (safeScriptSrc script).toList, isMarkupOrQuote c = false := by
  unfold safeScriptSrc
  by_cases h : isSafeUrl script = true
  · simpa [h] using escapeHtml_no_markup_or_quote script
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    have hconst : ("/qed.js".toList.all (!isMarkupOrQuote ·)) = true := by decide
    rw [List.all_eq_true] at hconst
    intro c hc
    simpa using hconst c hc

def renderDocument (title : String) (appHtml : String) (script : String := "/qed.js")
    (state : String := "") (css : String := "") : String :=
  -- Escape `</` → `<\/` (valid JSON/CSS) so embedded payloads cannot close `<script>`/`<style>` early.
  let styleTag := if css.isEmpty || appHtml.contains css then ""
                  else "<style id=\"qed-styles\">" ++ escapeRawText css ++ "</style>"
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\">"
    ++ "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
    ++ "<title>" ++ escapeHtml title ++ "</title>" ++ styleTag ++ "</head>\n"
    ++ "<body><div id=\"app\">" ++ appHtml ++ "</div>\n"
    ++ (if state.isEmpty then ""
        else "<script id=\"qed-state\" type=\"application/json\">" ++ escapeRawText state ++ "</script>\n")
    ++ "<script type=\"module\" src=\"" ++ safeScriptSrc script ++ "\"></script>\n</body>\n</html>"

private def ssrDrain (app : App Model Msg) (results : Array (Bool × String)) :
    Model → List (Cmd Msg) → Nat → Array (String × String × String) →
    Model × Array (String × String × String)
  | m, [], _, needs => (m, needs)
  | m, c :: rest, i, needs =>
    match c with
    | .request method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (ok, text) := results[i]
          let (m', c') := app.update m (onResult (if ok then .ok text else .error text))
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else
          ssrDrain app results m rest i (needs.push (method, url, body))
    -- Queue holds leaves only (via `Cmd.flatten`), so non-request arms drop `.batch` too, keeping `q.length` decreasing.
    | _ => ssrDrain app results m rest i needs
  termination_by _ q i _ => (results.size - i, q.length)

private def ssrResults (resultsJson : String) : Array (Bool × String) :=
  match Json.parse resultsJson with
  | .ok (.arr es) => es.foldl (fun acc e =>
      match e with
      | .obj fields =>
          let ok := match fields.lookup "ok" with | some (.bool b) => b | _ => false
          match fields.lookup "body" with
          | some (.str b) => acc.push (ok, b)
          | _             => acc
      | _ => acc) #[]
  | _ => #[]

def App.ssrStep (app : App Model Msg) (path title script resultsJson : String) : String :=
  let results := ssrResults resultsJson
  let m0 := app.init.1
  let (m1, cRoute) := match app.onUrlChange with
    | some f => app.update m0 (f path)
    | none   => (m0, .none)
  let queue := Cmd.flatten cRoute ++ Cmd.flatten app.init.2
  let (m, needs) := ssrDrain app results m1 queue 0 #[]
  if needs.isEmpty then
    Json.render (.obj [("html",
      .str (renderDocument title (app.renderModel m) script
        (state := app.dehydrate m) (css := renderStyleSheet app.styles)))])
  else
    Json.render (.obj [("need", .arr (needs.toList.map fun (method, url, body) =>
      .obj [("method", .str method), ("url", .str url), ("body", .str body)]))])

end Qed
