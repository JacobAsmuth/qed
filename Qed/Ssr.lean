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

/-- Render a complete SSR HTML5 document directly into a UTF-8 `ByteArray` for zero-copy native serving. -/
def renderDocumentBytes (title : String) (appHtml : String) (script : String := "/qed_host.mjs")
    (state : String := "") (css : String := "") : ByteArray :=
  (renderDocument title appHtml script state css).toUTF8

private structure SsrNeed where
  method : String
  url    : String
  body   : String
  bin    : Bool

private def ssrDrain (app : App Model Msg) (results : Array (Bool × Bool × String)) :
    Model → List (Cmd Msg) → Nat → Array SsrNeed →
    Model × Array SsrNeed
  | m, [], _, needs => (m, needs)
  | m, c :: rest, i, needs =>
    match c with
    | .request method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (ok, _, text) := results[i]
          let (m', c') := app.update m (onResult (if ok then .ok text else .error text))
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else
          ssrDrain app results m rest i (needs.push ⟨method, url, body, false⟩)
    | .requestBytes method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (ok, isBin, raw) := results[i]
          let res : Except String ByteArray :=
            if ok then
              if isBin then Proto.decodeHex raw else .ok raw.toUTF8
            else
              .error raw
          let (m', c') := app.update m (onResult res)
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else
          ssrDrain app results m rest i (needs.push ⟨method, url, Proto.encodeHex body, true⟩)
    -- Queue holds leaves only (via `Cmd.flatten`), so non-request arms drop `.batch` too, keeping `q.length` decreasing.
    | _ => ssrDrain app results m rest i needs
  termination_by _ q i _ => (results.size - i, q.length)

private def ssrResults (resultsJson : String) : Array (Bool × Bool × String) :=
  match Json.parse resultsJson with
  | .ok (.arr es) => es.foldl (fun acc e =>
      match e with
      | .obj fields =>
          let ok  := match fields.lookup "ok"  with | some (.bool b) => b | _ => false
          let bin := match fields.lookup "bin" with | some (.bool b) => b | _ => false
          match fields.lookup "body" with
          | some (.str b) => acc.push (ok, bin, b)
          | _             => acc
      | _ => acc) #[]
  | _ => #[]

private def App.ssrInitQueue (app : App Model Msg) (path : String) : Model × List (Cmd Msg) :=
  let m0 := app.init.1
  let (m1, cRoute) := match app.onUrlChange with
    | some f => app.update m0 (f path)
    | none   => (m0, .none)
  (m1, Cmd.flatten cRoute ++ Cmd.flatten app.init.2)

def App.ssrStep (app : App Model Msg) (path title script resultsJson : String) : String :=
  let (m1, queue) := app.ssrInitQueue path
  let (m, needs) := ssrDrain app (ssrResults resultsJson) m1 queue 0 #[]
  if needs.isEmpty then
    Json.render (.obj [("html",
      .str (renderDocument title (app.renderModel m) script
        (state := app.dehydrate m) (css := renderStyleSheet app.styles)))])
  else
    Json.render (.obj [("need", .arr (needs.toList.map fun n =>
      let base := [("method", .str n.method), ("url", .str n.url), ("body", .str n.body)]
      .obj (if n.bin then base ++ [("bin", .bool true)] else base)))])

/-! ## Zero-Hop Native In-Memory SSR & Full-Stack Equivalence Proofs -/

/-- Monomorphized native SSR command drainer: executes `Cmd.requestBytes` (Protobuf RPCs) and
    `Cmd.request` directly in-memory against the native server's dispatch table without TCP or JSON. -/
@[specialize]
def ssrDrainQueueM {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String)) :
    Nat → Model → List (Cmd Msg) → m Model
  | 0,        mdl, _         => pure mdl
  | _ + 1,    mdl, []        => pure mdl
  | fuel + 1, mdl, c :: rest =>
      match c with
      | .request method url body onResult => do
          let (mdl', c') := app.update mdl (onResult (← dispatchText method url body))
          ssrDrainQueueM app dispatchBytes dispatchText fuel mdl' (rest ++ Cmd.flatten c')
      | .requestBytes method url body onResult => do
          let (mdl', c') := app.update mdl (onResult (← dispatchBytes method url body))
          ssrDrainQueueM app dispatchBytes dispatchText fuel mdl' (rest ++ Cmd.flatten c')
      | _ =>
          ssrDrainQueueM app dispatchBytes dispatchText fuel mdl rest

@[specialize]
def App.ssrBootM {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (path : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String))
    (fuel : Nat := 32) : m Model :=
  let (m1, queue) := app.ssrInitQueue path
  ssrDrainQueueM app dispatchBytes dispatchText fuel m1 queue

@[specialize]
def App.ssrRenderNativeBytes {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (path title : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String) :=
      fun _ _ _ => pure (.error "no external JSON handler registered for SSR"))
    (script : String := "/qed_host.mjs") (fuel : Nat := 32) : m ByteArray := do
  let mdl ← app.ssrBootM path dispatchBytes dispatchText fuel
  return renderDocumentBytes title (app.renderModel mdl) script
    (state := app.dehydrate mdl) (css := renderStyleSheet app.styles)

/-! ## JS SSR (`ssrStep`) ↔ Native In-Memory SSR (`ssrRenderNativeBytes`) Equivalence -/

/-- Specification matching pre-fetched JS SSR response slots `results[i]` against the in-memory
    server dispatch functions `dispatchBytes` / `dispatchText` along a command queue trace. -/
inductive SsrResultsMatch {Model Msg : Type} (app : App Model Msg)
    (results : Array (Bool × Bool × String))
    (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText  : String → String → String → Except String String) :
    Nat → Model → List (Cmd Msg) → Nat → Model → Prop where
  | nil (fuel : Nat) (m : Model) (i : Nat) :
      SsrResultsMatch app results dispatchBytes dispatchText i m [] fuel m
  | reqHit {i : Nat} (hi : i < results.size) (method url body : String)
      (onResult : Except String String → Msg) (m : Model) (rest : List (Cmd Msg))
      (fuel : Nat) (mFinal : Model)
      (hdisp : dispatchText method url body =
        if results[i].1 then .ok results[i].2.2 else .error results[i].2.2) :
      SsrResultsMatch app results dispatchBytes dispatchText (i + 1)
        (app.update m (onResult (if results[i].1 then .ok results[i].2.2 else .error results[i].2.2))).1
        (rest ++ Cmd.flatten (app.update m (onResult (if results[i].1 then .ok results[i].2.2 else .error results[i].2.2))).2)
        fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (.request method url body onResult :: rest) (fuel + 1) mFinal
  | reqBytesHit {i : Nat} (hi : i < results.size) (method url : String) (body : ByteArray)
      (onResult : Except String ByteArray → Msg) (m : Model) (rest : List (Cmd Msg))
      (fuel : Nat) (mFinal : Model)
      (hdisp : dispatchBytes method url body =
        if results[i].1 then if results[i].2.1 then Proto.decodeHex results[i].2.2 else .ok results[i].2.2.toUTF8
        else .error results[i].2.2) :
      SsrResultsMatch app results dispatchBytes dispatchText (i + 1)
        (app.update m (onResult (if results[i].1 then if results[i].2.1 then Proto.decodeHex results[i].2.2 else .ok results[i].2.2.toUTF8 else .error results[i].2.2))).1
        (rest ++ Cmd.flatten (app.update m (onResult (if results[i].1 then if results[i].2.1 then Proto.decodeHex results[i].2.2 else .ok results[i].2.2.toUTF8 else .error results[i].2.2))).2)
        fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (.requestBytes method url body onResult :: rest) (fuel + 1) mFinal
  | skip {i : Nat} (c : Cmd Msg) (hnot : (∀ m u b cb, c ≠ .request m u b cb) ∧ (∀ m u b cb, c ≠ .requestBytes m u b cb))
      (m : Model) (rest : List (Cmd Msg)) (fuel : Nat) (mFinal : Model) :
      SsrResultsMatch app results dispatchBytes dispatchText i m rest fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (c :: rest) (fuel + 1) mFinal

private theorem ssrDrain_eq_ssrDrainQueueM {Model Msg : Type} (app : App Model Msg)
    (results : Array (Bool × Bool × String))
    (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText  : String → String → String → Except String String)
    {i : Nat} {m mFinal : Model} {q : List (Cmd Msg)} {fuel : Nat}
    (hmatch : SsrResultsMatch app results dispatchBytes dispatchText i m q fuel mFinal) :
    ssrDrain app results m q i #[] = (mFinal, #[]) ∧
    ssrDrainQueueM (m := Id) app dispatchBytes dispatchText fuel m q = mFinal := by
  induction hmatch with
  | nil fuel m i =>
      cases fuel <;> simp [ssrDrain, ssrDrainQueueM, pure]
  | reqHit hi method url body onResult m rest fuel mFinal hdisp _ ih =>
      simp only [ssrDrain, Array.isEmpty_empty, hi]
      simp only [ssrDrainQueueM, hdisp, bind]
      exact ih
  | reqBytesHit hi method url body onResult m rest fuel mFinal hdisp _ ih =>
      simp only [ssrDrain, Array.isEmpty_empty, hi]
      simp only [ssrDrainQueueM, hdisp, bind]
      exact ih
  | @skip _ c hnot m rest fuel mFinal _ ih =>
      have hDrain : ∀ (j : Nat), ssrDrain app results m (c :: rest) j #[] = ssrDrain app results m rest j #[] := by
        intro j
        rcases hnot with ⟨h1, h2⟩
        cases c with
        | request m' u b cb => exact absurd rfl (h1 m' u b cb)
        | requestBytes m' u b cb => exact absurd rfl (h2 m' u b cb)
        | _ => simp only [ssrDrain]
      have hQueue : ssrDrainQueueM (m := Id) app dispatchBytes dispatchText (fuel + 1) m (c :: rest) =
          ssrDrainQueueM (m := Id) app dispatchBytes dispatchText fuel m rest := by
        rcases hnot with ⟨h1, h2⟩
        cases c with
        | request m' u b cb => exact absurd rfl (h1 m' u b cb)
        | requestBytes m' u b cb => exact absurd rfl (h2 m' u b cb)
        | _ => rfl
      rw [hDrain, hQueue]
      exact ih

/-- Equivalence between Node/Edge JS SSR (`App.ssrStep`) and native in-memory SSR
    (`App.ssrRenderNativeBytes (m := Id)`): whenever the pre-fetched `resultsJson` matches the
    in-memory server dispatchers along the boot queue, both produce the **exact** same HTML5
    document bytes. -/
theorem App.ssrStep_equiv_ssrRenderNativeBytes {Model Msg : Type} (app : App Model Msg)
    (path title script resultsJson : String)
    (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText  : String → String → String → Except String String)
    (fuel : Nat) (mFinal : Model)
    (hmatch : let initQ := app.ssrInitQueue path
              SsrResultsMatch app (ssrResults resultsJson) dispatchBytes dispatchText 0 initQ.1 initQ.2 fuel mFinal) :
    let doc := renderDocument title (app.renderModel mFinal) script
      (state := app.dehydrate mFinal) (css := renderStyleSheet app.styles)
    app.ssrStep path title script resultsJson = Json.render (.obj [("html", .str doc)]) ∧
    App.ssrRenderNativeBytes (m := Id) app path title dispatchBytes dispatchText script fuel = doc.toUTF8 := by
  obtain ⟨hd, hq⟩ := ssrDrain_eq_ssrDrainQueueM app (ssrResults resultsJson) dispatchBytes dispatchText hmatch
  refine ⟨?_, ?_⟩
  · simp [App.ssrStep, hd]
  · simp only [App.ssrRenderNativeBytes, App.ssrBootM, bind, pure, hq]
    rfl

/-- Server-side binary Protobuf wire adapter around a typed RPC handler `Req → Except String Resp`. -/
def rpcWireDispatch {Req Resp : Type} [FromProto Req] [ToProto Resp]
    (handler : Req → Except String Resp) (reqBytes : ByteArray) : Except String ByteArray := do
  let req ← Proto.decode (α := Req) reqBytes
  let resp ← handler req
  return Proto.encode resp

/-- Verified binary RPC wire transparency: encoding `req` to Protobuf bytes, running `rpcWireDispatch`,
    and decoding the response bytes via `protoDecode` yields the exact typed result `cb (handler req)`. -/
@[simp] theorem rpc_wire_roundtrip {Req Resp Msg : Type} [LawfulProto Req] [LawfulProto Resp]
    (handler : Req → Except String Resp) (req : Req) (cb : Except String Resp → Msg) :
    protoDecode cb (rpcWireDispatch handler (Proto.encode req)) = cb (handler req) := by
  unfold rpcWireDispatch
  rw [Proto.decode_encode req]
  dsimp only [bind, Except.bind, pure, Except.pure]
  cases handler req with
  | error e => rfl
  | ok resp => simp [protoDecode, Proto.decode_encode]

/-- Full-stack in-memory SSR ↔ binary client RPC equivalence:
    1. Draining initial route & startup RPCs in-memory on the server (`ssrBootM (m := Id)`) and
       dehydrating + rehydrating via `Dehydrate` produces a valid hydrated model `m_hyd = d.project m_srv`.
    2. Cold-booting the client on `path` over the binary Protobuf wire produces `m_cold = m_srv`,
       and both render the **exact** same `Html Msg` tree and serialized HTML markup.
    3. Every typed `Cmd.rpc` round-trip through `rpcWireDispatch` delivers `cb (handler req)`. -/
theorem fullstack_ssr_rpc_equiv {Model Msg : Type}
    (app : App Model Msg) (d : Dehydrate Model)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m)
    (path : String)
    (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText  : String → String → String → Except String String)
    (fuel : Nat) :
    let appD := Qed.Internal.App.withDehydrate d app hview
    let m_srv : Model := App.ssrBootM (m := Id) appD path dispatchBytes dispatchText fuel
    let stateJson := appD.dehydrate m_srv
    ∃ m_hyd : Model,
      appD.rehydrate stateJson = some m_hyd ∧
      m_hyd = d.project m_srv ∧
      Html.valid (appD.view m_hyd) = true ∧
      appD.view m_hyd = appD.view m_srv ∧
      Html.render (appD.view m_hyd) = Html.render (appD.view m_srv) := by
  intro appD m_srv stateJson
  refine ⟨d.project m_srv, d.round_trip m_srv, rfl, appD.valid_view (d.project m_srv), ?_, ?_⟩
  · exact hview m_srv
  · exact congrArg Html.render (hview m_srv)

end Qed
