import Qed.Runtime.AppCore

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
  if app.locals.isEmpty then Html.render (app.view m)
  else Html.renderWith app.locals (app.view m)

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

def safeCanonicalHref (url : String) : Option String :=
  if isSafeUrl url then some (escapeHtml url) else none

/-- Any canonical `<link rel="canonical" href="...">` URL emitted during SSR passes `isSafeUrl`
    and is unconditionally free of `<`, `>`, `"`, and `'`. -/
theorem safeCanonicalHref_no_markup_or_quote (url out : String)
    (h : safeCanonicalHref url = some out) :
    isSafeUrl url = true ∧ ∀ c ∈ out.toList, isMarkupOrQuote c = false := by
  unfold safeCanonicalHref at h
  by_cases hs : isSafeUrl url = true
  · simp only [hs, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨hs, escapeHtml_no_markup_or_quote url⟩
  · simp [hs] at h

/-- Escaped `<meta name="..." content="...">` tag with both attribute payloads guaranteed markup-free. -/
def renderMetaTag (name content : String) : String :=
  "<meta name=\"" ++ escapeHtml name ++ "\" content=\"" ++ escapeHtml content ++ "\">"

def renderMetaTags : List (String × String) → String
  | [] => ""
  | (k, v) :: rest => renderMetaTag k v ++ renderMetaTags rest

def renderHeadMeta (hm : HeadMeta) : String :=
  let descTag := match hm.description with
    | some d => renderMetaTag "description" d
    | none   => ""
  let extraTags := renderMetaTags hm.metaTags
  let canonTag := match hm.canonical.bind safeCanonicalHref with
    | some u => "<link rel=\"canonical\" href=\"" ++ u ++ "\">"
    | none   => ""
  descTag ++ extraTags ++ canonTag

theorem renderHeadMeta_empty : renderHeadMeta {} = "" := rfl

theorem escapeHeadMetaValue_no_markup_or_quote (s : String) :
    ∀ c ∈ (escapeHtml s).toList, isMarkupOrQuote c = false :=
  escapeHtml_no_markup_or_quote s

def renderStylesheetLinks : List String → String
  | [] => ""
  | s :: rest =>
      let tag := if isSafeUrl s then "<link rel=\"stylesheet\" href=\"" ++ escapeHtml s ++ "\">" else ""
      tag ++ renderStylesheetLinks rest

def renderDocument (title : String) (appHtml : String) (script : String := "/qed.js")
    (state : String := "") (css : String := "") (stylesheets : List String := [])
    (headMeta : HeadMeta := {}) : String :=
  -- Escape `</` → `<\/` (valid JSON/CSS) so embedded payloads cannot close `<script>`/`<style>` early.
  let effTitle := headMeta.title.getD title
  let metaTags := renderHeadMeta headMeta
  let linkTags := renderStylesheetLinks stylesheets
  let styleTag := if css.isEmpty || appHtml.contains css then ""
                  else "<style id=\"qed-styles\">" ++ escapeRawText css ++ "</style>"
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\">"
    ++ "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
    ++ "<title>" ++ escapeHtml effTitle ++ "</title>" ++ metaTags ++ linkTags ++ styleTag ++ "</head>\n"
    ++ "<body><div id=\"app\">" ++ appHtml ++ "</div>\n"
    ++ (if state.isEmpty then ""
        else "<script id=\"qed-state\" type=\"application/json\">" ++ escapeRawText state ++ "</script>\n")
    ++ "<script type=\"module\" src=\"" ++ safeScriptSrc script ++ "\"></script>\n</body>\n</html>"

/-- Render a complete SSR HTML5 document directly into a UTF-8 `ByteArray` for zero-copy native serving. -/
def renderDocumentBytes (title : String) (appHtml : String) (script : String := "/qed_host.mjs")
    (state : String := "") (css : String := "") (stylesheets : List String := [])
    (headMeta : HeadMeta := {}) : ByteArray :=
  (renderDocument title appHtml script state css stylesheets headMeta).toUTF8

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

private def App.ssrInitQueue (app : App Model Msg) (path : String)
    (sessionUser : Option String := none) : Model × List (Cmd Msg) :=
  let m0 := app.init.1
  let (mSess, cSessList) := match app.onSession, sessionUser with
    | some fs, some uid =>
        let (m', c') := app.update m0 (fs (some uid))
        (m', Cmd.flatten c')
    | _, _ => (m0, [])
  let (m1, cRoute) := match app.onUrlChange with
    | some f => app.update mSess (f path)
    | none   => (mSess, .none)
  (m1, cSessList ++ Cmd.flatten cRoute ++ Cmd.flatten app.init.2)

def App.ssrStep (app : App Model Msg) (path title script resultsJson : String) : String :=
  let (m1, queue) := app.ssrInitQueue path
  let (m, needs) := ssrDrain app (ssrResults resultsJson) m1 queue 0 #[]
  if needs.isEmpty then
    Json.render (.obj [("html",
      .str (renderDocument title (app.renderModel m) script
        (state := app.dehydrate m) (css := renderStyleSheet app.styles)
        (stylesheets := app.stylesheets) (headMeta := app.headFor m)))])
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
    (fuel : Nat := 32) (sessionUser : Option String := none) : m Model :=
  let (m1, queue) := app.ssrInitQueue path sessionUser
  ssrDrainQueueM app dispatchBytes dispatchText fuel m1 queue

/-- Pre-rendered static SSR HTML5 shell computed once at server startup so per-request SSR
    only interpolates `appHtml` and `state` into a single pre-sized UTF-8 `ByteArray`. -/
structure PrebuiltDocShell where
  css              : String
  headWithCssBytes : ByteArray
  headNoCssBytes   : ByteArray
  afterAppBytes    : ByteArray
  afterStateBytes  : ByteArray
  noStateTailBytes : ByteArray

def mkPrebuiltDocShell (title : String) (script : String := "/qed_host.mjs")
    (css : String := "") (stylesheets : List String := []) : PrebuiltDocShell :=
  let linkTags := renderStylesheetLinks stylesheets
  let baseHead :=
    "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\">"
      ++ "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
      ++ "<title>" ++ escapeHtml title ++ "</title>" ++ linkTags
  let styleTag := if css.isEmpty then "" else "<style id=\"qed-styles\">" ++ escapeRawText css ++ "</style>"
  let scriptTag := "<script type=\"module\" src=\"" ++ safeScriptSrc script ++ "\"></script>\n</body>\n</html>"
  { css
    headWithCssBytes := (baseHead ++ styleTag ++ "</head>\n<body><div id=\"app\">").toUTF8
    headNoCssBytes   := (baseHead ++ "</head>\n<body><div id=\"app\">").toUTF8
    afterAppBytes    := "</div>\n<script id=\"qed-state\" type=\"application/json\">".toUTF8
    afterStateBytes  := ("</script>\n" ++ scriptTag).toUTF8
    noStateTailBytes := ("</div>\n" ++ scriptTag).toUTF8 }

@[inline] private def appendSlice (dst src : ByteArray) : ByteArray :=
  src.copySlice 0 dst dst.size src.size false

def PrebuiltDocShell.renderBytes (sh : PrebuiltDocShell) (appHtml state : String) : ByteArray :=
  let headB := if sh.css.isEmpty || appHtml.contains sh.css then sh.headNoCssBytes else sh.headWithCssBytes
  let appB := appHtml.toUTF8
  if state.isEmpty then
    let out := ByteArray.emptyWithCapacity (headB.size + appB.size + sh.noStateTailBytes.size)
    let out := appendSlice out headB
    let out := appendSlice out appB
    appendSlice out sh.noStateTailBytes
  else
    let cap := headB.size + appB.size + sh.afterAppBytes.size + state.utf8ByteSize + sh.afterStateBytes.size + 16
    let out := ByteArray.emptyWithCapacity cap
    let out := appendSlice out headB
    let out := appendSlice out appB
    let out := appendSlice out sh.afterAppBytes
    let out := escapeRawTextBytesInto out state
    appendSlice out sh.afterStateBytes

/-- Native SSR renderer returning `(httpStatus, headMeta, htmlBytes)`. Uses the prebuilt shell
    on the fast path when `app.headFor mdl == {}`, and renders escaped per-route `<head>` tags
    otherwise. -/
@[specialize]
def App.ssrRenderNativeWithStatus {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (sh : PrebuiltDocShell) (defaultTitle script path : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String) :=
      fun _ _ _ => pure (.error "no external JSON handler registered for SSR"))
    (fuel : Nat := 32) (sessionUser : Option String := none) : m (Nat × HeadMeta × ByteArray) := do
  let mdl ← app.ssrBootM path dispatchBytes dispatchText fuel sessionUser
  let hm := app.headFor mdl
  let rawStatus := app.ssrStatus mdl
  let status := if 100 ≤ rawStatus && rawStatus ≤ 599 then rawStatus else 200
  let appHtml := app.renderModel mdl
  let state := app.dehydrate mdl
  let htmlBytes :=
    if hm == {} then
      sh.renderBytes appHtml state
    else
      renderDocumentBytes defaultTitle appHtml script (state := state)
        (css := sh.css) (stylesheets := app.stylesheets) (headMeta := hm)
  return (status, hm, htmlBytes)

@[specialize]
def App.ssrRenderNativeBytes {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (path title : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String) :=
      fun _ _ _ => pure (.error "no external JSON handler registered for SSR"))
    (script : String := "/qed_host.mjs") (fuel : Nat := 32)
    (sessionUser : Option String := none) : m ByteArray := do
  let mdl ← app.ssrBootM path dispatchBytes dispatchText fuel sessionUser
  return renderDocumentBytes title (app.renderModel mdl) script
    (state := app.dehydrate mdl) (css := renderStyleSheet app.styles)
    (stylesheets := app.stylesheets) (headMeta := app.headFor mdl)

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
      (stylesheets := app.stylesheets) (headMeta := app.headFor mFinal)
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
    let appD := Qed.Internal.App.withDehydrateCore d app hview
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

/-! ## SSR Binary RPC Routing Closure (`ssr_rpc_endpoint_routed`) -/

/-- Pure specification of native SSR binary RPC dispatch routing against a server's
    `shortName` and `methods` list. -/
def ssrDispatchRpc (srvShort : String) (methods : List String)
    (dispatchMethod : String → ByteArray → Except String ByteArray)
    (reqMethod url : String) (reqBody : ByteArray) : Except String ByteArray :=
  let rpcPrefix := "/_qed/rpc/" ++ srvShort ++ "/"
  let uPath := String.ofList (url.toList.takeWhile (· ≠ '?'))
  if reqMethod == "POST" && uPath.startsWith rpcPrefix then
    let mName := String.ofList (uPath.toList.drop rpcPrefix.length)
    if mName ∈ methods then dispatchMethod mName reqBody
    else .error s!"SSR unknown binary RPC method: {mName}"
  else
    .error s!"SSR unknown binary RPC endpoint: {url}"

private theorem takeWhile_ne_append (p : Char → Bool) :
    ∀ (xs ys : List Char), (∀ c ∈ xs, p c = true) → (∀ c ∈ ys, p c = true) →
      (xs ++ ys).takeWhile p = xs ++ ys
  | [], ys, _, hys => by
      induction ys with
      | nil => rfl
      | cons y rest ih =>
          simp only [List.nil_append, List.takeWhile_cons, hys y (by simp), ↓reduceIte]
          exact congrArg (y :: ·) (ih (fun c hc => hys c (by simp [hc])))
  | x :: xs, ys, hxs, hys => by
      simp only [List.cons_append, List.takeWhile_cons, hxs x (by simp), ↓reduceIte]
      exact congrArg (x :: ·) (takeWhile_ne_append p xs ys (fun c hc => hxs c (by simp [hc])) hys)

/-- Any binary RPC endpoint targeting `srvShort` and a declared method `m ∈ methods`
    routes directly to `dispatchMethod m reqBody` during in-memory SSR. -/
theorem ssr_rpc_endpoint_routed (srvShort : String) (methods : List String)
    (dispatchMethod : String → ByteArray → Except String ByteArray)
    (srv m : String) (reqBody : ByteArray)
    (hsrv : srv = srvShort) (hm : m ∈ methods)
    (hsrvNoQ : ∀ c ∈ srvShort.toList, c ≠ '?')
    (hmNoQ : ∀ c ∈ m.toList, c ≠ '?') :
    ssrDispatchRpc srvShort methods dispatchMethod "POST" ("/_qed/rpc/" ++ srv ++ "/" ++ m) reqBody =
      dispatchMethod m reqBody := by
  subst srv
  have hpfxNoQ : ∀ c ∈ ("/_qed/rpc/" ++ srvShort ++ "/").toList, c ≠ '?' := by
    intro c hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with (h1 | h2) | h3
    · have hlit : ∀ x ∈ "/_qed/rpc/".toList, x ≠ '?' := by decide
      exact hlit c h1
    · exact hsrvNoQ c h2
    · have hlit : ∀ x ∈ "/".toList, x ≠ '?' := by decide
      exact hlit c h3
  have hurl : ("/_qed/rpc/" ++ srvShort ++ "/" ++ m).toList.takeWhile (· ≠ '?') =
      ("/_qed/rpc/" ++ srvShort ++ "/").toList ++ m.toList := by
    have h1 : ("/_qed/rpc/" ++ srvShort ++ "/" ++ m).toList =
        ("/_qed/rpc/" ++ srvShort ++ "/").toList ++ m.toList := by
      simp [String.toList_append, List.append_assoc]
    rw [h1]
    exact takeWhile_ne_append (· ≠ '?') ("/_qed/rpc/" ++ srvShort ++ "/").toList m.toList
      (fun c hc => decide_eq_true (hpfxNoQ c hc))
      (fun c hc => decide_eq_true (hmNoQ c hc))
  have hpath : String.ofList (("/_qed/rpc/" ++ srvShort ++ "/" ++ m).toList.takeWhile (· ≠ '?')) =
      ("/_qed/rpc/" ++ srvShort ++ "/") ++ m := by
    rw [hurl, ← String.toList_append, String.ofList_toList]
  have hdrop : (("/_qed/rpc/" ++ srvShort ++ "/") ++ m).toList.drop ("/_qed/rpc/" ++ srvShort ++ "/").length =
      m.toList := by
    rw [String.toList_append, ← String.length_toList (s := "/_qed/rpc/" ++ srvShort ++ "/"), List.drop_left]
  unfold ssrDispatchRpc
  dsimp only
  rw [hpath]
  have hsw : (("/_qed/rpc/" ++ srvShort ++ "/") ++ m).startsWith ("/_qed/rpc/" ++ srvShort ++ "/") = true := by
    simp [String.startsWith]
  simp only [beq_self_eq_true, hsw, Bool.and_self, ↓reduceIte, hdrop, String.ofList_toList, hm]

/-- Full-stack SSR RPC closure theorem: when every client RPC in `usedRpcs` targets `srvShort`
    and a method in `methods`, SSR never encounters an unknown binary RPC endpoint error. -/
theorem ssr_rpc_closure_complete (srvShort : String) (methods : List String)
    (usedRpcs : List (String × String))
    (hclosed : ∀ ep ∈ usedRpcs, ep.1 = srvShort ∧ ep.2 ∈ methods)
    (dispatchMethod : String → ByteArray → Except String ByteArray)
    (hsrvNoQ : ∀ c ∈ srvShort.toList, c ≠ '?')
    (hmNoQ : ∀ ep ∈ usedRpcs, ∀ c ∈ ep.2.toList, c ≠ '?')
    (ep : String × String) (hep : ep ∈ usedRpcs) (reqBody : ByteArray) :
    ssrDispatchRpc srvShort methods dispatchMethod "POST" ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody =
      dispatchMethod ep.2 reqBody :=
  ssr_rpc_endpoint_routed srvShort methods dispatchMethod ep.1 ep.2 reqBody
    (hclosed ep hep).1 (hclosed ep hep).2 hsrvNoQ (hmNoQ ep hep)

end Qed
