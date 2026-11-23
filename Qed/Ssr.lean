import Qed.Runtime.AppCore

namespace Qed

mutual
  def renderWithLocals {m : Type} (locals : List LocalDef) : Nat → Html m → String
    | 0, _ => "" | _ + 1, .text s => escapeHtml s
    | fuel + 1, .element tag attrs children =>
        match attrs.findSome? (fun | .localCell _ comp init p _ => some (comp, init, p) | _ => none) with
        | some (comp, init?, p) =>
            let childStr := match locals.find? (·.id == comp) with | some ldef => renderWithLocals locals fuel (ldef.viewForProps p (init?.getD ldef.init)) | none => ""
            s!"<{tag}{(renderAttrs #[] (normalizeAttrs attrs)).1}>{childStr}</{tag}>"
        | none => (renderElement (fun hs => (renderWithLocalsChildren locals fuel "" children, hs)) #[] tag attrs children).1
  def renderWithLocalsChildren {m : Type} (locals : List LocalDef) (fuel : Nat) (acc : String) : List (Html m) → String
    | [] => acc | c :: cs => renderWithLocalsChildren locals fuel (acc ++ renderWithLocals locals fuel c) cs
end

def Html.renderWith (locals : List LocalDef) (h : Html msg) (fuel : Nat := 64) : String := renderWithLocals locals fuel h
def App.renderModel (app : App Model Msg) (m : Model) : String := if app.locals.isEmpty then Html.render (app.view m) else Html.renderWith app.locals (app.view m)

def safeScriptSrc (script : String) : String := if isSafeUrl script then escapeHtml script else "/qed.js"

theorem safeScriptSrc_no_markup_or_quote (script : String) : ∀ c ∈ (safeScriptSrc script).toList, isMarkupOrQuote c = false := by
  unfold safeScriptSrc; by_cases h : isSafeUrl script = true
  · simpa [h] using escapeHtml_no_markup_or_quote script
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; intro c hc; simpa using List.all_eq_true.1 (by decide : ("/qed.js".toList.all (!isMarkupOrQuote ·)) = true) c hc

def safeCanonicalHref (url : String) : Option String := if isSafeUrl url then some (escapeHtml url) else none

theorem safeCanonicalHref_no_markup_or_quote (url out : String) (h : safeCanonicalHref url = some out) :
    isSafeUrl url = true ∧ ∀ c ∈ out.toList, isMarkupOrQuote c = false := by
  unfold safeCanonicalHref at h; by_cases hs : isSafeUrl url = true
  · simp only [hs, ↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨hs, escapeHtml_no_markup_or_quote url⟩
  · simp [hs] at h

def renderMetaTag (name content : String) : String := "<meta name=\"" ++ escapeHtml name ++ "\" content=\"" ++ escapeHtml content ++ "\">"

def renderHeadMeta (hm : HeadMeta) : String :=
  (hm.description.map (renderMetaTag "description") |>.getD "") ++
  String.join (hm.metaTags.map fun (k, v) => renderMetaTag k v) ++
  ((hm.canonical.bind safeCanonicalHref).map (fun u => "<link rel=\"canonical\" href=\"" ++ u ++ "\">") |>.getD "")

theorem renderHeadMeta_empty : renderHeadMeta {} = "" := rfl
theorem escapeHeadMetaValue_no_markup_or_quote (s : String) : ∀ c ∈ (escapeHtml s).toList, isMarkupOrQuote c = false := escapeHtml_no_markup_or_quote s

def renderStylesheetLinks (xs : List String) : String :=
  String.join (xs.map fun s => if isSafeUrl s then "<link rel=\"stylesheet\" href=\"" ++ escapeHtml s ++ "\">" else "")

private def docHeadPrefix (title extra : String) : String :=
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>" ++ escapeHtml title ++ "</title>" ++ extra
private def docStyleTag (css : String) : String := if css.isEmpty then "" else "<style id=\"qed-styles\">" ++ escapeRawText css ++ "</style>"
private def docScriptTag (script : String) : String := "<script type=\"module\" src=\"" ++ safeScriptSrc script ++ "\"></script>\n</body>\n</html>"

def renderDocument (title : String) (appHtml : String) (script : String := "/qed.js")
    (state : String := "") (css : String := "") (stylesheets : List String := []) (headMeta : HeadMeta := {}) : String :=
  let styleTag := if css.isEmpty || appHtml.contains css then "" else docStyleTag css
  docHeadPrefix (headMeta.title.getD title) (renderHeadMeta headMeta ++ renderStylesheetLinks stylesheets) ++
    styleTag ++ "</head>\n<body><div id=\"app\">" ++ appHtml ++ "</div>\n" ++
    (if state.isEmpty then "" else "<script id=\"qed-state\" type=\"application/json\">" ++ escapeRawText state ++ "</script>\n") ++ docScriptTag script

private structure SsrNeed where
  method : String
  url    : String
  body   : String
  bin    : Bool

@[reducible] def ssrSlotText (slot : Bool × Bool × String) : Except String String := if slot.1 then .ok slot.2.2 else .error slot.2.2
@[reducible] def ssrSlotBytes (slot : Bool × Bool × String) : Except String ByteArray :=
  if slot.1 then if slot.2.1 then Proto.decodeHex slot.2.2 else .ok slot.2.2.toUTF8 else .error slot.2.2

private def ssrDrain (app : App Model Msg) (results : Array (Bool × Bool × String)) :
    Model → List (Cmd Msg) → Nat → Array SsrNeed → Model × Array SsrNeed
  | m, [], _, needs => (m, needs)
  | m, c :: rest, i, needs =>
    match c with
    | .request method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (m', c') := app.update m (onResult (ssrSlotText results[i]))
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else ssrDrain app results m rest i (needs.push ⟨method, url, body, false⟩)
    | .requestBytes method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (m', c') := app.update m (onResult (ssrSlotBytes results[i]))
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else ssrDrain app results m rest i (needs.push ⟨method, url, Proto.encodeHex body, true⟩)
    | _ => ssrDrain app results m rest i needs
  termination_by _ q i _ => (results.size - i, q.length)

private def ssrResults (resultsJson : String) : Array (Bool × Bool × String) :=
  match Json.parse resultsJson with
  | .ok (.arr es) => es.foldl (fun acc e => match e.strAt? "body" with
      | some b => acc.push ((e.boolAt? "ok").getD false, (e.boolAt? "bin").getD false, b) | none => acc) #[]
  | _ => #[]

private def App.ssrInitQueue (app : App Model Msg) (path : String) (sessionUser : Option String := none) : Model × List (Cmd Msg) :=
  let (mSess, cSessList) := match app.onSession, sessionUser with
    | some fs, some uid => let (m', c') := app.update app.init.1 (fs (some uid)); (m', Cmd.flatten c') | _, _ => (app.init.1, [])
  let (m1, cRoute) := match app.onUrlChange with | some f => app.update mSess (f path) | none => (mSess, .none)
  (m1, cSessList ++ Cmd.flatten cRoute ++ Cmd.flatten app.init.2)

private def App.renderDocFor (app : App Model Msg) (title script : String) (m : Model) : String :=
  renderDocument title (app.renderModel m) script (state := app.dehydrate m) (css := renderStyleSheet app.styles) (stylesheets := app.stylesheets) (headMeta := app.headFor m)

def App.ssrStep (app : App Model Msg) (path title script resultsJson : String) : String :=
  let (m1, queue) := app.ssrInitQueue path
  let (m, needs) := ssrDrain app (ssrResults resultsJson) m1 queue 0 #[]
  if needs.isEmpty then Json.render (.obj [("html", .str (app.renderDocFor title script m))])
  else Json.render (.obj [("need", .arr (needs.toList.map fun n =>
    let base := [("method", .str n.method), ("url", .str n.url), ("body", .str n.body)]
    .obj (if n.bin then base ++ [("bin", .bool true)] else base)))])

/-! ## Zero-Hop Native In-Memory SSR & Full-Stack Equivalence Proofs -/

@[specialize]
def ssrDrainQueueM {Model Msg : Type} {m : Type → Type} [Monad m] (app : App Model Msg)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String)) : Nat → Model → List (Cmd Msg) → m Model
  | 0, mdl, _ | _ + 1, mdl, [] => pure mdl
  | fuel + 1, mdl, c :: rest => match c with
      | .request method url body onResult => do
          let (mdl', c') := app.update mdl (onResult (← dispatchText method url body))
          ssrDrainQueueM app dispatchBytes dispatchText fuel mdl' (rest ++ Cmd.flatten c')
      | .requestBytes method url body onResult => do
          let (mdl', c') := app.update mdl (onResult (← dispatchBytes method url body))
          ssrDrainQueueM app dispatchBytes dispatchText fuel mdl' (rest ++ Cmd.flatten c')
      | _ => ssrDrainQueueM app dispatchBytes dispatchText fuel mdl rest

@[specialize]
def App.ssrBootM {Model Msg : Type} {m : Type → Type} [Monad m] (app : App Model Msg) (path : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String)) (fuel : Nat := 32) (sessionUser : Option String := none) : m Model :=
  let (m1, queue) := app.ssrInitQueue path sessionUser
  ssrDrainQueueM app dispatchBytes dispatchText fuel m1 queue

structure PrebuiltDocShell where
  css              : String
  headWithCssBytes : ByteArray
  headNoCssBytes   : ByteArray
  afterAppBytes    : ByteArray
  afterStateBytes  : ByteArray
  noStateTailBytes : ByteArray

def mkPrebuiltDocShell (title : String) (script : String := "/qed_host.mjs") (css : String := "") (stylesheets : List String := []) : PrebuiltDocShell :=
  let baseHead := docHeadPrefix title (renderStylesheetLinks stylesheets); let scriptTag := docScriptTag script
  { css, headWithCssBytes := (baseHead ++ docStyleTag css ++ "</head>\n<body><div id=\"app\">").toUTF8
    headNoCssBytes := (baseHead ++ "</head>\n<body><div id=\"app\">").toUTF8
    afterAppBytes := "</div>\n<script id=\"qed-state\" type=\"application/json\">".toUTF8
    afterStateBytes := ("</script>\n" ++ scriptTag).toUTF8, noStateTailBytes := ("</div>\n" ++ scriptTag).toUTF8 }

@[inline] private def appendSlice (dst src : ByteArray) : ByteArray := src.copySlice 0 dst dst.size src.size false

def PrebuiltDocShell.renderBytes (sh : PrebuiltDocShell) (appHtml state : String) : ByteArray :=
  let headB := if sh.css.isEmpty || appHtml.contains sh.css then sh.headNoCssBytes else sh.headWithCssBytes
  let appB := appHtml.toUTF8
  if state.isEmpty then
    appendSlice (appendSlice (appendSlice (ByteArray.emptyWithCapacity (headB.size + appB.size + sh.noStateTailBytes.size)) headB) appB) sh.noStateTailBytes
  else
    let cap := headB.size + appB.size + sh.afterAppBytes.size + state.utf8ByteSize + sh.afterStateBytes.size + 16
    appendSlice (escapeRawTextBytesInto (appendSlice (appendSlice (appendSlice (ByteArray.emptyWithCapacity cap) headB) appB) sh.afterAppBytes) state) sh.afterStateBytes

@[specialize]
def App.ssrRenderNativeWithStatus {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (sh : PrebuiltDocShell) (defaultTitle script path : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String) := fun _ _ _ => pure (.error "no external JSON handler registered for SSR"))
    (fuel : Nat := 32) (sessionUser : Option String := none) : m (Nat × HeadMeta × ByteArray) := do
  let mdl ← app.ssrBootM path dispatchBytes dispatchText fuel sessionUser
  let hm := app.headFor mdl; let rawStatus := app.ssrStatus mdl
  let status := if 100 ≤ rawStatus && rawStatus ≤ 599 then rawStatus else 200
  let appHtml := app.renderModel mdl; let state := app.dehydrate mdl
  let htmlBytes := if hm == {} then sh.renderBytes appHtml state
    else (renderDocument defaultTitle appHtml script (state := state) (css := sh.css) (stylesheets := app.stylesheets) (headMeta := hm)).toUTF8
  return (status, hm, htmlBytes)

@[specialize]
def App.ssrRenderNativeBytes {Model Msg : Type} {m : Type → Type} [Monad m]
    (app : App Model Msg) (path title : String)
    (dispatchBytes : String → String → ByteArray → m (Except String ByteArray))
    (dispatchText  : String → String → String → m (Except String String) := fun _ _ _ => pure (.error "no external JSON handler registered for SSR"))
    (script : String := "/qed_host.mjs") (fuel : Nat := 32) (sessionUser : Option String := none) : m ByteArray := do
  return (app.renderDocFor title script (← app.ssrBootM path dispatchBytes dispatchText fuel sessionUser)).toUTF8

/-! ## JS SSR (`ssrStep`) ↔ Native In-Memory SSR (`ssrRenderNativeBytes`) Equivalence -/

inductive SsrResultsMatch {Model Msg : Type} (app : App Model Msg) (results : Array (Bool × Bool × String))
    (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText  : String → String → String → Except String String) : Nat → Model → List (Cmd Msg) → Nat → Model → Prop where
  | nil (fuel : Nat) (m : Model) (i : Nat) : SsrResultsMatch app results dispatchBytes dispatchText i m [] fuel m
  | reqHit {i : Nat} (hi : i < results.size) (method url body : String) (onResult : Except String String → Msg)
      (m : Model) (rest : List (Cmd Msg)) (fuel : Nat) (mFinal : Model) (hdisp : dispatchText method url body = ssrSlotText results[i]) :
      SsrResultsMatch app results dispatchBytes dispatchText (i + 1)
        (app.update m (onResult (ssrSlotText results[i]))).1 (rest ++ Cmd.flatten (app.update m (onResult (ssrSlotText results[i]))).2) fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (.request method url body onResult :: rest) (fuel + 1) mFinal
  | reqBytesHit {i : Nat} (hi : i < results.size) (method url : String) (body : ByteArray) (onResult : Except String ByteArray → Msg)
      (m : Model) (rest : List (Cmd Msg)) (fuel : Nat) (mFinal : Model) (hdisp : dispatchBytes method url body = ssrSlotBytes results[i]) :
      SsrResultsMatch app results dispatchBytes dispatchText (i + 1)
        (app.update m (onResult (ssrSlotBytes results[i]))).1 (rest ++ Cmd.flatten (app.update m (onResult (ssrSlotBytes results[i]))).2) fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (.requestBytes method url body onResult :: rest) (fuel + 1) mFinal
  | skip {i : Nat} (c : Cmd Msg) (hnot : (∀ m u b cb, c ≠ .request m u b cb) ∧ (∀ m u b cb, c ≠ .requestBytes m u b cb))
      (m : Model) (rest : List (Cmd Msg)) (fuel : Nat) (mFinal : Model) :
      SsrResultsMatch app results dispatchBytes dispatchText i m rest fuel mFinal →
      SsrResultsMatch app results dispatchBytes dispatchText i m (c :: rest) (fuel + 1) mFinal

private theorem ssrDrain_eq_ssrDrainQueueM {Model Msg : Type} (app : App Model Msg) (results : Array (Bool × Bool × String))
    (dispatchBytes : String → String → ByteArray → Except String ByteArray) (dispatchText : String → String → String → Except String String)
    {i : Nat} {m mFinal : Model} {q : List (Cmd Msg)} {fuel : Nat}
    (hmatch : SsrResultsMatch app results dispatchBytes dispatchText i m q fuel mFinal) :
    ssrDrain app results m q i #[] = (mFinal, #[]) ∧ ssrDrainQueueM (m := Id) app dispatchBytes dispatchText fuel m q = mFinal := by
  induction hmatch with
  | nil fuel => cases fuel <;> simp [ssrDrain, ssrDrainQueueM, pure]
  | reqHit hi _ _ _ _ _ _ _ _ hdisp _ ih | reqBytesHit hi _ _ _ _ _ _ _ _ hdisp _ ih =>
      simp only [ssrDrain, Array.isEmpty_empty, hi, ssrDrainQueueM, hdisp, bind]; exact ih
  | @skip _ c hnot _ _ _ _ _ ih =>
      cases c with
      | request m' u b cb => exact absurd rfl (hnot.1 m' u b cb)
      | requestBytes m' u b cb => exact absurd rfl (hnot.2 m' u b cb)
      | _ => simpa only [ssrDrain, ssrDrainQueueM] using ih

theorem App.ssrStep_equiv_ssrRenderNativeBytes {Model Msg : Type} (app : App Model Msg) (path title script resultsJson : String)
    (dispatchBytes : String → String → ByteArray → Except String ByteArray) (dispatchText : String → String → String → Except String String)
    (fuel : Nat) (mFinal : Model)
    (hmatch : let initQ := app.ssrInitQueue path
              SsrResultsMatch app (ssrResults resultsJson) dispatchBytes dispatchText 0 initQ.1 initQ.2 fuel mFinal) :
    let doc := renderDocument title (app.renderModel mFinal) script
      (state := app.dehydrate mFinal) (css := renderStyleSheet app.styles) (stylesheets := app.stylesheets) (headMeta := app.headFor mFinal)
    app.ssrStep path title script resultsJson = Json.render (.obj [("html", .str doc)]) ∧
    App.ssrRenderNativeBytes (m := Id) app path title dispatchBytes dispatchText script fuel = doc.toUTF8 := by
  obtain ⟨hd, hq⟩ := ssrDrain_eq_ssrDrainQueueM app (ssrResults resultsJson) dispatchBytes dispatchText hmatch
  exact ⟨by simp [App.ssrStep, App.renderDocFor, hd], by simp only [App.ssrRenderNativeBytes, App.ssrBootM, App.renderDocFor, bind, pure, hq]⟩

def rpcWireDispatch {Req Resp : Type} [FromProto Req] [ToProto Resp] (handler : Req → Except String Resp) (reqBytes : ByteArray) : Except String ByteArray := do
  return Proto.encode (← handler (← Proto.decode (α := Req) reqBytes))

@[simp] theorem rpc_wire_roundtrip {Req Resp Msg : Type} [LawfulProto Req] [LawfulProto Resp]
    (handler : Req → Except String Resp) (req : Req) (cb : Except String Resp → Msg) :
    protoDecode cb (rpcWireDispatch handler (Proto.encode req)) = cb (handler req) := by
  unfold rpcWireDispatch; rw [Proto.decode_encode req]; dsimp only [bind, Except.bind, pure, Except.pure]
  cases handler req with | error _ => rfl | ok _ => simp [protoDecode, Proto.decode_encode]

theorem fullstack_ssr_rpc_equiv {Model Msg : Type} (app : App Model Msg) (d : Dehydrate Model)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m)
    (path : String) (dispatchBytes : String → String → ByteArray → Except String ByteArray)
    (dispatchText : String → String → String → Except String String) (fuel : Nat) :
    let appD := Qed.Internal.App.withDehydrateCore d app hview
    let m_srv : Model := App.ssrBootM (m := Id) appD path dispatchBytes dispatchText fuel
    let stateJson := appD.dehydrate m_srv
    ∃ m_hyd : Model, appD.rehydrate stateJson = some m_hyd ∧ m_hyd = d.project m_srv ∧
      Html.valid (appD.view m_hyd) = true ∧ appD.view m_hyd = appD.view m_srv ∧ Html.render (appD.view m_hyd) = Html.render (appD.view m_srv) := by
  intro appD m_srv _
  exact ⟨d.project m_srv, d.round_trip m_srv, rfl, appD.valid_view (d.project m_srv), hview m_srv, congrArg Html.render (hview m_srv)⟩

/-! ## SSR Binary RPC Routing Closure (`ssr_rpc_endpoint_routed`) -/

def ssrDispatchRpc (srvShort : String) (methods : List String)
    (dispatchMethod : String → ByteArray → Except String ByteArray) (reqMethod url : String) (reqBody : ByteArray) : Except String ByteArray :=
  let rpcPrefix := "/_qed/rpc/" ++ srvShort ++ "/"
  let uPath := String.ofList (url.toList.takeWhile (· ≠ '?'))
  if reqMethod == "POST" && uPath.startsWith rpcPrefix then
    let mName := String.ofList (uPath.toList.drop rpcPrefix.length)
    if mName ∈ methods then dispatchMethod mName reqBody else .error s!"SSR unknown binary RPC method: {mName}"
  else .error s!"SSR unknown binary RPC endpoint: {url}"

theorem ssr_rpc_endpoint_routed (srvShort : String) (methods : List String)
    (dispatchMethod : String → ByteArray → Except String ByteArray) (srv m : String) (reqBody : ByteArray)
    (hsrv : srv = srvShort) (hm : m ∈ methods) (hsrvNoQ : ∀ c ∈ srvShort.toList, c ≠ '?') (hmNoQ : ∀ c ∈ m.toList, c ≠ '?') :
    ssrDispatchRpc srvShort methods dispatchMethod "POST" ("/_qed/rpc/" ++ srv ++ "/" ++ m) reqBody = dispatchMethod m reqBody := by
  subst srv; let pfx := "/_qed/rpc/" ++ srvShort ++ "/"
  have hnoQ : ∀ c ∈ (pfx ++ m).toList, c ≠ '?' := fun c hc => by
    simp only [pfx, String.toList_append, List.mem_append] at hc
    rcases hc with ((h | h) | h) | h
    · exact (by decide : ∀ x ∈ "/_qed/rpc/".toList, x ≠ '?') c h
    · exact hsrvNoQ c h
    · exact (by decide : ∀ x ∈ "/".toList, x ≠ '?') c h
    · exact hmNoQ c h
  unfold ssrDispatchRpc; dsimp only
  rw [show String.ofList ((pfx ++ m).toList.takeWhile (· ≠ '?')) = pfx ++ m by rw [list_takeWhile_eq_self _ fun c hc => decide_eq_true (hnoQ c hc), String.ofList_toList],
      show (pfx ++ m).startsWith pfx = true by simp [String.startsWith],
      show (pfx ++ m).toList.drop pfx.length = m.toList by rw [String.toList_append, ← String.length_toList (s := pfx), List.drop_left]]
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, String.ofList_toList, hm]

theorem ssr_rpc_closure_complete (srvShort : String) (methods : List String)
    (usedRpcs : List (String × String)) (hclosed : ∀ ep ∈ usedRpcs, ep.1 = srvShort ∧ ep.2 ∈ methods)
    (dispatchMethod : String → ByteArray → Except String ByteArray)
    (hsrvNoQ : ∀ c ∈ srvShort.toList, c ≠ '?') (hmNoQ : ∀ ep ∈ usedRpcs, ∀ c ∈ ep.2.toList, c ≠ '?')
    (ep : String × String) (hep : ep ∈ usedRpcs) (reqBody : ByteArray) :
    ssrDispatchRpc srvShort methods dispatchMethod "POST" ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody = dispatchMethod ep.2 reqBody :=
  ssr_rpc_endpoint_routed srvShort methods dispatchMethod ep.1 ep.2 reqBody (hclosed ep hep).1 (hclosed ep hep).2 hsrvNoQ (hmNoQ ep hep)

end Qed
