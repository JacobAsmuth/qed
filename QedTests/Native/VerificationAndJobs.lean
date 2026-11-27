import Qed
import Qed.Server.Native
import Cli.Common
import QedTests.Native.Harness
import QedTests.CssChecks
import QedTests.SyntaxChecks
open System (FilePath)
open Qed Qed.Server

namespace QedTests.Native.VerificationAndJobs

private def localDomHarnessJs : String := r#"
import assert from 'node:assert/strict';
class NodeBase {
  constructor(t) { this.nodeType = t; this.parentNode = null; }
  get isConnected() { for (let p = this; p; p = p.parentNode) if (p === document.body) return true; return false; }
  get nextSibling() { const cs = this.parentNode?.childNodes, i = cs ? cs.indexOf(this) : -1; return i >= 0 && i + 1 < cs.length ? cs[i + 1] : null; }
  get previousSibling() { const cs = this.parentNode?.childNodes, i = cs ? cs.indexOf(this) : -1; return i > 0 ? cs[i - 1] : null; }
}
class TextNode extends NodeBase {
  constructor(s) { super(3); this.nodeValue = String(s); }
  get textContent() { return this.nodeValue; } set textContent(v) { this.nodeValue = String(v); }
}
class Elem extends NodeBase {
  constructor(tag, ns = '') { super(tag === '#fragment' ? 11 : 1); this.localName = tag; this.tagName = tag.toUpperCase(); this.namespaceURI = ns; this.childNodes = []; this._a = new Map(); this._l = new Map(); this.value = ''; this.checked = false; }
  get firstChild() { return this.childNodes[0] ?? null; }
  get firstElementChild() { return this.childNodes.find((c) => c.nodeType === 1) ?? null; }
  get attributes() { return [...this._a.entries()].map(([name, value]) => ({ name, localName: name, namespaceURI: null, value })); }
  getAttribute(k) { return this._a.has(k) ? this._a.get(k) : null; } setAttribute(k, v) { this._a.set(k, String(v)); }
  removeAttribute(k) { this._a.delete(k); } removeAttributeNS(_, k) { this._a.delete(k); } hasAttribute(k) { return this._a.has(k); }
  get textContent() { return this.childNodes.map((c) => c.textContent).join(''); }
  set textContent(v) { for (const c of this.childNodes) c.parentNode = null; this.childNodes = []; const s = String(v); if (s !== '') this.appendChild(new TextNode(s)); }
  set innerHTML(s) { this.textContent = ''; if (s !== '') parseInto(this, s); }
  _det(c) { if (c.parentNode) { const a = c.parentNode.childNodes, i = a.indexOf(c); if (i >= 0) a.splice(i, 1); c.parentNode = null; } }
  appendChild(c) { if (c.nodeType === 11) { for (const k of [...c.childNodes]) this.appendChild(k); return c; } this._det(c); this.childNodes.push(c); c.parentNode = this; return c; }
  insertBefore(c, r) { if (!r) return this.appendChild(c); if (c.nodeType === 11) { for (const k of [...c.childNodes]) this.insertBefore(k, r); return c; } this._det(c); const i = this.childNodes.indexOf(r); i < 0 ? this.childNodes.push(c) : this.childNodes.splice(i, 0, c); c.parentNode = this; return c; }
  removeChild(c) { const i = this.childNodes.indexOf(c); if (i >= 0) { this.childNodes.splice(i, 1); c.parentNode = null; } return c; }
  replaceChild(n, o) { const i = this.childNodes.indexOf(o); if (i >= 0) { this._det(n); o.parentNode = null; this.childNodes[i] = n; n.parentNode = this; } return o; }
  replaceChildren(...xs) { for (const c of this.childNodes) c.parentNode = null; this.childNodes = []; for (const x of xs) this.appendChild(x); }
  addEventListener(ev, fn) { (this._l.get(ev) || this._l.set(ev, []).get(ev)).push(fn); }
  matches(sel) { return sel.split(',').some((raw) => { const s = raw.trim(); if (s.startsWith('[') && s.endsWith(']')) return this.hasAttribute(s.slice(1, -1)); if (s.startsWith('.')) return (this.getAttribute('class') || '').split(/\s+/).includes(s.slice(1)); const m = /^([a-z0-9-]+)\[([a-z0-9-]+)\]$/i.exec(s); return m ? this.localName === m[1].toLowerCase() && this.hasAttribute(m[2]) : this.localName === s.toLowerCase(); }); }
  closest(sel) { for (let c = this; c && c.nodeType === 1; c = c.parentNode) if (c.matches(sel)) return c; return null; }
  find(sel) { if (this.matches(sel)) return this; for (const c of this.childNodes) if (c.nodeType === 1) { const r = c.find(sel); if (r) return r; } return null; }
}
const voids = new Set(['input', 'img', 'br', 'hr', 'meta', 'link']);
function parseInto(root, html) {
  const st = [root], re = /<(\/?)([a-zA-Z0-9-]+)([^>]*)>|([^<]+)/g;
  for (let m; (m = re.exec(html)) !== null;) {
    if (m[4] !== undefined) { if (m[4].length) st[st.length - 1].appendChild(new TextNode(m[4])); }
    else if (m[1] === '/') st.pop();
    else {
      const tag = m[2].toLowerCase(), el = new Elem(tag);
      for (const am of m[3].matchAll(/([a-zA-Z0-9_:-]+)(?:="([^"]*)")?/g)) { const v = (am[2] ?? '').replace(/&quot;/g, '"').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>'); el.setAttribute(am[1], v); if (am[1] === 'value') el.value = v; }
      st[st.length - 1].appendChild(el); if (!voids.has(tag) && !m[3].trimEnd().endsWith('/')) st.push(el);
    }
  }
}
const body = new Elem('body'), head = new Elem('head'), appEl = new Elem('div'); appEl.setAttribute('id', 'app'); body.appendChild(appEl); let stateEl = null;
globalThis.window = { addEventListener() {} }; globalThis.location = { pathname: '/', search: '', protocol: 'http:', host: 'localhost' }; globalThis.history = { pushState() {}, replaceState() {} };
globalThis.document = { readyState: 'complete', body, head, createElement: (t) => new Elem(t), createElementNS: (ns, t) => new Elem(t, ns), createTextNode: (s) => new TextNode(s), createDocumentFragment: () => new Elem('#fragment'), getElementById: (id) => id === 'app' ? appEl : id === 'qed-state' ? stateEl : null, querySelector: () => null, addEventListener() {} };
const $ = (s) => appEl.find(s), eqAttr = (s, k, w) => assert.equal($(s).getAttribute(k), w);
const tap = (s) => { const el = $(s); assert.ok(el, `missing click ${s}`); for (const fn of (appEl._l.get('click') || [])) fn({ target: el, button: 0, preventDefault() {} }); };
const typeIn = (s, v) => { const el = $(s); assert.ok(el, `missing input ${s}`); el.value = v; for (const fn of (appEl._l.get('input') || [])) fn({ target: el, preventDefault() {} }); };
const outDir = process.argv[2]; await import(`${outDir}/qed_host.mjs`); const mod = await import(`${outDir}/app.mjs`);
assert.equal($('.plain-page').firstChild.nodeType, 3); tap('.p1'); eqAttr('.local-panel', 'data-mode', '0'); tap('.toggle'); eqAttr('.local-panel', 'data-mode', '1');
for (const [cls, want] of [['.new0', 'new0'], ['.new1', 'new1'], ['.card0', 'card0'], ['.card1', 'card1'], ['.knew', 'knew'], ['.kcard', 'kcard']]) { tap(cls); eqAttr('.local-panel', 'data-last', want); eqAttr('.root', 'data-bubbled', want); }
typeIn('.in-new', 'n-val'); eqAttr('.local-panel', 'data-new', 'n-val'); eqAttr('.local-panel', 'data-card', '');
typeIn('.in-card', 'c-val'); eqAttr('.local-panel', 'data-card', 'c-val'); eqAttr('.local-panel', 'data-new', 'n-val');
tap('.p2'); assert.equal($('.local-panel'), null); eqAttr('.leaf', 'data-label', 'alt'); tap('.leaf-inc'); eqAttr('.leaf', 'data-n', '1');
tap('.p0'); assert.equal($('.plain-page').textContent, 'Loading text child'); tap('.p2'); eqAttr('.leaf', 'data-n', '0');
for (const [clicks, lbl, n] of [[['.p3', '.leaf-inc'], null, '1'], [['.p4'], 'in-b', '1'], [['.leaf-inc'], null, '2'], [['.p6', '.leaf-inc'], null, '1'], [['.p7'], 's1', '1'], [['.leaf-inc'], null, '2'], [['.p6'], 's0', '2']]) { for (const s of clicks) tap(s); if (lbl !== null) eqAttr('.leaf', 'data-label', lbl); eqAttr('.leaf', 'data-n', n); }
tap('.p5'); tap('.leaf-inc'); eqAttr('.leaf', 'data-n', '1'); tap('.nest-toggle'); assert.equal($('.leaf'), null); tap('.nest-toggle'); eqAttr('.leaf', 'data-n', '0'); tap('.leaf-inc'); eqAttr('.leaf', 'data-n', '1');
window.__qedHost.active().teardown(); appEl.innerHTML = mod.ssr_page1();
stateEl = new Elem('script'); stateEl.setAttribute('id', 'qed-state'); stateEl.textContent = mod.state_page1(); body.appendChild(stateEl);
const ssrPanel = $('.local-panel'); assert.ok(ssrPanel); globalThis.__qed.nodes = [null]; globalThis.__qed.free = [];
mod.__main(0); mod.qed_init(0); assert.equal($('.local-panel'), ssrPanel);
tap('.toggle'); eqAttr('.local-panel', 'data-mode', '1'); tap('.new0'); eqAttr('.local-panel', 'data-last', 'new0'); console.log('OK');
"#

private def runLocalDomJsTest (c : TestChecker) : IO Unit := do
  let (root, qedjs, lp) := (← IO.currentDir, ← qedjsBinPath, ← getLeanPath)
  withTempDir "qed-local-dom-test" fun dir => do
    let outDir := FilePath.mk dir
    for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do IO.FS.writeFile (outDir / f) (← IO.FS.readFile (root / "runtime" / f))
    let entries := Qed.Cli.driverEntries.map (fun e => if e == "main:__main" then "JsGate.localBugsMain:__main" else e) ++ #["JsGate.localBugsSsrPage1:ssr_page1", "JsGate.localBugsStatePage1:state_page1"]
    let (jc, jo, je) ← runCmd qedjs (#["--rt", (root / "runtime" / "qed_rt.mjs").toString, (outDir / "app.mjs").toString, "QedTests.JsGate", "--"] ++ entries) (cwd := some root) (env := #[("LEAN_PATH", some lp)])
    c.check "qedjs compiles LocalBugsApp fixture" (jc == 0) (jo ++ je)
    if jc != 0 then return
    let harness := outDir / "run.mjs"; IO.FS.writeFile harness localDomHarnessJs
    let (nc, no, ne) ← runCmd "node" #[harness.toString, outDir.toString]
    c.check "JS/DOM localCell remount, reused-div clear, handler indices & SSR hydration" (nc == 0 && no.contains "OK") (no ++ ne)

section MovedChecks
open CssChecks SyntaxChecks

private def runMovedCssAndSyntaxChecks (c : TestChecker) : IO Unit := do
  let hasAll (s : String) (xs : List String) := xs.all (s.contains ·)
  let rt {α β : Type} [BEq α] (enc : α → β) (dec : β → Except String α) (x : α) := (dec (enc x)).toOption == some x
  let showcaseCss := renderStyleSheet StyledShowcase.app.styles
  let ssr := Html.renderWith Counter.regs (<div><style>{".a > .b { content: \"</style>\"; }"}</style><br/>{defaults}</div> : Html Unit)
  let (draft, vd) : Ticket.Draft × Ticket.Draft := ({ title := "Fix parser", priority := "2" }, { title := "Fix bug", priority := "3", kind := "bug" })
  let (jx, jxElseT, jxElseF) := (Html.render (jsxErgonomicsView #[1, 2] (some "ok") true), Html.render (jsxElseBranchesView (some "hi") true [<span>ex</span>]), Html.render (jsxElseBranchesView none false [<span>ex</span>]))
  let gl := Html.render (GoodLazy.app.view { m := 7 })
  let cs := Html.render (<Card title="Docs" badge={<span class="badge">v2</span>}><p>First</p><ul><ListChip key="a" text="Alpha"/></ul></Card> : Html Unit)
  let cd1 := CompositeDemo.update CompositeDemo.init (._sub_0 (._emit (.set_filter "lean4")))
  let cd2 := CompositeDemo.update cd1 (._sub_0 (._emit (.onPick "lean4"))); let cd3 := CompositeDemo.update cd2 (._sub_1 .toggle)
  let updPy := PythonicShowcase.update PythonicShowcase.init
  let (recS, tickEv) := (RoomSnapshotRec.sample, TickEvent.tick 7 "go")
  let pfRendered := Html.render (PureForwardHost.view PureForwardHost.init)
  let (_, pfHs) := renderNode #[] (PureForwardHost.view PureForwardHost.init)
  let pf1 := PureForwardHost.update PureForwardHost.init (pfHs[0]?.getD (.setLang "")); let pf2 := PureForwardHost.update pf1 (pfHs[1]?.getD (.setLang ""))
  let spStep (s : SessionParentShell.State) (m : SessionParentShell.Msg) := (SessionParentShell.update s m).1
  let s1 := spStep SessionParentShell.init (._onSession (some "alice")); let s2 := spStep s1 (._onRoute .account); let s3 := spStep s2 (._onRoute .tokens)
  let s4 := spStep s3 (._onRoute .home); let s5 := spStep s4 .bumpNested; let s6 := spStep s5 (.replaceItems #["one"]); let s7 := spStep s6 (.optimisticAdd "two")
  let (sBumped, cRef) := SessionParentShell.app.update s7 .refreshItems
  let countReqs (cmd : Cmd SessionParentShell.Msg) : Nat := (Cmd.flatten cmd).foldl (fun n x => match x with | .requestBytes .. => n + 1 | _ => n) 0
  let sAcct := (SessionParentShell.app.update s7 (._onRoute .account)).1
  let (_, cCoal1) := SessionParentShell.app.update sAcct (.searchAndRefetch "abc"); let (_, cCoal2) := SessionParentShell.app.update sAcct (.refetchThenSearch "def")
  let (sOff, _) := SessionParentShell.app.update { s7 with homeItems := s7.homeItems.setKey (SessionParentShell._qKey_homeItems s7) #["stale"] } (._onRoute .account)
  let (sOffInv, cOffInv) := SessionParentShell.app.update sOff .invBoth; let (sBack, cBack) := SessionParentShell.app.update sOffInv (._onRoute .home)
  let cAfterStale := sBumped.items.putRev (SessionParentShell._qKey_items s7) (.ok #["old"]) (SessionParentShell._qKey_items sBumped)
  let (_, cExt) := SessionParentShell.update s7 .goExternal; let uOk := url("https://checkout.stripe.com/c/pay_1")
  let (rOff, rOn) := (Html.render (MultiStyleSpliceDemo.view MultiStyleSpliceDemo.init), Html.render (MultiStyleSpliceDemo.view { active := true }))
  let c0 : Cached Nat := ({} : Cached Nat).setKey "k" 10; let c1 := c0.updateCurrent "k" (· + 5); let c2 := c1.map (· * 2); let c3 := c2.invalidateKey "k"
  let (cOk, cLoad, cIdle) : Cached Nat × Cached Nat × Cached Nat := ({ state := .ok 8 }, { state := .loading }, { state := .idle })
  c.checkAll [
    ("[css] AppTheme.style.raw renders :root, dark media/attr, & reset", hasAll AppTheme.style.raw [":root {", "@media (prefers-color-scheme: dark)", "[data-theme=\"dark\"]", ":where(*) { box-sizing: border-box; margin: 0; }"]),
    ("[css] primaryBtn.raw extends baseBtn, overrides border, & attaches fadeIn keyframes",
      hasAll primaryBtn.raw ["background-color: var(--brand);", "border: 1px solid var(--brand);", "&:hover { opacity: 1; transform: translateY(-1px); }", "@media (max-width: 600px) { width: 100%; }"] && !primaryBtn.raw.contains "#d1d5db" && primaryBtn.extraRules.any (·.contains "@keyframes fadeIn")),
    ("[css] modernStyle.raw renders dvh/clamp/oklch/dark media", hasAll modernStyle.raw ["box-sizing: border-box;", "min-height: 100dvh;", "clamp(20rem, 50vw, 45rem)", "oklch(0.6 0.15 250)", "@media (prefers-color-scheme: dark)"]),
    ("[css] renderStyleSheet StyledShowcase + renderDocument stylesheet link",
      hasAll showcaseCss [":root {", "@media (prefers-color-scheme: dark)", StyledCard.wrapper.className, StyledShowcase.shell.className, StyledShowcase.pillActive.className, "border-radius: 999px;", "padding: 0.5rem; margin-top: 1rem;"] &&
      (renderDocument "Demo" "" (stylesheets := StyledShowcase.app.stylesheets)).contains "<link rel=\"stylesheet\" href=\"/app.css\">"),
    ("[syn] SSR Counter, Owned, style escape, DocRoute/RepoRoute, Rehydrate, JSX ergonomics",
      (Html.renderWith Counter.regs defaults).contains "8</button>" && (Html.render (<Owned state={{ id = 4, count = 2 }} caption="Live" onMsg={Prod.mk}/> : Html (String × Owned.Msg))).contains "Live" &&
      hasAll ssr [".a > .b", "<\\/style>", "8</button>"] && !ssr.contains "</br>" && Router.toURL (DocRoute.sec .architecture 2) == "/docs/arch/2" &&
      [("/docs/bench/5", some (DocRoute.sec .benchmarks 5)), ("/docs/unknown/5", none), ("/docs/arch/2?tab=api#top", some (DocRoute.sec .architecture 2)), ("/?utm=1#hero", some DocRoute.home)].all (fun (u, w) => Router.fromURL u == w) &&
      (RoutedDehydrated.app.rehydrate (RoutedDehydrated.app.dehydrate { r := .sec .benchmarks 3 })).map (·.r) == some (.sec .benchmarks 3) &&
      (Html.render (TypedLink.view { target := .sec .architecture 2 } { cur := .home })).contains "href=\"/docs/arch/2\"" && (renderStyleSheet AutoStyled.app.styles).contains navOn.raw &&
      ResetTheme.style.raw.contains ":where(*, *::before) { margin: 0px; }" && typedBorderStyle.raw == "border: 1px solid var(--border-subtle); border-bottom: 2px dashed #333; border-top: none;" &&
      (Html.render (ParentPage.view { route := .sec .architecture 3 })).contains "/docs/arch/1" && Router.toURL (RepoRoute.edit "acme" "qed") == "/orgs/acme/repos/qed/edit" &&
      [("/orgs/acme/repos/qed/edit", some (RepoRoute.edit "acme" "qed")), ("/orgs/acme/repos/qed", some (RepoRoute.blob "acme" "qed")), ("/orgs/acme/issues/3", some (RepoRoute.issues "acme" 3))].all (fun (u, w) => Router.fromURL u == w) &&
      ((Json.parse (Json.render (toJson draft))).bind fromJson).toOption == some draft && hasAll jx ["<p>ok</p>", "<li>3</li><li>4</li>"] &&
      !(Html.render (jsxErgonomicsView #[] none false)).contains "<em>" && hasAll jxElseT ["<span>yes</span>", "<p>hi</p>", "<span>ex</span><span>ex</span>"] &&
      hasAll jxElseF ["<span>no</span>", "<p>empty</p>", "<b>f1</b><b>f2</b>", "<i>m1</i><i>m2</i>"] &&
      (RichAuto.app.rehydrate (RichAuto.app.dehydrate { tab := .tagged "lean", notes := #[{ id := 1, text := "hello" }], pick := some { id := 2, text := "pinned" }, cache := ({} : Cached String).put "k" (.ok "v") "k", child := { count := 42, saved := 0 } })).map
        (fun m => m.tab == .tagged "lean" && m.notes == #[{ id := 1, text := "hello" }] && m.pick == some { id := 2, text := "pinned" } && m.cache.lookup "k" == some "v" && m.child.count == 42) == some true &&
      ((PartialFn.app.rehydrate (PartialFn.app.dehydrate { count := 8, fn := (· * 2) })).map fun m => (m.count, m.fn 5)) == some (8, 15)),
    ("[syn] GoodLazy, fracStyle, Resource/Cached, Card/CompositeDemo, Await, EarlyReturn rehydrate",
      hasAll gl ["href=\"/docs/guide\"", "<span>3</span>"] && fracStyle.raw == "text-align: center; padding: 0.35rem 0 0.5rem; margin: 2rem auto; gap: 4px 8px; line-height: 1.5; font-weight: 600; opacity: 0.85; z-index: -1;" &&
      (match (Resource.ok (none : Option Nat)).someOr "missing" with | .failed "missing" => true | _ => false) && (match (Resource.ok (some 42)).someOr "missing" with | .ok 42 => true | _ => false) &&
      (match (({} : Cached Nat).put "a" (.ok 1) "b").state with | .idle => true | _ => false) && ((({} : Cached Nat).put "a" (.ok 1) "b").lookup "a" == some 1) && (match (({} : Cached Nat).put "a" (.ok 7) "a").state with | .ok 7 => true | _ => false) &&
      hasAll cs ["<h3>Docs</h3><span class=\"badge\">v2</span>", "<li class=\"chip\">Alpha</li>"] && !cs.contains "data-qed-local" && cd1.query == "lean4" && cd2.picked == "lean4" &&
      !(Html.render (CompositeDemo.view CompositeDemo.init)).contains "class=\"panel\"" && (Html.render (CompositeDemo.view cd3)).contains "class=\"panel\"" &&
      (CompositeDemo.app.rehydrate (CompositeDemo.app.dehydrate { cd3 with clicks := 5, scratch := 0 })).map (fun s => (s.query, s.clicks, s.scratch)) == some ("lean4", 5, 99) &&
      (Html.render (awaitSample .loading)).contains "<p>Wait</p>" && (Html.render (awaitSample (.failed "boom"))).contains "<p class=\"err\">boom</p>" &&
      (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := 5 })).map (·.x) == some 5 && (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := -1 })).isNone),
    ("[syn] SelfHostedForm, PythonicShowcase, Json.pathStr",
      SelfHostedFormKeep.init.picked.isNone && SelfHostedFormKeep.init._form_0 == Ticket.Draft.empty && (Html.render (SelfHostedFormKeep.view SelfHostedFormKeep.init)).contains "disabled" &&
      !(Html.render (SelfHostedFormKeep.view { picked := none, _form_0 := vd })).contains "disabled" &&
      (match Ticket.parse vd with | some t => let sK := SelfHostedFormKeep.update { picked := none, _form_0 := vd } (.set_picked (some t)); let sR := SelfHostedFormReset.update { picked := none, _form_0 := vd } ._form_reset_0; sK.picked.map (·.title.val) == some t.title.val && sK._form_0 == vd && sR.picked.map (·.title.val) == some t.title.val && sR._form_0 == Ticket.Draft.empty | none => false) &&
      [(.classify 5, "low:5"), (.classify 25, "mid:25"), (.classify 80, "high:80"), (.addTag "qed", "tags:2"), (.usePick, "score=4"), (.describeTab (.tagged "ui"), "tag:ui"), (.exprBranches 3 (some 7), "pos:7"), (.exprBranches 0 none, "zero:none")].all (fun (m, want) => (updPy m).label == want) &&
      (updPy (.addTag "lean")).tags.size == 1 && (Html.render (PythonicShowcase.view PythonicShowcase.init)).contains "has-lean" &&
      Json.pathStr "{\"choices\":[{\"delta\":{\"content\":\"hi\"}}]}" "choices.0.delta.content" == "hi" && Json.pathStr "{\"choices\":[]}" "choices.0.delta.content" == ""),
    ("[syn] Enum/Record/Schema/RoomFrameMap encode/decode & PureForwardHost",
      (GamePhase.ofString (toString GamePhase.playing)).toOption == some .playing && rt GamePhase.encode GamePhase.decode .playing && rt GamePhase.encodeBytes GamePhase.decodeBytes .playing &&
      rt RoleCard.encode RoleCard.decode (.agent "Pilot" (some "ok")) && rt RoleCard.encodeBytes RoleCard.decodeBytes (.agent "Pilot" none) &&
      rt TickEvent.encode TickEvent.decode tickEv && rt TickEvent.encodeBytes TickEvent.decodeBytes tickEv && rt RoomSnapshotRec.encode RoomSnapshotRec.decode recS && rt RoomSnapshotRec.encodeBytes RoomSnapshotRec.decodeBytes recS &&
      rt OptSchema.encode OptSchema.decode { title := "x", note := some "n", phase := some .playing } && rt OptSchema.encode OptSchema.decode { title := "x", note := none, phase := none } &&
      (RoomFrameMap.decode (RoomFrameMap.encode recS).val).toOption == some recS &&
      hasAll pfRendered ["class=\"lang-select\"", "data-qed-local=\"SyntaxChecks.KeyedTagPicker@tp\""] && PureForwardHost.app.locals.any (·.id == "SyntaxChecks.KeyedTagPicker") && pf1.lang == "fr" && pf2.lang == "en"),
    ("[syn] SessionParentShell, query coalescing/invalidation, Url codecs, headInfo",
      s1._sub_0.user == some "alice" && s2.visits == 1 && s2._sub_0.user == some "alice" && s3.visits == 2 && s3._sub_0.user == some "alice" && s4._sub_0.user == some "alice" &&
      s5.flt.page == 1 && s5.flt.tags == #["z", "b"] && s6.items.getD #[] == #["one"] && s6.items.isOk && s7.items.getD #[] == #["one", "two"] &&
      (match cRef with | .none => false | _ => true) && countReqs cCoal1 == 1 && countReqs cCoal2 == 1 && sOffInv.homeItems.seen.isEmpty && countReqs cOffInv == 1 &&
      sBack.homeItems.isLoading && countReqs cBack == 1 && cAfterStale.getD #[] != #["old"] && cAfterStale.seen.isEmpty &&
      (match cExt with | .fx "location.assign" "https://checkout.stripe.com/c/pay_1" "" "" => true | _ => false) &&
      (Qed.FromJson.fromJson (α := Qed.Url) (Qed.ToJson.toJson uOk)).toOption == some uOk && (Qed.Proto.decode (α := Qed.Url) (Qed.Proto.encode uOk)).toOption == some uOk &&
      !(Qed.FromJson.fromJson (α := Qed.Url) (.str "javascript:alert(1)")).isOk && !(Qed.Proto.decode (α := Qed.Url) (Qed.Proto.encode "javascript:alert(1)")).isOk &&
      (SessionParentShell.headInfo s2).1.title == some "Settings" && (SessionParentShell.headInfo s2).1.canonical == some "https://qed.cloud/account" &&
      (SessionParentShell.headInfo s2).1.redirect == some "/" && (SessionParentShell.headInfo s2).2 == 301 &&
      (SessionParentShell.headInfo s4).1.title == some "Home" && (SessionParentShell.headInfo s4).1.canonical == some "/"),
    ("[syn] PolishRoute, Fields, Date, PolishEvent, MultiStyleSplice, Cached, Qed.Str, Qed.Time",
      (PolishRoute.item "42").toPath == "/items/42" && PolishRoute.fromPath "/items/42" == some (.item "42") && toString (PolishRoute.item "42") == "/items/42" &&
      (PolishRoute.appTab (ShortSlug.make "my-app") .deployLogs).toPath == "/apps/my-app/deploy-logs" && PolishRoute.fromPath "/apps/my-app/database" == some (.appTab (ShortSlug.make "my-app") .db) &&
      ShortSlug.parse? "" == none && ShortSlug.parse? "ok" == some (ShortSlug.make "ok") && !(ShortSlug.parse "").isOk && (ServicePort.make 8080).val == 8080 && ServicePort.parse? 0 == none &&
      (BoundedStr.make 16 "hello").val == "hello" && BoundedStr.parse? 4 "too-long" == none && (ServiceFieldForm.parse { slug := "api", port := "8080", tag := "v1" }).isSome &&
      (ServiceFieldForm.parse { slug := "", port := "8080", tag := "v1" }).isNone && (ServiceFieldForm.parse { slug := "api", port := "70000", tag := "v1" }).isNone &&
      (Html.render (ServiceFieldForm.formView { slug := "api", port := "8080", tag := "v1" } id (fun _ => ServiceFieldForm.Draft.empty))).contains "type=\"number\"" &&
      (match Date.mk? 2026 11 25 with | some d => (PolishRoute.report d).toPath == "/reports/2026-11-25" && PolishRoute.fromPath "/reports/2026-11-25" == some (.report d) | none => false) &&
      (match Date.mk? (-44) 3 15 with | some d => d.toString == "-0044-03-15" && Date.parse? d.toString == some d | none => false) &&
      LawfulKey.toKey PolishTab.deployLogs == "deploy-logs" && LawfulKey.toKey (ShortSlug.make "my-app") == "my-app" &&
      (PolishEvent.encode (.deployStarted "r1")).contains "\"deploy-started\"" && rt PolishEvent.encode PolishEvent.decode (.deployFailed "oom") &&
      rOff.contains spliceBaseBtn.className && !rOff.contains spliceActiveBtn.className && rOn.contains spliceBaseBtn.className && rOn.contains spliceActiveBtn.className &&
      c0.getD 0 == 10 && c1.getD 0 == 15 && c2.getD 0 == 30 && !c3.isOk && Qed.Str.trim "  hi\t\n " == "hi" && Qed.Str.containsCI "Hello Qed" "qed" &&
      Qed.Str.startsWith "foobar" "foo" && Qed.Str.endsWith "foobar" "bar" && Qed.Str.split "a::b::c" "::" == ["a", "b", "c"] && Qed.Str.replace "a-b-c" "-" "_" == "a_b_c" &&
      Qed.Str.truncate "abcdef" 5 == "ab..." && Qed.Str.parseNat? "42" == some 42 && Qed.Str.parseInt? "-7" == some (-7) && Qed.Time.formatIsoUtc 0 == "1970-01-01T00:00:00Z" &&
      Qed.Time.formatDateUtc (11016 * 86400) == "2000-02-29" && Qed.Time.formatUtc 1700000000 == "2023-11-14 22:13 UTC" && Qed.Time.formatDuration 125 == "2m 5s" && Qed.Time.formatRelative 1000 700 == "5m ago"),
    ("[syn] for/range/break/continue, ??, dedupBy, Json.object",
      sumRange1 5 == 10 && sumRange2 2 6 == 14 && sumRange2 5 2 == 0 && sumRange3 1 10 3 == 12 && sumRange3 0 10 0 == 0 &&
      findFirstOver #[1, 5, 20, 40] 10 == some 20 && findFirstOver #[1, 150, 20] 10 == none && collectEvens 7 == #[0, 2, 4, 6] && nestedBreak 3 5 == 63 && mutArith 10 == 9 &&
      coalesceOpt none (some 7) 99 == 7 && coalesceOpt (some 3) (some 7) 99 == 3 && coalesceOpt none none 99 == 99 &&
      coalesceRes (.ok 12) 0 == 12 && coalesceRes .loading 55 == 55 && coalesceRes (.failed "boom") 55 == 55 &&
      coalesceCached cOk 0 == 8 && coalesceCached cLoad 44 == 44 && coalesceCached cIdle 44 == 44 && cOk.get? == some 8 && cLoad.get? == none && cIdle.get? == none &&
      #[("a", 1), ("b", 2), ("a", 9), ("c", 3), ("b", 7)].dedupBy (·.1) == #[("a", 1), ("b", 2), ("c", 3)] &&
      Json.render (Json.object #[("k", Json.str "v"), ("n", Json.num ⟨7, 0⟩)]) == "{\"k\":\"v\",\"n\":7}")]
end MovedChecks

server JobRunnerDemo:
  state ticks  : Nat = 0
  state resets : Nat = 0
  invariant bounded: ticks <= 50
  invariant mono: resets >= old(resets)
  rpc getTicks() -> Nat: return ticks
  every 15ms heartbeat: if ticks < 50: ticks += 1
  every 40ms markReset: atomic: resets += 1

def run : IO Bool := do
  let c ← mkChecker "verification-and-jobs"
  runTasks [runLocalDomJsTest c, runMovedCssAndSyntaxChecks c, (do
    let big := ByteArray.mk ((List.range 65536).toArray.map fun i => UInt8.ofNat ((i * 37 + 13) % 256)); let bigEnc := Base64.encode big
    let sampleBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0xFF]
    c.checkAll ([("base64 empty encode", Base64.encode ByteArray.empty == ""), ("base64 empty decode", Base64.decode "" == .ok ByteArray.empty),
      ("base64 64KiB encoded length", bigEnc.length == ((65536 + 2) / 3) * 4), ("base64 64KiB round-trip", Base64.decode bigEnc == .ok big),
      ("base64 rejects invalid length", !(Base64.decode "abc").isOk), ("base64 rejects invalid char", !(Base64.decode "ab!d").isOk)] ++
      ([1, 2, 3, 256].map fun n => let bs := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i % 256)); (s!"base64 round-trip ({n} bytes)", Base64.decode (Base64.encode bs) == .ok bs)))
    c.expectOk "FileBytes.decode ok" (FileBytes.decode (Json.render (.obj [("name", .str "icon.png"), ("mime", .str "image/png"), ("size", .num ⟨10, 0⟩), ("base64", .str (Base64.encode sampleBytes))]))) fun fb =>
      c.checkEq "FileBytes fields match" (fb.name, fb.mime, fb.size, fb.bytes) ("icon.png", "image/png", 10, sampleBytes)
    c.checkErrContains "FileBytes.decode propagates host error" (FileBytes.decode "{\"error\":\"file too large (200 bytes; max 100)\"}") "file too large"
    let srvInst : MonadServer IO := Qed.Server.Native.mkNativeServerInst none
    let mkJobs := do let box ← Prim.mkStateBox JobRunnerDemo.initState; return (box, JobRunnerDemo.jobs.map (·.toIoJob srvInst (Qed.Server.Native.withStateBox box)), ← IO.mkRef false)
    let (box, ioJobs, stopFlag) ← mkJobs; c.checkEq "JobRunnerDemo job count" ioJobs.size 2
    for t in ← Qed.Server.runServerJobs ioJobs (stopFlag? := some stopFlag) (maxTicks := 5) do if let .error e ← IO.wait t then c.check "job task exited cleanly" false (toString e)
    let st1 ← Prim.atomicRead box id; c.checkEq "heartbeat & markReset ran 5 ticks" (st1.ticks, st1.resets) (5, 5); c.check "final state preserves bounded invariant" (st1.ticks ≤ 50)
    let (box2, ioJobs2, stopFlag2) ← mkJobs; let tasks2 ← Qed.Server.spawnServerJobs ioJobs2 (stopFlag? := some stopFlag2) (maxTicks := 1000)
    IO.sleep 60; stopFlag2.set true; for t in tasks2 do discard <| IO.wait t
    let st2 ← Prim.atomicRead box2 id; c.check "background job ticked before stopFlag" (st2.ticks ≥ 1 && st2.ticks < 50))]
  c.finish

end QedTests.Native.VerificationAndJobs
