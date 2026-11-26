import Qed
import Qed.Server.Native
import Cli.Common
import QedTests.Native.Harness
open System (FilePath)
open Qed Qed.Server

namespace QedTests.Native.VerificationAndJobs

private def localDomHarnessJs : String := r#"
import assert from 'node:assert/strict';
class NodeBase {
  constructor(t) { this.nodeType = t; this.parentNode = null; }
  get isConnected() { for (let p = this; p; p = p.parentNode) if (p === document.body) return true; return false; }
  get nextSibling() { const cs = this.parentNode?.childNodes; const i = cs ? cs.indexOf(this) : -1; return i >= 0 && i + 1 < cs.length ? cs[i + 1] : null; }
  get previousSibling() { const cs = this.parentNode?.childNodes; const i = cs ? cs.indexOf(this) : -1; return i > 0 ? cs[i - 1] : null; }
}
class TextNode extends NodeBase {
  constructor(s) { super(3); this.nodeValue = String(s); }
  get textContent() { return this.nodeValue; }
  set textContent(v) { this.nodeValue = String(v); }
}
class Elem extends NodeBase {
  constructor(tag, ns = '') {
    super(tag === '#fragment' ? 11 : 1);
    this.localName = tag; this.tagName = tag.toUpperCase(); this.namespaceURI = ns;
    this.childNodes = []; this._a = new Map(); this._l = new Map(); this.value = ''; this.checked = false;
  }
  get firstChild() { return this.childNodes[0] ?? null; }
  get firstElementChild() { return this.childNodes.find((c) => c.nodeType === 1) ?? null; }
  get attributes() { return [...this._a.entries()].map(([name, value]) => ({ name, localName: name, namespaceURI: null, value })); }
  getAttribute(k) { return this._a.has(k) ? this._a.get(k) : null; }
  setAttribute(k, v) { this._a.set(k, String(v)); }
  removeAttribute(k) { this._a.delete(k); }
  removeAttributeNS(_, k) { this._a.delete(k); }
  hasAttribute(k) { return this._a.has(k); }
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
  matches(sel) {
    return sel.split(',').some((raw) => {
      const s = raw.trim();
      if (s.startsWith('[') && s.endsWith(']')) return this.hasAttribute(s.slice(1, -1));
      if (s.startsWith('.')) return (this.getAttribute('class') || '').split(/\s+/).includes(s.slice(1));
      const m = /^([a-z0-9-]+)\[([a-z0-9-]+)\]$/i.exec(s);
      return m ? this.localName === m[1].toLowerCase() && this.hasAttribute(m[2]) : this.localName === s.toLowerCase();
    });
  }
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
      for (const am of m[3].matchAll(/([a-zA-Z0-9_:-]+)(?:="([^"]*)")?/g)) {
        const v = (am[2] ?? '').replace(/&quot;/g, '"').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>');
        el.setAttribute(am[1], v); if (am[1] === 'value') el.value = v;
      }
      st[st.length - 1].appendChild(el);
      if (!voids.has(tag) && !m[3].trimEnd().endsWith('/')) st.push(el);
    }
  }
}
const body = new Elem('body'), head = new Elem('head'), appEl = new Elem('div');
appEl.setAttribute('id', 'app'); body.appendChild(appEl);
let stateEl = null;
globalThis.window = { addEventListener() {} };
globalThis.location = { pathname: '/', search: '', protocol: 'http:', host: 'localhost' };
globalThis.history = { pushState() {}, replaceState() {} };
globalThis.document = {
  readyState: 'complete', body, head,
  createElement: (t) => new Elem(t), createElementNS: (ns, t) => new Elem(t, ns),
  createTextNode: (s) => new TextNode(s), createDocumentFragment: () => new Elem('#fragment'),
  getElementById: (id) => id === 'app' ? appEl : id === 'qed-state' ? stateEl : null,
  querySelector: () => null, addEventListener() {},
};
const click = (el) => { assert.ok(el, 'missing click target'); for (const fn of (appEl._l.get('click') || [])) fn({ target: el, button: 0, preventDefault() {} }); };
const input = (el, v) => { assert.ok(el, 'missing input target'); el.value = v; for (const fn of (appEl._l.get('input') || [])) fn({ target: el, preventDefault() {} }); };
const outDir = process.argv[2];
await import(`${outDir}/qed_host.mjs`);
const mod = await import(`${outDir}/app.mjs`);

// 1. Patch non-local <div> with Text child into localCell (must clear stale children, not hydrate Text node)
assert.equal(appEl.find('.plain-page').firstChild.nodeType, 3);
click(appEl.find('.p1'));
assert.equal(appEl.find('.local-panel').getAttribute('data-mode'), '0');

// 2. localRerender inserting new buttons + input before reused positional & keyed siblings
click(appEl.find('.toggle'));
assert.equal(appEl.find('.local-panel').getAttribute('data-mode'), '1');
for (const [cls, want] of [['.new0', 'new0'], ['.new1', 'new1'], ['.card0', 'card0'], ['.card1', 'card1'], ['.knew', 'knew'], ['.kcard', 'kcard']]) {
  click(appEl.find(cls));
  assert.equal(appEl.find('.local-panel').getAttribute('data-last'), want);
  assert.equal(appEl.find('.root').getAttribute('data-bubbled'), want);
}
input(appEl.find('.in-new'), 'n-val');
assert.equal(appEl.find('.local-panel').getAttribute('data-new'), 'n-val');
assert.equal(appEl.find('.local-panel').getAttribute('data-card'), '');
input(appEl.find('.in-card'), 'c-val');
assert.equal(appEl.find('.local-panel').getAttribute('data-card'), 'c-val');
assert.equal(appEl.find('.local-panel').getAttribute('data-new'), 'n-val');

// 3. Patch localCell -> different localCell -> plain <div> -> localCell on reused <div>
click(appEl.find('.p2'));
assert.equal(appEl.find('.local-panel'), null);
assert.equal(appEl.find('.leaf').getAttribute('data-label'), 'alt');
click(appEl.find('.leaf-inc'));
assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.p0'));
assert.equal(appEl.find('.plain-page').textContent, 'Loading text child');
click(appEl.find('.p2'));
assert.equal(appEl.find('.leaf').getAttribute('data-n'), '0');

// 4. Same-render remount into new host (<section> -> <main>) and detached-before-remount slot reuse (page 6 <-> page 7)
click(appEl.find('.p3')); click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.p4'));
assert.equal(appEl.find('.leaf').getAttribute('data-label'), 'in-b');
assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '2');
click(appEl.find('.p6')); click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.p7'));
assert.equal(appEl.find('.leaf').getAttribute('data-label'), 's1');
assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '2');
click(appEl.find('.p6')); assert.equal(appEl.find('.leaf').getAttribute('data-label'), 's0'); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '2');

// 5. Nested local unmount & remount inside localRerender (localRun GC)
click(appEl.find('.p5')); click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');
click(appEl.find('.nest-toggle')); assert.equal(appEl.find('.leaf'), null);
click(appEl.find('.nest-toggle')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '0');
click(appEl.find('.leaf-inc')); assert.equal(appEl.find('.leaf').getAttribute('data-n'), '1');

// 6. SSR hydration of localCell preserves SSR DOM nodes in place and binds handlers cleanly
window.__qedHost.active().teardown();
appEl.innerHTML = mod.ssr_page1();
stateEl = new Elem('script'); stateEl.setAttribute('id', 'qed-state'); stateEl.textContent = mod.state_page1(); body.appendChild(stateEl);
const ssrPanel = appEl.find('.local-panel');
assert.ok(ssrPanel);
globalThis.__qed.nodes = [null]; globalThis.__qed.free = [];
mod.__main(0); mod.qed_init(0);
assert.equal(appEl.find('.local-panel'), ssrPanel);
click(appEl.find('.toggle')); assert.equal(appEl.find('.local-panel').getAttribute('data-mode'), '1');
click(appEl.find('.new0')); assert.equal(appEl.find('.local-panel').getAttribute('data-last'), 'new0');
console.log('OK');
"#

private def runLocalDomJsTest (c : TestChecker) : IO Unit := do
  let (root, qedjs, lp) := (← IO.currentDir, ← qedjsBinPath, ← getLeanPath)
  withTempDir "qed-local-dom-test" fun dir => do
    let outDir := FilePath.mk dir
    for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
      IO.FS.writeFile (outDir / f) (← IO.FS.readFile (root / "runtime" / f))
    let entries := Qed.Cli.driverEntries.map (fun e => if e == "main:__main" then "JsGate.localBugsMain:__main" else e) ++
      #["JsGate.localBugsSsrPage1:ssr_page1", "JsGate.localBugsStatePage1:state_page1"]
    let args := #["--rt", (root / "runtime" / "qed_rt.mjs").toString, (outDir / "app.mjs").toString, "QedTests.JsGate", "--"] ++ entries
    let (jc, jo, je) ← runCmd qedjs args (cwd := some root) (env := #[("LEAN_PATH", some lp)])
    c.check "qedjs compiles LocalBugsApp fixture" (jc == 0) (jo ++ je)
    if jc != 0 then return
    let harness := outDir / "run.mjs"
    IO.FS.writeFile harness localDomHarnessJs
    let (nc, no, ne) ← runCmd "node" #[harness.toString, outDir.toString]
    c.check "JS/DOM localCell remount, reused-div clear, handler indices & SSR hydration" (nc == 0 && no.contains "OK") (no ++ ne)
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
  c.checkEq "base64 empty encode" (Base64.encode ByteArray.empty) ""; c.checkEq "base64 empty decode" (Base64.decode "") (.ok ByteArray.empty)
  for n in [1, 2, 3, 256] do
    let bs := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i % 256))
    c.checkEq s!"base64 round-trip ({n} bytes)" (Base64.decode (Base64.encode bs)) (.ok bs)
  let big := ByteArray.mk ((List.range 65536).toArray.map fun i => UInt8.ofNat ((i * 37 + 13) % 256)); let bigEnc := Base64.encode big
  c.check "base64 64KiB encoded length" (bigEnc.length == ((65536 + 2) / 3) * 4); c.checkEq "base64 64KiB round-trip" (Base64.decode bigEnc) (.ok big)
  for (lbl, bad) in [("invalid length", "abc"), ("invalid char", "ab!d")] do c.check s!"base64 rejects {lbl}" (!(Base64.decode bad).isOk)
  let sampleBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0xFF]
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
  let st2 ← Prim.atomicRead box2 id; c.check "background job ticked before stopFlag" (st2.ticks ≥ 1 && st2.ticks < 50)
  runLocalDomJsTest c
  c.finish

end QedTests.Native.VerificationAndJobs
