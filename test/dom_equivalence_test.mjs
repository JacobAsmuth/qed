import { execFileSync } from 'node:child_process';
import { existsSync, mkdtempSync, mkdirSync, copyFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { ROOT, leanEnv, withBrowser, send } from './harness.mjs';

const out = mkdtempSync(join(tmpdir(), 'qed-dom-'));
const qedjsBin = join(ROOT, '.lake/build/bin/qedjs');
const run = (cmd, args, env = process.env) =>
  execFileSync(cmd, args, { cwd: ROOT, env, encoding: 'utf8', maxBuffer: 16 << 20 });

try {
  if (process.env.QED_PREBUILT !== '1' || !existsSync(qedjsBin)) {
    run('lake', ['build', 'Tests.DomProbe', 'qedjs']);
  }
  const entries = ['mount', 'advance', 'fresh', 'expected', 'handlerValue',
    'mountTemplate', 'advanceTemplate', 'expectedTemplate',
    'expectedDuplicate', 'duplicateBuild', 'duplicateUpdate', 'duplicateHydrate'];
  run(qedjsBin, [join(out, 'app.mjs'), 'Tests.DomProbe', '--', ...entries.map((n) => `DomProbe.${n}:${n}`)], leanEnv());
  const rtProbeEntries = [
    'DomProbe.bootRtProbe:__main', 'Qed.qedInit:qed_init', 'Qed.qedDispatch:qed_dispatch',
    'Qed.qedDispatchStr:qed_dispatch_str', 'Qed.qedStreamChunk:qed_stream_chunk', 'Qed.qedStreamDone:qed_stream_done',
    'Qed.qedHttpDone:qed_http_done', 'Qed.qedHttpBytesDone:qed_http_bytes_done', 'Qed.qedUrlChanged:qed_url_changed',
    'Qed.qedLocalDispatch:qed_local_dispatch', 'Qed.qedLocalDispatchStr:qed_local_dispatch_str',
    'Qed.qedLocalSnapshot:qed_local_snapshot', 'Qed.qedLocalRestore:qed_local_restore',
    'Qed.qedEffectDone:qed_effect_done', 'Qed.qedPortRecv:qed_port_recv',
    'Qed.qedWsOpen:qed_ws_open', 'Qed.qedWsBytes:qed_ws_bytes', 'Qed.qedWsText:qed_ws_text', 'Qed.qedWsClose:qed_ws_close',
  ];
  mkdirSync(join(out, 'host-test'), { recursive: true });
  run(qedjsBin, [join(out, 'host-test', 'app.mjs'), 'Tests.DomProbe', '--', ...rtProbeEntries], leanEnv());
  for (const name of ['qed_rt.mjs', 'qed_dom.mjs', 'qed_host.mjs']) {
    copyFileSync(join(ROOT, 'runtime', name), join(out, name));
    copyFileSync(join(ROOT, 'runtime', name), join(out, 'host-test', name));
  }

  await withBrowser('DOM-EQUIVALENCE', {
    dir: out,
    spa: false,
    routes: (req, res, url) => {
      if (url.pathname === '/') { send(res, 200, 'text/html', '<!doctype html><body></body>'); return true; }
      if (url.pathname === '/host-test/') {
        send(res, 200, 'text/html', '<!doctype html><body><div id="app"></div></body>');
        return true;
      }
      if (url.pathname === '/slow') {
        setTimeout(() => { try { send(res, 200, 'application/json', '{"slow":true}'); } catch {} }, 600);
        return true;
      }
      return false;
    },
  }, async ({ page, check, baseUrl }) => {
    await page.goto(`${baseUrl}/`);
    const result = await page.evaluate(async () => {
      const P = await import('/app.mjs'), $ = await import('/qed_rt.mjs');
      const { dom } = await import('/qed_dom.mjs');
      $.registerDom(dom);
      $.assertExterns(P.__externs, $);
      const io = (r) => { if (r.t !== 0) throw new Error(JSON.stringify(r, (_, v) => typeof v === 'bigint' ? String(v) : v)); return $.ioVal(r); };
      globalThis.__qed = { effect(kind, name, value) {
        if (kind !== 'signal.set') return;
        this.sigVals.set(name, value);
        const b = this.sig.get(name);
        if (b) { if (b.attr) b.el.setAttribute(b.attr, value); else b.el.textContent = value; }
      }};
      const node = (h) => globalThis.__qed.nodes[h];
      const snapshot = (n) => {
        if (n.nodeType === Node.TEXT_NODE) return ['text', n.textContent];
        const attrs = [...n.attributes].filter((a) => !a.name.startsWith('data-qed-') && !['value', 'checked'].includes(a.name))
          .map((a) => [a.namespaceURI, a.name, a.value]).sort((a, b) => a[1].localeCompare(b[1]));
        // HTML serialization omits empty text slots and coalesces adjacent text nodes.
        const children = [];
        for (const c of n.childNodes) {
          const child = snapshot(c);
          if (child[0] === 'text' && child[1] === '') continue;
          if (child[0] === 'text' && children.at(-1)?.[0] === 'text') children.at(-1)[1] += child[1];
          else children.push(child);
        }
        return [n.namespaceURI, n.localName, attrs,
          n instanceof HTMLInputElement ? [n.value, n.checked] : null, children];
      };
      const parse = (html) => { const t = document.createElement('template'); t.innerHTML = html; return t.content.firstChild; };
      const equal = (a, b, label) => { if (JSON.stringify(a) !== JSON.stringify(b)) throw new Error(`${label}\n${JSON.stringify(a)}\n${JSON.stringify(b)}`); };
      const sequence = Array.from({ length: 32 }, (_, i) => i);
      let seed = 0x51ed;
      for (let i = 0; i < 48; i++) { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; sequence.push(seed % 128); }
      let parent = node(io(P.mount(0n)));
      document.body.replaceChildren(parent);
      for (const s of sequence) {
        io(P.advance(BigInt(s)));
        const actual = parent.firstChild;
        for (const b of parent.querySelectorAll('button')) {
          const id = b.getAttribute('data-qed-on-click');
          if (s % 3 === 0) equal(id, null, `removed handler, seed ${s}`);
          else equal(String(io(P.handlerValue(BigInt(id)))), String(s + Number(b.parentElement.dataset.id)), `live handler, seed ${s}, slot ${id}, DOM ${parent.innerHTML}`);
        }
        equal(snapshot(actual), snapshot(node(io(P.fresh(BigInt(s))))), `incremental vs fresh, seed ${s}`);
        equal(snapshot(actual), snapshot(parse(P.expected(BigInt(s)))), `incremental vs Html.render, seed ${s}`);
      }
      parent = node(io(P.mount(2n)));
      document.body.replaceChildren(parent);
      const row0 = parent.querySelector('[data-id="0"]');
      io(P.advance(3n));
      if (parent.querySelector('[data-id="0"]') !== row0) throw new Error('unique keyed row lost identity on reorder');
      parent = node(io(P.mount(1n)));
      const memo = parent.querySelector('aside');
      io(P.advance(2n));
      if (parent.querySelector('aside') !== memo) throw new Error('valid memo reuse lost identity');
      parent = node(io(P.mountTemplate(1n)));
      document.body.replaceChildren(parent);
      const vmemo = parent.querySelector('.vmemo');
      io(P.advanceTemplate(2n));
      if (parent.querySelector('.vmemo') !== vmemo) throw new Error('V.memo lost DOM node identity when LawfulKey unchanged');
      io(P.advanceTemplate(3n));
      equal(parent.querySelector('.vmemo').textContent, 'vmemo 1', 'V.memo updated when LawfulKey changed');
      parent = node(io(P.mountTemplate(0n)));
      document.body.replaceChildren(parent);
      for (const s of sequence) {
        io(P.advanceTemplate(BigInt(s)));
        equal(snapshot(parent.firstChild), snapshot(parse(P.expectedTemplate(BigInt(s)))), `template vs Html.render, seed ${s}`);
      }
      const expectedDup = snapshot(parse(P.expectedDuplicate(1n)));
      for (const name of ['duplicateBuild', 'duplicateUpdate', 'duplicateHydrate']) {
        const h = io(P[name]());
        equal(snapshot(node(h)), expectedDup, `${name} disambiguated duplicate keys without crash or DOM drift`);
      }
      history.pushState({}, '', '/books/0?tab=reviews&sort=asc');
      equal(io(dom.currentPath(0)), '/books/0?tab=reviews&sort=asc', 'currentPath preserves query string');
      return { updates: sequence.length * 2, duplicateChecks: 3 };
    });
    check('160 incremental/template DOM equivalence updates', result.updates, 160);
    check('3 duplicate-key disambiguation lifecycles', result.duplicateChecks, 3);

    // Browser runtime edge cases (real Lean `Qed.Driver.Runtime` + thin `qed_host.mjs` & `qed_rt.mjs`)
    await page.goto(`${baseUrl}/host-test/`);
    const rtEdge = await page.evaluate(async () => {
      const origCreate = document.createElement.bind(document);
      let pickedInput = null;
      document.createElement = (tag, opts) => {
        const el = origCreate(tag, opts);
        if (tag === 'input') { pickedInput = el; el.click = () => {}; }
        return el;
      };
      const t0 = performance.now();
      const $ = await import('/host-test/qed_rt.mjs');
      await import('/host-test/qed_host.mjs');
      document.createElement = origCreate;
      const g = globalThis.__qed;

      // 1. Large non-ASCII string (> 4 KiB) UTF-8 indexing & microtask eviction safety
      const big = 'α'.repeat(3000) + '🚀' + 'b'.repeat(2000);
      const byteSize1 = $.String_utf8ByteSize(big);
      const rocketCode = $.String_get(big, 6000n);
      await Promise.resolve();
      const byteSize2 = $.String_utf8ByteSize(big);
      const bigStrOk = byteSize1 === 8004n && byteSize2 === 8004n && rocketCode === 0x1F680;

      // 2. `file.pick` cancel fires twice on DOM, Lean `effectDone` settles it exactly once
      pickedInput.dispatchEvent(new Event('cancel'));
      pickedInput.dispatchEvent(new Event('cancel'));

      // 3. Lean-managed 80ms HTTP timeout emits `http.abort` and settles `request timeout` once
      while (!(document.querySelector('.rt-probe')?.textContent || '').includes('|err:request timeout') && performance.now() - t0 < 500) {
        await new Promise((r) => setTimeout(r, 15));
      }
      const elapsed = performance.now() - t0;
      await new Promise((r) => setTimeout(r, 50));
      const probeText = document.querySelector('.rt-probe')?.textContent || '';

      // 4. Throwing `localStorage` must never crash `storage.*` effects
      const origGet = Storage.prototype.getItem, origSet = Storage.prototype.setItem;
      const origRem = Storage.prototype.removeItem, origClr = Storage.prototype.clear;
      Storage.prototype.getItem = () => { throw new DOMException('blocked', 'SecurityError'); };
      Storage.prototype.setItem = () => { throw new DOMException('quota', 'QuotaExceededError'); };
      Storage.prototype.removeItem = () => { throw new DOMException('blocked', 'SecurityError'); };
      Storage.prototype.clear = () => { throw new DOMException('blocked', 'SecurityError'); };
      let storageThrew = false;
      try {
        g.effect('storage.set', 'k', 'v');
        g.effect('storage.remove', 'k');
        g.effect('storage.clear');
        g.effectResult('storage.get', 'k', '', 999);
      } catch { storageThrew = true; }
      finally {
        Storage.prototype.getItem = origGet; Storage.prototype.setItem = origSet;
        Storage.prototype.removeItem = origRem; Storage.prototype.clear = origClr;
      }

      // 5. `file.download` must NOT revoke ObjectURL synchronously
      const origRevoke = URL.revokeObjectURL;
      let revokedUrls = [];
      URL.revokeObjectURL = (u) => { revokedUrls.push(u); origRevoke.call(URL, u); };
      g.effect('file.download', 'hello.txt', 'text/plain', 'hi');
      const revokedSync = revokedUrls.length > 0;
      URL.revokeObjectURL = origRevoke;

      return {
        bigStrOk,
        storageThrew,
        revokedSync,
        probeText,
        timeoutFast: elapsed < 450,
      };
    });
    check('qed_rt large non-ASCII string UTF-8 indexing & microtask eviction', rtEdge.bigStrOk, true);
    check('guarded localStorage never throws on SecurityError/QuotaExceededError', rtEdge.storageThrew, false);
    check('file.download defers URL.revokeObjectURL asynchronously', rtEdge.revokedSync, false);
    check('Lean runtime settles file.pick cancel & HTTP timeout exactly once',
      rtEdge.probeText, 'init|pick:{"error":"cancelled"}|err:request timeout');
    check('Lean HTTP timeout aborts slow fetch promptly (< 450ms)', rtEdge.timeoutFast, true);
  });
} finally {
  rmSync(out, { recursive: true, force: true });
}
