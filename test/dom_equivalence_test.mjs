// Compare the transpiled driver with fresh DOM and the pure Lean renderer after every step.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, copyFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createServer } from 'node:http';
import puppeteer from 'puppeteer';

const root = fileURLToPath(new URL('..', import.meta.url));
const out = mkdtempSync(join(tmpdir(), 'qed-dom-'));
const run = (cmd, args) => execFileSync(cmd, args, { cwd: root, stdio: 'inherit' });
let browser, server;
try {
  run('lake', ['build', 'Examples.DomProbe', 'qedjs']);
  const entries = ['mount', 'advance', 'fresh', 'expected', 'handlerValue',
    'mountTemplate', 'advanceTemplate', 'expectedTemplate', 'duplicateBuild', 'duplicateUpdate', 'duplicateHydrate'];
  run('lake', ['env', join(root, '.lake/build/bin/qedjs'), join(out, 'app.mjs'),
    'Examples.DomProbe', '--', ...entries.map(n => `DomProbe.${n}:${n}`)]);
  for (const name of ['qed_rt.mjs', 'qed_dom.mjs']) copyFileSync(join(root, 'runtime', name), join(out, name));
  server = createServer((req, res) => {
    if (req.url === '/') return res.end('<!doctype html><body></body>');
    const path = join(out, req.url.slice(1));
    if (dirname(path) !== out) { res.writeHead(404); return res.end(); }
    try { res.setHeader('Content-Type', 'text/javascript'); res.end(readFileSync(path)); }
    catch { res.writeHead(404); res.end(); }
  });
  await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve); });
  browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
  const page = await browser.newPage();
  await page.goto(`http://127.0.0.1:${server.address().port}/`);
  const result = await page.evaluate(async () => {
    const P = await import('/app.mjs'), $ = await import('/qed_rt.mjs');
    const { dom } = await import('/qed_dom.mjs');
    $.registerDom(dom);
    $.assertExterns(P.__externs, $);
    const io = r => { if (r.t !== 0) throw new Error(JSON.stringify(r, (_, v) => typeof v === 'bigint' ? String(v) : v)); return $.ioVal(r); };
    // Only the effect boundary is supplied here; every tree and patch comes from Lean.
    globalThis.__qed = { effect(kind, name, value) {
      if (kind !== 'signal.set') return;
      this.sigVals.set(name, value);
      const b = this.sig.get(name);
      if (b) { if (b.attr) b.el.setAttribute(b.attr, value); else b.el.textContent = value; }
    }};
    const node = h => globalThis.__qed.nodes[h];
    const snapshot = n => {
      if (n.nodeType === Node.TEXT_NODE) return ['text', n.textContent];
      const attrs = [...n.attributes].filter(a => !a.name.startsWith('data-qed-') && !['value', 'checked'].includes(a.name))
        .map(a => [a.namespaceURI, a.name, a.value]).sort((a, b) => a[1].localeCompare(b[1]));
      // Serialization omits empty text slots and the HTML parser coalesces adjacent
      // text nodes. Compare their content while preserving all element boundaries.
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
    const parse = html => { const t = document.createElement('template'); t.innerHTML = html; return t.content.firstChild; };
    const equal = (a, b, label) => { if (JSON.stringify(a) !== JSON.stringify(b)) throw new Error(`${label}\n${JSON.stringify(a)}\n${JSON.stringify(b)}`); };
    const sequence = Array.from({ length: 32 }, (_, i) => i);
    let seed = 0x51ed;
    for (let i = 0; i < 160; i++) { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; sequence.push(seed % 128); }
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
    parent = node(io(P.mountTemplate(0n)));
    document.body.replaceChildren(parent);
    for (const s of sequence) {
      io(P.advanceTemplate(BigInt(s)));
      equal(snapshot(parent.firstChild), snapshot(parse(P.expectedTemplate(BigInt(s)))), `template vs Html.render, seed ${s}`);
    }
    for (const name of ['duplicateBuild', 'duplicateUpdate', 'duplicateHydrate']) {
      const r = P[name]();
      if (r.t !== 1 || !JSON.stringify(r).includes('duplicate sibling key')) throw new Error(`${name} should reject duplicate keys`);
    }
    return { updates: sequence.length * 2, duplicateChecks: 3 };
  });
  assert.equal(result.updates, 384);
  console.log(`PASS DOM equivalence: ${result.updates} updates; ${result.duplicateChecks} duplicate-key checks`);
} finally {
  await browser?.close();
  if (server?.listening) await new Promise(resolve => server.close(resolve));
  rmSync(out, { recursive: true, force: true });
}
