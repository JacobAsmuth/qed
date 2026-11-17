import { spawn, spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import net from 'node:net';
import crypto from 'node:crypto';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { ROOT, buildDevAsync, checker, sleep, withPage } from './harness.mjs';

// Minimal binary Protocol Buffers helpers matching `Qed.Proto` (`LawfulProto`)
function encodeVarint(n) {
  let v = BigInt(n), out = [];
  while (v >= 128n) { out.push(Number((v & 0x7fn) | 0x80n)); v >>= 7n; }
  out.push(Number(v));
  return Buffer.from(out);
}
const tagBytes = (fieldNum, wireType) => encodeVarint((fieldNum << 3) | wireType);
const lenField = (fieldNum, buf) => { const b = Buffer.isBuffer(buf) ? buf : Buffer.from(buf); return Buffer.concat([tagBytes(fieldNum, 2), encodeVarint(b.length), b]); };
const varintField = (fieldNum, n) => Buffer.concat([tagBytes(fieldNum, 0), encodeVarint(n)]);
const encodeOrderReq = (idx, qty) => Buffer.concat([varintField(1, idx), varintField(2, qty)]);
const encodeAddBookReq = (id, title, stock, png) =>
  Buffer.concat([lenField(1, id), lenField(2, Buffer.concat([lenField(1, title), lenField(2, Buffer.concat([varintField(1, stock), lenField(2, png)]))]))]);

function decodeVarintAt(buf, pos) {
  let val = 0n, shift = 0n, p = pos;
  while (p < buf.length) {
    const b = BigInt(buf[p++]);
    val |= (b & 0x7fn) << shift;
    if ((b & 0x80n) === 0n) return { val: Number(val), pos: p };
    shift += 7n;
  }
  throw new Error('truncated varint');
}
function decodeSingleBytesMsg(buf) {
  const tag = decodeVarintAt(buf, 0);
  if (tag.val !== ((1 << 3) | 2)) throw new Error(`unexpected tag ${tag.val}`);
  const len = decodeVarintAt(buf, tag.pos);
  return Buffer.from(buf.subarray(len.pos, len.pos + len.val));
}

const getFreePort = () => new Promise((resolve, reject) => {
  const s = net.createServer();
  s.once('error', reject);
  s.listen(0, '127.0.0.1', () => { const { port } = s.address(); s.close(() => resolve(port)); });
});
const readRawBody = async (req) => {
  const chunks = [];
  for await (const c of req) chunks.push(c);
  return Buffer.concat(chunks);
};

const { check, fail, finish } = checker('Fullstack-RPC');

// 1. Dual-target fullstack build + client bundle leak check
const dir = await buildDevAsync('Examples.CloudBooks');
const serverBin = path.join(dir, 'server');
const appJsSrc = await readFile(path.join(dir, 'app.mjs'), 'utf8');
check('no server secrets or handlers in client JS',
  /CF_D1_TOKEN|GCP_SA_JSON|initState|dispatchM|qed_server_/.test(appJsSrc), false);

// 2. Fail-closed startup secret check
{
  const cleanEnv = { ...process.env };
  delete cleanEnv.CF_D1_TOKEN;
  delete cleanEnv.GCP_SA_JSON;
  const r = spawnSync(serverBin, [dir, '18999'], { cwd: ROOT, env: cleanEnv, encoding: 'utf8' });
  check('fail-closed exit code without secrets', r.status, 1);
  check('stderr mentions GCP_SA_JSON', (r.stderr || '').includes('GCP_SA_JSON'), true);
  check('stderr mentions CF_D1_TOKEN', (r.stderr || '').includes('CF_D1_TOKEN'), true);
}

// 3. Ephemeral RSA keypair + mock OAuth2 / GCS / Cloudflare D1 server
const { publicKey, privateKey } = crypto.generateKeyPairSync('rsa', {
  modulusLength: 2048,
  publicKeyEncoding: { type: 'spki', format: 'pem' },
  privateKeyEncoding: { type: 'pkcs8', format: 'pem' },
});

let tokenExchanges = 0, rsaVerified = false, sawUnescapedSlashInDownload = false, failD1 = false;
const gcsObjects = new Map();
const d1Queries = [];

const mockExt = createServer(async (req, res) => {
  const body = await readRawBody(req);
  const u = new URL(req.url, 'http://127.0.0.1');

  if (req.method === 'POST' && u.pathname === '/oauth2/token') {
    const parts = (new URLSearchParams(body.toString('utf8')).get('assertion') || '').split('.');
    if (parts.length === 3) {
      const hdr = JSON.parse(Buffer.from(parts[0], 'base64url').toString('utf8'));
      const claims = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
      const v = crypto.createVerify('RSA-SHA256').update(`${parts[0]}.${parts[1]}`);
      if (v.verify(publicKey, Buffer.from(parts[2], 'base64url')) && hdr.alg === 'RS256' &&
          claims.iss === 'qed-test@proj.iam.gserviceaccount.com' &&
          claims.scope === 'https://www.googleapis.com/auth/devstorage.read_write') {
        rsaVerified = true;
        tokenExchanges++;
        res.writeHead(200, { 'Content-Type': 'application/json' });
        return res.end(JSON.stringify({ access_token: 'mock-gcs-token-777', expires_in: 3600 }));
      }
    }
    res.writeHead(401, { 'Content-Type': 'application/json' });
    return res.end(JSON.stringify({ error: 'invalid_grant' }));
  }

  if (u.pathname.startsWith('/upload/storage/v1/b/') || u.pathname.startsWith('/storage/v1/b/')) {
    if (req.headers.authorization !== 'Bearer mock-gcs-token-777') {
      return res.writeHead(401, { 'Content-Type': 'text/plain' }).end('unauthorized gcs');
    }
    if (req.method === 'POST' && u.pathname === '/upload/storage/v1/b/qed-covers/o') {
      const name = u.searchParams.get('name') || '';
      gcsObjects.set(name, body);
      return res.writeHead(200, { 'Content-Type': 'application/json' }).end(JSON.stringify({ name, size: body.length }));
    }
    const dlPrefix = '/storage/v1/b/qed-covers/o/';
    if (req.method === 'GET' && u.pathname.startsWith(dlPrefix)) {
      if (req.url.includes('/o/covers/')) sawUnescapedSlashInDownload = true;
      const stored = gcsObjects.get(u.pathname.slice(dlPrefix.length));
      if (!stored) return res.writeHead(404, { 'Content-Type': 'text/plain' }).end('object not found');
      return res.writeHead(200, { 'Content-Type': 'application/octet-stream', 'Content-Length': stored.length }).end(stored);
    }
  }

  if (req.method === 'POST' && u.pathname === '/accounts/demo-account/d1/database/demo-db/query') {
    if (req.headers.authorization !== 'Bearer test-cf-d1-secret') {
      return res.writeHead(401, { 'Content-Type': 'text/plain' }).end('unauthorized d1');
    }
    d1Queries.push(JSON.parse(body.toString('utf8')));
    if (failD1) return res.writeHead(500, { 'Content-Type': 'application/json' }).end(JSON.stringify({ success: false, error: 'simulated D1 outage' }));
    return res.writeHead(200, { 'Content-Type': 'application/json' }).end(JSON.stringify({ success: true }));
  }

  res.writeHead(404, { 'Content-Type': 'text/plain' }).end('unknown mock route: ' + req.url);
});

await new Promise((resolve, reject) => { mockExt.once('error', reject); mockExt.listen(0, '127.0.0.1', resolve); });
const extBase = `http://127.0.0.1:${mockExt.address().port}`;
const saJson = JSON.stringify({ client_email: 'qed-test@proj.iam.gserviceaccount.com', private_key: privateKey, token_uri: `${extBase}/oauth2/token` });

const srvPort = await getFreePort();
const srvBase = `http://127.0.0.1:${srvPort}`;
const authSecret = 'super-secret-hmac-key';
const validToken = `alice.${crypto.createHmac('sha256', authSecret).update('alice').digest('hex')}`;

const srvProc = spawn(serverBin, [dir, String(srvPort), '--dev'], {
  cwd: ROOT,
  env: {
    ...process.env,
    QED_WORKERS: '4', QED_AUTH_SECRET: authSecret, CF_D1_TOKEN: 'test-cf-d1-secret', GCP_SA_JSON: saJson,
    QED_GCP_TOKEN_URL: `${extBase}/oauth2/token`, QED_EXT_GCPSTORAGE_BASE: extBase, QED_EXT_CLOUDFLARED1_BASE: extBase,
  },
  stdio: ['ignore', 'pipe', 'pipe'],
});

try {
  let ready = false;
  for (let i = 0; i < 60 && !ready; i++) {
    try { ready = (await fetch(`${srvBase}/_qed/health`)).status === 200; } catch {}
    if (!ready) await sleep(50);
  }
  check('native C server healthy', ready, true);

  // 4. Zero-hop native in-memory SSR checks
  const ssrCatalog = await fetch(`${srvBase}/`);
  const catalogHtml = await ssrCatalog.text();
  check('SSR / status', ssrCatalog.status, 200);
  check('SSR / content-type html', (ssrCatalog.headers.get('content-type') || '').includes('text/html'), true);
  check('SSR / renders book 0 title', catalogHtml.includes('Theorem Proving in Lean 4'), true);
  check('SSR / renders book 1 title', catalogHtml.includes('Functional Programming in Lean'), true);
  check('SSR / renders initial stock 12', catalogHtml.includes('Stock: 12'), true);
  check('SSR / embeds dehydrated qed-state', catalogHtml.includes('<script id="qed-state"'), true);

  const ssrDetail = await fetch(`${srvBase}/books/0`);
  check('SSR /books/0 status', ssrDetail.status, 200);
  check('SSR /books/0 renders detail stock', (await ssrDetail.text()).includes('In stock: 12'), true);

  // Path traversal defense via raw socket (bypassing client URL normalization)
  const rawTraversalResp = await new Promise((resolve, reject) => {
    const sock = net.connect(srvPort, '127.0.0.1', () => sock.write('GET /../lakefile.lean HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n'));
    const chunks = [];
    sock.on('data', (c) => chunks.push(c));
    sock.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    sock.on('error', reject);
  });
  check('path traversal never leaks lakefile.lean', rawTraversalResp.includes('lean_lib Qed'), false);

  const postRpc = (method, body, token = null) => fetch(`${srvBase}/_qed/rpc/Catalog/${method}`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-protobuf', ...(token ? { Authorization: `Bearer ${token}` } : {}) },
    body,
  });

  // 5. Auth (`ctx.userId != none`) & `requires` precondition enforcement
  check('unauthenticated order rejected with 401', (await postRpc('order', encodeOrderReq(0, 1))).status, 401);
  check('forged HMAC token rejected with 401', (await postRpc('order', encodeOrderReq(0, 1), `alice.${'0'.repeat(64)}`)).status, 401);
  check('violated `requires qty <= 50` rejected with 400', (await postRpc('order', encodeOrderReq(0, 99), validToken)).status, 400);

  // 6. GCP RS256 JWT token exchange + raw binary `Bytes` upload/download + token caching
  const pngBytes = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0xff, 0x42]);
  const addResp = await postRpc('addBook', encodeAddBookReq('plfa', 'Programming Language Foundations', 5, pngBytes), validToken);
  check('addBook status 200', addResp.status, 200);
  check('addBook content-type protobuf', addResp.headers.get('content-type'), 'application/x-protobuf');
  check('GCP RS256 JWT signature verified', rsaVerified, true);
  check('GCP token exchanged once on upload', tokenExchanges, 1);
  check('GCS received exact raw PNG bytes', Buffer.compare(gcsObjects.get('covers/plfa.png') || Buffer.alloc(0), pngBytes), 0);

  const coverResp = await postRpc('cover', lenField(1, 'plfa.png'));
  check('cover download status 200', coverResp.status, 200);
  check('cover download round-tripped exact binary PNG', Buffer.compare(decodeSingleBytesMsg(Buffer.from(await coverResp.arrayBuffer())), pngBytes), 0);
  check('`:key*` preserved literal `/` in download path', sawUnescapedSlashInDownload, true);
  check('C mutex OAuth2 cache reused token without re-exchange', tokenExchanges, 1);

  // 7. Inline `catch` fallback recovery when Cloudflare D1 returns HTTP 500
  failD1 = true;
  check('order succeeds via `catch` fallback during D1 500', (await postRpc('order', encodeOrderReq(0, 1), validToken)).status, 200);
  failD1 = false;

  // 8. Multi-core linearizability across 8 concurrent `await` + `atomic` RPCs (`QED_WORKERS=4`)
  const concurrentStatuses = await Promise.all(Array.from({ length: 8 }, async () => (await postRpc('order', encodeOrderReq(0, 1), validToken)).status));
  check('all 8 concurrent orders returned 200', concurrentStatuses.every((s) => s === 200), true);
  check('Cloudflare D1 received all 9 order queries', d1Queries.length, 9);
  check('linearizable stock after 1 + 8 concurrent orders is 3', (await (await fetch(`${srvBase}/books/0`)).text()).includes('In stock: 3'), true);

  // 9. Headless Puppeteer SSR hydration + live binary Protobuf RPC interaction
  await withPage(async (page) => {
    page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));
    const rpcCalls = [];
    page.on('request', (req) => { if (req.url().includes('/_qed/rpc/')) rpcCalls.push({ url: req.url(), contentType: req.headers()['content-type'] || '' }); });
    await page.setCookie({ name: 'qed_session', value: validToken, domain: '127.0.0.1', path: '/' });
    await page.goto(`${srvBase}/`, { waitUntil: 'load' });
    await page.waitForSelector('.book-row', { timeout: 10000 });
    check('zero RPC refetch on initial SSR hydration', rpcCalls.length, 0);
    check('hydrated catalog shows 3 books (including plfa)', await page.$$eval('.book-row', (els) => els.length), 3);
    check('hydrated DOM shows Stock: 3', await page.$eval('.book-row .book-stock', (el) => el.textContent.trim()), 'Stock: 3');

    await page.click('.book-row .order-btn');
    await page.waitForFunction(() => document.querySelector('.status')?.textContent?.includes('Ordered Theorem Proving in Lean 4'), { timeout: 5000 });
    check('browser sent binary Protobuf RPC on click', rpcCalls.length, 1);
    check('browser RPC content-type is application/x-protobuf', rpcCalls[0]?.contentType, 'application/x-protobuf');
    check('live DOM stock updated to Stock: 2', await page.$eval('.book-row .book-stock', (el) => el.textContent.trim()), 'Stock: 2');
  });
} finally {
  srvProc.kill('SIGTERM');
  await new Promise((resolve) => { srvProc.once('exit', resolve); setTimeout(() => { srvProc.kill('SIGKILL'); resolve(); }, 1500); });
  mockExt.closeAllConnections?.();
  await new Promise((resolve) => mockExt.close(resolve));
}

finish();
