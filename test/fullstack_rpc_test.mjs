import { spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import { rm, symlink } from 'node:fs/promises';
import { createServer } from 'node:http';
import path from 'node:path';
import {
  ROOT, buildDevAsync, checkLeakGate, checker, decodeVarintAt, lenField,
  rawHttpReq, signSessionToken, startNativeServer, varintField, withPage,
} from './harness.mjs';

const encodeOrderReq = (idx, qty) => Buffer.concat([varintField(1, idx), varintField(2, qty)]);
const encodeAddBookReq = (id, title, stock, png) =>
  Buffer.concat([lenField(1, id), lenField(2, Buffer.concat([lenField(1, title), lenField(2, Buffer.concat([varintField(1, stock), lenField(2, png)]))]))]);
function decodeSingleBytesMsg(buf) {
  const tag = decodeVarintAt(buf, 0);
  if (tag.val !== ((1 << 3) | 2)) throw new Error(`unexpected tag ${tag.val}`);
  const len = decodeVarintAt(buf, tag.pos);
  return Buffer.from(buf.subarray(len.pos, len.pos + len.val));
}
const readRawBody = async (req) => {
  const chunks = [];
  for await (const c of req) chunks.push(c);
  return Buffer.concat(chunks);
};

const { check, fail, finish } = checker('Fullstack-RPC');

// 1. Dual-target fullstack build + exact compiler server-leak gate
const dir = await buildDevAsync('Examples.CloudBooks');
checkLeakGate(check, 'Examples.CloudBooks', [
  'CloudBooks.Catalog.initState',
  'CloudBooks.Catalog.secrets',
  'CloudBooks.Catalog.dispatchM',
  'CloudBooks.Catalog.order_handler',
  'CloudBooks.CloudflareD1.secrets',
]);

// 2. Fail-closed startup secret check
{
  const cleanEnv = { ...process.env };
  delete cleanEnv.CF_D1_TOKEN;
  delete cleanEnv.GCP_SA_JSON;
  const r = spawnSync(path.join(dir, 'server'), [dir, '18999'], { cwd: ROOT, env: cleanEnv, encoding: 'utf8' });
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

const authSecret = 'super-secret-hmac-key';
const validToken = signSessionToken(authSecret, 'alice');
const srv = await startNativeServer(dir, {
  QED_WORKERS: '4', QED_AUTH_SECRET: authSecret, CF_D1_TOKEN: 'test-cf-d1-secret', GCP_SA_JSON: saJson,
  QED_GCP_TOKEN_URL: `${extBase}/oauth2/token`, QED_EXT_GCPSTORAGE_BASE: extBase, QED_EXT_CLOUDFLARED1_BASE: extBase,
});

try {
  check('native server healthy', srv.healthy, true);

  // 4. Path traversal, symlink escape (Rust `openat2`), & RPC CSRF header-forwarding checks
  const rawTraversalResp = await rawHttpReq(srv.port, 'GET /../lakefile.lean HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n');
  check('path traversal never leaks lakefile.lean', rawTraversalResp.includes('lean_lib Qed'), false);

  const escapeLink = path.join(dir, 'escape.txt');
  await rm(escapeLink, { force: true });
  await symlink(path.join(ROOT, 'lakefile.lean'), escapeLink);
  try {
    check('symlink inside staticDir blocked by openat2/O_NOFOLLOW',
      (await (await fetch(`${srv.baseUrl}/escape.txt`)).text()).includes('lean_lib Qed'), false);
  } finally {
    await rm(escapeLink, { force: true });
  }

  const postRpc = (method, body, token = null) => fetch(`${srv.baseUrl}/_qed/rpc/Catalog/${method}`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-protobuf', ...(token ? { Authorization: `Bearer ${token}` } : {}) },
    body,
  });
  const postCookieRpc = (method, body, extraHeaders = {}, contentType = 'application/x-protobuf') => fetch(`${srv.baseUrl}/_qed/rpc/Catalog/${method}`, {
    method: 'POST',
    headers: { Cookie: `qed_session=${validToken}`, 'Content-Type': contentType, ...extraHeaders },
    body,
  });
  check('RPC rejects cross-origin Origin header with 403',
    (await postCookieRpc('list', Buffer.alloc(0), { Origin: 'https://evil.example.com' })).status, 403);
  check('RPC rejects non-protobuf Content-Type with 415',
    (await postCookieRpc('list', Buffer.from('a=1'), {}, 'text/plain')).status, 415);
  check('RPC accepts same-origin Origin + Sec-Fetch-Site + application/x-protobuf with 200',
    (await postCookieRpc('list', Buffer.alloc(0), { Origin: srv.baseUrl, 'Sec-Fetch-Site': 'same-origin' })).status, 200);

  // 5. Auth (Rust HMAC FFI) & `requires` precondition enforcement
  check('unauthenticated order rejected with 401', (await postRpc('order', encodeOrderReq(0, 1))).status, 401);
  check('forged HMAC token rejected with 401', (await postRpc('order', encodeOrderReq(0, 1), `alice.${'0'.repeat(64)}`)).status, 401);
  check('violated `requires qty <= 50` rejected with 400', (await postRpc('order', encodeOrderReq(0, 99), validToken)).status, 400);

  // 6. GCP RS256 JWT token exchange (Rust `rsa` + `outbound.rs`) + raw binary `Bytes` + `StateBox` cache
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
  check('StateBox OAuth2 cache reused token without re-exchange', tokenExchanges, 1);

  // 7. Inline `catch` fallback recovery when Cloudflare D1 returns HTTP 500
  failD1 = true;
  check('order succeeds via `catch` fallback during D1 500', (await postRpc('order', encodeOrderReq(0, 1), validToken)).status, 200);
  failD1 = false;

  // 8. Multi-core linearizability across 8 concurrent `await` + `atomic` RPCs (`QED_WORKERS=4`)
  const concurrentStatuses = await Promise.all(Array.from({ length: 8 }, async () => (await postRpc('order', encodeOrderReq(0, 1), validToken)).status));
  check('all 8 concurrent orders returned 200', concurrentStatuses.every((s) => s === 200), true);
  check('Cloudflare D1 received all 9 order queries', d1Queries.length, 9);
  check('linearizable stock after 1 + 8 concurrent orders is 3', (await (await fetch(`${srv.baseUrl}/books/0`)).text()).includes('In stock: 3'), true);

  // 9. Headless Puppeteer SSR hydration + live binary Protobuf RPC + `query` smoke check
  await withPage(async (page) => {
    page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));
    const rpcCalls = [];
    page.on('request', (req) => { if (req.url().includes('/_qed/rpc/')) rpcCalls.push({ url: req.url(), contentType: req.headers()['content-type'] || '' }); });
    await page.setCookie({ name: 'qed_session', value: validToken, domain: '127.0.0.1', path: '/' });
    await page.goto(`${srv.baseUrl}/`, { waitUntil: 'load' });
    await page.waitForSelector('.book-row', { timeout: 10000 });
    check('zero RPC refetch on initial SSR hydration', rpcCalls.length, 0);
    check('SSR hydrated authenticated session user', await page.$eval('.session-user', (el) => el.textContent.trim()), 'alice');
    check('hydrated catalog shows 3 books (including plfa)', await page.$$eval('.book-row', (els) => els.length), 3);
    check('hydrated DOM shows Stock: 3', await page.$eval('.book-row .book-stock', (el) => el.textContent.trim()), 'Stock: 3');

    await page.click('.book-row .order-btn');
    await page.waitForFunction(() => document.querySelector('.status')?.textContent?.includes('Ordered Theorem Proving in Lean 4'), { timeout: 5000 });
    check('browser sent binary Protobuf RPC on click', rpcCalls.length, 1);
    check('browser RPC content-type is application/x-protobuf', rpcCalls[0]?.contentType, 'application/x-protobuf');
    check('live DOM stock updated to Stock: 2', await page.$eval('.book-row .book-stock', (el) => el.textContent.trim()), 'Stock: 2');

    await page.evaluate(() => document.querySelectorAll('.book-row a.book-title')[1].click());
    await page.waitForSelector('.detail-stock', { timeout: 5000 });
    check('reactive query fetched /books/1 via Protobuf findAt',
      rpcCalls.some((r) => r.url.endsWith('/_qed/rpc/Catalog/findAt') && r.contentType === 'application/x-protobuf'), true);
    check('detail view shows book 1 stock 8', await page.$eval('.detail-stock', (el) => el.textContent.trim()), 'In stock: 8');
  });
} finally {
  await srv.stop();
  mockExt.closeAllConnections?.();
  await new Promise((resolve) => mockExt.close(resolve));
}

finish();
