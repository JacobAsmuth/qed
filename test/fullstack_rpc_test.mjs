import { spawn, spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import net from 'node:net';
import crypto from 'node:crypto';
import { existsSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import puppeteer from 'puppeteer';
import { ROOT, SERVE, buildDev, checker, sleep } from './harness.mjs';

// Minimal binary Protocol Buffers helpers matching `Qed.Proto` (`LawfulProto`)
function encodeVarint(n) {
  let v = BigInt(n);
  const out = [];
  while (v >= 128n) {
    out.push(Number((v & 0x7fn) | 0x80n));
    v >>= 7n;
  }
  out.push(Number(v));
  return Buffer.from(out);
}

function encodeTag(fieldNum, wireType) {
  return encodeVarint((fieldNum << 3) | wireType);
}

function encodeLenBytes(fieldNum, buf) {
  const b = Buffer.isBuffer(buf) ? buf : Buffer.from(buf);
  return Buffer.concat([encodeTag(fieldNum, 2), encodeVarint(b.length), b]);
}

function encodeVarintField(fieldNum, n) {
  return Buffer.concat([encodeTag(fieldNum, 0), encodeVarint(n)]);
}

function encodeOrderReq(idx, qty) {
  // `(Nat × Nat)` -> field 1: varint idx, field 2: varint qty
  return Buffer.concat([encodeVarintField(1, idx), encodeVarintField(2, qty)]);
}

function encodeAddBookReq(id, title, stock, coverPng) {
  // Right-nested 4-tuple `(String × (String × (Nat × Bytes)))`
  const innerMost = Buffer.concat([
    encodeVarintField(1, stock),
    encodeLenBytes(2, coverPng),
  ]);
  const mid = Buffer.concat([
    encodeLenBytes(1, Buffer.from(title, 'utf8')),
    encodeLenBytes(2, innerMost),
  ]);
  return Buffer.concat([
    encodeLenBytes(1, Buffer.from(id, 'utf8')),
    encodeLenBytes(2, mid),
  ]);
}

function encodeCoverReq(key) {
  // Single scalar `String` -> field 1: UTF-8 bytes
  return encodeLenBytes(1, Buffer.from(key, 'utf8'));
}

function decodeVarintAt(buf, pos) {
  let val = 0n;
  let shift = 0n;
  let p = pos;
  while (p < buf.length) {
    const b = BigInt(buf[p++]);
    val |= (b & 0x7fn) << shift;
    if ((b & 0x80n) === 0n) return { val: Number(val), pos: p };
    shift += 7n;
  }
  throw new Error('truncated varint');
}

function decodeSingleBytesMsg(buf) {
  // Scalar `Bytes` -> field 1 (tag 0x0a), length varint, raw bytes
  const tag = decodeVarintAt(buf, 0);
  if (tag.val !== ((1 << 3) | 2)) throw new Error(`unexpected tag ${tag.val}`);
  const len = decodeVarintAt(buf, tag.pos);
  return Buffer.from(buf.subarray(len.pos, len.pos + len.val));
}

async function getFreePort() {
  return await new Promise((resolve, reject) => {
    const s = net.createServer();
    s.once('error', reject);
    s.listen(0, '127.0.0.1', () => {
      const port = s.address().port;
      s.close(() => resolve(port));
    });
  });
}

function readRawBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

const { check, fail, finish } = checker('Fullstack-RPC');

// 1. Dual-target fullstack build + client bundle leak check
buildDev('Examples.CloudBooks');

const serverBin = path.join(SERVE, 'server');
const clientBundle = path.join(SERVE, 'app.mjs');
check('native server binary built', existsSync(serverBin), true);
check('client JS bundle built', existsSync(clientBundle), true);

const appJsSrc = await readFile(clientBundle, 'utf8');
check('no CF_D1_TOKEN in client JS', appJsSrc.includes('CF_D1_TOKEN'), false);
check('no GCP_SA_JSON in client JS', appJsSrc.includes('GCP_SA_JSON'), false);
check('no initState in client JS', appJsSrc.includes('initState'), false);
check('no dispatchM in client JS', appJsSrc.includes('dispatchM'), false);
check('no C server FFI in client JS', appJsSrc.includes('qed_server_'), false);

// 2. Fail-closed startup secret check
{
  const cleanEnv = { ...process.env };
  delete cleanEnv.CF_D1_TOKEN;
  delete cleanEnv.GCP_SA_JSON;
  const r = spawnSync(serverBin, [SERVE, '18999'], { cwd: ROOT, env: cleanEnv, encoding: 'utf8' });
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

let tokenExchanges = 0;
let rsaVerified = false;
let sawUnescapedSlashInDownload = false;
let failD1 = false;
const gcsObjects = new Map();
const d1Queries = [];

const mockExt = createServer(async (req, res) => {
  const body = await readRawBody(req);
  const u = new URL(req.url, 'http://127.0.0.1');

  if (req.method === 'POST' && u.pathname === '/oauth2/token') {
    const params = new URLSearchParams(body.toString('utf8'));
    const assertion = params.get('assertion') || '';
    const parts = assertion.split('.');
    if (parts.length === 3) {
      const hdr = JSON.parse(Buffer.from(parts[0], 'base64url').toString('utf8'));
      const claims = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
      const verifier = crypto.createVerify('RSA-SHA256');
      verifier.update(`${parts[0]}.${parts[1]}`);
      verifier.end();
      const sigOk = verifier.verify(publicKey, Buffer.from(parts[2], 'base64url'));
      if (
        sigOk &&
        hdr.alg === 'RS256' &&
        claims.iss === 'qed-test@proj.iam.gserviceaccount.com' &&
        claims.scope === 'https://www.googleapis.com/auth/devstorage.read_write'
      ) {
        rsaVerified = true;
        tokenExchanges++;
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ access_token: 'mock-gcs-token-777', expires_in: 3600 }));
        return;
      }
    }
    res.writeHead(401, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ error: 'invalid_grant' }));
    return;
  }

  if (u.pathname.startsWith('/upload/storage/v1/b/') || u.pathname.startsWith('/storage/v1/b/')) {
    if (req.headers.authorization !== 'Bearer mock-gcs-token-777') {
      res.writeHead(401, { 'Content-Type': 'text/plain' });
      res.end('unauthorized gcs');
      return;
    }
    if (req.method === 'POST' && u.pathname === '/upload/storage/v1/b/qed-covers/o') {
      const name = u.searchParams.get('name') || '';
      gcsObjects.set(name, body);
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ name, size: body.length }));
      return;
    }
    const dlPrefix = '/storage/v1/b/qed-covers/o/';
    if (req.method === 'GET' && u.pathname.startsWith(dlPrefix)) {
      if (req.url.includes('/o/covers/')) sawUnescapedSlashInDownload = true;
      const key = u.pathname.slice(dlPrefix.length);
      const stored = gcsObjects.get(key);
      if (!stored) {
        res.writeHead(404, { 'Content-Type': 'text/plain' });
        res.end('object not found');
        return;
      }
      res.writeHead(200, { 'Content-Type': 'application/octet-stream', 'Content-Length': stored.length });
      res.end(stored);
      return;
    }
  }

  if (req.method === 'POST' && u.pathname === '/accounts/demo-account/d1/database/demo-db/query') {
    if (req.headers.authorization !== 'Bearer test-cf-d1-secret') {
      res.writeHead(401, { 'Content-Type': 'text/plain' });
      res.end('unauthorized d1');
      return;
    }
    const parsed = JSON.parse(body.toString('utf8'));
    d1Queries.push(parsed);
    if (failD1) {
      res.writeHead(500, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ success: false, error: 'simulated D1 outage' }));
      return;
    }
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ success: true }));
    return;
  }

  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('unknown mock route: ' + req.url);
});

await new Promise((resolve, reject) => {
  mockExt.once('error', reject);
  mockExt.listen(0, '127.0.0.1', resolve);
});
const extPort = mockExt.address().port;
const extBase = `http://127.0.0.1:${extPort}`;

const saJson = JSON.stringify({
  client_email: 'qed-test@proj.iam.gserviceaccount.com',
  private_key: privateKey,
  token_uri: `${extBase}/oauth2/token`,
});

const srvPort = await getFreePort();
const srvBase = `http://127.0.0.1:${srvPort}`;
const authSecret = 'super-secret-hmac-key';
const validSig = crypto.createHmac('sha256', authSecret).update('alice').digest('hex');
const validToken = `alice.${validSig}`;

const srvProc = spawn(serverBin, [SERVE, String(srvPort), '--dev'], {
  cwd: ROOT,
  env: {
    ...process.env,
    QED_WORKERS: '4',
    QED_AUTH_SECRET: authSecret,
    CF_D1_TOKEN: 'test-cf-d1-secret',
    GCP_SA_JSON: saJson,
    QED_GCP_TOKEN_URL: `${extBase}/oauth2/token`,
    QED_EXT_GCPSTORAGE_BASE: extBase,
    QED_EXT_CLOUDFLARED1_BASE: extBase,
  },
  stdio: ['ignore', 'pipe', 'pipe'],
});

let browser = null;
try {
  // Poll `/_qed/health` until ready
  let ready = false;
  for (let i = 0; i < 60; i++) {
    try {
      const hr = await fetch(`${srvBase}/_qed/health`);
      if (hr.status === 200) {
        ready = true;
        break;
      }
    } catch {}
    await sleep(50);
  }
  check('native C server healthy', ready, true);

  // 4. Zero-hop native in-memory SSR checks
  const ssrCatalog = await fetch(`${srvBase}/`);
  check('SSR / status', ssrCatalog.status, 200);
  check('SSR / content-type html', (ssrCatalog.headers.get('content-type') || '').includes('text/html'), true);
  const catalogHtml = await ssrCatalog.text();
  check('SSR / renders book 0 title', catalogHtml.includes('Theorem Proving in Lean 4'), true);
  check('SSR / renders book 1 title', catalogHtml.includes('Functional Programming in Lean'), true);
  check('SSR / renders initial stock 12', catalogHtml.includes('Stock: 12'), true);
  check('SSR / embeds dehydrated qed-state', catalogHtml.includes('<script id="qed-state"'), true);

  const ssrDetail = await fetch(`${srvBase}/books/0`);
  check('SSR /books/0 status', ssrDetail.status, 200);
  const detailHtml = await ssrDetail.text();
  check('SSR /books/0 renders detail stock', detailHtml.includes('In stock: 12'), true);

  // Path traversal defense via raw socket (bypassing client URL normalization)
  const rawTraversalResp = await new Promise((resolve, reject) => {
    const sock = net.connect(srvPort, '127.0.0.1', () => {
      sock.write('GET /../lakefile.lean HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n');
    });
    const chunks = [];
    sock.on('data', (c) => chunks.push(c));
    sock.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    sock.on('error', reject);
  });
  check('path traversal never leaks lakefile.lean', rawTraversalResp.includes('lean_lib Qed'), false);

  const postRpc = (method, body, token = null) =>
    fetch(`${srvBase}/_qed/rpc/Catalog/${method}`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/x-protobuf',
        ...(token ? { Authorization: `Bearer ${token}` } : {}),
      },
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

  const coverResp = await postRpc('cover', encodeCoverReq('plfa.png'));
  check('cover download status 200', coverResp.status, 200);
  const downloadedPng = decodeSingleBytesMsg(Buffer.from(await coverResp.arrayBuffer()));
  check('cover download round-tripped exact binary PNG', Buffer.compare(downloadedPng, pngBytes), 0);
  check('`:key*` preserved literal `/` in download path', sawUnescapedSlashInDownload, true);
  check('C mutex OAuth2 cache reused token without re-exchange', tokenExchanges, 1);

  // 7. Inline `catch` fallback recovery when Cloudflare D1 returns HTTP 500
  failD1 = true;
  check('order succeeds via `catch` fallback during D1 500', (await postRpc('order', encodeOrderReq(0, 1), validToken)).status, 200);
  failD1 = false;

  // 8. Multi-core linearizability across 8 concurrent `await` + `atomic` RPCs (`QED_WORKERS=4`)
  const concurrentStatuses = await Promise.all(
    Array.from({ length: 8 }, async () => (await postRpc('order', encodeOrderReq(0, 1), validToken)).status)
  );
  check('all 8 concurrent orders returned 200', concurrentStatuses.every((s) => s === 200), true);
  check('Cloudflare D1 received all 9 order queries', d1Queries.length, 9);

  const afterConcurrent = await (await fetch(`${srvBase}/books/0`)).text();
  check('linearizable stock after 1 + 8 concurrent orders is 3', afterConcurrent.includes('In stock: 3'), true);

  // 9. Headless Puppeteer SSR hydration + live binary Protobuf RPC interaction
  browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
  const page = await browser.newPage();
  page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));

  const rpcCalls = [];
  page.on('request', (req) => {
    if (req.url().includes('/_qed/rpc/')) {
      rpcCalls.push({ url: req.url(), contentType: req.headers()['content-type'] || '' });
    }
  });

  await page.setCookie({
    name: 'qed_session',
    value: validToken,
    domain: '127.0.0.1',
    path: '/',
  });

  await page.goto(`${srvBase}/`, { waitUntil: 'networkidle0' });
  check('zero RPC refetch on initial SSR hydration', rpcCalls.length, 0);

  const rowCount = await page.$$eval('.book-row', (els) => els.length);
  check('hydrated catalog shows 3 books (including plfa)', rowCount, 3);

  const initialDomStock = await page.$eval('.book-row .book-stock', (el) => el.textContent.trim());
  check('hydrated DOM shows Stock: 3', initialDomStock, 'Stock: 3');

  await page.click('.book-row .order-btn');
  await page.waitForFunction(
    () => document.querySelector('.status')?.textContent?.includes('Ordered Theorem Proving in Lean 4'),
    { timeout: 5000 }
  );

  check('browser sent binary Protobuf RPC on click', rpcCalls.length, 1);
  check('browser RPC content-type is application/x-protobuf', rpcCalls[0]?.contentType, 'application/x-protobuf');

  const updatedDomStock = await page.$eval('.book-row .book-stock', (el) => el.textContent.trim());
  check('live DOM stock updated to Stock: 2', updatedDomStock, 'Stock: 2');
} finally {
  if (browser) await browser.close();
  srvProc.kill('SIGTERM');
  await new Promise((resolve) => {
    srvProc.once('exit', resolve);
    setTimeout(() => {
      srvProc.kill('SIGKILL');
      resolve();
    }, 1500);
  });
  mockExt.closeAllConnections?.();
  await new Promise((resolve) => mockExt.close(() => resolve()));
}

finish();
