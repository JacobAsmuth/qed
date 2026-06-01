// socket_test.mjs — end-to-end test for first-class WebSockets (Cmd.wsOpen/wsSend/wsClose).
//
// Builds the echo demo to .qed/dev and serves it from a tiny node server that also
// speaks WebSocket at /echo (a hand-rolled RFC 6455 echo, so there's no `ws` dep),
// with the COOP/COEP headers the pthread WASM needs. Then it drives the real app in
// headless Chromium and checks the full lifecycle through the pure `update`:
//   • Connect opens the socket and the onOpen message flips the status to "online",
//   • a sent line echoes back and arrives as an inbound `received` message,
//   • a second send proves the connection persists (callbacks fire many times),
//   • Disconnect closes it and the onClose message flips back to "offline".
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8138;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building socket demo (Examples.SocketWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.SocketWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

// --- a minimal WebSocket echo server (RFC 6455), enough to bounce text frames. ---
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const frame = (str) => {
  const payload = Buffer.from(str, 'utf8');
  const n = payload.length;
  let head;
  if (n < 126) head = Buffer.from([0x81, n]);
  else if (n < 65536) { head = Buffer.alloc(4); head[0] = 0x81; head[1] = 126; head.writeUInt16BE(n, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x81; head[1] = 127; head.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([head, payload]);
};

const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.wasm': 'application/wasm',
               '.json': 'application/json', '.css': 'text/css' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const send = (code, type, body) => {
    res.writeHead(code, {
      'Content-Type': type,
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp',
      'Cache-Control': 'no-store',
    });
    res.end(body);
  };
  const fp = (pathname === '/' || !pathname.includes('.')) ? `${SERVE}/index.html` : SERVE + pathname;
  try {
    const buf = await readFile(fp);
    send(200, MIME[fp.slice(fp.lastIndexOf('.'))] || 'application/octet-stream', buf);
  } catch { send(404, 'text/plain', 'not found'); }
});

server.on('upgrade', (req, socket) => {
  if (new URL(req.url, 'http://x').pathname !== '/echo') { socket.destroy(); return; }
  const accept = createHash('sha1').update(req.headers['sec-websocket-key'] + GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n' +
               `Connection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`);
  let buf = Buffer.alloc(0);
  socket.on('data', (chunk) => {
    buf = Buffer.concat([buf, chunk]);
    while (buf.length >= 2) {
      const opcode = buf[0] & 0x0f, masked = (buf[1] & 0x80) !== 0;
      let len = buf[1] & 0x7f, off = 2;
      if (len === 126) { if (buf.length < 4) break; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) break; len = Number(buf.readBigUInt64BE(2)); off = 10; }
      let mask;
      if (masked) { if (buf.length < off + 4) break; mask = buf.slice(off, off + 4); off += 4; }
      if (buf.length < off + len) break;
      let body = buf.slice(off, off + len);
      if (masked) { const out = Buffer.alloc(len); for (let i = 0; i < len; i++) out[i] = body[i] ^ mask[i % 4]; body = out; }
      buf = buf.slice(off + len);
      if (opcode === 0x8) { socket.end(); return; }            // close
      if (opcode === 0x1) socket.write(frame(body.toString('utf8'))); // text → echo
    }
  });
  socket.on('error', () => {});
});
server.listen(PORT);
await sleep(300);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'],
});

try {
  const page = await browser.newPage();
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  const status = () => page.$eval('#app .ws .status', (e) => e.textContent.trim());
  const log = () => page.$$eval('#app .log .line', (els) => els.map((e) => e.textContent.trim()));

  await page.goto(`http://localhost:${PORT}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .ws .status', { timeout: 20000 });
  check('starts offline', await status(), 'offline');

  // --- Connect: open the socket; the onOpen message flips the status to online ---
  await page.click('#app .connect');
  await page.waitForFunction(() => document.querySelector('#app .ws .status')?.textContent.trim() === 'online',
    { timeout: 8000 });
  check('Connect brought the socket online', await status(), 'online');
  check('open was logged', (await log()).includes('● connected'), true);

  // --- send a line; it echoes back and arrives as an inbound message ---
  await page.type('#app .draft', 'hello qed');
  await page.click('#app .send');
  await page.waitForFunction(
    () => [...document.querySelectorAll('#app .log .line')].some((e) => e.textContent.trim() === '← hello qed'),
    { timeout: 8000 });
  const lines1 = await log();
  check('the sent line was logged', lines1.includes('→ hello qed'), true);
  check('the echo arrived as a received message', lines1.includes('← hello qed'), true);
  check('the composer cleared after send', await page.$eval('#app .draft', (e) => e.value), '');

  // --- a second send proves the same connection keeps delivering ---
  await page.type('#app .draft', 'again');
  await page.click('#app .send');
  await page.waitForFunction(
    () => [...document.querySelectorAll('#app .log .line')].some((e) => e.textContent.trim() === '← again'),
    { timeout: 8000 });
  check('the persistent socket echoed a second message', (await log()).includes('← again'), true);

  // --- Disconnect: close the socket; the onClose message flips back to offline ---
  await page.click('#app .disconnect');
  await page.waitForFunction(() => document.querySelector('#app .ws .status')?.textContent.trim() === 'offline',
    { timeout: 8000 });
  check('Disconnect took the socket offline', await status(), 'offline');
  check('close was logged', (await log()).includes('○ disconnected'), true);
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL SOCKET CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
