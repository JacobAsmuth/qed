import { createHash } from 'node:crypto';
import { withBrowser } from './harness.mjs';

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

await withBrowser('SOCKET', {
  webRoot: 'Examples.SocketWeb',
  upgrade: (req, socket) => {
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
        if (opcode === 0x8) { socket.end(); return; }
        if (opcode === 0x1) socket.write(frame(body.toString('utf8')));
      }
    });
    socket.on('error', () => {});
  },
}, async ({ page, check, baseUrl }) => {
  const status = () => page.$eval('#app .ws .status', (e) => e.textContent.trim());
  const log = () => page.$$eval('#app .log .line', (els) => els.map((e) => e.textContent.trim()));

  await page.goto(`${baseUrl}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .ws .status', { timeout: 20000 });
  check('starts offline', await status(), 'offline');

  await page.click('#app .connect');
  await page.waitForFunction(() => document.querySelector('#app .ws .status')?.textContent.trim() === 'online', { timeout: 8000 });
  check('Connect brought the socket online', await status(), 'online');
  check('open was logged', (await log()).includes('● connected'), true);

  await page.type('#app .draft', 'hello qed');
  await page.click('#app .send');
  await page.waitForFunction(
    () => [...document.querySelectorAll('#app .log .line')].some((e) => e.textContent.trim() === '← hello qed'),
    { timeout: 8000 });
  const lines1 = await log();
  check('the sent line was logged', lines1.includes('→ hello qed'), true);
  check('the echo arrived as a received message', lines1.includes('← hello qed'), true);
  check('the composer cleared after send', await page.$eval('#app .draft', (e) => e.value), '');

  await page.type('#app .draft', 'again');
  await page.click('#app .send');
  await page.waitForFunction(
    () => [...document.querySelectorAll('#app .log .line')].some((e) => e.textContent.trim() === '← again'),
    { timeout: 8000 });
  check('the persistent socket echoed a second message', (await log()).includes('← again'), true);

  await page.click('#app .disconnect');
  await page.waitForFunction(() => document.querySelector('#app .ws .status')?.textContent.trim() === 'offline', { timeout: 8000 });
  check('Disconnect took the socket offline', await status(), 'offline');
  check('close was logged', (await log()).includes('○ disconnected'), true);
});
