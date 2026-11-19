import crypto from 'node:crypto';
import { createServer } from 'node:http';
import net from 'node:net';
import {
  buildDevAsync, checkLeakGate, checker, decodeFields, lenField,
  signSessionToken, sleep, startNativeServer, varintField, withPage,
} from './harness.mjs';

// Qed.Proto helpers for LiveRoom
const encodeProtoNat = (n) => varintField(1, n);
const encodeProtoStr = (s) => lenField(1, Buffer.from(s, 'utf8'));
const encodeProtoNatStr = (n, s) => Buffer.concat([varintField(1, n), lenField(2, Buffer.from(s, 'utf8'))]);
const encodePriceTickProto = (symbol, price) => Buffer.concat([lenField(1, Buffer.from(symbol, 'utf8')), varintField(2, price)]);
const decodeSingleNat = (buf) => decodeFields(buf).find(([fn]) => fn === 1)?.[1] ?? null;
const decodeStringArray = (buf) => decodeFields(buf).filter(([fn]) => fn === 1).map(([, v]) => v.toString('utf8'));

// Minimal RFC 6455 helpers (client -> server masked, server -> client unmasked)
const wsAccept = (key) => crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');

function encodeWsFrame(opcode, payload, masked) {
  const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
  const len = data.length;
  const hdrLen = 2 + (len >= 65536 ? 8 : len >= 126 ? 2 : 0) + (masked ? 4 : 0);
  const out = Buffer.allocUnsafe(hdrLen + len);
  out[0] = 0x80 | (opcode & 0x0f);
  let p = 2;
  if (len < 126) { out[1] = (masked ? 0x80 : 0) | len; }
  else if (len < 65536) { out[1] = (masked ? 0x80 : 0) | 126; out.writeUInt16BE(len, 2); p = 4; }
  else { out[1] = (masked ? 0x80 : 0) | 127; out.writeBigUInt64BE(BigInt(len), 2); p = 10; }
  if (masked) {
    const mask = crypto.randomBytes(4);
    mask.copy(out, p); p += 4;
    for (let i = 0; i < len; i++) out[p + i] = data[i] ^ mask[i & 3];
  } else {
    data.copy(out, p);
  }
  return out;
}

function makeWsFrameParser(onFrame) {
  let buf = Buffer.alloc(0);
  return (chunk) => {
    buf = Buffer.concat([buf, chunk]);
    while (buf.length >= 2) {
      const opcode = buf[0] & 0x0f, masked = (buf[1] & 0x80) !== 0;
      let len = buf[1] & 0x7f, p = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); p = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); p = 10; }
      const maskOff = p;
      if (masked) p += 4;
      if (buf.length < p + len) return;
      const payload = Buffer.allocUnsafe(len);
      if (masked) { for (let i = 0; i < len; i++) payload[i] = buf[p + i] ^ buf[maskOff + (i & 3)]; }
      else { buf.copy(payload, 0, p, p + len); }
      buf = buf.subarray(p + len);
      onFrame(opcode, payload);
    }
  };
}

// Qed mux frame helpers ([opcode:u8][subId:u32be][...])
function encodeMuxSub(subId, channel, paramsBuf) {
  const chB = Buffer.from(channel, 'utf8');
  const out = Buffer.allocUnsafe(7 + chB.length + paramsBuf.length);
  out[0] = 0x01; out.writeUInt32BE(subId, 1); out.writeUInt16BE(chB.length, 5);
  chB.copy(out, 7); paramsBuf.copy(out, 7 + chB.length);
  return out;
}
function encodeMuxUnsub(subId) {
  const out = Buffer.allocUnsafe(5);
  out[0] = 0x02; out.writeUInt32BE(subId, 1);
  return out;
}
function encodeMuxSend(subId, payloadBuf) {
  const out = Buffer.allocUnsafe(5 + payloadBuf.length);
  out[0] = 0x03; out.writeUInt32BE(subId, 1);
  payloadBuf.copy(out, 5);
  return out;
}
function decodeMuxFrame(buf) {
  if (buf.length < 5) throw new Error(`short mux frame (${buf.length})`);
  return { op: buf[0], subId: buf.readUInt32BE(1), body: buf.subarray(5) };
}

function connectRawWs({ port, path: wsPath, origin, headers = {} }) {
  return new Promise((resolve, reject) => {
    const key = crypto.randomBytes(16).toString('base64');
    const sock = net.connect(port, '127.0.0.1', () => {
      sock.write([
        `GET ${wsPath} HTTP/1.1`, `Host: 127.0.0.1:${port}`,
        'Upgrade: websocket', 'Connection: Upgrade',
        `Sec-WebSocket-Key: ${key}`, 'Sec-WebSocket-Version: 13',
        ...(origin ? [`Origin: ${origin}`] : []),
        ...Object.entries(headers).map(([k, v]) => `${k}: ${v}`),
        '', '',
      ].join('\r\n'));
    });
    let upgraded = false, hdrBuf = Buffer.alloc(0);
    const queue = [], waiters = [];
    const feed = makeWsFrameParser((opcode, payload) => {
      if (opcode === 0x09) { sock.write(encodeWsFrame(0x0a, payload, true)); return; }
      if (opcode === 0x08) { try { sock.end(); } catch {} return; }
      const item = { opcode, payload };
      if (waiters.length > 0) waiters.shift()(item);
      else queue.push(item);
    });
    sock.on('data', (chunk) => {
      if (!upgraded) {
        hdrBuf = Buffer.concat([hdrBuf, chunk]);
        const idx = hdrBuf.indexOf('\r\n\r\n');
        if (idx === -1) return;
        const head = hdrBuf.subarray(0, idx).toString('utf8');
        const rest = hdrBuf.subarray(idx + 4);
        const statusCode = parseInt((head.split('\r\n')[0] || '').split(' ')[1] || '0', 10);
        if (statusCode !== 101) { sock.destroy(); return resolve({ statusCode, head, sock: null }); }
        const acceptLine = head.split('\r\n').find((l) => l.toLowerCase().startsWith('sec-websocket-accept:'));
        const gotAccept = acceptLine ? acceptLine.split(':')[1].trim() : '';
        upgraded = true;
        if (rest.length > 0) feed(rest);
        resolve({
          statusCode,
          acceptValid: gotAccept === wsAccept(key),
          sendBin: (b) => sock.write(encodeWsFrame(0x02, b, true)),
          nextFrame: (timeoutMs = 3000) => new Promise((res, rej) => {
            if (queue.length > 0) return res(queue.shift());
            const t = setTimeout(() => rej(new Error('timeout waiting for WS frame')), timeoutMs);
            waiters.push((item) => { clearTimeout(t); res(item); });
          }),
          drainCheckNone: async (waitMs = 200) => { await sleep(waitMs); return queue.length; },
          close: () => { try { sock.write(encodeWsFrame(0x08, Buffer.alloc(0), true)); } catch {} sock.end(); },
          destroy: () => sock.destroy(),
        });
      } else {
        feed(chunk);
      }
    });
    sock.on('error', (err) => { if (!upgraded) reject(err); });
  });
}

// Pure-Node mock 3rd-party WebSocket server on 127.0.0.1:19455 (TickerWs, RawFeedWs, ProtoFeedWs)
function startMock3pWsServer(port = 19455) {
  const sockets = new Set(), received = [], receivedBin = [];
  const srv = createServer((_req, res) => { res.writeHead(404); res.end('ws only'); });
  srv.on('upgrade', (req, sock, head) => {
    const key = req.headers['sec-websocket-key'];
    if (!key) { sock.destroy(); return; }
    sock.write([
      'HTTP/1.1 101 Switching Protocols', 'Upgrade: websocket', 'Connection: Upgrade',
      `Sec-WebSocket-Accept: ${wsAccept(key)}`, '', '',
    ].join('\r\n'));
    const entry = {
      path: req.url,
      sendText: (s) => sock.write(encodeWsFrame(0x01, Buffer.from(s, 'utf8'), false)),
      sendBin: (b) => sock.write(encodeWsFrame(0x02, b, false)),
      drop: () => sock.destroy(),
    };
    sockets.add(entry);
    const feed = makeWsFrameParser((opcode, payload) => {
      if (opcode === 0x01) received.push({ path: req.url, text: payload.toString('utf8') });
      else if (opcode === 0x02) receivedBin.push({ path: req.url, data: payload });
      else if (opcode === 0x09) sock.write(encodeWsFrame(0x0a, payload, false));
      else if (opcode === 0x08) { try { sock.end(); } catch {} }
    });
    if (head && head.length > 0) feed(head);
    sock.on('data', feed);
    sock.on('close', () => sockets.delete(entry));
    sock.on('error', () => sockets.delete(entry));
  });
  return new Promise((resolve, reject) => {
    srv.once('error', reject);
    srv.listen(port, '127.0.0.1', () => resolve({
      received,
      receivedBin,
      broadcastText: (pfx, text) => { for (const s of sockets) if (s.path.startsWith(pfx)) s.sendText(text); },
      broadcastBin: (pfx, buf) => { for (const s of sockets) if (s.path.startsWith(pfx)) s.sendBin(buf); },
      close: () => {
        for (const s of [...sockets]) s.drop();
        srv.closeAllConnections?.();
        return new Promise((r) => srv.close(r));
      },
    }));
  });
}

async function waitForMatch(arr, pred, timeoutMs = 1500) {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (arr.some(pred)) return true;
    await sleep(40);
  }
  return false;
}

const { check, fail, finish } = checker('WebSockets');

// 1. Build Examples.LiveRoom + verify exact compiler leak gate blocks WS server dispatcher
const dir = await buildDevAsync('Examples.LiveRoom');
checkLeakGate(check, 'Examples.LiveRoom', ['LiveRoom.Hub.wsDispatchM']);

// 2. Start mock 3p WebSocket server + native multi-worker server (`QED_WORKERS=4`)
const mock3p = await startMock3pWsServer(19455);
const authSecret = 'ws-test-hmac-secret';
const aliceToken = signSessionToken(authSecret, 'alice');
const bobToken = signSessionToken(authSecret, 'bob');
const srv = await startNativeServer(dir, { QED_WORKERS: '4', QED_AUTH_SECRET: authSecret });

const postRpc = (method, body, token = null) => fetch(`${srv.baseUrl}/_qed/rpc/Hub/${method}`, {
  method: 'POST',
  headers: { 'Content-Type': 'application/x-protobuf', ...(token ? { Authorization: `Bearer ${token}` } : {}) },
  body,
});
const getOnlineCount = async () => {
  const r = await postRpc('onlineCount', Buffer.alloc(0));
  if (r.status !== 200) throw new Error(`onlineCount HTTP ${r.status}`);
  return decodeSingleNat(Buffer.from(await r.arrayBuffer()));
};
const getActiveConns = async () => {
  const r = await postRpc('activeConnsList', Buffer.alloc(0));
  if (r.status !== 200) throw new Error(`activeConnsList HTTP ${r.status}`);
  return decodeStringArray(Buffer.from(await r.arrayBuffer()));
};

try {
  check('native WS server healthy', srv.healthy, true);

  // 3. CSWSH origin check wired into WS upgrade path + RFC 6455 SHA-1 handshake
  const evilWs = await connectRawWs({ port: srv.port, path: '/_qed/ws/Hub', origin: 'https://evil.example.com' });
  check('CSWSH cross-origin WS upgrade rejected with 403', evilWs.statusCode, 403);

  const clientAnon = await connectRawWs({ port: srv.port, path: '/_qed/ws/Hub', origin: srv.baseUrl });
  check('same-origin WS upgrade returns 101', clientAnon.statusCode, 101);
  check('RFC 6455 Sec-WebSocket-Accept valid', clientAnon.acceptValid, true);

  // 4. Auth & `requires` enforcement over multiplexed binary WS
  clientAnon.sendBin(encodeMuxSub(1, 'room', encodeProtoNat(1)));
  const anonResp = decodeMuxFrame((await clientAnon.nextFrame()).payload);
  check('unauthenticated SUB rejected with ERR (0x13)', anonResp.op, 0x13);
  check('unauthenticated SUB ERR preserves subId', anonResp.subId, 1);
  clientAnon.close();

  const clientA = await connectRawWs({ port: srv.port, path: '/_qed/ws/Hub', origin: srv.baseUrl, headers: { Cookie: `qed_session=${aliceToken}` } });
  const clientB = await connectRawWs({ port: srv.port, path: '/_qed/ws/Hub', origin: srv.baseUrl, headers: { Cookie: `qed_session=${bobToken}` } });
  check('authenticated clientA upgraded', clientA.statusCode, 101);
  check('authenticated clientB upgraded', clientB.statusCode, 101);

  clientA.sendBin(encodeMuxSub(99, 'room', encodeProtoNat(999)));
  check('violated channel `requires id <= 100` returns ERR (0x13)', decodeMuxFrame((await clientA.nextFrame()).payload).op, 0x13);

  clientA.sendBin(encodeMuxSub(1, 'room', encodeProtoNat(1)));
  check('clientA SUB returns JOIN_OK (0x11)', decodeMuxFrame((await clientA.nextFrame()).payload).op, 0x11);
  check('onlineCount after clientA join', await getOnlineCount(), 1);

  clientB.sendBin(encodeMuxSub(1, 'room', encodeProtoNat(1)));
  check('clientB SUB returns JOIN_OK (0x11)', decodeMuxFrame((await clientB.nextFrame()).payload).op, 0x11);
  check('onlineCount after clientB join', await getOnlineCount(), 2);

  const conns2 = await getActiveConns();
  check('two distinct ws-* ctx.connId values tracked',
    conns2.length === 2 && conns2[0].startsWith('ws-') && conns2[1].startsWith('ws-') && conns2[0] !== conns2[1], true);

  clientA.sendBin(encodeMuxSub(2, 'alerts', Buffer.alloc(0)));
  const joinAlert = decodeMuxFrame((await clientA.nextFrame()).payload);
  check('multiplexed alerts() SUB returns JOIN_OK on subId 2', joinAlert.op === 0x11 && joinAlert.subId === 2, true);

  // 5. Cross-worker fan-out from `on_send`
  clientA.sendBin(encodeMuxSend(1, encodeProtoStr('hello-mux')));
  const evA1 = decodeMuxFrame((await clientA.nextFrame()).payload);
  const evB1 = decodeMuxFrame((await clientB.nextFrame()).payload);
  check('clientA received EVENT from on_send', evA1.op === 0x12 && evA1.subId === 1, true);
  check('clientB received EVENT across workers from on_send', evB1.op === 0x12 && evB1.subId === 1, true);
  check('clientB EVENT payload contains hello-mux', evB1.body.toString('utf8').includes('hello-mux'), true);

  // 6. Transactional rollback cancels emit (zero phantom broadcast!)
  const rbResp = await postRpc('announce', encodeProtoNatStr(1, 'ROLLBACK'), aliceToken);
  const rbFields = decodeFields(Buffer.from(await rbResp.arrayBuffer()));
  check('rolled-back announce RPC returns Except.error (field 2)',
    rbFields.some(([fn]) => fn === 2) && !rbFields.some(([fn]) => fn === 1), true);
  check('zero phantom WS frames delivered on rollback (clientA)', await clientA.drainCheckNone(180), 0);
  check('zero phantom WS frames delivered on rollback (clientB)', await clientB.drainCheckNone(20), 0);

  // Committed HTTP RPC `announce` broadcasts to BOTH WS subscribers across workers
  check('committed announce RPC returns 200', (await postRpc('announce', encodeProtoNatStr(1, 'from-http-rpc'), aliceToken)).status, 200);
  const rpcEvA = decodeMuxFrame((await clientA.nextFrame()).payload);
  const rpcEvB = decodeMuxFrame((await clientB.nextFrame()).payload);
  check('clientA received HTTP RPC emit', rpcEvA.op === 0x12 && rpcEvA.body.toString('utf8').includes('from-http-rpc'), true);
  check('clientB received HTTP RPC emit', rpcEvB.op === 0x12 && rpcEvB.body.toString('utf8').includes('from-http-rpc'), true);

  // Multiplexed second channel `broadcastAlert` arrives on subId = 2 of clientA, NOT clientB
  check('broadcastAlert RPC returns 200', (await postRpc('broadcastAlert', encodeProtoStr('sys-alert-1'))).status, 200);
  const alertEv = decodeMuxFrame((await clientA.nextFrame()).payload);
  check('clientA received alert on multiplexed subId 2', alertEv.op === 0x12 && alertEv.subId === 2 && alertEv.body.toString('utf8').includes('sys-alert-1'), true);
  check('clientB (not subscribed to alerts) got 0 frames', await clientB.drainCheckNone(120), 0);

  // 7. `on_leave` runs on explicit UNSUB AND on abrupt TCP disconnect
  clientA.sendBin(encodeMuxUnsub(1));
  await sleep(120);
  check('on_leave decremented onlineCount on explicit UNSUB', await getOnlineCount(), 1);
  check('on_leave removed only clientA connId', (await getActiveConns()).length, 1);
  clientA.close();

  clientB.destroy();
  let leftAfterDrop = false;
  for (let i = 0; i < 30; i++) {
    if ((await getOnlineCount()) === 0 && (await getActiveConns()).length === 0) { leftAfterDrop = true; break; }
    await sleep(50);
  }
  check('on_leave cleaned up onlineCount and activeConns on abrupt TCP disconnect', leftAfterDrop, true);

  // 8. Headless Chromium E2E: SSR + hydration + multiplexed fullstack + 3p codecs (JSON, raw text, Proto) + server-restart reconnect
  await withPage(async (page1) => {
    await withPage(async (page2) => {
      page1.on('pageerror', (e) => fail(`[page1 error] ${e.message}`));
      page2.on('pageerror', (e) => fail(`[page2 error] ${e.message}`));
      await page1.setCookie({ name: 'qed_session', value: aliceToken, url: srv.baseUrl });
      await page2.setCookie({ name: 'qed_session', value: aliceToken, url: srv.baseUrl });

      await page1.goto(`${srv.baseUrl}/rooms/1`, { waitUntil: 'networkidle0' });
      await page1.waitForFunction(() =>
        document.querySelector('.chat-status')?.textContent === 'connected' &&
        document.querySelector('.alert-status')?.textContent === 'connected' &&
        document.querySelector('.ticker-status')?.textContent === 'connected' &&
        document.querySelector('.raw-status')?.textContent === 'connected' &&
        document.querySelector('.proto-status')?.textContent === 'connected' &&
        document.querySelector('.joined-count')?.textContent === '1' &&
        document.querySelector('.ext-joined')?.textContent === '1',
        { timeout: 6000 });
      check('page1 connected to multiplexed fullstack + all 3p WS codecs', true, true);
      check('custom on_status(st) fired on alertFeed connect',
        Number(await page1.$eval('.alert-status-count', (el) => el.textContent)) >= 2, true);

      await page2.goto(`${srv.baseUrl}/rooms/1`, { waitUntil: 'networkidle0' });
      await page2.waitForFunction(() =>
        document.querySelector('.chat-status')?.textContent === 'connected' &&
        document.querySelector('.online-count')?.textContent === '2',
        { timeout: 6000 });
      const conn1 = await page1.$eval('.my-conn-id', (el) => el.textContent.trim());
      const conn2 = await page2.$eval('.my-conn-id', (el) => el.textContent.trim());
      check('same user in two tabs receives distinct ws-* ctx.connId',
        conn1.startsWith('ws-') && conn2.startsWith('ws-') && conn1 !== conn2, true);

      await page1.type('.draft-input', 'hello browser ws');
      await page1.click('.send-btn');
      await page1.waitForFunction(() =>
        (document.querySelector('.msg-list')?.textContent || '').includes('[1] alice: hello browser ws') &&
        document.querySelector('.draft-input')?.value === '',
        { timeout: 5000 });
      await page2.waitForFunction(() =>
        (document.querySelector('.msg-list')?.textContent || '').includes('[1] alice: hello browser ws'),
        { timeout: 5000 });
      check('multi-tab fullstack WS send & broadcast delivered', true, true);

      await postRpc('broadcastAlert', encodeProtoStr('browser-alert-99'));
      await page1.waitForFunction(() => document.querySelector('.last-alert')?.textContent === 'browser-alert-99', { timeout: 5000 });
      check('multiplexed alertFeed delivered in browser', true, true);

      // 3rd-party codecs: JSON (TickerWs), raw String (RawFeedWs), binary Proto(T) (ProtoFeedWs)
      mock3p.broadcastText('/ticks/BTC', JSON.stringify({ symbol: 'BTC', price: 95123 }));
      await page1.waitForFunction(() => document.querySelector('.last-price')?.textContent === '95123', { timeout: 5000 });
      check('3p JSON WS message received in browser', true, true);
      await page1.click('.ping-ticker-btn');
      check('3p JSON WS typed send delivered',
        await waitForMatch(mock3p.received, (m) => m.path === '/ticks/BTC' && JSON.parse(m.text).action === 'ping'), true);

      mock3p.broadcastText('/raw/log', 'raw-line-77');
      await page1.waitForFunction(() => document.querySelector('.last-raw')?.textContent === 'raw-line-77', { timeout: 5000 });
      check('3p raw String WS message received in browser', true, true);
      await page1.click('.ping-raw-btn');
      check('3p raw String WS send delivered',
        await waitForMatch(mock3p.received, (m) => m.path === '/raw/log' && m.text === 'raw-hello'), true);

      mock3p.broadcastBin('/proto/btc', encodePriceTickProto('BTC', 88420));
      await page1.waitForFunction(() => document.querySelector('.last-proto-price')?.textContent === '88420', { timeout: 5000 });
      check('3p binary Proto(T) WS message decoded in browser', true, true);
      await page1.click('.ping-proto-btn');
      check('3p binary Proto(T) WS typed send delivered',
        await waitForMatch(mock3p.receivedBin, (m) => m.path === '/proto/btc' && m.data.toString('utf8').includes('proto-ping')), true);

      // Route switch unsubscribes & triggers server `on_leave` for only page1's `connId`
      await page1.click('.nav-home');
      await page1.waitForFunction(() => document.querySelector('.chat-status')?.textContent === 'disconnected', { timeout: 5000 });
      await sleep(120);
      const connsAfterLeave = await getActiveConns();
      check('route navigation unsubscribed only page1 connId',
        connsAfterLeave.length === 1 && connsAfterLeave[0] === conn2, true);

      // Navigate back to /rooms/1, then restart native server to verify mixed multiplexed reconnect:
      // `chat` (`backoff(80, 1000)`) auto-reconnects while `alertFeed` (`reconnect off`) stays disconnected.
      await page1.click('.nav-room-1');
      await page1.waitForFunction(() =>
        document.querySelector('.chat-status')?.textContent === 'connected' &&
        document.querySelector('.joined-count')?.textContent === '2',
        { timeout: 5000 });

      check('restarted native WS server healthy', await srv.restart(), true);

      await page1.waitForFunction(() =>
        document.querySelector('.chat-status')?.textContent === 'connected' &&
        Number(document.querySelector('.joined-count')?.textContent || '0') >= 3,
        { timeout: 6000 });
      check('multiplexed `chat` (`backoff`) auto-reconnected after server restart', true, true);
      check('multiplexed `alertFeed` (`reconnect off`) stayed disconnected on same shared socket',
        await page1.$eval('.alert-status', (el) => el.textContent), 'disconnected');

      await postRpc('broadcastAlert', encodeProtoStr('ignored-after-off'));
      await sleep(200);
      check('un-reconnected `alertFeed` did not receive post-restart alert',
        await page1.$eval('.last-alert', (el) => el.textContent), 'browser-alert-99');
    });
  });
} finally {
  await srv.stop();
  await mock3p.close();
}

finish();
