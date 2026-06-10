// qed_serve.mjs: the local server `qed dev`/`qed start` run. Static files from <dir>;
// when <dir>/ssr.mjs is present, every other GET is server-rendered through it (the
// handler `qed build` generated). In dev mode the SSR pages get the live-reload poller
// and ssr.mjs is re-imported when a rebuild replaces it.
// usage: node qed_serve.mjs <dir> <port> [--dev]
import { createServer } from 'node:http';
import { readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const [dirArg = 'dist', port = '8000', devFlag] = process.argv.slice(2);
const dev = devFlag === '--dev';
const dir = path.resolve(dirArg);
const ssrPath = path.join(dir, 'ssr.mjs');

// In dev, rebuilds replace ssr.mjs while this process lives; node's module cache would
// keep serving the old app, so re-import on an mtime change (the query busts the cache).
let cached = { mtime: 0, handler: null };
async function ssrHandler() {
  let st = null;
  try { st = await stat(ssrPath); } catch { return null; }
  const mtime = st.mtimeMs;
  if (!cached.handler || (dev && mtime !== cached.mtime)) {
    const mod = await import(pathToFileURL(ssrPath).href + '?t=' + mtime);
    cached = { mtime, handler: mod.default };
  }
  return cached.handler;
}

const MIME = {
  '.html': 'text/html; charset=utf-8', '.mjs': 'text/javascript', '.js': 'text/javascript',
  '.css': 'text/css', '.json': 'application/json', '.svg': 'image/svg+xml',
  '.map': 'application/json', '.txt': 'text/plain', '.ico': 'image/x-icon',
};

const reload = "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</scr" + "ipt>";

createServer(async (req, res) => {
  try {
    const u = new URL(req.url, `http://${req.headers.host ?? `localhost:${port}`}`);
    const file = path.join(dir, path.normalize(u.pathname));
    if (file.startsWith(dir)) {
      let st = null;
      try { st = await stat(file); } catch {}
      if (st?.isFile()) {
        // dev: never cache. prod: revalidate (no-cache + Last-Modified), so a repeat
        // visit costs a 304 per file instead of re-downloading the bundle.
        const lastMod = new Date(st.mtime).toUTCString();
        const ims = req.headers['if-modified-since'];
        if (!dev && ims && Math.floor(st.mtimeMs / 1000) <= Math.floor(Date.parse(ims) / 1000)) {
          res.writeHead(304, { 'last-modified': lastMod });
          res.end();
          return;
        }
        res.writeHead(200, {
          'content-type': MIME[path.extname(file)] ?? 'application/octet-stream',
          'cache-control': dev ? 'no-store' : 'no-cache',
          'last-modified': lastMod,
        });
        res.end(await readFile(file));
        return;
      }
    }
    // never SSR the renderer's own data fetches (no API behind this server → plain 404)
    if (req.headers['x-qed-ssr']) {
      res.writeHead(404, { 'content-type': 'application/json' });
      res.end('{"error":"qed serve: no API at this origin; put qed behind your API server or use makeHandler({fetch})"}');
      return;
    }
    const handler = req.method === 'GET' ? await ssrHandler() : null;
    if (handler) {
      const r = await handler(new Request(u, { method: 'GET' }));
      let body = await r.text();
      if (dev) body = body.replace('</body>', reload + '</body>');
      res.writeHead(r.status, Object.fromEntries(r.headers.entries()));
      res.end(body);
      return;
    }
    // no SSR: the SPA's index takes every route (deep links resolve client-side)
    res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
    res.end(await readFile(path.join(dir, 'index.html')));
  } catch (e) {
    res.writeHead(500, { 'content-type': 'text/plain' });
    res.end(String(e?.stack ?? e));
  }
}).listen(Number(port), async () => {
  const ssr = (await ssrHandler()) ? ' (SSR)' : '';
  console.log(`qed serve: http://localhost:${port}${ssr}${dev ? ' [dev]' : ''}`);
});
