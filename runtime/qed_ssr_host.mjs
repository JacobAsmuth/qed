// `App.ssrStep` is generic over `(Model, Msg)`, which compile to two leading erased parameters.
const ERASED = 0;

function fromHex(hex) {
  const out = new Uint8Array(hex.length >>> 1);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  return out;
}
function toHex(buf) {
  let s = '';
  for (let i = 0; i < buf.length; i++) s += buf[i].toString(16).padStart(2, '0');
  return s;
}

export function makeHandler(mod, opts = {}) {
  const app = mod.app();
  const title = opts.title ?? 'app';
  const script = opts.script ?? '/qed_host.mjs';
  const maxRounds = opts.maxRounds ?? 8;
  const doFetch = opts.fetch ?? ((...args) => fetch(...args));

  return async (request) => {
    const url = new URL(request.url);
    const path = url.pathname + url.search;
    const results = [];
    for (let round = 0; round < maxRounds; round++) {
      const out = JSON.parse(
        mod.ssrStep(ERASED, ERASED, app, path, title, script, JSON.stringify(results)));
      if (out.html !== undefined)
        return new Response(out.html,
          { headers: { 'content-type': 'text/html; charset=utf-8' } });
      const fetched = await Promise.all(out.need.map(async (n) => {
        try {
          const noBody = n.method === 'GET' || n.method === 'HEAD';
          // `x-qed-ssr` prevents a fronting `qed_serve` from recursively SSR-rendering API misses.
          const res = await doFetch(new URL(n.url, url.origin), {
            method: n.method,
            body: noBody ? undefined : (n.bin ? fromHex(n.body || '') : n.body),
            headers: n.bin
              ? { 'x-qed-ssr': '1', 'content-type': 'application/x-protobuf', 'accept': 'application/x-protobuf' }
              : { 'x-qed-ssr': '1', ...(n.body ? { 'content-type': 'application/json' } : {}) },
          });
          if (n.bin) {
            return res.ok
              ? { ok: true, bin: true, body: toHex(new Uint8Array(await res.arrayBuffer())) }
              : { ok: false, bin: true, body: (await res.text()) || `HTTP ${res.status}` };
          }
          const body = await res.text();
          return res.ok ? { ok: true, body } : { ok: false, body: `HTTP ${res.status}: ${body}` };
        } catch (e) {
          return { ok: false, body: String(e) };
        }
      }));
      results.push(...fetched);
    }
    return new Response('qed ssr: request did not settle (data dependency too deep?)',
      { status: 500 });
  };
}
