// `App.ssrStep` is generic over `(Model, Msg)`, which compile to two leading erased parameters.
const ERASED = 0;

export function makeHandler(mod, opts = {}) {
  const app = mod.app();
  const title = opts.title ?? 'app';
  const script = opts.script ?? '/qed.js';
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
          // `x-qed-ssr` prevents a fronting `qed_serve` from recursively SSR-rendering API misses.
          const res = await doFetch(new URL(n.url, url.origin), {
            method: n.method,
            body: n.method === 'GET' || n.method === 'HEAD' ? undefined : n.body,
            headers: { 'x-qed-ssr': '1',
                       ...(n.body ? { 'content-type': 'application/json' } : {}) },
          });
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
