// qed_ssr_host.mjs: the request loop around the transpiled `Qed.App.ssrStep`.
// All the SSR logic (route dispatch, running the app's queries, render, dehydrate) is
// verified Lean inside the step; this file only performs the fetches the step asks for
// and hands back a Response. Web-standard APIs only (URL/Response/fetch), so the same
// handler runs under node and edge runtimes.
//
// `qed build` emits `dist/ssr.mjs`, which imports the transpiled app and calls
// `makeHandler` (see Cli.lean). Apps never import this file directly.

// The transpiler erases type arguments to placeholder parameters: `App.ssrStep` is
// generic over (Model, Msg), so the exported function takes two dummies first.
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
      // Fetch everything the step still needs; an error becomes an `ok: false` result,
      // which the app's own error arm folds in (it renders its failed state, no throw).
      const fetched = await Promise.all(out.need.map(async (n) => {
        try {
          // `x-qed-ssr` marks the fetch as the renderer's own, so a fronting server
          // (qed_serve.mjs) answers it with data or 404, never by rendering a page,
          // which would recurse.
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
