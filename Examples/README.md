# The examples, in order

Each example is one concept, built on the ones before it. Read them top to bottom and you have
the whole framework. Every `X.lean` here is a complete, verified app (pure Lean, no JS); the
matching `XWeb.lean` is its one-line browser entry, and `test/x_test.mjs` drives the real thing
in headless Chromium. Run any of them yourself:

```sh
QED_WEB_ROOT=Examples.TodoWeb ./qed build --dev   # then serve .qed/dev
```

A few examples have no browser entry at all: their point is a proof, and the demo is that the
file compiles.

## The architecture

1. **[Counter](Counter.lean)** · `Model`, `Msg`, `update`, `view`, and the `ui` builder: the
   whole shape of an app, plus the first `invariant … preserved_by`: state a property, the
   build proves every transition keeps it.
2. **[Native](Native.lean)** · the same `app`, run as a native binary: server-renders the
   initial page to stdout from the same verified view the browser uses. Nothing in an app is
   browser-specific.
3. **[Live](Live.lean)** · handlers that read the model (`onClick={.setTo (m.n * 2)}`) stay
   current across updates, and the event set is open (`onDoubleClick` works without a named
   helper).

## Views, styles, and proofs about them

4. **[Badge](Badge.lean)** · scoped styles (`css`, `styleSheet`) and the second kind of
   invariant: `holds_in view` proves a styling claim ("the badge is always on- or off-styled",
   "these two elements are never on together") for every reachable state. Proof-only, no
   browser entry.
5. **[Template](Template.lean)** · the full view vocabulary in one app: conditionals,
   controlled inputs, keyed and keyless lists, rows that change element by state, inline
   editing. Also the first hand-written invariant proof (`:= by …`) for a claim the automation
   can't guess: unique row ids, the fact that makes the keyed diff sound.

## Components

6. **[Todo](Todo.lean)** · a reusable `Component` (own model/msg/update/view) repeated as keyed
   rows in the parent's list, wired with one `embed` line. Parent-owned state: the rows live in
   the root model.
7. **[Feed](Feed.lean)** · `for_each`: lift one card's contract to "every card in the feed
   stays valid" across re-rank, dismiss, and load, in one line. Proof-only, no browser entry.
8. **[Local](Local.lean)** · the `component` declaration: state declared next to the view that
   uses it, `set`/`send` as the only mutations, each site compiled to a named `Msg` case the
   invariant machinery can point at (`stepperSafe`). Components bubble typed output
   (`emits`/`mountWith`), nest (a `Tag` inside each `Widget`), seed from props (`.localInit`),
   and the whole local store snapshots/restores.

## Forms and data

9. **[Signup](Signup.lean)** · `schema`: one declaration generates the draft, the validated
   type (proof-carrying fields), the form view, and the JSON codec, with "submit ⇔ valid" as a
   theorem, not a convention.
10. **[Booking](Booking.lean)** · a schema with a context binder: `schema Appt (today : Date)`
    lets a refinement depend on the clock, read once at startup with `Cmd.now`.
11. **[Users](Users.lean)** · the verified router (URL round-trip by proof), HTTP fetch +
    decode into typed data, and the form/keyboard/focus events.

## Effects

12. **[Effects](Effects.lean)** · side effects as data: localStorage, title, randomness, focus,
    file pick, batch, keyed-timer debounce, startup effects, and typed `ports` as the userland
    escape hatch. `update` stays pure throughout.
13. **[Chat](Chat.lean)** · `Cmd.stream`: a streaming LLM chat (POST + Server-Sent Events),
    one message per chunk, entirely in pure Lean.
14. **[Socket](Socket.lean)** · WebSockets: `Cmd.wsOpen`/`wsSend`/`wsClose` behind the same
    pure `update`; every inbound frame is an ordinary `Msg`.

## Everything together

15. **[Bookshelf](Bookshelf.lean)** · the capstone: three routed pages over a typed remote
    `Resource`, a schema form that POSTs and navigates to the result, scoped styles, and
    server-side rendering the client adopts without a refetch or flash
    ([BookshelfSSR.lean](BookshelfSSR.lean)).

## Appendix: entries and infrastructure

These are not part of the tour; they are the plumbing the tour runs on.

- **`*Web.lean`**: one-line browser entries (`import` the app, `Qed.run app`). `qed build`
  picks the entry from `QED_WEB_ROOT`; [Web.lean](Web.lean) (the counter) is the default.
- **SSR binaries**: [UsersSSR.lean](UsersSSR.lean), [BookshelfSSR.lean](BookshelfSSR.lean),
  [TemplateSSR.lean](TemplateSSR.lean) render full pages per request/route on the server, from
  the same views.
- **Benchmarks** ([Bench/](Bench/)): [Pipeline.lean](Bench/Pipeline.lean) (native rebuild+diff,
  `lake exe bench`), [App.lean](Bench/App.lean) (the React head-to-head,
  `test/bench_react.mjs`), and the `Scalar*`/`List*` entries (the template-vs-diff layer bench,
  `test/bench_template.mjs`).
- **Differential gate**: [JsGate.lean](JsGate.lean) / [JsProbe.lean](JsProbe.lean) render 96
  probe cases through native Lean and the transpiled JS and require byte-identical output
  (`test/js_gate_test.mjs`). They build `Html` via raw constructors on purpose; don't convert
  them.
