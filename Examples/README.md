# The examples, in order

**[Bookshelf](Bookshelf.lean)** covers forms and routing,
**[Local](Local.lean)** covers component state and props, and **[Chat](Chat.lean)** covers streaming.
The numbered tour below introduces one concept at a time. The apps are written in Lean and
compiled to JavaScript to run in the browser. Some examples focus on proofs and don't have
a browser demo.

Run the self-contained component examples from the repository root with the Lean toolchain
and Node.js installed:

```sh
QED_WEB_ROOT=Examples.TodoWeb ./qed dev
# Open http://localhost:8000. LocalWeb and SignupWeb work the same way.
```

Examples that use HTTP also need a backend. The following demos supply local mock APIs.
Only run one build/dev command at a time: the examples share `.qed/dev`.

## Bookshelf

```bash
QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev
node Examples/bookshelf-server.mjs
```

The app runs at http://localhost:8000. Its form's submit button is disabled until the fields
validate. Submission adds the book and navigates to its detail page. Direct page loads are
server-rendered. The local mock API stores books in memory and
resets when stopped. The app includes its data in the server-rendered page so the browser can
reuse it. The demo server connects the generated SSR handler to the API.

The README screenshot shows this app's catalog with the demo seed data. To run the browser
checks, install the test dependencies with `npm ci --prefix test`, then run
`node test/bookshelf_test.mjs` and `node test/bookshelf_hydrate_test.mjs` separately.

## Streaming chat

```bash
QED_WEB_ROOT=Examples.ChatWeb ./qed build --dev
python3 test/mock_llm.py 8000 .qed/dev
```

The app runs at http://localhost:8000. The local mock streams a canned reply to each message;
no API key is needed. The transition from [Chat.lean](Chat.lean) uses that file's
`Model`, `Msg`, and helper definitions:

```lean
def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .typed s   => { m with draft := s }
  | .send      =>
      let draft := m.draft.trimmed
      if draft.isEmpty then m else
      let convo := m.turns.push { user? := true, text := draft }
      ({ turns   := convo.push { user? := false, text := "" }
         draft   := ""
         pending := true },
       .stream "/v1/chat/completions" (reqBody convo) .chunk .done)
  | .chunk raw => { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => { m with pending := false }
```

For branches returning only a model, `steps` supplies an empty command. `Cmd.stream` delivers
SSE payloads as `.chunk` messages and signals completion with `.done`; the transition itself
performs no I/O. The `streamSafe` invariant in the source proves that a pending reply has a
nonempty conversation in the model.

## The architecture

0. **[Hello](Hello.lean)** · a component with state, a view, and `set` handlers,
   started with `Qed.run Hello.app`.
1. **[Counter](Counter.lean)** · `Model`, `Msg`, `update`, `view`, and the `ui` builder: the
   app structure that `component` generates, written explicitly. An
   `invariant … preserved_by` checks that every transition preserves a property.
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
   can't guess: every existing id is below the next allocated id. Pairwise uniqueness is
   a separate property.

## Components

6. **[Todo](Todo.lean)** · a `component` repeated as keyed rows in a parent-owned list:
   `collection rows : Row` generates the parent message and routing arm. `Row.each` keys
   the wrappers and routes messages using the child's declared identity.
7. **[Feed](Feed.lean)** · `for_each`: lift one card's contract to "every card in the feed
   stays valid" across re-rank, tick (the parent updating its rows directly), dismiss, and
   load. A multi-field `set` chain in the card's like handler. Proof-only, no
   browser entry.
8. **[Local](Local.lean)** · the same `component` declaration mounted the other way
   (`<Widget key={…}/>`): the framework owns the state, keyed per instance, outside the
   root model. `set`/`send` as the only mutations, each site compiled to a named `Msg` case
   the invariant machinery can point at (`stepperSafe`). Components bubble typed output
   (`emits`/`onEmit`), nest (a `Tag` inside each `Widget`), separate live props from
   `initial` state, register through helper functions, and the local
   store snapshots/restores.

## Forms and data

9. **[Signup](Signup.lean)** · `schema`: one declaration generates the draft, the validated
   type (proof-carrying fields), the form view, and the JSON codec. A theorem checks that
   the submit gate agrees with validation.
10. **[Booking](Booking.lean)** · a schema with a context binder: `schema Appt (today : Date)`
    lets a refinement depend on the clock, read once at startup with `Cmd.now`.
11. **[Users](Users.lean)** · the verified router (URL round-trip by proof), HTTP fetch +
    decode into typed data, and the form/keyboard/focus events.

## Effects

12. **[Effects](Effects.lean)** · side effects as data: localStorage, title, randomness, focus,
    file pick, batch, keyed-timer debounce, startup effects, and typed `ports` as the userland
    escape hatch. `update` stays pure throughout.
13. **[Chat](Chat.lean)** · `Cmd.stream`: a streaming LLM chat (POST + Server-Sent Events),
    one message per chunk, handled by a Lean transition function.
14. **[Socket](Socket.lean)** · WebSockets: `Cmd.wsOpen`/`wsSend`/`wsClose` behind the same
    pure `update`; every inbound frame is an ordinary `Msg`.

## Everything together

15. **[Bookshelf](Bookshelf.lean)** · three routed pages over a typed remote
    `Resource`, a schema form that POSTs and navigates to the result, scoped styles, and
    server-side rendering the client adopts using the app's state restoration hooks.
    `qed build` emits the request handler (`ssr.mjs`) from the app itself
    (see `test/bookshelf_ssr_test.mjs`).

## Appendix: entries and infrastructure

These are not part of the tour; they are the plumbing the tour runs on.

- **`*Web.lean`**: one-line browser entries (`import` the app, `Qed.run app`). `qed build`
  picks the entry from `QED_WEB_ROOT`; [Web.lean](Web.lean) (the counter) is the default.
- **SSR substrate binaries**: [UsersSSR.lean](UsersSSR.lean) and
  [TemplateSSR.lean](TemplateSSR.lean) call the render primitives (`renderModel` /
  `renderDocument`) directly, for the hydration tests. Apps don't write this; `qed build`
  generates the per-request handler (`ssr.mjs`) from the app itself.
- **Benchmarks** ([Bench/](Bench/)): [Pipeline.lean](Bench/Pipeline.lean) (native rebuild+diff,
  `lake exe bench`), [App.lean](Bench/App.lean) (the React head-to-head,
  `test/bench_react.mjs`), and the `Scalar*`/`List*` entries (the template-vs-diff layer bench,
  `test/bench_template.mjs`).
- **Differential gate**: [JsGate.lean](JsGate.lean) / [JsProbe.lean](JsProbe.lean) render 96
  probe cases through native Lean and the transpiled JS and require byte-identical output
  (`test/js_gate_test.mjs`). They build `Html` via raw constructors on purpose; don't convert
  them.
