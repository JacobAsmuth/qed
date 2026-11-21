# Components & Apps

A `component` bundles props—including `Html` props and implicit `{children}`—local or routed state,
effectful actions, ports, queries, invariants, and a JSX view into a single verified declaration.
All Qed DSL blocks—`component`, `database`, `server`, `external`, `schema`, `router`, `invariant`,
and JSX `{...}`—share one unified Python-esque grammar with `:` headers, `=` assignment, `==`
equality, `and`/`or`/`not`/`in`/`is`, `1 <= x <= 10`, `f"..."`, `a if cond else b`, `elif`,
`match`/`case`, `return`, and `pass`.

## Pure sub-components

Stateless components compile to zero-overhead polymorphic view functions `Props msg → Html msg`
with no wrapper `<div>` and no JSON serialization, while preserving full cross-component HTML5 tag
nesting and attribute validation. `{children}` is automatically available whenever referenced in `view:`:

```lean
component Card:
  prop title : String
  prop badge : Html
  view:
    <div class="card">
      <header><h3>{title}</h3>{badge}</header>
      <div class="card-body">{children}</div>
    </div>

component BookRow:
  prop book : Book
  event onOrder
  view:
    <li class="book-row">
      <a href={R.detail(book.slot)}>{book.title}</a>
      <button onClick={onOrder}>Order copy</button>
    </li>

component SearchBar:
  bind query : String = ""
  event onSubmit(q: String)
  view:
    <form onSubmit={onSubmit(query)}>
      <input bind={query}/>
    </form>
```

Compose them directly inside JSX—including inside `<ul>`, `<tr>`, or `<select>`, and with two-way
`bind:field={parentField}` shorthands:

```lean
<Card title="Catalog" badge={<span>Live</span>}>
  <SearchBar bind:query={filter} onSubmit={.runSearch}/>
  <ul>{for b in books: <BookRow key={b.id} book={b} onOrder={.orderOne(b.slot)}/>}</ul>
</Card>
```

## Unified stateful & effectful components

Top-level applications and reusable stateful components use the same `component` syntax:

```lean
component Storefront:
  session user
  route : R = .catalog:
    case .catalog:
      books = await Catalog.list()
    case .detail(_):
      pass
  query current = Catalog.findAt(idx) if let .detail(idx) = route
  state books       : Resource Book[]
  state statusMsg   = ""
  ephemeral hover   = false

  action orderOne(idx: Nat):
    if user.isSome:
      statusMsg = "Ordering…"
      let updated = await Catalog.order(idx, 1) catch:
        case .outOfStock:  statusMsg = "Order failed: out of stock"
        case .notFound:    statusMsg = "Order failed: book not found"
        case .failed(err): statusMsg = f"Order failed: {err}"
      books = books.map(arr => arr.set(idx, updated) if idx < arr.size else arr)
      statusMsg = f"Ordered {updated.title}"

  view:
    <Await of={books} as={arr} err={e} loading={<p>Loading…</p>} failed={<p class="error">{e}</p>}>
      <ul>{for b in arr: <BookRow key={b.id} book={b} onOrder={.orderOne(b.slot)}/>}</ul>
    </Await>
```

- **`session user`** declares a `String?` field hydrated automatically from the verified server session during SSR via `App.onSession`, so actions requiring `ctx.userId != none` can guard with `if user.isSome:` or `if not user.isSome: return`.
- **`await` and `catch:`** allow direct async RPC calls inside `route` and `action` blocks: `field = await Server.fn(...)` transitions `field : Resource α` to `.loading` and populates it on completion, while `let x = await Server.fn(...) catch: case .tag: ...` flushes pre-`await` assignments, suspends, enforces exhaustive domain error handling, and resumes in a synthesized continuation message with the server's `ensures` proof in scope.
- **`(field = _)` and bare `Cmd` calls** remain available for lower-level `Cmd` composition in `start`, `route`, or `action`—for example `Catalog.list((books = _))` or `Cmd.pushUrl(...)`—and schemas provide `<Book.Form onSubmit={.submit}/>` with optional `bind={draft}`, `reset`, and `field = some(_)` shorthand.
- **`route`** binds the current URL route into state, defaulting the field name to `route`, and runs optional `case` arms on navigation.
- **`start`** schedules initial commands when the app mounts.
- **`ephemeral`** excludes client-only fields from SSR dehydration and resets them to their defaults on hydration. All other `state` fields auto-dehydrate by default, and `T[]`, `T?`, `Resource T`, and `Cached T` default to `[]`, `none`, `.idle`, and `{}`.
- **`port`** declares typed JS interop ports: `port name : Arg` for outbound events and `port name(arg: Arg): ...` for inbound callbacks.
- **`query`** declares cached reactive server queries such as `query current = Catalog.findAt(idx) if let .detail(idx) = route` or `query quote = Store.quote(qty) if user.isSome`. Queries enforce read-only server RPCs, prove `session` auth and parameter `requires` preconditions from `if` guards and component invariants, key entries with binary Protobuf cache keys for stale-while-revalidate and stale-response rejection, preload on SSR with zero-refetch hydration, and propagate server `ensures` into `Cached.all` invariants such as `quote.all(v => ...)`.
- **`<Await of={res} as={val} err={e} loading={…} failed={…}>`** renders `Resource α` or `Cached α`
  declaratively in JSX.
- **`fullstack`** accepts `client Storefront` directly for any `component`.
- **Namespace helpers:** If a namespace with the component's name, such as `namespace Storefront ... end Storefront`,
  is defined beforehand, its symbols are automatically in scope inside `component Storefront:`.

## Optimistic UI with `predict`

Any client `await` on a server RPC can attach a `predict` clause so the UI updates at 0 ms latency
and automatically reconciles or rolls back when the server replies:

```lean
action orderOne(idx: Nat):
  if not user.isSome: return
  let updated = await Catalog.order(idx, 1)
    predict:
      if let .ok(arr) = books:
        if idx < arr.size:
          let b = arr[idx]
          if 1 <= b.stock:
            return Book(id=b.id, slot=b.slot, title=b.title, stock=b.stock - 1)
    on_confirm:
      statusMsg = f"Confirmed order for {updated.title}"
    catch:
      case .outOfStock:  statusMsg = "Order failed: out of stock"
      case .notFound:    statusMsg = "Order failed: book not found"
      case .failed(err): statusMsg = f"Order failed: {err}"
  books = books.map(arr => arr.set(idx, updated) if idx < arr.size else arr)
  statusMsg = f"Ordered {updated.title}"
```

- **Inline or conditional prediction:** Use `predict <expr>` for an always-on prediction, or
  `predict: <suite>` returning via `return <expr>` to fall back to a regular blocking `await`
  when a branch doesn't return. Resource fields also support the shorthand
  `items = await Store.add(item) predict nextItems`.
- **Event-sourced transactional rollback:** Speculative updates run inside a verified speculative
  journal in `Qed.Speculative`. When the server responds:
  - **Exact match via `SpecEq`:** the pending entry confirms in place with zero UI flicker, and
    `on_confirm:` runs once.
  - **Mismatch:** by default, the speculative continuation is rolled back, re-applied with the
    server's `actual` value, `on_confirm:` runs, and any concurrent local edits such as typing in
    an `<input>` are replayed cleanly on top without losing user input.
  - **Custom `rollback:` / `rollback(actual):`:** overrides the default mismatch reconciliation by
    dropping the speculative continuation and running the rollback block instead, skipping
    `on_confirm:`.
  - **Server error via `catch:`:** rolls back the speculative continuation, runs the matching `catch:`
    arm, and replays subsequent concurrent local edits on top.
- **Compile-time guarantees:**
  - The speculative continuation must be pure state updates—no `Cmd` calls, `.emit(...)`, `.send(...)`, nested `await`,
    or `bind` writes; put side effects in `on_confirm:`.
  - The predicted value is statically proved to satisfy the server method's `ensures` postconditions
    as well as any `schema` `Field` refinements.
  - Declared component `invariant`s are automatically proved across the speculative continuation,
    `on_confirm:`, `rollback:`, `catch:`, and journal replay via `SpecEngine.step_preserves_inv`.

## Stateful sub-components: static hoisting vs. keyed `LocalDef`

Qed supports three stateful composition modes:

1. **Static hoisting:** Automatic inside `component`. Mounting a stateful or effectful
   sub-component without `key=` or `initial=`—or one using `{children}`, `Html` props, `bind:`, or
   `Cmd` effects—hoists its state, `Out` events, `bind:` updates, and `Cmd` effects directly into the
   parent component with zero JSON overhead, including interactive `{children}` that dispatch parent
   actions.
2. **Dynamic keyed local cells:** Mounting `<Editor key={row.id} initial={{ note = row.text }} onSave={…}/>`
   registers a `LocalDef` cell whose state is keyed per row and survives parent list re-renders.
3. **Parent-owned `collection`s:** When a parent needs to read, filter, or sort child states,
   declare `collection rows : Row` where `Row` declares `key id`. Inside the parent view,
   `<Row key={r.id} state={r}/>` automatically infers `onMsg={.rows}`, and `{for r in rows: <Row state={r}/>}`
   automatically injects the child's key.

## Actions & inline invariants

Actions execute **sequentially**—matching `server` functions, so each assignment is immediately visible to subsequent lines—and support `let` bindings, field and array updates `=`, `+=`, `-=`, `arr.push(x)`, `arr[i] = val`, handle calls `ev.emit(...)`, `chan.send(...)`, `port.send(...)`, bare `Cmd` calls like `Cmd.pushUrl(...)` and `Resource.fetch(...)`, `pass`, `return`, `if`/`elif`/`else`, `if let`, and `match`/`case`:

```lean
action advance(times: Nat):
  if times > 0:
    count += step * times
    saved = count

invariant countBounds: 0 <= count, saved <= count
invariant saveStyled: roleHasOneOf("save", [primaryStyle, disabledStyle])
invariant feedSafe: Feed.Card.cardSafe for_each cards
```

Because statements execute sequentially, `saved` observes the updated `count`, and Qed automatically proves declared state invariants across `init`, every action, and hoisted sub-component transitions.
