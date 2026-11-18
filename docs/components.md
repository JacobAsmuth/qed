# Components & Apps

A `component` bundles props, slots, `children`, local or routed state,
effectful actions, ports, queries, invariants, and a JSX view into a single verified declaration.

## Pure sub-components (`children`, `slot`, `event`, and `bind:`)

Stateless components compile to zero-overhead polymorphic view functions (`Props msg → Html msg`)
with no wrapper `<div>` and no JSON serialization, while preserving full cross-component HTML5 tag
nesting and attribute validation:

```lean
component Card where
  prop title : String
  slot badge
  children
  view =>
    <div class="card">
      <header><h3>{title}</h3>{badge}</header>
      <div class="card-body">{children}</div>
    </div>

component BookRow where
  prop book : Book
  event onOrder
  view =>
    <li class="book-row">
      <a href={R.detail book.slot}>{book.title}</a>
      <button onClick={onOrder}>Order copy</button>
    </li>

component SearchBar where
  bind query : String := ""
  event onSubmit (q : String)
  view =>
    <form onSubmit={onSubmit query}>
      <input bind={query}/>
    </form>
```

Compose them directly inside JSX—including inside `<ul>`, `<tr>`, or `<select>`, and with two-way
`bind:field={parentField}` shorthands:

```lean
<Card title="Catalog" badge={<span>Live</span>}>
  <SearchBar bind:query={filter} onSubmit={.runSearch}/>
  <ul>{for b in books => <BookRow key={b.id} book={b} onOrder={.orderOne b.slot}/>}</ul>
</Card>
```

## Unified stateful & effectful `component` (`session`, `route`, `start`, `await`, `ephemeral`, `port`, `query`)

Top-level applications and reusable stateful components use the same `component` syntax:

```lean
component Storefront where
  session user
  route : R := .catalog
    | .catalog    => books := await Catalog.list()
    | .detail idx => current := await Catalog.findAt(idx)
  state books       : Resource (Array Book) := .idle
  state current     : Resource Book := .idle
  state statusMsg   := ""
  ephemeral hover   := false

  action orderOne (idx : Nat) when user.isSome =>
    statusMsg := "Ordering…"
    let updated := await Catalog.order(idx, 1) catch
      | .outOfStock => statusMsg := "Order failed: out of stock"
      | .notFound   => statusMsg := "Order failed: book not found"
      | .failed err => statusMsg := s!"Order failed: {err}"
    books := books.map fun arr => if h : idx < arr.size then arr.set idx updated else arr
    statusMsg := s!"Ordered {updated.title}"

  view =>
    <Await of={books} as={arr} err={e} loading={<p>Loading…</p>} failed={<p class="error">{e}</p>}>
      <ul>{for b in arr => <BookRow key={b.id} book={b} onOrder={.orderOne b.slot}/>}</ul>
    </Await>
```

- **`session user`** declares an `Option String` field hydrated automatically from the verified server session during SSR (`App.onSession`) so actions requiring `ctx.userId != none` can guard with `when user.isSome =>`.
- **`await` and `catch`** allow direct C-style async RPC calls inside `route` and `action` blocks: `field := await Server.fn(...)` transitions `field : Resource α` to `.loading` and populates it on completion, while `let x := await Server.fn(...) catch | .tag => ... | .failed err => ...` flushes pre-`await` assignments, suspends, enforces exhaustive domain error handling, and resumes in a synthesized continuation message with the server's `ensures` proof in scope.
- **`(field := ·)` and `perform`** remain available for lower-level `Cmd` composition in `start`, `route`, or `action` (for example `perform (Catalog.list (books := ·))`), and schemas provide `<Book.Form bind={draft} onSubmit={.submit}/>`.
- **`route`** binds the current URL route into state (defaulting the field name to `route`) and runs optional match arms on navigation.
- **`start`** schedules initial commands when the app mounts.
- **`ephemeral`** excludes client-only fields from SSR dehydration and resets them to their defaults on hydration (all other `state` fields auto-dehydrate by default).
- **`port`** declares typed JS interop ports (`port name : Arg` outbound, `port name (arg : Arg) => ...` inbound).
- **`query`** declares cached remote queries (`query items : Array Item` with `key := ...` and `url := ...`).
- **`<Await of={res} as={val} err={e} loading={…} failed={…}>`** renders `Resource α` or `Cached α`
  declaratively in JSX.
- **`fullstack`** accepts `client Storefront` directly for any `component`.
- **Namespace helpers:** If a namespace with the component's name (such as `namespace Storefront ... end Storefront`)
  is defined beforehand, its symbols are automatically in scope inside `component Storefront where`.

## Stateful sub-components: static hoisting vs. keyed `LocalDef`

Qed supports three stateful composition modes:

1. **Static hoisting (automatic inside `component`):** Mounting a stateful or effectful
   sub-component without `key=` / `initial=` (or one using `children`, `slot`, `bind:`, or
   `perform`) hoists its state, `Out` events, `bind:` updates, and `Cmd` effects directly into the
   parent component with zero JSON overhead—including interactive `{children}` that dispatch parent
   actions.
2. **Dynamic keyed local cells (`key=` / `initial=`):** Mounting `<Editor key={row.id} initial={{ note := row.text }} onSave={…}/>`
   registers a `LocalDef` cell whose state is keyed per row and survives parent list re-renders.
3. **Parent-owned `collection`s:** When a parent needs to read, filter, or sort child states,
   declare `collection rows : Row` (where `Row` declares `key id`). Inside the parent view,
   `<Row key={r.id} state={r}/>` automatically infers `onMsg={.rows}`, and `{for r in rows => <Row state={r}/>}`
   automatically injects the child's key.

## Actions & inline invariants

Actions support `let` bindings, simultaneous field updates (`:=`, `+=`, `-=`), `when` guards,
`perform`, `send`, `()`, `return` (early exit), `if … then … else …`, `if let … := … then …`, and `match … with`:

```lean
action advance (times : Nat) when times > 0 =>
  count += step * times
  saved := count

invariant 0 ≤ count, saved ≤ count
invariant roleHasOneOf "save" [primaryStyle, disabledStyle]
invariant feedSafe : Feed.Card.cardSafe for_each cards
```

Flat assignment sequences read *pre-action* state simultaneously (`saved` receives the previous
`count`), and Qed automatically proves declared state invariants across `init`, every action, and
hoisted sub-component transitions.
