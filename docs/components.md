# Components & Apps

A `component` (or top-level `app`) bundles props, slots, `children`, local or routed state,
effectful actions, invariants, and a JSX view into a single verified declaration.

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
  <ul>{books.map fun b => <BookRow key={b.id} book={b} onOrder={.orderOne b.slot}/>}</ul>
</Card>
```

## Unified `app` / effectful `component` (`route`, `start`, `perform`, `ephemeral`)

Top-level applications and stateful components share the exact same syntax (`app Name where` is an
alias for `component Name where`):

```lean
app Storefront where
  route route : R := .catalog
    | .catalog    => books := .loading, perform (Catalog.list (books := ·))
    | .detail idx => current := .loading, perform (Catalog.findAt idx (current := ·))
  state books     : Resource (Array Book) := .idle
  state current   : Resource Book := .idle
  ephemeral hover := false

  action orderOne (idx : Nat) =>
    perform (Catalog.order idx 1 (.ordered idx))

  action ordered (idx : Nat) (r : Resource Book) =>
    match r with
    | .ok updated =>
        books := books.map fun arr => if h : idx < arr.size then arr.set idx updated else arr
    | _ => ()

  view =>
    <Await of={books} as={arr} loading={<p>Loading…</p>}>
      <ul>{arr.map fun b => <BookRow key={b.id} book={b} onOrder={.orderOne b.slot}/>}</ul>
    </Await>
```

- **`(field := ·)`** creates a typed setter callback (`T → Msg`) anywhere inside `perform`,
  `start`, or `view` (for example `Catalog.list (books := ·)` or `Book.formView draft (draft := ·) .submit`).
- **`route`** binds the current URL route into state and runs optional match arms on navigation.
- **`start`** schedules initial commands when the app mounts.
- **`ephemeral`** excludes client-only fields from SSR dehydration (all other `state` fields
  auto-dehydrate by default).
- **`<Await of={res} as={val} loading={…} failed={…}>`** renders `Resource α` or `Cached α`
  declaratively in JSX.
- **`fullstack`** accepts `client Storefront` directly when `Storefront` is an `app` or `component`.

## Stateful sub-components: static hoisting vs. keyed `LocalDef`

Qed supports three stateful composition modes:

1. **Static hoisting (automatic inside `component` / `app`):** Mounting a stateful or effectful
   sub-component without `key=` / `initial=` (or one using `children`, `slot`, `bind:`, or
   `perform`) hoists its state, `Out` events, `bind:` updates, and `Cmd` effects directly into the
   parent component with zero JSON overhead—including interactive `{children}` that dispatch parent
   actions.
2. **Dynamic keyed local cells (`key=` / `initial=`):** Mounting `<Editor key={row.id} initial={{ note := row.text }} onEmit={…}/>`
   registers a `LocalDef` cell whose state is keyed per row and survives parent list re-renders
   (see [`Examples/Local.lean`](../Examples/Local.lean)).
3. **Parent-owned `collection`s:** When a parent needs to read, filter, or sort child states,
   declare `collection rows : Row` (where `Row` declares `key id`). Inside the parent view,
   `<Row key={r.id} state={r}/>` automatically infers `onMsg={.rows}` (or use `Row.each rows .rows`
   to wrap each row).

## Actions & inline invariants

Actions support `let` bindings, simultaneous field updates (`:=`, `+=`, `-=`), `when` guards,
`perform`, `send` / `emit`, `()`, `if … then … else …`, `if let … := … then …`, and `match … with`:

```lean
action advance (times : Nat) when times > 0 =>
  count += step * times
  saved := count

invariant 0 ≤ count, saved ≤ count
invariant roleHasOneOf "save" [primaryStyle, disabledStyle]
```

Flat assignment sequences read *pre-action* state simultaneously (`saved` receives the previous
`count`), and Qed automatically proves declared state invariants across `init`, every action, and
hoisted sub-component transitions.
