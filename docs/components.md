# Components

A `component` bundles props, state, actions, invariants, and a JSX view into a single
declaration. You can run a component on its own (`Qed.run Name.app`), mount it with isolated
local state inside a parent view, or manage an array of child components from a parent's
`collection`.

## Local state, props, and outputs

```lean
component Editor where
  prop label : String
  state note := ""
  emits String
  action save => send note
  view =>
    <div>
      <label>{label}</label>
      <input bind={note}/>
      <button onClick={.save}>Save</button>
    </div>
```

Mount `Editor` inside a parent view like an ordinary JSX element:

```lean
<Editor key={row.id} label={row.title}
  initial={{ note := row.text }} onEmit={Msg.saved row.id}/>
```

How these attributes behave across updates:

- **`key`** gives the local instance a stable identity so its state survives parent re-renders.
- **`prop` fields** (like `label`) stay live—when `row.title` changes in the parent, the child
  updates immediately. Declaring a default value on a `prop` makes that attribute optional.
- **`initial`** seeds local `state` on first mount only. Later changes to `row.text` will not
  overwrite an in-progress edit.
- **`onEmit`** maps emitted child values (`send note`) into parent messages, typed against the
  component's `emits` declaration.
- **Snapshots:** state snapshots capture local `state` only, never `prop` values, so restoring a
  snapshot leaves current props intact.

See [`Examples/Local.lean`](../Examples/Local.lean) for live parent updates during editing,
nested local components, and state snapshot restoration.

> **Migration note:** Older versions seeded state from tag attributes named after state fields.
> Pass initial state via `initial={{ … }}` instead, or change the field to `prop` if it should
> track the parent on every render.

## Actions

Each `action` generates a typed message constructor and a branch in the component's pure
`update` function. Inline handlers—such as `{count += 1}`, `{note := ""}`, and `<input bind={note}/>`—also
compile into named message constructors rather than opaque closures.

Actions can take typed parameters, an optional `when` guard, local `let` bindings, and one or
more assignments (separated by newlines or commas):

```lean
action increment (amount : Nat) when amount > 0 =>
  let next := count + amount
  count := next
  saved := count
```

Trigger this action from JSX with `onClick={.increment 2}`. Keep three evaluation rules in mind:

- **Simultaneous updates:** field updates (`:=`, `+=`, `-=`) and `send` outputs read the
  *pre-action* state (plus any earlier `let` bindings). Above, `next` is `count + amount`, while
  `saved` receives the old `count`.
- **Guards:** when a `when` condition is false, the action becomes a no-op and emits nothing.
- **Input binding:** `<input bind={note}/>` (or `{note := ·}`) wires a string/checkbox input
  directly to a state field. Actions with explicit parameters receive all arguments from the
  handler call site.

## Inline invariants

Components can declare state and styling invariants directly inside the `component` block:

```lean
invariant 0 ≤ count, saved ≤ count
invariant roleHasOneOf "save" [primaryStyle, disabledStyle]
```

- **State invariants** refer to state fields directly. For standalone components (without
  props), Qed automatically verifies both `Name.init` and every branch of `Name.update`.
- **View invariants** check rendered output across all component states (see
  [invariants](invariants.md#styling-invariants-over-the-view)).

Generated transitions are ordinary Lean functions (`Name.update state msg`, or
`Name.update props state msg` when props exist), so you can also reference them in external
theorems. When a component needs HTTP, timers, routing, or custom effectful transitions, drop
down to an explicit `Model`, `Msg`, `transition`, and `ui`.

## Child collections

When a parent needs to read, filter, or sort its children's state, use `collection` instead of
isolated local state. Here `Board` manages an array of `Row` items (from
[`Examples/Todo.lean`](../Examples/Todo.lean), where `Row` declares `key id`):

```lean
component Board where
  collection rows : Row
  action remove (id : Nat) => rows := rows.filter (·.id != id)
  view =>
    <ul>{Row.each rows .rows fun row child =>
      <li>
        {child}
        <button onClick={.remove row.id}>Remove</button>
      </li>}</ul>
```

`collection rows : Row` generates:

1. An array state field (`rows : Array Row.State`).
2. A parent message constructor (`.rows`) that wraps child messages by key.
3. A keyed update branch (`Row.updateKeyed`) that routes messages to the matching row and
   safely ignores stale messages for deleted rows.

In the view, `Row.each` keys the wrapper element (`<li>`)—or the child's own root when no
wrapper is added—using the child's declared `key`. Keep keys unique and stable across updates so
sorting or deleting rows needs no manual index bookkeeping.

`collection` targets state-only children without `emits`. If a child's update depends on parent
props, route messages explicitly with `Row.updateKeyed props` and render `<Row state={row} onMsg={.row} …/>`.

## Extracting helper views

You can freely extract parts of a view into helper functions (including across modules). When
Qed compiles `ui`, `Name.app`, or `Name.regs`, it automatically discovers and registers any
local components mounted inside those helpers—no manual registration list is needed.

Inline JSX inside `ui` gives Qed's template compiler maximum visibility for fine-grained signal
bindings, whereas extracted `Html` helpers reconcile through standard virtual-DOM diffing. For
low-level manual mounts or opaque definitions that Qed cannot unfold, you can still pass
`locals := …` explicitly (or wrap `mkApp` with `withLocalRegistry`).
