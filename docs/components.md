# Components

## Local state, props, and outputs

```lean
component Editor where
  prop label : String
  state note : String := ""
  emits String
  action edit => set note
  action save => send note
  view =>
    <div>
      <label>{label}</label>
      <input value={note} onInput={.edit}/>
      <button onClick={.save}>Save</button>
    </div>
```

Parent usage:

```lean
<Editor key={row.id} label={row.title}
  initial={{ note := row.text }} onEmit={Msg.saved row.id}/>
```

With a stable `key`, the local instance persists across parent updates. Changes to `row.title`
update the label. Changes to `row.text` do not reset the note: `initial` is used only on mount.
Qed maps emitted values to parent messages through `onEmit`. Here, the callback must accept
the `String` specified by `emits`.

Props are absent from state snapshots; restoring a snapshot does not replace current props.
A prop default allows callers to omit that prop. [Local](../Examples/Local.lean) demonstrates
parent updates during editing, nested components, and state restoration.

Previously, tag attributes named after state fields seeded state. Move those values into
`initial`, or declare them as `prop` if they should track the parent.

## Actions

For each `action` declaration, Qed generates a message constructor and a branch in the pure
update function. Inline `set` handlers still work. Action declarations allow typed parameters
and an optional guard:

```lean
action increment (amount : Nat) when (amount > 0) =>
  set count (count + amount), set saved count
```

Use `.increment 2` in an event handler. All `set` expressions and `send` outputs use the state
from before the action. In this example, `saved` is assigned the count before the increment.
When the guard is false, Qed skips the action's updates and output. `action edit => set note`
accepts an input payload; actions with explicit parameters must supply their set values explicitly.

Actions are `set`/`send` chains. Arbitrary transitions and effects remain available through
ordinary `Model`, `Msg`, `update`, and `ui`. Generated transitions are still usable in proofs;
for a component with props, their signature is `update props state message`.

## Child collections

For parent-managed state, `collection` generates child-message routing. The following parent
uses the `Row` component from [Todo](../Examples/Todo.lean), where `key id` defines row identity:

```lean
component Board where
  collection rows : Row
  action remove (id : Nat) => set rows (rows.filter (·.id != id))
  view =>
    <ul>{Row.each rows .rows fun row child =>
      <li>
        {child}
        <button onClick={.remove row.id}>Remove</button>
      </li>}</ul>
```

For each `collection` declaration, Qed generates an array field, a child message constructor,
and an `updateKeyed` branch. `Row.each` derives wrapper keys from the child's `key` declaration
and routes messages by that identity. Without a wrapper, it keys the child's root. Sorting
or deleting rows requires no manual message remapping; messages for removed rows are ignored.
Keys must remain unique and stable.

The shorthand binds children with state-only updates and no `emits` channel. For children
whose update also needs props, use explicit parent routing and `Row.updateKeyed props`.
Parent-owned tags accept live props alongside `state={row}` and `onMsg={.row}`.
See [Todo](../Examples/Todo.lean) for a complete app.

## Extracting views

Qed registers components used in helper functions, including imported helpers, when compiling
`ui`, generated component apps, and `Name.regs`. No helper annotation or manual registration
is required. Extracted `Html` helpers use normal DOM reconciliation; inline templates
can expose more bindings to the signal optimization.

Explicit `locals := …` remains available for low-level mounts or opaque definitions whose
implementations cannot be inspected. `mkApp` callers can use `withLocalRegistry (mkApp …)`.
