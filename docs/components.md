# Components

Declare state, live props, and actions next to the view:

```lean
component Editor where
  prop label : String
  state note : String := ""
  state saved : String := ""
  action edit => set note
  action save => set saved note
  view =>
    <div>
      <label>{label}</label>
      <input value={note} onInput={.edit}/>
      <button onClick={.save}>Save</button>
    </div>
```

Mount it with `<Editor key={id} label={title} initial={{ note := text }}/>`.
Changing `title` updates the label. Changing `text` leaves the user's edited note alone:
`initial` applies only when the instance first mounts. Props are absent from state snapshots,
and restoring a snapshot keeps current props. Declare a prop default when callers may omit it.

Previously, tag attributes named after state fields seeded state. Move those values into
`initial`, or declare them as `prop` if they should track the parent.

## Actions

An action generates a named message constructor and a pure update arm. Inline `set`
handlers still work. Actions accept typed parameters and an optional guard:

```lean
action increment (amount : Nat) when (amount > 0) =>
  set count (count + amount), set saved count
```

Use `.increment 2` in an event handler. Both assignments read the same pre-update state:
`saved` receives the old count. With `emits T`, a trailing `send value` reads that state too.
A false guard changes nothing and emits nothing. `action edit => set note` accepts an input
payload; actions with explicit parameters must supply their set values explicitly.

Actions are `set`/`send` chains. Arbitrary transitions and effects remain available through
ordinary `Model`, `Msg`, `update`, and `ui`. Generated transitions are still usable in proofs;
for a component with props, their signature is `update props state message`.

## Child collections

Declare identity on the child with `key id`, then bind it in the parent:

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

`collection` generates the array field, the child message constructor, and the `updateKeyed`
arm. `Row.each` routes child messages and keys each wrapper using the child's declared identity.
Without a wrapper, it keys the child's root. Keys must remain unique and stable. Sorting and
deletion stay explicit; a message for a removed row is ignored.

The shorthand binds children with state-only updates and no `emits` channel. For children
whose update also needs props, use explicit parent routing and `Row.updateKeyed props`.
Parent-owned tags accept live props alongside `state={row}` and `onMsg={.row}`.
See [Todo](../Examples/Todo.lean) for a complete app.

## Extracting views

Ordinary helper functions, including imported helpers, carry their component registrations
into `ui`, generated component apps, and `Name.regs`. There is no helper annotation or manual
registration step. Extracted `Html` helpers use normal DOM reconciliation; inline templates
can expose more bindings to the signal optimization.

Explicit `locals := …` remains available for low-level mounts or opaque definitions whose
implementations cannot be inspected. `mkApp` callers can use `withLocalRegistry (mkApp …)`.
