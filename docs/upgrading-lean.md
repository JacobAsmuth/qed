# Upgrading the Lean toolchain

Qed pins one Lean toolchain for the whole repo (`lean-toolchain`). The pin exists because the
build-time transpiler (`Js/Backend.lean`) reads `Lean.IR`, which is internal and changes between
releases. **What you ship is unaffected** — the emitted `.mjs` is plain JavaScript with no Lean at
runtime — only the *build* is coupled, and the coupling is bounded and fail-loud. A bump is a
checklist, not an archaeology dig. This file is that checklist, with the v4.15 → v4.30 jump as a
worked example.

Do it on a branch. At each step, the failure mode tells you exactly what to fix.

## 1. Bump the toolchain

```bash
echo "leanprover/lean4:vX.Y.0" > lean-toolchain
elan toolchain install leanprover/lean4:vX.Y.0
```

No external package deps (`lake-manifest.json` is empty), so there is nothing else to co-upgrade.

## 2. Build the framework — `lake build Qed`

Surfaces core/`Std` API churn in the framework itself. These are ordinary deprecations/renames; the
error or warning names the fix. From v4.15 → v4.30:

- `String.mk` → `String.ofList`, `String.data` → `String.toList` (deprecations).
- `Array.mkArray` → `Array.replicate`.
- `String` became UTF-8/`ByteArray`-backed: the anonymous constructor `⟨listChar⟩ : String` no
  longer works (it now resolves to `String.ofByteArray`); use `String.ofList`. Proofs over the old
  `List Char` representation switch to `String.toList_ofList` and friends.
- Stdlib lemmas making their explicit args implicit: `List.not_mem_nil`, `List.mem_cons_self`.
- A stricter `simp`: an `if` in a proof goal is no longer split for free — add `split` (this bit
  `Examples/Chat.lean`'s invariant).
- The `unusedSimpArgs` linter flags now-redundant `simp only [...]` args; trim them.

## 3. Build the transpiler — `lake build qedjs`

Surfaces `Lean.IR` changes. The dependent surface is enumerated in the header of `Js/Backend.lean`;
that header is the list to recheck. Failures are loud: a removed/renamed IR constructor breaks an
exhaustive `match` ("Unknown constant …" / "Missing cases …"), a renamed accessor fails to resolve.
From v4.15 → v4.30:

- `Lean.IR.Arg.irrelevant` → `Arg.erased`; `Lean.IR.IRType.isIrrelevant` → `isErased`.
- `Lean.IR.FnBody.mdata` was removed (drop the match arms).
- `List.enum` → `List.zipIdx` (the tuple flips from `(i, a)` to `(a, i)`).
- `Lean.Import` gained fields (`importAll`/`isExported`/`isMeta`); build it with `{ module := … }`
  and the defaults instead of `Import.mk m false`.

## 4. The runtime IO convention (`runtime/qed_rt.mjs`)

This is the one change that isn't a compile error — it is a *semantic* convention. Confirm how the
target version represents IO by dumping the IR of a small IO function:

```lean
-- lake env lean --run a file that importModules and `IO.println (toString (format decl))`
```

What to check: does a `BaseIO` extern's result get used directly (`case x` on the value) or
`.f[0]`-unwrapped? Is the monad's `pure` a one-field ctor or two? v4.30 **erased the RealWorld
token** and made IO results single-field `EST.Out.ok`/`.error`, so in `qed_rt.mjs`:

- `BaseIO` externs return their value directly (`ST.Prim.Ref` get/set/mkRef/take,
  `getStderr`/`getStdout`), **not** `mkOk(value, world)`.
- `mkOk`/`mkErr` are single-field.

If this is wrong the app builds and the gate passes (both are pure) but the live driver silently
takes a wrong branch on boot — so do this step deliberately.

## 5. Discover new/renamed runtime externs

The transpiled stdlib will reference externs the runtime doesn't implement yet. They are listed by
name at boot (the runtime's `assertExterns`) and by the differential gate:

```bash
node test/js_gate_test.mjs        # lists "missing externs: …" then 96/96 once implemented
```

Most are renames (`Array.mkArray` → `Array_replicate`) or thin scalars; the substantive batch is
whatever new String/`ByteArray` byte-API the version introduced. Add them to the
"v4.x stdlib externs" block in `qed_rt.mjs`. Watch the arity: an extern carrying a type-class
instance (e.g. `Array.get!Internal`'s `[Inhabited α]`) takes that instance as a real argument.

## 6. Validate

```bash
./qed check                 # proofs replay, axiom-clean, no sorry — the verification gate
node test/js_gate_test.mjs  # 96/96 — transpiled JS == native Lean
./qed test                  # the full browser suite (apps cover HTTP/streaming/ws/timers/SSR)
```

The gate is the contract: it pins the transpiled JavaScript to the native Lean semantics, so a
subtle IR mis-read shows up as a mismatch rather than a silent bug. When all three are green, the
bump is done.
