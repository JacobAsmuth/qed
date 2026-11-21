# Upgrading the Lean toolchain

Qed pins a single Lean version in `lean-toolchain`. Emitted `.mjs` bundles are plain JavaScript
with zero Lean runtime dependencies, so **deployed apps are unaffected**—only build-time tools
`Js/Backend.lean` and `Js/VerifyEnv.lean` read internal `Lean.IR` and `Lean.Environment` APIs
that can change across Lean releases.

Upgrading Lean is a bounded, fail-loud checklist: at almost every step, the compiler or test
gate tells you exactly what changed. Work on a branch and walk through the six steps below,
illustrated with concrete examples from the `v4.15` → `v4.30` upgrade.

## 1. Update `lean-toolchain`

```bash
echo "leanprover/lean4:vX.Y.0" > lean-toolchain
elan toolchain install leanprover/lean4:vX.Y.0
```

Qed has no external Lake package dependencies—`lake-manifest.json` is empty—so there are no
third-party libraries to co-upgrade.

## 2. Build the framework with `lake build Qed`

This surfaces `Init` and `Std` renames, deprecations, and tactic changes across
`Qed/`. Compiler errors and deprecation warnings usually suggest the replacement directly.

Examples from `v4.15` → `v4.30`:

- **Renames:** `String.mk` → `String.ofList`, `String.data` → `String.toList`, and
  `Array.mkArray` → `Array.replicate`.
- **`String` representation:** `String` switched to UTF-8 `ByteArray` backing, so anonymous
  constructors `⟨chars⟩ : String` now resolve to `String.ofByteArray`; use `String.ofList`
  and `String.toList_ofList` in proofs instead.
- **Implicit arguments:** stdlib lemmas like `List.not_mem_nil` and `List.mem_cons_self` made
  previously explicit arguments implicit.
- **Tactic strictness:** `simp` no longer splits `if` expressions automatically—add `split`—and
  the `unusedSimpArgs` linter flags redundant entries in `simp only [...]`.

## 3. Build the JS compiler with `lake build qedjs`

This surfaces internal changes in `Lean.IR` and `Lean.Environment` across
[`Js/Backend.lean`](../Js/Backend.lean), [`Js/VerifyEnv.lean`](../Js/VerifyEnv.lean), and
[`Js/Main.lean`](../Js/Main.lean). Because IR lowering matches exhaustively over `FnBody`,
`Expr`, and `Arg`, added or removed constructors fail immediately at compile time.

Examples from `v4.15` → `v4.30`:

- `Lean.IR.Arg.irrelevant` → `Arg.erased`, and `Lean.IR.IRType.isIrrelevant` → `isErased`.
- `Lean.IR.FnBody.mdata` was removed; drop the obsolete match arm.
- `List.enum` → `List.zipIdx`, with tuple order flipped from `(i, a)` to `(a, i)`.
- `Lean.Import` gained fields `importAll`, `isExported`, and `isMeta`; construct it with
  `{ module := … }` so new fields pick up their defaults.

## 4. Verify the runtime `IO` convention in `runtime/qed_rt.mjs`

This is the one step that is **semantic rather than a compile error**, so check it deliberately.
Inspect the lowered IR of a tiny `IO` function to confirm how the new Lean release represents
`BaseIO` and `IO` return values:

- Does a `BaseIO` primitive like `ST.Prim.Ref.get`, `mkRef`, `set`, `take`, or `getStdout` return its
  value directly, or wrapped in a constructor?
- Does `EST.Out.ok` / `.error` carry one field for the value or error alone, or two with a world
  token?

In `v4.30`, Lean **erased the `RealWorld` token**, making `EST.Out.ok` and `.error` single-field
constructors and causing `BaseIO` externs to return raw values directly rather than
`mkOk(value, world)`. If `runtime/qed_rt.mjs` disagrees with this convention, pure builds and
pure tests will still pass while the live browser driver misreads `IO` results on boot.

## 5. Implement any new stdlib externs

When Lean's standard library introduces or renames `@[extern]` functions used by reachable code,
`qed check` reports their exact names via `qedjs --check-externs`:

```bash
./scripts/qed check   # reports "missing externs: …" until all are implemented
```

Add missing primitives to the stdlib externs section of [`runtime/qed_rt.mjs`](../runtime/qed_rt.mjs).
Most are simple renames like `Array_replicate` or byte and string helpers like
`ByteArray_get`. Check parameter arity carefully: externs with a typeclass constraint—like
`Array.get!Internal`'s `[Inhabited α]`—receive that instance as a runtime parameter unless Lean
erased it.

## 6. Run the full verification suite

```bash
./scripts/qed check   # Lean proofs, VerifyEnv gate, extern coverage, and axiom manifest
./scripts/qed test    # native test suites: CLI scaffold, fullstack RPC, databases, WebSockets
```

Once both commands pass cleanly, the toolchain upgrade is complete.
