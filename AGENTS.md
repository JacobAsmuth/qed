# Qed Engineering & Anti-Bloat Rules

## 1. Anti-Bloat Development Process (Required on Every Feature)

### Before Writing Code: Search-First Reuse Check
- Before adding any local helper, parser, codec, validator, HTTP/JSON/SQL utility, or test harness helper, search the relevant core modules and sibling files to see what already exists.
- If a helper is missing from the lowest shared layer but needed across 2+ modules, lift a clean general primitive there rather than defining private copies in each caller.
- **Rule of Two**: When adding a second similar flow, protocol, proof, or check, parameterize or table-drive the first instead of copying and mutating it.
- **Avoid sprawl**: Do not create a new `.lean` file or single-use wrapper struct unless module boundaries (such as pure vs `import Lean` separation) require it. Every extra `import Lean` module adds clean-build overhead.
- **Tests**: Reuse shared test macros and harness utilities; prefer table-driven test arrays/loops over copy-pasted test blocks or giant `&&` chains, without weakening coverage or assertions.

### Before Finishing Any Non-Trivial Feature: Self-Compaction Pass
Once tests pass and before replying to the user, run a dedicated self-review on your `git diff` (use the `self-compact` skill for multi-file or >100-LOC changes):
1. **Deduplicate**: Collapse repeated branches, retry/polling loops, serialization plumbing, or proof cases into shared helpers or data tables.
2. **Prune dead code**: Remove any zero-caller helpers, lemmas, struct fields, imports, or superseded paths introduced or orphaned by your edits.
3. **Verify zero regressions**: Confirm correctness, axioms, runtime perf, and build times all stay green after compacting.

## 2. Lean 4, Rust & JS Performance / Build-Time Guardrails
- **No eager monadic lifts**: Never write `cond && (← act)`, `cond || (← act)`, or `.getD (← act)` in `do` blocks. Lean 4 lifts `(← act)` eagerly before evaluating `&&`/`||`/`getD`. Always short-circuit with nested `if`, `match`, or lazy short-circuit helpers.
- **Hot loops (RC=1 & kernel gate)**:
  - Never pass closure callbacks that capture a `HashSet`/accumulator inside hot loops (breaks RC=1 in-place updates). Use a closure-free mode `inductive` instead.
  - Avoid `while` loops with many `let mut` variables on hot paths (allocates right-nested `Prod` spines per iteration) or in `qedjs --verify-env`-checked modules (emits `Lean.Loop.forIn` symbols that can fail the kernel gate via closed-term CSE). Use tail-recursive fuel/index helpers instead.
- **Elaborator compile speed**: Mark polymorphic `{M}` and quotation-heavy elaborator helpers `@[noinline, nospecialize]` or `@[noinline]` to prevent LCNF specialization blowups.
- **Fast proofs**: Never trade build time for LOC via heavy `simp [*]`, slow `grind`, or giant `decide`. Prefer bundled context structs, `section`/`variable` binders, small structural lemmas, targeted `simp only`, or direct term proofs.
- **Pure module boundaries**: Respect build-graph isolation enforced by `./scripts/qed check` (pure modules must never transitively import `Lean`; keep `@[export]` and `@[extern]`/`opaque` declarations in their designated runtime/FFI modules).
- **JS runtime V8 ICs**: Keep BigInt and Number arithmetic helpers monomorphic (never mix BigInt and Number in the same hot arithmetic function) and preserve exported runtime symbols/contracts checked by `qed check` and tests.

## 3. Repository Hygiene & Verification Gates
- **No em/en dashes**: Never use U+2014 or U+2013 in repository files; use colons, commas, or periods.
- **Do not weaken gates**: Keep benchmarks, `scripts/axioms.lean` (zero `sorry`, zero unexpected axioms), and all test assertions intact.
- **Verification commands**: Run `./scripts/qed check`, `lake env lean scripts/axioms.lean`, `cargo test --manifest-path rust/qed_server/Cargo.toml`, and `./scripts/qed test` after substantive changes.

## 4. Language & Syntax Design
Keep Qed's surface language simple, flexible, and readable whenever adding or modifying grammar, parsers, or DSL clauses:
- **Avoid new keywords**: Exhaust existing Qed keywords and constructs before minting a new one. Reuse the same keyword in a new block/context (for example `fn` inside `database` instead of `policy_fn`) when the concept is the same.
- **Keep keywords consistent across contexts**: Before designing any new clause, inspect existing parsers (`Qed/Lang.lean`, `Qed/Schema.lean`, `Qed/Component/Syntax.lean`, `Qed/Server/Syntax.lean`, `Qed/Server/Db/Elab.lean`) so shared concepts (`fn`, `example`, `rejects`, `invariant`, `requires`, `with`, etc.) follow a uniform shape everywhere.
- **Avoid keyword chains at all costs**: Never stack multi-word keyword prefixes (like `example policy read ...`) just to simplify parsing or disambiguation. Use flat, concise syntax (like `example read ...:`) and let the parser handle disambiguation cleanly.
- **Prefer simple, composable primitives**: Favor orthogonal, readable forms over special-case grammar. If a syntax feels noisy or redundant when read aloud, simplify it and align with the user before implementing.
