---
name: self-compact
description: >-
  Run a post-feature self-reflection, deduplication, dead-code pruning, and
  performance/build-time hygiene pass before finalizing non-trivial changes.
  Activate after tests pass on any feature adding >100 LOC, touching multiple
  files, or when the user asks to review, simplify, or trim code.
---

# Post-Feature Self-Compaction Review

Switch hats from "make the feature work" to "make the diff as small, unified,
and fast as possible without losing coverage or readability."

## Step 1: Snapshot Your Diff
1. Run `git diff --stat` and list any new untracked files.
2. Note current line counts of every touched/added file and current timing of
   `./scripts/qed check` (or single-file `lake env lean` on modified modules).

## Step 2: Cross-File Reuse & Duplication Audit
Read your entire diff critically and answer:
1. **Did I reinvent an existing primitive?** For every new helper, parser,
   validator, codec, HTTP/JSON/SQL wrapper, or test utility in your diff,
   search (`rg`) the owning subsystem's core module and shared test harness
   for equivalent functionality. Reuse existing primitives, or lift a clean
   shared helper when 2+ modules need it.
2. **Did I copy-paste a pattern twice (Rule of Two)?** Look for parallel
   pipelines, duplicated retry/polling/HTTP/JSON/SQL loops, mirrored proof
   branches, or repeated test fixtures. Parameterize or table-drive them.
3. **Did I add an unnecessary file or single-use wrapper?** Merge thin new
   files into an existing module unless pure-vs-meta import boundaries require
   separation. Inline or delete single-use wrapper structs and 1-line
   delegators.

## Step 3: Dead Code & Boilerplate Pruning
1. Check every new or modified private helper, lemma, struct field, and import
   for actual callers (`rg` across the repo). Delete anything with 0 callers.
2. Check whether any old helper, field, or code path became orphaned by your
   change and remove it.
3. In Lean proofs and elaborators: factor repeated context arguments into
   `section`/`variable` or a small context `structure`, replace repetitive
   mechanical declarations with a compact pure-`Init` macro, and replace
   copy-pasted test blocks with table-driven loops or shared test macros.
4. Do NOT obfuscate or drop test assertions, edge cases, or error diagnostics.

## Step 4: Static Pitfall & Performance Audit
Run quick scans across your modified files:
1. **Eager monadic lifts in Lean** (must be 0 unintended hits):
   ```bash
   rg -n '(&&|\|\||\.getD)\s*\(?\s*←' <modified .lean files>
   ```
2. **Hot-path traps**:
   - Check new Lean loops for closure callbacks over `HashSet`/accumulators
     (replace with closure-free enum dispatch) or multi-`let mut` `while` loops
     (replace with tail-recursive fuel/index loops).
   - Check new quotation-heavy or polymorphic `{M}` elaborators with
     `lake env lean -Dtrace.profiler=true <file>` if compilation feels slow;
     add `@[noinline, nospecialize]` where LCNF specialization dominates.
   - Confirm no heavy `simp [*]`, slow `grind`, or large `decide` slowed down
     elaboration.
3. **Repo hygiene**:
   - Verify 0 `sorry`/`admit`/`native_decide`/`sorryAx` in modified `.lean`
     files.
   - Verify 0 em/en dashes (`rg -nP '[\x{2014}\x{2013}]' <modified files>`).
   - In `Tests/`, ensure string literals passed to the forbidden-token scanner
     contain `\n` so single-line custom-token scanning does not index them.

## Step 5: Non-Regression Verification Gate
Re-run the relevant checks and compare against Step 1:
- `lake build` (0 errors, 0 warnings)
- `./scripts/qed check`
- `lake env lean scripts/axioms.lean`
- `cargo test --manifest-path rust/qed_server/Cargo.toml` (if Rust touched)
- `./scripts/qed test` (for runtime/server/CLI/cloud changes)

Never keep a LOC reduction that regresses runtime performance, build time,
test coverage, or axiom cleanliness.
