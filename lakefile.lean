import Lake
open Lake DSL

package qed where
  -- WASM is built by `scripts/build_wasm.sh`, which compiles the C generated
  -- here and links it against the prebuilt Lean `linux_wasm32` runtime.

@[default_target]
lean_lib Qed where

/-- The Lean-IR → JavaScript transpiler (build-time tool; `import Lean`, never shipped). -/
lean_lib Js where

/-- The transpiler CLI: `lake exe qedjs <out.mjs> <module>… -- <decl>[:<export>]…`. -/
lean_exe qedjs where
  root := `Js.Main
  supportInterpreter := true

/-- The example modules (shared app + the two entry points). Grouping them in a
    library lets lake build `Examples.Counter` as a dependency of both entries. -/
lean_lib Examples where
  globs := #[.submodules `Examples]

/-- The counter demo as a *native* program: pure Lean, total `update`/`view`, an
    auto-proven invariant. `lake exe counter` renders it to static HTML (sanity).
    Uses no DOM externs, so it links natively. -/
lean_exe counter where
  root := `Examples.Native

/-- The counter demo as the *WASM* entry point. Declared so the build script can
    generate its C via the `:c.o` facet; it is never linked as a native binary
    (it references the browser-only DOM externs). -/
lean_exe web where
  root := `Examples.Web

/-- The `qed` CLI. Drive it via the `./qed` shim, which sets up the environment
    and runs this binary. -/
lean_exe qed where
  root := `Cli

/-- Native performance benchmarks for the rebuild + diff pipeline. `lake exe bench`.
    Pure Lean (no DOM externs), so it links natively. -/
lean_exe bench where
  root := `Examples.Bench

/-- Dynamic per-request SSR of the Users app: `lake exe users_ssr <path>` prints the full
    page for that route, profile filled server-side. A front server calls it per request. -/
lean_exe users_ssr where
  root := `Examples.UsersSSR

/-- SSR of the `view%` template demo's initial view, for the template-hydration test. -/
lean_exe template_ssr where
  root := `Examples.TemplateSSR

/-- Dynamic per-request SSR of the Bookshelf app: `lake exe bookshelf_ssr <path>` prints the
    full page for that route, its catalog/detail data filled server-side. -/
lean_exe bookshelf_ssr where
  root := `Examples.BookshelfSSR
