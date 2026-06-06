/-
  Dynamic per-request server-side rendering of the Bookshelf app.

  A request is a URL path (argv); this renders the full page for that path with the
  same verified `view`/router the browser runs. The route comes from `Router.fromURL`,
  and the page's data is filled from a server-side lookup (standing in for a database),
  so the catalog list and a book's detail are in the initial HTML with no client fetch.
  Each invocation handles one request, CGI-style; a front HTTP server calls it per request.
  The browser then hydrates the result.
-/
import Examples.Bookshelf
open Qed

namespace Bookshelf

/-- Build a seed `Book`, discharging each refinement on the literal value with `decide` —
    so an empty title or an out-of-range year would fail to compile, not at runtime. -/
def book (id title author : String) (year : Nat) (genre : String) (inPrint : Bool)
    (hTitle : NonEmpty title := by decide) (hAuthor : NonEmpty author := by decide)
    (hYear : Year year := by decide) : Book :=
  { id, title := ⟨title, hTitle⟩, author := ⟨author, hAuthor⟩, year := ⟨year, hYear⟩, genre, inPrint }

/-- Stand-in for the server's data source. -/
def serverBooks : List Book :=
  [ book "dune"        "Dune"                "Frank Herbert"      1965 "fiction"    true,
    book "neuromancer" "Neuromancer"         "William Gibson"     1984 "fiction"    true,
    book "geb"         "Gödel, Escher, Bach" "Douglas Hofstadter" 1979 "nonfiction" false ]

/-- The model for a request path: parse the route and fill its data server-side
    (a real server would hit a DB here). -/
def modelFor (path : String) : Model :=
  let route : R := (Router.fromURL path).getD .catalog
  { init with
    route   := route
    catalog := match route with | .catalog  => .ok serverBooks.toArray | _ => .idle
    current := match route with
      | .detail id => match serverBooks.find? (·.id == id) with
                      | some b => .ok b
                      | none   => .failed "no such book"
      | _          => .idle }

end Bookshelf

def main (args : List String) : IO Unit := do
  let path  := args.head?.getD "/"
  let model := Bookshelf.modelFor path
  -- embed the model as dehydrated state so the client starts from it (no flash, no refetch)
  IO.println (renderDocument s!"Bookshelf — {path}" (Bookshelf.app.renderModel model)
                (state := Bookshelf.app.dehydrate model))
