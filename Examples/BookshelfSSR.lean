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

/-- Stand-in for the server's data source. -/
def serverBooks : List Book :=
  [ { id := "dune",        title := "Dune",                author := "Frank Herbert",      year := 1965, genre := "fiction",    inPrint := true },
    { id := "neuromancer", title := "Neuromancer",         author := "William Gibson",     year := 1984, genre := "fiction",    inPrint := true },
    { id := "geb",         title := "Gödel, Escher, Bach", author := "Douglas Hofstadter", year := 1979, genre := "nonfiction", inPrint := false } ]

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
  let path := args.head?.getD "/"
  IO.println (renderDocument s!"Bookshelf — {path}" (Bookshelf.app.renderModel (Bookshelf.modelFor path)))
