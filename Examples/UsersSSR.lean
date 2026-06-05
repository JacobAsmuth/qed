/-
  Dynamic per-request server-side rendering of the routed Users app.

  A request is a URL path (argv); this renders the *full page for that path* using the same
  verified `view`/router the browser runs — the route comes from `Router.fromURL`, and a user
  page's profile is filled from a server-side lookup (standing in for a database), so the bio
  is in the initial HTML with no client fetch. Each invocation handles one request, CGI-style;
  a front HTTP server (see `test/ssr_dynamic_test.mjs`) calls it per request. The browser then
  hydrates the result.
-/
import Examples.Users
open Qed

namespace Users

/-- Stand-in for the server's data source. -/
def serverProfiles : List (String × Profile) :=
  [ ("ada",  { name := "Ada",  bio := "Wrote the first algorithm." }),
    ("alan", { name := "Alan", bio := "Asked what machines can decide." }) ]

/-- The model for a request path: parse the route, and for a user page fill the profile
    from the server-side lookup (a real fetch would hit a DB here). -/
def modelFor (path : String) : Model :=
  let route : R := (Router.fromURL path).getD .home
  { init with
    route   := route
    profile := { state := match route with
      | .user name => match serverProfiles.lookup name with
                      | some p => .ok p
                      | none   => .failed "no such user"
      | _          => .idle } }

end Users

def main (args : List String) : IO Unit := do
  let path := args.head?.getD "/"
  IO.println (renderDocument s!"Users — {path}" (Users.app.renderModel (Users.modelFor path)))
