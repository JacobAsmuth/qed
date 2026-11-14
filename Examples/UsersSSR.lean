import Examples.Users
open Qed

namespace Users

def serverProfiles : List (String × Profile) :=
  [ ("ada",  { name := "Ada",  bio := "Wrote the first algorithm." }),
    ("alan", { name := "Alan", bio := "Asked what machines can decide." }) ]

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
