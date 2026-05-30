/-
  A URL-routed app: HTTP fetch + decode, the verified router wired to the browser,
  and the form/keyboard/focus events.

  Two pages — a search home and a user profile. The router round-trips URLs *by
  proof* (`R.round_trip`); navigation goes through `link` / `Cmd.pushUrl`, so it
  never reloads the page. Visiting `/users/<name>` fetches `/api/users/<name>` and
  decodes the JSON with the verified `Qed.Json`. Submitting the search runs through
  `onSubmit` (Enter or the button, reload suppressed), Escape clears it
  (`onKeydown`), and the box highlights while focused (`onFocus`/`onBlur`).

  Pure Lean, total by construction; the browser entry is `Examples/UsersWeb.lean`.
-/
import Qed
open Qed

namespace Users

-- The pages, with a lawful `Router` instance generated alongside.
router R where
  home => ""
  user (name : String) => "users"

-- One profile, decoded from the API response.
jsonStruct Profile where
  name : String
  bio  : String

structure Model where
  route   : R
  query   : String
  profile : Option (Except String Profile)   -- the fetched profile on a user page
  focused : Bool

def init : Model := { route := .home, query := "", profile := none, focused := false }

inductive Msg where
  | urlChanged (path : String)               -- the URL changed (startup/link/back/push)
  | typeQuery (s : String)
  | submit                                   -- run the search → navigate
  | gotProfile (res : Except String Profile) -- the fetch resolved
  | focus
  | blur
  | key (k : String)

def update (m : Model) : Msg → Model
  | .urlChanged path =>
      let route : R := (Router.fromURL path).getD .home
      -- entering a user page clears the old profile; `effects` refetches
      { m with route, profile := match route with | .user _ => none | _ => m.profile }
  | .typeQuery s    => { m with query := s }
  | .submit         => m                     -- navigation is the effect below
  | .gotProfile res => { m with profile := some res }
  | .focus          => { m with focused := true }
  | .blur           => { m with focused := false }
  | .key k          => if k == "Escape" then { m with query := "" } else m

def effects (m : Model) : Msg → Cmd Msg
  | .submit =>
      if m.query.trim.isEmpty then .none
      else .pushUrl (Router.toURL (R.user m.query.trim))
  | .urlChanged _ =>
      match m.route with
      | .user name => Cmd.getJson s!"/api/users/{name}"
                        (fun p => .gotProfile (.ok p)) (fun e => .gotProfile (.error e))
      | _          => .none
  | _ => .none

def view (m : Model) : Html Msg :=
  div [cls "app"] [
    nav [] [ link "/" [cls "home-link"] "Home" ],
    match m.route with
    | .home =>
        formEl [cls "search", onSubmit .submit] [
          input [cls (if m.focused then "q focused" else "q"), value m.query,
                 placeholder "Find a user…",
                 onInput .typeQuery, onFocus .focus, onBlur .blur, onKeydown .key],
          button [cls "go", type' "submit"] "Search",
          div [cls "hint"] [ "try ", link "/users/ada" [] "ada", " or ", link "/users/alan" [] "alan" ]
        ]
    | .user name =>
        div [cls "profile"] [
          h1 [] [name],
          match m.profile with
          | none            => p [cls "loading"] ["Loading…"]
          | some (.ok prof) => p [cls "bio"] [prof.bio]
          | some (.error e) => p [cls "error"] ["Error: ", e]
        ]
  ]

def app : App Model Msg :=
  routed init update view (onUrlChange := Msg.urlChanged) (effects := effects)

end Users
