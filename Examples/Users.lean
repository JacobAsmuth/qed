/-
  A URL-routed app: HTTP fetch + decode, the verified router wired to the browser,
  and the form/keyboard/focus events.

  Two pages, a search home and a user profile. The router round-trips URLs *by
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
schema Profile where
  name : Codec.text
  bio  : Codec.text

structure Model where
  route   : R
  query   : String
  profile : Cached Profile   -- the fetched profile (SWR cache), keyed on the username
  focused : Bool

def init : Model := { route := .home, query := "", profile := {}, focused := false }

inductive Msg where
  | routed (r : R)                                -- the URL changed (startup/link/back/push), parsed
  | typeQuery (s : String)
  | submit                                        -- run the search → navigate
  | gotProfile (key : String) (r : Resource Profile)   -- a fetch resolved, tagged with its issued key
  | focus
  | blur
  | key (k : String)

-- The username the profile depends on, defined once, used by both the query and the result arm.
def userKey (m : Model) : String := match m.route with | .user name => name | _ => ""

-- The transition just sets state. The profile is not flipped to `loading` or fetched here, it
-- auto-refetches whenever `userKey` changes (see `profileQuery`). The result arm folds the response
-- into the cache via `put`, which drops it if the user has already navigated to a different name.
def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .routed route => { m with route }
  | .typeQuery s  => { m with query := s }
  | .submit       => if m.query.trimmed.isEmpty then m
                     else (m, .pushUrl (Router.toURL (R.user m.query.trimmed)))
  | .gotProfile k r => { m with profile := m.profile.put k r (userKey m) }
  | .focus        => { m with focused := true }
  | .blur         => { m with focused := false }
  | .key k        => if k == "Escape" then { m with query := "" } else m

-- The profile depends on the route's username. On a change the framework shows the cached value
-- (revalidating) or `.loading` and refetches `/api/users/<name>`; on a non-user page (empty key) it
-- clears to `.idle`. The initial deep-link fetch fires too, the URL dispatch takes the key "" → name.
def profileQuery : Query Model Msg :=
  Resource.query
    (key := userKey)
    (url := fun name => s!"/api/users/{name}")
    (got := Msg.gotProfile)
    (get := fun m => m.profile) (set := fun c m => { m with profile := c })

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) (queries := [profileQuery]) fun m =>
    div [cls "app"] [
      nav [] [ linkTo R.home [cls "home-link"] "Home" ],
      match m.route with
      | .home =>
          formEl [cls "search", onSubmit .submit] [
            input [cls (if m.focused then "q focused" else "q"), value m.query,
                   placeholder "Find a user…",
                   onInput .typeQuery, onFocus .focus, onBlur .blur, onKeydown .key],
            button [cls "go", type' "submit"] "Search",
            div [cls "hint"] [ "try ", linkTo (R.user "ada") [] "ada", " or ", linkTo (R.user "alan") [] "alan" ]
          ]
      | .user name =>
          div [cls "profile"] [
            h1 [] [name],
            m.profile.view (fun prof => p [cls "bio"] [prof.bio])
              (loading := p [cls "loading"] ["Loading…"])
              (failed  := fun e => p [cls "error"] ["Error: ", e])
          ]
    ]

end Users
