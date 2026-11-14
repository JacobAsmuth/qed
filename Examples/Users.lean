import Qed
open Qed

namespace Users

router R where
  home => "/"
  user => "/users/:name"

schema Profile where
  name : String
  bio  : String

structure Model where
  route   : R
  query   : String
  profile : Cached Profile
  focused : Bool

def init : Model := { route := .home, query := "", profile := {}, focused := false }

inductive Msg where
  | routed (r : R)
  | typeQuery (s : String)
  | submit
  | gotProfile (key : String) (r : Resource Profile)
  | focus
  | blur
  | key (k : String)

def userKey (m : Model) : String := match m.route with | .user name => name | _ => ""

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .routed route   => { m with route }
  | .typeQuery s    => { m with query := s }
  | .submit         => if m.query.trimmed.isEmpty then m
                       else (m, .pushUrl (R.user m.query.trimmed))
  | .gotProfile k r => { m with profile := m.profile.put k r (userKey m) }
  | .focus          => { m with focused := true }
  | .blur           => { m with focused := false }
  | .key k          => if k == "Escape" then { m with query := "" } else m

def profileQuery : Query Model Msg :=
  Resource.queryFor profile
    (key := userKey)
    (url := fun name => s!"/api/users/{name}")
    (got := Msg.gotProfile)

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) (queries := [profileQuery]) fun m =>
    <div class="app">
      <nav><a href={R.home} class="home-link">Home</a></nav>
      {match m.route with
       | .home =>
           <form class="search" onSubmit={.submit}>
             <input class={if m.focused then "q focused" else "q"} value={m.query}
                    placeholder="Find a user…"
                    onInput={.typeQuery} onFocus={.focus} onBlur={.blur} onKeydown={.key}/>
             <button class="go" type="submit">Search</button>
             <div class="hint">try <a href={R.user "ada"}>ada</a> or <a href={R.user "alan"}>alan</a></div>
           </form>
       | .user name =>
           <div class="profile">
             <h1>{name}</h1>
             {m.profile.view (fun prof => <p class="bio">{prof.bio}</p>)
               (loading := <p class="loading">Loading…</p>)
               (failed  := fun e => <p class="error">Error: {e}</p>)}
           </div>}
    </div>

end Users
