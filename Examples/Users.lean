import Qed
open Qed

namespace Users

router R where
  home => "/"
  user => "/users/:name"

schema Profile where
  name : String
  bio  : String

end Users

component Users where
  route : R := .home
  state query   := ""
  state focused := false
  query profile : Profile
    key := match route with | .user name => name | _ => ""
    url := fun name => s!"/api/users/{name}"

  action submit when !query.trimmed.isEmpty =>
    perform (Cmd.pushUrl (R.user query.trimmed))
  action key (k : String) =>
    if k == "Escape" then query := ""

  view =>
    <div class="app">
      <nav><a href={R.home} class="home-link">Home</a></nav>
      {match route with
       | .home =>
           <form class="search" onSubmit={.submit}>
             <input class={if focused then "q focused" else "q"} bind={query}
                    placeholder="Find a user…"
                    onFocus={focused := true} onBlur={focused := false} onKeydown={.key}/>
             <button class="go" type="submit">Search</button>
             <div class="hint">try <a href={R.user "ada"}>ada</a> or <a href={R.user "alan"}>alan</a></div>
           </form>
       | .user name =>
           <div class="profile">
             <h1>{name}</h1>
             <Await of={profile} as={prof} err={e}
               loading={<p class="loading">Loading…</p>}
               failed={<p class="error">Error: {e}</p>}>
               <p class="bio">{prof.bio}</p>
             </Await>
           </div>}
    </div>
