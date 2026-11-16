import Qed
open Qed

schema Account where
  email : String where email.contains '@', email.length ≥ 3
  age   : Nat    where age ≥ 18
  born  : Date
  agree : Bool   where agree
  plan  : select [("free", "Free"), ("pro", "Pro")]

component Signup where
  state draft                     := Account.Draft.empty
  state submitted : Option Account := none
  action submit => submitted := Account.parse draft
  view =>
    <div class="app">
      <h1>Create account</h1>
      <Account.Form bind={draft} onSubmit={.submit}/>
      {if let some acc := submitted then
        <p class="ok">Created account for {acc.email}</p>}
    </div>
