import Qed
open Qed

schema Account:
  email : String where '@' in email, email.length >= 3
  age   : Nat    where age >= 18
  born  : Date
  agree : Bool   where agree
  plan  : select([("free", "Free"), ("pro", "Pro")])

component Signup:
  state submitted : Account?
  view:
    <div class="app">
      <h1>Create account</h1>
      <Account.Form reset onSubmit={submitted = some(_)}/>
      {if let some(acc) = submitted:
        <p class="ok">Created account for {acc.email}</p>}
    </div>
