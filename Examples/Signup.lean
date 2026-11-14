import Qed
open Qed

namespace Signup

schema Account where
  email : String where email.contains '@', email.length ≥ 3
  age   : Nat    where age ≥ 18
  born  : Date
  agree : Bool   where agree
  plan  : select [("free", "Free"), ("pro", "Pro")]

structure Model where
  draft     : Account.Draft
  submitted : Option Account

inductive Msg
  | edit (d : Account.Draft)
  | submit

def update (m : Model) : Msg → Model
  | .edit d => { m with draft := d }
  | .submit => { m with submitted := Account.parse m.draft }

def app : App Model Msg :=
  ui { draft := Account.Draft.empty, submitted := none } update fun m =>
    <div class="app">
      <h1>Create account</h1>
      {Account.formView m.draft .edit .submit}
      {if let some acc := m.submitted then
        <p class="ok">Created account for {acc.email}</p>}
    </div>

end Signup
