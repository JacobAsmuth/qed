import Qed
open Qed

namespace Signup

abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

schema Account where
  email : Codec.text.refine Email
  age   : Codec.nat.refine Adult
  born  : Codec.date
  agree : Codec.checkbox.refine (· = true)
  plan  : Codec.select [("free", "Free"), ("pro", "Pro")]

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
      {match m.submitted with
       | some acc => <p class="ok">Created account for {text acc.email}</p>
       | none     => .text ""}
    </div>

end Signup
