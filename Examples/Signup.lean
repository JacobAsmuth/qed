/-
  A form across HTML input types, with "submit ⇔ valid" by construction.

  `schema Account` generates the editable `Account.Draft` (raw strings), the validated
  `Account` (each refined field a proof-carrying `Field`), `Account.parse`, the
  `canSubmit` gate + its `canSubmit_iff` proof, and `Account.formView` (the widgets). The app
  holds a draft, replaces it on every edit, and on submit stores the parsed
  `Option Account` — which is `some` only when every field validates. The submit
  button `formView` renders is disabled unless the draft parses, so it cannot fire
  on invalid data.
-/
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
  | edit (d : Account.Draft)   -- the form hands back the whole updated draft
  | submit

def update (m : Model) : Msg → Model
  | .edit d => { m with draft := d }
  | .submit => { m with submitted := Account.parse m.draft }

def app : App Model Msg :=
  ui { draft := Account.Draft.empty, submitted := none } update fun m =>
    div [cls "app"] [
      h1 [] ["Create account"],
      Account.formView m.draft .edit .submit,
      match m.submitted with
      | some acc => p [cls "ok"] ["Created account for ", acc.email.val]
      | none     => .text ""
    ]

end Signup
