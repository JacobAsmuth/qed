import Qed

namespace Qed
router Route:
  home = ""
  about
  post(slug: String) = "posts"
  user(name: String) = "users"
router TypedRoute:
  page(n: Nat) = "page"
  delta(i: Int) = "delta"
  item(slug: String, n: Nat) = "items"
namespace Demo
schema Signup:
  email : String where '@' in email, email.length >= 3
  age   : Nat    where age >= 18
  agree : Bool   where agree
end Demo
end Qed
