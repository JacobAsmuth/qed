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
  note  : String?
enum FixturePhase:
  lobby
  playing
enum FixtureRole:
  none
  agent(name: String, extra: String?)
schema FixtureRoom:
  code  : String
  phase : FixturePhase = .lobby
  spies : Nat          = 1 where 1 <= spies <= 4
  role  : FixtureRole? = none
style fixtureContrastBtn contrast >= 4.5:
  color: #ffffff
  background-color: #15694b
theorem fixture_codecs_sound (p : FixturePhase) (r : FixtureRole) (rm : FixtureRoom) (s : Signup) :
    Proto.decode (Proto.encode p) = .ok p ∧
    fromJson (toJson p) = .ok p ∧
    Proto.decode (Proto.encode r) = .ok r ∧
    fromJson (toJson r) = .ok r ∧
    Proto.decode (Proto.encode rm) = .ok rm ∧
    fromJson (toJson rm) = .ok rm ∧
    fromJson (toJson s) = .ok s :=
  ⟨Proto.decode_encode p, LawfulJson.fromJson_toJson p,
   Proto.decode_encode r, LawfulJson.fromJson_toJson r,
   Proto.decode_encode rm, LawfulJson.fromJson_toJson rm,
   LawfulJson.fromJson_toJson s⟩

schema FixtureSecret:
  code   : String
  secret : String
  spies  : String[]

schema FixtureRedacted:
  code   : String
  secret : String?

fn fixtureProject(room: FixtureSecret, viewerId: String) -> FixtureRedacted:
  if viewerId in room.spies:
    ensures result.secret == none
    blindTo room.secret
  let isSpy = viewerId in room.spies
  return { code = room.code, secret = none if isSpy else some(room.secret) }

component FixtureCompFn:
  state active : Bool = false
  state label  : String = ""
  fn clear():
    active = false
    label = ""
  action reset:
    clear()
  action activate(s: String):
    active = true
    label = s
  invariant inactiveClean: not active -> label == ""
  view: <span>{label}</span>
end Demo
end Qed
