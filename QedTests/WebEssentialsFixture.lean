import Qed

namespace WebEssentialsFixture
-- Keep client component before `server` so Lean closed-term CSE cannot point client literals at `WebEssentialsSrv.*._closed_*`.
inductive TestRoute where | home | old | missing deriving Inhabited, DecidableEq
instance : Qed.Router TestRoute where
  print | .home => [] | .old => ["old"] | .missing => ["missing"]
  parse | [] => some .home | ["old"] => some .old | _ => some .missing
  round_trip r := by cases r <;> rfl
component RoutedSite:
  route : TestRoute = .home
  head:
    case .home:
      title       "Home </title><script>alert(1)</script>"
      description "Verified \"SSR\" <head>"
      canonical   "https://example.com/"
      meta        "og:type", "website"
    case .old:
      title       "Moved"
      redirect    "/new"
    case .missing:
      status      404
      title       "404 Not Found"
      description "Missing page"
  view: <main>ok</main>
server WebEssentialsSrv:
  state hits : Nat = 0
  invariant hitsBounded: hits <= 1000
  rpc login(token: String) -> String:
    setCookie("qed_session", token)
    return "ok"
  get "/robots.txt": return text("User-agent: *\nAllow: /\n")
  post "/webhook":
    requires ctx.isAuthenticated
    atomic: if hits < 1000: hits += 1
    setCookie("wh_seen", "1")
    return json({ ok = true })
  post "/echo-cookie":
    atomic: if hits < 1000: hits += 1
    setCookie("echo_ck", ctx.body)
    return json({ ok = true })
  get "/stats": return json({ ok = true, hits = hits })
  get "/hits": return json(hits)
  stream "/events":
    send("hello", event = "greeting", id = "1")
    send("world")
fullstack WebEssentialsApp:
  server WebEssentialsSrv
  client RoutedSite
  title "Fallback Title"

end WebEssentialsFixture
