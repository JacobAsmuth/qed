import Qed
import Tests.ServerChecks

namespace WebEssentialsFixture

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

fullstack WebEssentialsApp:
  server ServerChecks.WebEssentialsSrv
  client RoutedSite
  title "Fallback Title"

end WebEssentialsFixture
