import Qed
import Tests.ServerChecks

namespace WebEssentialsFixture

inductive TestRoute where
  | home | old | missing
deriving Inhabited, DecidableEq

instance : Qed.Router TestRoute where
  print
    | .home    => []
    | .old     => ["old"]
    | .missing => ["missing"]
  parse
    | []          => some .home
    | ["old"]     => some .old
    | ["missing"] => some .missing
    | _           => some .missing
  round_trip r := by cases r <;> rfl

def routedApp : Qed.App TestRoute TestRoute :=
  let base : Qed.App TestRoute TestRoute :=
    Qed.Internal.mkRoutedAppCore (R := TestRoute)
      .home
      (fun _ r => (r, .none))
      (Qed.V.el "main" [] [Qed.V.text "ok"])
      id
      (valid_view := fun _ => rfl)
  let withH := Qed.App.withHead (fun r =>
    match r with
    | .missing => { title := some "404 Not Found", description := some "Missing page" }
    | .old     => { title := some "Moved", canonical := some "/new" }
    | .home    =>
      {
        title := some "Home </title><script>alert(1)</script>"
        description := some "Verified \"SSR\" <head>"
        metaTags := [("og:type", "website")]
        canonical := some "https://example.com/"
      }) base
  Qed.App.withSsrStatus (fun r =>
    match r with
    | .missing => 404
    | .old     => 302
    | .home    => 200) withH

fullstack WebEssentialsApp:
  server ServerChecks.WebEssentialsSrv
  client routedApp
  title "Fallback Title"

end WebEssentialsFixture
