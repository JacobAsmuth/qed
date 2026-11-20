import Qed
open Qed

namespace BenchServer

router R:
  home = "/"

schema Fortune:
  id      : Nat
  message : String

/-- Classic 12 TechEmpower Fortunes rows (including XSS and UTF-8 payloads). -/
def baseFortunes : Array Fortune := #[
  { id := 1,  message := "fortune: No such file or directory" },
  { id := 2,  message := "A computer scientist is someone who fixes things that aren't broken." },
  { id := 3,  message := "After enough decimal places, nobody gives a damn." },
  { id := 4,  message := "A bad random number generator: 1, 1, 1, 1, 1, 4.33e+67, 1, 1, 1" },
  { id := 5,  message := "A computer program does what you tell it to do, not what you want it to do." },
  { id := 6,  message := "Emacs is a nice operating system, but I prefer UNIX. — Tom Christaensen" },
  { id := 7,  message := "Any program that runs right is obsolete." },
  { id := 8,  message := "A list is only as strong as its weakest link. — Donald Knuth" },
  { id := 9,  message := "Feature: A bug with seniority." },
  { id := 10, message := "Computers make very fast, very accurate mistakes." },
  { id := 11, message := "<script>alert(\"This should not be displayed in a browser alert box.\");</script>" },
  { id := 12, message := "フレームワークのベンチマーク" }
]

def sortedFortunes (extra : String := "Additional fortune added at request time.") : Array Fortune :=
  (baseFortunes.push { id := 0, message := extra }).qsort
    (fun a b => a.message < b.message)

server BenchSrv:
  def ping(msg: String) -> String:
    return msg

  def fortunes() -> Fortune[]:
    return sortedFortunes("Additional fortune added at request time.")

  def broadcast(msg: String) -> Unit:
    feed.emit(msg)
    return ()

  channel feed() -> String:
    on_join:
      pass
    on_send(msg: String):
      feed.emit(msg)
    on_leave:
      pass

component BenchPage:
  route : R = .home:
    case .home:
      fortunes = await BenchSrv.fortunes()
  state fortunes : Resource Fortune[]
  view:
    <div>
      <h1>Fortunes</h1>
      <Await of={fortunes} as={rows} err={e}
        loading={<p>Loading…</p>}
        failed={<p>{e}</p>}>
        <table>
          <thead><tr><th>id</th><th>message</th></tr></thead>
          <tbody>{for f in rows:
            <tr key={toString(f.id)}><td>{toString(f.id)}</td><td>{f.message}</td></tr>}</tbody>
        </table>
      </Await>
    </div>

fullstack App:
  server BenchSrv
  client BenchPage
  title "Fortunes"

end BenchServer
