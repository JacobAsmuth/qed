import Qed
import Qed.Driver
open Qed

namespace JsGate
router GateR:
  home = ""
  user(name: String) = "users"
schema ProtoRec:
  id  : String where 1 <= id.length <= 32
  qty : Nat    where qty <= 500
  raw : Bytes

private inductive GateTag where
  | a | b | c | d | e | f | g | h | n (v : Nat) | s (v : String)
  deriving BEq, Ord

private def protoRT {α : Type} [ToProto α] [FromProto α] (a : α) (eq : α → α → Bool) : String :=
  let bs := Proto.encode a; s!"{Proto.encodeHex bs}|{match Proto.decode (α := α) bs with | .ok b => eq a b | .error _ => false}"
private def tailSumAcc : Nat → Nat → Nat | 0, acc => acc | k + 1, acc => tailSumAcc k (acc + k + 1)

/-- Static Lean-IR extern-coverage & reachability surface compiled by `qedjs --check-externs`. -/
def run (probe i : Nat) : String :=
  let (t, e) := (Html.text, Html.element)
  match probe with
  | 0 =>
      let tree := e "div" [.cls "a", .attr "id" "x", .flag "disabled" true, .on "click" (), .onValue "input" (fun _ => ()), .signalBind "s1", .signalAttr "s2" "data-x" "v"]
        [t "hi & <bye> \"q\" café 日本語 😀", e "style" [] [t "a < b </style>"], e "script" [] [t "a < b"],
         e "ul" [] [e "li" [.key "1"] [t "a"], e "li" [.key "2"] [t "b"]], Qed.lazy (fun s : String => e "p" [.cls "m"] [t s]) "memo"]
      let next := e "div" [.cls "b"] [e "ul" [] [e "li" [.key "2"] [t "b"], e "li" [.key "1"] [t "c"]]]
      let patched := applyChildrenTR #[t "p"] [.create (t "n"), .reuse 0 (.patchElement [.cls "x"] [.reuse 0 (.setText "0")])] #[e "span" [] [t "0"]]
      let (rnd, hs) := renderNode #[777] (Html.element "main" [] [Html.element "button" [.on "click" i, .attr "title" "<&\""] [Html.text s!"row {i}"]])
      let ki := ((validatedKeyIndex [e "div" [.key "a"] []]).bind (·["a"]?)).map toString |>.getD "none"
      s!"{Html.render tree}|{Html.render (applyPatch (diff tree next) tree)}|{patched.size}|{rnd}|{hs.size}|{ki}"
  | 1 =>
      let n : Int := (Int.ofNat i) - 7; let b := if 0 < n then n else -n; let c : Nat := i * i + 5
      let s := "héllo<日本語!"; let a := (Array.range (i + 1)).map (· * 2); let f := a.filter (· % 3 == 0)
      let j := match Json.parse "{\"a\":1,\"b\":[true,null,-4,\"x\\ny\"]}" with | .ok v => Json.render v | .error err => err
      let d := (Date.parse? "2024-02-29").map toString |>.getD "none"
      let r := ((Router.fromURL "/users/a%20b" : Option GateR).map Router.toURL).getD "none"
      let seg := toString ((("/users/a%20b".splitOn "/").filter (· ≠ "")).map decodeSeg)
      String.intercalate "|" [s!"{n * n - 3 * n + b}", s!"{c - 100}", s!"{c % 7}", s!"{n.natAbs}", s!"{s.length}",
        ((s ++ "!?").take 4).toString, (s.drop 2).toString, String.ofList s.toList.reverse, String.intercalate "," (s.splitOn "<"),
        s!"{s.startsWith "hé"}", s!"{s.endsWith "語!"}", j, d, s!"{a.toList}", s!"{f.size}", s!"{a.foldl (· + ·) 0}", s!"{a.reverse.toList}", r, seg]
  | 2 =>
      let grown := (List.range 4).foldl (fun acc n => acc.push (UInt8.ofNat n)) ByteArray.empty
      let eqR : Resource (String × Nat) → Resource (String × Nat) → Bool | .idle, .idle | .loading, .loading => true | .ok x, .ok y => x == y | .failed x, .failed y => x == y | _, _ => false
      let recVal : ProtoRec := { id := ⟨"tpil4", by dsimp [Codec.refine]; decide⟩, qty := ⟨12, by dsimp [Codec.refine]; decide⟩, raw := ByteArray.mk #[0x89, 0x50] }
      String.intercalate ";" [protoRT () (fun _ _ => true), protoRT (true, false) (· == ·), protoRT #[0, 128, 1000000007] (· == ·),
        protoRT #[(0 : Int), -64, 100000] (· == ·), protoRT ((0xDEADBEEF : UInt32), (0x0102030405060708 : UInt64)) (· == ·),
        protoRT #["", "héllo", "日本語!"] (· == ·), protoRT grown (fun a b => a.data == b.data),
        protoRT (#[none, some #[-42, 999]] : Array (Option (Array Int))) (· == ·),
        protoRT (.ok ("qed", 42) : Resource (String × Nat)) eqR, protoRT recVal (fun a b => a.id.val == b.id.val && a.qty.val == b.qty.val && a.raw.data == b.raw.data)]
  | _ =>
      let sty := inlineStyleStr [letterSpacing (em (-0.015)), zIndex (-1)]
      let fs : Array WsMuxFrame := #[.sub 1 "room" (ByteArray.mk #[8]), .unsub 2, .send 3 "hi".toUTF8, .joinOk 4 (ByteArray.mk #[1]), .event 5 (ByteArray.mk #[2]), .err 6 "e", .closed 7 "c"]
      let mux := fs.foldl (init := "") fun acc f => acc ++ match WsMuxFrame.decode (WsMuxFrame.encode f) with | .ok d => s!"{decide (d == f)}" | .error err => err
      let recD := s!"{Reconnect.off.nextDelayMs 0}|{Reconnect.fixed 120 (some 3) |>.nextDelayMs 2}|{Reconnect.backoff 80 1000 none |>.nextDelayMs 3}"
      let tags : Array GateTag := #[.a, .e, .n i, .s "ok"]
      let tagEq := s!"{GateTag.a == .a}|{GateTag.a == .h}|{GateTag.n i == .n i}|{GateTag.n i == .s "ok"}|{tags.map (·.ctorIdx)}|{compare (GateTag.c) (.n i) == .lt}"
      s!"{sty}|{mux}|{recD}|{tagEq}|{(fun (a b : Nat) => a * 17 + b) i (tailSumAcc (i + 5) 0)}"

def counts (_ : Nat) : Nat := 1
def probeCount : Nat := 4
def names : Array String := #["dom", "core", "proto", "wsStyle"]

component LocalPanel:
  prop tag : String = "p"
  state mode : Nat = 0
  state last : String = "none"
  state newDraft : String = ""
  state cardDraft : String = ""
  event onHit(label : String)
  action setMode(m : Nat): mode = m
  action hit(lbl : String): last = lbl; onHit.emit(lbl)
  view:
    <div class="local-panel" data-mode={mode} data-last={last} data-new={newDraft} data-card={cardDraft} data-tag={tag}>
      {<p class="idle">idle</p> if mode == 0 else
        <div class="banner">
          <button class="new0" onClick={.hit("new0")}>New0</button>
          <button class="new1" onClick={.hit("new1")}>New1</button>
          <input class="in-new" bind={newDraft}/>
        </div>}
      <div class="card">
        <button class="card0" onClick={.hit("card0")}>Card0</button>
        <button class="card1" onClick={.hit("card1")}>Card1</button>
        <button class="toggle" onClick={.setMode(1 if mode == 0 else 0)}>Toggle</button>
        <input class="in-card" bind={cardDraft}/>
      </div>
      {<div class="klist"><div key="kc"><button class="kcard" onClick={.hit("kcard")}>KC</button></div></div> if mode == 0 else
        <div class="klist">
          <div key="kb"><button class="knew" onClick={.hit("knew")}>KN</button></div>
          <div key="kc"><button class="kcard" onClick={.hit("kcard")}>KC</button></div>
        </div>}
    </div>

component LocalLeaf:
  prop label : String = "leaf"
  state n : Nat = 0
  action bump: n += 1
  view: <div class="leaf" data-label={label} data-n={n}><button class="leaf-inc" onClick={.bump}>Inc</button></div>

component LocalNestParent:
  state showChild : Bool = true
  action toggle: showChild = not showChild
  view:
    <div class="nest-parent">
      <button class="nest-toggle" onClick={.toggle}>ToggleChild</button>
      {<LocalLeaf key="child" label="nested"/> if showChild else <span class="hidden">off</span>}
    </div>

component LocalBugsApp:
  state page : Nat = 0
  state bubbled : String = ""
  action setPage(p : Nat): page = p
  action record(s : String): bubbled = s
  view:
    <div class="root" data-page={page} data-bubbled={bubbled}>
      <nav>
        <button class="p0" onClick={.setPage(0)}>0</button>
        <button class="p1" onClick={.setPage(1)}>1</button>
        <button class="p2" onClick={.setPage(2)}>2</button>
        <button class="p3" onClick={.setPage(3)}>3</button>
        <button class="p4" onClick={.setPage(4)}>4</button>
        <button class="p5" onClick={.setPage(5)}>5</button>
        <button class="p6" onClick={.setPage(6)}>6</button>
        <button class="p7" onClick={.setPage(7)}>7</button>
      </nav>
      {match page:
        case 0: <div class="plain-page">Loading text child</div>
        case 1: <LocalPanel key="p1" tag="v1" onHit={.record}/>
        case 2: <LocalLeaf key="leaf2" label="alt"/>
        case 3: <section class="wrap-a"><LocalLeaf key="moved" label="in-a"/></section>
        case 4: <main class="wrap-b"><LocalLeaf key="moved" label="in-b"/></main>
        case 5: <LocalNestParent key="nest"/>
        case 6: <div class="move-a"><div class="slot0"><LocalLeaf key="swap" label="s0"/></div><span class="slot1">empty</span></div>
        case _: <div class="move-b"><span class="slot0">empty</span><div class="slot1"><LocalLeaf key="swap" label="s1"/></div></div>}
    </div>

def localBugsMain : IO Unit := Qed.run LocalBugsApp.app
def localBugsSsrPage1 : String := LocalBugsApp.app.renderModel { page := 1, bubbled := "" }
def localBugsStatePage1 : String := LocalBugsApp.app.dehydrate { page := 1, bubbled := "" }

end JsGate
