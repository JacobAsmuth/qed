import Qed
open Qed

namespace JsGate

def t (s : String) : Html Unit := Html.text s
def e (tag : String) (ats : List (Attr Unit)) (cs : List (Html Unit)) : Html Unit :=
  Html.element tag ats cs

def trees : Array (Html Unit) := #[
  t "hello",
  e "div" [Attr.cls "a", Attr.cls "b", Attr.attr "id" "x"] [t "hi & <bye> \"q\" 'a'"],
  e "input" [Attr.attr "value" "v", Attr.flag "disabled" true, Attr.flag "readonly" false] [],
  e "ul" [] [e "li" [Attr.key "k1"] [t "1"], e "li" [Attr.key "k2"] [t "2"]],
  e "button" [Attr.on "click" (), Attr.onValue "input" (fun _ => ())] [t "go"],
  e "span" [Attr.signalBind "sig"] [],
  e "div" [Attr.signalAttr "s2" "data-x" "v0"] [],
  e "style" [] [t "a < b { x: 1 } </style>"],
  e "script" [] [t "if (a < b) { x }"],
  e "div" [] [t "unicode: café — naïve — 日本語 — 😀 end"],
  Qed.lazy (fun s : String => e "p" [Attr.cls "memo"] [t s]) "memo",
  e "form" [Attr.attr "x<y" "1", Attr.cls ""] [e "div" [] [t "nested", e "b" [] [t "deep"]]]
]
def renderCase (i : Nat) : String := Html.render (trees.getD i (t ""))
def treeCount : Nat := trees.size

def pairs : Array (Html Unit × Html Unit) := #[
  (e "div" [] [t "a"], e "div" [] [t "b"]),
  (e "div" [Attr.cls "x"] [t "a"], e "div" [Attr.cls "y"] [t "a", t "c"]),
  (e "ul" [] [e "li" [Attr.key "1"] [t "a"], e "li" [Attr.key "2"] [t "b"]],
   e "ul" [] [e "li" [Attr.key "2"] [t "b"], e "li" [Attr.key "1"] [t "a"], e "li" [Attr.key "3"] [t "c"]]),
  (e "div" [] [t "x", t "y", t "z"], e "div" [] [t "x"]),
  (t "x", e "div" [] [t "y"])
]
def diffCase (i : Nat) : String := let p := pairs.getD i (t "", t ""); Html.render (applyPatch (diff p.1 p.2) p.1)
def pairCount : Nat := pairs.size

def childPatchCase (i : Nat) : String :=
  let n := (#[0, 1, 32, 12000] : Array Nat).getD i 0
  let old := (Array.range n).map fun j => e "span" [] [t (toString j)]
  let steps : List (KeyedStep Unit) :=
    .create (t "new") :: ((List.range n).reverse.map fun j =>
      .reuse j (.patchElement [Attr.cls "patched"] [.reuse 0 (.setText (toString j))])) ++
    [.reuse (n + 1) (.patchElement [] [])]
  let patched := applyChildrenTR #[t "prefix"] steps old
  let (length, checksum) := patched.foldl (init := (0, 0)) fun (length, checksum) child =>
    let rendered := Html.render child
    (length + rendered.length,
      rendered.foldl (init := checksum) fun acc c => (acc * 31 + c.toNat) % 1000000007)
  s!"{patched.size}|{length}|{checksum}"

def wideRenderCase (i : Nat) : String :=
  let n := (#[0, 1, 32, 12000] : Array Nat).getD i 0
  let children : List (Html Nat) := (List.range n).map fun j =>
    .element "button" [.on "click" j, .attr "title" "<&\""] [.text s!"row {j} & < >"]
  let (html, handlers) := renderNode #[777] (.element "main" [] children)
  let digest := html.toList.foldl (init := 0) fun acc c => (acc * 31 + c.toNat) % 1000000007
  let handlerDigest := handlers.foldl (init := 0) fun acc m => (acc * 31 + m) % 1000000007
  s!"{html.length}|{digest}|{handlers.size}|{handlerDigest}"

def keyIndexCase (i : Nat) : String :=
  let row (key : String) := e "div" [.key key] []
  let cases := #[[], [row "a"], [row "b", row "a"], [row "a", row "a"],
    [row "a", t "unkeyed"], [row "a", row "b", row "a"]]
  match validatedKeyIndex (cases.getD i []) with
  | none => "invalid"
  | some index =>
      let showIndex := fun key => match index[key]? with | some n => toString n | none => "missing"
      showIndex "a" ++ "|" ++ showIndex "b"

def arith (i : Nat) : String :=
  let n : Int := (Int.ofNat i) - 7
  let a := n * n - 3 * n
  let b := if 0 < n then n else -n
  let c : Nat := i * i + 5
  s!"{a + b}|{b}|{c - 100}|{c % 7}|{n.natAbs}"

def strs : Array String := #["", "a", "héllo", "日本語!", "a<b&c", "  sp  ", "café", "x\ny\tz", "-0.015"]
def strop (i : Nat) : String :=
  let s := strs.getD i ""
  let pfx := s.startsWith "hé"
  let pfx2 := s.startsWith "-"
  let pfxEmpty := s.startsWith ""
  let sfx := s.endsWith "語!"
  let sfx2 := s.endsWith "é"
  let sfxLong := s.endsWith "日本語!!"
  s!"{s.length}|{(s ++ "!?").take 4}|{s.drop 2}|{s.toList.reverse |> String.ofList}|{String.intercalate "," (s.splitOn "<")}|{pfx},{pfx2},{pfxEmpty},{sfx},{sfx2},{sfxLong}"

def jsons : Array String :=
  #["null", "true", "[1,2,3]", "{\"a\":1,\"b\":[true,null]}", "\"x\\ny\"", "123", "[]", "{}",
    "[[1],[2,3],[]]", "{\"n\":-4,\"s\":\"hi\"}"]
def jsonRt (i : Nat) : String :=
  match Json.parse (jsons.getD i "null") with
  | .ok j    => Json.render j
  | .error e => s!"ERR {e}"

def dates : Array String := #["2024-02-29", "2023-02-29", "2024-13-01", "2024-06-15", "bad", "2024-1-5", "0001-12-31"]
def dateP (i : Nat) : String :=
  match Date.parse? (dates.getD i "") with
  | some d => d.toString
  | none   => "none"

def arrP (i : Nat) : String :=
  let a := (Array.range (i + 1)).map (fun x => x * 2)
  let b := a.filter (fun x => x % 3 == 0)
  s!"{a.toList}|{b.size}|{a.foldl (· + ·) 0}|{a.reverse.toList}"

router GateR:
  home = ""
  user(name: String) = "users"

def routes : Array String := #["/", "/users/ada", "/users/alan", "/users/a%20b", "/nope/x"]
def routeP (i : Nat) : String :=
  match (Router.fromURL (routes.getD i "") : Option GateR) with
  | some r => Router.toURL r
  | none   => "none"

def segP (i : Nat) : String :=
  let p := routes.getD i ""
  toString (((p.splitOn "/").filter (· ≠ "")).map decodeSeg)

schema ProtoRec:
  id  : String where 1 <= id.length <= 32
  qty : Nat    where qty <= 500
  raw : Bytes

private def protoRoundTrip {α : Type} [ToProto α] [FromProto α] (a : α) (eq : α → α → Bool) : String :=
  let bs := Proto.encode a
  let ok := match Proto.decode (α := α) bs with
    | .ok b    => eq a b
    | .error _ => false
  s!"{Proto.encodeHex bs}|{ok}"

def protoP (i : Nat) : String :=
  match i with
  | 0 => protoRoundTrip () (fun _ _ => true)
  | 1 => protoRoundTrip (true, false) (· == ·)
  | 2 => protoRoundTrip #[0, 1, 127, 128, 16384, 1000000007] (· == ·)
  | 3 => protoRoundTrip #[(0 : Int), -1, 1, -64, 64, -100000, 100000] (· == ·)
  | 4 => protoRoundTrip ((0xDEADBEEF : UInt32), (0x0102030405060708 : UInt64)) (· == ·)
  | 5 => protoRoundTrip #["", "héllo", "日本語!"] (· == ·)
  | 6 =>
      let grown := (List.range 300).foldl (fun acc n => acc.push (UInt8.ofNat (n % 256))) ByteArray.empty
      protoRoundTrip grown (fun a b => a.data == b.data)
  | 7 =>
      let opts : Array (Option (Array Int)) := #[none, some #[], some #[-42, 0, 999]]
      protoRoundTrip opts (· == ·)
  | 8 =>
      let r1 : Resource (String × Nat) := .idle
      let r2 : Resource (String × Nat) := .ok ("qed", 42)
      let r3 : Resource (String × Nat) := .failed "err"
      let eqR (x y : Resource (String × Nat)) : Bool :=
        match x, y with
        | .idle, .idle => true
        | .loading, .loading => true
        | .ok a, .ok b => a == b
        | .failed a, .failed b => a == b
        | _, _ => false
      String.intercalate ";" [protoRoundTrip r1 eqR, protoRoundTrip r2 eqR, protoRoundTrip r3 eqR]
  | 9 =>
      let recVal : ProtoRec := {
        id  := ⟨"tpil4", by dsimp [Codec.refine]; decide⟩
        qty := ⟨12, by dsimp [Codec.refine]; decide⟩
        raw := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47]
      }
      protoRoundTrip recVal (fun a b =>
        a.id.val == b.id.val && a.qty.val == b.qty.val && a.raw.data == b.raw.data)
  | _ => ""

def styleP (i : Nat) : String :=
  match i with
  | 0 => inlineStyleStr [letterSpacing (em (-0.015)), zIndex (-1)]
  | 1 => inlineStyleStr [letterSpacing (em (-(-0.015))), zIndex (-0)]
  | _ => ""

def wsMuxP (i : Nat) : String :=
  let frames : Array WsMuxFrame := #[
    .sub 1 "room" (ByteArray.mk #[0x08, 0x01]),
    .sub 0xDEADBEEF "chat/日本語" (ByteArray.mk #[0x00, 0xFF, 0x7F]),
    .unsub 0x80000001,
    .send 42 ("hello".toUTF8),
    .joinOk 7 (ByteArray.mk #[1, 2, 3]),
    .event 0xFFFFFFFF (ByteArray.mk #[9, 8, 7]),
    .err 9 "unauthorized",
    .closed 10 "bye"
  ]
  if h : i < frames.size then
    let f := frames[i]
    let enc := WsMuxFrame.encode f
    match WsMuxFrame.decode enc with
    | .ok d => s!"{Proto.encodeHex enc}|{decide (d == f)}"
    | .error e => s!"ERR:{e}"
  else
    let recPols : Array (Reconnect × Nat) := #[
      (.off, 0),
      (.fixed 120 (some 3), 2),
      (.fixed 120 (some 3), 3),
      (.backoff 80 1000 none, 0),
      (.backoff 80 1000 none, 5)
    ]
    match recPols[i - frames.size]? with
    | some (p, att) => toString (p.nextDelayMs att)
    | none => ""

def tailSumAcc (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => tailSumAcc k (acc + k + 1)

def codegenStressP (i : Nat) : String :=
  -- Exercises direct-loop tail recursion, multi-branch join points, and closures (for `--min` identifier renaming)
  let s := tailSumAcc (i * 10 + 5) 0
  let tag :=
    if i % 3 == 0 then s!"even3:{s}"
    else if i % 3 == 1 then s!"mod1:{s + 1}"
    else s!"mod2:{s + 2}"
  let pairFn := fun (a b : Nat) => a * 17 + b
  s!"{tag}|{pairFn i s}"

def probes : Array (String × Nat × (Nat → String)) := #[
  ("render",        treeCount,   renderCase),
  ("diff",          pairCount,   diffCase),
  ("arith",         32,          arith),
  ("string",        strs.size,   strop),
  ("json",          jsons.size,  jsonRt),
  ("date",          dates.size,  dateP),
  ("array",         12,          arrP),
  ("router",        routes.size, routeP),
  ("seg",           routes.size, segP),
  ("childPatch",    4,           childPatchCase),
  ("wideRender",    4,           wideRenderCase),
  ("keyIndex",      6,           keyIndexCase),
  ("proto",         10,          protoP),
  ("style",         2,           styleP),
  ("wsMux",         13,          wsMuxP),
  ("codegenStress", 8,           codegenStressP)
]

def run (probe i : Nat) : String := match probes[probe]? with | some (_, _, f) => f i | none => ""
def counts (probe : Nat) : Nat := match probes[probe]? with | some (_, n, _) => n | none => 0
def probeCount : Nat := probes.size
def names : Array String := probes.map Prod.fst

end JsGate
