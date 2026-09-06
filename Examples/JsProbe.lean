/-
  A probe used to differentially test the Lean-IR → JS transpiler against native Lean.
  Each `*Case` builds a value and renders it to a String; the harness runs the SAME
  decl natively and (transpiled) under node, and asserts identical output — so JS never
  hand-constructs Lean values, it calls these transpiled builders.
-/
import Qed
open Qed

namespace JsProbe

def t (s : String) : Html Unit := Html.text s
def e (tag : String) (ats : List (Attr Unit)) (cs : List (Html Unit)) : Html Unit :=
  Html.element tag ats cs

/-- A spread of trees exercising escaping, attrs, void elements, keys, signals, lazy. -/
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
  Html.lazy "lz" (e "p" [Attr.cls "memo"] [t "memo"]),
  e "form" [Attr.attr "x<y" "1", Attr.cls ""] [e "div" [] [t "nested", e "b" [] [t "deep"]]]
]
def renderCase (i : Nat) : String := Html.render (trees.getD i (t ""))
def treeCount : Nat := trees.size

/-- Pairs for diffing: `applyPatch (diff a b) a`, which `diff_apply` says equals `b`. -/
def pairs : Array (Html Unit × Html Unit) := #[
  (e "div" [] [t "a"], e "div" [] [t "b"]),
  (e "div" [Attr.cls "x"] [t "a"], e "div" [Attr.cls "y"] [t "a", t "c"]),
  (e "ul" [] [e "li" [Attr.key "1"] [t "a"], e "li" [Attr.key "2"] [t "b"]],
   e "ul" [] [e "li" [Attr.key "2"] [t "b"], e "li" [Attr.key "1"] [t "a"], e "li" [Attr.key "3"] [t "c"]]),
  (e "div" [] [t "x", t "y", t "z"], e "div" [] [t "x"]),
  (t "x", e "div" [] [t "y"])
]
def diffCase   (i : Nat) : String := let p := pairs.getD i (t "", t ""); Html.render (applyPatch (diff p.1 p.2) p.1)
def diffExpect (i : Nat) : String := Html.render (pairs.getD i (t "", t "")).2
def pairCount : Nat := pairs.size

/-- Exercise pure child patching with wide lists, reordering, creation, a nonempty
    accumulator, and out-of-range reuse (which the pure model defines via its default). -/
def childPatchCase (i : Nat) : String :=
  let n := (#[0, 1, 32, 1000, 8000] : Array Nat).getD i 0
  let old := (Array.range n).map fun j => e "span" [] [t (toString j)]
  let steps : List (KeyedStep Unit) :=
    .create (t "new") :: ((List.range n).reverse.map fun j =>
      .reuse j (.patchElement [Attr.cls "patched"] [.reuse 0 (.lazyPatch "" (.setText (toString j)))])) ++
    [.reuse (n + 1) (.patchElement [] [])]
  let patched := applyChildrenTR #[t "prefix"] steps old
  -- Render each child separately: this probes the wide patch traversal, without the
  -- string renderer's recursive sibling walk. Incorporate every character in row order.
  let (length, checksum) := patched.foldl (init := (0, 0)) fun (length, checksum) child =>
    let rendered := Html.render child
    (length + rendered.length,
      rendered.foldl (init := checksum) fun acc c => (acc * 31 + c.toNat) % 1000000007)
  s!"{patched.size}|{length}|{checksum}"

/-- Wide HTML serialization and handler order, including a pre-existing handler slot.
    The previous recursive sibling renderer overflowed the JavaScript stack here. -/
def wideRenderCase (i : Nat) : String :=
  let n := (#[0, 1, 32, 8000, 16000] : Array Nat).getD i 0
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

end JsProbe
