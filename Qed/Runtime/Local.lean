import Qed.Runtime.LocalCore
import Qed.Runtime.Verify

namespace Qed

private def wrapLocalView {S M O : Type} [ToJson S] [FromJson S] [ToJson O] (init : S) (view : S → Html M) (update : S → M → S × Option O) : String → Html LocalMsg :=
  let dec (s : String) : S := ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  fun s => (view (dec s)).map fun m => { run := fun st => let (s', o) := update (dec st) m; (Json.render (ToJson.toJson s'), o.map (Json.render ∘ toJson)) }

def LocalDef.of {S M O : Type} [ToJson S] [FromJson S] [ToJson O] (id : String) (init : S) (view : S → Html M) (update : S → M → S × Option O)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  { id, init := Json.render (ToJson.toJson init), view := wrapLocalView init view update, valid_view := ⟨fun _ => by simpa [wrapLocalView, Html.valid] using hvalid _, trivial⟩ }

def LocalDef.ofSimple {S M : Type} [ToJson S] [FromJson S] (id : String) (init : S) (view : S → Html M) (update : S → M → S)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  LocalDef.of (O := String) id init view (fun s m => (update s m, none)) hvalid

def LocalDef.ofProps {P S M O : Type} [FromJson P] [ToJson S] [FromJson S] [ToJson O] (id : String) (init : S) (view : P → S → Html M) (update : P → S → M → S × Option O)
    (hvalid : ∀ p s, Html.valid (view p s) = true := by qedProveValidHtml) : LocalDef :=
  { id, init := Json.render (toJson init), view := fun _ => .text ""
    viewProps := some fun props => match (Json.parse props).bind (FromJson.fromJson (α := P)) with
      | .error e => fun _ => .text s!"Invalid component props: {e}" | .ok p => wrapLocalView init (view p) (update p)
    valid_view := ⟨fun _ => rfl, fun props _ => by dsimp only; cases (Json.parse props).bind (FromJson.fromJson (α := P)) with | error _ => rfl | ok p => simpa [wrapLocalView, Html.valid] using hvalid p _⟩ }

theorem LocalDef.of_view_roundtrip {S M O : Type} [LawfulJson S] [ToJson O] (id : String) (init s : S) (view : S → Html M)
    (update : S → M → S × Option O) (hvalid : ∀ x, Html.valid (view x) = true) (hdepth : LawfulJson.depthBound S ≤ 64) :
    (LocalDef.of id init view update hvalid).view (Json.render (toJson s)) =
      (view s).map (fun m => { run := fun st =>
        let (s', o) := update (((Json.parse st).bind FromJson.fromJson).toOption.getD init) m
        (Json.render (ToJson.toJson s'), o.map fun x => Json.render (ToJson.toJson x)) }) := by
  simp only [LocalDef.of, wrapLocalView, LocalDef.decode_toJson_eq s init hdepth]; rfl

theorem LocalDef.ofProps_view_roundtrip {P S M O : Type} [LawfulJson P] [LawfulJson S] [ToJson O] (id : String) (init s : S) (p : P)
    (view : P → S → Html M) (update : P → S → M → S × Option O) (hvalid : ∀ p x, Html.valid (view p x) = true)
    (hdepthP : LawfulJson.depthBound P ≤ 64) (hdepthS : LawfulJson.depthBound S ≤ 64) :
    (LocalDef.ofProps id init view update hvalid).viewForProps (Json.render (toJson p)) (Json.render (toJson s)) =
      (view p s).map (fun m => { run := fun st =>
        let (next, out) := update p (((Json.parse st).bind FromJson.fromJson).toOption.getD init) m
        (Json.render (toJson next), out.map (Json.render ∘ toJson)) }) := by
  simp only [LocalDef.viewForProps, LocalDef.ofProps, wrapLocalView, Option.map_some, Option.getD_some]
  rw [LawfulJson.parse_render_toJson p hdepthP]; simp only [LocalDef.decode_toJson_eq s init hdepthS]

end Qed
