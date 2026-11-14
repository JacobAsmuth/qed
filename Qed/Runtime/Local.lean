import Qed.Html
import Qed.Json.Basic
import Qed.Runtime.Verify

namespace Qed

structure LocalMsg where
  run : String → String × Option String

structure LocalDef where
  id         : String
  init       : String
  view       : String → Html LocalMsg
  viewProps  : Option (String → String → Html LocalMsg) := none
  valid_view : (∀ s, Html.valid (view s) = true) ∧
               match viewProps with
               | none   => True
               | some f => ∀ p s, Html.valid (f p s) = true

def LocalDef.viewForProps (ldef : LocalDef) (props : String) : String → Html LocalMsg :=
  (ldef.viewProps.map (· props)).getD ldef.view

def LocalDef.dedupe (ds : List LocalDef) : List LocalDef :=
  (ds.foldl (fun (acc : Array LocalDef) d =>
    if acc.any (·.id == d.id) then acc else acc.push d) #[]).toList

def LocalDef.of {S M O : Type} [ToJson S] [FromJson S] [ToJson O]
    (id : String) (init : S)
    (view : S → Html M) (update : S → M → S × Option O)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id   := id
    init := Json.render (ToJson.toJson init)
    view := fun s => (view (dec s)).map fun m =>
      { run := fun st =>
          let (s', o) := update (dec st) m
          (Json.render (ToJson.toJson s'), o.map fun x => Json.render (ToJson.toJson x)) }
    valid_view := ⟨fun s => by simpa [Html.valid] using hvalid (dec s), trivial⟩ }

def LocalDef.ofSimple {S M : Type} [ToJson S] [FromJson S]
    (id : String) (init : S) (view : S → Html M) (update : S → M → S)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  LocalDef.of (O := String) id init view (fun s m => (update s m, none)) hvalid

def LocalDef.ofProps {P S M O : Type} [FromJson P] [ToJson S] [FromJson S] [ToJson O]
    (id : String) (init : S) (view : P → S → Html M)
    (update : P → S → M → S × Option O)
    (hvalid : ∀ p s, Html.valid (view p s) = true := by qedProveValidHtml) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id
    init := Json.render (toJson init)
    view := fun _ => .text ""
    viewProps := some fun props =>
      match (Json.parse props).bind (FromJson.fromJson (α := P)) with
      | .error e => fun _ => .text s!"Invalid component props: {e}"
      | .ok p => fun s => (view p (dec s)).map fun m =>
          { run := fun st =>
              let (next, out) := update p (dec st) m
              (Json.render (toJson next), out.map (Json.render ∘ toJson)) }
    valid_view := by
      refine ⟨fun _ => rfl, fun props s => ?_⟩
      dsimp only
      cases (Json.parse props).bind (FromJson.fromJson (α := P)) with
      | error _ => rfl
      | ok p    => simpa [Html.valid] using hvalid p (dec s) }

def Attr.localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) : Attr msg :=
  match a with
  | .localCell k c i _ b => .localCell k c i (Json.render (toJson props)) b
  | x => x

def localMount (component key : String) : Attr msg :=
  .localCell key component none "" (fun _ => none)

def localMountWith {O msg : Type} [FromJson O] (component key : String)
    (onOut : O → Option msg) : Attr msg :=
  .localCell key component none "" fun s =>
    (((Json.parse s).bind FromJson.fromJson : Except String O)).toOption.bind onOut

def Attr.localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : Attr msg :=
  match a with
  | .localCell k comp _ p bubble => .localCell k comp (some (Json.render (ToJson.toJson init))) p bubble
  | x => x

@[simp] theorem Attr.localProps_localCell {msg P : Type} [ToJson P]
    (k c : String) (i : Option String) (p0 : String) (b : String → Option msg) (props : P) :
    (Attr.localCell k c i p0 b).localProps props = .localCell k c i (Json.render (toJson props)) b := rfl

@[simp] theorem Attr.localInit_localCell {msg S : Type} [ToJson S]
    (k c : String) (i0 : Option String) (p : String) (b : String → Option msg) (init : S) :
    (Attr.localCell k c i0 p b).localInit init = .localCell k c (some (Json.render (ToJson.toJson init))) p b := rfl

@[simp] theorem Attr.valid_localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) :
    (a.localProps props).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.valid_localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) :
    (a.localInit init).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.valid_localMount (component key : String) :
    (localMount component key : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_localMountWith {O msg : Type} [FromJson O]
    (component key : String) (onOut : O → Option msg) :
    (localMountWith component key onOut).valid = true := rfl

end Qed
