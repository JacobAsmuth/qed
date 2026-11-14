import Qed.Html
import Qed.Json.Basic

namespace Qed

structure LocalMsg where
  run : String → String × Option String

structure LocalDef where
  id        : String
  init      : String
  view      : String → Html LocalMsg
  viewProps : Option (String → String → Html LocalMsg) := none

def LocalDef.dedupe (ds : List LocalDef) : List LocalDef :=
  (ds.foldl (fun (acc : Array LocalDef) d =>
    if acc.any (·.id == d.id) then acc else acc.push d) #[]).toList

def LocalDef.of {S M O : Type} [ToJson S] [FromJson S] [ToJson O]
    (id : String) (init : S)
    (view : S → Html M) (update : S → M → S × Option O) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id   := id
    init := Json.render (ToJson.toJson init)
    view := fun s => (view (dec s)).map fun m =>
      { run := fun st =>
          let (s', o) := update (dec st) m
          (Json.render (ToJson.toJson s'), o.map fun x => Json.render (ToJson.toJson x)) } }

def LocalDef.ofSimple {S M : Type} [ToJson S] [FromJson S]
    (id : String) (init : S) (view : S → Html M) (update : S → M → S) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id   := id
    init := Json.render (ToJson.toJson init)
    view := fun s => (view (dec s)).map fun m =>
      { run := fun st => (Json.render (ToJson.toJson (update (dec st) m)), none) } }

def LocalDef.ofProps {P S M O : Type} [FromJson P] [ToJson S] [FromJson S] [ToJson O]
    (id : String) (init : S) (view : P → S → Html M)
    (update : P → S → M → S × Option O) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id, init := Json.render (toJson init), view := fun _ => .text "",
    viewProps := some fun props =>
      match (Json.parse props).bind (FromJson.fromJson (α := P)) with
      | .error e => fun _ => .text s!"Invalid component props: {e}"
      | .ok p => fun s => (view p (dec s)).map fun m =>
          { run := fun st =>
              let (next, out) := update p (dec st) m
              (Json.render (toJson next), out.map (Json.render ∘ toJson)) } }

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

private def attrWithLocalInit {msg : Type} (a : Attr msg) (i : String) : Attr msg :=
  match a with
  | .localCell key comp _ p bubble => .localCell key comp (some i) p bubble
  | x => x

def Attr.localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : Attr msg :=
  attrWithLocalInit a (Json.render (ToJson.toJson init))

end Qed
