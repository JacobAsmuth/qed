import Qed.Html
import Qed.Date
import Qed.Router

namespace Qed

inductive Cmd (msg : Type) where
  | none
  | stream (url : String) (body : String) (onChunk : String → msg) (onDone : msg)
  | now (onNow : Date → msg)
  | request (method url body : String) (onResult : Except String String → msg)
  | pushPath (url : Url)
  | batch (cmds : List (Cmd msg))
  | port (name payload : String)
  | fx (kind a b c : String)
  | fxResult (kind a b : String) (onResult : String → msg)
  | socket (key url : String) (onMessage : String → msg)
           (onOpen : Option msg) (onClose : Option msg) (onError : Option (String → msg))

instance : Coe (List (Cmd msg)) (Cmd msg) := ⟨.batch⟩

mutual
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none                      => .none
  | .stream u b onChunk onDone => .stream u b (fun c => f (onChunk c)) (f onDone)
  | .now onNow                 => .now (fun d => f (onNow d))
  | .request m u b onResult    => .request m u b (fun r => f (onResult r))
  | .pushPath p                => .pushPath p
  | .batch cmds                => .batch (Cmd.mapList f cmds)
  | .port n p                  => .port n p
  | .fx k a b c                => .fx k a b c
  | .fxResult k a b onResult   => .fxResult k a b (fun s => f (onResult s))
  | .socket key url onMsg onOpen onClose onErr =>
      .socket key url (fun d => f (onMsg d)) (onOpen.map f) (onClose.map f)
              (onErr.map (fun g d => f (g d)))
def Cmd.mapList (f : α → β) : List (Cmd α) → List (Cmd β)
  | []      => []
  | c :: cs => Cmd.map f c :: Cmd.mapList f cs
end

mutual
def Cmd.flatten : Cmd msg → List (Cmd msg)
  | .batch cmds => Cmd.flattenList cmds
  | c           => [c]
def Cmd.flattenList : List (Cmd msg) → List (Cmd msg)
  | []      => []
  | c :: cs => Cmd.flatten c ++ Cmd.flattenList cs
end

def httpDecode [FromJson α] (onOk : α → msg) (onErr : String → msg) :
    Except String String → msg
  | .error e   => onErr e
  | .ok   body => match (Json.parse body).bind FromJson.fromJson with
                  | .ok a    => onOk a
                  | .error e => onErr e

def Cmd.getJson [FromJson α] (url : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "GET" url "" (httpDecode onOk onErr)

def Cmd.postJson [FromJson α] (url body : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "POST" url body (httpDecode onOk onErr)

def Cmd.storageSet    (key value : String) : Cmd msg := .fx "storage.set" key value ""
def Cmd.storageRemove (key : String)       : Cmd msg := .fx "storage.remove" key "" ""
def Cmd.storageClear                       : Cmd msg := .fx "storage.clear" "" "" ""
def Cmd.storageGet (key : String) (onValue : Option String → msg) : Cmd msg :=
  .fxResult "storage.get" key "" fun s =>
    onValue (match (Json.parse s).toOption with | some (.str v) => some v | _ => Option.none)

def Cmd.pushUrl {α} [ToHref α] (target : α) : Cmd msg := .pushPath (ToHref.toUrl target)
def Cmd.navigate {α} [ToHref α] (target : α) : Cmd msg := .pushPath (ToHref.toUrl target)
def Cmd.replaceUrl {α} [ToHref α] (target : α) : Cmd msg := .fx "history.replace" (ToHref.toHref target) "" ""
def Cmd.back    : Cmd msg := .fx "history.back" "" "" ""
def Cmd.forward : Cmd msg := .fx "history.forward" "" "" ""

def Cmd.copy  (text : String)         : Cmd msg := .fx "clipboard.write" text "" ""
def Cmd.paste (onText : String → msg) : Cmd msg := .fxResult "clipboard.read" "" "" onText

def Cmd.focus          (elementId : String) : Cmd msg := .fx "dom.focus" elementId "" ""
def Cmd.blur           (elementId : String) : Cmd msg := .fx "dom.blur" elementId "" ""
def Cmd.select         (elementId : String) : Cmd msg := .fx "dom.select" elementId "" ""
def Cmd.scrollIntoView (elementId : String) : Cmd msg := .fx "dom.scrollIntoView" elementId "" ""

def Cmd.after (ms : Nat) (onTick : msg) : Cmd msg := .fxResult "timer.after" (toString ms) "" fun _ => onTick
def Cmd.afterKeyed (key : String) (ms : Nat) (onTick : msg) : Cmd msg :=
  .fxResult "timer.afterKeyed" key (toString ms) fun _ => onTick
def Cmd.cancel (key : String) : Cmd msg := .fx "timer.cancel" key "" ""

def Cmd.setTitle (title : String) : Cmd msg := .fx "document.title" title "" ""

def Cmd.randomInt (lo hi : Int) (onInt : Int → msg) : Cmd msg :=
  .fxResult "random.int" (toString lo) (toString hi) fun s => onInt ((s.toInt?).getD lo)

def Cmd.wsOpen (key url : String) (onMessage : String → msg)
    (onOpen : Option msg := Option.none) (onClose : Option msg := Option.none)
    (onError : Option (String → msg) := Option.none) : Cmd msg :=
  .socket key url onMessage onOpen onClose onError

def Cmd.wsSend (key data : String) : Cmd msg := .fx "ws.send" key data ""
def Cmd.wsClose (key : String) : Cmd msg := .fx "ws.close" key "" ""

def Cmd.download (filename mime content : String) : Cmd msg := .fx "file.download" filename mime content

structure FilePick where
  name : String
  mime : String
  size : Nat
  text : String

instance : FromJson FilePick where
  fromJson j := do
    return { name := (← fromField j "name"), mime := (← fromField j "mime"),
             size := (← fromField j "size"), text := (← fromField j "text") }

def FilePick.decode (s : String) (maxDepth : Nat := 64) : Except String FilePick :=
  (Json.parse s maxDepth).bind fromJson

def Cmd.pickFile (accept : String) (onFile : Except String FilePick → msg) : Cmd msg :=
  .fxResult "file.pick" accept "" fun s => onFile (FilePick.decode s)

def dispatchPorts (handlers : Array (String × (String → Option msg))) (name payload : String) : Option msg :=
  match handlers.find? (fun h => h.1 == name) with
  | some h => h.2 payload
  | none   => none

end Qed
