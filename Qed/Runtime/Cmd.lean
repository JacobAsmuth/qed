import Qed.Html
import Qed.Date
import Qed.Proto
import Qed.Base64
import Qed.Router.Basic
import Qed.Socket.Basic

namespace Qed

inductive Cmd (msg : Type) where
  | none
  | stream (url body : String) (onChunk : String → msg) (onDone : msg)
  | now (onNow : Date → msg)
  | request (method url body : String) (onResult : Except String String → msg)
  | requestBytes (method url : String) (body : ByteArray) (onResult : Except String ByteArray → msg)
  | pushPath (url : Url)
  | batch (cmds : List (Cmd msg))
  | port (name payload : String)
  | fx (kind a b c : String)
  | fxResult (kind a b : String) (onResult : String → msg)
  | wsMuxSub (slot url channel : String) (params : ByteArray) (reconnect : Reconnect) (onJoin : ByteArray → msg) (onMessage : ByteArray → msg) (onStatus : SocketStatus → msg)
  | wsMuxSend (slot : String) (payload : ByteArray)
  | wsMuxUnsub (slot : String)
  | wsExtOpen (slot url : String) (isBinary : Bool) (reconnect : Reconnect) (onJoin : Unit → msg) (onText : String → msg) (onBytes : ByteArray → msg) (onStatus : SocketStatus → msg)
  | wsExtSendText (slot text : String)
  | wsExtSendBytes (slot : String) (payload : ByteArray)
  | wsExtClose (slot : String)

instance : Coe (List (Cmd msg)) (Cmd msg) := ⟨.batch⟩

mutual
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none => .none | .stream u b c d => .stream u b (f ∘ c) (f d) | .now onNow => .now (f ∘ onNow)
  | .request m u b r => .request m u b (f ∘ r) | .requestBytes m u b r => .requestBytes m u b (f ∘ r)
  | .pushPath p => .pushPath p | .batch cmds => .batch (Cmd.mapList f cmds) | .port n p => .port n p
  | .fx k a b c => .fx k a b c | .fxResult k a b r => .fxResult k a b (f ∘ r)
  | .wsMuxSub s u ch p rec j m st => .wsMuxSub s u ch p rec (f ∘ j) (f ∘ m) (f ∘ st)
  | .wsMuxSend s p => .wsMuxSend s p | .wsMuxUnsub s => .wsMuxUnsub s
  | .wsExtOpen s u bin rec j t b st => .wsExtOpen s u bin rec (f ∘ j) (f ∘ t) (f ∘ b) (f ∘ st)
  | .wsExtSendText s t => .wsExtSendText s t | .wsExtSendBytes s p => .wsExtSendBytes s p | .wsExtClose s => .wsExtClose s
def Cmd.mapList (f : α → β) : List (Cmd α) → List (Cmd β) | [] => [] | c :: cs => Cmd.map f c :: Cmd.mapList f cs
end

mutual
def Cmd.prefixSlots (pfx : String) : Cmd α → Cmd α
  | .batch cmds => .batch (Cmd.prefixSlotsList pfx cmds)
  | .wsMuxSub s u ch p rec j m st => .wsMuxSub (pfx ++ s) u ch p rec j m st
  | .wsMuxSend s p => .wsMuxSend (pfx ++ s) p
  | .wsMuxUnsub s => .wsMuxUnsub (pfx ++ s)
  | .wsExtOpen s u bin rec j t b st => .wsExtOpen (pfx ++ s) u bin rec j t b st
  | .wsExtSendText s t => .wsExtSendText (pfx ++ s) t
  | .wsExtSendBytes s p => .wsExtSendBytes (pfx ++ s) p
  | .wsExtClose s => .wsExtClose (pfx ++ s)
  | c => c
def Cmd.prefixSlotsList (pfx : String) : List (Cmd α) → List (Cmd α)
  | [] => [] | c :: cs => Cmd.prefixSlots pfx c :: Cmd.prefixSlotsList pfx cs
end

def Cmd.mapScoped (pfx : String) (f : α → β) (c : Cmd α) : Cmd β :=
  Cmd.map f (if pfx.isEmpty then c else Cmd.prefixSlots pfx c)

mutual
def Cmd.flatten : Cmd msg → List (Cmd msg) | .batch cmds => Cmd.flattenList cmds | c => [c]
def Cmd.flattenList : List (Cmd msg) → List (Cmd msg) | [] => [] | c :: cs => Cmd.flatten c ++ Cmd.flattenList cs
end

mutual
def Cmd.clientOnly : Cmd msg → Cmd msg
  | .request .. | .requestBytes .. | .wsMuxSub .. | .wsExtOpen .. => .none
  | .batch cmds => .batch (Cmd.clientOnlyList cmds) | c => c
def Cmd.clientOnlyList : List (Cmd msg) → List (Cmd msg) | [] => [] | c :: cs => Cmd.clientOnly c :: Cmd.clientOnlyList cs
end

def httpDecode [FromJson α] (onOk : α → msg) (onErr : String → msg) : Except String String → msg
  | .error e => onErr e | .ok body => match (Json.parse body).bind FromJson.fromJson with | .ok a => onOk a | .error e => onErr e
def protoDecode [FromProto α] (onResult : Except String α → msg) : Except String ByteArray → msg
  | .error e => onResult (.error e) | .ok body => onResult (Proto.decode body)

def Cmd.rpc [ToProto req] [FromProto resp] (url : String) (payload : req) (onResult : Except String resp → msg) : Cmd msg := .requestBytes "POST" url (Proto.encode payload) (protoDecode onResult)
def Cmd.getJson [FromJson α] (url : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg := .request "GET" url "" (httpDecode onOk onErr)
def Cmd.postJson [FromJson α] (url body : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg := .request "POST" url body (httpDecode onOk onErr)
def Cmd.streamJson [ToJson α] (url : String) (body : α) (onChunk : String → msg) (onDone : msg) : Cmd msg := .stream url (Json.render (toJson body)) onChunk onDone

def Cmd.storageSet (key value : String) : Cmd msg := .fx "storage.set" key value ""
def Cmd.storageRemove (key : String) : Cmd msg := .fx "storage.remove" key "" ""
def Cmd.storageClear : Cmd msg := .fx "storage.clear" "" "" ""
def Cmd.storageGet (key : String) (onValue : Option String → msg) : Cmd msg :=
  .fxResult "storage.get" key "" fun s => onValue (match (Json.parse s).toOption with | some (.str v) => some v | _ => Option.none)

def Cmd.pushUrl {α} [ToHref α] (target : α) : Cmd msg := .pushPath (ToHref.toUrl target)
def Cmd.navigate {α} [ToHref α] (target : α) : Cmd msg := .pushPath (ToHref.toUrl target)
def Cmd.replaceUrl {α} [ToHref α] (target : α) : Cmd msg := .fx "history.replace" (ToHref.toHref target) "" ""
def Cmd.openExternal (url : Url) : Cmd msg := .fx "location.assign" url.raw "" ""
def Cmd.back : Cmd msg := .fx "history.back" "" "" ""
def Cmd.forward : Cmd msg := .fx "history.forward" "" "" ""
def Cmd.copy (text : String) : Cmd msg := .fx "clipboard.write" text "" ""
def Cmd.paste (onText : String → msg) : Cmd msg := .fxResult "clipboard.read" "" "" onText
def Cmd.focus (elementId : String) : Cmd msg := .fx "dom.focus" elementId "" ""
def Cmd.blur (elementId : String) : Cmd msg := .fx "dom.blur" elementId "" ""
def Cmd.select (elementId : String) : Cmd msg := .fx "dom.select" elementId "" ""
def Cmd.scrollIntoView (elementId : String) : Cmd msg := .fx "dom.scrollIntoView" elementId "" ""
def Cmd.after (ms : Nat) (onTick : msg) : Cmd msg := .fxResult "timer.after" (toString ms) "" fun _ => onTick
def Cmd.afterKeyed (key : String) (ms : Nat) (onTick : msg) : Cmd msg := .fxResult "timer.afterKeyed" key (toString ms) fun _ => onTick
def Cmd.cancel (key : String) : Cmd msg := .fx "timer.cancel" key "" ""
def Cmd.setTitle (title : String) : Cmd msg := .fx "document.title" title "" ""
def Cmd.randomInt (lo hi : Int) (onInt : Int → msg) : Cmd msg := .fxResult "random.int" (toString lo) (toString hi) fun s => onInt ((s.toInt?).getD lo)
def Cmd.download (filename mime content : String) : Cmd msg := .fx "file.download" filename mime content

structure FilePick where
  name : String
  mime : String
  size : Nat
  text : String

instance : FromJson FilePick where
  fromJson j := return FilePick.mk (← fromField j "name") (← fromField j "mime") (← fromField j "size") (← fromField j "text")
def FilePick.decode (s : String) (maxDepth : Nat := 64) : Except String FilePick := (Json.parse s maxDepth).bind fromJson
def Cmd.pickFile (accept : String) (onFile : Except String FilePick → msg) : Cmd msg := .fxResult "file.pick" accept "" fun s => onFile (FilePick.decode s)

structure FileBytes where
  name : String
  mime : String
  size : Nat
  bytes : ByteArray

instance : BEq FileBytes := ⟨fun a b => a.name == b.name && a.mime == b.mime && a.size == b.size && a.bytes.data == b.bytes.data⟩
instance : FromJson FileBytes where
  fromJson j := do
    if let .ok (e : String) := fromField j "error" then return ← .error e
    return FileBytes.mk (← fromField j "name") (← fromField j "mime") (← fromField j "size") (← Base64.decode (← fromField j "base64"))
def FileBytes.decode (s : String) (maxDepth : Nat := 64) : Except String FileBytes := (Json.parse s maxDepth).bind fromJson
def Cmd.pickFileBytes (accept : String) (maxBytes : Nat := 10 * 1024 * 1024) (onFile : Except String FileBytes → msg) : Cmd msg :=
  .fxResult "file.pickBytes" accept (toString maxBytes) fun s => onFile (FileBytes.decode s)

def dispatchPorts (handlers : Array (String × (String → Option msg))) (name payload : String) : Option msg :=
  (handlers.find? (·.1 == name)).bind (·.2 payload)

end Qed
