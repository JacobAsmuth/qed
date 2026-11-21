import Qed.Html
import Qed.Date
import Qed.Proto
import Qed.Base64
import Qed.Router.Basic
import Qed.Socket.Basic

namespace Qed

inductive Cmd (msg : Type) where
  | none
  | stream (url : String) (body : String) (onChunk : String → msg) (onDone : msg)
  | now (onNow : Date → msg)
  | request (method url body : String) (onResult : Except String String → msg)
  | requestBytes (method url : String) (body : ByteArray) (onResult : Except String ByteArray → msg)
  | pushPath (url : Url)
  | batch (cmds : List (Cmd msg))
  | port (name payload : String)
  | fx (kind a b c : String)
  | fxResult (kind a b : String) (onResult : String → msg)
  | wsMuxSub (slot url channel : String) (params : ByteArray) (reconnect : Reconnect)
             (onJoin : ByteArray → msg) (onMessage : ByteArray → msg) (onStatus : SocketStatus → msg)
  | wsMuxSend (slot : String) (payload : ByteArray)
  | wsMuxUnsub (slot : String)
  | wsExtOpen (slot url : String) (isBinary : Bool) (reconnect : Reconnect)
              (onJoin : Unit → msg) (onText : String → msg) (onBytes : ByteArray → msg)
              (onStatus : SocketStatus → msg)
  | wsExtSendText (slot text : String)
  | wsExtSendBytes (slot : String) (payload : ByteArray)
  | wsExtClose (slot : String)

instance : Coe (List (Cmd msg)) (Cmd msg) := ⟨.batch⟩

mutual
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none                           => .none
  | .stream u b onChunk onDone      => .stream u b (fun c => f (onChunk c)) (f onDone)
  | .now onNow                      => .now (fun d => f (onNow d))
  | .request m u b onResult         => .request m u b (fun r => f (onResult r))
  | .requestBytes m u b onResult    => .requestBytes m u b (fun r => f (onResult r))
  | .pushPath p                     => .pushPath p
  | .batch cmds                     => .batch (Cmd.mapList f cmds)
  | .port n p                       => .port n p
  | .fx k a b c                     => .fx k a b c
  | .fxResult k a b onResult        => .fxResult k a b (fun s => f (onResult s))
  | .wsMuxSub slot url ch params rec onJoin onMsg onStatus =>
      .wsMuxSub slot url ch params rec (fun b => f (onJoin b)) (fun b => f (onMsg b)) (fun s => f (onStatus s))
  | .wsMuxSend slot payload => .wsMuxSend slot payload
  | .wsMuxUnsub slot => .wsMuxUnsub slot
  | .wsExtOpen slot url isBin rec onJoin onTxt onBin onStatus =>
      .wsExtOpen slot url isBin rec (fun u => f (onJoin u)) (fun s => f (onTxt s)) (fun b => f (onBin b)) (fun s => f (onStatus s))
  | .wsExtSendText slot text => .wsExtSendText slot text
  | .wsExtSendBytes slot payload => .wsExtSendBytes slot payload
  | .wsExtClose slot => .wsExtClose slot
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

mutual
/-- Strips HTTP/RPC data-loading commands already resolved during SSR while preserving
    client-only subscriptions (`fx`, `fxResult`, `stream`, `now`, `port`). -/
def Cmd.clientOnly : Cmd msg → Cmd msg
  | .request ..      => .none
  | .requestBytes .. => .none
  | .wsMuxSub ..     => .none
  | .wsExtOpen ..    => .none
  | .batch cmds      => .batch (Cmd.clientOnlyList cmds)
  | c                => c
def Cmd.clientOnlyList : List (Cmd msg) → List (Cmd msg)
  | []      => []
  | c :: cs => Cmd.clientOnly c :: Cmd.clientOnlyList cs
end

def httpDecode [FromJson α] (onOk : α → msg) (onErr : String → msg) :
    Except String String → msg
  | .error e   => onErr e
  | .ok   body => match (Json.parse body).bind FromJson.fromJson with
                  | .ok a    => onOk a
                  | .error e => onErr e

def protoDecode [FromProto α] (onResult : Except String α → msg) :
    Except String ByteArray → msg
  | .error e   => onResult (.error e)
  | .ok   body => onResult (Proto.decode body)

/-- Binary Protocol Buffers RPC command (`POST` with `application/x-protobuf`). -/
def Cmd.rpc [ToProto req] [FromProto resp] (url : String) (payload : req)
    (onResult : Except String resp → msg) : Cmd msg :=
  .requestBytes "POST" url (Proto.encode payload) (protoDecode onResult)

def Cmd.getJson [FromJson α] (url : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "GET" url "" (httpDecode onOk onErr)

def Cmd.postJson [FromJson α] (url body : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "POST" url body (httpDecode onOk onErr)

/-- Streams SSE chunks from a JSON-encoded request body (`POST` with `ToJson`). -/
def Cmd.streamJson [ToJson α] (url : String) (body : α) (onChunk : String → msg) (onDone : msg) : Cmd msg :=
  .stream url (Json.render (toJson body)) onChunk onDone

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

/-- Binary file upload payload returned by `Cmd.pickFileBytes`. -/
structure FileBytes where
  name  : String
  mime  : String
  size  : Nat
  bytes : ByteArray

instance : BEq FileBytes where
  beq a b := a.name == b.name && a.mime == b.mime && a.size == b.size && a.bytes.data == b.bytes.data

instance : FromJson FileBytes where
  fromJson j := do
    match (fromField j "error" : Except String String) with
    | .ok errMsg => .error errMsg
    | .error _   =>
        let name  ← fromField j "name"
        let mime  ← fromField j "mime"
        let size  ← fromField j "size"
        let b64   ← (fromField j "base64" : Except String String)
        let bytes ← Base64.decode b64
        return { name, mime, size, bytes }

def FileBytes.decode (s : String) (maxDepth : Nat := 64) : Except String FileBytes :=
  (Json.parse s maxDepth).bind fromJson

/-- Opens the native browser file picker and reads the selected file as raw binary `ByteArray`,
    enforcing `maxBytes` client-side (default 10 MiB) and decoding the base64 transfer payload
    with Qed's verified `Base64.decode`. -/
def Cmd.pickFileBytes (accept : String) (maxBytes : Nat := 10 * 1024 * 1024)
    (onFile : Except String FileBytes → msg) : Cmd msg :=
  .fxResult "file.pickBytes" accept (toString maxBytes) fun s => onFile (FileBytes.decode s)

def dispatchPorts (handlers : Array (String × (String → Option msg))) (name payload : String) : Option msg :=
  match handlers.find? (fun h => h.1 == name) with
  | some h => h.2 payload
  | none   => none

end Qed
