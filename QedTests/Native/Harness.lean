import Qed.Server.Prim
import Qed.Server.Http
import Qed.Server.Net
import Qed.Proto
import Qed.Json
open System (FilePath)
open Qed.Server Qed.Server.Http

namespace QedTests.Native
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where beq | .ok a, .ok b => a == b | .error e, .error f => e == f | _, _ => false
instance : BEq ByteArray where beq a b := a.data == b.data
instance : Repr ByteArray where reprPrec b _ := s!"ByteArray({b.size} bytes)"

structure TestChecker where
  name  : String
  state : IO.Ref (Nat × Nat)
class ErrMsg (ε : Type) where errMsg : ε → String
instance : ErrMsg String where errMsg := id
instance : ErrMsg ApiError where errMsg := ApiError.message

def mkChecker (name : String) : IO TestChecker := return { name, state := ← IO.mkRef (0, 0) }
def TestChecker.check (c : TestChecker) (label : String) (ok : Bool) (detail : String := "") : IO Unit := do
  c.state.modify fun (p, f) => if ok then (p + 1, f) else (p, f + 1)
  if !ok then IO.eprintln s!"  FAIL  {label}{if detail.isEmpty then "" else s!": {detail}"}"
def TestChecker.checkEq {α : Type} [BEq α] [Repr α] (c : TestChecker) (label : String) (got want : α) : IO Unit := c.check label (got == want) s!"got {reprStr got}, want {reprStr want}"
def TestChecker.expectOk {ε α : Type} [ErrMsg ε] (c : TestChecker) (label : String) (res : Except ε α) (k : α → IO Unit) : IO Unit := match res with | .ok v => k v | .error e => c.check label false (ErrMsg.errMsg e)
def TestChecker.checkOkBy {ε α β : Type} [ErrMsg ε] [BEq β] [Repr β] (c : TestChecker) (label : String) (res : Except ε α) (f : α → β) (want : β) : IO Unit :=
  c.expectOk label res fun v => c.checkEq label (f v) want
def TestChecker.checkErrCode {α : Type} (c : TestChecker) (label : String) (res : Except ApiError α) (wantCode : Nat) (wantMsg? : Option String := none) : IO Unit :=
  match res with
  | .error e => if let some m := wantMsg? then c.checkEq label (e.code, e.message) (wantCode, m) else c.checkEq label e.code wantCode
  | .ok _ => c.check label false s!"expected ApiError {wantCode}, got ok"
def TestChecker.checkErrContains {ε α : Type} [ErrMsg ε] (c : TestChecker) (label : String) (res : Except ε α) (sub : String) : IO Unit :=
  match res with | .error e => let m := ErrMsg.errMsg e; c.check label (m.contains sub) m | .ok _ => c.check label false s!"expected error containing `{sub}`, got ok"
def TestChecker.finish (c : TestChecker) : IO Bool := do
  let (p, f) ← c.state.get; if f == 0 then IO.println s!"  ✓ {c.name} ({p})"; return true
  IO.eprintln s!"  ✗ {c.name}: {f} failed ({p} passed)"; return false

def decodeJson (α : Type) [Qed.FromJson α] (s : String) : Except String α := Qed.Json.parse s >>= Qed.fromJson
def jsonRt {α : Type} [Qed.ToJson α] [Qed.FromJson α] [BEq α] (x : α) : Bool := decodeJson α (Qed.toJson x).render == .ok x
def badJson (α : Type) [Qed.FromJson α] (s : String) : Bool := !(decodeJson α s).isOk

def runCmd (cmd : String) (args : Array String) (cwd : Option FilePath := none) (env : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let o ← IO.Process.output { cmd, args, cwd, env }; return (o.exitCode, o.stdout, o.stderr)
private def buildBinPath (name : String) : IO String := return ((← IO.currentDir) / ".lake" / "build" / "bin" / name).toString
def qedBinPath : IO String := buildBinPath "qed"
def qedjsBinPath : IO String := buildBinPath "qedjs"
def getLeanPath : IO String := do
  if let some lp ← IO.getEnv "LEAN_PATH" then if !lp.isEmpty then return lp
  let (code, out, _) ← runCmd "lake" #["env", "printenv", "LEAN_PATH"]; return if code == 0 then out.trimAscii.toString else ""
private def buildDevApp (webRoot : String) : IO (Option String) := do
  let cwd ← IO.currentDir; let outDir := (cwd / ".qed" / "test" / webRoot).toString
  let (code, out, err) ← runCmd (← qedBinPath) #["build", "--dev"] (cwd := some cwd)
    (env := #[("QED_HOME", some cwd.toString), ("QED_WEB_ROOT", some webRoot), ("QED_OUT_DIR", some outDir), ("QED_SKIP_VERIFY", some "1"), ("QED_PREBUILT", some "1")])
  if code != 0 then IO.eprintln s!"buildDevApp({webRoot}) failed (exit {code}):\n{out}\n{err}"; return none
  return some outDir
def withDevApp (c : TestChecker) (webRoot : String) (k : String → IO Unit) : IO Unit := do
  match ← buildDevApp webRoot with | some dir => k dir | none => c.check s!"buildDevApp {webRoot}" false
def checkLeakGate (c : TestChecker) (modName : String) (decls : Array String) : IO Unit := do
  let cwd ← IO.currentDir; let (qedjs, rtPath, lp) := (← qedjsBinPath, (cwd / "runtime" / "qed_rt.mjs").toString, ← getLeanPath)
  for decl in decls do
    let (code, out, err) ← runCmd qedjs #["--check-externs", rtPath, modName, "--", decl] (cwd := some cwd) (env := #[("LEAN_PATH", some lp)])
    let comb := out ++ err; c.check s!"leak gate blocks {decl}" (code != 0 && comb.contains "client bundle leak gate") s!"exit={code}, out={comb.take 160}"

private def signHmac (secret payload : String) : IO String := return s!"{payload}.{Qed.Proto.encodeHex (← Prim.hmacSha256 secret.toUTF8 payload.toUTF8)}"
def signSessionToken (secret userId : String) : IO String := signHmac secret userId
def signExpiringSessionToken (secret userId : String) (expSec : Nat) : IO String := signHmac secret s!"v1.{expSec}.{userId}"
def utf8Str (b : ByteArray) : String := (String.fromUTF8? b).getD ""
def dropChars (s : String) (n : Nat := 1) : String := String.ofList (s.toList.drop n)
def getHeader? (hdrs : Array (String × String)) (name : String) : Option String := let w := name.toLower; (hdrs.find? (·.1.toLower == w)).map Prod.snd
def jsonResp (st : Nat := 200) (j : Qed.Json := .obj []) : Nat × String × ByteArray := (st, "application/json", (Qed.Json.render j).toUTF8)
def jsonStrResp (st : Nat) (s : String) : Nat × String × ByteArray := (st, "application/json", s.toUTF8)
def txtResp (st : Nat) (s : String) : Nat × String × ByteArray := (st, "text/plain", s.toUTF8)
def jsonErrResp (st : Nat) (msg : String) : Nat × String × ByteArray := jsonResp st (.obj [("error", .str msg)])
def splitPathQuery (target : String) : String × String := match target.splitOn "?" with | [] => ("/", "") | [p] => (p, "") | p :: qs => (p, String.intercalate "?" qs)

private def readSocketUntil (handle : UInt64) (buf : ByteArray) (done : ByteArray → Bool) (maxReads : Nat := 10000) (chunkSize : UInt32 := 16384) : IO (Option ByteArray) := do
  let mut b := buf
  for _ in [0 : maxReads] do
    if done b then return some b
    match ← Prim.outboundReadSome handle chunkSize with | .ok c => if c.size == 0 then return none else b := b ++ c | .error _ => return none
  return if done b then some b else none
def readHeadUntilCrlfCrlf (handle : UInt64) (maxReads : Nat := 64) : IO (Option (ByteArray × Nat)) := do
  return (← readSocketUntil handle ByteArray.empty (fun b => (Net.findCrlfCrlf b).isSome) maxReads).bind fun b => (Net.findCrlfCrlf b).map (b, ·)
def readExact (handle : UInt64) (buf : ByteArray) (n : Nat) : IO (Option ByteArray) := readSocketUntil handle buf (·.size >= n)
private def readAllSocket (handle : UInt64) : IO ByteArray := do
  let mut acc := ByteArray.empty
  for _ in [0 : 100000] do
    match ← Prim.outboundReadSome handle 65536 with | .ok c => if c.size == 0 then break else acc := acc ++ c | .error _ => break
  return acc
def rawTcpReq (port : UInt16) (rawReq : ByteArray) : IO (Except String ByteArray) := do
  match ← Prim.outboundAcquire 0 "127.0.0.1" port 0 (fun _ => false) with
  | .error e => return .error e
  | .ok (hNat, _) =>
      let h := hNat.toUInt64
      let res ← match ← Prim.outboundWriteAll h rawReq with | .error e => pure (.error e) | .ok () => pure (.ok (← readAllSocket h))
      Prim.outboundRelease h 0; return res

structure HttpResp where
  status  : Nat
  headers : Array (String × String)
  body    : ByteArray

def HttpResp.header? (r : HttpResp) (name : String) : Option String := getHeader? r.headers name
def HttpResp.bodyStr (r : HttpResp) : String := utf8Str r.body
def HttpResp.cookies (r : HttpResp) : List String := r.headers.foldl (init := []) fun acc (k, v) => if k.toLower == "set-cookie" then acc ++ [v] else acc
def HttpResp.cookie? (r : HttpResp) (name : String) : Option String := r.cookies.findSome? fun sc => let p := ((sc.splitOn ";").headD "").trimAscii.toString; if p.startsWith (name ++ "=") then some p else none
def HttpResp.checkCookieFlag (r : HttpResp) (c : TestChecker) (label : String) (substrs : List String) : IO Unit := c.check label (r.cookies.any fun s => substrs.all (s.contains ·)) ((r.header? "set-cookie").getD "")
def HttpResp.checkDefaultCsp (r : HttpResp) (c : TestChecker) (label : String) : IO Unit := let csp := (r.header? "content-security-policy").getD ""; c.check label (["default-src 'self'", "script-src 'self'", "object-src 'none'"].all (csp.contains ·)) csp
def HttpResp.check (r : HttpResp) (c : TestChecker) (label : String) (status? : Option Nat := none) (headers : List (String × Option String) := [])
    (bodyEq? : Option String := none) (contains : List String := []) (notContains : List String := []) : IO Unit := do
  if let some st := status? then c.checkEq s!"{label} status {st}" r.status st
  for (k, want) in headers do c.checkEq s!"{label} header {k}" (r.header? k) want
  if let some b := bodyEq? then c.checkEq s!"{label} body" r.bodyStr b
  for sub in contains do c.check s!"{label} contains {sub}" (r.bodyStr.contains sub) r.bodyStr
  for sub in notContains do c.check s!"{label} omits {sub}" (!r.bodyStr.contains sub) r.bodyStr

def parseHttpResp (raw : ByteArray) : Except String HttpResp := do
  let some hdrEnd := Net.findCrlfCrlf raw | .error "missing CRLFCRLF in HTTP response"
  let head ← Net.parseHttpResponseHead (raw.extract 0 hdrEnd)
  return { status := head.status, headers := head.headers, body := raw.extract (hdrEnd + 4) raw.size }
def httpReq (port : UInt16) (method path : String) (headers : Array (String × String) := #[]) (body : ByteArray := ByteArray.empty) : IO (Except String HttpResp) := do
  let cl := if body.size > 0 || method == "POST" then s!"Content-Length: {body.size}\r\n" else ""
  let hdrStr := headers.foldl (init := "") fun acc (k, v) => acc ++ s!"{k}: {v}\r\n"
  return (← rawTcpReq port (s!"{method} {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n{cl}{hdrStr}\r\n".toUTF8 ++ body)).bind parseHttpResp
def httpRpc (port : UInt16) (srv fn : String) (body : ByteArray := ByteArray.empty) (tok? : Option String := none) (extraHdrs : Array (String × String) := #[]) : IO (Except String HttpResp) :=
  httpReq port "POST" s!"/_qed/rpc/{srv}/{fn}" (#[("Content-Type", "application/x-protobuf")] ++ (tok?.map (fun t => #[("Authorization", s!"Bearer {t}")]) |>.getD #[]) ++ extraHdrs) body

def TestChecker.checkStatus (c : TestChecker) (label : String) (res : Except String HttpResp) (want : Nat) : IO Unit := c.expectOk label res fun r => c.checkEq label r.status want
def TestChecker.checkHttp (c : TestChecker) (label : String) (res : Except String HttpResp) (status? : Option Nat := some 200) (headers : List (String × Option String) := [])
    (bodyEq? : Option String := none) (contains : List String := []) (notContains : List String := []) (extra : HttpResp → IO Unit := fun _ => pure ()) : IO Unit :=
  c.expectOk label res fun r => do r.check c label status? headers bodyEq? contains notContains; extra r
def TestChecker.checkRaw400 (c : TestChecker) (port : UInt16) (label raw : String) : IO Unit := do
  c.expectOk label (← rawTcpReq port raw.toUTF8) fun resp => c.check label ((utf8Str resp).startsWith "HTTP/1.1 400 ")
def TestChecker.checkRawNoLeak (c : TestChecker) (port : UInt16) (label reqPath forbidden : String) : IO Unit := do
  c.expectOk label (← rawTcpReq port s!"GET {reqPath} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n".toUTF8) fun resp => let s := utf8Str resp; c.check label (!s.contains forbidden) s

private def TestChecker.checkRpcDomain {ε E α : Type} [ErrMsg ε] [Qed.FromProto E] [Qed.FromProto α] (c : TestChecker) (label : String) (res : Except ε ByteArray) (k : Except (Qed.RpcDomainError E) α → IO Unit) : IO Unit :=
  c.expectOk label res fun bs => c.expectOk label (Qed.Proto.decode (α := Except (Qed.RpcDomainError E) α) bs) k
def TestChecker.checkRpcDomainOk {ε E α : Type} [ErrMsg ε] [Qed.FromProto E] [Qed.FromProto α] (c : TestChecker) (label : String) (res : Except ε ByteArray) (k : α → IO Unit) : IO Unit :=
  c.checkRpcDomain (E := E) (α := α) label res fun | .ok v => k v | .error err => c.check label false s!"unexpected domain error: {err.message}"
def TestChecker.checkRpcDomainErr {ε E α : Type} [ErrMsg ε] [Qed.FromProto E] [Qed.FromProto α] (c : TestChecker) (label : String) (res : Except ε ByteArray) (pred : Qed.RpcDomainError E → Bool := fun _ => true) : IO Unit :=
  c.checkRpcDomain (E := E) (α := α) label res fun | .error err => c.check label (pred err) s!"got domain error: {err.message}" | .ok _ => c.check label false "expected domain error, got ok"

def TestChecker.checkJsonPath (c : TestChecker) (label : String) (j : Qed.Json) (path : String) (pred : Qed.Json → Bool) (detail : String := "") : IO Unit :=
  match j.atPath path with | some v => c.check label (pred v) (if detail.isEmpty then Qed.Json.render v else detail) | none => c.check label false s!"missing JSON path `{path}`"
def TestChecker.checkJsonArr (c : TestChecker) (label : String) (j : Qed.Json) (path : String) (pred : List Qed.Json → Bool) (detail : String := "") : IO Unit := c.checkJsonPath label j path (fun | .arr xs => pred xs | _ => false) detail
def TestChecker.checkJsonStr (c : TestChecker) (label : String) (j : Qed.Json) (path want : String) : IO Unit := c.checkEq label (j.pathStr? path) (some want)
def TestChecker.checkJsonInt (c : TestChecker) (label : String) (j : Qed.Json) (path : String) (want : Int) : IO Unit := c.checkEq label (((j.atPath path).bind (·.num?)).bind (·.toInt?)) (some want)

def TestChecker.checkProtoBy {ε α β : Type} [ErrMsg ε] [Qed.FromProto α] [BEq β] [Repr β] (c : TestChecker) (label : String) (res : Except ε ByteArray) (f : α → β) (want : β) : IO Unit :=
  c.expectOk label res fun bs => c.expectOk label (Qed.Proto.decode (α := α) bs) fun v => c.checkEq label (f v) want
def TestChecker.checkProto {ε α : Type} [ErrMsg ε] [Qed.FromProto α] [BEq α] [Repr α] (c : TestChecker) (label : String) (res : Except ε ByteArray) (want : α) : IO Unit := c.checkProtoBy label res id want
def TestChecker.checkRpcProtoBy {α β : Type} [Qed.FromProto α] [BEq β] [Repr β] (c : TestChecker) (label : String) (res : Except String HttpResp) (f : α → β) (want : β) : IO Unit := c.checkProtoBy label (res.map (·.body)) f want
def TestChecker.checkRpcProto {α : Type} [Qed.FromProto α] [BEq α] [Repr α] (c : TestChecker) (label : String) (res : Except String HttpResp) (want : α) : IO Unit := c.checkProtoBy label (res.map (·.body)) id want

private def waitHealth (port : UInt16) (timeoutMs : Nat := 5000) : IO Bool := do
  let deadline := (← Prim.nowMs).toNat + timeoutMs
  for _ in [0 : 200] do
    if let .ok r ← httpReq port "GET" "/_qed/health" then if r.status == 200 then return true
    if (← Prim.nowMs).toNat >= deadline then return false else IO.sleep 30
  return false
private def spawnNullProc (cmd : String) (args : Array String) (env : Array (String × Option String)) : IO (IO.Process.Child ⟨.null, .null, .null⟩) :=
  IO.Process.spawn { cmd, args, env, stdin := .null, stdout := .null, stderr := .null }

structure NativeServerProc where
  port     : UInt16
  cmd      : String
  args     : Array String
  env      : Array (String × Option String)
  childRef : IO.Ref (IO.Process.Child ⟨.null, .null, .null⟩)

def NativeServerProc.stop (s : NativeServerProc) : IO Unit := do let ch ← s.childRef.get; try ch.kill catch _ => pure (); try discard <| ch.wait catch _ => pure ()
def NativeServerProc.restart (s : NativeServerProc) : IO Bool := do s.stop; IO.sleep 50; s.childRef.set (← spawnNullProc s.cmd s.args s.env); waitHealth s.port
def withNativeBin (c : TestChecker) (label bin : String) (args : Array String) (port : UInt16) (extraEnv : Array (String × Option String) := #[]) (k : NativeServerProc → IO Unit) : IO Unit := do
  let srv : NativeServerProc := { port, cmd := bin, args, env := extraEnv, childRef := ← IO.mkRef (← spawnNullProc bin args extraEnv) }
  try let ok ← waitHealth port; c.check label ok; if ok then k srv finally srv.stop
def withNativeServer (c : TestChecker) (label dir : String) (extraEnv : Array (String × Option String) := #[]) (dev : Bool := true) (k : NativeServerProc → IO Unit) : IO Unit := do
  let port ← Prim.freePort; withNativeBin c label (dir ++ "/server") (#[dir, toString port] ++ if dev then #["--dev"] else #[]) port extraEnv k
def withMockServer {α : Type} (c : TestChecker) (label : String) (start : IO (Except String α)) (stop : α → IO Unit) (k : α → IO Unit) : IO Unit := do c.expectOk label (← start) fun m => try k m finally stop m
def startMockTcpServer (onConn : UInt64 → IO Unit) (concurrent : Bool := false) : IO (Except String (UInt16 × IO Unit)) := do
  match ← Prim.tcpListen 0 with
  | .error e => return .error e
  | .ok (lid, port) =>
      let runningRef ← IO.mkRef true; let handle (conn : UInt64) : IO Unit := do try onConn conn catch _ => pure (); Prim.outboundRelease conn 0
      discard <| IO.asTask (prio := .dedicated) do
        while ← runningRef.get do
          match ← Prim.tcpAccept lid 100 with | .error "timeout" => pure () | .error _ => break | .ok conn => if concurrent then discard <| IO.asTask (prio := .dedicated) (handle conn) else handle conn
      return .ok (port, do runningRef.set false; Prim.tcpCloseListener lid)
def startMockHttpServer (onReq : String → String → Array (String × String) → ByteArray → IO (Nat × String × ByteArray)) : IO (Except String (UInt16 × IO Unit)) :=
  startMockTcpServer fun conn => do
    let some (buf, hdrEnd) ← readHeadUntilCrlfCrlf conn | return
    let .ok h := Http.parseRequestHead (buf.extract 0 hdrEnd) | return
    let initBody := buf.extract (hdrEnd + 4) buf.size
    let body := ((← readExact conn initBody h.contentLen).getD initBody).extract 0 h.contentLen
    let (status, ctype, respBytes) ← onReq h.method h.target h.headers body
    discard <| Prim.outboundWriteAll conn (formatHttpResponse status ctype respBytes false false true)

def rmRf (path : String) : IO Unit := discard <| runCmd "rm" #["-rf", path]
def withTempDir {α : Type} (prefixStr : String) (k : String → IO α) : IO α := do let dir := s!"/tmp/{prefixStr}-{← Prim.randomHex 8}"; IO.FS.createDirAll dir; try k dir finally rmRf dir
def withSymlink (target link : String) (k : IO Unit) : IO Unit := do rmRf link; discard <| runCmd "ln" #["-sf", target, link]; try k finally rmRf link
def runParallelAll (n : Nat) (f : IO Bool) : IO Bool := do
  let tasks ← (Array.range n).mapM fun _ => IO.asTask (prio := .dedicated) f
  tasks.allM fun t => return (← IO.wait t).toOption == some true

end QedTests.Native
