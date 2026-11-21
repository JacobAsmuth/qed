import Qed.Server.Prim
import Qed.Server.Http
import Qed.Server.Net
import Qed.Proto
import Qed.Json

open System (FilePath)
open Qed.Server
open Qed.Server.Http

namespace Tests.Native

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a,    .ok b    => a == b
    | .error e, .error f => e == f
    | _,        _        => false

instance : BEq ByteArray where
  beq a b := a.data == b.data

instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray({b.size} bytes)"

structure TestChecker where
  name  : String
  state : IO.Ref (Nat × Nat)

def mkChecker (name : String) : IO TestChecker := do
  return { name, state := ← IO.mkRef (0, 0) }

def TestChecker.check (c : TestChecker) (label : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    c.state.modify fun (p, f) => (p + 1, f)
  else
    c.state.modify fun (p, f) => (p, f + 1)
    let extra := if detail.isEmpty then "" else s!": {detail}"
    IO.eprintln s!"  FAIL  {label}{extra}"

def TestChecker.checkEq {α : Type} [BEq α] [Repr α] (c : TestChecker) (label : String)
    (got want : α) : IO Unit := do
  if got == want then
    c.state.modify fun (p, f) => (p + 1, f)
  else
    c.state.modify fun (p, f) => (p, f + 1)
    IO.eprintln s!"  FAIL  {label}: got {reprStr got}, want {reprStr want}"

def TestChecker.finish (c : TestChecker) : IO Bool := do
  let (passed, failed) ← c.state.get
  if failed == 0 then
    IO.println s!"  ✓ {c.name} ({passed})"
    return true
  else
    IO.eprintln s!"  ✗ {c.name}: {failed} failed ({passed} passed)"
    return false

/-- Runs an external command and returns `(exitCode, stdout, stderr)`. -/
def runCmd (cmd : String) (args : Array String) (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd, args, cwd, env }
  return (out.exitCode, out.stdout, out.stderr)

def qedBinPath : IO String := do
  let cwd ← IO.currentDir
  return (cwd / ".lake" / "build" / "bin" / "qed").toString

def qedjsBinPath : IO String := do
  let cwd ← IO.currentDir
  return (cwd / ".lake" / "build" / "bin" / "qedjs").toString

def getLeanPath : IO String := do
  if let some lp ← IO.getEnv "LEAN_PATH" then
    if !lp.isEmpty then return lp
  let (code, out, _) ← runCmd "lake" #["env", "printenv", "LEAN_PATH"]
  if code == 0 then return out.trimAscii.toString
  return ""

/-- Builds a Qed module in dev mode into `.qed/test/<webRoot>` and returns the output directory. -/
def buildDevApp (webRoot : String) : IO (Option String) := do
  let cwd ← IO.currentDir
  let outDir := (cwd / ".qed" / "test" / webRoot).toString
  let qed ← qedBinPath
  let (code, out, err) ← runCmd qed #["build", "--dev"] (cwd := some cwd) (env := #[
    ("QED_HOME", some cwd.toString),
    ("QED_WEB_ROOT", some webRoot),
    ("QED_OUT_DIR", some outDir),
    ("QED_SKIP_VERIFY", some "1"),
    ("QED_PREBUILT", some "1")
  ])
  if code != 0 then
    IO.eprintln s!"buildDevApp({webRoot}) failed (exit {code}):\n{out}\n{err}"
    return none
  return some outDir

/-- Verifies `qedjs --check-externs` blocks each server/database declaration from entering client JS. -/
def checkLeakGate (c : TestChecker) (modName : String) (decls : Array String) : IO Unit := do
  let cwd ← IO.currentDir
  let qedjs ← qedjsBinPath
  let rtPath := (cwd / "runtime" / "qed_rt.mjs").toString
  let lp ← getLeanPath
  for decl in decls do
    let (code, out, err) ← runCmd qedjs #["--check-externs", rtPath, modName, "--", decl]
      (cwd := some cwd) (env := #[("LEAN_PATH", some lp)])
    let combined := out ++ err
    let blocked := code != 0 && combined.contains "client bundle leak gate"
    c.check s!"leak gate blocks {decl}" blocked s!"exit={code}, out={combined.take 160}"

def signSessionToken (secret userId : String) : IO String := do
  let mac ← Prim.hmacSha256 secret.toUTF8 userId.toUTF8
  return s!"{userId}.{Qed.Proto.encodeHex mac}"

def signExpiringSessionToken (secret userId : String) (expSec : Nat) : IO String := do
  let payload := s!"v1.{expSec}.{userId}"
  let mac ← Prim.hmacSha256 secret.toUTF8 payload.toUTF8
  return s!"{payload}.{Qed.Proto.encodeHex mac}"

def findSubBytes (hay needle : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  if needle.size == 0 || start + needle.size > hay.size then return none
  for i in [start : hay.size - needle.size + 1] do
    let mut matched := true
    for j in [0 : needle.size] do
      if hay[i + j]! != needle[j]! then
        matched := false
        break
    if matched then return some i
  return none

/-- Reads all bytes from a connected socket until EOF. -/
partial def readAllSocket (handle : UInt64) (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  match ← Prim.outboundReadSome handle 65536 with
  | .error _ => return acc
  | .ok chunk =>
      if chunk.size == 0 then return acc
      readAllSocket handle (acc ++ chunk)

/-- Sends raw bytes over loopback TCP (`127.0.0.1:<port>`) and returns the full raw response. -/
def rawTcpReq (port : UInt16) (rawReq : ByteArray) : IO (Except String ByteArray) := do
  match ← Prim.outboundAcquire 0 "127.0.0.1" port 0 (fun _ => false) with
  | .error e => return .error e
  | .ok (hNat, _) =>
      let handle := hNat.toUInt64
      let res ← do
        match ← Prim.outboundWriteAll handle rawReq with
        | .error e => pure (.error e)
        | .ok () =>
            let resp ← readAllSocket handle
            pure (.ok resp)
      Prim.outboundRelease handle 0
      return res

structure HttpResp where
  status  : Nat
  headers : Array (String × String)
  body    : ByteArray

def HttpResp.header? (r : HttpResp) (name : String) : Option String :=
  let want := name.toLower
  (r.headers.find? fun (k, _) => k.toLower == want).map Prod.snd

def HttpResp.bodyStr (r : HttpResp) : String :=
  (String.fromUTF8? r.body).getD ""

/-- Parses a raw HTTP/1.x response (`Connection: close` framing). -/
def parseHttpResp (raw : ByteArray) : Except String HttpResp := do
  let sep := "\r\n\r\n".toUTF8
  let some hdrEnd := findSubBytes raw sep
    | .error "missing CRLFCRLF in HTTP response"
  let headStr := (String.fromUTF8? (raw.extract 0 hdrEnd)).getD ""
  let body := raw.extract (hdrEnd + 4) raw.size
  let lines := headStr.splitOn "\r\n"
  let statusLine := lines.headD ""
  let parts := statusLine.splitOn " "
  let status := (parts.getD 1 "0").toNat?.getD 0
  let mut hdrs : Array (String × String) := #[]
  for l in lines.drop 1 do
    match l.splitOn ":" with
    | k :: rest => hdrs := hdrs.push (k.trimAscii.toString, (String.intercalate ":" rest).trimAscii.toString)
    | _ => pure ()
  return { status, headers := hdrs, body }

/-- Performs a loopback HTTP/1.1 request with `Connection: close`. -/
def httpReq (port : UInt16) (method path : String)
    (headers : Array (String × String) := #[]) (body : ByteArray := ByteArray.empty) :
    IO (Except String HttpResp) := do
  let mut reqHead := s!"{method} {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n"
  if body.size > 0 || method == "POST" then
    reqHead := reqHead ++ s!"Content-Length: {body.size}\r\n"
  for (k, v) in headers do
    reqHead := reqHead ++ s!"{k}: {v}\r\n"
  reqHead := reqHead ++ "\r\n"
  match ← rawTcpReq port (reqHead.toUTF8 ++ body) with
  | .error e => return .error e
  | .ok raw  => return parseHttpResp raw

def waitHealth (port : UInt16) (timeoutMs : Nat := 5000) : IO Bool := do
  let deadline := (← Prim.nowMs).toNat + timeoutMs
  let rec loop : Nat → IO Bool
    | 0 => return false
    | fuel + 1 => do
        match ← httpReq port "GET" "/_qed/health" with
        | .ok r => if r.status == 200 then return true
        | .error _ => pure ()
        if (← Prim.nowMs).toNat >= deadline then return false
        IO.sleep 30
        loop fuel
  loop 200

structure NativeServerProc where
  port    : UInt16
  dir     : String
  cmd     : String
  args    : Array String
  env     : Array (String × Option String)
  childRef : IO.Ref (IO.Process.Child ⟨.null, .null, .null⟩)

def NativeServerProc.stop (s : NativeServerProc) : IO Unit := do
  let child ← s.childRef.get
  try child.kill catch _ => pure ()
  try discard <| child.wait catch _ => pure ()

def NativeServerProc.restart (s : NativeServerProc) : IO Bool := do
  s.stop
  IO.sleep 50
  let next ← IO.Process.spawn {
    cmd := s.cmd, args := s.args, env := s.env,
    stdin := .null, stdout := .null, stderr := .null
  }
  s.childRef.set next
  waitHealth s.port

def startNativeBin (bin : String) (args : Array String) (port : UInt16)
    (extraEnv : Array (String × Option String) := #[]) : IO (NativeServerProc × Bool) := do
  let child ← IO.Process.spawn {
    cmd := bin, args, env := extraEnv,
    stdin := .null, stdout := .null, stderr := .null
  }
  let ref ← IO.mkRef child
  let proc : NativeServerProc := { port, dir := "", cmd := bin, args, env := extraEnv, childRef := ref }
  let ok ← waitHealth port
  return (proc, ok)

def startNativeServer (dir : String) (extraEnv : Array (String × Option String) := #[])
    (dev : Bool := true) : IO (NativeServerProc × Bool) := do
  let port ← Prim.freePort
  let args := #[dir, toString port] ++ (if dev then #["--dev"] else #[])
  startNativeBin (dir ++ "/server") args port extraEnv

/-- Reads one HTTP/1.1 request (headers + `Content-Length` body) from an accepted socket handle. -/
partial def readOneHttpReq (handle : UInt64) : IO (Option (String × String × Array (String × String) × ByteArray)) := do
  let sep := "\r\n\r\n".toUTF8
  let rec readHead (buf : ByteArray) : IO (Option (ByteArray × Nat)) := do
    if let some idx := findSubBytes buf sep then
      return some (buf, idx)
    match ← Prim.outboundReadSome handle 16384 with
    | .error _ => return none
    | .ok chunk =>
        if chunk.size == 0 then return none
        readHead (buf ++ chunk)
  let some (buf, hdrEnd) ← readHead ByteArray.empty | return none
  let headStr := (String.fromUTF8? (buf.extract 0 hdrEnd)).getD ""
  let lines := headStr.splitOn "\r\n"
  let reqLine := (lines.headD "").splitOn " "
  let method := reqLine.getD 0 ""
  let target := reqLine.getD 1 "/"
  let mut hdrs : Array (String × String) := #[]
  let mut contentLen : Nat := 0
  for l in lines.drop 1 do
    match l.splitOn ":" with
    | k :: rest =>
        let kn := k.trimAscii.toString
        let kv := (String.intercalate ":" rest).trimAscii.toString
        hdrs := hdrs.push (kn, kv)
        if kn.toLower == "content-length" then
          contentLen := kv.toNat?.getD 0
    | _ => pure ()
  let mut body := buf.extract (hdrEnd + 4) buf.size
  while body.size < contentLen do
    match ← Prim.outboundReadSome handle 16384 with
    | .error _ => break
    | .ok chunk =>
        if chunk.size == 0 then break
        body := body ++ chunk
  return some (method, target, hdrs, body.extract 0 contentLen)

def makeTempDir (prefixStr : String) : IO String := do
  let rnd ← Prim.randomHex 8
  let dir := s!"/tmp/{prefixStr}-{rnd}"
  IO.FS.createDirAll dir
  return dir

def rmRf (path : String) : IO Unit := do
  discard <| runCmd "rm" #["-rf", path]

end Tests.Native
