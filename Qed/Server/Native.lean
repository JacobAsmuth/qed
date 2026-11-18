import Lean
import Qed.Ssr
import Qed.Server.Core
import Qed.Server.Elab
import Qed.Server.Prim

namespace Qed.Server.Native

/-! ## Constant-Time HMAC Session & Bearer Token Verification -/

private def trimWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

private def stripTrailingSlash (s : String) : String :=
  if s.endsWith "/" then String.ofList (s.toList.take (s.length - 1)) else s

private def constTimeXorLoop (a b : ByteArray) (i : Nat) (acc : UInt8) : UInt8 :=
  if h : i < a.size then
    if hb : i < b.size then
      constTimeXorLoop a b (i + 1) (acc ||| (a[i] ^^^ b[i]))
    else
      1
  else
    acc
termination_by a.size - i

/-- Constant-time equality over two byte buffers of equal length. -/
def constTimeEqBytes (a b : ByteArray) : Bool :=
  if a.size != b.size then false
  else constTimeXorLoop a b 0 0 == 0

/-- Signs `userId` as `<userId>.<hmacSha256Hex>` using `secret`. -/
def signUserToken (secret userId : String) : IO String := do
  let mac ← Prim.hmacSha256 secret.toUTF8 userId.toUTF8
  return userId ++ "." ++ Proto.encodeHex mac

/-- Verifies `<userId>.<hmacSha256Hex>` in constant time and returns `some userId` iff valid. -/
def verifyUserToken (secret token : String) : IO (Option String) := do
  let parts := token.splitOn "."
  match parts.reverse with
  | [] | [_] => return none
  | sigHex :: revUidParts =>
      let uid := String.intercalate "." revUidParts.reverse
      if uid.isEmpty || sigHex.length != 64 then
        return none
      match Proto.decodeHex sigHex with
      | .error _ => return none
      | .ok sigBytes =>
          let expected ← Prim.hmacSha256 secret.toUTF8 uid.toUTF8
          if constTimeEqBytes sigBytes expected then
            return some uid
          else
            return none

/-! ## Inbound `RequestCtx` Extraction -/

private def parseCookiePairs (raw : String) : List (String × String) :=
  (raw.splitOn ";").foldl (fun acc seg =>
    let t := trimWs seg
    if t.isEmpty then acc
    else
      match t.splitOn "=" with
      | []       => acc
      | [k]      => acc ++ [(trimWs k, "")]
      | k :: vs  => acc ++ [(trimWs k, trimWs (String.intercalate "=" vs))]) []

private def extractBearer (authHdr : String) : Option String :=
  let t := trimWs authHdr
  if t.length > 7 && (String.ofList (t.toList.take 7)).toLower == "bearer " then
    let tok := trimWs (String.ofList (t.toList.drop 7))
    if tok.isEmpty then none else some tok
  else
    none

def buildRequestCtx (headers : Array (String × String)) (clientIp : String) : IO RequestCtx := do
  let hdrList := headers.toList
  let cookies := hdrList.foldl (fun acc (k, v) =>
    if k.toLower == "cookie" then acc ++ parseCookiePairs v else acc) []
  let bearer? := hdrList.findSome? fun (k, v) =>
    if k.toLower == "authorization" then extractBearer v else none
  let sessionCookie? := (cookies.find? fun (k, _) => k == "qed_session").map Prod.snd
  let authSecret? ← Prim.getEnv "QED_AUTH_SECRET"
  let userId? ← match authSecret? with
    | some sec =>
        if sec.isEmpty then pure none
        else match bearer?.orElse (fun _ => sessionCookie?) with
          | some tok => verifyUserToken sec tok
          | none     => pure none
    | none => pure none
  return {
    headers     := hdrList
    cookies     := cookies
    bearerToken := bearer?
    userId      := userId?
    clientIp    := clientIp
  }

/-! ## Native `MonadServer IO` & `MonadAtomic σ IO` Instances -/

private def resolveBaseOrigin (req : OutboundReq) : IO String := do
  if req.serviceName == "Webhook" || req.ssrfGuard then
    return stripTrailingSlash req.baseOrigin
  for key in ["QED_EXT_" ++ req.serviceName.toUpper ++ "_BASE", "QED_EXT_" ++ req.serviceName ++ "_BASE"] do
    if let some ov ← Prim.getEnv key then
      let t := stripTrailingSlash (trimWs ov)
      if !t.isEmpty then return t
  return stripTrailingSlash req.baseOrigin

private def requireSecretEnv (envVar : String) : IO (Except ApiError String) := do
  match ← Prim.getEnv envVar with
  | some tok =>
      if tok.isEmpty then return .error (ApiError.internal s!"secret environment variable `{envVar}` is empty")
      else return .ok tok
  | none =>
      return .error (ApiError.internal s!"missing secret environment variable `{envVar}`")

private def resolveAuthHeaders (spec : AuthSpec) : IO (Except ApiError (List (String × String))) := do
  match spec with
  | .none => return .ok []
  | .bearerSecret envVar =>
      return (← requireSecretEnv envVar).map fun tok => [("Authorization", "Bearer " ++ sanitizeHeader tok)]
  | .headerSecret hdrName envVar =>
      return (← requireSecretEnv envVar).map fun tok => [(sanitizeHeader hdrName, sanitizeHeader tok)]
  | .gcpServiceAccount envVar scope =>
      match ← requireSecretEnv envVar with
      | .error e => return .error e
      | .ok saJson =>
          match ← Prim.gcpBearerToken saJson scope with
          | .ok accessToken => return .ok [("Authorization", "Bearer " ++ sanitizeHeader accessToken)]
          | .error errMsg   => return .error (ApiError.internal s!"GCP OAuth2 token exchange failed: {errMsg}")

instance : MonadServer IO where
  httpCall req := do
    match ← resolveAuthHeaders req.auth with
    | .error e => return .error e
    | .ok authHdrs =>
        let base ← resolveBaseOrigin req
        let fullUrl := base ++ req.pathAndQuery
        let sanitizedReqHdrs := req.headers.map fun (k, v) => (sanitizeHeader k, sanitizeHeader v)
        let allHdrs := (sanitizedReqHdrs ++ authHdrs).toArray
        let guardFlag : UInt8 := if req.ssrfGuard then 1 else 0
        match ← Prim.httpCall req.method fullUrl allHdrs req.body guardFlag with
        | .error transportErr =>
            return .error (ApiError.internal s!"external HTTP transport error ({req.serviceName}): {transportErr}")
        | .ok (status, respBody, respHdrs) =>
            return .ok {
              status  := status.toUInt32
              body    := respBody
              headers := respHdrs.toList
            }
  readEnv := Prim.getEnv
  nowMs := Prim.nowMs
  randomHex := Prim.randomHex
  hmacSha256 := Prim.hmacSha256

@[implicit_reducible]
def withStateBox {σ : Type} (box : Prim.StateBox σ) : MonadAtomic σ IO where
  runAtomic     := Prim.atomicModify box
  runAtomicRead := Prim.atomicRead box

/-! ## Fail-Closed Startup Secret Check -/

def verifyRequiredSecrets (secrets : Array String) : IO Bool := do
  secrets.foldlM (init := true) fun ok name => do
    match ← requireSecretEnv name with
    | .ok _    => return ok
    | .error _ =>
        IO.eprintln s!"✗ missing required secret `{name}` (set `{name}` before starting the server)"
        return false

/-! ## Full-Stack Native Server Runner (Binary Protobuf RPC + Zero-Hop In-Memory SSR) -/

private def devReloadSnippet : String :=
  "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n</body>"

private def injectDevReload (htmlBytes : ByteArray) : ByteArray :=
  match String.fromUTF8? htmlBytes with
  | some html => (html.replace "</body>" devReloadSnippet).toUTF8
  | none      => htmlBytes

def runFullstackWithDispatch {Model Msg : Type}
    (app : Qed.App Model Msg)
    (title : String)
    (serverShortName : String)
    (requiredSecrets : Array String)
    (dispatchFn : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray))
    (port : UInt16)
    (staticDir : String)
    (devMode : Bool := false)
    (numWorkers : UInt32 := 0) : IO UInt32 := do
  if !(← verifyRequiredSecrets requiredSecrets) then
    return 1
  let rpcPrefix := "/_qed/rpc/" ++ serverShortName ++ "/"
  let handler := fun (method pathAndQuery : String) (headers : Array (String × String))
                     (body : ByteArray) (clientIp : String) => do
    let pathOnly := (pathAndQuery.splitOn "?").headD pathAndQuery
    if method == "GET" && pathOnly == "/_qed/health" then
      return (200, "application/json", "{\"ok\":true}".toUTF8)
    let ctx ← buildRequestCtx headers clientIp
    if method == "POST" && pathOnly.startsWith rpcPrefix then
      let rpcMethod := String.ofList (pathOnly.toList.drop rpcPrefix.length)
      match ← dispatchFn ctx rpcMethod body with
      | .ok respBytes =>
          return (200, "application/x-protobuf", respBytes)
      | .error apiErr =>
          return (apiErr.httpStatus.toNat, "text/plain; charset=utf-8", apiErr.message.toUTF8)
    else if (method == "GET" || method == "HEAD") && !pathOnly.startsWith "/_qed/" then
      let ssrDispatchBytes : String → String → ByteArray → IO (Except String ByteArray) :=
        fun reqMethod url reqBody => do
          let uPath := (url.splitOn "?").headD url
          if reqMethod == "POST" && uPath.startsWith rpcPrefix then
            let mName := String.ofList (uPath.toList.drop rpcPrefix.length)
            match ← dispatchFn ctx mName reqBody with
            | .ok bs   => return .ok bs
            | .error e => return .error e.message
          else
            return .error s!"SSR unknown binary RPC endpoint: {url}"
      let rawHtml ← app.ssrRenderNativeBytes pathAndQuery title ssrDispatchBytes (sessionUser := ctx.userId)
      let finalHtml := if devMode then injectDevReload rawHtml else rawHtml
      return (200, "text/html; charset=utf-8", if method == "HEAD" then ByteArray.empty else finalHtml)
    else
      return (404, "text/plain; charset=utf-8", "not found".toUTF8)
  Prim.serveNative port numWorkers staticDir (if devMode then 1 else 0) handler

def runStatefulFullstack {σ Model Msg : Type}
    (app : Qed.App Model Msg)
    (title : String)
    (serverShortName : String)
    (initState : σ)
    (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16)
    (staticDir : String)
    (devMode : Bool := false)
    (numWorkers : UInt32 := 0) : IO UInt32 := do
  let box ← Prim.mkStateBox initState
  let atomicInst : MonadAtomic σ IO := withStateBox box
  let dispatchIO : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray) :=
    fun ctx mName reqBytes => @dispatchM IO _ inferInstance atomicInst ctx mName reqBytes
  runFullstackWithDispatch app title serverShortName requiredSecrets dispatchIO port staticDir devMode numWorkers

def runStatelessFullstack {Model Msg : Type}
    (app : Qed.App Model Msg)
    (title : String)
    (serverShortName : String)
    (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16)
    (staticDir : String)
    (devMode : Bool := false)
    (numWorkers : UInt32 := 0) : IO UInt32 :=
  let dispatchIO : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray) :=
    fun ctx mName reqBytes => @dispatchM IO _ inferInstance ctx mName reqBytes
  runFullstackWithDispatch app title serverShortName requiredSecrets dispatchIO port staticDir devMode numWorkers

/-! ## `qedServerMain <FullstackName>` Entrypoint Generator -/

syntax (name := qedServerMainCmd) "qedServerMain " ident : command

open Lean Elab Command in
@[command_elab qedServerMainCmd]
def elabQedServerMain : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩
  let env ← getEnv
  let currNs ← getCurrNamespace
  let fsMap := fullstackRegistry.getState env
  let cand1 := currNs ++ fsIdent.getId
  let some fsInfo := (fsMap.find? cand1).orElse (fun _ =>
      fsMap.toList.findSome? fun (k, v) =>
        if k == fsIdent.getId || k.getString! == fsIdent.getId.toString then some v else none)
    | throwErrorAt fsIdent s!"unknown `fullstack` declaration `{fsIdent.getId}`"
  let srvMap := serverRegistry.getState env
  let some srvInfo := srvMap.find? fsInfo.serverName
    | throwErrorAt fsIdent s!"internal error: `server` `{fsInfo.serverName}` not found in registry"
  let cliAppId := mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp)
  let titleLit := Syntax.mkStrLit fsInfo.title
  let shortLit := Syntax.mkStrLit srvInfo.shortName
  let secretsId := mkIdentFrom fsIdent (srvInfo.serverName ++ `secrets)
  let dispatchId := mkIdentFrom fsIdent (srvInfo.serverName ++ `dispatchM)
  let mainId := mkIdent `main
  let runnerCall ← if srvInfo.hasState then
    let initStateId := mkIdentFrom fsIdent (srvInfo.serverName ++ `initState)
    `(Qed.Server.Native.runStatefulFullstack
        $cliAppId $titleLit $shortLit $initStateId $secretsId
        (fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $dispatchId)
        port staticDir devMode numWorkers)
  else
    `(Qed.Server.Native.runStatelessFullstack
        $cliAppId $titleLit $shortLit $secretsId
        (fun {m} [Monad m] [Qed.Server.MonadServer m] => $dispatchId)
        port staticDir devMode numWorkers)
  elabCommand (← `(command|
    def $mainId:ident (args : List String) : IO UInt32 := do
      let staticDir := args[0]?.getD "dist"
      let envPort ← Qed.Server.Prim.getEnv "PORT"
      let port := ((args[1]?.getD (envPort.getD "8000")).toNat?.getD 8000).toUInt16
      let devMode := args.contains "--dev"
      let numWorkers := (((← Qed.Server.Prim.getEnv "QED_WORKERS").bind String.toNat?).getD 0).toUInt32
      $runnerCall:term))

end Qed.Server.Native
