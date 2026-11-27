import Qed.Cloud.GcpApi
import Qed.Server.Native

/-! ## Thin GCP Cloud Run & IAM Executor (`Qed.Cloud.Executor`) -/

namespace Qed.Cloud
open Qed Qed.Server Qed.Server.Net Qed.Server.Native

inductive GcpAuthMode where
  | serviceAccountJson (saJson : String) | bearerToken (token : String) | metadata | none
deriving Inhabited

structure GcpExecConfig where
  (endpoints : GcpEndpoints := {}) (auth : GcpAuthMode := .none) (region : GcpRegion := .us_central1)
  (edgeSaEmail : String := "qed-edge@qed-cloud.iam.gserviceaccount.com")
  (builderSaEmail : String := "qed-builder@qed-cloud.iam.gserviceaccount.com")
  (deployerSaEmail? healthIdToken? : Option String := none) (ssrfGuard : Bool := true)
  (healthBaseUrl? : Option String := none) (pollDelayMs : UInt32 := 250)
deriving Inhabited

def gcpCloudPlatformScope : String := "https://www.googleapis.com/auth/cloud-platform"

def effectiveDeployerSaEmail? (cfg : GcpExecConfig) : Option String :=
  (nonEmptyStr? cfg.deployerSaEmail?).orElse fun _ => match cfg.auth with
    | .serviceAccountJson js => nonEmptyStr? ((Json.parse js).toOption.bind (·.strAt? "client_email")) | _ => none

def verifyHealthIdTokenAudience (jwt expectedAud : String) : Except String Unit := do
  let (_, payB64, _) ← (Qed.Auth.splitCompactJwt jwt).mapError (s!"healthIdToken? malformed: {·}")
  let payJson ← Qed.Auth.decodeBase64UrlJson payB64 "healthIdToken? payload"
  match payJson.strAt? "aud" with
  | some tokAud => if tokAud == expectedAud then .ok () else .error s!"healthIdToken? JWT `aud` (`{tokAud}`) does not match expected Cloud Run audience (`{expectedAud}`)"
  | none => .error "healthIdToken? JWT payload missing string `aud` claim"

def resolveToken (cfg : GcpExecConfig) (audience? : Option String := none) : IO (Except String (Option String)) := do
  if let (some aud, some idTok) := (audience?, nonEmptyStr? cfg.healthIdToken?) then return (verifyHealthIdTokenAudience idTok aud).map fun _ => some idTok
  match audience?, cfg.auth with
  | _, .none => return .ok none
  | some _, .bearerToken _ => return .error "refusing to send raw cloud-platform OAuth2 bearerToken to Cloud Run /_qed/health (use serviceAccountJson or set healthIdToken?)"
  | none, .bearerToken tok => return .ok (if tok.isEmpty then none else some tok)
  | some aud, .serviceAccountJson js => (·.map some) <$> fetchGcpBearerToken none js aud (isIdToken := true) (ssrfGuard := cfg.ssrfGuard)
  | none, .serviceAccountJson js => (·.map some) <$> fetchGcpBearerToken none js gcpCloudPlatformScope (isIdToken := false) (ssrfGuard := cfg.ssrfGuard)
  | aud?, .metadata => (·.map some) <$> fetchGcpMetadataToken none aud?

private def gcpContentType? (req : GcpHttpRequest) (bodyBytes : ByteArray) : Option String :=
  if bodyBytes.isEmpty && req.method == "GET" then none else some req.contentType

private def sendGcpRaw (cfg : GcpExecConfig) (req : GcpHttpRequest) (bodyBytes : ByteArray) (tok? : Option String) : IO (Except String (Nat × String)) := do
  match ← execHttpCall req.method req.url (mkBearerHeaders tok? (gcpContentType? req bodyBytes) req.headers.toArray) bodyBytes cfg.ssrfGuard with
  | .error e => return .error s!"GCP HTTP {req.method} {req.url}: {e}"
  | .ok (st, body, _) => return .ok (st, (String.fromUTF8? body).getD "")

private def sendGcpJson (cfg : GcpExecConfig) (req : GcpHttpRequest) (tok? : Option String) (allowStatuses : List Nat := [200, 201, 204]) : IO (Except String (Nat × Json)) :=
  let bodyBytes := req.body.toUTF8
  execHttpJson req.method req.url tok? bodyBytes (gcpContentType? req bodyBytes) req.headers.toArray cfg.ssrfGuard
    (okStatus := allowStatuses.contains) (allowEmptyBody := true)
    (fmtTransportErr := fun e => s!"GCP HTTP {req.method} {req.url}: {e}")
    (fmtStatusErr := fun st txt => s!"GCP {req.method} {req.url} failed (HTTP {st}): {txt}")
    (fmtJsonErr := fun st e => s!"GCP {req.method} {req.url} invalid JSON (HTTP {st}): {e}")

private def pollOp (cfg : GcpExecConfig) (tok? : Option String) (label : String)
    (parseNext : Json → Except String (Option String)) (mkReq : String → GcpHttpRequest) (resp : Json) : Nat → ExceptT String IO Unit
  | 0 => match parseNext resp with | .error e => throw e | .ok (some _) => throw s!"{label} timed out waiting for completion" | .ok none => return ()
  | fuel + 1 => do
      let some opId ← liftP (parseNext resp) | return ()
      liftIO (IO.sleep cfg.pollDelayMs)
      pollOp cfg tok? label parseNext mkReq (← liftE (sendGcpJson cfg (mkReq opId) tok? [200])).2 fuel

private def pollLro (cfg : GcpExecConfig) (tok? : Option String) (resp : Json) (fuel : Nat) : ExceptT String IO Unit :=
  pollOp cfg tok? "GCP operation" (fun j => match j.get? "error" with | some e => .error s!"GCP operation failed: {Json.render e}" | none => parsePendingLro j)
    (reqGetCloudRunOp cfg.endpoints) resp fuel

private def sendSqlMutationWithRetry (cfg : GcpExecConfig) (tok? : Option String) (projId : String) (req : GcpHttpRequest) (alreadyDoneStatuses : List Nat) : Nat → ExceptT String IO Unit
  | 0 => throw s!"Cloud SQL {req.method} {req.url} exceeded operationInProgress retry limit"
  | n + 1 => do
      let (st, txt) ← liftE (sendGcpRaw cfg req req.body.toUTF8 tok?)
      if st == 409 && isSqlOperationInProgress txt then
        if n == 0 then throw s!"Cloud SQL {req.method} {req.url} blocked by ongoing operation (HTTP 409 operationInProgress): {txt}"
        else liftIO (IO.sleep cfg.pollDelayMs); sendSqlMutationWithRetry cfg tok? projId req alreadyDoneStatuses n
      else if alreadyDoneStatuses.contains st then return ()
      else if [200, 201, 204].contains st then
        if !txt.trimAscii.toString.isEmpty then
          pollOp cfg tok? "Cloud SQL operation" parsePendingSqlOp (reqGetSqlOp cfg.endpoints projId)
            (← liftP ((Json.parse txt).mapError (s!"GCP {req.method} {req.url} invalid JSON (HTTP {st}): {·}"))) 60
      else throw s!"GCP {req.method} {req.url} failed (HTTP {st}): {txt}"

/-! ### Multi-Region Live GCP State Observation (`observeGcpState`) -/

private def listAllSecrets (cfg : GcpExecConfig) (tok? : Option String) (key : DeployKey) (pageToken? : Option String) (seenTokens acc : List String) : Nat → ExceptT String IO (List String)
  | 0 => throw s!"listAllSecrets: exceeded maximum pagination depth (100 pages) for `{renderKeySlug key}`; refusing partial observation"
  | fuel + 1 => do
      let (st, j) ← liftE (sendGcpJson cfg (reqListSecrets cfg.endpoints key pageToken?) tok? [200, 404])
      if st == 404 then return acc.eraseDups
      let nextAcc := acc ++ parseListedSecrets key j
      match parseNextPageToken? j with
      | some nextTok =>
          if seenTokens.contains nextTok then throw s!"listAllSecrets: detected repeating Secret Manager pagination token `{nextTok}`"
          listAllSecrets cfg tok? key (some nextTok) (nextTok :: seenTokens) nextAcc fuel
      | none => return nextAcc.eraseDups

private def isDangerousProjectRole (role : String) : Bool :=
  let base := if role.endsWith "[conditional]" then (role.dropEnd 13).toString else role
  !base.startsWith "roles/" || ["roles/owner", "roles/editor", "roles/viewer"].contains base ||
  ["roles/iam.", "roles/run.", "roles/secretmanager.", "roles/cloudsql.", "roles/storage.", "roles/networksecurity.", "roles/resourcemanager.",
   "roles/artifactregistry.", "roles/cloudbuild.", "roles/cloudfunctions.", "roles/deploymentmanager.", "roles/cloudkms.", "roles/compute."].any (base.startsWith ·) ||
  [".admin", "Admin", ".editor", "Editor", ".writer", "Writer", ".developer", "Developer", ".builder", "Decrypter"].any (base.contains ·)

private def readIamPolicy (cfg : GcpExecConfig) (tok? : Option String) (key : DeployKey) (r : GcpRegion) (res : GcpResource) :
    ExceptT String IO (List GcpIamBinding × List (String × String × GcpResource)) := do
  let (st, j) ← liftE (sendGcpJson cfg (reqGetIamPolicy cfg.endpoints r res) tok? [200, 404])
  if st != 200 then return ([], [])
  return (← liftP (IamPolicyDoc.fromJson j)).partitionBindings cfg.edgeSaEmail cfg.builderSaEmail key res

def observeGcpState (cfg : GcpExecConfig) (key : DeployKey) (knownDbs : List (String × DbCluster) := []) (regions : List GcpRegion := []) (assetsPublic : Bool := true) : IO (Except String GcpLiveSnapshot) := do
  let (targetRegions, projId) := (if regions.isEmpty then [cfg.region] else regions, key.shard.projectFor key.env)
  ExceptT.run do
    let tok? ← liftE (resolveToken cfg)
    let getOpt (req : GcpHttpRequest) : ExceptT String IO (Option Json) := do let (st, j) ← liftE (sendGcpJson cfg req tok? [200, 404]); return if st == 200 then some j else none
    let secretNames ← listAllSecrets cfg tok? key none [] [] 100
    let secRes ← secretNames.mapM fun s => readIamPolicy cfg tok? key cfg.region (.secret key s)
    let (secretBindings, secRaw) := (secRes.flatMap Prod.fst, secRes.flatMap Prod.snd)
    let regObs ← targetRegions.mapM fun r => do
      let (kb, rb) ← readIamPolicy cfg tok? key r (.cloudRun key)
      let spec := (← getOpt (reqGetCloudRunService cfg.endpoints r key)).elim { region := r, existsService := false } (parseCloudRunServiceSpec r)
      let egJ? ← getOpt (reqGetEgressPolicy cfg.endpoints r key)
      return ((r, kb, (egJ?.map parseEgressPolicy).getD []), rb, spec, egJ?.isSome)
    let (regionStates, regRaw, serviceSpecs) := (regObs.map (·.1), regObs.flatMap (·.2.1), regObs.map (·.2.2.1))
    let presentEgressPolicies := regObs.filterMap fun (rs, _, _, hasEg) => if hasEg then some rs.1 else none
    let cl := clusterForEnv key.env
    let managedDbs := ((← getOpt (reqListDbs cfg.endpoints cl key)).map (parseListedDbs key)).getD []
    let dbTargets := (knownDbs ++ managedDbs.map (·, cl)).eraseDups
    let (probeRes, projRes) := (GcpResource.cloudSqlDb cl key ((dbTargets.head?.map Prod.fst).getD "_project"), GcpResource.project projId)
    let saMem := (GcpPrincipal.runtimeSa key).gcpMember cfg.edgeSaEmail cfg.builderSaEmail
    let (projKnown, projRaw) ← readIamPolicy cfg tok? key cfg.region projRes
    let projExpanded := projKnown.flatMap fun b =>
      if b.principal == .runtimeSa key && b.role == .cloudSqlClient then
        if dbTargets.isEmpty then [{ b with resource := probeRes }] else dbTargets.map fun (dbName, c) => { b with resource := .cloudSqlDb c key dbName }
      else if b.principal == .allUsers || b.principal == .allAuthenticatedUsers then [{ b with resource := if b.role == .cloudSqlClient then probeRes else projRes }]
      else if b.principal != .runtimeSa key && b.role == .cloudSqlClient then
        if match b.principal with | .external m => !isQedRuntimeSaMember projId m | _ => true then [{ b with resource := probeRes }] else []
      else [b]
    let (bucketKnown, bucketRaw) ← readIamPolicy cfg tok? key cfg.region (.assetPrefix key "_bucket" assetsPublic)
    let bucketBad := bucketKnown.filter fun b => !((b.principal == .builder && b.role == .storageObjectAdmin) || (b.role == .storageLegacyObjectReader && b.principal == (if assetsPublic then .allUsers else .edgeRouter)))
    let effDeployerSa := effectiveDeployerSaEmail? cfg
    let presentDenyPolicies ← [("deny-qed-run-public", false, [.runInvoke]), ("deny-qed-secrets-public", true, [.secretAccessor])].filterMapM fun (denyId, allowRt, perms) => do
      return (← getOpt (reqGetDenyPolicyById cfg.endpoints projId denyId)).bind fun dj => if isValidDenyPolicyDoc projId cfg.edgeSaEmail cfg.builderSaEmail effDeployerSa allowRt perms dj then some denyId else none
    let edgeRunB : GcpIamBinding := { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key }
    let allRegBs := regionStates.map (·.2.1)
    let obsRunBs := (if !allRegBs.isEmpty && allRegBs.all (·.contains edgeRunB) then [edgeRunB] else []) ++ (allRegBs.flatMap fun bs => bs.filter (· != edgeRunB)).eraseDups
    return {
      observed := { key, secretNames, managedDbs, egressAllow := (regionStates.flatMap (·.2.2)).eraseDups, bindings := (secretBindings ++ projExpanded ++ bucketBad ++ obsRunBs).eraseDups },
      rawBindings := (secRaw ++ regRaw ++ bucketRaw ++ projRaw.filter fun (m, role, _) => m == saMem || m == "allUsers" || m == "allAuthenticatedUsers" || isDangerousProjectRole role).eraseDups,
      regionStates, serviceSpecs, presentDenyPolicies, presentEgressPolicies }

/-! ### ETag-Retry Mutators, Collision-Free Upload, Health Check, & 4-Phase Rollout -/

private def withEtagRetry (label : String) (step : ExceptT String IO (Option (Nat × Json))) : Nat → ExceptT String IO (Option Json)
  | 0 => throw s!"{label} exceeded ETag retry limit"
  | n + 1 => do
      let some (st, j) ← step | return none
      if st == 409 || st == 412 then (if n == 0 then throw s!"{label} ETag/create conflict (HTTP {st})" else withEtagRetry label step n) else return some j

private def withEtagLro (cfg : GcpExecConfig) (tok? : Option String) (label : String) (step : ExceptT String IO (Option (Nat × Json))) (attempts : Nat := 3) : ExceptT String IO Unit := do
  if let some respJ ← withEtagRetry label step attempts then pollLro cfg tok? respJ 60

private def mutateIamBindingInRegion (cfg : GcpExecConfig) (region : GcpRegion) (tok? : Option String) (b : GcpIamBinding) (grant : Bool) (allowMissingResource : Bool := false) (attempts : Nat := 3) : ExceptT String IO Unit :=
  discard <| withEtagRetry s!"IAM update for `{b.role.gcpName}`" (do
    let (getSt, getJson) ← liftE (sendGcpJson cfg (reqGetIamPolicy cfg.endpoints region b.resource) tok? [200, 404])
    if getSt == 404 && (!grant || allowMissingResource) then return none
    let doc ← if getSt == 200 then liftP (IamPolicyDoc.fromJson getJson) else pure ({} : IamPolicyDoc)
    let member := b.principal.gcpMember cfg.edgeSaEmail cfg.builderSaEmail
    let nextDoc := if grant then doc.addBinding b.role.gcpName member else doc.removeBinding b.role.gcpName member (match b.resource with | .cloudRun _ | .secret _ _ => true | _ => false)
    if getSt == 200 && nextDoc == doc then return none
    some <$> liftE (sendGcpJson cfg (reqSetIamPolicy cfg.endpoints region b.resource nextDoc) tok? [200, 201, 409, 412])) attempts

private def buildCollisionFreeUpload (ep : GcpEndpoints) (key : DeployKey) (buildHash rel : String) (bytes : ByteArray) (isPublic : Bool) : Nat → ExceptT String IO (GcpHttpRequest × ByteArray)
  | 0 => throw s!"uploadAssets `{rel}`: failed to generate collision-free multipart boundary"
  | fuel + 1 => do match reqUploadAsset ep key buildHash rel bytes s!"qed_gcs_{← liftIO (Qed.Server.Prim.randomHex 16)}" isPublic with
      | .ok pair => return pair | .error _ => buildCollisionFreeUpload ep key buildHash rel bytes isPublic fuel

def realPathExcept (p : System.FilePath) (label : String) : ExceptT String IO System.FilePath :=
  ExceptT.mk (try Except.ok <$> IO.FS.realPath p catch e => pure (.error s!"{label} `{p}`: {e}"))

private def executeHealthCheckInRegion (cfg : GcpExecConfig) (region : GcpRegion) (tok? : Option String) (key : DeployKey) (buildHash : String) : ExceptT String IO Unit := do
  let (candUrl, baseUri) ← match cfg.healthBaseUrl? with
    | some u => pure (u, u)
    | none =>
        let expectedRev := cloudRunRevisionName key buildHash
        let (_, svcJson) ← liftE (sendGcpJson cfg (reqGetCloudRunService cfg.endpoints region key) tok? [200])
        let some (cUrl, bUri) := parseCloudRunCandidateUrls expectedRev svcJson
          | throw s!"Cloud Run `{renderCloudRunName key}` ({region}) missing candidate revision `{expectedRev}` in `trafficStatuses`"
        let loopbackOk := cfg.endpoints.baseOverride?.any fun ov => isStrictLoopbackUrl ov && trimTrailingSlash cUrl == trimTrailingSlash ov && trimTrailingSlash bUri == trimTrailingSlash ov
        if !loopbackOk && !isValidCloudRunCandidateForService key region cUrl bUri then throw s!"Cloud Run `{renderCloudRunName key}` ({region}) returned untrusted candidate/base URI (`{cUrl}`, `{bUri}`)"
        pure (cUrl, bUri)
  let healthUrl := trimTrailingSlash candUrl ++ "/_qed/health"
  let hdrs := (← liftE (resolveToken cfg (some (trimTrailingSlash baseUri)))).elim #[] fun t => #[("Authorization", s!"Bearer {t}")]
  let (st, body, _) ← liftE (execHttpCall "GET" healthUrl hdrs ByteArray.empty cfg.ssrfGuard)
  if st != 200 then throw s!"health check GET {healthUrl} returned HTTP {st}: {(String.fromUTF8? body).getD ""}"

def executeAction (cfg : GcpExecConfig) (plan : GcpPlan) (imageUri : String) (distDir : System.FilePath) (tok? : Option String) (a : GcpAction) (includeSqlUser : Bool := true) : IO (Except String Unit) := do
  let regions := if plan.regions.isEmpty then [cfg.region] else plan.regions
  ExceptT.run do
    let sendOk (req : GcpHttpRequest) (okSt : List Nat := [200, 201]) : ExceptT String IO Json := Prod.snd <$> liftE (sendGcpJson cfg req tok? okSt)
    let delOk (req : GcpHttpRequest) : ExceptT String IO Unit := discard <| sendOk req [200, 204, 404]
    let isRunRes : GcpResource → Bool | .cloudRun _ => true | _ => false
    let runGrants := plan.bindings.filter (isRunRes ·.resource)
    let mutateRegions (b : GcpIamBinding) (grant allowMiss : Bool) := (if isRunRes b.resource then regions else [cfg.region]).forM fun r => mutateIamBindingInRegion cfg r tok? b grant allowMiss
    let sqlPair (cl : DbCluster) (key : DeployKey) (r1 r2 : GcpHttpRequest) (okSt : List Nat) : ExceptT String IO Unit := do
      let sqlProj := key.shard.clusterProject cl; sendSqlMutationWithRetry cfg tok? sqlProj r1 okSt 5
      if includeSqlUser then sendSqlMutationWithRetry cfg tok? sqlProj r2 okSt 5
    match a with
    | .uploadAssets key buildHash paths =>
        let realDist ← realPathExcept distDir "uploadAssets: invalid distDir"; let distPrefix := trimTrailingSlash realDist.toString ++ "/"
        for rel in paths do
          if !isSafeRelativeAssetPath rel then throw s!"uploadAssets: unsafe relative asset path `{rel}`"
          let filePath := distDir / trimLeadingSlash rel
          if !(← filePath.pathExists) then throw s!"uploadAssets: missing local asset file `{filePath}`"
          let realFile ← realPathExcept filePath "uploadAssets: cannot resolve asset path"
          if !realFile.toString.startsWith distPrefix then throw s!"uploadAssets: symlink/path escape blocked for `{rel}` (resolved to `{realFile}` outside `{realDist}`)"
          let (req, payload) ← buildCollisionFreeUpload cfg.endpoints key buildHash rel (← liftIO (IO.FS.readBinFile realFile)) plan.assetsArePublic 4
          let (st, txt) ← liftE (sendGcpRaw cfg req payload tok?)
          if !(200 ≤ st && st < 300) then throw s!"uploadAssets `{rel}` failed (HTTP {st}): {txt}"
    | .ensureSecret key s => discard <| sendOk (reqEnsureSecret cfg.endpoints key s) [200, 201, 409]
    | .ensureDb cl key db => sqlPair cl key (reqEnsureDb cfg.endpoints cl key db) (reqEnsureSqlIamUser cfg.endpoints cl key) [409]
    | .grantBinding b => if !(isRunRes b.resource && b.principal == .edgeRouter && b.role == .runInvoker) then mutateRegions b true (isRunRes b.resource)
    | .revokeBinding b => if !(match b.resource with | .cloudSqlDb _ _ _ => b.principal == .runtimeSa plan.key && !plan.managedDbs.isEmpty | _ => false) then mutateRegions b false false
    | .putDenyRule rule =>
        withEtagLro cfg tok? s!"IAM v2 deny policy `{rule.resource.denyPolicyId}`" do
          let (getSt, getJ) ← liftE (sendGcpJson cfg (reqGetDenyRule cfg.endpoints rule) tok? [200, 404])
          let (etag?, prevExcs) := if getSt == 200 then (some (getJ.strAtD "etag"), parseDenyExceptionPrincipals getJ) else (none, [])
          some <$> liftE (sendGcpJson cfg (reqUpsertDenyRule cfg.endpoints cfg.edgeSaEmail cfg.builderSaEmail rule etag? prevExcs (effectiveDeployerSaEmail? cfg)) tok? [200, 201, 409, 412])
    | .setEgressRules key os | .narrowEgressRules key os => regions.forM fun r => discard <| sendOk (reqPutEgressPolicy cfg.endpoints r key os)
    | .deployRevisionZero key buildHash scale =>
        discard <| sendOk (reqCreateServiceAccount cfg.endpoints key) [200, 201, 409]
        regions.forM fun r => do
          let (curSt, curJ) ← liftE (sendGcpJson cfg (reqGetCloudRunService cfg.endpoints r key) tok? [200, 404])
          let existingTraffic ← if curSt == 200 then liftP (parseLiveTrafficTargets curJ) else pure []
          pollLro cfg tok? (← sendOk (reqDeployRevisionZero cfg.endpoints r key buildHash imageUri scale plan.secretNames existingTraffic)) 180
          for b in runGrants do if !existingTraffic.isEmpty || b.principal != .edgeRouter then mutateIamBindingInRegion cfg r tok? b true false
    | .healthCheck key buildHash => regions.forM fun r => executeHealthCheckInRegion cfg r tok? key buildHash
    | .shiftTraffic100 key buildHash =>
        let edgeRunB : GcpIamBinding := { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key }
        let preStates ← regions.mapM fun r => do
          let (curSt, curJ) ← liftE (sendGcpJson cfg (reqGetCloudRunService cfg.endpoints r key) tok? [200, 404])
          let (kb, _) ← (try readIamPolicy cfg tok? key r (.cloudRun key) catch _ => pure ([], []))
          return (r, if curSt == 200 then parseAllTrafficTargets curJ else [], kb.contains edgeRunB)
        let mut shifted : List (GcpRegion × List Json × Bool) := []
        let rollbackAll (targets : List (GcpRegion × List Json × Bool)) : IO String := do
          let runNote (okMsg errPfx : String) (m : ExceptT String IO Unit) : IO String := do match ← ExceptT.run m with | .ok () => pure okMsg | .error e => pure s!"{errPfx}: {e}"
          let mut notes : List String := []
          for (rbReg, rbTraffic, rbHadEdge) in targets do
            if !rbTraffic.isEmpty then notes := notes ++ [← runNote s!"rolled back {rbReg}" s!"rollback {rbReg} failed" (do pollLro cfg tok? (← sendOk (reqRestoreTraffic cfg.endpoints rbReg key rbTraffic)) 60)]
            if !rbHadEdge then notes := notes ++ [← runNote s!"revoked edgeRouter on {rbReg}" s!"edgeRouter revoke on {rbReg} failed" (mutateIamBindingInRegion cfg rbReg tok? edgeRunB false false)]
          return if notes.isEmpty then "" else s!" (compensating rollback: {"; ".intercalate notes})"
        for (r, prevTraffic, hadEdge) in preStates do
          if let .error err ← liftIO (ExceptT.run do pollLro cfg tok? (← sendOk (reqShiftTraffic100 cfg.endpoints r key buildHash)) 180) then
            throw s!"shiftTraffic100 failed in {r}: {err}{← liftIO (rollbackAll shifted)}"
          shifted := shifted ++ [(r, prevTraffic, hadEdge)]
          if let .error err ← liftIO (ExceptT.run do for b in runGrants do mutateIamBindingInRegion cfg r tok? b true false) then
            throw s!"shiftTraffic100 post-cutover IAM grant failed in {r}: {err}{← liftIO (rollbackAll shifted)}"
    | .deleteSecret key s => delOk (reqDeleteSecret cfg.endpoints key s)
    | .deleteService key => regions.forM fun r => do let (st, opJ) ← liftE (sendGcpJson cfg (reqDeleteCloudRunService cfg.endpoints r key) tok? [200, 204, 404]); if st != 404 then pollLro cfg tok? opJ 180
    | .dropPreviewDb key db => sqlPair .nonProdCluster key (reqDropPreviewDb cfg.endpoints key db) (reqDeleteSqlIamUser cfg.endpoints .nonProdCluster key) [404]
    | .pruneDenyException key =>
        withEtagLro cfg tok? s!"IAM v2 deny policy prune for `{renderSaId key}`" do
          let (getSt, getJ) ← liftE (sendGcpJson cfg (reqGetDenyPolicyById cfg.endpoints (key.shard.projectFor key.env) "deny-qed-secrets-public") tok? [200, 404])
          if getSt == 404 then return none
          let some req := reqPruneDenyException cfg.endpoints cfg.edgeSaEmail cfg.builderSaEmail key (getJ.strAtD "etag") (parseDenyExceptionPrincipals getJ) (effectiveDeployerSaEmail? cfg) | return none
          some <$> liftE (sendGcpJson cfg req tok? [200, 201, 409, 412])
    | .deleteServiceAccount key => delOk (reqDeleteServiceAccount cfg.endpoints key)
    | .deleteEgressPolicy key => regions.forM fun r => delOk (reqDeleteEgressPolicy cfg.endpoints r key)

def executeRollout (cfg : GcpExecConfig) (plan : GcpPlan) (imageUri : String) (distDir : System.FilePath) (actions : List GcpAction) (onStep : GcpAction → IO Unit := fun _ => pure ()) : IO (Except String Nat) := do
  if actions.isEmpty then return .ok 0
  ExceptT.run do
    let tok? ← liftE (resolveToken cfg)
    if actions.any fun | .grantBinding b => (match b.principal with | .runtimeSa _ => true | _ => false) | .ensureDb _ _ _ | .deployRevisionZero _ _ _ => true | _ => false then
      discard <| liftP ((← liftIO (sendGcpJson cfg (reqCreateServiceAccount cfg.endpoints plan.key) tok? [200, 201, 409])).mapError (s!"failed to ensure runtime service account: {·}"))
    let mut done : Nat := 0; let mut seenDenyKeys : List (String × String × List GcpPermission) := []; let mut ensuredSqlUsers : List (DbCluster × DeployKey) := []
    for (a, idx) in actions.zipIdx do
      liftIO (onStep a)
      let denyKey? := match a with | .putDenyRule r => some (r.resource.projectOf, r.resource.denyPolicyId, r.permissions) | _ => none
      if denyKey?.any seenDenyKeys.contains then done := done + 1
      else
        let includeSqlUser := match a with
          | .ensureDb cl key _ => !ensuredSqlUsers.contains (cl, key)
          | .dropPreviewDb key _ => !((actions.drop (idx + 1)).any fun | .dropPreviewDb k' _ => k' == key | _ => false) | _ => true
        match ← liftIO (executeAction cfg plan imageUri distDir tok? a includeSqlUser) with
        | .error e => throw s!"aborted after {done} step(s) at phase {a.phase.rank}: {e}"
        | .ok () =>
            if let some dk := denyKey? then seenDenyKeys := dk :: seenDenyKeys
            if let .ensureDb cl key _ := a then if includeSqlUser then ensuredSqlUsers := (cl, key) :: ensuredSqlUsers
            done := done + 1
    return done

/-! ### Human-Readable Plan & Drift Formatters -/

private def renderResourceShort : GcpResource → String
  | .cloudRun k => s!"cloudRun/{renderCloudRunName k}" | .secret k s => s!"secret/{secretId k s}" | .cloudSqlDb c k db => s!"sql/{sqlInstanceName c k}/{sqlDbName k db}"
  | .assetPrefix k h pub => s!"gcs/{assetBucketName k pub}/{renderKeySlug k}/{sanitizeToken h 16}" | .project p => s!"project/{p}"
private def renderPrincipalShort : GcpPrincipal → String
  | .allUsers => "allUsers" | .allAuthenticatedUsers => "allAuthenticatedUsers" | .builder => "builder"
  | .edgeRouter => "edgeRouter" | .runtimeSa k => s!"runtimeSa({renderSaId k})" | .external e => s!"external({e})"
private def renderBinding (verb : String) (b : GcpIamBinding) : String := s!"{renderPrincipalShort b.principal} {verb} {b.role.gcpName} on {renderResourceShort b.resource}"

def formatAction : GcpAction → String
  | .uploadAssets k h ps => s!"uploadAssets {ps.length} file(s) → gs://{assetBucketName k}/{renderKeySlug k}/{sanitizeToken h 16}/"
  | .ensureSecret k s => s!"ensureSecret {secretId k s}" | .ensureDb cl k db => s!"ensureDb {sqlInstanceName cl k}/{sqlDbName k db} (+ IAM user {sqlIamUserName k})"
  | .grantBinding b => s!"grantBinding {renderBinding "←" b}" | .putDenyRule d => s!"putDenyRule deny {d.principals.map renderPrincipalShort} on {renderResourceShort d.resource}"
  | .setEgressRules _ os => s!"setEgressRules ({os.length} origin(s)): {", ".intercalate os}"
  | .deployRevisionZero k h sc => s!"deployRevisionZero {cloudRunRevisionName k h} (0% traffic, concurrency={sc.concurrency}, {sc.cpuMilli}m CPU, {sc.memoryMb}Mi, min={sc.minInstances}, max={sc.maxInstances})"
  | .healthCheck k h => s!"healthCheck GET /_qed/health on {cloudRunRevisionName k h}" | .shiftTraffic100 k h => s!"shiftTraffic100 {cloudRunRevisionName k h} (0% → 100%)"
  | .revokeBinding b => s!"revokeBinding {renderBinding "✗" b}" | .deleteSecret k s => s!"deleteSecret {secretId k s}" | .narrowEgressRules _ os => s!"narrowEgressRules ({os.length} origin(s)): {", ".intercalate os}"
  | .deleteService k => s!"deleteService {renderCloudRunName k}" | .dropPreviewDb k db => s!"dropPreviewDb {sqlDbName k db} (+ IAM user {sqlIamUserName k})"
  | .pruneDenyException k => s!"pruneDenyException {renderSaEmail k} from deny-qed-secrets-public" | .deleteServiceAccount k => s!"deleteServiceAccount {renderSaEmail k}"
  | .deleteEgressPolicy k => s!"deleteEgressPolicy egress-{renderKeySlug k}"

def formatRolloutPlan (plan : GcpPlan) (actions : List GcpAction) : String :=
  s!"Qed Cloud Plan: {plan.cloudRunName} (env={plan.key.env.toDeployEnv}, project={plan.key.shard.projectFor plan.key.env}, sa={plan.serviceAccountId})\n" ++
  s!"  regions={",".intercalate (plan.regions.map GcpRegion.toString)} compute={plan.scale.cpuMilli}m/{plan.scale.memoryMb}Mi concurrency={plan.scale.concurrency} instances={plan.scale.minInstances}..{plan.scale.maxInstances} timeout={plan.scale.timeoutSec}s" ++
  String.join ([(.phase1_provision, "Phase 1: Provision (assets, secrets, DBs, IAM grants, denies, additive egress)"),
    (.phase2_deployZero, "Phase 2: Deploy 0% & Verify (new Cloud Run revision + /_qed/health)"),
    (.phase3_shiftTraffic, "Phase 3: Atomic Cutover (0% → 100% traffic)"), (.phase4_cleanup, "Phase 4: Cleanup (revoke stale bindings/secrets, narrow egress)")].filterMap fun (ph, title) =>
      match actions.filter (·.phase == ph) with | [] => none | xs => some (s!"\n  [{title}]\n" ++ "\n".intercalate (xs.map fun a => s!"    • {formatAction a}")))

def formatDriftFindings (findings : List DriftFinding) : String :=
  if findings.isEmpty then "✓ zero drift: live GCP IAM, Cloud Run specs, deny policies, secrets, DBs, and egress match verified plan"
  else s!"✗ detected {findings.length} drift finding(s):\n" ++ "\n".intercalate (findings.map fun
    | .keyMismatch o d => s!"  • KEY MISMATCH: observed={renderKeySlug o}, desired={renderKeySlug d}"
    | .unauthorizedBinding b => s!"  • UNAUTHORIZED IAM BINDING: {renderBinding "has" b}"
    | .unauthorizedRawBinding m r res => s!"  • UNAUTHORIZED PRIVILEGED/CONDITIONAL ROLE: {m} has {r} on {renderResourceShort res}"
    | .missingBinding b => s!"  • MISSING IAM BINDING: {renderBinding "needs" b}" | .missingRegionalBinding reg b => s!"  • MISSING IAM BINDING ({reg}): {renderBinding "needs" b}"
    | .missingRegion reg => s!"  • MISSING REGION OBSERVATION: {reg}" | .missingRegionalEgressPolicy reg => s!"  • MISSING EGRESS POLICY ({reg}): GatewaySecurityPolicy not found"
    | .unsafeCloudRunSpec reg detail => s!"  • UNSAFE CLOUD RUN SPEC ({reg}): {detail}" | .missingDenyPolicy pid => s!"  • MISSING/INVALID IAM V2 DENY POLICY: {pid}"
    | .extraSecret s => s!"  • EXTRA SECRET: {s}" | .missingSecret s => s!"  • MISSING SECRET: {s}" | .extraDb d => s!"  • EXTRA MANAGED DB: {d}"
    | .missingDb d => s!"  • MISSING MANAGED DB: {d}" | .extraEgress o => s!"  • EXTRA EGRESS ORIGIN: {o}" | .missingEgress o => s!"  • MISSING EGRESS ORIGIN: {o}"
    | .missingRegionalEgress reg o => s!"  • MISSING EGRESS ORIGIN ({reg}): {o}")

end Qed.Cloud
