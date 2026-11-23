import Cli.Build
import Qed.Cloud.Executor

open System (FilePath)
open Qed.Cloud Qed.Server.Net

namespace Qed.Cli

private structure DeployCliOpts where
  dryRun          : Bool := false
  checkDrift      : Bool := false
  teardown        : Bool := false
  skipBuild       : Bool := false
  envStr          : String := "prod"
  prStr           : String := "0"
  project?        : Option String := none
  prodProject?    : Option String := none
  nonProdProject? : Option String := none
  tenantStr?      : Option String := none
  appIdStr?       : Option String := none
  mod?            : Option String := none
  deployName?     : Option String := none
  image?          : Option String := none
  apiBase?        : Option String := none
  distDir?        : Option String := none

private def parseDeployOpts : List String → DeployCliOpts → Except String DeployCliOpts
  | [], o => .ok o
  | "--dry-run" :: r, o => parseDeployOpts r { o with dryRun := true } | "--check-drift" :: r, o => parseDeployOpts r { o with checkDrift := true }
  | "--teardown" :: r, o => parseDeployOpts r { o with teardown := true } | "--skip-build" :: r, o => parseDeployOpts r { o with skipBuild := true }
  | "--env" :: v :: r, o => parseDeployOpts r { o with envStr := v } | "--pr" :: v :: r, o => parseDeployOpts r { o with prStr := v }
  | "--project" :: v :: r, o => parseDeployOpts r { o with project? := some v } | "--prod-project" :: v :: r, o => parseDeployOpts r { o with prodProject? := some v }
  | "--nonprod-project" :: v :: r, o => parseDeployOpts r { o with nonProdProject? := some v } | "--tenant" :: v :: r, o => parseDeployOpts r { o with tenantStr? := some v }
  | "--app-id" :: v :: r, o => parseDeployOpts r { o with appIdStr? := some v } | "--mod" :: v :: r, o => parseDeployOpts r { o with mod? := some v }
  | "--deploy" :: v :: r, o => parseDeployOpts r { o with deployName? := some v } | "--image" :: v :: r, o => parseDeployOpts r { o with image? := some v }
  | "--api-base" :: v :: r, o => parseDeployOpts r { o with apiBase? := some v } | "--dist" :: v :: r, o => parseDeployOpts r { o with distDir? := some v }
  | flag :: _, _ => .error s!"unknown or incomplete `qed deploy` flag: `{flag}`"

private def isAllowedRemoteApiBase (u : String) : Bool :=
  u.startsWith "https://" && !u.toList.any (fun c => c.isWhitespace || c.toNat < 0x20 || c.toNat == 0x7F || "@\\?#".contains c) &&
  let after := (u.drop 8).toString
  let auth := if after.endsWith "/" then (after.dropEnd 1).toString else after
  !auth.contains "/" && match auth.splitOn ":" with
    | [h] | [h, "443"] =>
        let host := h.toLower
        isValidHostname host && (["private.googleapis.com", "restricted.googleapis.com", "run.googleapis.com", "iam.googleapis.com",
          "secretmanager.googleapis.com", "sqladmin.googleapis.com", "cloudresourcemanager.googleapis.com", "networksecurity.googleapis.com"].contains host ||
          (host.endsWith "-run.googleapis.com" && host.length > 19 && (GcpRegion.parse? (host.dropEnd 19).toString).isSome))
    | _ => false

private def validateContainerImageUri (uri targetProjectId : String) : Except String String := do
  let bad (msg : String) : Except String String := .error s!"invalid container image URI `{uri}`: {msg}"
  if uri.isEmpty || uri != uri.cliTrim then return ← bad "must not be empty or have leading/trailing whitespace"
  if uri.toList.any (fun c => c.isWhitespace || c.toNat < 0x20 || c.toNat == 0x7F || "\\?#".contains c) then return ← bad "contains forbidden whitespace or control characters"
  if uri.contains ".." then return ← bad "contains `..`"
  match uri.splitOn "/" with
  | host :: proj :: rest =>
      if rest.isEmpty || rest.any (·.isEmpty) then return ← bad "missing repository/image path"
      let validHost := host == "gcr.io" || [".gcr.io", "-docker.pkg.dev"].any fun suf => host.endsWith suf && host.length > suf.length && isValidDnsLabel (host.dropEnd suf.length).toString
      if !validHost then return ← bad s!"host `{host}` must be `*-docker.pkg.dev` or `gcr.io`"
      if proj != targetProjectId then return ← bad s!"project `{proj}` does not match target GCP project `{targetProjectId}`"
      for seg in rest do if !seg.toList.all (fun c => c.isAlphanum || "._-:@".contains c) then return ← bad s!"invalid character in path segment `{seg}`"
      return uri
  | _ => bad "expected `<region>-docker.pkg.dev/<project>/<repo>/<image>:<tag>` or `gcr.io/<project>/<image>:<tag>`"

private def canonicalizeBuildDir (outDir : FilePath) : ExceptT String IO FilePath := do
  let raw := outDir.toString
  if raw.isEmpty || raw.startsWith "-" then throw s!"invalid build output directory `{raw}`"
  if !(← outDir.pathExists) then throw s!"build output directory does not exist: `{raw}`"
  let realDir ← ExceptT.mk (try Except.ok <$> IO.FS.realPath outDir catch e => pure (.error s!"failed to canonicalize build output directory `{raw}`: {e}"))
  let rs := realDir.toString
  if ← orB (rs.isEmpty || rs.startsWith "-") ((!·) <$> realDir.isDir) then throw s!"invalid canonical build output directory `{rs}`"
  return realDir

private def computeBuildHash (outDir : FilePath) (mod : String) : IO String := do
  let acc ← [outDir / "qed_manifest.json", outDir / "server"].foldlM (init := ByteArray.empty) fun a p => do
    if ← p.pathExists then return a ++ (← IO.FS.readBinFile p) else return a
  if !acc.isEmpty then return shortContentHash acc
  if ← (modOleanPath mod).pathExists then return shortContentHash (← IO.FS.readBinFile (modOleanPath mod))
  return shortContentHash mod.toUTF8

private def resolveGcpAuth (allowNone : Bool) : ExceptT String IO GcpAuthMode := do
  if let some t ← nonEmptyEnv "QED_GCP_TOKEN" then return .bearerToken t
  if let some s ← nonEmptyEnv "QED_GCP_SA_JSON" then return .serviceAccountJson s
  if let some credPath ← nonEmptyEnv "GOOGLE_APPLICATION_CREDENTIALS" then
    let p : FilePath := credPath; if ← p.pathExists then return .serviceAccountJson (← IO.FS.readFile p)
    throw s!"GOOGLE_APPLICATION_CREDENTIALS file not found: {p}"
  if allowNone then return .none
  throw "missing GCP credentials: set GOOGLE_APPLICATION_CREDENTIALS, QED_GCP_SA_JSON, or QED_GCP_TOKEN"

private def emitCloudPlan (mod envStr prStr prodProject nonProdProject tenantStr appStr buildHash : String)
    (outDir : FilePath) (deployName? : Option String) (needBuild : Bool) : ExceptT String IO GcpPlan := do
  let expectedKey ← liftP (DeployKey.mkCheckedStr prodProject nonProdProject tenantStr appStr envStr prStr)
  let some q ← resolveQedjsEnv (needBuild := needBuild) | throw "could not locate qedjs binary"
  let planDir : FilePath := ".qed" / "plans"; IO.FS.createDirAll planDir; let planDirReal ← IO.FS.realPath planDir
  let planPath : FilePath := planDir / s!"cloud_plan_{← Qed.Server.Prim.randomHex 16}.json"
  if ← planPath.pathExists then throw s!"unexpected existing plan temp file `{planPath}`"
  let args := #["--emit-cloud-plan", planPath.toString, mod, envStr, prStr, prodProject, nonProdProject, tenantStr, appStr, buildHash] ++
    (if ← outDir.pathExists then #["--assets-dir", outDir.toString] else #[]) ++ (deployName?.elim #[] fun d => #["--deploy", d]) ++ #[mod]
  let res ← liftIO <| try
    let out ← IO.Process.output { cmd := q.bin.toString, args, env := #[("LEAN_PATH", some q.leanPath)] }
    if out.exitCode != 0 then pure (.error s!"failed to compile cloud plan: {(out.stderr ++ out.stdout).cliTrim}")
    else do
      let planReal ← IO.FS.realPath planPath
      if !planReal.toString.startsWith (dirPrefix planDirReal) then pure (.error s!"cloud plan file resolved outside `{planDirReal}`")
      else pure <| (Qed.Json.parse (← IO.FS.readFile planReal).cliTrim).mapError (s!"invalid cloud plan JSON: {·}") >>= GcpPlan.fromJson
  finally removeIfExists planPath
  let plan ← liftP res
  if plan.key != expectedKey then throw s!"cloud plan key mismatch: got `{renderKeySlug plan.key}`, expected `{renderKeySlug expectedKey}`"
  if plan.buildHash != buildHash then throw s!"cloud plan buildHash mismatch: got `{plan.buildHash}`, expected `{buildHash}`"
  return plan

private def buildAndPushContainer (plan : GcpPlan) (region : GcpRegion) (outDir : FilePath) : ExceptT String IO String := do
  if !(← onPath "docker") then throw "docker not found on PATH (install Docker or pass `--image <artifact-registry-uri>`)"
  let realOutDir ← canonicalizeBuildDir outDir
  if !(← (realOutDir / "server").pathExists) then throw s!"missing native server binary `{realOutDir}/server` (run `qed build` first or pass `--image`)"
  let imageUri := s!"{region}-docker.pkg.dev/{plan.key.shard.projectFor plan.key.env}/qed-apps/{plan.cloudRunName}:{plan.buildHash}"
  discard <| liftE (writeFileInsideDir realOutDir ".dockerignore" "Dockerfile\n.dockerignore\nqed_deploy.json\n.git\n.git/**\n.env\n.env.*\n")
  let dfPath ← liftE (writeFileInsideDir realOutDir "Dockerfile" (
    "FROM debian:bookworm-slim\nRUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/* && useradd --system --uid 65532 --no-create-home --shell /usr/sbin/nologin qed\n" ++
    "WORKDIR /app\nCOPY . /app/dist\nRUN rm -f /app/dist/Dockerfile /app/dist/.dockerignore /app/dist/qed_deploy.json /app/dist/.env /app/dist/.env.* && chmod +x /app/dist/server && chown -R 65532:65532 /app\n" ++
    "USER 65532:65532\nEXPOSE 8080\nENV PORT=8080\nENTRYPOINT [\"/app/dist/server\", \"/app/dist\", \"8080\"]\n"))
  liftIO (step s!"building container image {imageUri}")
  if (← sh "docker" #["build", "--platform", "linux/amd64", "-t", imageUri, "-f", dfPath.toString, realOutDir.toString]) != 0 then throw s!"docker build failed for {imageUri}"
  liftIO (step s!"pushing container image {imageUri}")
  if (← sh "docker" #["push", imageUri]) != 0 then throw s!"docker push failed for {imageUri}"
  return imageUri

private def runDeploy (args : List String) : ExceptT String IO UInt32 := do
  let opts ← liftP (parseDeployOpts args {})
  let optOrEnv (o : Option String) (k : String) : IO (Option String) := o.elim (nonEmptyEnv k) (pure ∘ some)
  if opts.checkDrift && opts.teardown then throw "`--check-drift` and `--teardown` cannot be combined"
  if let some d := opts.distDir? then if d.isEmpty || d.startsWith "-" then throw s!"invalid `--dist` directory `{d}`"
  if opts.envStr == "preview" then match opts.prStr.toNat? with
    | some 0 => throw "`--env preview` requires `--pr <positive-number>`" | none => throw s!"invalid `--pr` number `{opts.prStr}`" | some _ => pure ()
  let isLocalApi := opts.apiBase?.any isStrictLoopbackUrl
  if let some apiUrl := opts.apiBase? then if !isLocalApi && !isAllowedRemoteApiBase apiUrl then
    throw s!"`--api-base` must be either a strict local loopback URL (`http://127.0.0.1[:port]`) or an `https://*.googleapis.com` endpoint (got `{apiUrl}`)"
  let mod ← liftIO (opts.mod?.elim jsRoot pure); let outDir : FilePath := (opts.distDir?.map FilePath.mk).getD distDir
  let baseProj ← optOrEnv opts.project? "QED_GCP_PROJECT"
  let prodProject := ((← optOrEnv opts.prodProject? "QED_GCP_PROD_PROJECT").orElse fun _ => baseProj).getD (if opts.dryRun || isLocalApi then "qed-local" else "")
  if prodProject.isEmpty then throw "missing GCP project: pass `--project <gcp-project>` (or `--prod-project` / `--nonprod-project`) or set `QED_GCP_PROJECT`"
  let nonProdProject := (← optOrEnv opts.nonProdProject? "QED_GCP_NONPROD_PROJECT").getD s!"{prodProject}-nonprod"
  if nonProdProject.isEmpty || prodProject == nonProdProject then throw "prod and non-prod GCP projects must be distinct (pass distinct `--prod-project` and `--nonprod-project`)"
  let (tenantStr, appStr) := ((← optOrEnv opts.tenantStr? "QED_TENANT_ID").getD "1", (← optOrEnv opts.appIdStr? "QED_APP_ID").getD "1")
  if !opts.skipBuild then
    if opts.dryRun || opts.checkDrift || opts.teardown then if (← shLakeBuild #["build", mod]) != 0 then throw s!"failed to build `{mod}`"
    else if (← cmdBuild (prod := true) (mod? := some mod) (outDir? := some outDir)) != 0 then throw "production build failed"
  let plan ← emitCloudPlan mod opts.envStr opts.prStr prodProject nonProdProject tenantStr appStr (← computeBuildHash outDir mod) outDir opts.deployName? (!opts.skipBuild)
  let region := plan.regions.headD .us_central1
  let auth ← if isLocalApi then pure GcpAuthMode.none else resolveGcpAuth (allowNone := opts.dryRun && !opts.checkDrift)
  let healthIdToken? ← if isLocalApi then pure none else nonEmptyEnv "QED_HEALTH_ID_TOKEN"
  let cfg : GcpExecConfig := {
    endpoints := (opts.apiBase?.map GcpEndpoints.allLocal).getD {}, auth, region,
    edgeSaEmail := (← nonEmptyEnv "QED_EDGE_SA_EMAIL").getD "qed-edge@qed-cloud.iam.gserviceaccount.com",
    builderSaEmail := (← nonEmptyEnv "QED_BUILDER_SA_EMAIL").getD "qed-builder@qed-cloud.iam.gserviceaccount.com",
    deployerSaEmail? := ← nonEmptyEnv "QED_DEPLOYER_SA_EMAIL", healthIdToken?, ssrfGuard := !isLocalApi,
    healthBaseUrl? := if isLocalApi then opts.apiBase? else none }
  let observe : ExceptT String IO GcpLiveSnapshot :=
    if opts.apiBase?.isSome || (match auth with | .none => false | _ => true) then
      liftE (observeGcpState cfg plan.key plan.managedDbs plan.regions plan.assetsArePublic)
    else pure { observed := { key := plan.key } }
  if opts.checkDrift then
    liftIO (step s!"checking live GCP drift for {plan.cloudRunName}"); let findings := checkDriftLive (← observe) plan
    if findings.isEmpty then liftIO (IO.println (green (formatDriftFindings findings))); return 0
    liftIO (IO.eprintln (red (formatDriftFindings findings))); return 1
  if opts.teardown then
    let actions := planPreviewTeardown (← observe).observed
    if actions.isEmpty then liftIO (IO.println (green s!"✓ teardown is a safe no-op for `{plan.key.env.toDeployEnv}` ({plan.cloudRunName})")); return 0
    if opts.dryRun then liftIO (IO.println (formatRolloutPlan plan actions)); return 0
    liftIO (step s!"tearing down preview {plan.cloudRunName} ({actions.length} action(s))")
    let n ← liftE (executeRollout cfg { plan with managedDbs := [] } "" outDir actions fun a => IO.println s!"  ▸ {formatAction a}")
    liftIO (IO.println (green s!"✓ preview teardown complete ({n} action(s))")); return 0
  let actions := planRollout (← observe).observed plan
  if opts.dryRun then liftIO (IO.println (formatRolloutPlan plan actions)); return 0
  let imageUri ← match ← optOrEnv (opts.image?.filter (!·.cliTrim.isEmpty)) "QED_CLOUD_IMAGE" with
    | some img => if isLocalApi then pure img else liftP (validateContainerImageUri img (plan.key.shard.projectFor plan.key.env))
    | none     => if isLocalApi then pure s!"local/{plan.cloudRunName}:{plan.buildHash}" else buildAndPushContainer plan region outDir
  liftIO (step s!"deploying {plan.cloudRunName} ({plan.key.env.toDeployEnv}) — {actions.length} action(s)")
  let n ← liftE (executeRollout cfg plan imageUri outDir actions fun a => IO.println s!"  ▸ [P{a.phase.rank}] {formatAction a}")
  liftIO (IO.println (green s!"✓ deploy complete: {plan.cloudRunName} ({n} action(s) across 4 phases)")); return 0

def cmdDeploy (args : List String) : IO UInt32 := do
  match ← (runDeploy args).run with | .ok code => return code | .error e => IO.eprintln (red s!"✗ {e}"); return 1

end Qed.Cli
