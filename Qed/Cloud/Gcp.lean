import Qed.Cloud.Env

/-! ## Formal GCP Cloud Run & IAM Model (`Qed.Cloud.Gcp`) -/

namespace Qed.Cloud

/-! ### 1. GCP Regions, Compute Tiers & Cloud Run Scaling Spec -/

inductive GcpRegion where
  | us_central1 | us_east1 | us_east4 | us_west1 | europe_west1 | europe_west4 | asia_east1 | asia_northeast1
deriving Inhabited, DecidableEq

def GcpRegion.toString : GcpRegion → String
  | .us_central1 => "us-central1" | .us_east1 => "us-east1" | .us_east4 => "us-east4" | .us_west1 => "us-west1"
  | .europe_west1 => "europe-west1" | .europe_west4 => "europe-west4" | .asia_east1 => "asia-east1" | .asia_northeast1 => "asia-northeast1"
instance : ToString GcpRegion := ⟨GcpRegion.toString⟩
def GcpRegion.all : List GcpRegion := [.us_central1, .us_east1, .us_east4, .us_west1, .europe_west1, .europe_west4, .asia_east1, .asia_northeast1]
def GcpRegion.allNames : List String := GcpRegion.all.map (·.toString.replace "-" "_")
def GcpRegion.parse? (s : String) : Option GcpRegion := let norm := s.replace "_" "-"; GcpRegion.all.find? (·.toString == norm)
def GcpRegion.inEu : GcpRegion → Bool | .europe_west1 | .europe_west4 => true | _ => false

inductive ComputeTier where | standard | performance | large | xlarge
deriving Inhabited, DecidableEq

def ComputeTier.specs : ComputeTier → Nat × Nat | .standard => (2048, 1000) | .performance => (4096, 2000) | .large => (8192, 4000) | .xlarge => (16384, 8000)
def ComputeTier.memoryMb (t : ComputeTier) : Nat := t.specs.1
def ComputeTier.cpuMilli (t : ComputeTier) : Nat := t.specs.2
def ComputeTier.toString : ComputeTier → String | .standard => "standard" | .performance => "performance" | .large => "large" | .xlarge => "xlarge"
def ComputeTier.all : List ComputeTier := [.standard, .performance, .large, .xlarge]
def ComputeTier.allNames : List String := ComputeTier.all.map ComputeTier.toString
def ComputeTier.parse? (s : String) : Option ComputeTier := ComputeTier.all.find? (·.toString == s)

structure ScaleSpec where
  (minInstances : Nat := 0) (maxInstances : Nat := 100) (memoryMb : Nat := 2048) (cpuMilli concurrency : Nat := 1000) (timeoutSec : Nat := 60)
deriving Inhabited, DecidableEq

def minCpuRules : List (Nat × Nat × String) :=
  [(24576, 8000, "8 vCPU"), (16384, 6000, "at least 6 vCPU"), (8192, 4000, "at least 4 vCPU"),
   (4096, 2000, "at least 2 vCPU"), (1024, 1000, "at least 1 vCPU"), (512, 500, "at least 500m CPU")]
def minMemRules : List (Nat × Nat × String) := [(6000, 4096, "4gb"), (4000, 2048, "2gb"), (2000, 512, "512mb")]

def ScaleSpec.validate (s : ScaleSpec) : Except String Unit := do
  let failIf (bad : Bool) (msg : String) : Except String Unit := if bad then .error s!"scale: {msg}" else .ok ()
  failIf (s.maxInstances == 0) "`max_instances` must be at least 1"
  failIf (s.minInstances > s.maxInstances) s!"`min_instances` ({s.minInstances}) cannot exceed `max_instances` ({s.maxInstances})"
  failIf (s.memoryMb < 128 || s.memoryMb > 32768) s!"unsupported Cloud Run `memory` ({s.memoryMb}mb; expected 128mb..32gb)"
  failIf (!(s.cpuMilli ∈ [250, 500, 1000, 2000, 4000, 6000, 8000])) s!"unsupported Cloud Run `cpu` ({s.cpuMilli}m)"
  if let some (_, _, req) := minCpuRules.find? fun (m, c, _) => s.memoryMb > m && s.cpuMilli < c then
    failIf true s!"Cloud Run `memory` {s.memoryMb}mb requires {req}"
  if let some (_, _, req) := minMemRules.find? fun (c, m, _) => s.cpuMilli ≥ c && s.memoryMb < m then
    failIf true s!"Cloud Run {s.cpuMilli / 1000} vCPU requires at least {req} `memory` (got {s.memoryMb}mb)"
  failIf (s.cpuMilli < 1000 && s.concurrency > 1) "fractional `cpu` (< 1 vCPU) on Cloud Run requires `concurrency` = 1 (or raise `cpu` to >= 1)"
  failIf (s.concurrency == 0 || s.concurrency > 1000) s!"`concurrency` ({s.concurrency}) must be between 1 and 1000"
  failIf (s.timeoutSec == 0 || s.timeoutSec > 3600) s!"`timeout` ({s.timeoutSec}s) must be between 1s and 3600s"

theorem ScaleSpec.validate_default_ok : ({} : ScaleSpec).validate = .ok () := rfl

/-! ### 2. Preview & Top-Level `DeploySpec` -/

inductive PreviewProtection where | team_only | pub
deriving Inhabited, DecidableEq

structure PreviewSpec where
  (enabled : Bool := true) (subdomain? : Option String := some "preview") (host? : Option HostPattern := none)
  (protection : PreviewProtection := .team_only) (ttlSec : Nat := 7 * 86400)
deriving Inhabited, DecidableEq

abbrev PreviewSpec.subdomain (p : PreviewSpec) : Option String := p.subdomain?
abbrev PreviewSpec.host (p : PreviewSpec) : Option HostPattern := p.host?
abbrev PreviewSpec.ttl_sec (p : PreviewSpec) : Nat := p.ttlSec

def PreviewSpec.resolvedHost? (p : PreviewSpec) (prodDomain? : Option String) : Option HostPattern :=
  p.host?.orElse fun _ => match prodDomain?, p.subdomain? with | some prod, some sub => some (derivePreviewHost prod sub) | _, _ => none

structure DeploySpec where
  (name appName : String) (regions : List GcpRegion := [.us_central1]) (domain? : Option String := none)
  (compute : ComputeTier := .standard) (timeoutSec? : Option Nat := none) (preview : PreviewSpec := {})
deriving Inhabited, DecidableEq

inductive DeploySection where | regions | timeout | domain | preview
deriving Inhabited, DecidableEq

def DeploySpec.validateSectioned (d : DeploySpec) : Except (DeploySection × String) Unit := do
  let check (sec : DeploySection) (bad : Bool) (msg : String) : Except (DeploySection × String) Unit :=
    if bad then .error (sec, s!"`deploy {d.name}`: {msg}") else .ok ()
  if d.name.isEmpty then .error (.regions, "`deploy`: `name` must be non-empty")
  for (sec, bad, msg) in [(.regions, d.appName.isEmpty, "`appName` must be non-empty"),
      (.regions, d.regions.isEmpty, "`regions` must list at least one GCP region"),
      (.regions, d.regions.eraseDups.length != d.regions.length, "`regions` must not contain duplicates")] do check sec bad msg
  if let some t := d.timeoutSec? then check .timeout (t == 0 || t > 3600) s!"`timeout` ({t}s) must be between 1s and 3600s"
  if let some dom := d.domain? then
    check .domain (!isValidHostname dom) s!"invalid RFC 1123 production `domain` `{dom}` (omit scheme/path/trailing dot)"
    check .domain (isReservedLocalDomain dom) s!"production `domain` `{dom}` cannot use reserved local domain (`.localhost` / `.local`)"
  if d.preview.enabled then
    check .preview (d.preview.ttlSec == 0) "preview `ttl` must be positive"
    if let some sub := d.preview.subdomain? then check .preview (!isValidDnsLabel sub) s!"invalid preview `subdomain` label `{sub}`"
    if let some hp := d.preview.resolvedHost? d.domain? then
      check .preview (!hp.isValid) s!"invalid preview host `{hp.render}`"
      check .preview (isReservedLocalDomain hp.baseHost) s!"preview host `{hp.render}` cannot use reserved local domain (`.localhost` / `.local`)"
      if let some prodDom := d.domain? then
        check .preview (hp.matches prodDom) s!"preview host `{hp.render}` overlaps production domain `{prodDom}`"
        check .preview (isDomainAncestor hp.baseHost prodDom) s!"preview host `{hp.render}` is an ancestor of production domain `{prodDom}` (cookie-tossing risk)"

def DeploySpec.validate (d : DeploySpec) : Except String Unit := d.validateSectioned.mapError Prod.snd

/-! ### 3. Canonical Proved-Injective GCP Naming (`DeployKey`, `renderSaId`, `renderCloudRunName`) -/

structure BoundedId (bound : Nat) where (num : Nat) (valid : num < bound)
deriving DecidableEq
instance {b : Nat} [NeZero b] : Inhabited (BoundedId b) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne b)⟩⟩
abbrev TenantId := BoundedId 1000000
abbrev AppId    := BoundedId 100000
abbrev PrId     := BoundedId 100000

inductive EnvInstance where | prod | staging | preview (pr : PrId)
deriving Inhabited, DecidableEq
def EnvInstance.toDeployEnv : EnvInstance → DeployEnv | .prod => .prod | .staging => .staging | .preview _ => .preview
def EnvInstance.isProd : EnvInstance → Bool | .prod => true | _ => false
def EnvInstance.isPreview : EnvInstance → Bool | .preview _ => true | _ => false

structure ShardProject where (prodProjectId nonProdProjectId : String) (separated : prodProjectId ≠ nonProdProjectId)
deriving DecidableEq
instance : Inhabited ShardProject := ⟨⟨"qed-prod", "qed-nonprod", by decide⟩⟩
def ShardProject.projectFor (s : ShardProject) : EnvInstance → String | .prod => s.prodProjectId | _ => s.nonProdProjectId
def ShardProject.clusterProject (s : ShardProject) : DbCluster → String | .prodCluster => s.prodProjectId | .nonProdCluster => s.nonProdProjectId
def ShardProject.mkPair (prodId nonProdId : String) : Except String ShardProject :=
  if h : prodId = nonProdId then .error s!"shard projects must be distinct: prod (`{prodId}`) and non-prod (`{nonProdId}`) cannot share a GCP project" else .ok ⟨prodId, nonProdId, h⟩

structure DeployKey where (shard : ShardProject) (tenant : TenantId) (app : AppId) (env : EnvInstance)
deriving Inhabited, DecidableEq

def encNatAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc | k + 1, n, acc => let d := Char.ofNat (48 + n % 10); if n < 10 then d :: acc else encNatAux k (n / 10) (d :: acc)
def encNat (n : Nat) : String := String.ofList (encNatAux 10 n [])
def decDigitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc | c :: cs => if '0' ≤ c && c ≤ '9' then decDigitsAux (acc * 10 + (c.toNat - 48)) cs else none
def decNat (s : String) : Option Nat := match s.toList with | [] => none | cs => decDigitsAux 0 cs

private theorem encNatAux_bounds (d k n : Nat) (hn : n < 10 ^ (d + 1)) (hk : d + 1 ≤ k) (acc : List Char) :
    acc.length < (encNatAux k n acc).length ∧ (encNatAux k n acc).length ≤ d + 1 + acc.length := by
  induction d generalizing k n acc with
  | zero => cases k with | zero => omega | succ _ => have h10 : n < 10 := (by simpa using hn); simp [encNatAux, h10]; omega
  | succ d ih => cases k with | zero => omega | succ k' =>
      simp only [encNatAux]; split
      · simp; omega
      · have h := ih k' (n / 10) (by rw [Nat.pow_succ] at hn; omega) (by omega) (Char.ofNat (48 + n % 10) :: acc); simp at h; omega

private theorem encNat_len_bounds {d n : Nat} (hn : n < 10 ^ (d + 1)) (hd : d ≤ 9) :
    1 ≤ (encNat n).toList.length ∧ (encNat n).toList.length ≤ d + 1 := by
  have h := encNatAux_bounds d 10 n hn (by omega) []; simp only [encNat, String.toList_ofList, List.length_nil, Nat.add_zero] at h ⊢; omega

private theorem char_ofNat_digit (d : Nat) (hd : d < 10) :
    '0' ≤ Char.ofNat (48 + d) ∧ Char.ofNat (48 + d) ≤ '9' ∧ (Char.ofNat (48 + d)).toNat - 48 = d :=
  (by decide : ∀ i : Fin 10, '0' ≤ Char.ofNat (48 + i.val) ∧ Char.ofNat (48 + i.val) ≤ '9' ∧ (Char.ofNat (48 + i.val)).toNat - 48 = i.val) ⟨d, hd⟩

private theorem encNatAux_all_digits (k n : Nat) (acc : List Char) (hacc : ∀ c ∈ acc, '0' ≤ c ∧ c ≤ '9') :
    ∀ c ∈ encNatAux k n acc, '0' ≤ c ∧ c ≤ '9' := by
  induction k generalizing n acc with
  | zero => exact hacc
  | succ k ih =>
      have hd := char_ofNat_digit (n % 10) (Nat.mod_lt _ (by decide))
      have hnext : ∀ c ∈ Char.ofNat (48 + n % 10) :: acc, '0' ≤ c ∧ c ≤ '9' := fun c hc => (List.mem_cons.mp hc).elim (fun h => h ▸ ⟨hd.1, hd.2.1⟩) (hacc c)
      simp only [encNatAux]; split; exact hnext; exact ih (n / 10) _ hnext

private theorem decDigitsAux_encNatAux (k n : Nat) (hbound : n < 10 ^ k) (cs : List Char) :
    decDigitsAux 0 (encNatAux k n cs) = decDigitsAux n cs := by
  have step (acc d : Nat) (hd : d < 10) (xs : List Char) : decDigitsAux acc (Char.ofNat (48 + d) :: xs) = decDigitsAux (acc * 10 + d) xs := by
    have h := char_ofNat_digit d hd; simp [decDigitsAux, h.1, h.2.1, h.2.2]
  induction k generalizing n cs with
  | zero => simp at hbound; subst hbound; rfl
  | succ k ih =>
      simp only [encNatAux]; split
      · rename_i hlt; rw [step 0 (n % 10) (Nat.mod_lt _ (by decide))]; simp [Nat.mod_eq_of_lt hlt]
      · rw [ih (n / 10) (by rw [Nat.pow_succ] at hbound; omega) _, step (n / 10) (n % 10) (Nat.mod_lt _ (by decide)), show n / 10 * 10 + n % 10 = n by omega]

theorem decNat_encNat (n : Nat) (hn : n < 10000000000) : decNat (encNat n) = some n := by
  unfold decNat encNat; rw [String.toList_ofList]; have hpos := (encNatAux_bounds 9 10 n hn (by decide) []).1
  cases h : encNatAux 10 n [] with | nil => simp [h] at hpos | cons _ _ => have hdec := decDigitsAux_encNatAux 10 n hn []; rwa [h] at hdec
theorem encNat_injective {a b : Nat} (ha : a < 10000000000) (hb : b < 10000000000) (heq : encNat a = encNat b) : a = b :=
  Option.some.inj ((decNat_encNat a ha).symm.trans (heq ▸ decNat_encNat b hb))
theorem encNat_no_hyphen (n : Nat) : '-' ∉ (encNat n).toList := fun hmem => by
  rw [encNat, String.toList_ofList] at hmem; exact absurd (encNatAux_all_digits 10 n [] (by simp) '-' hmem).1 (by decide)

def renderEnvTag : EnvInstance → String | .prod => "p" | .staging => "s" | .preview pr => "r" ++ encNat pr.num
def renderKeySlug (k : DeployKey) : String := encNat k.tenant.num ++ "-" ++ encNat k.app.num ++ "-" ++ renderEnvTag k.env
def renderSaId (k : DeployKey) : String := "q-" ++ renderKeySlug k
def renderSaEmail (k : DeployKey) : String := renderSaId k ++ "@" ++ k.shard.projectFor k.env ++ ".iam.gserviceaccount.com"
def renderCloudRunName (k : DeployKey) : String := "cr-" ++ renderKeySlug k

private theorem append_hyphen_inj {a₁ b₁ a₂ b₂ : List Char} (h1 : '-' ∉ a₁) (h2 : '-' ∉ a₂)
    (heq : a₁ ++ '-' :: b₁ = a₂ ++ '-' :: b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  match a₁, a₂ with
  | [], [] => simp_all | [], _ :: _ => cases heq; exact absurd List.mem_cons_self h2 | _ :: _, [] => cases heq; exact absurd List.mem_cons_self h1
  | c :: cs, d :: ds =>
      injection heq with hcd htail; subst hcd
      have ⟨hcs, hb⟩ := append_hyphen_inj (fun hm => h1 (List.mem_cons_of_mem _ hm)) (fun hm => h2 (List.mem_cons_of_mem _ hm)) htail
      exact ⟨congrArg (c :: ·) hcs, hb⟩

private theorem str_eq_of_toList {s₁ s₂ : String} (h : s₁.toList = s₂.toList) : s₁ = s₂ := by
  rw [← String.ofList_toList (s := s₁), ← String.ofList_toList (s := s₂), h]
private theorem str_append_left_inj {p a b : String} (h : p ++ a = p ++ b) : a = b :=
  str_eq_of_toList (List.append_cancel_left (by simpa only [String.toList_append] using congrArg String.toList h))

private theorem renderEnvTag_injective {e₁ e₂ : EnvInstance} (heq : renderEnvTag e₁ = renderEnvTag e₂) : e₁ = e₂ := by
  have hlist := congrArg String.toList heq
  cases e₁ <;> cases e₂ <;> simp [renderEnvTag, String.toList_append] at hlist
  · rfl
  · rfl
  case preview.preview pr₁ pr₂ =>
    have hn := encNat_injective (by have := pr₁.valid; omega) (by have := pr₂.valid; omega) (str_eq_of_toList hlist)
    cases pr₁; cases pr₂; simp_all

theorem renderKeySlug_injective {k₁ k₂ : DeployKey} (hshard : k₁.shard = k₂.shard) (heq : renderKeySlug k₁ = renderKeySlug k₂) : k₁ = k₂ := by
  rcases k₁ with ⟨sh₁, ⟨t₁, _⟩, ⟨a₁, _⟩, e₁⟩; rcases k₂ with ⟨sh₂, ⟨t₂, _⟩, ⟨a₂, _⟩, e₂⟩
  simp only at hshard; subst hshard
  have hlist : (encNat t₁).toList ++ '-' :: ((encNat a₁).toList ++ '-' :: (renderEnvTag e₁).toList) =
      (encNat t₂).toList ++ '-' :: ((encNat a₂).toList ++ '-' :: (renderEnvTag e₂).toList) := by
    simpa [renderKeySlug, String.toList_append, List.append_assoc] using congrArg String.toList heq
  rcases append_hyphen_inj (encNat_no_hyphen t₁) (encNat_no_hyphen t₂) hlist with ⟨htL, hrest⟩
  rcases append_hyphen_inj (encNat_no_hyphen a₁) (encNat_no_hyphen a₂) hrest with ⟨haL, heL⟩
  have htEq := encNat_injective (by omega) (by omega) (str_eq_of_toList htL)
  have haEq := encNat_injective (by omega) (by omega) (str_eq_of_toList haL)
  have heEq := renderEnvTag_injective (str_eq_of_toList heL)
  subst htEq haEq heEq; rfl

theorem renderSaId_injective {k₁ k₂ : DeployKey} (hshard : k₁.shard = k₂.shard) (heq : renderSaId k₁ = renderSaId k₂) : k₁ = k₂ :=
  renderKeySlug_injective hshard (str_append_left_inj heq)
theorem renderCloudRunName_injective {k₁ k₂ : DeployKey} (hshard : k₁.shard = k₂.shard) (heq : renderCloudRunName k₁ = renderCloudRunName k₂) : k₁ = k₂ :=
  renderKeySlug_injective hshard (str_append_left_inj heq)

private theorem renderKeySlug_length_bounds (k : DeployKey) : 5 ≤ (renderKeySlug k).toList.length ∧ (renderKeySlug k).toList.length ≤ 19 := by
  have ht := encNat_len_bounds (d := 5) k.tenant.valid (by decide); have ha := encNat_len_bounds (d := 4) k.app.valid (by decide)
  have he : 1 ≤ (renderEnvTag k.env).toList.length ∧ (renderEnvTag k.env).toList.length ≤ 6 := by
    cases h : k.env with | prod | staging => decide | preview pr => have := encNat_len_bounds (d := 4) pr.valid (by decide); simp [renderEnvTag, String.toList_append] at *; omega
  simp [renderKeySlug, String.toList_append] at *; omega
theorem renderSaId_gcp_length_valid (k : DeployKey) : 6 ≤ (renderSaId k).toList.length ∧ (renderSaId k).toList.length ≤ 30 := by
  have := renderKeySlug_length_bounds k; simp [renderSaId, String.toList_append] at *; omega
theorem renderCloudRunName_gcp_length_valid (k : DeployKey) : 6 ≤ (renderCloudRunName k).toList.length ∧ (renderCloudRunName k).toList.length ≤ 63 := by
  have := renderKeySlug_length_bounds k; simp [renderCloudRunName, String.toList_append] at *; omega

/-! ### 4. Open Principal Universe, Typed Roles (No `owner`/`editor`), & IAM Semantics -/

inductive GcpPrincipal where | allUsers | allAuthenticatedUsers | builder | edgeRouter | runtimeSa (key : DeployKey) | external (email : String)
deriving Inhabited, DecidableEq

inductive GcpPermission where
  | secretAccessor | runInvoke | cloudSqlClient | storageObjectViewer | storageObjectAdmin | iamSetPolicy | iamActAs | iamGetAccessToken | iamSignJwt
deriving Inhabited, DecidableEq
def GcpPermission.isEscalation : GcpPermission → Bool | .iamSetPolicy | .iamActAs | .iamGetAccessToken | .iamSignJwt => true | _ => false

inductive GcpRole where | secretManagerAccessor | runInvoker | cloudSqlClient | storageLegacyObjectReader | storageObjectAdmin
deriving Inhabited, DecidableEq
def GcpRole.gcpName : GcpRole → String
  | .secretManagerAccessor => "roles/secretmanager.secretAccessor" | .runInvoker => "roles/run.invoker" | .cloudSqlClient => "roles/cloudsql.client"
  | .storageLegacyObjectReader => "roles/storage.legacyObjectReader" | .storageObjectAdmin => "roles/storage.objectAdmin"
def GcpRole.permissions : GcpRole → List GcpPermission
  | .secretManagerAccessor => [.secretAccessor] | .runInvoker => [.runInvoke] | .cloudSqlClient => [.cloudSqlClient]
  | .storageLegacyObjectReader => [.storageObjectViewer] | .storageObjectAdmin => [.storageObjectAdmin, .storageObjectViewer]
theorem GcpRole.no_escalation (role : GcpRole) (perm : GcpPermission) (h : perm ∈ role.permissions) : perm.isEscalation = false := by
  cases role <;> simp [GcpRole.permissions] at h <;> rcases h with rfl | rfl <;> rfl

inductive GcpResource where
  | secret (key : DeployKey) (secretName : String) | cloudRun (key : DeployKey)
  | cloudSqlDb (cluster : DbCluster) (key : DeployKey) (dbName : String)
  | assetPrefix (key : DeployKey) (buildHash : String) (isPublic : Bool := true) | project (projectId : String)
deriving Inhabited, DecidableEq

def GcpResource.ownerKey? : GcpResource → Option DeployKey
  | .secret k _ | .cloudRun k | .cloudSqlDb _ k _ | .assetPrefix k _ _ => some k | .project _ => none
def GcpResource.ownerKey (r : GcpResource) : DeployKey := r.ownerKey?.getD default
theorem GcpResource.ownerKey?_eq_some_imp_ownerKey {r : GcpResource} {k : DeployKey} (h : r.ownerKey? = some k) : r.ownerKey = k := by
  simp [GcpResource.ownerKey, h]
def GcpResource.projectOf : GcpResource → String
  | .cloudSqlDb cl k _ => k.shard.clusterProject cl | .project p => p | r => r.ownerKey.shard.projectFor r.ownerKey.env
def GcpResource.isProdResource : GcpResource → Bool
  | .cloudSqlDb .prodCluster _ _ => true | .cloudSqlDb .nonProdCluster _ _ | .project _ => false | r => r.ownerKey.env.isProd
theorem GcpResource.projectOf_of_isProdResource {r : GcpResource} (hprod : r.isProdResource = true) : r.projectOf = r.ownerKey.shard.prodProjectId := by
  cases r with
  | cloudSqlDb cl k db => cases cl <;> (try rfl); simp [GcpResource.isProdResource] at hprod
  | project p => simp [GcpResource.isProdResource] at hprod
  | secret k _ | cloudRun k | assetPrefix k _ _ =>
      cases h : k.env <;> simp [GcpResource.isProdResource, GcpResource.ownerKey, GcpResource.ownerKey?, EnvInstance.isProd, h] at hprod
      simp [GcpResource.projectOf, GcpResource.ownerKey, GcpResource.ownerKey?, ShardProject.projectFor, h]
def GcpResource.isPublicAsset : GcpResource → Bool | .assetPrefix _ _ true => true | _ => false
def GcpResource.isAsset : GcpResource → Bool | .assetPrefix _ _ _ => true | _ => false
def GcpResource.bindingApplies (bindingRes targetRes : GcpResource) : Prop := bindingRes = targetRes ∨ bindingRes = .project targetRes.projectOf

structure GcpIamBinding where (principal : GcpPrincipal) (role : GcpRole) (resource : GcpResource)
deriving Inhabited, DecidableEq
structure GcpDenyRule where (principals : List GcpPrincipal) (permissions : List GcpPermission) (resource : GcpResource)
deriving Inhabited, DecidableEq
structure GcpPolicyState where (bindings : List GcpIamBinding := []) (denies : List GcpDenyRule := []) (egressAllow : List (DeployKey × String) := [])
deriving Inhabited, DecidableEq

def GcpPolicyState.allows (st : GcpPolicyState) (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) : Prop :=
  (∃ b ∈ st.bindings, b.principal = p ∧ b.resource.bindingApplies r ∧ perm ∈ b.role.permissions) ∧
  ¬ (∃ d ∈ st.denies, p ∈ d.principals ∧ perm ∈ d.permissions ∧ d.resource.bindingApplies r)
def GcpPolicyState.canStep (st : GcpPolicyState) (p₁ _p₂ : GcpPrincipal) : Prop := ∃ perm r, perm.isEscalation = true ∧ st.allows p₁ perm r
inductive GcpPolicyState.canReachPrincipal (st : GcpPolicyState) : GcpPrincipal → GcpPrincipal → Prop where
  | refl (p : GcpPrincipal) : st.canReachPrincipal p p
  | step {p₁ p₂ p₃ : GcpPrincipal} : st.canStep p₁ p₂ → st.canReachPrincipal p₂ p₃ → st.canReachPrincipal p₁ p₃
def GcpPolicyState.canReach (st : GcpPolicyState) (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) : Prop :=
  ∃ p', st.canReachPrincipal p p' ∧ st.allows p' perm r
def GcpPolicyState.egressAllowed (st : GcpPolicyState) (k : DeployKey) (origin : String) : Prop := (k, origin) ∈ st.egressAllow

/-! ### 5. Four-Phase Zero-Downtime Cloud Run Rollout Model -/

inductive RolloutPhase where | phase1_provision | phase2_deployZero | phase3_shiftTraffic | phase4_cleanup
deriving Inhabited, DecidableEq
def RolloutPhase.rank : RolloutPhase → Nat | .phase1_provision => 1 | .phase2_deployZero => 2 | .phase3_shiftTraffic => 3 | .phase4_cleanup => 4

inductive GcpAction where
  | uploadAssets (key : DeployKey) (buildHash : String) (paths : List String)
  | ensureSecret (key : DeployKey) (secretName : String) | ensureDb (cluster : DbCluster) (key : DeployKey) (dbName : String)
  | grantBinding (binding : GcpIamBinding) | putDenyRule (rule : GcpDenyRule) | setEgressRules (key : DeployKey) (origins : List String)
  | deployRevisionZero (key : DeployKey) (buildHash : String) (scale : ScaleSpec)
  | healthCheck (key : DeployKey) (buildHash : String) | shiftTraffic100 (key : DeployKey) (buildHash : String)
  | revokeBinding (binding : GcpIamBinding) | deleteSecret (key : DeployKey) (secretName : String)
  | narrowEgressRules (key : DeployKey) (origins : List String) | deleteService (key : DeployKey)
  | dropPreviewDb (key : DeployKey) (dbName : String) | pruneDenyException (key : DeployKey)
  | deleteServiceAccount (key : DeployKey) | deleteEgressPolicy (key : DeployKey)
deriving Inhabited, DecidableEq

def GcpAction.phase : GcpAction → RolloutPhase
  | .uploadAssets _ _ _ | .ensureSecret _ _ | .ensureDb _ _ _ | .grantBinding _ | .putDenyRule _ | .setEgressRules _ _ => .phase1_provision
  | .deployRevisionZero _ _ _ | .healthCheck _ _ => .phase2_deployZero | .shiftTraffic100 _ _ => .phase3_shiftTraffic
  | .revokeBinding _ | .deleteSecret _ _ | .narrowEgressRules _ _ | .deleteService _
  | .dropPreviewDb _ _ | .pruneDenyException _ | .deleteServiceAccount _ | .deleteEgressPolicy _ => .phase4_cleanup
def GcpAction.isDestructive (a : GcpAction) : Bool := a.phase == .phase4_cleanup
def GcpAction.targetKey : GcpAction → DeployKey
  | .grantBinding b | .revokeBinding b => b.resource.ownerKey | .putDenyRule d => d.resource.ownerKey
  | .uploadAssets k _ _ | .ensureSecret k _ | .ensureDb _ k _ | .setEgressRules k _ | .deployRevisionZero k _ _
  | .healthCheck k _ | .shiftTraffic100 k _ | .deleteSecret k _ | .narrowEgressRules k _ | .deleteService k
  | .dropPreviewDb k _ | .pruneDenyException k | .deleteServiceAccount k | .deleteEgressPolicy k => k
def actionsPhaseOrdered : List GcpAction → Prop
  | [] | [_] => True | a :: b :: xs => a.phase.rank ≤ b.phase.rank ∧ actionsPhaseOrdered (b :: xs)

end Qed.Cloud
