import Qed.Cloud.Env

/-! ## Formal GCP Cloud Run & IAM Model (`Qed.Cloud.Gcp`)
    Pure, total, axiom-free model of Qed Cloud's opinionated GCP Cloud Run topology:
    - Typed `GcpRegion`, `ScaleSpec` (full Cloud Run CPU↔memory↔concurrency↔timeout tier checks),
      `PreviewSpec`, and `DeploySpec` (with section-tagged validation errors).
    - Proved-injective, GCP-length-bounded canonical Service Account (`[6, 30]`) and Cloud Run
      service (`[6, 63]`) naming (`renderSaId_injective`, `renderCloudRunName_injective`).
    - Open `GcpPrincipal` universe (including `allUsers`, `allAuthenticatedUsers`, `external`).
    - Typed predefined `GcpRole`s (basic `roles/owner` and `roles/editor` are unrepresentable).
    - Formal IAM `allows` (allow ∧ ¬deny) and conservative transitive escalation reachability (`canReach`).
    - 4-phase zero-downtime Cloud Run rollout model (`RolloutPhase`, `GcpAction`). -/

namespace Qed.Cloud

/-! ### 1. GCP Regions & Cloud Run Scaling Spec -/

inductive GcpRegion where
  | us_central1
  | us_east1
  | us_east4
  | us_west1
  | europe_west1
  | europe_west4
  | asia_east1
  | asia_northeast1
deriving Inhabited, DecidableEq, Repr

def GcpRegion.toString : GcpRegion → String
  | .us_central1     => "us-central1"
  | .us_east1        => "us-east1"
  | .us_east4        => "us-east4"
  | .us_west1        => "us-west1"
  | .europe_west1    => "europe-west1"
  | .europe_west4    => "europe-west4"
  | .asia_east1      => "asia-east1"
  | .asia_northeast1 => "asia-northeast1"

instance : ToString GcpRegion := ⟨GcpRegion.toString⟩

def GcpRegion.all : List GcpRegion :=
  [.us_central1, .us_east1, .us_east4, .us_west1, .europe_west1, .europe_west4, .asia_east1, .asia_northeast1]

def GcpRegion.allNames : List String :=
  GcpRegion.all.map fun r => r.toString.replace "-" "_"

def GcpRegion.parse? (s : String) : Option GcpRegion :=
  let norm := s.replace "_" "-"
  GcpRegion.all.find? (·.toString == norm)

def GcpRegion.inEu : GcpRegion → Bool
  | .europe_west1 | .europe_west4 => true
  | _                             => false

/-- Vercel-style bundled `(vCPU, RAM)` compute presets, all valid on Cloud Run by construction. -/
inductive ComputeTier where
  | standard     -- 1 vCPU,  2 GB RAM (default)
  | performance  -- 2 vCPU,  4 GB RAM
  | large        -- 4 vCPU,  8 GB RAM
  | xlarge       -- 8 vCPU, 16 GB RAM
deriving Inhabited, DecidableEq, Repr

/-- `(memoryMb, cpuMilli, defaultConcurrency)` tuned for Qed's epoll Rust/Lean runtime. -/
def ComputeTier.specs : ComputeTier → Nat × Nat × Nat
  | .standard    => (2048, 1000, 250)
  | .performance => (4096, 2000, 500)
  | .large       => (8192, 4000, 1000)
  | .xlarge      => (16384, 8000, 1000)

def ComputeTier.memoryMb (t : ComputeTier) : Nat := t.specs.1
def ComputeTier.cpuMilli (t : ComputeTier) : Nat := t.specs.2.1
def ComputeTier.defaultConcurrency (t : ComputeTier) : Nat := t.specs.2.2

def ComputeTier.toString : ComputeTier → String
  | .standard    => "standard"
  | .performance => "performance"
  | .large       => "large"
  | .xlarge      => "xlarge"

def ComputeTier.all : List ComputeTier := [.standard, .performance, .large, .xlarge]
def ComputeTier.allNames : List String := ComputeTier.all.map ComputeTier.toString
def ComputeTier.parse? (s : String) : Option ComputeTier := ComputeTier.all.find? (·.toString == s)

/-- Compiled Cloud Run container scaling & hardware configuration (platform-derived in `compileInfra`). -/
structure ScaleSpec where
  minInstances : Nat := 0
  maxInstances : Nat := 100
  memoryMb     : Nat := 2048
  cpuMilli     : Nat := 1000
  concurrency  : Nat := 250
  timeoutSec   : Nat := 60
deriving Inhabited, DecidableEq, Repr

def minCpuRules : List (Nat × Nat × String) :=
  [(24576, 8000, "8 vCPU"), (16384, 6000, "at least 6 vCPU"), (8192, 4000, "at least 4 vCPU"),
   (4096, 2000, "at least 2 vCPU"), (1024, 1000, "at least 1 vCPU"), (512, 500, "at least 500m CPU")]

def minMemRules : List (Nat × Nat × String) :=
  [(6000, 4096, "4gb"), (4000, 2048, "2gb"), (2000, 512, "512mb")]

/-- Exact Cloud Run hardware coupling & tier validation. -/
def ScaleSpec.validate (s : ScaleSpec) : Except String Unit := do
  if s.maxInstances == 0 then
    .error "scale: `max_instances` must be at least 1"
  if s.minInstances > s.maxInstances then
    .error s!"scale: `min_instances` ({s.minInstances}) cannot exceed `max_instances` ({s.maxInstances})"
  if s.memoryMb < 128 || s.memoryMb > 32768 then
    .error s!"scale: unsupported Cloud Run `memory` ({s.memoryMb}mb; expected 128mb..32gb)"
  if !(s.cpuMilli ∈ [250, 500, 1000, 2000, 4000, 6000, 8000]) then
    .error s!"scale: unsupported Cloud Run `cpu` ({s.cpuMilli}m)"
  if let some (_, _, req) := minCpuRules.find? fun (m, c, _) => s.memoryMb > m && s.cpuMilli < c then
    .error s!"scale: Cloud Run `memory` {s.memoryMb}mb requires {req}"
  if let some (_, _, req) := minMemRules.find? fun (c, m, _) => s.cpuMilli ≥ c && s.memoryMb < m then
    .error s!"scale: Cloud Run {s.cpuMilli / 1000} vCPU requires at least {req} `memory` (got {s.memoryMb}mb)"
  if s.cpuMilli < 1000 && s.concurrency > 1 then
    .error "scale: fractional `cpu` (< 1 vCPU) on Cloud Run requires `concurrency` = 1 (or raise `cpu` to >= 1)"
  if s.concurrency == 0 || s.concurrency > 1000 then
    .error s!"scale: `concurrency` ({s.concurrency}) must be between 1 and 1000"
  if s.timeoutSec == 0 || s.timeoutSec > 3600 then
    .error s!"scale: `timeout` ({s.timeoutSec}s) must be between 1s and 3600s"

theorem ScaleSpec.validate_default_ok : ({} : ScaleSpec).validate = .ok () := rfl

/-! ### 2. Preview & Top-Level `DeploySpec` -/

inductive PreviewProtection where
  | team_only
  | pub
deriving Inhabited, DecidableEq, Repr

structure PreviewSpec where
  enabled    : Bool := true
  subdomain? : Option String := some "preview"
  host?      : Option HostPattern := none
  protection : PreviewProtection := .team_only
  ttlSec     : Nat := 7 * 86400
deriving Inhabited, DecidableEq, Repr

/-- Resolves the preview host pattern: explicit `host?` if set, otherwise derived from `prodDomain` + `subdomain?`. -/
def PreviewSpec.resolvedHost? (p : PreviewSpec) (prodDomain? : Option String) : Option HostPattern :=
  match p.host? with
  | some hp => some hp
  | none    =>
      match prodDomain?, p.subdomain? with
      | some prod, some sub => some (derivePreviewHost prod sub)
      | _, _                => none

structure DeploySpec where
  name        : String
  appName     : String
  regions     : List GcpRegion := [.us_central1]
  domain?     : Option String := none
  compute     : ComputeTier := .standard
  timeoutSec? : Option Nat := none
  preview     : PreviewSpec := {}
deriving Inhabited, DecidableEq, Repr

inductive DeploySection where
  | regions | timeout | domain | preview
deriving Inhabited, DecidableEq, Repr

/-- Section-tagged validation so elaborator errors highlight the exact offending clause. -/
def DeploySpec.validateSectioned (d : DeploySpec) : Except (DeploySection × String) Unit := do
  if d.regions.isEmpty then
    .error (.regions, s!"`deploy {d.name}`: `regions` must list at least one GCP region")
  if let some t := d.timeoutSec? then
    if t == 0 || t > 3600 then
      .error (.timeout, s!"`deploy {d.name}`: `timeout` ({t}s) must be between 1s and 3600s")
  if let some dom := d.domain? then
    if !isValidHostname dom then
      .error (.domain, s!"`deploy {d.name}`: invalid RFC 1123 production `domain` `{dom}` (omit scheme/path/trailing dot)")
  if d.preview.enabled then
    if d.preview.ttlSec == 0 then
      .error (.preview, s!"`deploy {d.name}`: preview `ttl` must be positive")
    if let some sub := d.preview.subdomain? then
      if !isValidDnsLabel sub then
        .error (.preview, s!"`deploy {d.name}`: invalid preview `subdomain` label `{sub}`")
    if let some hp := d.preview.resolvedHost? d.domain? then
      if !hp.isValid then
        .error (.preview, s!"`deploy {d.name}`: invalid preview host `{hp.render}`")
      if let some prodDom := d.domain? then
        if hp.matches prodDom then
          .error (.preview, s!"`deploy {d.name}`: preview host `{hp.render}` overlaps production domain `{prodDom}`")

def DeploySpec.validate (d : DeploySpec) : Except String Unit :=
  match d.validateSectioned with
  | .ok ()         => .ok ()
  | .error (_, msg) => .error msg

/-! ### 3. Canonical Proved-Injective GCP Naming (`DeployKey`, `renderSaId`, `renderCloudRunName`) -/

structure TenantId where
  num   : Nat
  valid : num < 1000000
deriving DecidableEq, Repr

instance : Inhabited TenantId := ⟨⟨0, by decide⟩⟩

structure AppId where
  num   : Nat
  valid : num < 100000
deriving DecidableEq, Repr

instance : Inhabited AppId := ⟨⟨0, by decide⟩⟩

structure PrId where
  num   : Nat
  valid : num < 100000
deriving DecidableEq, Repr

instance : Inhabited PrId := ⟨⟨0, by decide⟩⟩

/-- Concrete deployed environment instance (distinguishes distinct bounded PR previews). -/
inductive EnvInstance where
  | prod
  | staging
  | preview (pr : PrId)
deriving Inhabited, DecidableEq, Repr

def EnvInstance.toDeployEnv : EnvInstance → DeployEnv
  | .prod      => .prod
  | .staging   => .staging
  | .preview _ => .preview

def EnvInstance.isProd : EnvInstance → Bool
  | .prod => true
  | _     => false

def EnvInstance.isPreview : EnvInstance → Bool
  | .preview _ => true
  | _          => false

structure ShardProject where
  projectId : String
deriving Inhabited, DecidableEq, Repr

/-- Unique identity of a single deployed `(shard, tenant, app, envInstance)` slice. -/
structure DeployKey where
  shard  : ShardProject
  tenant : TenantId
  app    : AppId
  env    : EnvInstance
deriving Inhabited, DecidableEq, Repr

/-- Encode a natural number into decimal digits (always non-empty, pure digits `'0'..'9'`, no `'-'`). -/
def encNatAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | k + 1, n, acc =>
      let d := Char.ofNat (48 + n % 10)
      if n < 10 then d :: acc
      else encNatAux k (n / 10) (d :: acc)

def encNat (n : Nat) : String :=
  String.ofList (encNatAux 10 n [])

def decDigitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
      if '0' ≤ c && c ≤ '9' then decDigitsAux (acc * 10 + (c.toNat - 48)) cs
      else none

def decNat (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | cs => decDigitsAux 0 cs

private theorem encNatAux_bounds (d k n : Nat) (hn : n < 10 ^ (d + 1)) (hk : d + 1 ≤ k)
    (acc : List Char) :
    acc.length < (encNatAux k n acc).length ∧ (encNatAux k n acc).length ≤ d + 1 + acc.length := by
  induction d generalizing k n acc with
  | zero =>
      cases k with
      | zero => omega
      | succ _ =>
          have h10 : n < 10 := by simpa using hn
          simp [encNatAux, h10]; omega
  | succ d ih =>
      cases k with
      | zero => omega
      | succ k' =>
          simp only [encNatAux]; split
          · simp; omega
          · have h := ih k' (n / 10) (by rw [Nat.pow_succ] at hn; omega) (by omega)
              (Char.ofNat (48 + n % 10) :: acc)
            simp at h; omega

private theorem encNat_len_bounds {d n : Nat} (hn : n < 10 ^ (d + 1)) (hd : d ≤ 9) :
    1 ≤ (encNat n).toList.length ∧ (encNat n).toList.length ≤ d + 1 := by
  have h := encNatAux_bounds d 10 n hn (by omega) []
  simpa [encNat] using h

private theorem char_ofNat_digit (d : Nat) (hd : d < 10) :
    '0' ≤ Char.ofNat (48 + d) ∧ Char.ofNat (48 + d) ≤ '9' ∧ (Char.ofNat (48 + d)).toNat - 48 = d :=
  (by decide : ∀ i : Fin 10, '0' ≤ Char.ofNat (48 + i.val) ∧ Char.ofNat (48 + i.val) ≤ '9' ∧
    (Char.ofNat (48 + i.val)).toNat - 48 = i.val) ⟨d, hd⟩

private theorem encNatAux_all_digits (k n : Nat) (acc : List Char)
    (hacc : ∀ c ∈ acc, '0' ≤ c ∧ c ≤ '9') :
    ∀ c ∈ encNatAux k n acc, '0' ≤ c ∧ c ≤ '9' := by
  induction k generalizing n acc with
  | zero => exact hacc
  | succ k ih =>
      have hd := char_ofNat_digit (n % 10) (Nat.mod_lt _ (by decide))
      have hnext : ∀ c ∈ Char.ofNat (48 + n % 10) :: acc, '0' ≤ c ∧ c ≤ '9' := fun c hc =>
        (List.mem_cons.mp hc).elim (fun h => h ▸ ⟨hd.1, hd.2.1⟩) (hacc c)
      simp only [encNatAux]; split
      · exact hnext
      · exact ih (n / 10) _ hnext

private theorem decDigitsAux_append_digit (acc d : Nat) (hd : d < 10) (cs : List Char) :
    decDigitsAux acc (Char.ofNat (48 + d) :: cs) = decDigitsAux (acc * 10 + d) cs := by
  have h := char_ofNat_digit d hd
  simp [decDigitsAux, h.1, h.2.1, h.2.2]

private theorem decDigitsAux_encNatAux (k n : Nat) (hbound : n < 10 ^ k) (cs : List Char) :
    decDigitsAux 0 (encNatAux k n cs) = decDigitsAux n cs := by
  induction k generalizing n cs with
  | zero => simp at hbound; subst hbound; rfl
  | succ k ih =>
      simp only [encNatAux]; split
      · rename_i hlt
        rw [decDigitsAux_append_digit 0 (n % 10) (Nat.mod_lt _ (by decide))]
        simp [Nat.mod_eq_of_lt hlt]
      · rw [ih (n / 10) (by rw [Nat.pow_succ] at hbound; omega) (Char.ofNat (48 + n % 10) :: cs),
            decDigitsAux_append_digit (n / 10) (n % 10) (Nat.mod_lt _ (by decide)),
            show n / 10 * 10 + n % 10 = n by omega]

theorem decNat_encNat (n : Nat) (hn : n < 10000000000) : decNat (encNat n) = some n := by
  unfold decNat encNat; rw [String.toList_ofList]
  have hpos := (encNatAux_bounds 9 10 n hn (by decide) []).1
  cases h : encNatAux 10 n [] with
  | nil => rw [h] at hpos; simp at hpos
  | cons _ _ => have hdec := decDigitsAux_encNatAux 10 n hn []; rw [h] at hdec; exact hdec

theorem encNat_injective {a b : Nat} (ha : a < 10000000000) (hb : b < 10000000000)
    (heq : encNat a = encNat b) : a = b :=
  Option.some.inj ((decNat_encNat a ha).symm.trans (heq ▸ decNat_encNat b hb))

theorem encNat_no_hyphen (n : Nat) : '-' ∉ (encNat n).toList := fun hmem => by
  rw [encNat, String.toList_ofList] at hmem
  have hle : (48 : Nat) ≤ ('-').toNat := (encNatAux_all_digits 10 n [] (by simp) '-' hmem).1
  revert hle; decide

def renderEnvTag : EnvInstance → String
  | .prod       => "p"
  | .staging    => "s"
  | .preview pr => "r" ++ encNat pr.num

/-- Canonical slug `<tenant>-<app>-<envTag>` shared by SA IDs (`q-<slug>`) and Cloud Run (`cr-<slug>`). -/
def renderKeySlug (k : DeployKey) : String :=
  encNat k.tenant.num ++ "-" ++ encNat k.app.num ++ "-" ++ renderEnvTag k.env

def renderSaId (k : DeployKey) : String :=
  "q-" ++ renderKeySlug k

def renderSaEmail (k : DeployKey) : String :=
  renderSaId k ++ "@" ++ k.shard.projectId ++ ".iam.gserviceaccount.com"

def renderCloudRunName (k : DeployKey) : String :=
  "cr-" ++ renderKeySlug k

private theorem append_hyphen_inj {a₁ b₁ a₂ b₂ : List Char}
    (h1 : '-' ∉ a₁) (h2 : '-' ∉ a₂)
    (heq : a₁ ++ '-' :: b₁ = a₂ ++ '-' :: b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  match a₁, a₂ with
  | [], [] => simp_all
  | [], c :: _ => cases heq; exact absurd List.mem_cons_self h2
  | c :: _, [] => cases heq; exact absurd List.mem_cons_self h1
  | c :: cs, d :: ds =>
      injection heq with hcd htail; subst hcd
      have ⟨hcs, hb⟩ := append_hyphen_inj
        (fun hm => h1 (List.mem_cons_of_mem _ hm)) (fun hm => h2 (List.mem_cons_of_mem _ hm)) htail
      exact ⟨congrArg (c :: ·) hcs, hb⟩

private theorem str_eq_of_toList {s₁ s₂ : String} (h : s₁.toList = s₂.toList) : s₁ = s₂ := by
  rw [← String.ofList_toList (s := s₁), ← String.ofList_toList (s := s₂), h]

private theorem str_append_left_inj {p a b : String} (h : p ++ a = p ++ b) : a = b := by
  have hl := congrArg String.toList h
  simp only [String.toList_append] at hl
  exact str_eq_of_toList (List.append_cancel_left hl)

private theorem renderEnvTag_injective {e₁ e₂ : EnvInstance}
    (heq : renderEnvTag e₁ = renderEnvTag e₂) : e₁ = e₂ := by
  have hlist := congrArg String.toList heq
  cases e₁ <;> cases e₂ <;> simp [renderEnvTag, String.toList_append] at hlist
  · rfl
  · rfl
  case preview.preview pr₁ pr₂ =>
    have hn := encNat_injective (by have := pr₁.valid; omega) (by have := pr₂.valid; omega) (str_eq_of_toList hlist)
    cases pr₁; cases pr₂; simp_all

theorem renderKeySlug_injective {k₁ k₂ : DeployKey}
    (hshard : k₁.shard = k₂.shard) (heq : renderKeySlug k₁ = renderKeySlug k₂) : k₁ = k₂ := by
  rcases k₁ with ⟨sh₁, ⟨t₁, _⟩, ⟨a₁, _⟩, e₁⟩
  rcases k₂ with ⟨sh₂, ⟨t₂, _⟩, ⟨a₂, _⟩, e₂⟩
  simp only at hshard; subst hshard
  have hlist :
      (encNat t₁).toList ++ '-' :: ((encNat a₁).toList ++ '-' :: (renderEnvTag e₁).toList) =
      (encNat t₂).toList ++ '-' :: ((encNat a₂).toList ++ '-' :: (renderEnvTag e₂).toList) := by
    simpa [renderKeySlug, String.toList_append, List.append_assoc] using congrArg String.toList heq
  rcases append_hyphen_inj (encNat_no_hyphen t₁) (encNat_no_hyphen t₂) hlist with ⟨htL, hrest⟩
  rcases append_hyphen_inj (encNat_no_hyphen a₁) (encNat_no_hyphen a₂) hrest with ⟨haL, heL⟩
  have htEq := encNat_injective (by omega) (by omega) (str_eq_of_toList htL)
  have haEq := encNat_injective (by omega) (by omega) (str_eq_of_toList haL)
  have heEq := renderEnvTag_injective (str_eq_of_toList heL)
  subst htEq; subst haEq; subst heEq; rfl

/-- **SA Injectivity Theorem:** Distinct `(tenant, app, env)` deployments in a shard ALWAYS map
    to distinct GCP Service Account IDs (zero collision/truncation risk). -/
theorem renderSaId_injective {k₁ k₂ : DeployKey}
    (hshard : k₁.shard = k₂.shard) (heq : renderSaId k₁ = renderSaId k₂) : k₁ = k₂ :=
  renderKeySlug_injective hshard (str_append_left_inj heq)

/-- **Cloud Run Service Injectivity Theorem:** Distinct `(tenant, app, env)` deployments in a shard
    ALWAYS map to distinct Cloud Run service names. -/
theorem renderCloudRunName_injective {k₁ k₂ : DeployKey}
    (hshard : k₁.shard = k₂.shard) (heq : renderCloudRunName k₁ = renderCloudRunName k₂) : k₁ = k₂ :=
  renderKeySlug_injective hshard (str_append_left_inj heq)

private theorem renderKeySlug_length_bounds (k : DeployKey) :
    5 ≤ (renderKeySlug k).toList.length ∧ (renderKeySlug k).toList.length ≤ 19 := by
  have ht := encNat_len_bounds (d := 5) k.tenant.valid (by decide)
  have ha := encNat_len_bounds (d := 4) k.app.valid (by decide)
  have he : 1 ≤ (renderEnvTag k.env).toList.length ∧ (renderEnvTag k.env).toList.length ≤ 6 := by
    cases h : k.env with
    | prod | staging => decide
    | preview pr =>
        have hpr := encNat_len_bounds (d := 4) pr.valid (by decide)
        simp only [renderEnvTag, String.toList_append, List.length_append]
        have hr : "r".toList.length = 1 := rfl
        omega
  simp only [renderKeySlug, String.toList_append, List.length_append]
  have hd : "-".toList.length = 1 := rfl
  omega

/-- **GCP SA Length-Bound Theorem:** Every SA ID length is in `[7, 21]` (strictly inside `[6, 30]`). -/
theorem renderSaId_gcp_length_valid (k : DeployKey) :
    6 ≤ (renderSaId k).toList.length ∧ (renderSaId k).toList.length ≤ 30 := by
  have hb := renderKeySlug_length_bounds k
  simp only [renderSaId, String.toList_append, List.length_append]
  have hq : "q-".toList.length = 2 := rfl; omega

/-- **Cloud Run Name Length-Bound Theorem:** Every Cloud Run service name length is in `[8, 22]` (≤ 63). -/
theorem renderCloudRunName_gcp_length_valid (k : DeployKey) :
    6 ≤ (renderCloudRunName k).toList.length ∧ (renderCloudRunName k).toList.length ≤ 63 := by
  have hb := renderKeySlug_length_bounds k
  simp only [renderCloudRunName, String.toList_append, List.length_append]
  have hcr : "cr-".toList.length = 3 := rfl; omega

/-! ### 4. Open Principal Universe, Typed Roles (No `owner`/`editor`), & IAM Semantics -/

/-- Open principal universe: includes unauthenticated internet callers (`allUsers`),
    any Google account (`allAuthenticatedUsers`), external accounts, control-plane SAs,
    and per-deployment runtime SAs. -/
inductive GcpPrincipal where
  | allUsers
  | allAuthenticatedUsers
  | builder
  | edgeRouter
  | runtimeSa (key : DeployKey)
  | external  (email : String)
deriving Inhabited, DecidableEq, Repr

inductive GcpPermission where
  | secretAccessor
  | runInvoke
  | cloudSqlClient
  | storageObjectViewer
  | storageObjectAdmin
  | iamSetPolicy
  | iamActAs
  | iamGetAccessToken
  | iamSignJwt
deriving Inhabited, DecidableEq, Repr

/-- Permissions that allow modifying IAM or impersonating another principal in GCP. -/
def GcpPermission.isEscalation : GcpPermission → Bool
  | .iamSetPolicy | .iamActAs | .iamGetAccessToken | .iamSignJwt => true
  | _ => false

/-- Typed least-privilege GCP predefined roles.
    Basic roles (`roles/owner`, `roles/editor`) are structurally unrepresentable. -/
inductive GcpRole where
  | secretManagerAccessor
  | runInvoker
  | cloudSqlClient
  | storageObjectViewer
  | storageObjectAdmin
deriving Inhabited, DecidableEq, Repr

def GcpRole.gcpName : GcpRole → String
  | .secretManagerAccessor => "roles/secretmanager.secretAccessor"
  | .runInvoker            => "roles/run.invoker"
  | .cloudSqlClient        => "roles/cloudsql.client"
  | .storageObjectViewer   => "roles/storage.objectViewer"
  | .storageObjectAdmin    => "roles/storage.objectAdmin"

def GcpRole.permissions : GcpRole → List GcpPermission
  | .secretManagerAccessor => [.secretAccessor]
  | .runInvoker            => [.runInvoke]
  | .cloudSqlClient        => [.cloudSqlClient]
  | .storageObjectViewer   => [.storageObjectViewer]
  | .storageObjectAdmin    => [.storageObjectAdmin, .storageObjectViewer]

/-- No predefined role emitted by Qed Cloud contains an IAM escalation permission. -/
theorem GcpRole.no_escalation (role : GcpRole) (perm : GcpPermission)
    (h : perm ∈ role.permissions) : perm.isEscalation = false := by
  cases role <;> simp [GcpRole.permissions] at h <;> rcases h with rfl | rfl <;> rfl

inductive GcpResource where
  | secret      (key : DeployKey) (secretName : String)
  | cloudRun    (key : DeployKey)
  | cloudSqlDb  (cluster : DbCluster) (key : DeployKey) (dbName : String)
  | assetPrefix (key : DeployKey) (buildHash : String)
deriving Inhabited, DecidableEq, Repr

def GcpResource.ownerKey : GcpResource → DeployKey
  | .secret k _        => k
  | .cloudRun k        => k
  | .cloudSqlDb _ k _  => k
  | .assetPrefix k _   => k

def GcpResource.isProdResource : GcpResource → Bool
  | .cloudSqlDb .prodCluster _ _ => true
  | r                            => r.ownerKey.env.isProd

def GcpResource.isPublicAsset : GcpResource → Bool
  | .assetPrefix _ _ => true
  | _                => false

structure GcpIamBinding where
  principal : GcpPrincipal
  role      : GcpRole
  resource  : GcpResource
deriving Inhabited, DecidableEq, Repr

structure GcpDenyRule where
  principals  : List GcpPrincipal
  permissions : List GcpPermission
  resource    : GcpResource
deriving Inhabited, DecidableEq, Repr

/-- Combined multi-tenant GCP policy & egress state across all deployments. -/
structure GcpPolicyState where
  bindings    : List GcpIamBinding := []
  denies      : List GcpDenyRule := []
  egressAllow : List (DeployKey × String) := []
deriving Inhabited, DecidableEq, Repr

/-- Direct GCP IAM evaluation: `p` is allowed `perm` on `r` iff some binding grants `perm`
    to `p` on `r` AND no deny rule blocks `(p, perm, r)`. -/
def GcpPolicyState.allows (st : GcpPolicyState) (p : GcpPrincipal)
    (perm : GcpPermission) (r : GcpResource) : Prop :=
  (∃ b ∈ st.bindings, b.principal = p ∧ b.resource = r ∧ perm ∈ b.role.permissions) ∧
  ¬ (∃ d ∈ st.denies, p ∈ d.principals ∧ perm ∈ d.permissions ∧ d.resource = r)

/-- Conservative privilege-escalation step relation:
    if `p₁` holds ANY escalation permission on ANY resource, we conservatively allow `p₁` to step to any `p₂`. -/
def GcpPolicyState.canStep (st : GcpPolicyState) (p₁ _p₂ : GcpPrincipal) : Prop :=
  ∃ perm r, perm.isEscalation = true ∧ st.allows p₁ perm r

inductive GcpPolicyState.canReachPrincipal (st : GcpPolicyState) : GcpPrincipal → GcpPrincipal → Prop where
  | refl (p : GcpPrincipal) : st.canReachPrincipal p p
  | step {p₁ p₂ p₃ : GcpPrincipal} :
      st.canStep p₁ p₂ → st.canReachPrincipal p₂ p₃ → st.canReachPrincipal p₁ p₃

/-- Transitive IAM reachability across any sequence of `canStep` hops. -/
def GcpPolicyState.canReach (st : GcpPolicyState) (p : GcpPrincipal)
    (perm : GcpPermission) (r : GcpResource) : Prop :=
  ∃ p', st.canReachPrincipal p p' ∧ st.allows p' perm r

def GcpPolicyState.egressAllowed (st : GcpPolicyState) (k : DeployKey) (origin : String) : Prop :=
  (k, origin) ∈ st.egressAllow

/-! ### 5. Four-Phase Zero-Downtime Cloud Run Rollout Model -/

inductive RolloutPhase where
  | phase1_provision     -- upload immutable assets, create secrets/DBs, grant new IAM, widen egress union
  | phase2_deployZero    -- deploy Cloud Run revision at 0% traffic & health check
  | phase3_shiftTraffic  -- atomically shift traffic 0% -> 100%
  | phase4_cleanup       -- revoke stale bindings/secrets & narrow removed egress AFTER traffic flip
deriving Inhabited, DecidableEq, Repr

def RolloutPhase.rank : RolloutPhase → Nat
  | .phase1_provision    => 1
  | .phase2_deployZero   => 2
  | .phase3_shiftTraffic => 3
  | .phase4_cleanup      => 4

inductive GcpAction where
  | uploadAssets       (key : DeployKey) (buildHash : String) (paths : List String)
  | ensureSecret       (key : DeployKey) (secretName : String)
  | ensureDb           (cluster : DbCluster) (key : DeployKey) (dbName : String)
  | grantBinding       (binding : GcpIamBinding)
  | putDenyRule        (rule : GcpDenyRule)
  | setEgressRules     (key : DeployKey) (origins : List String)
  | deployRevisionZero (key : DeployKey) (buildHash : String) (scale : ScaleSpec)
  | healthCheck        (key : DeployKey) (buildHash : String)
  | shiftTraffic100    (key : DeployKey) (buildHash : String)
  | revokeBinding      (binding : GcpIamBinding)
  | deleteSecret       (key : DeployKey) (secretName : String)
  | narrowEgressRules  (key : DeployKey) (origins : List String)
  | deleteService      (key : DeployKey)
  | dropPreviewDb      (key : DeployKey) (dbName : String)
deriving Inhabited, DecidableEq, Repr

def GcpAction.phase : GcpAction → RolloutPhase
  | .uploadAssets _ _ _ | .ensureSecret _ _ | .ensureDb _ _ _
  | .grantBinding _ | .putDenyRule _ | .setEgressRules _ _        => .phase1_provision
  | .deployRevisionZero _ _ _ | .healthCheck _ _                  => .phase2_deployZero
  | .shiftTraffic100 _ _                                          => .phase3_shiftTraffic
  | .revokeBinding _ | .deleteSecret _ _ | .narrowEgressRules _ _
  | .deleteService _ | .dropPreviewDb _ _                         => .phase4_cleanup

def GcpAction.isDestructive : GcpAction → Bool
  | .revokeBinding _ | .deleteSecret _ _ | .narrowEgressRules _ _
  | .deleteService _ | .dropPreviewDb _ _ => true
  | _ => false

def GcpAction.targetKey : GcpAction → DeployKey
  | .grantBinding b | .revokeBinding b => b.resource.ownerKey
  | .putDenyRule d                     => d.resource.ownerKey
  | .uploadAssets k _ _ | .ensureSecret k _ | .ensureDb _ k _
  | .setEgressRules k _ | .deployRevisionZero k _ _ | .healthCheck k _
  | .shiftTraffic100 k _ | .deleteSecret k _ | .narrowEgressRules k _
  | .deleteService k | .dropPreviewDb k _ => k

/-- Monotonicity predicate: every action list is non-decreasing in `RolloutPhase.rank`. -/
def actionsPhaseOrdered : List GcpAction → Prop
  | []           => True
  | [_]          => True
  | a :: b :: xs => a.phase.rank ≤ b.phase.rank ∧ actionsPhaseOrdered (b :: xs)

end Qed.Cloud
