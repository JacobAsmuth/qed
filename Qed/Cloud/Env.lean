/-! ## Qed Cloud Environment & Target Primitives (`Qed.Cloud.Env`)
    Pure, zero-dependency foundational types shared across `database`, `auth`, `Deploy`,
    and `Qed.Cloud`:
    - Closed 4-environment universe `DeployEnv` (`dev | preview | staging | prod`)
    - Serializable, decidable 4-field `EnvMap α` (reduces `∀ e : DeployEnv, ...` automatically)
    - Scoped secret references (`envScoped` vs `pinned env`)
    - Typed database targets (`DbEnvSpec`) with static durability & isolation proofs
    - Typed auth targets (`AuthEnvTarget`) ensuring `previewIdp` never ships to `prod`
    - Kernel-reducible RFC 1123 hostname & wildcard validation with disjointness proofs -/

namespace Qed.Cloud

/-! ### 1. Deployment Environments & `EnvMap` -/

inductive DeployEnv where
  | dev
  | preview
  | staging
  | prod
deriving Inhabited, DecidableEq, Repr

def DeployEnv.all : List DeployEnv := [.dev, .preview, .staging, .prod]

theorem DeployEnv.mem_all (e : DeployEnv) : e ∈ DeployEnv.all := by
  cases e <;> simp [DeployEnv.all]

def DeployEnv.toString : DeployEnv → String
  | .dev     => "dev"
  | .preview => "preview"
  | .staging => "staging"
  | .prod    => "prod"

instance : ToString DeployEnv := ⟨DeployEnv.toString⟩

/-- Strict, fail-closed environment parser. Never defaults unknown strings to `dev`. -/
def DeployEnv.parse? : String → Option DeployEnv
  | "dev"     => some .dev
  | "preview" => some .preview
  | "staging" => some .staging
  | "prod"    => some .prod
  | _         => none

theorem DeployEnv.parse_toString (e : DeployEnv) : DeployEnv.parse? e.toString = some e := by
  cases e <;> rfl

theorem DeployEnv.parse_rejects_unknown (s : String)
    (h1 : s ≠ "dev") (h2 : s ≠ "preview") (h3 : s ≠ "staging") (h4 : s ≠ "prod") :
    DeployEnv.parse? s = none := by
  unfold DeployEnv.parse?
  split <;> simp_all

/-- Total 4-slot per-environment map. Concrete record so `DecidableEq`, `Repr`,
    registry persistence, and `cases e` proofs work with zero `funext` friction. -/
structure EnvMap (α : Type) where
  dev     : α
  preview : α
  staging : α
  prod    : α
deriving Inhabited, DecidableEq, Repr

def EnvMap.get {α : Type} (m : EnvMap α) : DeployEnv → α
  | .dev     => m.dev
  | .preview => m.preview
  | .staging => m.staging
  | .prod    => m.prod

def EnvMap.ofDefault {α : Type} (x : α) : EnvMap α :=
  { dev := x, preview := x, staging := x, prod := x }

def EnvMap.set {α : Type} (m : EnvMap α) (e : DeployEnv) (v : α) : EnvMap α :=
  match e with
  | .dev     => { m with dev     := v }
  | .preview => { m with preview := v }
  | .staging => { m with staging := v }
  | .prod    => { m with prod    := v }

theorem EnvMap.get_set_eq {α : Type} (m : EnvMap α) (e : DeployEnv) (v : α) :
    (m.set e v).get e = v := by
  cases e <;> rfl

theorem EnvMap.get_set_ne {α : Type} (m : EnvMap α) {e₁ e₂ : DeployEnv} (v : α) (hne : e₁ ≠ e₂) :
    (m.set e₁ v).get e₂ = m.get e₂ := by
  cases e₁ <;> cases e₂ <;> simp_all [EnvMap.set, EnvMap.get]

/-! ### 2. Scoped Secrets -/

/-- Distinguishes per-environment Secret Manager vaults (e.g. `DATABASE_URL` bound to distinct
    secrets in `preview` vs `prod`) from explicitly environment-pinned secret names. -/
inductive SecretScope where
  | envScoped
  | pinned (env : DeployEnv)
deriving Inhabited, DecidableEq, Repr

structure SecretRef where
  envVar : String
  scope  : SecretScope := .envScoped
deriving Inhabited, DecidableEq, Repr

def SecretRef.allowedIn (s : SecretRef) (e : DeployEnv) : Bool :=
  match s.scope with
  | .envScoped => true
  | .pinned pe => pe == e

theorem SecretRef.pinned_rejects_other (k : String) {e₁ e₂ : DeployEnv} (hne : e₁ ≠ e₂) :
    ({ envVar := k, scope := .pinned e₁ } : SecretRef).allowedIn e₂ = false := by
  simp [SecretRef.allowedIn, hne]

/-! ### 3. Typed Database Targets (`DbEnvSpec`) & `managed postgres` Expansion -/

inductive DbCluster where
  | prodCluster
  | nonProdCluster
deriving Inhabited, DecidableEq, Repr

/-- Canonical sanitized env-var name for a `managed postgres` database secret
    (single source of truth shared across `Env.lean`, `Deploy.lean`, and `Native.lean`). -/
def managedPostgresSecretVar (dbName : String) : String :=
  let sanitized := String.ofList <| dbName.toUpper.toList.map fun c =>
    if ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_' then c else '_'
  "QED_MANAGED_DB_" ++ sanitized

inductive DbEnvSpec where
  | managedPostgres (dbName : String) (env : DeployEnv)
  | ephemeralSqlite (path : String)
  | byoPostgres     (secret : SecretRef)
  | byoUrl          (secret : SecretRef)
  | byoSqlite       (path : String)
  | byoSqliteEnv    (envVar : String) (defaultPath? : Option String := none)
  | byoD1           (accountEnv : String) (dbEnv : String) (token : SecretRef)
  | byoTurso        (urlEnv : String) (token : SecretRef)
  | byoHttpSql      (urlEnv : String) (token? : Option SecretRef := none)
deriving Inhabited, DecidableEq, Repr

def DbEnvSpec.isEphemeral : DbEnvSpec → Bool
  | .ephemeralSqlite _ => true
  | .byoSqlite _       => true
  | .byoSqliteEnv _ _  => true
  | _                  => false

def DbEnvSpec.cluster? : DbEnvSpec → Option DbCluster
  | .managedPostgres _ .prod => some .prodCluster
  | .managedPostgres _ _     => some .nonProdCluster
  | _                        => none

def DbEnvSpec.secrets : DbEnvSpec → List SecretRef
  | .managedPostgres dbName env => [{ envVar := managedPostgresSecretVar dbName, scope := .pinned env }]
  | .byoPostgres s              => [s]
  | .byoUrl s                   => [s]
  | .byoD1 _ _ tok              => [tok]
  | .byoTurso _ tok             => [tok]
  | .byoHttpSql _ (some tok)    => [tok]
  | _                           => []

/-- Known static HTTPS egress origins implied by a database transport (for default-deny firewalls). -/
def DbEnvSpec.egressOrigins : DbEnvSpec → List String
  | .byoD1 _ _ _ => ["https://api.cloudflare.com"]
  | _            => []

/-- Canonical expansion of `managed postgres` inside `database <dbName>:`. -/
def managedPostgresTargets (dbName : String) (previewEphemeral : Bool := false)
    (devOverride? : Option DbEnvSpec := none) : EnvMap DbEnvSpec :=
  { dev     := devOverride?.getD (.byoSqlite s!".qed/dev/{dbName}.db")
    preview := if previewEphemeral then .ephemeralSqlite s!"/tmp/qed-preview-{dbName}.db"
               else .managedPostgres dbName .preview
    staging := .managedPostgres dbName .staging
    prod    := .managedPostgres dbName .prod }

theorem managedPostgresTargets_prod_durable (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).prod.isEphemeral = false := rfl

theorem managedPostgresTargets_staging_durable (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).staging.isEphemeral = false := rfl

theorem managedPostgresTargets_prod_cluster (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).prod.cluster? = some .prodCluster := rfl

theorem managedPostgresTargets_nonprod_never_prod_cluster (dbName : String) (ephem : Bool)
    (e : DeployEnv) (hne : e ≠ .prod) :
    ((managedPostgresTargets dbName ephem none).get e).cluster? ≠ some .prodCluster := by
  cases e <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get, DbEnvSpec.cluster?]

theorem managedPostgresTargets_env_disjoint (dbName : String) (ephem : Bool)
    {e₁ e₂ : DeployEnv} (hne : e₁ ≠ e₂) :
    (managedPostgresTargets dbName ephem none).get e₁ ≠
    (managedPostgresTargets dbName ephem none).get e₂ := by
  cases e₁ <;> cases e₂ <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get]

theorem managedPostgresTargets_secrets_scoped (dbName : String) (ephem : Bool)
    (e : DeployEnv) (s : SecretRef)
    (hs : s ∈ ((managedPostgresTargets dbName ephem none).get e).secrets) :
    s.allowedIn e = true := by
  cases e <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get, DbEnvSpec.secrets, SecretRef.allowedIn]

/-! ### 4. Managed Auth Targets -/

inductive AuthEnvTarget where
  | localDev
  | previewIdp
  | managedOidc (providers : List String)
  | customOidc
deriving Inhabited, DecidableEq, Repr

def managedAuthTargets (providers : List String) : EnvMap AuthEnvTarget :=
  { dev     := .localDev
    preview := .previewIdp
    staging := .managedOidc providers
    prod    := .managedOidc providers }

theorem managedAuthTargets_prod_never_previewIdp (providers : List String) :
    (managedAuthTargets providers).prod ≠ .previewIdp := by
  simp [managedAuthTargets]

theorem managedAuthTargets_prod_never_localDev (providers : List String) :
    (managedAuthTargets providers).prod ≠ .localDev := by
  simp [managedAuthTargets]

/-! ### 5. RFC 1123 Hostname & Wildcard Validation + Disjointness Proofs -/

def isDnsAlnum (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

def isDnsLabelChar (c : Char) : Bool :=
  isDnsAlnum c || c == '-'

/-- Pure, kernel-reducible dot splitter on `List Char`. -/
private def splitDotsAux : List Char → List Char → List (List Char)
  | [],        cur => [cur.reverse]
  | '.' :: cs, cur => cur.reverse :: splitDotsAux cs []
  | c :: cs,   cur => splitDotsAux cs (c :: cur)

def isValidDnsLabelChars (cs : List Char) : Bool :=
  1 ≤ cs.length && cs.length ≤ 63 &&
  cs.all isDnsLabelChar &&
  match cs.head?, cs.getLast? with
  | some h, some t => isDnsAlnum h && isDnsAlnum t
  | _, _           => false

/-- Valid lowercase RFC 1123 DNS label: 1..63 chars, `[a-z0-9-]`, starts & ends alphanumeric. -/
def isValidDnsLabel (s : String) : Bool :=
  isValidDnsLabelChars s.toList

/-- Valid RFC 1123 FQDN hostname (at least 2 dot-separated labels, ≤ 253 chars, no scheme/port/path). -/
def isValidHostname (s : String) : Bool :=
  let cs := s.toList
  let labels := splitDotsAux cs []
  cs.length ≤ 253 && labels.length ≥ 2 && labels.all isValidDnsLabelChars

inductive HostPattern where
  | exact    (host : String)
  | wildcard (suffix : String) -- represents `*.<suffix>`
deriving Inhabited, DecidableEq, Repr

def HostPattern.render : HostPattern → String
  | .exact h    => h
  | .wildcard s => "*." ++ s

def HostPattern.isValid : HostPattern → Bool
  | .exact h    => isValidHostname h
  | .wildcard s => isValidHostname s

/-- Parses an exact RFC 1123 hostname or `*.<hostname>` wildcard pattern. -/
def HostPattern.parse? (raw : String) : Option HostPattern :=
  match raw.toList with
  | '*' :: '.' :: rest =>
      let suf := String.ofList rest
      if isValidHostname suf then some (.wildcard suf) else none
  | _ =>
      if isValidHostname raw then some (.exact raw) else none

/-- True iff concrete hostname `h` matches `pat`.
    `wildcard suf` matches `<label>.<suf>` for any single valid DNS label `<label>`. -/
def HostPattern.matches (pat : HostPattern) (h : String) : Bool :=
  match pat with
  | .exact target => h == target
  | .wildcard suf =>
      let hcs := h.toList
      let scs := '.' :: suf.toList
      if hcs.length ≤ scs.length then false
      else
        let prefixLen := hcs.length - scs.length
        isValidDnsLabelChars (hcs.take prefixLen) && (hcs.drop prefixLen == scs)

/-- Derives `*.<subdomain>.<prodHost>` from a declared `prodHost` and `subdomain` label. -/
def derivePreviewHost (prodHost : String) (subdomain : String) : HostPattern :=
  .wildcard (subdomain ++ "." ++ prodHost)

/-- Any derived preview wildcard `*.<subLabel>.<prodHost>` is strictly longer than `prodHost`,
    so it can NEVER shadow or match `prodHost`. -/
theorem derivePreviewHost_disjoint (prodHost subLabel : String) :
    (derivePreviewHost prodHost subLabel).matches prodHost = false := by
  unfold derivePreviewHost HostPattern.matches
  have hlen : prodHost.toList.length ≤ ('.' :: (subLabel ++ "." ++ prodHost).toList).length := by
    simp [String.toList_append]
    omega
  exact if_pos hlen

/-- Extracts the lowercase host from a URL (or bare authority), handling IPv6 `[...]` and `:port`. -/
private def extractUrlHost (raw : String) : String :=
  let low := raw.toLower
  let afterScheme :=
    match low.splitOn "://" with
    | _ :: rest :: _ => rest
    | _              => low
  let authority := String.ofList (afterScheme.toList.takeWhile fun c => c != '/' && c != '?' && c != '#')
  let hostPort :=
    match authority.splitOn "@" with
    | [hp]     => hp
    | _ :: rhs => String.intercalate "@" rhs
    | []       => ""
  match hostPort.toList with
  | '[' :: rest => String.ofList (rest.takeWhile (· != ']'))
  | cs          => String.ofList (cs.takeWhile (· != ':'))

/-- Detects loopback / local-only hosts (authority-aware, avoiding false positives on
    domains like `notlocalhost.example.com` while catching `127.0.0.0/8`, `::1`, `0.0.0.0`, `*.localhost`). -/
def isLocalhostUrl (s : String) : Bool :=
  let host := extractUrlHost s
  host == "localhost" || host.endsWith ".localhost" || host.endsWith ".local" ||
  host.startsWith "127." || host == "0.0.0.0" ||
  host == "::1" || host == "::" || host == "0:0:0:0:0:0:0:1" ||
  host.startsWith "::ffff:127."

end Qed.Cloud
