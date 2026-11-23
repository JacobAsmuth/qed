/-! ## Qed Cloud Environment & Target Primitives (`Qed.Cloud.Env`) -/

namespace Qed.Cloud

/-! ### 1. Deployment Environments & `EnvMap` -/

inductive DeployEnv where | dev | preview | staging | prod
deriving Inhabited, DecidableEq, Repr

def DeployEnv.all : List DeployEnv := [.dev, .preview, .staging, .prod]
theorem DeployEnv.mem_all (e : DeployEnv) : e ∈ DeployEnv.all := by cases e <;> simp [DeployEnv.all]
def DeployEnv.toString : DeployEnv → String | .dev => "dev" | .preview => "preview" | .staging => "staging" | .prod => "prod"
instance : ToString DeployEnv := ⟨DeployEnv.toString⟩
def DeployEnv.parse? : String → Option DeployEnv | "dev" => some .dev | "preview" => some .preview | "staging" => some .staging | "prod" => some .prod | _ => none
theorem DeployEnv.parse_toString (e : DeployEnv) : DeployEnv.parse? e.toString = some e := by cases e <;> rfl
theorem DeployEnv.parse_rejects_unknown (s : String) (h1 : s ≠ "dev") (h2 : s ≠ "preview") (h3 : s ≠ "staging") (h4 : s ≠ "prod") :
    DeployEnv.parse? s = none := by unfold DeployEnv.parse?; split <;> simp_all

structure EnvMap (α : Type) where
  dev : α
  preview : α
  staging : α
  prod : α
deriving Inhabited, DecidableEq, Repr

def EnvMap.get {α : Type} (m : EnvMap α) : DeployEnv → α | .dev => m.dev | .preview => m.preview | .staging => m.staging | .prod => m.prod
def EnvMap.ofDefault {α : Type} (x : α) : EnvMap α := { dev := x, preview := x, staging := x, prod := x }
def EnvMap.set {α : Type} (m : EnvMap α) (e : DeployEnv) (v : α) : EnvMap α :=
  match e with | .dev => { m with dev := v } | .preview => { m with preview := v } | .staging => { m with staging := v } | .prod => { m with prod := v }
def EnvMap.mapM {m : Type → Type} [Monad m] {α β : Type} (f : DeployEnv → α → m β) (mp : EnvMap α) : m (EnvMap β) := do
  return { dev := ← f .dev mp.dev, preview := ← f .preview mp.preview, staging := ← f .staging mp.staging, prod := ← f .prod mp.prod }

theorem EnvMap.get_set_eq {α : Type} (m : EnvMap α) (e : DeployEnv) (v : α) : (m.set e v).get e = v := by cases e <;> rfl
theorem EnvMap.get_set_ne {α : Type} (m : EnvMap α) {e₁ e₂ : DeployEnv} (v : α) (hne : e₁ ≠ e₂) :
    (m.set e₁ v).get e₂ = m.get e₂ := by cases e₁ <;> cases e₂ <;> simp_all [EnvMap.set, EnvMap.get]

/-! ### 2. Scoped Secrets -/

inductive SecretScope where | envScoped | pinned (env : DeployEnv)
deriving Inhabited, DecidableEq, Repr

structure SecretRef where
  envVar : String
  scope  : SecretScope := .envScoped
deriving Inhabited, DecidableEq, Repr

def SecretRef.allowedIn (s : SecretRef) (e : DeployEnv) : Bool := match s.scope with | .envScoped => true | .pinned pe => pe == e
theorem SecretRef.pinned_rejects_other (k : String) {e₁ e₂ : DeployEnv} (hne : e₁ ≠ e₂) :
    ({ envVar := k, scope := .pinned e₁ } : SecretRef).allowedIn e₂ = false := by simp [SecretRef.allowedIn, hne]

/-! ### 3. Typed Database Targets (`DbEnvSpec`) & `managed postgres` Expansion -/

inductive DbCluster where | prodCluster | nonProdCluster
deriving Inhabited, DecidableEq, Repr

def managedPostgresSecretVar (dbName : String) : String :=
  "QED_MANAGED_DB_" ++ String.ofList (dbName.toUpper.toList.map fun c => if ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_' then c else '_')

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

def DbEnvSpec.isEphemeral : DbEnvSpec → Bool | .ephemeralSqlite _ | .byoSqlite _ | .byoSqliteEnv _ _ => true | _ => false
def DbEnvSpec.cluster? : DbEnvSpec → Option DbCluster | .managedPostgres _ .prod => some .prodCluster | .managedPostgres _ _ => some .nonProdCluster | _ => none
def DbEnvSpec.secrets : DbEnvSpec → List SecretRef
  | .managedPostgres dbName env => [{ envVar := managedPostgresSecretVar dbName, scope := .pinned env }]
  | .byoPostgres s | .byoUrl s | .byoD1 _ _ s | .byoTurso _ s | .byoHttpSql _ (some s) => [s] | _ => []
def DbEnvSpec.egressOrigins : DbEnvSpec → List String | .byoD1 _ _ _ => ["https://api.cloudflare.com"] | _ => []

def managedPostgresTargets (dbName : String) (previewEphemeral : Bool := false) (devOverride? : Option DbEnvSpec := none) : EnvMap DbEnvSpec :=
  { dev     := devOverride?.getD (.byoSqlite s!".qed/dev/{dbName}.db")
    preview := if previewEphemeral then .ephemeralSqlite s!"/tmp/qed-preview-{dbName}.db" else .managedPostgres dbName .preview
    staging := .managedPostgres dbName .staging, prod := .managedPostgres dbName .prod }

theorem managedPostgresTargets_prod_durable (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).prod.isEphemeral = false := rfl
theorem managedPostgresTargets_staging_durable (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).staging.isEphemeral = false := rfl
theorem managedPostgresTargets_prod_cluster (dbName : String) (ephem : Bool) (devOv? : Option DbEnvSpec) :
    (managedPostgresTargets dbName ephem devOv?).prod.cluster? = some .prodCluster := rfl
theorem managedPostgresTargets_nonprod_never_prod_cluster (dbName : String) (ephem : Bool) (e : DeployEnv) (hne : e ≠ .prod) :
    ((managedPostgresTargets dbName ephem none).get e).cluster? ≠ some .prodCluster := by
  cases e <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get, DbEnvSpec.cluster?]
theorem managedPostgresTargets_env_disjoint (dbName : String) (ephem : Bool) {e₁ e₂ : DeployEnv} (hne : e₁ ≠ e₂) :
    (managedPostgresTargets dbName ephem none).get e₁ ≠ (managedPostgresTargets dbName ephem none).get e₂ := by
  cases e₁ <;> cases e₂ <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get]
theorem managedPostgresTargets_secrets_scoped (dbName : String) (ephem : Bool) (e : DeployEnv) (s : SecretRef)
    (hs : s ∈ ((managedPostgresTargets dbName ephem none).get e).secrets) : s.allowedIn e = true := by
  cases e <;> cases ephem <;> simp_all [managedPostgresTargets, EnvMap.get, DbEnvSpec.secrets, SecretRef.allowedIn]

/-! ### 4. Managed Auth Targets -/

inductive AuthEnvTarget where | localDev | previewIdp | managedOidc (providers : List String) | customOidc
deriving Inhabited, DecidableEq, Repr

def managedAuthTargets (providers : List String) : EnvMap AuthEnvTarget :=
  { dev := .localDev, preview := .previewIdp, staging := .managedOidc providers, prod := .managedOidc providers }
theorem managedAuthTargets_prod_never_previewIdp (providers : List String) : (managedAuthTargets providers).prod ≠ .previewIdp := by simp [managedAuthTargets]
theorem managedAuthTargets_prod_never_localDev (providers : List String) : (managedAuthTargets providers).prod ≠ .localDev := by simp [managedAuthTargets]

/-! ### 5. RFC 1123 Hostname, Wildcard, IPv4/IPv6 & Loopback Validation -/

def isDnsAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isDnsAlnum (c : Char) : Bool := isDnsAlpha c || ('0' ≤ c && c ≤ '9')
def isDnsLabelChar (c : Char) : Bool := isDnsAlnum c || c == '-'
def asciiToLower (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
private def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Pure, kernel-reducible character splitter on `List Char`. -/
def splitCharAux (sep : Char) : List Char → List Char → List (List Char)
  | [],      cur => [cur.reverse]
  | c :: cs, cur => if c == sep then cur.reverse :: splitCharAux sep cs [] else splitCharAux sep cs (c :: cur)

private def parseBaseAux (base maxVal acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
      let ok := if base == 8 then '0' ≤ c && c ≤ '7' else if base == 10 then isAsciiDigit c else isAsciiDigit c || ('a' ≤ c && c ≤ 'f')
      if !ok then none else
        let next := acc * base + (if isAsciiDigit c then c.toNat - 48 else c.toNat - 87)
        if next > maxVal then none else parseBaseAux base maxVal next cs

def parsePort? (cs : List Char) : Option Nat :=
  if cs.isEmpty || cs.length > 5 then none else (parseBaseAux 10 65535 0 cs).bind fun p => if p ≥ 1 then some p else none

private def parseIpv4Strict4 (cs : List Char) : Option Nat :=
  let oct (x : List Char) := if x.isEmpty || x.length > 3 then none else parseBaseAux 10 255 0 x
  match splitCharAux '.' cs [] with
  | [a, b, c, d] => do return ((← oct a) <<< 24) ||| ((← oct b) <<< 16) ||| ((← oct c) <<< 8) ||| (← oct d)
  | _ => none

private def parseIpv4Part (maxVal : Nat) : List Char → Option Nat
  | [] => none
  | '0' :: 'x' :: rest => if rest.isEmpty then none else parseBaseAux 16 maxVal 0 rest
  | '0' :: rest        => if rest.isEmpty then some 0 else parseBaseAux 8 maxVal 0 rest
  | cs                 => parseBaseAux 10 maxVal 0 cs

/-- Parses IPv4 in standard 4-octet or shorthand 1/2/3-part decimal/hex/octal notation into a 32-bit `Nat`. -/
def parseIpv4UInt32 (host : String) : Option Nat :=
  let p := parseIpv4Part
  match splitCharAux '.' (host.toList.map asciiToLower) [] with
  | [a]          => p 0xFFFFFFFF a
  | [a, b]       => do return ((← p 0xFF a) <<< 24) ||| (← p 0xFFFFFF b)
  | [a, b, c]    => do return ((← p 0xFF a) <<< 24) ||| ((← p 0xFF b) <<< 16) ||| (← p 0xFFFF c)
  | [a, b, c, d] => do return ((← p 0xFF a) <<< 24) ||| ((← p 0xFF b) <<< 16) ||| ((← p 0xFF c) <<< 8) ||| (← p 0xFF d)
  | _            => none

def isValidDnsLabelChars (cs : List Char) : Bool :=
  1 ≤ cs.length && cs.length ≤ 63 && cs.all isDnsLabelChar &&
  match cs.head?, cs.getLast? with | some h, some t => isDnsAlnum h && isDnsAlnum t | _, _ => false

def isValidDnsLabel (s : String) : Bool := isValidDnsLabelChars s.toList

def isValidHostname (s : String) : Bool :=
  let cs := s.toList; let labels := splitCharAux '.' cs []
  cs.length ≤ 253 && labels.length ≥ 2 && labels.all isValidDnsLabelChars &&
  (labels.getLast?.map (·.any isDnsAlpha)).getD false && (parseIpv4UInt32 s).isNone

def isReservedLocalDomain (s : String) : Bool :=
  match (splitCharAux '.' (s.toList.map asciiToLower) []).getLast? with
  | some tld => tld == "localhost".toList || tld == "local".toList | none => false

def isDomainAncestor (anc child : String) : Bool :=
  let (acs, ccs) := (anc.toList.map asciiToLower, child.toList.map asciiToLower)
  acs == ccs || (let dotAnc := '.' :: acs; ccs.length > dotAnc.length && ccs.drop (ccs.length - dotAnc.length) == dotAnc)

inductive HostPattern where | exact (host : String) | wildcard (suffix : String)
deriving Inhabited, DecidableEq, Repr

def HostPattern.baseHost : HostPattern → String | .exact h | .wildcard h => h
def HostPattern.render : HostPattern → String | .exact h => h | .wildcard s => "*." ++ s
def HostPattern.isValid : HostPattern → Bool | .exact s | .wildcard s => isValidHostname s
def HostPattern.parse? (raw : String) : Option HostPattern :=
  match raw.toList with
  | '*' :: '.' :: rest => let suf := String.ofList rest; if isValidHostname suf then some (.wildcard suf) else none
  | _ => if isValidHostname raw then some (.exact raw) else none

def HostPattern.matches (pat : HostPattern) (h : String) : Bool :=
  let hcs := h.toList.map asciiToLower
  match pat with
  | .exact target => hcs == target.toList.map asciiToLower
  | .wildcard suf =>
      let scs := '.' :: suf.toList.map asciiToLower
      if hcs.length ≤ scs.length then false
      else let n := hcs.length - scs.length; isValidDnsLabelChars (hcs.take n) && (hcs.drop n == scs)

def derivePreviewHost (prodHost subdomain : String) : HostPattern := .wildcard (subdomain ++ "." ++ prodHost)

theorem derivePreviewHost_disjoint (prodHost subLabel : String) : (derivePreviewHost prodHost subLabel).matches prodHost = false := by
  unfold derivePreviewHost HostPattern.matches
  exact ite_eq_left (by simp [String.toList_append]; omega)

private def findAfterScheme : List Char → Option (List Char)
  | ':' :: '/' :: '/' :: rest => some rest
  | c :: cs => if c == '/' || c == '?' || c == '#' || c == '\\' then none else findAfterScheme cs
  | [] => none

private def extractUrlHost (raw : String) : String :=
  let low := (((raw.toList.dropWhile (·.toNat ≤ 32)).reverse.dropWhile (·.toNat ≤ 32)).reverse).map asciiToLower
  let auth := ((findAfterScheme low).getD low).takeWhile fun c => !("/?#\\".contains c)
  let hostChars := match (splitCharAux '@' auth []).getLast?.getD [] with
    | '[' :: rest => if rest.contains ']' then (rest.takeWhile (· != ']')).takeWhile (· != '%') else []
    | cs => cs.takeWhile (· != ':')
  String.ofList (hostChars.reverse.dropWhile (· == '.')).reverse

private def parseIpv6HexGroup (cs : List Char) : Option Nat := if cs.isEmpty || cs.length > 4 then none else parseBaseAux 16 0xFFFF 0 cs

private def parseIpv6Side (allowIpv4Tail : Bool) : List (List Char) → Option (List Nat)
  | [] => some []
  | [last] => if allowIpv4Tail && last.contains '.' then (parseIpv4Strict4 last).map fun ip => [ip >>> 16, ip &&& 0xFFFF]
              else (parseIpv6HexGroup last).map (· :: [])
  | g :: gs => do return (← parseIpv6HexGroup g) :: (← parseIpv6Side allowIpv4Tail gs)

private def splitDoubleColonAux (acc : List Char) : List Char → Option (Option (List Char × List Char))
  | [] => some none
  | ':' :: ':' :: rest => if rest.head? == some ':' then none else match splitDoubleColonAux [] rest with | some none => some (some (acc.reverse, rest)) | _ => none
  | c :: cs => splitDoubleColonAux (c :: acc) cs

private def parseIpv6Groups (host : String) : Option (List Nat) := do
  let cs := host.toList.map asciiToLower; guard (!cs.isEmpty && cs.contains ':')
  match ← splitDoubleColonAux [] cs with
  | none => let gs ← parseIpv6Side true (splitCharAux ':' cs []); guard (gs.length == 8); some gs
  | some (lhs, rhs) =>
      let lg ← if lhs.isEmpty then some [] else parseIpv6Side false (splitCharAux ':' lhs [])
      let rg ← if rhs.isEmpty then some [] else parseIpv6Side true (splitCharAux ':' rhs [])
      guard (lg.length + rg.length < 8); some (lg ++ List.replicate (8 - lg.length - rg.length) 0 ++ rg)

private def isLoopbackIpv4 (ip : Nat) : Bool := (ip >>> 24) == 127 || ip == 0

private def isLoopbackIpv6 (host : String) : Bool :=
  match parseIpv6Groups host with
  | some [0, 0, 0, 0, 0, 0, 0, 1] | some [0, 0, 0, 0, 0, 0, 0, 0] => true
  | some [0, 0, 0, 0, 0, 0, hi, lo] | some [0, 0, 0, 0, 0, 0xFFFF, hi, lo] => isLoopbackIpv4 ((hi <<< 16) ||| lo)
  | _ => false

def isLocalhostUrl (s : String) : Bool :=
  let host := extractUrlHost s
  if host.isEmpty then false
  else if host == "localhost" || (host.endsWith ".localhost" && !host.startsWith ".") then true
  else match parseIpv4UInt32 host with | some ip => isLoopbackIpv4 ip | none => isLoopbackIpv6 host

def isStrictLoopbackUrl (u : String) : Bool :=
  match u.toList with
  | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: rest =>
      let trimmed := match rest.reverse with | '/' :: r => r.reverse | _ => rest
      ["127.0.0.1", "localhost", "[::1]"].any fun exp =>
        let ecs := exp.toList
        trimmed == ecs || (trimmed.take ecs.length == ecs && match trimmed.drop ecs.length with | ':' :: pc => (parsePort? pc).isSome | _ => false)
  | _ => false

end Qed.Cloud
