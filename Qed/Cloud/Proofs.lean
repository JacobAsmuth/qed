import Qed.Cloud.Compile

/-! ## Universal Formal Security & Rollout Proofs (`Qed.Cloud.Proofs`)
    Kernel-verified theorems over `compileInfra`, `compileOrgPolicy`, `planRollout`, and
    `planPreviewTeardown`. Every theorem quantifies over *all* tenants, *all* `DeploySpec`s,
    *all* `DeployManifest`s, and the open `GcpPrincipal` universe—using zero `sorry`, zero
    `native_decide`, and zero custom axioms. -/

namespace Qed.Cloud

/-- Predicate witnessing that a `GcpPlan` was produced by `compileInfra`. -/
def IsCompiledPlan (p : GcpPlan) : Prop :=
  ∃ key buildHash spec m, p = compileInfra key buildHash spec m

/-! ### Helper Lemmas on Compiled Bindings & Denies -/

private theorem compileInfra_binding_mem {key : DeployKey} {buildHash : String}
    {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {b : GcpIamBinding}
    (hb : b ∈ (compileInfra key buildHash spec m).bindings) :
    (∃ s ∈ (m.footprintFor key.env.toDeployEnv).secrets.map (·.envVar),
        b = { principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s }) ∨
    (∃ dbName ∈ (m.footprintFor key.env.toDeployEnv).managedDbs.map Prod.fst,
        b = { principal := .runtimeSa key, role := .cloudSqlClient,
              resource := .cloudSqlDb (clusterForEnv key.env) key dbName }) ∨
    b = { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key } ∨
    b = { principal := .builder, role := .storageObjectAdmin, resource := .assetPrefix key buildHash } ∨
    b = { principal := .allUsers, role := .storageObjectViewer, resource := .assetPrefix key buildHash } := by
  simp only [compileInfra, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with (((⟨s, hs, rfl⟩ | ⟨⟨dbName, cl⟩, hdb, rfl⟩) | rfl) | (rfl | rfl))
  · exact Or.inl ⟨s, List.mem_map.mpr hs, rfl⟩
  · rcases hdb with ⟨⟨db0, cl0⟩, hdb0, hpair⟩
    cases hpair
    exact Or.inr (Or.inl ⟨db0, List.mem_map.mpr ⟨(db0, cl0), hdb0, rfl⟩, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem compileInfra_deny_mem {key : DeployKey} {buildHash : String}
    {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {d : GcpDenyRule}
    (hd : d ∈ (compileInfra key buildHash spec m).denies) :
    d.principals = [.allUsers, .allAuthenticatedUsers] := by
  simp only [compileInfra, List.mem_cons, List.mem_map] at hd
  rcases hd with rfl | ⟨_, _, rfl⟩ <;> rfl

private theorem compileInfra_binding_runtimeSa_owner {key : DeployKey} {buildHash : String}
    {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {b : GcpIamBinding}
    (hb : b ∈ (compileInfra key buildHash spec m).bindings)
    {kSa : DeployKey} (hp : b.principal = .runtimeSa kSa) :
    kSa = key ∧ b.resource.ownerKey = key ∧
    (kSa.env.isPreview = true → b.resource.isProdResource = false) := by
  rcases compileInfra_binding_mem hb with
    ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> try cases hp
  all_goals
    refine ⟨rfl, rfl, fun hprev => ?_⟩
    cases h : key.env <;> simp [h, EnvInstance.isPreview, EnvInstance.isProd, clusterForEnv,
      GcpResource.isProdResource, GcpResource.ownerKey] at hprev ⊢

/-! ### Theorem 1: Zero Privilege Escalation (`canStep` is Empty Everywhere) -/

/-- No principal in ANY org state compiled by Qed Cloud holds any IAM escalation permission. -/
theorem compileOrgPolicy_no_escalation (plans : List GcpPlan)
    (p₁ p₂ : GcpPrincipal) :
    ¬ (compileOrgPolicy plans).canStep p₁ p₂ := by
  intro ⟨perm, _, hesc, ⟨b, _, _, _, hperm⟩, _⟩
  rw [GcpRole.no_escalation b.role perm hperm] at hesc
  exact Bool.false_ne_true hesc

theorem compileOrgPolicy_canReachPrincipal_eq (plans : List GcpPlan)
    {p₁ p₂ : GcpPrincipal}
    (hr : (compileOrgPolicy plans).canReachPrincipal p₁ p₂) : p₂ = p₁ := by
  cases hr with
  | refl => rfl
  | step hstep _ => exact absurd hstep (compileOrgPolicy_no_escalation plans _ _)

theorem compileOrgPolicy_canReach_iff_allows (plans : List GcpPlan)
    (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) :
    (compileOrgPolicy plans).canReach p perm r ↔ (compileOrgPolicy plans).allows p perm r :=
  ⟨fun ⟨_, hreach, hallows⟩ => by rw [compileOrgPolicy_canReachPrincipal_eq plans hreach] at hallows; exact hallows,
   fun hallows => ⟨p, .refl p, hallows⟩⟩

private theorem compileOrgPolicy_canReach_elim {plans : List GcpPlan}
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    {p : GcpPrincipal} {perm : GcpPermission} {r : GcpResource}
    (hreach : (compileOrgPolicy plans).canReach p perm r) :
    ∃ key buildHash spec m b,
      compileInfra key buildHash spec m ∈ plans ∧
      b ∈ (compileInfra key buildHash spec m).bindings ∧
      b.principal = p ∧ b.resource = r ∧ perm ∈ b.role.permissions := by
  rw [compileOrgPolicy_canReach_iff_allows] at hreach
  rcases hreach with ⟨⟨b, hbOrg, hbp, hbr, hperm⟩, _⟩
  simp only [compileOrgPolicy, List.mem_flatMap] at hbOrg
  rcases hbOrg with ⟨plan, hplanMem, hbPlan⟩
  rcases hcompiled plan hplanMem with ⟨key, buildHash, spec, m, rfl⟩
  exact ⟨key, buildHash, spec, m, b, hplanMem, hbPlan, hbp, hbr, hperm⟩

/-! ### Theorem 2: Strict Per-Deployment-Key & Multi-Tenant Isolation -/

/-- **Key Isolation Theorem:** Across ANY list of compiled deployments in an org,
    for ANY two distinct deployment keys `k₁ ≠ r.ownerKey` (different tenants, different apps,
    `staging` vs `prod`, or `preview pr₁` vs `preview pr₂`), `k₁`'s runtime SA can NEVER
    transitively reach ANY permission on `r`. -/
theorem compileOrgPolicy_key_isolation (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    (k₁ : DeployKey) (perm : GcpPermission) (r : GcpResource)
    (hdiff : k₁ ≠ r.ownerKey) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa k₁) perm r := by
  intro hreach
  rcases compileOrgPolicy_canReach_elim hcompiled hreach with ⟨_, _, _, _, _, _, hbPlan, hbp, hbr, _⟩
  have ⟨hk, hown, _⟩ := compileInfra_binding_runtimeSa_owner hbPlan hbp
  subst hk; rw [← hbr, hown] at hdiff; exact hdiff rfl

/-- **Tenant Isolation Theorem (corollary):** Distinct tenants (`k₁.tenant ≠ r.ownerKey.tenant`)
    can NEVER transitively reach each other's resources. -/
theorem compileOrgPolicy_tenant_isolation (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    (k₁ : DeployKey) (perm : GcpPermission) (r : GcpResource)
    (hdiff : k₁.tenant ≠ r.ownerKey.tenant) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa k₁) perm r :=
  compileOrgPolicy_key_isolation plans hcompiled k₁ perm r fun h => hdiff (congrArg DeployKey.tenant h)

/-! ### Theorem 3: Preview-to-Prod Isolation -/

/-- **Preview-to-Prod Isolation Theorem:** A PR preview runtime SA can NEVER transitively reach
    ANY permission on ANY production resource (prod secrets, prod Cloud Run, or `prodCluster` DBs). -/
theorem compileOrgPolicy_preview_no_prod (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    (kPrev : DeployKey) (hprev : kPrev.env.isPreview = true)
    (perm : GcpPermission) (r : GcpResource) (hprod : r.isProdResource = true) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa kPrev) perm r := by
  intro hreach
  rcases compileOrgPolicy_canReach_elim hcompiled hreach with ⟨_, _, _, _, _, _, hbPlan, hbp, hbr, _⟩
  have ⟨hk, _, hnotProd⟩ := compileInfra_binding_runtimeSa_owner hbPlan hbp
  subst hk
  have hfalse := hnotProd hprev
  rw [hbr, hprod] at hfalse
  exact Bool.false_ne_true hfalse.symm

/-! ### Theorem 4: No Raw `*.run.app` Bypass (Edge-Router-Only Cloud Run Invoke) -/

/-- **Edge-Only Invoke Theorem:** Across ANY caller `p` in the open `GcpPrincipal` universe,
    `p` can invoke a Cloud Run service ONLY if `p = .edgeRouter`. -/
theorem compileOrgPolicy_edge_only_invoke (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    (p : GcpPrincipal) (key : DeployKey)
    (hreach : (compileOrgPolicy plans).canReach p .runInvoke (.cloudRun key)) :
    p = .edgeRouter := by
  rcases compileOrgPolicy_canReach_elim hcompiled hreach with ⟨_, _, _, _, _, _, hbPlan, hbp, hbr, _⟩
  rcases compileInfra_binding_mem hbPlan with
    ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> try cases hbr
  exact hbp.symm

/-! ### Theorem 5: Public Callers Cannot Reach Any Non-Asset Resource -/

/-- **No Public Non-Asset Access:** `allUsers` and `allAuthenticatedUsers` can NEVER reach
    any permission on any secret, Cloud Run service, or Cloud SQL database. -/
theorem compileOrgPolicy_no_public_non_assets (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    (p : GcpPrincipal) (hpub : p = .allUsers ∨ p = .allAuthenticatedUsers)
    (perm : GcpPermission) (r : GcpResource) (hnotAsset : r.isPublicAsset = false) :
    ¬ (compileOrgPolicy plans).canReach p perm r := by
  intro hreach
  rcases compileOrgPolicy_canReach_elim hcompiled hreach with ⟨_, _, _, _, _, _, hbPlan, hbp, hbr, _⟩
  rcases compileInfra_binding_mem hbPlan with
    ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;>
    try (rcases hpub with rfl | rfl <;> cases hbp)
  rw [← hbr] at hnotAsset
  simp [GcpResource.isPublicAsset] at hnotAsset

/-! ### Theorem 6: Exact Least-Privilege Secrets (`iff`) -/

/-- **Exact Secret Least-Privilege Theorem:** For any compiled deployment with unique `key` in
    `plans`, its runtime SA can access `.secret key s` IF AND ONLY IF `s` is in
    `(m.footprintFor key.env.toDeployEnv).secrets`. -/
theorem compileOrgPolicy_exact_secrets (plans : List GcpPlan)
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
    {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest}
    (hmem : compileInfra key buildHash spec m ∈ plans)
    (huniq : ∀ p ∈ plans, p.key = key → p = compileInfra key buildHash spec m)
    (s : String) :
    (compileOrgPolicy plans).canReach (.runtimeSa key) .secretAccessor (.secret key s) ↔
      s ∈ (m.footprintFor key.env.toDeployEnv).secrets.map (·.envVar) := by
  constructor
  · intro hreach
    rcases compileOrgPolicy_canReach_elim hcompiled hreach with
      ⟨key', buildHash', spec', m', _, hplanMem, hbPlan, hbp, hbr, _⟩
    rcases compileInfra_binding_mem hbPlan with
      ⟨s', hs', rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> try cases hbr
    cases hbp
    have hsecEq := congrArg GcpPlan.secretNames (huniq _ hplanMem rfl)
    simp only [compileInfra] at hsecEq
    rw [← hsecEq]; exact hs'
  · intro hs
    rw [compileOrgPolicy_canReach_iff_allows]
    refine ⟨⟨{ principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s },
        ?_, rfl, rfl, by simp [GcpRole.permissions]⟩, ?_⟩
    · simp only [compileOrgPolicy, List.mem_flatMap]
      refine ⟨compileInfra key buildHash spec m, hmem, ?_⟩
      simp only [compileInfra, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨s, List.mem_map.mp hs, rfl⟩))
    · rintro ⟨d, hdOrg, hdp, _, _⟩
      simp only [compileOrgPolicy, List.mem_flatMap] at hdOrg
      rcases hdOrg with ⟨plan, hplanMem, hdPlan⟩
      rcases hcompiled plan hplanMem with ⟨_, _, _, _, rfl⟩
      rw [compileInfra_deny_mem hdPlan] at hdp
      simp at hdp

/-! ### Theorem 7: Exact Egress Allowlist (`iff`) -/

/-- **Exact Egress Theorem:** For any compiled deployment with unique `key` in `plans`,
    an egress origin is permitted IF AND ONLY IF it appears in `(m.footprintFor key.env.toDeployEnv).egress`. -/
theorem compileOrgPolicy_exact_egress (plans : List GcpPlan)
    {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest}
    (hmem : compileInfra key buildHash spec m ∈ plans)
    (huniq : ∀ p ∈ plans, p.key = key → p = compileInfra key buildHash spec m)
    (origin : String) :
    (compileOrgPolicy plans).egressAllowed key origin ↔
      origin ∈ (m.footprintFor key.env.toDeployEnv).egress := by
  simp only [GcpPolicyState.egressAllowed, compileOrgPolicy, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨plan, hplanMem, o, ho, hpair⟩
    rcases Prod.mk.inj hpair with ⟨hkeq, rfl⟩
    rw [huniq plan hplanMem hkeq] at ho
    exact ho
  · intro horig
    exact ⟨compileInfra key buildHash spec m, hmem, origin, horig, rfl⟩

/-! ### Theorem 8: Zero-Downtime 4-Phase Rollout Ordering -/

private theorem actionsPhaseOrdered_append {xs ys : List GcpAction}
    (hx : actionsPhaseOrdered xs) (hy : actionsPhaseOrdered ys)
    (hbound : ∀ a ∈ xs, ∀ b ∈ ys, a.phase.rank ≤ b.phase.rank) :
    actionsPhaseOrdered (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons x rest ih =>
      cases rest with
      | nil =>
          cases ys with
          | nil => trivial
          | cons y ys' => exact ⟨hbound x List.mem_cons_self y List.mem_cons_self, hy⟩
      | cons x2 rest' =>
          exact ⟨hx.1, ih hx.2 fun a ha b hb => hbound a (List.mem_cons_of_mem x ha) b hb⟩

private theorem actionsPhaseOrdered_const_rank {xs : List GcpAction} {r : Nat}
    (h : ∀ a ∈ xs, a.phase.rank = r) : actionsPhaseOrdered xs := by
  induction xs with
  | nil => trivial
  | cons x rest ih =>
      cases rest with
      | nil => trivial
      | cons y rest' =>
          have hx := h x List.mem_cons_self
          have hy := h y (List.mem_cons_of_mem x List.mem_cons_self)
          exact ⟨by omega, ih fun a ha => h a (List.mem_cons_of_mem x ha)⟩

private theorem actionsPhaseOrdered_four {p1 p2 p3 p4 : List GcpAction}
    (h1 : ∀ a ∈ p1, a.phase.rank = 1) (h2 : ∀ a ∈ p2, a.phase.rank = 2)
    (h3 : ∀ a ∈ p3, a.phase.rank = 3) (h4 : ∀ a ∈ p4, a.phase.rank = 4) :
    actionsPhaseOrdered (((p1 ++ p2) ++ p3) ++ p4) := by
  have step {xs ys} {rx ry : Nat} (hx : actionsPhaseOrdered xs) (hry : ∀ b ∈ ys, b.phase.rank = ry)
      (hbx : ∀ a ∈ xs, a.phase.rank ≤ rx) (hle : rx ≤ ry) :
      actionsPhaseOrdered (xs ++ ys) ∧ ∀ a ∈ xs ++ ys, a.phase.rank ≤ ry :=
    ⟨actionsPhaseOrdered_append hx (actionsPhaseOrdered_const_rank hry) fun a ha b hb => by
       have := hbx a ha; rw [hry b hb]; omega,
     fun a ha => (List.mem_append.1 ha).elim (fun h => Nat.le_trans (hbx a h) hle)
       (fun h => by rw [hry a h]; exact Nat.le_refl _)⟩
  have ⟨h12, b12⟩ := step (rx := 1) (actionsPhaseOrdered_const_rank h1) h2
    (fun a ha => by rw [h1 a ha]; exact Nat.le_refl _) (by decide)
  have ⟨h123, b123⟩ := step h12 h3 b12 (by decide)
  exact (step h123 h4 b123 (by decide)).1

/-- **Zero-Downtime Rollout Ordering Theorem:** For ANY live state and desired plan,
    `planRollout` emits actions in non-decreasing phase order:
    Phase 1 (provision + widen egress) ≤ Phase 2 (0% deploy + health check)
    ≤ Phase 3 (atomic 100% traffic flip) ≤ Phase 4 (revoke stale bindings/secrets + narrow egress). -/
theorem planRollout_zero_downtime_order (live : GcpObservedState) (desired : GcpPlan) :
    actionsPhaseOrdered (planRollout live desired) := by
  unfold planRollout
  refine actionsPhaseOrdered_four ?_ ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (((((hA | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | rfl) <;> try rfl
    split at hA <;> simp at hA; subst hA; rfl
  · intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> rfl
  · intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; rfl
  · intro a ha
    simp only [List.mem_append, List.mem_map] at ha
    rcases ha with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | hN <;> try rfl
    split at hN <;> simp at hN; rcases hN with ⟨_, rfl⟩; rfl

private theorem planRollout_mem_spec {live : GcpObservedState} {desired : GcpPlan} {a : GcpAction}
    (ha : a ∈ planRollout live desired) :
    a.isDestructive = false ∨
      (a.phase = .phase4_cleanup ∧ a.targetKey = desired.key ∧ live.key = desired.key) := by
  simp only [planRollout, List.mem_append, List.mem_map, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with (((((((hA | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | rfl) | (rfl | rfl)) | rfl) |
    ((⟨b, ⟨hbL, hfilt⟩, rfl⟩ | ⟨s, hsL, rfl⟩) | hN) <;> try exact Or.inl rfl
  · split at hA <;> simp at hA; subst hA; exact Or.inl rfl
  · split at hbL <;> simp_all [GcpAction.targetKey]
    exact Or.inr rfl
  · split at hsL <;> simp_all [GcpAction.targetKey]
    exact Or.inr rfl
  · split at hN
    · rename_i hne; simp at hN; rcases hN with ⟨_, rfl⟩
      simp_all [GcpAction.targetKey]; exact Or.inr rfl
    · simp at hN

/-- Every destructive action emitted by `planRollout` occurs strictly in Phase 4 (after traffic flip)
    and targets ONLY `desired.key`. -/
theorem planRollout_destructive_scoped_phase4 (live : GcpObservedState) (desired : GcpPlan)
    (a : GcpAction) (ha : a ∈ planRollout live desired) (hdest : a.isDestructive = true) :
    a.phase = .phase4_cleanup ∧ a.targetKey = desired.key := by
  rcases planRollout_mem_spec ha with hnd | ⟨hp, ht, _⟩
  · rw [hnd] at hdest; cases hdest
  · exact ⟨hp, ht⟩

/-- If `live.key ≠ desired.key`, `planRollout` safely ignores `live` and emits ZERO destructive actions. -/
theorem planRollout_mismatched_live_no_destructive (live : GcpObservedState) (desired : GcpPlan)
    (hne : live.key ≠ desired.key) (a : GcpAction) (ha : a ∈ planRollout live desired) :
    a.isDestructive = false := by
  rcases planRollout_mem_spec ha with hnd | ⟨_, _, hkey⟩
  · exact hnd
  · exact absurd hkey hne

/-- Any preview deployment with an ephemeral DB is pinned to `maxInstances = 1` and at most 1 region. -/
theorem compileInfra_ephemeral_preview_pinned (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (hprev : key.env.isPreview = true)
    (hephem : (m.footprintFor key.env.toDeployEnv).ephemeralDbs.isEmpty = false) :
    (compileInfra key buildHash spec m).scale.maxInstances = 1 ∧
    (compileInfra key buildHash spec m).regions.length ≤ 1 := by
  simp [compileInfra, hephem, hprev]
  exact Nat.min_le_left _ _

/-- Any stateful server (`hasState = true`) is automatically pinned to `maxInstances = 1`,
    at most 1 region, and `concurrency = 1000` (so Cloud Run never rejects concurrent requests
    while preserving single-process `atomic:` soundness). -/
theorem compileInfra_stateful_single_instance (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (hstate : (m.server?.map (·.hasState)).getD false = true) :
    let p := compileInfra key buildHash spec m
    p.scale.maxInstances = 1 ∧ p.regions.length ≤ 1 ∧ p.scale.concurrency = 1000 := by
  simp [compileInfra, hstate]
  exact Nat.min_le_left _ _

/-- Any server declaring background `every` jobs is automatically kept warm (`minInstances = 1`). -/
theorem compileInfra_jobs_never_scale_to_zero (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (hjobs : (m.server?.map fun s => !s.jobs.isEmpty).getD false = true) :
    (compileInfra key buildHash spec m).scale.minInstances = 1 := by
  simp [compileInfra, hjobs]

/-- Any server declaring WebSocket `channel`s gets `concurrency = 1000` and (when `timeout` is omitted)
    the full 3600s Cloud Run socket timeout. -/
theorem compileInfra_channels_socket_ready (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (hch : (m.server?.map fun s => !s.channels.isEmpty).getD false = true) :
    (compileInfra key buildHash spec m).scale.concurrency = 1000 ∧
    (spec.timeoutSec? = none → (compileInfra key buildHash spec m).scale.timeoutSec = 3600) :=
  ⟨by simp [compileInfra, hch], fun hnone => by simp [compileInfra, hch, hnone]⟩

/-- Every `GcpPlan` emitted by `compileInfra` with an omitted or in-range `timeoutSec?`
    satisfies Cloud Run's full hardware & scaling `ScaleSpec.validate` contract by construction. -/
theorem compileInfra_scale_valid (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (hto : ∀ t, spec.timeoutSec? = some t → 1 ≤ t ∧ t ≤ 3600) :
    (compileInfra key buildHash spec m).scale.validate = .ok () := by
  have htier (tier : ComputeTier) (minI maxI conc t : Nat)
      (hmin : minI ≤ maxI) (hmax : 1 ≤ maxI) (hconc : 1 ≤ conc ∧ conc ≤ 1000) (ht : 1 ≤ t ∧ t ≤ 3600) :
      ScaleSpec.validate {
        minInstances := minI, maxInstances := maxI,
        memoryMb := tier.memoryMb, cpuMilli := tier.cpuMilli,
        concurrency := conc, timeoutSec := t
      } = .ok () := by
    unfold ScaleSpec.validate
    cases tier <;>
      (simp [ComputeTier.memoryMb, ComputeTier.cpuMilli, ComputeTier.specs, minCpuRules, minMemRules,
            beq_false_of_ne (show maxI ≠ 0 by omega), show ¬ (minI > maxI) by omega,
            beq_false_of_ne (show conc ≠ 0 by omega), show ¬ (conc > 1000) by omega,
            beq_false_of_ne (show t ≠ 0 by omega), show ¬ (t > 3600) by omega]; rfl)
  apply htier
  · split <;> split <;> omega
  · split <;> omega
  · split
    · decide
    · cases spec.compute <;> decide
  · cases ht : spec.timeoutSec? with
    | none => cases (m.server?.map fun s => !s.channels.isEmpty).getD false <;> decide
    | some t => simpa [ht] using hto t ht

/-! ### Theorem 9: Safe PR Preview Teardown (Never Touches Prod) -/

/-- Tearing down a `.prod` environment via `planPreviewTeardown` is strictly a no-op. -/
theorem planPreviewTeardown_noop_on_prod (live : GcpObservedState)
    (hprod : live.key.env = .prod) :
    planPreviewTeardown live = [] := by
  simp [planPreviewTeardown, hprod, EnvInstance.isPreview]

/-- No action emitted by `planPreviewTeardown` EVER targets a production deployment key. -/
theorem planPreviewTeardown_never_targets_prod (live : GcpObservedState)
    (a : GcpAction) (ha : a ∈ planPreviewTeardown live) :
    a.targetKey.env.isProd = false := by
  unfold planPreviewTeardown at ha
  split at ha
  · simp at ha
  · rename_i hnot
    have hnotProd : live.key.env.isProd = false := by
      cases h : live.key.env <;> simp [h, EnvInstance.isPreview, EnvInstance.isProd] at hnot ⊢
    simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((⟨b, ⟨_, hown⟩, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | rfl <;> try exact hnotProd
    simp only [beq_iff_eq] at hown
    simp [GcpAction.targetKey, hown, hnotProd]

end Qed.Cloud
