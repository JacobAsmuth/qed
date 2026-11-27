import Qed.Cloud.Compile

/-! ## Universal Formal Security & Rollout Proofs (`Qed.Cloud.Proofs`) -/

namespace Qed.Cloud

def IsCompiledPlan (p : GcpPlan) : Prop := ∃ key buildHash spec m, p = compileInfra key buildHash spec m

private theorem isPreview_imp_not_isProd {e : EnvInstance} (h : e.isPreview = true) : e.isProd = false := by cases e <;> first | rfl | exact Bool.noConfusion h

private theorem compileInfra_binding_mem {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {b : GcpIamBinding}
    (hb : b ∈ (compileInfra key buildHash spec m).bindings) :
    let assetIsPublic := !(key.env.isPreview && spec.preview.protection == .team_only)
    (∃ s ∈ (m.footprintFor key.env.toDeployEnv).secrets.map (·.envVar), b = { principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s }) ∨
    (∃ dbName ∈ (m.footprintFor key.env.toDeployEnv).managedDbs.map Prod.fst, b = { principal := .runtimeSa key, role := .cloudSqlClient, resource := .cloudSqlDb (clusterForEnv key.env) key dbName }) ∨
    b = { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key } ∨
    b = { principal := .builder, role := .storageObjectAdmin, resource := .assetPrefix key buildHash assetIsPublic } ∨
    b = { principal := if assetIsPublic then .allUsers else .edgeRouter, role := .storageLegacyObjectReader, resource := .assetPrefix key buildHash assetIsPublic } := by
  simp only [compileInfra, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (((⟨s, hs, rfl⟩ | ⟨⟨_, _⟩, ⟨⟨db0, cl0⟩, hdb0, hp⟩, rfl⟩) | rfl) | (rfl | rfl))
  · exact .inl ⟨s, List.mem_map.2 hs, rfl⟩
  · cases hp; exact .inr (.inl ⟨db0, List.mem_map.2 ⟨(db0, cl0), hdb0, rfl⟩, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr rfl)))

private theorem compileInfra_binding_not_project {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {b : GcpIamBinding}
    (hb : b ∈ (compileInfra key buildHash spec m).bindings) {r : GcpResource} (hap : b.resource.bindingApplies r) : b.resource = r := by
  rcases hap with h | hproj; exact h; rcases compileInfra_binding_mem hb with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> cases hproj

private theorem compileInfra_deny_mem {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest} {d : GcpDenyRule}
    (hd : d ∈ (compileInfra key buildHash spec m).denies) : d.principals = [.allUsers, .allAuthenticatedUsers] := by
  simp only [compileInfra, List.mem_cons, List.mem_map] at hd; rcases hd with rfl | ⟨_, _, rfl⟩ <;> rfl

/-! ### Theorem 1: Zero Privilege Escalation (Universal for Any `GcpPolicyState`) -/

private theorem policy_no_escalation (st : GcpPolicyState) (p₁ p₂ : GcpPrincipal) : ¬ st.canStep p₁ p₂ := by
  intro ⟨perm, _, hesc, ⟨b, _, _, _, hperm⟩, _⟩; rw [GcpRole.no_escalation b.role perm hperm] at hesc; exact Bool.false_ne_true hesc
private theorem policy_canReachPrincipal_eq (st : GcpPolicyState) {p₁ p₂ : GcpPrincipal} (hr : st.canReachPrincipal p₁ p₂) : p₂ = p₁ := by
  cases hr with | refl => rfl | step hstep _ => exact absurd hstep (policy_no_escalation st _ _)
private theorem policy_canReach_iff_allows (st : GcpPolicyState) (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) :
    st.canReach p perm r ↔ st.allows p perm r := ⟨fun ⟨_, hr, ha⟩ => policy_canReachPrincipal_eq st hr ▸ ha, fun ha => ⟨p, .refl p, ha⟩⟩

theorem compileOrgPolicy_no_escalation (plans : List GcpPlan) (p₁ p₂ : GcpPrincipal) : ¬ (compileOrgPolicy plans).canStep p₁ p₂ := policy_no_escalation _ p₁ p₂
theorem compileOrgPolicy_canReachPrincipal_eq (plans : List GcpPlan) {p₁ p₂ : GcpPrincipal} (hr : (compileOrgPolicy plans).canReachPrincipal p₁ p₂) : p₂ = p₁ := policy_canReachPrincipal_eq _ hr
theorem compileOrgPolicy_canReach_iff_allows (plans : List GcpPlan) (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) :
    (compileOrgPolicy plans).canReach p perm r ↔ (compileOrgPolicy plans).allows p perm r := policy_canReach_iff_allows _ p perm r
theorem realizeOrgPolicy_canReach_iff_allows (plans : List GcpPlan) (p : GcpPrincipal) (perm : GcpPermission) (r : GcpResource) :
    (realizeOrgPolicy plans).canReach p perm r ↔ (realizeOrgPolicy plans).allows p perm r := policy_canReach_iff_allows _ p perm r

private theorem mapped_canReach_elim {plans : List GcpPlan} {st : GcpPolicyState} {f : GcpIamBinding → GcpIamBinding}
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p) (hB : ∀ rb ∈ st.bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = f b)
    {p : GcpPrincipal} {perm : GcpPermission} {r : GcpResource} (hreach : st.canReach p perm r) :
    ∃ key buildHash spec m b, compileInfra key buildHash spec m ∈ plans ∧ b ∈ (compileInfra key buildHash spec m).bindings ∧
      (f b).principal = p ∧ (f b).resource.bindingApplies r ∧ perm ∈ (f b).role.permissions := by
  rcases (policy_canReach_iff_allows st p perm r).1 hreach with ⟨⟨rb, hrb, hbp, hbr, hperm⟩, _⟩
  rcases hB rb hrb with ⟨plan, hplanMem, b, hbPlan, rfl⟩; rcases hcompiled plan hplanMem with ⟨key, buildHash, spec, m, rfl⟩
  exact ⟨key, buildHash, spec, m, b, hplanMem, hbPlan, hbp, hbr, hperm⟩

private theorem compileOrgPolicy_bindings_mem (plans : List GcpPlan) :
    ∀ rb ∈ (compileOrgPolicy plans).bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = id b := by
  simp only [compileOrgPolicy, List.mem_flatMap, id_eq]; rintro rb ⟨plan, hplan, hb⟩; exact ⟨plan, hplan, rb, hb, rfl⟩
private theorem realizeOrgPolicy_bindings_mem (plans : List GcpPlan) :
    ∀ rb ∈ (realizeOrgPolicy plans).bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = realizeGcpBinding b := by
  simp only [realizeOrgPolicy, compileOrgPolicy, List.mem_map, List.mem_flatMap]; rintro _ ⟨b, ⟨plan, hplan, hb⟩, rfl⟩; exact ⟨plan, hplan, b, hb, rfl⟩
private theorem realizeGcpBinding_pr_role (b : GcpIamBinding) :
    (realizeGcpBinding b).principal = b.principal ∧ (realizeGcpBinding b).role = b.role := by rcases b with ⟨_, _, res⟩; cases res <;> exact ⟨rfl, rfl⟩

private theorem mapped_runtimeSa_owner {plans : List GcpPlan} {st : GcpPolicyState} {f : GcpIamBinding → GcpIamBinding}
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p) (hB : ∀ rb ∈ st.bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = f b)
    (hpr : ∀ b, (f b).principal = b.principal) {kSa : DeployKey} {perm : GcpPermission} {r : GcpResource} (hreach : st.canReach (.runtimeSa kSa) perm r) :
    ∃ b, ((∃ s, b = { principal := .runtimeSa kSa, role := .secretManagerAccessor, resource := .secret kSa s }) ∨
          (∃ dbName, b = { principal := .runtimeSa kSa, role := .cloudSqlClient, resource := .cloudSqlDb (clusterForEnv kSa.env) kSa dbName })) ∧
      (f b).resource.bindingApplies r := by
  rcases mapped_canReach_elim hcompiled hB hreach with ⟨_, _, _, _, b, _, hbPlan, hbp, hbr, _⟩; rw [hpr b] at hbp
  rcases compileInfra_binding_mem hbPlan with ⟨s, _, rfl⟩ | ⟨dbName, _, rfl⟩ | rfl | rfl | rfl
  · cases hbp; exact ⟨_, .inl ⟨s, rfl⟩, hbr⟩
  · cases hbp; exact ⟨_, .inr ⟨dbName, rfl⟩, hbr⟩
  · cases hbp
  · cases hbp
  · dsimp only at hbp; split at hbp <;> cases hbp

private theorem secret_preview_ne_prod {kPrev : DeployKey} {s : String} {r : GcpResource}
    (hprev : kPrev.env.isPreview = true) (hprod : r.isProdResource = true) (hbr : (GcpResource.secret kPrev s).bindingApplies r) : False := by
  rcases hbr with rfl | hproj; · have := isPreview_imp_not_isProd hprev; simp [GcpResource.isProdResource, GcpResource.ownerKey, GcpResource.ownerKey?, this] at hprod
  · cases hproj

private theorem mapped_edge_only_invoke {plans : List GcpPlan} {st : GcpPolicyState} {f : GcpIamBinding → GcpIamBinding}
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p) (hB : ∀ rb ∈ st.bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = f b)
    (hpr : ∀ b, (f b).principal = b.principal ∧ (f b).role = b.role) {p : GcpPrincipal} {key : DeployKey}
    (hreach : st.canReach p .runInvoke (.cloudRun key)) : p = .edgeRouter := by
  rcases mapped_canReach_elim hcompiled hB hreach with ⟨_, _, _, _, b, _, hbPlan, hbp, _, hperm⟩
  rw [(hpr b).1] at hbp; rw [(hpr b).2] at hperm
  rcases compileInfra_binding_mem hbPlan with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> simp [GcpRole.permissions] at hperm
  exact hbp.symm

private theorem mapped_no_public_non_assets {plans : List GcpPlan} {st : GcpPolicyState} {f : GcpIamBinding → GcpIamBinding}
    (hcompiled : ∀ p ∈ plans, IsCompiledPlan p) (hB : ∀ rb ∈ st.bindings, ∃ plan ∈ plans, ∃ b ∈ plan.bindings, rb = f b)
    (hpr : ∀ b, (f b).principal = b.principal) (hasset : ∀ k h pub pr ro, f { principal := pr, role := ro, resource := .assetPrefix k h pub } = { principal := pr, role := ro, resource := .assetPrefix k h pub })
    {p : GcpPrincipal} (hpub : p = .allUsers ∨ p = .allAuthenticatedUsers) {perm : GcpPermission} {r : GcpResource} (hnotAsset : r.isPublicAsset = false) :
    ¬ st.canReach p perm r := fun hreach => by
  rcases mapped_canReach_elim hcompiled hB hreach with ⟨key, _, spec, _, b, _, hbPlan, hbp, hbr, _⟩; rw [hpr b] at hbp
  rcases compileInfra_binding_mem hbPlan with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> try (rcases hpub with rfl | rfl <;> cases hbp)
  rw [hasset] at hbr; dsimp only at hbp hbr; cases hpubA : !(key.env.isPreview && spec.preview.protection == .team_only)
  · simp [hpubA] at hbp; rcases hpub with rfl | rfl <;> cases hbp
  · simp [hpubA] at hbr; rcases hbr with rfl | hProj; (simp [GcpResource.isPublicAsset] at hnotAsset); cases hProj

/-! ### Theorems 2-7 & 10: Multi-Tenant, Preview-to-Prod, Edge-Only Invoke, Public Non-Asset, Secrets, & Egress -/

section OrgTheorems
variable (plans : List GcpPlan) (hcompiled : ∀ p ∈ plans, IsCompiledPlan p)
include hcompiled

theorem compileOrgPolicy_key_isolation (k₁ : DeployKey) (perm : GcpPermission) (r : GcpResource) (hdiff : k₁ ≠ r.ownerKey) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa k₁) perm r := fun hreach => by
  rcases mapped_runtimeSa_owner hcompiled (compileOrgPolicy_bindings_mem plans) (fun _ => rfl) hreach with ⟨_, (⟨_, rfl⟩ | ⟨_, rfl⟩), hbr⟩ <;>
    (rcases hbr with rfl | hproj; exact hdiff rfl; cases hproj)

theorem compileOrgPolicy_tenant_isolation (k₁ : DeployKey) (perm : GcpPermission) (r : GcpResource) (hdiff : k₁.tenant ≠ r.ownerKey.tenant) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa k₁) perm r :=
  compileOrgPolicy_key_isolation plans hcompiled k₁ perm r fun h => hdiff (congrArg DeployKey.tenant h)

theorem compileOrgPolicy_preview_no_prod (kPrev : DeployKey) (hprev : kPrev.env.isPreview = true) (perm : GcpPermission) (r : GcpResource) (hprod : r.isProdResource = true) :
    ¬ (compileOrgPolicy plans).canReach (.runtimeSa kPrev) perm r := fun hreach => by
  rcases mapped_runtimeSa_owner hcompiled (compileOrgPolicy_bindings_mem plans) (fun _ => rfl) hreach with ⟨_, (⟨_, rfl⟩ | ⟨_, rfl⟩), hbr⟩
  · exact secret_preview_ne_prod hprev hprod hbr
  · rcases hbr with rfl | hproj; (cases h : kPrev.env <;> simp [h, EnvInstance.isPreview, clusterForEnv, GcpResource.isProdResource] at hprev hprod); cases hproj

theorem compileOrgPolicy_edge_only_invoke (p : GcpPrincipal) (key : DeployKey) (hreach : (compileOrgPolicy plans).canReach p .runInvoke (.cloudRun key)) : p = .edgeRouter :=
  mapped_edge_only_invoke hcompiled (compileOrgPolicy_bindings_mem plans) (fun _ => ⟨rfl, rfl⟩) hreach
theorem realizeOrgPolicy_edge_only_invoke (p : GcpPrincipal) (key : DeployKey) (hreach : (realizeOrgPolicy plans).canReach p .runInvoke (.cloudRun key)) : p = .edgeRouter :=
  mapped_edge_only_invoke hcompiled (realizeOrgPolicy_bindings_mem plans) realizeGcpBinding_pr_role hreach
theorem compileOrgPolicy_no_public_non_assets (p : GcpPrincipal) (hpub : p = .allUsers ∨ p = .allAuthenticatedUsers) (perm : GcpPermission) (r : GcpResource) (hnotAsset : r.isPublicAsset = false) :
    ¬ (compileOrgPolicy plans).canReach p perm r := mapped_no_public_non_assets hcompiled (compileOrgPolicy_bindings_mem plans) (fun _ => rfl) (fun _ _ _ _ _ => rfl) hpub hnotAsset
theorem realizeOrgPolicy_no_public_non_assets (p : GcpPrincipal) (hpub : p = .allUsers ∨ p = .allAuthenticatedUsers) (perm : GcpPermission) (r : GcpResource) (hnotAsset : r.isPublicAsset = false) :
    ¬ (realizeOrgPolicy plans).canReach p perm r := mapped_no_public_non_assets hcompiled (realizeOrgPolicy_bindings_mem plans) (fun b => (realizeGcpBinding_pr_role b).1) (fun _ _ _ _ _ => rfl) hpub hnotAsset

theorem realizeOrgPolicy_preview_no_prod (kPrev : DeployKey) (hprev : kPrev.env.isPreview = true) (perm : GcpPermission) (r : GcpResource) (hprod : r.isProdResource = true) (hshard : r.ownerKey.shard = kPrev.shard) :
    ¬ (realizeOrgPolicy plans).canReach (.runtimeSa kPrev) perm r := fun hreach => by
  rcases mapped_runtimeSa_owner hcompiled (realizeOrgPolicy_bindings_mem plans) (fun b => (realizeGcpBinding_pr_role b).1) hreach with ⟨_, (⟨_, rfl⟩ | ⟨_, rfl⟩), hbr⟩
  · exact secret_preview_ne_prod hprev hprod hbr
  · simp only [realizeGcpBinding] at hbr; rcases hbr with rfl | hproj; (simp [GcpResource.isProdResource] at hprod)
    injection hproj with hProjEq; rw [GcpResource.projectOf_of_isProdResource hprod, hshard] at hProjEq
    have hcl : clusterForEnv kPrev.env = .nonProdCluster := by cases h : kPrev.env <;> simp [h, EnvInstance.isPreview, clusterForEnv] at hprev ⊢
    rw [hcl, ShardProject.clusterProject] at hProjEq; exact kPrev.shard.separated hProjEq.symm

theorem compileOrgPolicy_exact_secrets {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest}
    (hmem : compileInfra key buildHash spec m ∈ plans) (huniq : ∀ p ∈ plans, p.key = key → p = compileInfra key buildHash spec m) (s : String) :
    (compileOrgPolicy plans).canReach (.runtimeSa key) .secretAccessor (.secret key s) ↔ s ∈ (m.footprintFor key.env.toDeployEnv).secrets.map (·.envVar) := by
  constructor
  · intro hreach; rcases mapped_canReach_elim hcompiled (compileOrgPolicy_bindings_mem plans) hreach with ⟨_, _, _, _, _, hplanMem, hbPlan, hbp, hbr, _⟩
    have hbr := compileInfra_binding_not_project hbPlan hbr
    rcases compileInfra_binding_mem hbPlan with ⟨_, hs', rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> try cases hbr
    cases hbp; have hsecEq := congrArg GcpPlan.secretNames (huniq _ hplanMem rfl); simp only [compileInfra] at hsecEq; rwa [← hsecEq]
  · intro hs; rw [compileOrgPolicy_canReach_iff_allows]
    refine ⟨⟨{ principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s }, ?_, rfl, .inl rfl, by simp [GcpRole.permissions]⟩, ?_⟩
    · simp only [compileOrgPolicy, List.mem_flatMap]; refine ⟨compileInfra key buildHash spec m, hmem, ?_⟩
      simp only [compileInfra, List.mem_append, List.mem_map]; exact .inl (.inl (.inl ⟨s, List.mem_map.mp hs, rfl⟩))
    · rintro ⟨d, hdOrg, hdp, _, _⟩; simp only [compileOrgPolicy, List.mem_flatMap] at hdOrg
      rcases hdOrg with ⟨plan, hplanMem, hdPlan⟩; rcases hcompiled plan hplanMem with ⟨_, _, _, _, rfl⟩; rw [compileInfra_deny_mem hdPlan] at hdp; simp at hdp

end OrgTheorems

theorem compileOrgPolicy_exact_egress (plans : List GcpPlan) {key : DeployKey} {buildHash : String} {spec : DeploySpec} {m : Qed.Deploy.DeployManifest}
    (hmem : compileInfra key buildHash spec m ∈ plans) (huniq : ∀ p ∈ plans, p.key = key → p = compileInfra key buildHash spec m) (origin : String) :
    (compileOrgPolicy plans).egressAllowed key origin ↔ origin ∈ (m.footprintFor key.env.toDeployEnv).egress := by
  simp only [GcpPolicyState.egressAllowed, compileOrgPolicy, List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨plan, hpm, o, ho, hp⟩ => by rcases Prod.mk.inj hp with ⟨hk, rfl⟩; rwa [huniq plan hpm hk] at ho, fun ho => ⟨compileInfra key buildHash spec m, hmem, origin, ho, rfl⟩⟩

/-! ### Theorem 8: Zero-Downtime 4-Phase Rollout Ordering & Destructive Scoping -/

private theorem actionsPhaseOrdered_append : ∀ {xs ys : List GcpAction}, actionsPhaseOrdered xs → actionsPhaseOrdered ys →
    (∀ a ∈ xs, ∀ b ∈ ys, a.phase.rank ≤ b.phase.rank) → actionsPhaseOrdered (xs ++ ys)
  | [], _, _, hy, _ => hy | [_], [], _, _, _ => trivial | [x], y :: _, _, hy, hb => ⟨hb x (.head _) y (.head _), hy⟩
  | _ :: _ :: _, _, hx, hy, hb => ⟨hx.1, actionsPhaseOrdered_append hx.2 hy fun a ha b hb' => hb a (.tail _ ha) b hb'⟩
private theorem actionsPhaseOrdered_const {r : Nat} : ∀ {xs : List GcpAction}, (∀ a ∈ xs, a.phase.rank = r) → actionsPhaseOrdered xs
  | [], _ | [_], _ => trivial
  | x :: y :: _, h => ⟨by rw [h x (.head _), h y (.tail _ (.head _))]; exact Nat.le_refl _, actionsPhaseOrdered_const fun a ha => h a (.tail _ ha)⟩
private theorem actionsPhaseOrdered_four {p1 p2 p3 p4 : List GcpAction} {P : GcpAction → Prop}
    (h1 : ∀ a ∈ p1, a.phase.rank = 1 ∧ P a) (h2 : ∀ a ∈ p2, a.phase.rank = 2 ∧ P a) (h3 : ∀ a ∈ p3, a.phase.rank = 3 ∧ P a) (h4 : ∀ a ∈ p4, a.phase.rank = 4 ∧ P a) :
    actionsPhaseOrdered (((p1 ++ p2) ++ p3) ++ p4) ∧ ∀ a ∈ ((p1 ++ p2) ++ p3) ++ p4, P a := by
  have step {xs ys} {rx ry : Nat} (hx : actionsPhaseOrdered xs) (hpx : ∀ a ∈ xs, P a) (hry : ∀ b ∈ ys, b.phase.rank = ry ∧ P b) (hbx : ∀ a ∈ xs, a.phase.rank ≤ rx) (hle : rx ≤ ry) :
      actionsPhaseOrdered (xs ++ ys) ∧ (∀ a ∈ xs ++ ys, a.phase.rank ≤ ry) ∧ (∀ a ∈ xs ++ ys, P a) :=
    ⟨actionsPhaseOrdered_append hx (actionsPhaseOrdered_const fun b hb => (hry b hb).1) fun a ha b hb => Nat.le_trans (Nat.le_trans (hbx a ha) hle) (Nat.le_of_eq (hry b hb).1.symm),
     fun a ha => (List.mem_append.1 ha).elim (fun h => Nat.le_trans (hbx a h) hle) (fun h => Nat.le_of_eq (hry a h).1),
     fun a ha => (List.mem_append.1 ha).elim (hpx a) (fun h => (hry a h).2)⟩
  have ⟨h12, b12, p12⟩ := step (rx := 1) (actionsPhaseOrdered_const fun a ha => (h1 a ha).1) (fun a ha => (h1 a ha).2) h2 (fun a ha => Nat.le_of_eq (h1 a ha).1) (by decide)
  have ⟨h123, b123, p123⟩ := step h12 p12 h3 b12 (by decide); have ⟨h1234, _, p1234⟩ := step h123 p123 h4 b123 (by decide); exact ⟨h1234, p1234⟩

private theorem planRollout_all_spec (live : GcpObservedState) (desired : GcpPlan) :
    actionsPhaseOrdered (planRollout live desired) ∧
    ∀ a ∈ planRollout live desired, a.isDestructive = false ∨ (a.phase = .phase4_cleanup ∧ a.targetKey = desired.key ∧ live.key = desired.key ∧ ∀ b, a = .revokeBinding b → b.resource.isAsset = false) := by
  unfold planRollout; refine actionsPhaseOrdered_four ?_ ?_ ?_ ?_
  · intro a ha; simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (((((hA | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | rfl) <;> try exact ⟨rfl, .inl rfl⟩
    split at hA; (cases hA); cases List.mem_singleton.1 hA; exact ⟨rfl, .inl rfl⟩
  · intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> exact ⟨rfl, .inl rfl⟩
  · intro a ha; cases List.mem_singleton.1 ha; exact ⟨rfl, .inl rfl⟩
  · intro a ha; simp only [List.mem_append, List.mem_map, List.mem_filter] at ha
    rcases ha with (⟨b, ⟨hbL, hfilt⟩, rfl⟩ | ⟨s, ⟨hsL, _⟩, rfl⟩) | hN
    · split at hbL; (rename_i hkey; simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hkey hfilt; exact ⟨rfl, .inr ⟨rfl, GcpResource.ownerKey?_eq_some_imp_ownerKey hfilt.1.1, hkey, fun _ h => by cases h; exact hfilt.1.2⟩⟩); cases hbL
    · split at hsL; exact ⟨rfl, .inr ⟨rfl, rfl, beq_iff_eq.mp ‹_›, fun _ h => by cases h⟩⟩; cases hsL
    · split at hN; (rename_i hkey; split at hN; (cases List.mem_singleton.1 hN; exact ⟨rfl, .inr ⟨rfl, rfl, beq_iff_eq.mp hkey, fun _ h => by cases h⟩⟩); cases hN); simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte] at hN; cases hN

section RolloutTheorems
variable (live : GcpObservedState) (desired : GcpPlan)
theorem planRollout_zero_downtime_order : actionsPhaseOrdered (planRollout live desired) := (planRollout_all_spec live desired).1
theorem planRollout_never_revokes_asset (b : GcpIamBinding) (ha : GcpAction.revokeBinding b ∈ planRollout live desired) :
    b.resource.isAsset = false := ((planRollout_all_spec live desired).2 _ ha).elim (fun h => by cases h) (fun ⟨_, _, _, hna⟩ => hna b rfl)
theorem planRollout_destructive_scoped_phase4 (a : GcpAction) (ha : a ∈ planRollout live desired) (hdest : a.isDestructive = true) :
    a.phase = .phase4_cleanup ∧ a.targetKey = desired.key := ((planRollout_all_spec live desired).2 _ ha).elim (fun h => by rw [h] at hdest; cases hdest) (fun ⟨hp, ht, _⟩ => ⟨hp, ht⟩)
theorem planRollout_mismatched_live_no_destructive (hne : live.key ≠ desired.key) (a : GcpAction) (ha : a ∈ planRollout live desired) :
    a.isDestructive = false := ((planRollout_all_spec live desired).2 _ ha).elim id (fun ⟨_, _, hk, _⟩ => absurd hk hne)
end RolloutTheorems

/-! ### Platform-Derived Scaling & Safe PR Preview Teardown Proofs -/

section ScaleTheorems
variable (key : DeployKey) (buildHash : String) (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
theorem compileInfra_ephemeral_preview_pinned (hprev : key.env.isPreview = true) (hephem : (m.footprintFor key.env.toDeployEnv).ephemeralDbs.isEmpty = false) :
    (compileInfra key buildHash spec m).scale.maxInstances = 1 ∧ (compileInfra key buildHash spec m).regions.length ≤ 1 := by simp [compileInfra, hephem, hprev]; exact Nat.min_le_left _ _
theorem compileInfra_stateful_single_instance (hstate : (m.server?.map (·.hasState)).getD false = true) :
    let p := compileInfra key buildHash spec m; p.scale.maxInstances = 1 ∧ p.regions.length ≤ 1 ∧ p.scale.concurrency = 1000 := by simp [compileInfra, hstate]; exact Nat.min_le_left _ _
theorem compileInfra_jobs_never_scale_to_zero (hjobs : (m.server?.map fun s => !s.jobs.isEmpty).getD false = true) :
    (compileInfra key buildHash spec m).scale.minInstances = 1 := by simp [compileInfra, hjobs]
theorem compileInfra_channels_socket_ready (hch : (m.server?.map fun s => !s.channels.isEmpty).getD false = true) :
    (compileInfra key buildHash spec m).scale.concurrency = 1000 ∧ (spec.timeoutSec? = none → (compileInfra key buildHash spec m).scale.timeoutSec = 3600) := ⟨by simp [compileInfra, hch], fun hnone => by simp [compileInfra, hch, hnone]⟩
theorem compileInfra_scale_valid (hto : ∀ t, spec.timeoutSec? = some t → 1 ≤ t ∧ t ≤ 3600) : (compileInfra key buildHash spec m).scale.validate = .ok () := by
  have htier (tier : ComputeTier) (minI maxI conc t : Nat) (hmin : minI ≤ maxI) (hmax : 1 ≤ maxI) (hconc : 1 ≤ conc ∧ conc ≤ 1000) (ht : 1 ≤ t ∧ t ≤ 3600) :
      ScaleSpec.validate { minInstances := minI, maxInstances := maxI, memoryMb := tier.memoryMb, cpuMilli := tier.cpuMilli, concurrency := conc, timeoutSec := t } = .ok () := by
    have ⟨hmem, hcpu, hminC, hminM, hlt1k⟩ : (tier.memoryMb < 128 || tier.memoryMb > 32768) = false ∧ decide (tier.cpuMilli ∈ [250, 500, 1000, 2000, 4000, 6000, 8000]) = true ∧ minCpuRules.find? (fun (m, c, _) => tier.memoryMb > m && tier.cpuMilli < c) = none ∧ minMemRules.find? (fun (c, m, _) => tier.cpuMilli ≥ c && tier.memoryMb < m) = none ∧ decide (tier.cpuMilli < 1000) = false := by cases tier <;> decide
    simp only [ScaleSpec.validate, beq_false_of_ne (show maxI ≠ 0 by omega), decide_eq_false (show ¬ minI > maxI by omega),
      hmem, hcpu, hminC, hminM, hlt1k, beq_false_of_ne (show conc ≠ 0 by omega), decide_eq_false (show ¬ conc > 1000 by omega),
      beq_false_of_ne (show t ≠ 0 by omega), decide_eq_false (show ¬ t > 3600 by omega), Bool.false_and, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  exact htier _ _ _ _ _ (by split <;> split <;> omega) (by split <;> omega) (by decide)
    (by cases ht : spec.timeoutSec? with | none => cases (m.server?.map fun s => !s.channels.isEmpty).getD false <;> decide | some t => simpa [ht] using hto t ht)
end ScaleTheorems

theorem planPreviewTeardown_noop_on_prod (live : GcpObservedState) (hprod : live.key.env = .prod) : planPreviewTeardown live = [] := by simp [planPreviewTeardown, hprod, EnvInstance.isPreview]
private theorem planPreviewTeardown_mem_spec {live : GcpObservedState} {a : GcpAction} (ha : a ∈ planPreviewTeardown live) :
    a.targetKey.env.isProd = false ∧ ∀ b, a = .revokeBinding b → b.resource.isAsset = false := by
  unfold planPreviewTeardown at ha; split at ha; (simp at ha)
  rename_i hnot; have hnotProd : live.key.env.isProd = false := isPreview_imp_not_isProd (by simpa using hnot)
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ((⟨b, ⟨_, hfilt⟩, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | (rfl | rfl | rfl | rfl) <;> try exact ⟨hnotProd, fun _ h => by cases h⟩
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hfilt
  exact ⟨by simp [GcpAction.targetKey, GcpResource.ownerKey?_eq_some_imp_ownerKey hfilt.1, hnotProd], fun _ h => by cases h; exact hfilt.2⟩
theorem planPreviewTeardown_never_targets_prod (live : GcpObservedState) (a : GcpAction) (ha : a ∈ planPreviewTeardown live) : a.targetKey.env.isProd = false := (planPreviewTeardown_mem_spec ha).1
theorem planPreviewTeardown_never_revokes_asset (live : GcpObservedState) (b : GcpIamBinding) (ha : GcpAction.revokeBinding b ∈ planPreviewTeardown live) : b.resource.isAsset = false := (planPreviewTeardown_mem_spec ha).2 b rfl

end Qed.Cloud
