import Qed.Proofs.Hydration.View
import Qed.Proofs.ViewPatch

namespace Qed

theorem App.ssr_hydrate_patch_equiv {Model Msg : Type} (app : App Model Msg) (m m' : Model) (msg : Msg)
    (hre : app.rehydrate (app.dehydrate m) = some m') (hclean : View.DomClean app.template)
    (f : Nat) (parent root : Dom.Node) (ptag : String) (pst : SpecElemState Msg) (pmg : List String) (lo hi : Nat) (a : DomArena Msg)
    (hpar : a.get parent = .element "" ptag pst pmg [root]) (hparLo : parent.toNat < lo) (hdom : HydratableDom (f + 1) "" (app.view m) a lo hi root)
    (hbound : a.nextId + htmlNodeCount (app.view m') < UInt32.size) (hdep : htmlDepth (app.view m') ≤ f + 1)
    (hboundNext : a.nextId + htmlNodeCount (app.view m') + htmlNodeCount (app.view (app.update m' msg).1) < UInt32.size) (hdepNext : htmlDepth (app.view (app.update m' msg).1) ≤ f + 1) :
    let (vst, aHyd) := (hydrateViewM (m := StateM (DomArena Msg)) app.template m' root).run a
    let mNext := (app.update m' msg).1
    let (vst', aPatch) := (patchViewM (m := StateM (DomArena Msg)) parent 0 app.template mNext vst).run aHyd
    DomTreeAssocEquiv (readDomTree (f + 1) aHyd vst.rootNode) (specDom "" (app.view m)) ∧
    VStateValid (f + 1) "" app.template mNext aPatch (fun k => ((lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aHyd.nextId)) ∨ (aHyd.nextId ≤ k ∧ k < aPatch.nextId)) vst' ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aPatch vst'.rootNode) (specDom "" (app.view mNext)) := by
  have hview : View.render app.template m' = app.view m := app.dehydrate_view m m' hre
  have hb := HydratableDom_bounds (f + 1) "" (app.view m) a lo hi root hdom
  have ⟨hroot, haHydGe, haHydBound, haHydFr, hVstHyd, hEquivHyd⟩ := hydrateViewM_spec "" f app.template m' root a lo hi hclean hbound hdep (hview.symm ▸ hdom)
  dsimp only [StateT.run] at hroot haHydGe haHydBound haHydFr hVstHyd hEquivHyd ⊢
  have hrootLt : (hydrateViewM (m := ArenaM Msg) app.template m' root a).1.rootNode.toNat < (hydrateViewM (m := ArenaM Msg) app.template m' root a).2.nextId := by
    rcases VStateValid_root_mem hVstHyd with h1 | h2 <;> omega
  have ⟨_, _, _, _, hVstPatch, hEquivPatch⟩ := patchViewM_spec ⟨f + 1, "", parent, "", ptag, pst, pmg⟩ app.template m' (app.update m' msg).1
    [] [] (HydSet lo hi a.nextId (hydrateViewM (m := ArenaM Msg) app.template m' root a).2.nextId) _ _
    ⟨rfl, by simp only [List.length_nil]; decide, by dsimp only; omega, by omega, by rw [haHydFr parent (.inl hparLo) (by omega), hpar, hroot]; rfl, by simp,
      fun h => h.elim (fun _ => by dsimp only at *; omega) (fun _ => by dsimp only at *; omega), fun _ hk => hk.elim (fun _ => by omega) (·.2),
      fun _ hr => by simp only [List.nil_append, List.mem_singleton] at hr; exact hr ▸ hrootLt⟩
    hclean (by dsimp only [App.view] at hbound hboundNext; omega) hdepNext hVstHyd
  dsimp only [App.view] at hVstPatch hEquivPatch hview ⊢
  exact ⟨by rw [← hview, hroot]; exact hEquivHyd, hVstPatch, hEquivPatch⟩

end Qed
