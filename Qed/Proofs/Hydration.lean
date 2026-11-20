import Qed.Proofs.Hydration.View
import Qed.Proofs.ViewPatch

namespace Qed

theorem App.ssr_hydrate_patch_equiv {Model Msg : Type} (app : App Model Msg)
    (m m' : Model) (msg : Msg)
    (hre : app.rehydrate (app.dehydrate m) = some m')
    (hclean : View.DomClean app.template)
    (f : Nat) (parent root : Dom.Node) (ptag : String) (pst : SpecElemState Msg) (pmg : List String)
    (lo hi : Nat) (a : DomArena Msg)
    (hpar : a.get parent = .element "" ptag pst pmg [root])
    (hparLo : parent.toNat < lo)
    (hdom : HydratableDom (f + 1) "" (app.view m) a lo hi root)
    (hbound : a.nextId + htmlNodeCount (app.view m') < UInt32.size)
    (hdep : htmlDepth (app.view m') ≤ f + 1)
    (hboundNext : a.nextId + htmlNodeCount (app.view m') + htmlNodeCount (app.view (app.update m' msg).1) < UInt32.size)
    (hdepNext : htmlDepth (app.view (app.update m' msg).1) ≤ f + 1) :
    let (vst, aHyd) := (hydrateViewM (m := StateM (DomArena Msg)) app.template m' root).run a
    let mNext := (app.update m' msg).1
    let (vst', aPatch) := (patchViewM (m := StateM (DomArena Msg)) parent 0 app.template mNext vst).run aHyd
    DomTreeAssocEquiv (readDomTree (f + 1) aHyd vst.rootNode) (specDom "" (app.view m)) ∧
    VStateValid (f + 1) "" app.template mNext aPatch
      (fun k => ((lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aHyd.nextId)) ∨ (aHyd.nextId ≤ k ∧ k < aPatch.nextId)) vst' ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aPatch vst'.rootNode) (specDom "" (app.view mNext)) := by
  have hview : app.view m' = app.view m := app.dehydrate_view m m' hre
  have hb := HydratableDom_bounds (f + 1) "" (app.view m) a lo hi root hdom
  have hdom' : HydratableDom (f + 1) "" (View.render app.template m') a lo hi root := by
    change HydratableDom (f + 1) "" (app.view m') a lo hi root; rw [hview]; exact hdom
  have hhyd := hydrateViewM_spec "" f app.template m' root a lo hi hclean hbound hdep hdom'
  dsimp only [StateT.run] at hhyd ⊢
  cases hH : hydrateViewM (m := StateM (DomArena Msg)) app.template m' root a with
  | mk vst aHyd =>
      rw [hH] at hhyd; dsimp only at hhyd ⊢
      rcases hhyd with ⟨hroot, haHydGe, haHydBound, haHydFr, hVstHyd, hEquivHyd⟩
      let S_hyd : Nat → Prop := fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aHyd.nextId)
      have hparHyd : aHyd.get parent = .element "" ptag pst pmg ([] ++ vst.rootNode :: []) := by
        rw [haHydFr parent (.inl hparLo) (by omega), hpar, hroot]; rfl
      have hbNext : aHyd.nextId + htmlNodeCount (View.render app.template (app.update m' msg).1) < UInt32.size := by
        dsimp only [App.view] at hbound hboundNext; omega
      have hrootLt : vst.rootNode.toNat < aHyd.nextId := by
        rcases VStateValid_root_mem hVstHyd with h1 | h2 <;> omega
      have hpatch := patchViewM_spec (f + 1) "" parent "" ptag pst pmg app.template m' (app.update m' msg).1
        [] [] S_hyd aHyd vst rfl hclean (by simp only [List.length_nil]; decide) hbNext
        (by simpa [App.view] using hdepNext) (by omega) (by omega) hparHyd (by simp)
        (fun h => h.elim (fun h1 => by omega) (fun h2 => by omega))
        (fun k hk => hk.elim (fun h1 => by omega) (fun h2 => h2.2))
        (fun r hr => by simp only [List.nil_append, List.mem_singleton] at hr; exact hr ▸ hrootLt)
        hVstHyd
      dsimp only [StateT.run] at hpatch
      have h0 : (UInt32.ofNat ([] : List Dom.Node).length) = 0 := rfl
      rw [h0] at hpatch
      cases hP : patchViewM (m := StateM (DomArena Msg)) parent 0 app.template (app.update m' msg).1 vst aHyd with
      | mk vst' aPatch =>
          rw [hP] at hpatch; dsimp only [App.view] at hpatch ⊢
          rcases hpatch with ⟨_, _, _, _, _, _, hVstP, hEquivP⟩
          dsimp only [App.view] at hview
          exact ⟨by rw [← hview]; simpa [hroot] using hEquivHyd, by simpa [S_hyd] using hVstP, hEquivP⟩

end Qed
