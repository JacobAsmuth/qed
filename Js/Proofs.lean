import Js.Proofs.SimIJ
import Js.Proofs.SimJI

namespace Js.Proofs
open Lean IR

theorem lowerBody_equiv (prog : IrProg) (c0 c : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName)
    (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (b : FnBody) (irSt : IrState) (jsSt : JsState) (hnames : c.names = c0.names) (hmin : c.min = c0.min) (henv : c.env = c0.env)
    (hself : ∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup)
    (hwf : BodyWf c prog inlineJps recJps allowTailCont b) (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) :
    (∀ fuel irO irSt1, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt b = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1) ∧
    (∀ fuel ex jsSt1, evalJsStmts jsProg fuel jsSt (lowerBody c b) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1) :=
  ⟨fun fuel _ _ h => (eval_sim_ir_to_js ⟨prog, c0, jsProg, revName⟩ hprog fuel).2.2 ⟨c, inlineJps, recJps, allowTailCont⟩ b irSt jsSt _ _ ⟨hnames, hmin, henv, hself⟩ hwf hsm h,
   fun fuel _ _ h => (eval_sim_js_to_ir ⟨prog, c0, jsProg, revName⟩ hprog fuel).2.2 ⟨c, inlineJps, recJps, allowTailCont⟩ b irSt jsSt _ _ ⟨hnames, hmin, henv, hself⟩ hwf hsm h⟩

theorem lowerDecl_equiv (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName)
    (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (f : Name) (args : List JsVal) (jsSt : JsState)
    (hf : prog f ≠ none) (hhp : h = jsSt.heap) (hmEq : ∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) (hmNo : ∀ g, (mIr g).val.elim True JsVal.noTc)
    (hargs : ∀ a ∈ args, a.noTc) (hfns : ∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) :
    (∀ fuel v h1 m1, evalIrCall prog c0 revName fuel h mIr f args = some (v, h1, m1) → ∃ fJs st2, evalJsCall jsProg fJs jsSt (c0.js f) args = some (v, st2) ∧ CallPost prog c0 v v h1 m1 jsSt st2) ∧
    (∀ fuel v st2, evalJsCall jsProg fuel jsSt (c0.js f) args = some (v, st2) → ∃ fIr h1 m1, evalIrCall prog c0 revName fIr h mIr f args = some (v, h1, m1) ∧ CallPost prog c0 v v h1 m1 jsSt st2) :=
  ⟨fun fuel _ _ _ hir => (eval_sim_ir_to_js ⟨prog, c0, jsProg, revName⟩ hprog fuel).1 h mIr f args jsSt _ _ _ hf hhp hmEq hmNo hargs hfns hir,
   fun fuel _ _ hjs => (eval_sim_js_to_ir ⟨prog, c0, jsProg, revName⟩ hprog fuel).1 h mIr f args jsSt _ _ hf hhp hmEq hmNo hargs hfns hjs⟩

theorem projTransfer_prefix_equiv (root cont : FnBody) (x : VarId) (p n id : Nat)
    (hsrc : (collectProjSrc {} {} root).get? x.idx = some p) (hdec : hasDecOf p cont = true) (hn : n ≥ 1) (ρ : Nat → RcVal) (hcon : NonArrConsistent ρ root) (h : CowHeap α) :
    ((collectNonArr {} root).contains p = true) ∧ DropsVar p cont ∧ (∀ m, h.rcInc (ρ p) m = h ∧ h.rcDec (ρ p) m = h) ∧
    (∀ k : Nat, (h.jsTransferInc id n).get k = ((h.rcInc (.arr id) n).rcDec (.arr id) 1).get k) :=
  ⟨collectProjSrc_subset_collectNonArr root x.idx p hsrc, hasDecOf_sound p cont hdec,
   fun m => collectNonArr_sound root ρ hcon ⟨p⟩ (collectProjSrc_subset_collectNonArr root x.idx p hsrc) h m, projRefTransfer_cowHeap_equiv h id n hn⟩

end Js.Proofs
