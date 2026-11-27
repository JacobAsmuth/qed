import Qed.View.Core
import Lean

namespace Qed.ValidLemmas

theorem not_isVoidTag_or (tag : String) (b : Bool) (h : isVoidTag tag = false) : (!isVoidTag tag || b) = true := by rw [h]; rfl
theorem attr_nonUrl {msg : Type} (k v : String) (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) : (Attr.attr k v : Attr msg).valid = true := by simp [Attr.valid, Attr.validKeyValue, h.1, h.2]
theorem signalAttr_nonUrl {msg : Type} (n k v : String) (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) : (Attr.signalAttr n k v : Attr msg).valid = true := by simp [Attr.valid, Attr.validKeyValue, h.1, h.2]
theorem flag_safe {msg : Type} (k : String) (p : Bool) (h : isSafeAttrName k = true) : (Attr.flag k p : Attr msg).valid = true := h
theorem on_safe {msg : Type} (e : String) (m : msg) (h : isSafeAttrName e = true) : (Attr.on e m).valid = true := h
theorem signalOn_safe {msg : Type} (n e : String) (m : msg) (h : isSafeAttrName e = true) : (Attr.signalOn n e m).valid = true := h
theorem onValue_safe {msg : Type} (e : String) (f : String → msg) (h : isSafeAttrName e = true) : (Attr.onValue e f).valid = true := h
theorem valid_attr_nonUrl {msg α : Type} [ToString α] (k : String) (v : α) (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) : (Qed.attr k v : Attr msg).valid = true := attr_nonUrl k (toString v) h

private theorem dite_eq_intro {α β : Type} (f : α → β) (v : β) (c : Prop) [Decidable c]
    (a : c → α) (b : ¬c → α) (ha : ∀ h, f (a h) = v) (hb : ∀ h, f (b h) = v) : f (dite c a b) = v := by by_cases h : c <;> simp [h, ha, hb]
theorem attr_valid_dite_intro {msg : Type} (c : Prop) [Decidable c] (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).valid = true) (hb : ∀ h, (b h).valid = true) : (dite c a b).valid = true := dite_eq_intro Attr.valid true c a b ha hb
theorem attr_isLocalCell_dite_eq_false {msg : Type} (c : Prop) [Decidable c] (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).isLocalCell = false) (hb : ∀ h, (b h).isLocalCell = false) : (dite c a b).isLocalCell = false := dite_eq_intro Attr.isLocalCell false c a b ha hb
theorem validListIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a : c → List (Html msg)) (b : ¬c → List (Html msg))
    (ha : ∀ h, Html.validListIn ctx (a h) = true) (hb : ∀ h, Html.validListIn ctx (b h) = true) : Html.validListIn ctx (dite c a b) = true := dite_eq_intro (Html.validListIn ctx) true c a b ha hb

private theorem mk_nv (t : String) (h : isVoidTagFast t = false) : isVoidTag t = false := congrFun isVoidTag_eq_fast t ▸ h
private theorem bool_guard_false : ∀ {x req bad : Bool}, (x && !req) = false → (!req || !bad) = true → (x && bad) = false
  | false, _, _, _, _ | true, _, false, _, _ => rfl | true, true, true, _, h | true, false, true, h, _ => nomatch h
private theorem eq_false_of_sz_ne {t s : String} (h : (t.utf8ByteSize == s.utf8ByteSize) = false) : (t == s) = false := beq_eq_false_iff_ne.2 fun heq => by subst heq; simp at h
private def tagEqSz (n : Nat) (s t : String) : Bool := t.utf8ByteSize == n && t == s
private theorem tagEqSz_eq (n : Nat) (s : String) (hn : s.utf8ByteSize = n) (t : String) : tagEqSz n s t = (t == s) := by
  unfold tagEqSz; cases hsz : (t.utf8ByteSize == n)
  · rw [Bool.false_and, eq_false_of_sz_ne (hn ▸ hsz)]
  · rfl

private def normalStepTagOk (t : String) (m2 : TagMode) (reqNoCloseP reqNonInter wantHead wantInter : Bool) : Bool :=
  isSafeTagBytes t && !isForbiddenTag t && !isContextOnlyTag t &&
  !(tagEqSz 3 "svg" t || tagEqSz 5 "style" t || tagEqSz 2 "dl" t || tagEqSz 4 "form" t) &&
  (!reqNoCloseP || !closesPTag t) && (!reqNonInter || !(isInteractiveTag t || tagEqSz 5 "label" t)) &&
  if m2 == .normal then
    !(tagEqSz 8 "textarea" t || tagEqSz 6 "select" t || tagEqSz 2 "ul" t || tagEqSz 2 "ol" t || tagEqSz 5 "table" t) &&
    ((tagEqSz 1 "p" t || isHeadingTag t) == wantHead) &&
    ((tagEqSz 1 "a" t || tagEqSz 6 "button" t || tagEqSz 7 "details" t || tagEqSz 7 "summary" t) == wantInter)
  else
    !wantHead &&
    (if tagEqSz 8 "textarea" t then m2 == .textarea && wantInter
     else if tagEqSz 6 "select" t then m2 == .select && wantInter
     else if tagEqSz 2 "ul" t || tagEqSz 2 "ol" t then m2 == .ulOl && !wantInter
     else if tagEqSz 5 "table" t then m2 == .table && !wantInter else false)

private theorem mk_normalStep (t : String) (m2 : TagMode) (reqNoCloseP reqNonInter wantHead wantInter : Bool)
    (h : normalStepTagOk t m2 reqNoCloseP reqNonInter wantHead wantInter = true)
    (p i f p' i' : Bool) (hp : (p && !reqNoCloseP) = false) (hi : (i && !reqNonInter) = false)
    (hp' : (p || wantHead) = p') (hi' : (i || wantInter) = i') :
    stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } t = some { mode := m2, inP := p', interactive := i', inForm := f } := by
  simp only [normalStepTagOk, tagEqSz_eq 3 "svg" rfl, tagEqSz_eq 5 "style" rfl, tagEqSz_eq 2 "dl" rfl, tagEqSz_eq 4 "form" rfl,
    tagEqSz_eq 5 "label" rfl, tagEqSz_eq 8 "textarea" rfl, tagEqSz_eq 6 "select" rfl, tagEqSz_eq 2 "ul" rfl, tagEqSz_eq 2 "ol" rfl,
    tagEqSz_eq 5 "table" rfl, tagEqSz_eq 1 "p" rfl, tagEqSz_eq 1 "a" rfl, tagEqSz_eq 6 "button" rfl, tagEqSz_eq 7 "details" rfl,
    tagEqSz_eq 7 "summary" rfl, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hsB, hfb⟩, hc⟩, hsp⟩, hcp⟩, hni⟩, hm⟩
  have hs := isSafeTagName_of_bytes t hsB
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hfb hc hsp; rcases hsp with ⟨⟨⟨hsvg, hsty⟩, hdl⟩, hfrm⟩
  have hp0 : (p && closesPTag t) = false := bool_guard_false hp hcp
  have hi0 : (i && (isInteractiveTag t || t == "label")) = false := bool_guard_false hi hni
  simp only [stepHtmlCtx, hs, hfb, hc, hp0, hfrm, Bool.or_false, hi0, hsvg, hsty, hdl, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  split at hm
  · rename_i hmN; cases beq_iff_eq.1 hmN
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_iff_eq] at hm
    rcases hm with ⟨⟨⟨⟨⟨⟨hta, hsel⟩, hul⟩, hol⟩, htbl⟩, hhd⟩, hint⟩
    have hP : (p || t == "p" || isHeadingTag t) = p' := by rw [Bool.or_assoc, hhd, hp']
    have hI : (i || t == "a" || t == "button" || t == "details" || t == "summary") = i' := by simp only [Bool.or_assoc] at hint ⊢; rw [hint, hi']
    simp only [hta, hsel, hul, hol, htbl, hP, hI, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm; rcases hm with ⟨rfl, hstep⟩; simp only [Bool.or_false] at hp'; subst hp'
    repeat (split at hstep <;> first
      | (simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hstep; rcases hstep with ⟨rfl, rfl⟩
         simp only [*, Bool.or_true, Bool.or_false, ↓reduceIte] at hi' ⊢; subst hi'; rfl)
      | simp only [*, ↓reduceIte])
    cases hstep

private theorem mk_modeStep (m1 m2 : TagMode) (tag : String) (resetP : Bool)
    (hsB : isSafeTagBytes tag = true) (hf : isForbiddenTag tag = false)
    (hstep : (match m1 with
      | .ulOl => if tag == "li" then some (TagMode.normal, true) else none
      | .table => if tag == "caption" then some (TagMode.normal, true) else if tag == "colgroup" then some (TagMode.colgroup, true)
                  else if tag == "thead" || tag == "tbody" || tag == "tfoot" then some (TagMode.tableSection, true) else none
      | .tableSection => if tag == "tr" then some (TagMode.tableRow, true) else none
      | .tableRow => if tag == "td" || tag == "th" then some (TagMode.normal, true) else none
      | .select => if tag == "option" then some (TagMode.option, false) else none | _ => none) = some (m2, resetP)) (p i f : Bool) :
    stepHtmlCtx { mode := m1, inP := p, interactive := i, inForm := f } tag = some { mode := m2, inP := if resetP then false else p, interactive := i, inForm := f } := by
  have hs := isSafeTagName_of_bytes tag hsB
  cases m1 with
  | ulOl | tableSection | tableRow | select | table =>
      simp only [stepHtmlCtx, hs, hf, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
      repeat (split at hstep <;> first | (simp only [*, ↓reduceIte]; cases hstep; rfl) | simp only [*])
      cases hstep
  | _ => cases hstep

private def camelValidName (pfx s : String) : String :=
  match s.splitOn "-" with
  | [] => pfx | h :: t => pfx ++ h ++ String.join (t.map fun p => match p.toList with | [] => "" | c :: cs => String.ofList (c.toUpper :: cs))
private def validThmName (pfx s : String) : Lean.Name := .str (.str (.str .anonymous "Qed") "ValidLemmas") (camelValidName pfx s)
private def modeStepInfo : String → TagMode × TagMode × Bool
  | "li" => (.ulOl, .normal, true) | "thead" | "tbody" => (.table, .tableSection, true)
  | "tr" => (.tableSection, .tableRow, true) | "option" => (.select, .option, false) | _ => (.tableRow, .normal, true)
private def tagModeConst : TagMode → Lean.Name
  | .normal => ``TagMode.normal | .ulOl => ``TagMode.ulOl | .table => ``TagMode.table | .tableSection => ``TagMode.tableSection
  | .tableRow => ``TagMode.tableRow | .select => ``TagMode.select | .option => ``TagMode.option | .textarea => ``TagMode.textarea | _ => ``TagMode.normal

private def snuRaw : String := "data-role data-qed-link value placeholder name alt title style type class id for role aria-label aria-invalid aria-live rows cols min max step tabindex target rel accept autocomplete"
private def saRaw : String := "click input change keydown keyup submit blur focus dblclick mousedown mouseup disabled required checked readonly selected multiple hidden"
private def blockRaw : String := "div section article aside header footer main nav blockquote pre fieldset figure figcaption hr"
private def headingRaw : String := "p h1 h2 h3 h4 h5 h6"
private def modeBlockRaw : String := "ul ol table"
private def inlineRaw : String := "span strong em code small b i u s mark time kbd img br legend"
private def interRaw : String := "button a summary"
private def inputRaw : String := "input label"
private def modeInterRaw : String := "textarea select"
private def modeStepRaw : String := "li thead tbody tr td th option"
private def nvRaw : String := "div span p a button form label ul ol li h1 h2 h3 h4 h5 h6 section article aside header footer main nav blockquote pre code strong em small b i u s mark time kbd table thead tbody tr td th select option textarea fieldset legend figure figcaption summary"

section GenValid
open Lean Elab Command

@[noinline] private def forWords (raw : String) (f : String → CommandElabM Unit) : CommandElabM Unit :=
  let rec go : List String → CommandElabM Unit | [] => pure () | s :: ss => do f s; go ss
  go (raw.splitOn " ")

@[noinline] private def emitValidThms : CommandElabM Unit := do
  let boolT := mkConst ``Bool; let bT := mkConst ``Bool.true; let bF := mkConst ``Bool.false
  let bE (b : Bool) := if b then bT else bF
  let eqB (l r : Expr) := mkApp3 (mkConst ``Eq [Level.one]) boolT l r
  let rflB (b : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) boolT b
  let addT (pfx s : String) (type value : Expr) : CommandElabM Unit := liftCoreM (addDecl (.thmDecl { name := validThmName pfx s, levelParams := [], type, value }))
  forWords snuRaw fun s => let se := mkStrLit s; let t1 := eqB (mkApp (mkConst ``Qed.isSafeAttrName) se) bT; let t2 := eqB (mkApp (mkConst ``Qed.isUrlAttrName) se) bF
    addT "snu_" s (mkApp2 (mkConst ``And) t1 t2) (mkApp4 (mkConst ``And.intro) t1 t2 (mkApp2 (mkConst ``Qed.isSafeAttrName_of_bytes) se (rflB bT)) (rflB bF))
  forWords saRaw fun s => let se := mkStrLit s; addT "sa_" s (eqB (mkApp (mkConst ``Qed.isSafeAttrName) se) bT) (mkApp2 (mkConst ``Qed.isSafeAttrName_of_bytes) se (rflB bT))
  forWords nvRaw fun s => let se := mkStrLit s; addT "nv_" s (eqB (mkApp (mkConst ``Qed.isVoidTag) se) bF) (mkApp2 (mkConst ``mk_nv) se (rflB bF))
  let optCtxT := mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx)
  let mkStepTy (m1 m2 : TagMode) (pIn iIn pOut iOut fE se : Expr) :=
    mkApp3 (mkConst ``Eq [Level.one]) optCtxT (mkApp2 (mkConst ``Qed.stepHtmlCtx) (mkApp4 (mkConst ``HtmlCtx.mk) (mkConst (tagModeConst m1)) pIn iIn fE) se)
      (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) (mkApp4 (mkConst ``HtmlCtx.mk) (mkConst (tagModeConst m2)) pOut iOut fE))
  let wrap (pVar iVar isTy : Bool) (e : Expr) : Expr :=
    let mk1 (n : Name) (b : Expr) := if isTy then Expr.forallE n boolT b .default else Expr.lam n boolT b .default
    let e2 := if iVar then mk1 `i (mk1 `f e) else mk1 `f e
    if pVar then mk1 `p e2 else e2
  let addNormal (pVar iVar wHead wInter : Bool) (m2Of : String → TagMode) (raw : String) : CommandElabM Unit :=
    forWords raw fun s => do
      let se := mkStrLit s; let m2 := m2Of s; let fE := mkBVar 0; let iE := if iVar then mkBVar 1 else bF
      let pE := if pVar then mkBVar (if iVar then 2 else 1) else bF
      let pOut := if pVar then pE else bE wHead; let iOut := if iVar then iE else bE wInter
      let optPf (flag : Bool) (lem : Name) (v dflt : Expr) := if flag then mkApp (mkConst lem) v else rflB dflt
      let bodyTy := mkStepTy .normal m2 pE iE pOut iOut fE se
      let bodyPf := mkAppN (mkConst ``mk_normalStep) #[se, mkConst (tagModeConst m2), bE pVar, bE iVar, bE wHead, bE wInter, rflB bT, pE, iE, fE, pOut, iOut,
        optPf pVar ``Bool.and_false pE bF, optPf iVar ``Bool.and_false iE bF, optPf pVar ``Bool.or_false pE (bE wHead), optPf iVar ``Bool.or_false iE (bE wInter)]
      addT "step_" s (wrap pVar iVar true bodyTy) (wrap pVar iVar false bodyPf)
  addNormal false true false false (fun _ => .normal) blockRaw
  addNormal false true true false (fun _ => .normal) headingRaw
  addNormal false true false false (fun s => if s == "table" then .table else .ulOl) modeBlockRaw
  addNormal true true false false (fun _ => .normal) inlineRaw
  addNormal true false false true (fun _ => .normal) interRaw
  addNormal true false false false (fun _ => .normal) inputRaw
  addNormal true false false true (fun s => if s == "select" then .select else .textarea) modeInterRaw
  let prodM := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``TagMode) boolT
  forWords modeStepRaw fun s => do
    let se := mkStrLit s; let (m1, m2, rst) := modeStepInfo s; let (pE, iE, fE) := (mkBVar 2, mkBVar 1, mkBVar 0)
    let rflOpt := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkApp (mkConst ``Option [Level.zero]) prodM)
      (mkApp2 (mkConst ``Option.some [Level.zero]) prodM (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``TagMode) boolT (mkConst (tagModeConst m2)) (bE rst)))
    addT "step_" s (wrap true true true (mkStepTy m1 m2 pE iE (if rst then bF else pE) iE fE se))
      (wrap true true false (mkAppN (mkConst ``mk_modeStep) #[mkConst (tagModeConst m1), mkConst (tagModeConst m2), se, bE rst, rflB bT, rflB bF, rflOpt, pE, iE, fE]))

local elab "#genValidLemmas" : command => emitValidThms
#genValidLemmas
end GenValid

theorem valid_value {msg α : Type} [ToString α] (v : α) : (Qed.value v : Attr msg).valid = true := attr_nonUrl "value" (toString v) snu_value
theorem valid_onCheck {msg : Type} (f : Bool → msg) : (Qed.onCheck f).valid = true := sa_change
theorem valid_vOnCheck {σ msg : Type} (s : σ) (f : σ → Bool → msg) : (VAttr.eval s (V.onCheck' f)).valid = true := sa_change
theorem step_form : stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
    some { mode := .normal, inP := false, interactive := false, inForm := true } := rfl

private def mkNameMap (pfx raw : String) : Std.HashMap String Lean.Name :=
  (raw.splitOn " ").foldl (fun m s => m.insert s (validThmName pfx s)) {}

def safeNonUrlAttrMap : Std.HashMap String Lean.Name := mkNameMap "snu_" snuRaw
def safeAttrMap : Std.HashMap String Lean.Name := mkNameMap "sa_" saRaw
private def stepBlockMap : Std.HashMap String Lean.Name := mkNameMap "step_" (blockRaw ++ " " ++ headingRaw ++ " " ++ modeBlockRaw)
def stepInlineMap : Std.HashMap String Lean.Name := mkNameMap "step_" inlineRaw
private def stepNonInterMap : Std.HashMap String Lean.Name := mkNameMap "step_" (interRaw ++ " " ++ inputRaw ++ " " ++ modeInterRaw)
private def stepModeMap : Std.HashMap (Nat × String) Lean.Name := (modeStepRaw.splitOn " ").foldl (fun m s => m.insert ((modeStepInfo s).1.ctorIdx, s) (validThmName "step_" s)) {}
def nonVoidTagMap : Std.HashMap String Lean.Name := mkNameMap "nv_" nvRaw

open Lean

def strLitVal? (e : Expr) : Option String := match e.consumeMData with | .lit (.strVal s) => some s | _ => none

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let (bP, bI, bF) := (toExpr ctxV.inP, toExpr ctxV.interactive, toExpr ctxV.inForm)
  let rflStep := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
    (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) childCtxE)
  match ctxV.mode with
  | .normal =>
      if let some lm := if !ctxV.inP then stepBlockMap[tagS]? else none then mkApp2 (mkConst lm) bI bF
      else if !ctxV.inP && !ctxV.interactive && !ctxV.inForm && tagS == "form" then mkConst ``step_form
      else if let some lm := if !ctxV.interactive then stepNonInterMap[tagS]? else none then mkApp2 (mkConst lm) bP bF
      else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
      else rflStep
  | m => (stepModeMap[(m.ctorIdx, tagS)]?.map fun lm => mkApp3 (mkConst lm) bP bI bF).getD rflStep

def qedAttrWrapperMap : Std.HashMap Name (Name × String × Name) :=
  let add (comb : Name) (tbl : Std.HashMap String Name) (ps : Array (Name × String)) (m : Std.HashMap Name (Name × String × Name)) :=
    ps.foldl (fun m (fn, key) => match tbl[key]? with | some lm => m.insert fn (comb, key, lm) | none => m) m
  {} |> add ``attr_nonUrl safeNonUrlAttrMap #[(``Qed.role, "data-role"), (``Qed.placeholder, "placeholder"), (``Qed.name, "name"),
          (``Qed.alt, "alt"), (``Qed.title, "title"), (``Qed.style, "style"), (``Qed.type', "type")]
     |> add ``on_safe safeAttrMap #[(``Qed.onClick, "click"), (``Qed.onSubmit, "submit"), (``Qed.onBlur, "blur"), (``Qed.onFocus, "focus"),
          (``Qed.onDoubleClick, "dblclick"), (``Qed.onMouseDown, "mousedown"), (``Qed.onMouseUp, "mouseup")]
     |> add ``onValue_safe safeAttrMap #[(``Qed.onInput, "input"), (``Qed.onChange, "input"), (``Qed.onKeydown, "keydown"), (``Qed.onKeyup, "keyup")]
     |> add ``flag_safe safeAttrMap #[(``Qed.disabled, "disabled"), (``Qed.required, "required"), (``Qed.checked, "checked"), (``Qed.readOnly, "readonly")]

private def fastAttrCtorMap : Std.HashMap Name (Nat × Nat × Bool × Name) :=
  #[(``Attr.attr, (3, 1, true, ``attr_nonUrl)), (``Attr.signalAttr, (4, 2, true, ``signalAttr_nonUrl)),
    (``Attr.flag, (3, 1, false, ``flag_safe)), (``Attr.on, (3, 1, false, ``on_safe)),
    (``Attr.signalOn, (4, 2, false, ``signalOn_safe)), (``Attr.onValue, (3, 1, false, ``onValue_safe))].foldl (fun m (k, v) => m.insert k v) {}

def fastAttrValidProof? (msgTy a : Expr) : Option Expr :=
  let a := a.consumeMData; let args := a.getAppArgs
  a.getAppFn.constName?.bind fun fn => match fn, args.size with
    | ``VAttr.eval, 4 =>
        let va := args[3]!.consumeMData
        if va.getAppFn.constName? == some ``V.onCheck' && va.getAppArgs.size == 3 then
          some (mkApp4 (mkConst ``valid_vOnCheck) args[0]! args[1]! args[2]! va.getAppArgs[2]!)
        else none
    | ``Qed.value, 4 => some (mkApp4 (mkConst ``valid_value) args[0]! args[1]! args[2]! args[3]!)
    | ``Qed.onCheck, 2 => some (mkApp2 (mkConst ``valid_onCheck) args[0]! args[1]!)
    | ``Qed.attr, 5 => (strLitVal? args[3]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
        mkAppN (mkConst ``valid_attr_nonUrl) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, mkConst lem]
    | _, 2 => qedAttrWrapperMap[fn]?.map fun (comb, key, lem) => mkApp4 (mkConst comb) msgTy (toExpr key) args[1]! (mkConst lem)
    | _, sz => fastAttrCtorMap[fn]?.bind fun (arity, keyIdx, nonUrl, thm) =>
        if sz != arity then none else (strLitVal? args[keyIdx]! >>= ((if nonUrl then safeNonUrlAttrMap else safeAttrMap)[·]?)).map fun lem =>
          mkAppN (mkConst thm) (#[msgTy] ++ args.extract 1 arity ++ #[mkConst lem])

end Qed.ValidLemmas
