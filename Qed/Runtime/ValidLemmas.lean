import Qed.View.Core
import Lean

/-! ## Pre-proved O(1) HTML Validity Lemmas
Eliminates per-component UTF-8 `String` kernel reduction for common HTML5 tags and attributes. -/

namespace Qed.ValidLemmas

theorem not_isVoidTag_or (tag : String) (b : Bool) (h : isVoidTag tag = false) :
    (!isVoidTag tag || b) = true := by rw [h]; rfl

theorem attr_nonUrl {msg : Type} (k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.attr k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem signalAttr_nonUrl {msg : Type} (n k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.signalAttr n k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem flag_safe {msg : Type} (k : String) (p : Bool) (h : isSafeAttrName k = true) :
    (Attr.flag k p : Attr msg).valid = true := h

theorem on_safe {msg : Type} (e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.on e m).valid = true := h

theorem signalOn_safe {msg : Type} (n e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.signalOn n e m).valid = true := h

theorem onValue_safe {msg : Type} (e : String) (f : String → msg) (h : isSafeAttrName e = true) :
    (Attr.onValue e f).valid = true := h

theorem valid_attr_nonUrl {msg α : Type} [ToString α] (k : String) (v : α)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Qed.attr k v : Attr msg).valid = true :=
  attr_nonUrl k (toString v) h

theorem attr_valid_dite_intro {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).valid = true) (hb : ∀ h, (b h).valid = true) :
    (dite c a b).valid = true := by
  by_cases h : c <;> simp [h, ha, hb]

theorem attr_isLocalCell_dite_eq_false {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).isLocalCell = false) (hb : ∀ h, (b h).isLocalCell = false) :
    (dite c a b).isLocalCell = false := by
  by_cases h : c <;> simp [h, ha, hb]

theorem validListIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a : c → List (Html msg)) (b : ¬c → List (Html msg))
    (ha : ∀ h, Html.validListIn ctx (a h) = true) (hb : ∀ h, Html.validListIn ctx (b h) = true) :
    Html.validListIn ctx (dite c a b) = true := by
  by_cases h : c <;> simp [h, ha, hb]

private def mkMap {α β : Type} [BEq α] [Hashable α] (entries : Array (α × β)) : Std.HashMap α β :=
  entries.foldl (fun m (k, v) => m.insert k v) {}

private theorem mk_nv (t : String) (h : isVoidTagFast t = false) : isVoidTag t = false := by
  rw [isVoidTag_eq_fast]; exact h

private def normalStepTagOk (t : String) (m2 : TagMode) (reqNoCloseP reqNonInter wantHead wantInter : Bool) : Bool :=
  isSafeTagName t && !isForbiddenTag t && !isContextOnlyTag t &&
  !(t == "svg" || t == "style" || t == "dl" || t == "form") &&
  (!reqNoCloseP || !closesPTag t) && (!reqNonInter || !(isInteractiveTag t || t == "label")) &&
  if m2 == .normal then
    !(t == "textarea" || t == "select" || t == "ul" || t == "ol" || t == "table") &&
    ((t == "p" || isHeadingTag t) == wantHead) &&
    ((t == "a" || t == "button" || t == "details" || t == "summary") == wantInter)
  else
    !wantHead && ((t == "textarea" || t == "select") == wantInter) &&
    (if t == "textarea" then m2 == .textarea
     else if t == "select" then m2 == .select
     else if t == "ul" || t == "ol" then m2 == .ulOl
     else if t == "table" then m2 == .table else false)

private theorem mk_normalStep (t : String) (m2 : TagMode) (reqNoCloseP reqNonInter wantHead wantInter : Bool)
    (h : normalStepTagOk t m2 reqNoCloseP reqNonInter wantHead wantInter = true)
    (p i f p' i' : Bool)
    (hp : (p && !reqNoCloseP) = false) (hi : (i && !reqNonInter) = false)
    (hp' : (p || wantHead) = p') (hi' : (i || wantInter) = i') :
    stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } t =
      some { mode := m2, inP := p', interactive := i', inForm := f } := by
  simp only [normalStepTagOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hs, hfb⟩, hc⟩, ⟨⟨⟨hsvg, hsty⟩, hdl⟩, hfrm⟩⟩, hcp⟩, hni⟩, hm⟩
  have hp0 : (p && closesPTag t) = false := by cases p <;> cases reqNoCloseP <;> simp_all
  have hi0 : (i && (isInteractiveTag t || t == "label")) = false := by
    cases i <;> cases reqNonInter <;> simp_all
  simp only [stepHtmlCtx, hs, hfb, hc, hp0, hfrm, Bool.or_false, hi0, hsvg, hsty, hdl,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  split at hm
  · rename_i hmN; have hmN := eq_of_beq hmN; subst hmN
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_iff_eq] at hm
    rcases hm with ⟨⟨⟨⟨⟨⟨hta, hsel⟩, hul⟩, hol⟩, htbl⟩, hhd⟩, hint⟩
    have hP : (p || t == "p" || isHeadingTag t) = p' := by rw [Bool.or_assoc, hhd, hp']
    have hI : (i || t == "a" || t == "button" || t == "details" || t == "summary") = i' := by
      simp only [Bool.or_assoc] at hint ⊢; rw [hint, hi']
    simp only [hta, hsel, hul, hol, htbl, hP, hI, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
    rcases hm with ⟨⟨hwH, hwI⟩, hstep⟩
    subst hwH; simp only [Bool.or_false] at hp'; subst hp'
    cases wantInter <;> repeat (first | (simp at hstep; done) | (split at hstep <;> simp_all [Bool.or_false, Bool.or_true, Bool.or_eq_true, beq_iff_eq]))

private theorem mk_modeStep (m1 m2 : TagMode) (tag : String) (resetP : Bool)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hstep : (match m1 with
      | .ulOl => if tag == "li" then some (TagMode.normal, true) else none
      | .table => if tag == "caption" then some (TagMode.normal, true)
                  else if tag == "colgroup" then some (TagMode.colgroup, true)
                  else if tag == "thead" || tag == "tbody" || tag == "tfoot" then some (TagMode.tableSection, true)
                  else none
      | .tableSection => if tag == "tr" then some (TagMode.tableRow, true) else none
      | .tableRow => if tag == "td" || tag == "th" then some (TagMode.normal, true) else none
      | .select => if tag == "option" then some (TagMode.option, false) else none
      | _ => none) = some (m2, resetP))
    (p i f : Bool) :
    stepHtmlCtx { mode := m1, inP := p, interactive := i, inForm := f } tag =
      some { mode := m2, inP := if resetP then false else p, interactive := i, inForm := f } := by
  cases m1 <;>
    simp only [stepHtmlCtx, hs, hf, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hstep ⊢ <;>
    repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

private def camelValidName (pfx s : String) : String :=
  match s.splitOn "-" with
  | [] => pfx
  | h :: t => pfx ++ h ++ String.join (t.map fun p =>
      match p.toList with | [] => "" | c :: cs => String.ofList (c.toUpper :: cs))

private def modeStepInfo : String → Lean.Name × Lean.Name × Bool
  | "li" => (`ulOl, `normal, true) | "thead" | "tbody" => (`table, `tableSection, true)
  | "tr" => (`tableSection, `tableRow, true) | "option" => (`select, `option, false)
  | _ => (`tableRow, `normal, true)

private def genStepItem (k : String) (ref thm : Lean.Ident) (sLit : Lean.StrLit) :
    Lean.MacroM (Lean.TSyntax `command) := do
  let mk (n : String) := Lean.mkIdentFrom ref (Lean.Name.mkSimple n)
  let mkM (m : Lean.Name) := Lean.mkIdentFrom ref (``TagMode ++ m)
  let (p, i, f) := (mk "p", mk "i", mk "f")
  let (tT, tF, tRfl) : Lean.TSyntax `term × Lean.TSyntax `term × Lean.TSyntax `term := (mk "true", mk "false", mk "rfl")
  let bT (b : Bool) := if b then tT else tF
  let (m1, m2, pVar, iVar, pOut, iOut, prf) ←
    if k == "modeStep" then
      let (m1, m2, rst) := modeStepInfo sLit.getString
      let prf ← `($(mk "mk_modeStep") $(mkM m1) $(mkM m2) $sLit $(bT rst) rfl rfl rfl $p $i $f)
      pure (m1, m2, true, true, (if rst then tF else p), (i : Lean.TSyntax `term), prf)
    else
      let (pVar, iVar, wHead, wInter) ← match k with
        | "block" | "modeBlock" => pure (false, true, false, false)
        | "inter" | "modeInter" => pure (true, false, false, true)
        | "inline" => pure (true, true, false, false) | "heading" => pure (false, true, true, false)
        | "input"  => pure (true, false, false, false) | _ => Lean.Macro.throwUnsupported
      let (pIn, iIn) : Lean.TSyntax `term × Lean.TSyntax `term := (if pVar then p else tF, if iVar then i else tF)
      let (pOut, iOut) : Lean.TSyntax `term × Lean.TSyntax `term := (if pVar then p else bT wHead, if iVar then i else bT wInter)
      let hp ← if pVar then `(Bool.and_false $p) else pure tRfl
      let hi ← if iVar then `(Bool.and_false $i) else pure tRfl
      let hp' ← if pVar then `(Bool.or_false $p) else pure tRfl
      let hi' ← if iVar then `(Bool.or_false $i) else pure tRfl
      let m2 := match k, sLit.getString with
        | "modeBlock", "table" => `table | "modeBlock", _ => `ulOl
        | "modeInter", "select" => `select | "modeInter", _ => `textarea | _, _ => `normal
      let prf ← `($(mk "mk_normalStep") $sLit $(mkM m2) $(bT pVar) $(bT iVar) $(bT wHead) $(bT wInter) rfl
        $pIn $iIn $f $pOut $iOut $hp $hi $hp' $hi')
      pure (`normal, m2, pVar, iVar, pOut, iOut, prf)
  let pIn : Lean.TSyntax `term := if pVar then p else tF
  let iIn : Lean.TSyntax `term := if iVar then i else tF
  let bs : Array Lean.Ident := (if pVar then #[p] else #[]) ++ (if iVar then #[i] else #[]) ++ #[f]
  `(command| theorem $thm ($bs* : Bool) :
      stepHtmlCtx { mode := $(mkM m1), inP := $pIn, interactive := $iIn, inForm := $f } $sLit =
        some { mode := $(mkM m2), inP := $pOut, interactive := $iOut, inForm := $f } := $prf)

local macro "genValidTable " kind:ident mapDef:ident " [" keys:str,* "]" : command => do
  let mut cmds := #[]; let mut entries : Array (Lean.TSyntax `term) := #[]
  let k := kind.getId.eraseMacroScopes.toString
  let pfx := match k with | "snu" => "snu_" | "sa" => "sa_" | "nv" => "nv_" | _ => "step_"
  for sLit in keys.getElems do
    let thmStr := camelValidName pfx sLit.getString
    let thm := Lean.mkIdentFrom sLit (Lean.Name.mkSimple thmStr)
    let fullName := Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkSimple "Qed") "ValidLemmas") thmStr
    let entry ← if k == "modeStep" then
        `(((($(Lean.mkIdentFrom kind (``TagMode ++ (modeStepInfo sLit.getString).1))).ctorIdx, $sLit), $(Lean.quote fullName)))
      else `(($sLit, $(Lean.quote fullName)))
    let cmd ← match k with
      | "snu" => `(command| theorem $thm : isSafeAttrName $sLit = true ∧ isUrlAttrName $sLit = false := ⟨rfl, rfl⟩)
      | "sa"  => `(command| theorem $thm : isSafeAttrName $sLit = true := rfl)
      | "nv"  => `(command| theorem $thm : isVoidTag $sLit = false := $(Lean.mkIdentFrom kind `mk_nv) $sLit rfl)
      | _     => genStepItem k kind thm sLit
    entries := entries.push entry; cmds := cmds.push cmd
  let defCmd ←
    if k == "snu" || k == "sa" || k == "nv" || k == "inline" then
      `(command| def $mapDef : Std.HashMap String Lean.Name := mkMap #[$entries,*])
    else if k == "modeStep" then
      `(command| private def $mapDef : Std.HashMap (Nat × String) Lean.Name := mkMap #[$entries,*])
    else
      `(command| private def $mapDef : Array (String × Lean.Name) := #[$entries,*])
  return ⟨Lean.mkNullNode (cmds.push defCmd)⟩

genValidTable snu safeNonUrlAttrMap [
  "data-role", "data-qed-link", "value", "placeholder", "name", "alt", "title", "style", "type",
  "class", "id", "for", "role", "aria-label", "aria-invalid", "aria-live", "rows", "cols",
  "min", "max", "step", "tabindex", "target", "rel", "accept", "autocomplete"]

genValidTable sa safeAttrMap [
  "click", "input", "change", "keydown", "keyup", "submit", "blur", "focus", "dblclick",
  "mousedown", "mouseup", "disabled", "required", "checked", "readonly", "selected", "multiple", "hidden"]

theorem valid_value {msg α : Type} [ToString α] (v : α) : (Qed.value v : Attr msg).valid = true :=
  attr_nonUrl "value" (toString v) snu_value
theorem valid_onCheck {msg : Type} (f : Bool → msg) : (Qed.onCheck f).valid = true := sa_change
theorem valid_vOnCheck {σ msg : Type} (s : σ) (f : σ → Bool → msg) :
    (VAttr.eval s (V.onCheck' f)).valid = true := sa_change

genValidTable block stepPlainBlockEntries [
  "div", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "fieldset", "figure", "figcaption", "hr"]

genValidTable inline stepInlineMap [
  "span", "strong", "em", "code", "small", "b", "i", "u", "s", "mark", "time", "kbd", "img", "br", "legend"]

genValidTable heading stepHeadingEntries ["p", "h1", "h2", "h3", "h4", "h5", "h6"]
genValidTable inter stepInterEntries ["button", "a", "summary"]
genValidTable input stepInputEntries ["input", "label"]

theorem step_form :
    stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
      some { mode := .normal, inP := false, interactive := false, inForm := true } := rfl

genValidTable modeBlock stepModeBlockEntries ["ul", "ol", "table"]
genValidTable modeInter stepModeInterEntries ["textarea", "select"]
genValidTable modeStep stepModeMap ["li", "thead", "tbody", "tr", "td", "th", "option"]

genValidTable nv nonVoidTagMap [
  "div", "span", "p", "a", "button", "form", "label", "ul", "ol", "li",
  "h1", "h2", "h3", "h4", "h5", "h6", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "code", "strong", "em", "small", "b", "i", "u", "s", "mark", "time", "kbd",
  "table", "thead", "tbody", "tr", "td", "th", "select", "option", "textarea", "fieldset", "legend",
  "figure", "figcaption", "summary"]

open Lean

private def stepBlockMap : Std.HashMap String Name :=
  mkMap (stepPlainBlockEntries ++ stepHeadingEntries ++ stepModeBlockEntries)

private def stepNonInterMap : Std.HashMap String Name :=
  mkMap (stepInterEntries ++ stepInputEntries ++ stepModeInterEntries)

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let (bP, bI, bF) := (toExpr ctxV.inP, toExpr ctxV.interactive, toExpr ctxV.inForm)
  let rflStep := mkApp2 (mkConst ``Eq.refl [Level.one])
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
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
  let add (comb : Name) (tbl : Std.HashMap String Name) (ps : Array (Name × String))
      (m : Std.HashMap Name (Name × String × Name)) :=
    ps.foldl (fun m (fn, key) => match tbl[key]? with | some lm => m.insert fn (comb, key, lm) | none => m) m
  {} |> add ``attr_nonUrl safeNonUrlAttrMap #[
          (``Qed.role, "data-role"), (``Qed.placeholder, "placeholder"), (``Qed.name, "name"),
          (``Qed.alt, "alt"), (``Qed.title, "title"), (``Qed.style, "style"), (``Qed.type', "type")]
     |> add ``on_safe safeAttrMap #[
          (``Qed.onClick, "click"), (``Qed.onSubmit, "submit"), (``Qed.onBlur, "blur"), (``Qed.onFocus, "focus"),
          (``Qed.onDoubleClick, "dblclick"), (``Qed.onMouseDown, "mousedown"), (``Qed.onMouseUp, "mouseup")]
     |> add ``onValue_safe safeAttrMap #[
          (``Qed.onInput, "input"), (``Qed.onChange, "input"), (``Qed.onKeydown, "keydown"), (``Qed.onKeyup, "keyup")]
     |> add ``flag_safe safeAttrMap #[
          (``Qed.disabled, "disabled"), (``Qed.required, "required"), (``Qed.checked, "checked"), (``Qed.readOnly, "readonly")]

private def fastAttrCtorMap : Std.HashMap Name (Nat × Nat × Bool × Name) := mkMap #[
  (``Attr.attr,       (3, 1, true,  ``attr_nonUrl)),
  (``Attr.signalAttr, (4, 2, true,  ``signalAttr_nonUrl)),
  (``Attr.flag,       (3, 1, false, ``flag_safe)),
  (``Attr.on,         (3, 1, false, ``on_safe)),
  (``Attr.signalOn,   (4, 2, false, ``signalOn_safe)),
  (``Attr.onValue,    (3, 1, false, ``onValue_safe))]

def fastAttrValidProof? (msgTy a : Expr) : Option Expr :=
  let a := a.consumeMData
  let args := a.getAppArgs
  let strLit? (e : Expr) : Option String := match e.consumeMData with | .lit (.strVal s) => some s | _ => none
  a.getAppFn.constName?.bind fun fn =>
    match fn, args.size with
    | ``VAttr.eval, 4 =>
        let va := args[3]!.consumeMData
        if va.getAppFn.constName? == some ``V.onCheck' && va.getAppArgs.size == 3 then
          some (mkApp4 (mkConst ``valid_vOnCheck) args[0]! args[1]! args[2]! va.getAppArgs[2]!)
        else none
    | ``Qed.value, 4 => some (mkApp4 (mkConst ``valid_value) args[0]! args[1]! args[2]! args[3]!)
    | ``Qed.onCheck, 2 => some (mkApp2 (mkConst ``valid_onCheck) args[0]! args[1]!)
    | ``Qed.attr, 5 =>
        (strLit? args[3]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``valid_attr_nonUrl) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, mkConst lem]
    | _, 2 =>
        qedAttrWrapperMap[fn]?.map fun (comb, key, lem) =>
          mkApp4 (mkConst comb) msgTy (toExpr key) args[1]! (mkConst lem)
    | _, sz =>
        fastAttrCtorMap[fn]?.bind fun (arity, keyIdx, nonUrl, thm) =>
          if sz != arity then none
          else
            let tbl := if nonUrl then safeNonUrlAttrMap else safeAttrMap
            (strLit? args[keyIdx]! >>= (tbl[·]?)).map fun lem =>
              mkAppN (mkConst thm) (#[msgTy] ++ args.extract 1 arity ++ #[mkConst lem])

end Qed.ValidLemmas
