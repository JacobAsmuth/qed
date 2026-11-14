import Qed.Render
import Qed.Diff
import Qed.Style

namespace Qed

inductive VAttr (σ : Type) (msg : Type) where
  | stat (a : Attr msg)
  | bind (get : σ → Attr msg)
  | dynVal (attr : String) (get : σ → String)

inductive View (σ : Type) (msg : Type) where
  | text (s : String)
  | dyn (get : σ → String)
  | element (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg))
  | ifElse (cond : σ → Bool) (yes no : View σ msg)
  | keyedList (tag : String) (attrs : List (VAttr σ msg))
      (keys : σ → Array String)
      (marks : σ → Array USize) (rowSig : σ → Nat → Array (String × String))
      (rowsHtml : σ → List (Html msg))
  | static (html : Html msg)
  | dynNode (get : σ → Html msg)

def View.showIf (cond : σ → Bool) (child : View σ msg) : View σ msg :=
  .ifElse cond child (.text "")

-- Transpiler emits `$.refMark` (ids ≥ 1); pure `0` never matches a real stamp so native evaluation never skips.
@[noinline] def refMark {α : Type} (a : α) : USize := (fun _ => 0) a

def VAttr.eval (s : σ) : VAttr σ msg → Attr msg
  | .stat a          => a
  | .bind f          => f s
  | .dynVal attr get => .attr attr (get s)

def VAttr.mapScope (f : σ' → σ) : VAttr σ msg → VAttr σ' msg
  | .stat a          => .stat a
  | .bind g          => .bind (fun s' => g (f s'))
  | .dynVal attr get => .dynVal attr (fun s' => get (f s'))

def withKey (k : String) : Html msg → Html msg
  | .element t as cs => .element t (.key k :: as) cs
  | h                => h

mutual
  def View.mapScope (f : σ' → σ) : View σ msg → View σ' msg
    | .text s                          => .text s
    | .dyn get                         => .dyn (fun s' => get (f s'))
    | .element t as ks                 => .element t (as.map (VAttr.mapScope f)) (View.mapScopeEach f ks)
    | .ifElse cond y n                 => .ifElse (fun s' => cond (f s')) (y.mapScope f) (n.mapScope f)
    | .keyedList t as keys marks rs rh =>
        .keyedList t (as.map (VAttr.mapScope f)) (fun s' => keys (f s'))
          (fun s' => marks (f s')) (fun s' => rs (f s')) (fun s' => rh (f s'))
    | .static h                        => .static h
    | .dynNode get                     => .dynNode (fun s' => get (f s'))
  def View.mapScopeEach (f : σ' → σ) : List (View σ msg) → List (View σ' msg)
    | []      => []
    | k :: ks => k.mapScope f :: View.mapScopeEach f ks
end

mutual
  def View.render : View σ msg → σ → Html msg
    | .text s,          _ => .text s
    | .dyn get,         s => .text (get s)
    | .element t as ks, s => .element t (as.map (VAttr.eval s)) (View.renderEach ks s)
    | .ifElse cond y n, s => if cond s then View.render y s else View.render n s
    | .keyedList tag as _ _ _ rowsHtml, s => .element tag (as.map (VAttr.eval s)) (rowsHtml s)
    | .static h,        _ => h
    | .dynNode get,     s => get s
  def View.renderEach : List (View σ msg) → σ → List (Html msg)
    | [],      _ => []
    | k :: ks, s => View.render k s :: View.renderEach ks s
end

instance : CoeFun (View σ msg) (fun _ => σ → Html msg) := ⟨View.render⟩

def View.ofHtml (f : σ → Html msg) : View σ msg := .dynNode f

mutual
  def applyValues : View σ msg → σ → Html msg → Html msg
    | .dyn get,              s', _                      => .text (get s')
    | .element _ attrs kids, s', .element tag _ oldKids =>
        .element tag (attrs.map (VAttr.eval s')) (applyValuesList kids s' oldKids)
    | .ifElse cond y n,      s', old                    => if cond s' then applyValues y s' old else applyValues n s' old
    | _,                     _,  old                    => old
  def applyValuesList : List (View σ msg) → σ → List (Html msg) → List (Html msg)
    | k :: ks, s', o :: os => applyValues k s' o :: applyValuesList ks s' os
    | _,       _,  _       => []
end

mutual
  def stable : View σ msg → σ → σ → Bool
    | .element _ _ kids, s, s' => stableList kids s s'
    | .ifElse cond y n,  s, s' => (cond s == cond s') && (if cond s then stable y s s' else stable n s s')
    | .keyedList ..,     _, _  => false
    | .dynNode _,        _, _  => false
    | _,                 _, _  => true
  def stableList : List (View σ msg) → σ → σ → Bool
    | k :: ks, s, s' => stable k s s' && stableList ks s s'
    | [],      _, _  => true
end

mutual
  theorem applyValues_render (t : View σ msg) (s s' : σ) :
      stable t s s' = true → applyValues t s' (View.render t s) = View.render t s' := by
    intro h
    cases t with
    | element tag attrs kids =>
        simp only [View.render, applyValues]
        rw [applyValuesList_render kids s s' (by simpa [stable] using h)]
    | ifElse cond y no =>
        cases h₁ : cond s <;> cases h₂ : cond s' <;>
          simp_all [stable, View.render, applyValues, applyValues_render y s s', applyValues_render no s s']
    | _ => simp_all [stable, View.render, applyValues]
  theorem applyValuesList_render (ts : List (View σ msg)) (s s' : σ) :
      stableList ts s s' = true → applyValuesList ts s' (View.renderEach ts s) = View.renderEach ts s' := by
    cases ts with
    | nil => simp [View.renderEach, applyValuesList]
    | cons k ks =>
        simp only [stableList, Bool.and_eq_true, View.renderEach, applyValuesList]
        rintro ⟨hk, hks⟩
        rw [applyValues_render k s s' hk, applyValuesList_render ks s s' hks]
end

def patch (t : View σ msg) (s s' : σ) (old : Html msg) : Html msg :=
  if stable t s s' then applyValues t s' old else applyPatch (diff old (View.render t s')) old

theorem patch_render (t : View σ msg) (s s' : σ) :
    patch t s s' (View.render t s) = View.render t s' := by
  simp only [patch]
  split <;> simp_all [applyValues_render, diff_apply]

mutual
  def View.hasOpaque : View σ msg → Bool
    | .text _               => false
    | .dyn _                => false
    | .element _ attrs kids =>
        attrs.any (fun | .bind _ => true | _ => false) || View.hasOpaqueList kids
    | .ifElse ..            => true
    | .keyedList ..         => true
    | .static _             => false
    | .dynNode _            => true
  def View.hasOpaqueList : List (View σ msg) → Bool
    | []      => false
    | k :: ks => k.hasOpaque || View.hasOpaqueList ks
end

mutual
  def View.collectShape : View σ msg → σ → String
    | .text _,          _ => ""
    | .dyn _,           _ => ""
    | .element _ _ kids, s => View.collectShapeList kids s
    | .ifElse cond y no, s =>
        if cond s then "1" ++ View.collectShape y s else "0" ++ View.collectShape no s
    | .keyedList tag as _ _ _ rowsHtml, s =>
        "{" ++ Html.render (.element tag (as.map (VAttr.eval s)) (rowsHtml s)) ++ "}"
    | .static _,        _ => ""
    | .dynNode get,     s => "<" ++ Html.render (get s) ++ ">"
  def View.collectShapeList : List (View σ msg) → σ → String
    | [],      _ => ""
    | k :: ks, s => View.collectShape k s ++ View.collectShapeList ks s
end

def dynValGets (attrs : List (VAttr σ msg)) : List (σ → String) :=
  attrs.filterMap fun | .dynVal _ get => some get | _ => none

mutual
  def View.collectDyn : View σ msg → List (σ → String)
    | .text _               => []
    | .dyn get              => [get]
    | .element _ attrs kids => dynValGets attrs ++ View.collectDynList kids
    | .ifElse _ y no        => View.collectDyn y ++ View.collectDyn no
    | .keyedList ..         => []
    | .static _             => []
    | .dynNode _            => []
  def View.collectDynList : List (View σ msg) → List (σ → String)
    | []      => []
    | k :: ks => View.collectDyn k ++ View.collectDynList ks
end

def renderSigAttrs (s : σ) (pre : String) : List (VAttr σ msg) → Nat → List (Attr msg) × Nat
  | [],        n => ([], n)
  | va :: rest, n =>
      let (a, n1) := match va with
        | .dynVal attr get => (Attr.signalAttr s!"{pre}#{n}" attr (get s), n + 1)
        | other            => (VAttr.eval s other, n)
      let (as, n2) := renderSigAttrs s pre rest n1
      (a :: as, n2)

mutual
  def View.renderSig : View σ msg → σ → String → Nat → Html msg × Nat
    | .text s,          _, _,   n => (.text s, n)
    | .dyn get,         s, pre, n => (.element "span" [.signalBind s!"{pre}#{n}"] [.text (get s)], n + 1)
    | .element tag attrs kids, s, pre, n =>
        let (attrs', n1) := renderSigAttrs s pre attrs n
        let (cs, n2) := View.renderSigList kids s pre n1
        (.element tag attrs' cs, n2)
    | .ifElse cond y no, s, pre, n =>
        -- Reserve inactive branch's signal indices so leaf names stay aligned with `collectDyn` across flips.
        if cond s then
          let (h, n1) := View.renderSig y s pre n
          (h, n1 + (View.collectDyn no).length)
        else
          let (h, n2) := View.renderSig no s pre (n + (View.collectDyn y).length)
          (h, n2)
    | .keyedList tag as _ _ _ rowsHtml, s, _, n =>
        (.element tag (as.map (VAttr.eval s)) (rowsHtml s), n)
    | .static h,        _, _,   n => (h, n)
    | .dynNode get,     s, _,   n => (get s, n)
  def View.renderSigList : List (View σ msg) → σ → String → Nat → List (Html msg) × Nat
    | [],      _, _,   n => ([], n)
    | k :: ks, s, pre, n =>
        let (h,  n')  := View.renderSig k s pre n
        let (hs, n'') := View.renderSigList ks s pre n'
        (h :: hs, n'')
end

@[simp] theorem View.render_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) :
    (View.showIf cond child).render s = (if cond s then child.render s else .text "") := rfl

theorem View.stable_showIf_hidden (cond : σ → Bool) (child : View σ msg) (s s' : σ)
    (h : cond s = false) (h' : cond s' = false) :
    stable (View.showIf cond child) s s' = true := by
  simp [View.showIf, stable, h, h']

@[simp] theorem View.collectShape_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) :
    (View.showIf cond child).collectShape s =
      (if cond s then "1" ++ child.collectShape s else "0") := by
  simp [View.showIf, View.collectShape]

@[simp] theorem View.collectDyn_showIf (cond : σ → Bool) (child : View σ msg) :
    (View.showIf cond child).collectDyn = child.collectDyn := by
  simp [View.showIf, View.collectDyn]

@[simp] theorem View.renderSig_showIf (cond : σ → Bool) (child : View σ msg)
    (s : σ) (pre : String) (n : Nat) :
    (View.showIf cond child).renderSig s pre n =
      (if cond s then child.renderSig s pre n else (.text "", n + child.collectDyn.length)) := by
  simp [View.showIf, View.renderSig, View.collectDyn]

namespace V

instance : Coe (Attr msg) (VAttr σ msg) := ⟨.stat⟩
instance : Coe Style (VAttr σ msg) := ⟨fun s => .stat (.cls s.className)⟩
instance : Coe String (View σ msg) := ⟨.text⟩
instance : Coe String (List (View σ msg)) := ⟨fun s => [.text s]⟩

def text (s : String) : View σ msg := .text s
def dyn (get : σ → String) : View σ msg := .dyn get
def bindAttr (get : σ → Attr msg) : VAttr σ msg := .bind get
def dynAttr (name : String) (get : σ → String) : VAttr σ msg := .dynVal name get
def onClick' (get : σ → msg) : VAttr σ msg := .bind (fun s => .on "click" (get s))
def onInput' (get : σ → String → msg) : VAttr σ msg := .bind (fun s => .onValue "input" (get s))
def onCheck' (get : σ → Bool → msg) : VAttr σ msg :=
  .bind (fun s => .onValue "change" (fun str => get s (str == "true")))
def static (h : Html msg) : View σ msg := .static h

def el (tag : String) (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) :
    View σ msg := .element tag attrs kids

def showIf (cond : σ → Bool) (child : View σ msg) : View σ msg := .showIf cond child
def ifElse (cond : σ → Bool) (yes no : View σ msg) : View σ msg := .ifElse cond yes no
def dynNode (get : σ → Html msg) : View σ msg := .dynNode get

def forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg) := []) (sigPrefix : String := "") : View σ msg :=
  -- `hasOpaque` rows can change props/closures without changing signal leaves, so fall back to `dynNode` diff.
  if child.hasOpaque then
    .dynNode fun s => .element tag (attrs.map (VAttr.eval s))
      (((items s).map fun a => withKey (key a) (child.render a)).toList)
  else
    let projs := View.collectDyn child
    let skey : α → String := fun a => sigPrefix ++ key a
    .keyedList tag attrs
      (fun s => (items s).map key)
      (fun s => (items s).map (fun a => Qed.refMark a))
      (fun s i => match (items s)[i]? with
        | some a => (projs.mapIdx fun j p => (s!"{skey a}#{j}", p a)).toArray
        | none   => #[])
      (fun s => ((items s).map fun a =>
        Html.lazy (key a) (withKey (key a) (View.renderSig child a (skey a) 0).1)).toList)

end V

end Qed
