import Qed.Style.Core

namespace Qed

def attrClasses : List (Attr msg) → List String
  | []                     => []
  | .cls c :: r            => c :: attrClasses r
  | .attr k c :: r         => if k == "class" then c :: attrClasses r else attrClasses r
  | .signalAttr _ k c :: r => if k == "class" then c :: attrClasses r else attrClasses r
  | _ :: r                 => attrClasses r

abbrev attrRole {msg : Type} : List (Attr msg) → Option String :=
  attrValue "data-role"

mutual
def everyElement (p : String → List (Attr msg) → Bool) : Html msg → Bool
  | .text _        => true
  | .element t a k => p t a && everyElementL p k
def everyElementL (p : String → List (Attr msg) → Bool) : List (Html msg) → Bool
  | []     => true
  | h :: t => everyElement p h && everyElementL p t
end

private theorem everyElement_eq_fold (p : String → List (Attr msg) → Bool) (h : Html msg) :
    everyElement p h = Html.fold (fun _ => true) (fun t a _ r => p t a && r) true (· && ·) h :=
  Html.fold_eq_node (everyElement p) (everyElementL p) _ _ _ _ (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) h

private theorem everyElementL_eq_fold (p : String → List (Attr msg) → Bool) (cs : List (Html msg)) :
    everyElementL p cs = Html.foldList (fun _ => true) (fun t a _ r => p t a && r) true (· && ·) cs :=
  Html.fold_eq_list (everyElement p) (everyElementL p) _ _ _ _ (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) cs

def hasRole (r : String) (h : Html msg) : Bool :=
  !everyElement (fun _ a => !(attrRole a == some r)) h

def hasTag (tag : String) (h : Html msg) : Bool :=
  !everyElement (fun t _ => !(t == tag)) h

-- Filter `a`'s classes against `styles` so `s.className == s.className` reduces by reflexivity without unfolding hashes.
def hasOneClass (styles : List Style) (a : List (Attr msg)) : Bool :=
  let cs := attrClasses a
  (cs.filter (fun c => (styles.map (·.className)).contains c)).length == 1

def roleHasOneOf (r : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || hasOneClass styles a)

def tagHasOneOf (tag : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun t a => !(t == tag) || hasOneClass styles a)

def roleHas (r : String) (s : Style) (h : Html msg) : Bool :=
  hasRole r h &&
  everyElement (fun _ a => !(attrRole a == some r) || (attrClasses a).contains s.className) h

def roleHasOnly (r : String) (chosen excluded : Style) (h : Html msg) : Bool :=
  roleHas r chosen h && roleHasOneOf r [chosen, excluded] h

def roleLacks (r : String) (s : Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || !(attrClasses a).contains s.className)

def tagLacks (tag : String) (s : Style) : Html msg → Bool :=
  everyElement (fun t a => !(t == tag) || !(attrClasses a).contains s.className)

def roleHasAll (r : String) (styles : List Style) (h : Html msg) : Bool :=
  hasRole r h &&
  everyElement (fun _ a => !(attrRole a == some r) || styles.all (fun s => (attrClasses a).contains s.className)) h

def tagHas (tag : String) (s : Style) (h : Html msg) : Bool :=
  hasTag tag h &&
  everyElement (fun t a => !(t == tag) || (attrClasses a).contains s.className) h

def noConflictingStyles (styles : List Style) : Html msg → Bool :=
  everyElement (fun _ a =>
    let cs := attrClasses a
    (cs.filter (fun c => (styles.map (·.className)).contains c)).length ≤ 1)

def both (p q : Html msg → Bool) : Html msg → Bool := fun h => p h && q h
def either (p q : Html msg → Bool) : Html msg → Bool := fun h => p h || q h

def exactlyOne (roleA roleB : String) (on off : Style) : Html msg → Bool :=
  either (both (roleHasOnly roleA on off) (roleHasOnly roleB off on))
         (both (roleHasOnly roleA off on) (roleHasOnly roleB on off))

def allRolesOff : List String → Style → Style → Html msg → Bool
  | [],      _,  _,   _ => true
  | r :: rs, on, off, h => roleHasOnly r off on h && allRolesOff rs on off h

def exactlyOneOf (roles : List String) (on off : Style) (h : Html msg) : Bool :=
  let rec go (before : List String) : List String → Bool
    | []      => false
    | r :: rs =>
        (allRolesOff before on off h && roleHasOnly r on off h && allRolesOff rs on off h)
          || go (r :: before) rs
  go [] roles

theorem attrClasses_map {α β} (f : α → β) (a : List (Attr α)) :
    attrClasses (a.map (Attr.map f)) = attrClasses a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | attr k _ | signalAttr _ k _ =>
          by_cases hk : (k == "class") <;> simp [Attr.map, attrClasses, hk, ih]
      | _ => simp_all [attrClasses, Attr.map]

theorem attrRole_map {α β} (f : α → β) (a : List (Attr α)) :
    attrRole (a.map (Attr.map f)) = attrRole a := attrValue_map "data-role" f a

theorem everyElement_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) (h : Html α) :
    everyElement pβ (h.map f) = everyElement pα h := by
  rw [everyElement_eq_fold, everyElement_eq_fold]
  exact Html.fold_map f _ _ _ true (· && ·) (fun t a _ _ => by simp [hp]) h

theorem everyElementL_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) (l : List (Html α)) :
    everyElementL pβ (Html.mapChildren f l) = everyElementL pα l := by
  rw [everyElementL_eq_fold, everyElementL_eq_fold]
  exact Html.foldList_map f _ _ _ true (· && ·) (fun t a _ _ => by simp [hp]) l

theorem everyElementL_mapList {α β} (p) (g : β → Html α) (l : List β) :
    everyElementL p (l.map g) = true ↔ ∀ x ∈ l, everyElement p (g x) = true := by
  simp only [everyElementL_eq_fold, everyElement_eq_fold]
  exact Html.foldList_all_mapList _ _ g l

@[simp] theorem roleLacks_map {α β} (f : α → β) (r) (s) (h : Html α) :
    roleLacks r s (h.map f) = roleLacks r s h :=
  everyElement_map f (fun _ _ => by simp [attrClasses_map]) h

@[simp] theorem tagLacks_map {α β} (f : α → β) (tag) (s) (h : Html α) :
    tagLacks tag s (h.map f) = tagLacks tag s h :=
  everyElement_map f (fun _ _ => by simp [attrClasses_map]) h

theorem everyElement_through_map {α β} (f : α → β) {Pα : String → List (Attr α) → Bool}
    {Pβ : String → List (Attr β) → Bool} (h : Html α)
    (hP : ∀ t a, Pβ t (a.map (Attr.map f)) = Pα t a) (hc : everyElement Pα h = true) :
    everyElement Pβ (h.map f) = true := by rw [everyElement_map f hP]; exact hc

@[simp] theorem attrClasses_canonical (a : List (Attr msg)) :
    attrClasses (a.filterMap Attr.canonical) = attrClasses a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | attr k c | signalAttr _ k c =>
          by_cases hk : (k == "class") <;> simp [Attr.canonical, attrClasses, hk, ih]
      | _ => simp [Attr.canonical, attrClasses, ih]

@[simp] theorem attrRole_canonical (a : List (Attr msg)) :
    attrRole (a.filterMap Attr.canonical) = attrRole a :=
  attrValue_canonical "data-role" (by decide) a

private theorem attrRole_of_onlySignalBind (a : List (Attr msg)) (h : onlySignalBind a = true) :
    attrRole a = none := attrValue_of_onlySignalBind "data-role" a h

private theorem attrClasses_of_onlySignalBind :
    ∀ a : List (Attr msg), onlySignalBind a = true → attrClasses a = []
  | [.signalBind _], _ => rfl
  | .key _ :: rest, h => attrClasses_of_onlySignalBind rest h

theorem everyElement_canonical {p : String → List (Attr msg) → Bool}
    (hcanonical : ∀ t a, p t (a.filterMap Attr.canonical) = p t a)
    (hspan : ∀ a, onlySignalBind a = true → p "span" a = true)
    (h : Html msg) : everyElement p (Html.canonical h) = everyElement p h := by
  rw [everyElement_eq_fold, everyElement_eq_fold]
  exact Html.fold_canonical _ _ true (· && ·)
    (fun a _ _ ha => by simp [hspan a ha])
    (fun t a _ _ => by simp [hcanonical t a]) h

theorem everyElementL_canonical {p : String → List (Attr msg) → Bool}
    (hcanonical : ∀ t a, p t (a.filterMap Attr.canonical) = p t a)
    (hspan : ∀ a, onlySignalBind a = true → p "span" a = true)
    (cs : List (Html msg)) : everyElementL p (Html.canonicalList cs) = everyElementL p cs := by
  rw [everyElementL_eq_fold, everyElementL_eq_fold]
  exact Html.foldList_canonical _ _ true (· && ·)
    (fun a _ _ ha => by simp [hspan a ha])
    (fun t a _ _ => by simp [hcanonical t a]) cs

@[simp] theorem hasRole_canonical (r : String) (h : Html msg) :
    hasRole r (Html.canonical h) = hasRole r h := by
  unfold hasRole
  rw [everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrRole_of_onlySignalBind a ha])]

theorem hasTag_canonical (tag : String) (h : Html msg) (ht : tag ≠ "span") :
    hasTag tag (Html.canonical h) = hasTag tag h := by
  have hne : ("span" == tag) = false := beq_false_of_ne (Ne.symm ht)
  unfold hasTag
  rw [everyElement_canonical (fun _ _ => rfl) (fun _ _ => by simp [hne])]

@[simp] theorem roleHasOneOf_canonical (r : String) (styles : List Style) (h : Html msg) :
    roleHasOneOf r styles (Html.canonical h) = roleHasOneOf r styles h :=
  everyElement_canonical (fun _ _ => by simp [hasOneClass])
    (fun a ha => by simp [attrRole_of_onlySignalBind a ha]) h

@[simp] theorem roleLacks_canonical (r : String) (s : Style) (h : Html msg) :
    roleLacks r s (Html.canonical h) = roleLacks r s h :=
  everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrRole_of_onlySignalBind a ha]) h

@[simp] theorem tagLacks_canonical (tag : String) (s : Style) (h : Html msg) :
    tagLacks tag s (Html.canonical h) = tagLacks tag s h :=
  everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrClasses_of_onlySignalBind a ha]) h

@[simp] theorem roleHasAll_canonical (r : String) (styles : List Style) (h : Html msg) :
    roleHasAll r styles (Html.canonical h) = roleHasAll r styles h := by
  unfold roleHasAll
  rw [hasRole_canonical, everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrRole_of_onlySignalBind a ha])]

theorem tagHas_canonical (tag : String) (s : Style) (h : Html msg) (ht : tag ≠ "span") :
    tagHas tag s (Html.canonical h) = tagHas tag s h := by
  have hne : ("span" == tag) = false := beq_false_of_ne (Ne.symm ht)
  unfold tagHas
  rw [hasTag_canonical tag h ht, everyElement_canonical (fun _ _ => by simp)
    (fun _ _ => by simp [hne])]

@[simp] theorem noConflictingStyles_canonical (styles : List Style) (h : Html msg) :
    noConflictingStyles styles (Html.canonical h) = noConflictingStyles styles h :=
  everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrClasses_of_onlySignalBind a ha]) h

theorem tagHasOneOf_canonical (tag : String) (styles : List Style) (h : Html msg) (ht : tag ≠ "span") :
    tagHasOneOf tag styles (Html.canonical h) = tagHasOneOf tag styles h := by
  have hne : ("span" == tag) = false := beq_false_of_ne (Ne.symm ht)
  exact everyElement_canonical (fun _ _ => by simp [hasOneClass]) (fun _ _ => by simp [hne]) h

@[simp] theorem roleHas_canonical (r : String) (s : Style) (h : Html msg) :
    roleHas r s (Html.canonical h) = roleHas r s h := by
  unfold roleHas
  rw [hasRole_canonical, everyElement_canonical (fun _ _ => by simp)
    (fun a ha => by simp [attrRole_of_onlySignalBind a ha])]

@[simp] theorem roleHasOnly_canonical (r : String) (chosen excluded : Style) (h : Html msg) :
    roleHasOnly r chosen excluded (Html.canonical h) = roleHasOnly r chosen excluded h := by
  simp [roleHasOnly]

@[simp] theorem allRolesOff_canonical (roles : List String) (on off : Style) (h : Html msg) :
    allRolesOff roles on off (Html.canonical h) = allRolesOff roles on off h := by
  induction roles with
  | nil => rfl
  | cons _ _ ih => simp [allRolesOff, ih]

@[simp] theorem exactlyOne_canonical (rA rB : String) (on off : Style) (h : Html msg) :
    exactlyOne rA rB on off (Html.canonical h) = exactlyOne rA rB on off h := by
  simp [exactlyOne, both, either]

@[simp] theorem exactlyOneOf_canonical (roles : List String) (on off : Style) (h : Html msg) :
    exactlyOneOf roles on off (Html.canonical h) = exactlyOneOf roles on off h := by
  suffices hgo : ∀ before rest,
      exactlyOneOf.go on off (Html.canonical h) before rest = exactlyOneOf.go on off h before rest from hgo [] roles
  intro before rest
  induction rest generalizing before with
  | nil => rfl
  | cons r rs ih => simp [exactlyOneOf.go, ih (r :: before)]

theorem canonical_congr_pred {P : Html msg → Bool} {h₁ h₂ : Html msg}
    (hcan : Html.canonical h₁ = Html.canonical h₂)
    (heq₁ : P (Html.canonical h₁) = P h₁)
    (heq₂ : P (Html.canonical h₂) = P h₂) :
    P h₁ = P h₂ := by
  rw [← heq₁, hcan, heq₂]

end Qed
