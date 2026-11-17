import Qed.Style

namespace Qed

def attrClasses : List (Attr msg) → List String
  | []                     => []
  | .cls c :: r            => c :: attrClasses r
  | .attr k c :: r         => if k == "class" then c :: attrClasses r else attrClasses r
  | .signalAttr _ k c :: r => if k == "class" then c :: attrClasses r else attrClasses r
  | _ :: r                 => attrClasses r

def attrRole : List (Attr msg) → Option String
  | []                                => none
  | .attr "data-role" v :: _          => some v
  | .signalAttr _ "data-role" v :: _  => some v
  | _ :: r                            => attrRole r

mutual
def everyElement (p : String → List (Attr msg) → Bool) : Html msg → Bool
  | .text _        => true
  | .element t a k => p t a && everyElementL p k
def everyElementL (p : String → List (Attr msg) → Bool) : List (Html msg) → Bool
  | []     => true
  | h :: t => everyElement p h && everyElementL p t
end

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

def roleHas (r : String) (style : Style) (h : Html msg) : Bool :=
  hasRole r h &&
  everyElement (fun _ a => !(attrRole a == some r) || (attrClasses a).contains style.className) h

def roleHasOnly (r : String) (chosen excluded : Style) (h : Html msg) : Bool :=
  roleHas r chosen h && roleHasOneOf r [chosen, excluded] h

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
    attrRole (a.map (Attr.map f)) = attrRole a := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x
                    case attr k v => by_cases hk : k = "data-role" <;>
                                       simp [List.map, Attr.map, attrRole, hk, ih]
                    case signalAttr sig k v =>
                                     by_cases hk : k = "data-role" <;>
                                       simp [List.map, Attr.map, attrRole, hk, ih]
                    all_goals simp [List.map, Attr.map, attrRole, ih]

mutual
theorem everyElement_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) :
    (h : Html α) → everyElement pβ (h.map f) = everyElement pα h
  | .text _        => rfl
  | .element t a k => by simp only [Html.map, everyElement, hp, everyElementL_map f hp k]
theorem everyElementL_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) :
    (l : List (Html α)) → everyElementL pβ (Html.mapChildren f l) = everyElementL pα l
  | []     => rfl
  | c :: cs => by simp only [Html.mapChildren, everyElementL,
                             everyElement_map f hp c, everyElementL_map f hp cs]
end

theorem everyElementL_mapList {α β} (p) (g : β → Html α) (l : List β) :
    everyElementL p (l.map g) = true ↔ ∀ x ∈ l, everyElement p (g x) = true := by
  induction l with
  | nil => simp [everyElementL]
  | cons x xs ih => simp [List.map, everyElementL, ih, Bool.and_eq_true]

theorem roleHasOneOf_map {α β} (f : α → β) (r) (styles) (h : Html α) :
    roleHasOneOf r styles (h.map f) = roleHasOneOf r styles h :=
  everyElement_map f (fun _ _ => by simp [attrRole_map, attrClasses_map, hasOneClass]) h

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
    attrRole (a.filterMap Attr.canonical) = attrRole a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | attr k v | signalAttr _ k v =>
          by_cases hk : k = "data-role" <;>
            simp [Attr.canonical, attrRole, hk, ih]
      | _ => simp [Attr.canonical, attrRole, ih]

private theorem canonicalList_eq_singleton {cs : List (Html msg)} {c : Html msg}
    (h : Html.canonicalList cs = [c]) : ∃ c₀, cs = [c₀] ∧ c = Html.canonical c₀ := by
  cases cs with
  | nil => simp [Html.canonicalList] at h
  | cons c₀ rest =>
      cases rest with
      | nil => simp [Html.canonicalList] at h; exact ⟨c₀, rfl, h.symm⟩
      | cons _ _ => simp [Html.canonicalList] at h

private theorem attrRole_of_onlySignalBind :
    ∀ a : List (Attr msg), onlySignalBind a = true → attrRole a = none
  | [.signalBind _], _ => rfl
  | .key _ :: rest, h => attrRole_of_onlySignalBind rest h

mutual
  theorem everyElement_canonical {p : String → List (Attr msg) → Bool}
      (hcanonical : ∀ t a, p t (a.filterMap Attr.canonical) = p t a)
      (hspan : ∀ a, onlySignalBind a = true → p "span" a = true) :
      ∀ h : Html msg, everyElement p (Html.canonical h) = everyElement p h
    | .text _ => rfl
    | .element t a cs => by
        dsimp [Html.canonical, mkCanonicalElem]
        by_cases hcond : (t == "span" && onlySignalBind a) = true
        · rw [if_pos hcond]
          have ⟨ht, ha⟩ := Bool.and_eq_true_iff.1 hcond
          have hteq : t = "span" := beq_iff_eq.1 ht
          subst hteq
          cases hcl : Html.canonicalList cs with
          | nil =>
              have hL := everyElementL_canonical hcanonical hspan cs
              rw [hcl] at hL
              simp [everyElement, hcanonical, hL]
          | cons c rest =>
              cases rest with
              | nil =>
                  rcases canonicalList_eq_singleton hcl with ⟨c₀, rfl, rfl⟩
                  simp [everyElement, everyElementL, hspan a ha,
                        everyElement_canonical hcanonical hspan c₀]
              | cons _ _ =>
                  have hL := everyElementL_canonical hcanonical hspan cs
                  rw [hcl] at hL
                  simp [everyElement, hcanonical, hL]
        · rw [if_neg hcond]
          simp [everyElement, hcanonical t a, everyElementL_canonical hcanonical hspan cs]

  theorem everyElementL_canonical {p : String → List (Attr msg) → Bool}
      (hcanonical : ∀ t a, p t (a.filterMap Attr.canonical) = p t a)
      (hspan : ∀ a, onlySignalBind a = true → p "span" a = true) :
      ∀ cs : List (Html msg), everyElementL p (Html.canonicalList cs) = everyElementL p cs
    | [] => rfl
    | c :: cs => by
        simp [Html.canonicalList, everyElementL,
              everyElement_canonical hcanonical hspan c,
              everyElementL_canonical hcanonical hspan cs]
end

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

@[simp] theorem roleHas_canonical (r : String) (style : Style) (h : Html msg) :
    roleHas r style (Html.canonical h) = roleHas r style h := by
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
