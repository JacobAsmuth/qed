import Qed.Style

namespace Qed

def attrClasses : List (Attr msg) → List String
  | []          => []
  | .cls c :: r => c :: attrClasses r
  | _ :: r      => attrClasses r

def attrRole : List (Attr msg) → Option String
  | []                       => none
  | .attr "data-role" v :: _ => some v
  | _ :: r                   => attrRole r

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
  | cons x xs ih => cases x <;> simp_all [attrClasses, Attr.map]

theorem attrRole_map {α β} (f : α → β) (a : List (Attr α)) :
    attrRole (a.map (Attr.map f)) = attrRole a := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x
                    case attr k v => by_cases hk : k = "data-role" <;>
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

end Qed
