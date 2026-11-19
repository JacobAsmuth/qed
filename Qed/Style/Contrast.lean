import Qed.Style.Core

namespace Qed

/-! ## Exact Integer WCAG 2.1 Relative Luminance & Contrast Ratio Proofs -/

/-- Exact WCAG 2.1 sRGB channel linearization (`c ∈ 0..255` → `linear(c/255) × 1_000_000`).
    2-level `c / 16` + `c % 16` dispatch reduces in ≤ 16 steps inside Lean's kernel (`decide`/`rfl`). -/
def srgbLinearX1M (c : Nat) : Nat :=
  match c / 16 with
  |  0 => match c % 16 with | 0 => 0 | 1 => 304 | 2 => 607 | 3 => 911 | 4 => 1214 | 5 => 1518 | 6 => 1821 | 7 => 2125 | 8 => 2428 | 9 => 2732 | 10 => 3035 | 11 => 3347 | 12 => 3677 | 13 => 4025 | 14 => 4391 | _ => 4777
  |  1 => match c % 16 with | 0 => 5182 | 1 => 5605 | 2 => 6049 | 3 => 6512 | 4 => 6995 | 5 => 7499 | 6 => 8023 | 7 => 8568 | 8 => 9134 | 9 => 9721 | 10 => 10330 | 11 => 10960 | 12 => 11612 | 13 => 12286 | 14 => 12983 | _ => 13702
  |  2 => match c % 16 with | 0 => 14444 | 1 => 15209 | 2 => 15996 | 3 => 16807 | 4 => 17642 | 5 => 18500 | 6 => 19382 | 7 => 20289 | 8 => 21219 | 9 => 22174 | 10 => 23153 | 11 => 24158 | 12 => 25187 | 13 => 26241 | 14 => 27321 | _ => 28426
  |  3 => match c % 16 with | 0 => 29557 | 1 => 30713 | 2 => 31896 | 3 => 33105 | 4 => 34340 | 5 => 35601 | 6 => 36889 | 7 => 38204 | 8 => 39546 | 9 => 40915 | 10 => 42311 | 11 => 43735 | 12 => 45186 | 13 => 46665 | 14 => 48172 | _ => 49707
  |  4 => match c % 16 with | 0 => 51269 | 1 => 52861 | 2 => 54480 | 3 => 56128 | 4 => 57805 | 5 => 59511 | 6 => 61246 | 7 => 63010 | 8 => 64803 | 9 => 66626 | 10 => 68478 | 11 => 70360 | 12 => 72272 | 13 => 74214 | 14 => 76185 | _ => 78187
  |  5 => match c % 16 with | 0 => 80220 | 1 => 82283 | 2 => 84376 | 3 => 86500 | 4 => 88656 | 5 => 90842 | 6 => 93059 | 7 => 95307 | 8 => 97587 | 9 => 99899 | 10 => 102242 | 11 => 104616 | 12 => 107023 | 13 => 109462 | 14 => 111932 | _ => 114435
  |  6 => match c % 16 with | 0 => 116971 | 1 => 119538 | 2 => 122139 | 3 => 124772 | 4 => 127438 | 5 => 130136 | 6 => 132868 | 7 => 135633 | 8 => 138432 | 9 => 141263 | 10 => 144128 | 11 => 147027 | 12 => 149960 | 13 => 152926 | 14 => 155926 | _ => 158961
  |  7 => match c % 16 with | 0 => 162029 | 1 => 165132 | 2 => 168269 | 3 => 171441 | 4 => 174647 | 5 => 177888 | 6 => 181164 | 7 => 184475 | 8 => 187821 | 9 => 191202 | 10 => 194618 | 11 => 198069 | 12 => 201556 | 13 => 205079 | 14 => 208637 | _ => 212231
  |  8 => match c % 16 with | 0 => 215861 | 1 => 219526 | 2 => 223228 | 3 => 226966 | 4 => 230740 | 5 => 234551 | 6 => 238398 | 7 => 242281 | 8 => 246201 | 9 => 250158 | 10 => 254152 | 11 => 258183 | 12 => 262251 | 13 => 266356 | 14 => 270498 | _ => 274677
  |  9 => match c % 16 with | 0 => 278894 | 1 => 283149 | 2 => 287441 | 3 => 291771 | 4 => 296138 | 5 => 300544 | 6 => 304987 | 7 => 309469 | 8 => 313989 | 9 => 318547 | 10 => 323143 | 11 => 327778 | 12 => 332452 | 13 => 337164 | 14 => 341914 | _ => 346704
  | 10 => match c % 16 with | 0 => 351533 | 1 => 356400 | 2 => 361307 | 3 => 366253 | 4 => 371238 | 5 => 376262 | 6 => 381326 | 7 => 386429 | 8 => 391572 | 9 => 396755 | 10 => 401978 | 11 => 407240 | 12 => 412543 | 13 => 417885 | 14 => 423268 | _ => 428690
  | 11 => match c % 16 with | 0 => 434154 | 1 => 439657 | 2 => 445201 | 3 => 450786 | 4 => 456411 | 5 => 462077 | 6 => 467784 | 7 => 473531 | 8 => 479320 | 9 => 485150 | 10 => 491021 | 11 => 496933 | 12 => 502886 | 13 => 508881 | 14 => 514918 | _ => 520996
  | 12 => match c % 16 with | 0 => 527115 | 1 => 533276 | 2 => 539479 | 3 => 545724 | 4 => 552011 | 5 => 558340 | 6 => 564712 | 7 => 571125 | 8 => 577580 | 9 => 584078 | 10 => 590619 | 11 => 597202 | 12 => 603827 | 13 => 610496 | 14 => 617207 | _ => 623960
  | 13 => match c % 16 with | 0 => 630757 | 1 => 637597 | 2 => 644480 | 3 => 651406 | 4 => 658375 | 5 => 665387 | 6 => 672443 | 7 => 679542 | 8 => 686685 | 9 => 693872 | 10 => 701102 | 11 => 708376 | 12 => 715694 | 13 => 723055 | 14 => 730461 | _ => 737910
  | 14 => match c % 16 with | 0 => 745404 | 1 => 752942 | 2 => 760525 | 3 => 768151 | 4 => 775822 | 5 => 783538 | 6 => 791298 | 7 => 799103 | 8 => 806952 | 9 => 814847 | 10 => 822786 | 11 => 830770 | 12 => 838799 | 13 => 846873 | 14 => 854993 | _ => 863157
  | 15 => match c % 16 with | 0 => 871367 | 1 => 879622 | 2 => 887923 | 3 => 896269 | 4 => 904661 | 5 => 913099 | 6 => 921582 | 7 => 930111 | 8 => 938686 | 9 => 947307 | 10 => 955973 | 11 => 964686 | 12 => 973445 | 13 => 982251 | 14 => 991102 | _ => 1000000
  | _  => 1000000

/-- WCAG 2.1 relative luminance scaled by `1_000_000` (`0` for black, `1_000_000` for white). -/
def relLuminanceX1M (r g b : Nat) : Nat :=
  (2126 * srgbLinearX1M r + 7152 * srgbLinearX1M g + 722 * srgbLinearX1M b) / 10000

/-- WCAG 2.1 contrast ratio scaled by `100` (e.g., `450` = `4.50:1`, `2100` = `21.00:1`). -/
def rgbContrastX100 (c1 c2 : Nat × Nat × Nat) : Nat :=
  let l1 := relLuminanceX1M c1.1 c1.2.1 c1.2.2
  let l2 := relLuminanceX1M c2.1 c2.2.1 c2.2.2
  let hi := max l1 l2
  let lo := min l1 l2
  ((hi + 50000) * 100) / (lo + 50000)

/-- Contrast ratio `× 100` for two `Color` values (`0` if either color lacks an opaque RGB value). -/
def Color.contrastX100 (fg bg : Color) : Nat :=
  match fg.rgb?, bg.rgb? with
  | some c1, some c2 => rgbContrastX100 c1 c2
  | _, _ => 0

def formatContrastX100 (ratio : Nat) : String :=
  let whole := ratio / 100
  let frac  := ratio % 100
  let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
  s!"{whole}.{fracStr}:1"

def wcagContrastAtLeast (fg bg : Color) (minX100 : Nat) : Bool :=
  decide (Color.contrastX100 fg bg ≥ minX100)

/-- WCAG 2.1 Level AA normal text contrast (`>= 4.50:1`). -/
def wcagAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 450

/-- WCAG 2.1 Level AA large text / UI components contrast (`>= 3.00:1`). -/
def wcagAALarge (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 300

/-- WCAG 2.1 Level AAA normal text contrast (`>= 7.00:1`). -/
def wcagAAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 700

/-- Checks WCAG contrast across BOTH light mode and dark mode for a pair of typed color tokens. -/
def TypedToken.wcagCheck (fg bg : TypedToken Color) (minX100 : Nat) : Bool :=
  let lightOk := match fg.lightVal, bg.lightVal with
    | some f, some b => wcagContrastAtLeast f b minX100
    | _, _           => false
  let darkOk :=
    if fg.darkVal.isNone && bg.darkVal.isNone then true
    else
      match fg.darkVal.orElse (fun _ => fg.lightVal), bg.darkVal.orElse (fun _ => bg.lightVal) with
      | some f, some b => wcagContrastAtLeast f b minX100
      | _, _           => false
  lightOk && darkOk

def TypedToken.wcagAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 450
def TypedToken.wcagAALarge (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 300
def TypedToken.wcagAAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 700

/-! ## WCAG Contrast Theorems -/

theorem rgbContrastX100_symm (c1 c2 : Nat × Nat × Nat) :
    rgbContrastX100 c1 c2 = rgbContrastX100 c2 c1 := by
  unfold rgbContrastX100
  simp only [Nat.max_comm, Nat.min_comm]

theorem Color.contrastX100_symm (fg bg : Color) :
    Color.contrastX100 fg bg = Color.contrastX100 bg fg := by
  unfold Color.contrastX100
  cases fg.rgb? <;> cases bg.rgb?
  · rfl
  · rfl
  · rfl
  · exact rgbContrastX100_symm _ _

theorem rgbContrastX100_self (c : Nat × Nat × Nat) :
    rgbContrastX100 c c = 100 := by
  unfold rgbContrastX100
  simp only [Nat.max_self, Nat.min_self]
  have hpos : 0 < relLuminanceX1M c.1 c.2.1 c.2.2 + 50000 := by omega
  exact Nat.mul_div_right 100 hpos

theorem Color.contrastX100_self (c : Color) (h : c.rgb?.isSome = true) :
    Color.contrastX100 c c = 100 := by
  unfold Color.contrastX100
  cases hr : c.rgb? with
  | none => simp [hr] at h
  | some rgb => exact rgbContrastX100_self rgb

theorem wcagAAA_implies_wcagAA (fg bg : Color) (h : wcagAAA fg bg = true) :
    wcagAA fg bg = true := by
  unfold wcagAAA wcagAA wcagContrastAtLeast at *
  simp only [decide_eq_true_eq] at *
  omega

theorem wcagAA_implies_wcagAALarge (fg bg : Color) (h : wcagAA fg bg = true) :
    wcagAALarge fg bg = true := by
  unfold wcagAA wcagAALarge wcagContrastAtLeast at *
  simp only [decide_eq_true_eq] at *
  omega

end Qed
