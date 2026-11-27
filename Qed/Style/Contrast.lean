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

def relLuminanceX1M (r g b : Nat) : Nat :=
  (2126 * srgbLinearX1M r + 7152 * srgbLinearX1M g + 722 * srgbLinearX1M b) / 10000

def rgbContrastX100 (c1 c2 : Nat × Nat × Nat) : Nat :=
  let l1 := relLuminanceX1M c1.1 c1.2.1 c1.2.2; let l2 := relLuminanceX1M c2.1 c2.2.1 c2.2.2
  ((max l1 l2 + 50000) * 100) / (min l1 l2 + 50000)

def Color.contrastX100 (fg bg : Color) : Nat :=
  match fg.rgb?, bg.rgb? with | some c1, some c2 => rgbContrastX100 c1 c2 | _, _ => 0

def formatContrastX100 (ratio : Nat) : String :=
  let frac := ratio % 100
  s!"{ratio / 100}.{if frac < 10 then "0" else ""}{frac}:1"

def wcagContrastAtLeast (fg bg : Color) (minX100 : Nat) : Bool := decide (Color.contrastX100 fg bg ≥ minX100)
def wcagAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 450
def wcagAALarge (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 300
def wcagAAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 700

def TypedToken.wcagCheck (fg bg : TypedToken Color) (minX100 : Nat) : Bool :=
  let chk (a b : Option Color) := match a, b with | some f, some bg => wcagContrastAtLeast f bg minX100 | _, _ => false
  chk fg.lightVal bg.lightVal &&
    ((fg.darkVal.isNone && bg.darkVal.isNone) ||
      chk (fg.darkVal.orElse fun _ => fg.lightVal) (bg.darkVal.orElse fun _ => bg.lightVal))

def TypedToken.wcagAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 450
def TypedToken.wcagAALarge (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 300
def TypedToken.wcagAAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 700

/-! ## WCAG Contrast Theorems -/

theorem rgbContrastX100_symm (c1 c2 : Nat × Nat × Nat) : rgbContrastX100 c1 c2 = rgbContrastX100 c2 c1 := by
  simp only [rgbContrastX100, Nat.max_comm, Nat.min_comm]

theorem Color.contrastX100_symm (fg bg : Color) : Color.contrastX100 fg bg = Color.contrastX100 bg fg := by
  unfold Color.contrastX100; cases fg.rgb? <;> cases bg.rgb? <;> first | exact rgbContrastX100_symm _ _ | rfl

theorem rgbContrastX100_self (c : Nat × Nat × Nat) : rgbContrastX100 c c = 100 := by
  unfold rgbContrastX100; simp only [Nat.max_self, Nat.min_self]; exact Nat.mul_div_right 100 (Nat.add_pos_right _ (by decide))

theorem Color.contrastX100_self (c : Color) (h : c.rgb?.isSome = true) : Color.contrastX100 c c = 100 := by
  unfold Color.contrastX100; cases hr : c.rgb? with | none => simp [hr] at h | some rgb => exact rgbContrastX100_self rgb

private theorem wcagContrastAtLeast_mono {fg bg : Color} {m n : Nat} (hmn : m ≤ n)
    (h : wcagContrastAtLeast fg bg n = true) : wcagContrastAtLeast fg bg m = true := by
  simp only [wcagContrastAtLeast, decide_eq_true_eq] at *; omega

theorem wcagAAA_implies_wcagAA (fg bg : Color) (h : wcagAAA fg bg = true) : wcagAA fg bg = true :=
  wcagContrastAtLeast_mono (by decide) h

theorem wcagAA_implies_wcagAALarge (fg bg : Color) (h : wcagAA fg bg = true) : wcagAALarge fg bg = true :=
  wcagContrastAtLeast_mono (by decide) h

/-! ## Style & Stylesheet Contrast Verification (Fast Kernel-Reducible) -/

private def isSimpleNumericStr (s : String) : Bool :=
  let cs := match s.toList with | '-' :: r | '+' :: r => r | r => r
  let (d1, r1) := cs.span Char.isDigit
  !d1.isEmpty && match r1 with | [] => true | '.' :: r2 => !r2.isEmpty && r2.all Char.isDigit | _ => false

def parseRgbArgs (fnName argsStr : String) (parts : List String) : Except String (Option (Nat × Nat × Nat)) := do
  let parseCh (p : String) : Except String (Option Nat) := do
    if p.startsWith "var(" then return none
    let some n := p.toNat? | throw s!"`{fnName}({argsStr})`: expected integer channel 0..255, got `{p}`"
    if n > 255 then throw s!"`{fnName}({argsStr})`: channel value `{n}` is out of range (must be 0..255)"
    return some n
  let (rS, gS, bS, a?) ← match parts with
    | [r, g, b] => pure (r, g, b, none) | [r, g, b, a] => pure (r, g, b, some a)
    | _ => throw s!"`{fnName}({argsStr})` expects {if fnName == "rgba" then 4 else 3} arguments"
  let some r ← parseCh rS | return none
  let some g ← parseCh gS | return none
  let some b ← parseCh bS | return none
  if let some aS := a? then
    if aS.startsWith "var(" then return none
    if !isSimpleNumericStr aS && !(aS.endsWith "%" && isSimpleNumericStr (String.ofList aS.toList.dropLast)) then
      throw s!"`{fnName}({argsStr})`: invalid alpha value `{aS}`"
    if aS != "1" && aS != "1.0" && aS != "100%" then return none
  return some (r, g, b)

def parseCssColorRgb? (raw : String) : Option (Nat × Nat × Nat) :=
  let t := raw.trimmed
  if t.startsWith "#" then parseHexRgb? t
  else if t == "white" then some (255, 255, 255)
  else if t == "black" then some (0, 0, 0)
  else if (t.startsWith "rgb(" || t.startsWith "rgba(") && t.endsWith ")" then
    let argsStr := String.ofList ((t.toList.drop (if t.startsWith "rgba(" then 5 else 4)).dropLast)
    let parts :=
      if argsStr.contains ',' then (argsStr.splitOn ",").map String.trimmed
      else ((argsStr.replace "/" " ").splitOn " ").map String.trimmed |>.filter (!·.isEmpty)
    match parseRgbArgs "rgb" argsStr parts with | .ok res => res | .error _ => none
  else none

def unwrapCssVarName? (raw : String) : Option String :=
  let t := raw.trimmed
  if t.startsWith "var(--" && t.endsWith ")" then
    let inner := (String.ofList ((t.toList.drop 6).dropLast)).trimmed
    match inner.splitOn "," with
    | tok :: _ => let clean := tok.trimmed; if clean.isEmpty then none else some clean
    | [] => none
  else none

private def lastDeclValue (prop : String) (items : List Item) : Option String :=
  items.foldl (fun acc it => match it with | .decl p v => if p == prop then some v else acc | .nest _ _ => acc) none

private def isDarkSelector (sel : String) : Bool :=
  sel.contains "prefers-color-scheme: dark" || sel.contains "data-theme=\"dark\""

private def mkStyleColorCheck (scope : String) (forcedDark : Bool) (fgCss bgCss : String) : StyleColorCheck :=
  { scope, fgCss, bgCss
    fgRgb? := parseCssColorRgb? fgCss, bgRgb? := if bgCss.isEmpty then none else parseCssColorRgb? bgCss
    fgTok? := unwrapCssVarName? fgCss, bgTok? := if bgCss.isEmpty then none else unwrapCssVarName? bgCss
    forcedDark }

mutual
  def collectStyleColorChecks (outerFg outerBg : Option String) (dark : Bool) (scope : String)
      (items : List Item) : List StyleColorCheck :=
    let localFg := lastDeclValue "color" items
    let localBg := lastDeclValue "background-color" items
    let fg? := localFg.orElse fun _ => outerFg
    let bg? := localBg.orElse fun _ => outerBg
    let here :=
      if localFg.isSome || localBg.isSome then
        match fg? with
        | some fg => [mkStyleColorCheck scope dark fg (bg?.getD "")]
        | none => []
      else []
    here ++ collectNestedColorChecks fg? bg? dark scope items
  termination_by (sizeOf items, 1)
  decreasing_by exact Prod.Lex.right _ (Nat.zero_lt_one)

  def collectNestedColorChecks (fg? bg? : Option String) (dark : Bool) (scope : String) :
      List Item → List StyleColorCheck
    | [] => []
    | .decl _ _ :: rest => collectNestedColorChecks fg? bg? dark scope rest
    | .nest sel sub :: rest =>
        let nextScope := if scope.isEmpty then sel else scope ++ " " ++ sel
        collectStyleColorChecks fg? bg? (dark || isDarkSelector sel) nextScope sub ++
          collectNestedColorChecks fg? bg? dark scope rest
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (apply Prod.Lex.left; simp_wf; omega)
end

structure ContrastFallbackBg where mk ::
  (css : String) (rgb? : Option (Nat × Nat × Nat) := none) (tok? : Option String := none)
deriving Inhabited, BEq, Repr

structure ContrastViolation where
  styleName : String
  scope     : String
  fgCss     : String
  bgCss     : String
  ratioX100 : Nat
deriving Inhabited, BEq, Repr

private def lookupPaletteRgb (palette : List ThemeColorEntry) (dark : Bool) (tok : String) : Option (Nat × Nat × Nat) :=
  match palette.find? (fun e => e.cssName == tok) with
  | some e => if dark then e.darkRgb?.orElse fun _ => some e.lightRgb else some e.lightRgb
  | none => none

private def paletteHasDark (palette : List ThemeColorEntry) : Bool :=
  palette.any (fun e => e.darkRgb?.isSome)

private def resolveCheckColor (palette : List ThemeColorEntry) (dark : Bool)
    (rgb? : Option (Nat × Nat × Nat)) (tok? : Option String) : Option (Nat × Nat × Nat) :=
  match rgb? with
  | some c => some c
  | none => match tok? with | some tok => lookupPaletteRgb palette dark tok | none => none

private def checkOneColorCheck (styleName : String) (minX100 : Nat) (palette : List ThemeColorEntry)
    (fallbackBg? : Option ContrastFallbackBg) (chk : StyleColorCheck) : List ContrastViolation :=
  let (bgCss, bgRgb?, bgTok?) :=
    if !chk.bgCss.isEmpty then (chk.bgCss, chk.bgRgb?, chk.bgTok?)
    else match fallbackBg? with
      | some fb => (fb.css, fb.rgb?, fb.tok?)
      | none => ("", none, none)
  if bgCss.isEmpty then []
  else
    let runMode (modeLabel : String) (dark : Bool) : List ContrastViolation :=
      match resolveCheckColor palette dark chk.fgRgb? chk.fgTok?, resolveCheckColor palette dark bgRgb? bgTok? with
      | some fgRgb, some bgRgb =>
          let r := rgbContrastX100 fgRgb bgRgb
          if r < minX100 then [{ styleName, scope := modeLabel, fgCss := chk.fgCss, bgCss, ratioX100 := r }] else []
      | _, _ => []
    if chk.forcedDark then
      runMode (if chk.scope.isEmpty then "dark" else chk.scope) true
    else
      let lightLbl := if chk.scope.isEmpty then "light" else chk.scope ++ " (light)"
      let lightRes := runMode lightLbl false
      let darkRes :=
        if paletteHasDark palette && (chk.fgTok?.isSome || bgTok?.isSome) then
          let darkLbl := if chk.scope.isEmpty then "dark" else chk.scope ++ " (dark)"
          runMode darkLbl true
        else []
      lightRes ++ darkRes

def Style.contrastViolations (minX100 : Nat) (palette : List ThemeColorEntry)
    (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : List ContrastViolation :=
  if s.isGlobal then []
  else s.colorChecks.flatMap (checkOneColorCheck s.className minX100 palette fallbackBg?)

def Style.hasContrastPair (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : Bool :=
  s.colorChecks.any fun chk => !chk.bgCss.isEmpty || fallbackBg?.isSome

def Style.checkContrast (minX100 : Nat) (palette : List ThemeColorEntry)
    (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : Bool :=
  (s.contrastViolations minX100 palette fallbackBg?).isEmpty

def findStylesContrastViolations (minX100 : Nat) (extraPalette : List ThemeColorEntry)
    (fallbackBg? : Option ContrastFallbackBg := none) (styles : List Style) : List ContrastViolation :=
  let palette := styles.flatMap (·.themePalette) ++ extraPalette
  styles.flatMap (Style.contrastViolations minX100 palette fallbackBg?)

def checkStylesContrast (minX100 : Nat) (extraPalette : List ThemeColorEntry)
    (fallbackBg? : Option ContrastFallbackBg := none) (styles : List Style) : Bool :=
  (findStylesContrastViolations minX100 extraPalette fallbackBg? styles).isEmpty

def formatContrastViolations (minX100 : Nat) (vs : List ContrastViolation) : String :=
  if vs.isEmpty then ""
  else
    let lines := vs.map fun v =>
      s!"  • style `{v.styleName}` ({v.scope}): color `{v.fgCss}` on background-color `{v.bgCss}` is {formatContrastX100 v.ratioX100}"
    s!"WCAG contrast check failed (required >= {formatContrastX100 minX100}):\n" ++ String.intercalate "\n" lines

end Qed
