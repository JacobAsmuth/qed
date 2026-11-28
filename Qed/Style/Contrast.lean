import Qed.Style.Core

namespace Qed

private def srgbLinearTable : Array (Array Nat) := #[
  #[0, 304, 607, 911, 1214, 1518, 1821, 2125, 2428, 2732, 3035, 3347, 3677, 4025, 4391, 4777],
  #[5182, 5605, 6049, 6512, 6995, 7499, 8023, 8568, 9134, 9721, 10330, 10960, 11612, 12286, 12983, 13702],
  #[14444, 15209, 15996, 16807, 17642, 18500, 19382, 20289, 21219, 22174, 23153, 24158, 25187, 26241, 27321, 28426],
  #[29557, 30713, 31896, 33105, 34340, 35601, 36889, 38204, 39546, 40915, 42311, 43735, 45186, 46665, 48172, 49707],
  #[51269, 52861, 54480, 56128, 57805, 59511, 61246, 63010, 64803, 66626, 68478, 70360, 72272, 74214, 76185, 78187],
  #[80220, 82283, 84376, 86500, 88656, 90842, 93059, 95307, 97587, 99899, 102242, 104616, 107023, 109462, 111932, 114435],
  #[116971, 119538, 122139, 124772, 127438, 130136, 132868, 135633, 138432, 141263, 144128, 147027, 149960, 152926, 155926, 158961],
  #[162029, 165132, 168269, 171441, 174647, 177888, 181164, 184475, 187821, 191202, 194618, 198069, 201556, 205079, 208637, 212231],
  #[215861, 219526, 223228, 226966, 230740, 234551, 238398, 242281, 246201, 250158, 254152, 258183, 262251, 266356, 270498, 274677],
  #[278894, 283149, 287441, 291771, 296138, 300544, 304987, 309469, 313989, 318547, 323143, 327778, 332452, 337164, 341914, 346704],
  #[351533, 356400, 361307, 366253, 371238, 376262, 381326, 386429, 391572, 396755, 401978, 407240, 412543, 417885, 423268, 428690],
  #[434154, 439657, 445201, 450786, 456411, 462077, 467784, 473531, 479320, 485150, 491021, 496933, 502886, 508881, 514918, 520996],
  #[527115, 533276, 539479, 545724, 552011, 558340, 564712, 571125, 577580, 584078, 590619, 597202, 603827, 610496, 617207, 623960],
  #[630757, 637597, 644480, 651406, 658375, 665387, 672443, 679542, 686685, 693872, 701102, 708376, 715694, 723055, 730461, 737910],
  #[745404, 752942, 760525, 768151, 775822, 783538, 791298, 799103, 806952, 814847, 822786, 830770, 838799, 846873, 854993, 863157],
  #[871367, 879622, 887923, 896269, 904661, 913099, 921582, 930111, 938686, 947307, 955973, 964686, 973445, 982251, 991102, 1000000]
]
def srgbLinearX1M (c : Nat) : Nat := match srgbLinearTable[c / 16]? with | some r => (r[c % 16]?).getD 1000000 | none => 1000000

def relLuminanceX1M (r g b : Nat) : Nat := (2126 * srgbLinearX1M r + 7152 * srgbLinearX1M g + 722 * srgbLinearX1M b) / 10000
def rgbContrastX100 (c1 c2 : Nat × Nat × Nat) : Nat :=
  let l1 := relLuminanceX1M c1.1 c1.2.1 c1.2.2; let l2 := relLuminanceX1M c2.1 c2.2.1 c2.2.2; ((max l1 l2 + 50000) * 100) / (min l1 l2 + 50000)
def Color.contrastX100 (fg bg : Color) : Nat := match fg.rgb?, bg.rgb? with | some c1, some c2 => rgbContrastX100 c1 c2 | _, _ => 0
def formatContrastX100 (ratio : Nat) : String := let frac := ratio % 100; s!"{ratio / 100}.{if frac < 10 then "0" else ""}{frac}:1"
def wcagContrastAtLeast (fg bg : Color) (minX100 : Nat) : Bool := decide (Color.contrastX100 fg bg ≥ minX100)
def wcagAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 450
def wcagAALarge (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 300
def wcagAAA (fg bg : Color) : Bool := wcagContrastAtLeast fg bg 700

def TypedToken.wcagCheck (fg bg : TypedToken Color) (minX100 : Nat) : Bool :=
  let chk (a b : Option Color) := match a, b with | some f, some bg => wcagContrastAtLeast f bg minX100 | _, _ => false
  chk fg.lightVal bg.lightVal && ((fg.darkVal.isNone && bg.darkVal.isNone) || chk (fg.darkVal.orElse fun _ => fg.lightVal) (bg.darkVal.orElse fun _ => bg.lightVal))
def TypedToken.wcagAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 450
def TypedToken.wcagAALarge (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 300
def TypedToken.wcagAAA (fg bg : TypedToken Color) : Bool := TypedToken.wcagCheck fg bg 700

theorem rgbContrastX100_symm (c1 c2 : Nat × Nat × Nat) : rgbContrastX100 c1 c2 = rgbContrastX100 c2 c1 := by simp only [rgbContrastX100, Nat.max_comm, Nat.min_comm]
theorem Color.contrastX100_symm (fg bg : Color) : Color.contrastX100 fg bg = Color.contrastX100 bg fg := by
  unfold Color.contrastX100; cases fg.rgb? <;> cases bg.rgb? <;> first | exact rgbContrastX100_symm _ _ | rfl
theorem rgbContrastX100_self (c : Nat × Nat × Nat) : rgbContrastX100 c c = 100 := by
  unfold rgbContrastX100; simp only [Nat.max_self, Nat.min_self]; exact Nat.mul_div_right 100 (Nat.add_pos_right _ (by decide))
theorem Color.contrastX100_self (c : Color) (h : c.rgb?.isSome = true) : Color.contrastX100 c c = 100 := by
  unfold Color.contrastX100; cases hr : c.rgb? with | none => simp [hr] at h | some rgb => exact rgbContrastX100_self rgb
private theorem wcagContrastAtLeast_mono {fg bg : Color} {m n : Nat} (hmn : m ≤ n) (h : wcagContrastAtLeast fg bg n = true) : wcagContrastAtLeast fg bg m = true := by
  simp only [wcagContrastAtLeast, decide_eq_true_eq] at *; omega
theorem wcagAAA_implies_wcagAA (fg bg : Color) (h : wcagAAA fg bg = true) : wcagAA fg bg = true := wcagContrastAtLeast_mono (by decide) h
theorem wcagAA_implies_wcagAALarge (fg bg : Color) (h : wcagAA fg bg = true) : wcagAALarge fg bg = true := wcagContrastAtLeast_mono (by decide) h

def parseNumberWithUnit (tok : String) : Option (String × String) :=
  let (sign, r0) := match tok.toList with | '-' :: r => ("-", r) | '+' :: r => ("", r) | r => ("", r)
  let (d1, r1) := r0.span Char.isDigit
  let (numCs, unitCs) := match r1 with | '.' :: r2 => let (d2, u) := r2.span Char.isDigit; if d2.isEmpty then (d1, '.' :: r2) else (d1 ++ '.' :: d2, u) | _ => (d1, r1)
  if numCs.isEmpty then none else some (sign ++ String.ofList numCs, String.ofList unitCs)
def isNumericString (s : String) : Bool := (parseNumberWithUnit s).any (·.2.isEmpty)

def splitTopLevel (sep : Char) (s : String) : List String :=
  let flush (cur : List Char) (acc : List String) := let t := (String.ofList cur.reverse).trimmed; if t.isEmpty then acc else t :: acc
  let rec go : List Char → Nat → Bool → Char → List Char → List String → List String
    | [], _, _, _, cur, acc => (flush cur acc).reverse
    | c :: rest, d, true, q, cur, acc => go rest d (c != q) q (c :: cur) acc
    | c :: rest, d, false, q, cur, acc =>
        if c == '"' || c == '\'' then go rest d true c (c :: cur) acc
        else if c == '(' then go rest (d + 1) false q (c :: cur) acc
        else if c == ')' then go rest (d - 1) false q (c :: cur) acc
        else if d == 0 && (if sep == ' ' then c.isWhitespace else c == sep) then go rest 0 false q [] (flush cur acc)
        else go rest d false q (c :: cur) acc
  go s.toList 0 false '"' [] []

def parseFuncCall? (tok : String) : Option (String × String) :=
  let (fnCs, rest) := tok.toList.span fun c => c.isAlphanum || c == '-' || c == '_'
  match fnCs, rest with
  | _ :: _, '(' :: inner => match inner.reverse with | ')' :: revArgs => some (String.ofList fnCs, (String.ofList revArgs.reverse).trimmed) | _ => none
  | _, _ => none

def parseRgbArgs (fnName argsStr : String) (parts : List String) : Except String (Option (Nat × Nat × Nat)) := do
  let parseCh (p : String) : Except String (Option Nat) := do
    if p.startsWith "var(" then return none
    let some n := p.toNat? | throw s!"`{fnName}({argsStr})`: expected integer channel 0..255, got `{p}`"
    if n > 255 then throw s!"`{fnName}({argsStr})`: channel value `{n}` is out of range (must be 0..255)"
    return some n
  let (rS, gS, bS, a?) ← match parts with | [r, g, b] => pure (r, g, b, none) | [r, g, b, a] => pure (r, g, b, some a) | _ => throw s!"`{fnName}({argsStr})` expects {if fnName == "rgba" then 4 else 3} arguments"
  let some r ← parseCh rS | return none
  let some g ← parseCh gS | return none
  let some b ← parseCh bS | return none
  if let some aS := a? then
    if aS.startsWith "var(" then return none
    if !isNumericString aS && !(aS.endsWith "%" && isNumericString (String.ofList aS.toList.dropLast)) then throw s!"`{fnName}({argsStr})`: invalid alpha value `{aS}`"
    if aS != "1" && aS != "1.0" && aS != "100%" then return none
  return some (r, g, b)

def validateRgbArgs (fnName argsStr : String) : Except String (Option (Nat × Nat × Nat)) :=
  let byComma := splitTopLevel ',' argsStr
  parseRgbArgs fnName argsStr (if byComma.length > 1 then byComma else splitTopLevel ' ' (argsStr.replace "/" " "))

def parseCssColorRgb? (raw : String) : Option (Nat × Nat × Nat) :=
  let t := raw.trimmed
  if t.startsWith "#" then parseHexRgb? t else if t == "white" then some (255, 255, 255) else if t == "black" then some (0, 0, 0)
  else match parseFuncCall? t with | some ("rgb", args) | some ("rgba", args) => (validateRgbArgs "rgb" args).toOption.join | _ => none

def unwrapCssVarName? (raw : String) : Option String :=
  match parseFuncCall? raw.trimmed with
  | some ("var", inner) => match inner.toList with
      | '-' :: '-' :: rest => match (String.ofList rest).splitOn "," with | tok :: _ => let clean := tok.trimmed; if clean.isEmpty then none else some clean | [] => none
      | _ => none
  | _ => none

private def lastDeclValue (prop : String) (items : List Item) : Option String := items.foldl (fun acc it => match it with | .decl p v => if p == prop then some v else acc | .nest _ _ => acc) none
private def isDarkSelector (sel : String) : Bool := sel.contains "prefers-color-scheme: dark" || sel.contains "data-theme=\"dark\""
private def mkStyleColorCheck (scope : String) (forcedDark : Bool) (fgCss bgCss : String) : StyleColorCheck :=
  { scope, fgCss, bgCss, fgRgb? := parseCssColorRgb? fgCss, bgRgb? := if bgCss.isEmpty then none else parseCssColorRgb? bgCss,
    fgTok? := unwrapCssVarName? fgCss, bgTok? := if bgCss.isEmpty then none else unwrapCssVarName? bgCss, forcedDark }

mutual
  def collectStyleColorChecks (outerFg outerBg : Option String) (dark : Bool) (scope : String) (items : List Item) : List StyleColorCheck :=
    let (localFg, localBg) := (lastDeclValue "color" items, lastDeclValue "background-color" items)
    let (fg?, bg?) := (localFg.orElse fun _ => outerFg, localBg.orElse fun _ => outerBg)
    let here := if localFg.isSome || localBg.isSome then match fg? with | some fg => [mkStyleColorCheck scope dark fg (bg?.getD "")] | none => [] else []
    here ++ collectNestedColorChecks fg? bg? dark scope items
  termination_by (sizeOf items, 1)
  decreasing_by exact Prod.Lex.right _ (Nat.zero_lt_one)
  def collectNestedColorChecks (fg? bg? : Option String) (dark : Bool) (scope : String) : List Item → List StyleColorCheck
    | [] => [] | .decl _ _ :: rest => collectNestedColorChecks fg? bg? dark scope rest
    | .nest sel sub :: rest => collectStyleColorChecks fg? bg? (dark || isDarkSelector sel) (if scope.isEmpty then sel else scope ++ " " ++ sel) sub ++ collectNestedColorChecks fg? bg? dark scope rest
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (apply Prod.Lex.left; simp_wf; omega)
end

structure ContrastFallbackBg where mk :: (css : String) (rgb? : Option (Nat × Nat × Nat) := none) (tok? : Option String := none) deriving Inhabited, BEq
structure ContrastViolation where (styleName scope fgCss bgCss : String) (ratioX100 : Nat) deriving Inhabited, BEq

private def resolveCheckColor (palette : List ThemeColorEntry) (dark : Bool) (rgb? : Option (Nat × Nat × Nat)) (tok? : Option String) : Option (Nat × Nat × Nat) :=
  rgb?.orElse fun _ => tok?.bind fun tok => (palette.find? (·.cssName == tok)).map fun e => if dark then e.darkRgb?.getD e.lightRgb else e.lightRgb

private def checkOneColorCheck (styleName : String) (minX100 : Nat) (palette : List ThemeColorEntry) (fallbackBg? : Option ContrastFallbackBg) (chk : StyleColorCheck) : List ContrastViolation :=
  let (bgCss, bgRgb?, bgTok?) := if !chk.bgCss.isEmpty then (chk.bgCss, chk.bgRgb?, chk.bgTok?) else match fallbackBg? with | some fb => (fb.css, fb.rgb?, fb.tok?) | none => ("", none, none)
  if bgCss.isEmpty then [] else
    let runMode (modeLabel : String) (dark : Bool) : List ContrastViolation :=
      match resolveCheckColor palette dark chk.fgRgb? chk.fgTok?, resolveCheckColor palette dark bgRgb? bgTok? with
      | some fgRgb, some bgRgb => let r := rgbContrastX100 fgRgb bgRgb; if r < minX100 then [{ styleName, scope := modeLabel, fgCss := chk.fgCss, bgCss, ratioX100 := r }] else []
      | _, _ => []
    let lbl (m : String) := if chk.scope.isEmpty then m else chk.scope ++ s!" ({m})"
    if chk.forcedDark then runMode (if chk.scope.isEmpty then "dark" else chk.scope) true
    else runMode (lbl "light") false ++ if palette.any (·.darkRgb?.isSome) && (chk.fgTok?.isSome || bgTok?.isSome) then runMode (lbl "dark") true else []

def Style.contrastViolations (minX100 : Nat) (palette : List ThemeColorEntry) (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : List ContrastViolation :=
  if s.isGlobal then [] else s.colorChecks.flatMap (checkOneColorCheck s.className minX100 palette fallbackBg?)
def Style.hasContrastPair (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : Bool := s.colorChecks.any fun chk => !chk.bgCss.isEmpty || fallbackBg?.isSome
def Style.checkContrast (minX100 : Nat) (palette : List ThemeColorEntry) (fallbackBg? : Option ContrastFallbackBg := none) (s : Style) : Bool := (s.contrastViolations minX100 palette fallbackBg?).isEmpty
def findStylesContrastViolations (minX100 : Nat) (extraPalette : List ThemeColorEntry) (fallbackBg? : Option ContrastFallbackBg := none) (styles : List Style) : List ContrastViolation :=
  let palette := styles.flatMap (·.themePalette) ++ extraPalette; styles.flatMap (Style.contrastViolations minX100 palette fallbackBg?)
def checkStylesContrast (minX100 : Nat) (extraPalette : List ThemeColorEntry) (fallbackBg? : Option ContrastFallbackBg := none) (styles : List Style) : Bool :=
  (findStylesContrastViolations minX100 extraPalette fallbackBg? styles).isEmpty
def ContrastFallbackBg.ofToken (tok : TypedToken Color) : ContrastFallbackBg :=
  { css := s!"var(--{tok.name})", rgb? := none, tok? := some tok.name }
def Theme.checkContrast (th : Theme) (styles : List Style) (minX100 : Nat := 450) (bg? : Option (TypedToken Color) := none) : Bool :=
  checkStylesContrast minX100 th.colorPalette (bg?.map ContrastFallbackBg.ofToken) styles
def formatContrastViolations (minX100 : Nat) (vs : List ContrastViolation) : String :=
  if vs.isEmpty then "" else s!"WCAG contrast check failed (required >= {formatContrastX100 minX100}):\n" ++
    String.intercalate "\n" (vs.map fun v => s!"  • style `{v.styleName}` ({v.scope}): color `{v.fgCss}` on background-color `{v.bgCss}` is {formatContrastX100 v.ratioX100}")
end Qed
