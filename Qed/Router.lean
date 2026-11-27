import Qed.Router.Basic
import Qed.Json
import Qed.Proto.Lawful
import Qed.Lang
import Lean

namespace Qed

syntax:max (name := qedArrType) term:max noWs "[" "]" : term
syntax:max (name := qedOptType) term:max noWs "?" : term
@[macro qedArrType] def expandQedArrType : Lean.Macro := fun stx => `(Array $(⟨stx.getArg 0⟩))
@[macro qedOptType] def expandQedOptType : Lean.Macro := fun stx => `(Option $(⟨stx.getArg 0⟩))

section RouterParsers
open Lean Parser
def routeEnumAltP : Parser := node `Qed.routeEnumAlt (ident >> optional ("=" >> strLit))
@[command_parser] def routeEnumCmd : Parser := leading_parser withPosition
  ("route_enum " >> ident >> ":" >> checkColGt "expected indented `route_enum` variants" >> many1Indent routeEnumAltP)
def routeParamP : Parser := node `Qed.routeParam (ident >> optional (":" >> withPosition (categoryParser `qedType 0)))
def routeAltP : Parser := node `Qed.routeAlt (withPosition
  (optional (symbol "*") >> ident >> optional (checkLineEq >> "(" >> sepBy1 routeParamP "," >> ")") >> optional ("=" >> strLit)))
@[command_parser] def routerCmd : Parser := leading_parser withPosition
  ("router " >> ident >> ":" >> checkColGt "expected indented `router` routes" >> many1Indent routeAltP)
end RouterParsers

section RouterElab
open Lean Qed.Lang

private structure RouteAltInfo where mk ::
  (ctor : Ident) (params : Array (Ident × Term)) (segments : Array (Sum String Ident)) (marked : Bool)

@[noinline] private def mkRouteEnumCmdPure (t : Ident) (alts : Array (Ident × Term)) : PureQuotM Syntax := do
  let (toSegId, fromSegId, rtId) := (mkIdent (t.getId ++ `toSeg), mkIdent (t.getId ++ `fromSeg), mkIdent (t.getId ++ `round_trip))
  let (ctors, slugs) := (alts.map (·.1), alts.map (·.2)); let ctorPats : Array Term := ctors.map fun c => mkIdent (t.getId ++ c.getId)
  let parsePats := slugs.push (← `(_)); let parseRhss := (← ctorPats.mapM fun cp => `(some $cp)).push (← `(none))
  `(inductive $t:ident where $[| $ctors:ident]*
    deriving Repr, DecidableEq, Inhabited
    def $toSegId:ident (x : $t) : String := match x with $[| $ctorPats:term => $slugs:term]*
    def $fromSegId:ident (s : String) : Option $t := match s with $[| $parsePats:term => $parseRhss:term]*
    theorem $rtId:ident : ∀ a, $fromSegId:ident ($toSegId:ident a) = some a := by intro a; cases a <;> rfl
    instance : RouteParam $t:ident := ⟨$toSegId, $fromSegId, $rtId⟩)

@[noinline, macro routeEnumCmd] def expandRouteEnumCmd : Macro := fun stx =>
  runPureQuot (mkRouteEnumCmdPure ⟨stx.getArg 1⟩ ((stx.getArg 3).getArgs.map fun alt =>
    let c : Ident := ⟨alt.getArg 0⟩; (c, if (alt.getArg 1).getNumArgs == 2 then (⟨(alt.getArg 1).getArg 1⟩ : Term) else quote (toString c.getId))))

@[noinline] private def parseRouteAlt (tName : Name) (strTy : Term) (alt : Syntax) : MacroM RouteAltInfo := do
  let err (s : Syntax) (msg : String) := Macro.throwErrorAt s s!"router `{tName}`: {msg}"
  let (marked, c) := ((alt.getArg 0).getNumArgs == 1, (⟨alt.getArg 1⟩ : Ident))
  let rawBs := if (alt.getArg 2).getNumArgs == 3 then ((alt.getArg 2).getArg 1).getSepArgs else #[]
  let seg : Option (TSyntax `str) := if (alt.getArg 3).getNumArgs == 2 then some ⟨(alt.getArg 3).getArg 1⟩ else none
  let explicitBs ← rawBs.mapM fun b => do
    let ty ← if (b.getArg 1).getNumArgs == 2 then do pure (← lowerQedType ((b.getArg 1).getArg 1) false).1 else pure strTy
    pure ((⟨b.getArg 0⟩ : Ident), ty)
  let rawSegs := seg.elim #[toString c.getId] fun s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray
  let pathDesc := seg.elim s!"`/{c.getId}`" fun s => s!"`{s.getString}`"
  if !rawSegs.any (·.startsWith ":") then return .mk c explicitBs (rawSegs.map Sum.inl ++ explicitBs.map (Sum.inr ·.1)) marked
  let mut params := #[]; let mut segs := #[]; let mut seen := #[]
  for rs in rawSegs do
    if !rs.startsWith ":" then segs := segs.push (.inl rs)
    else
      let pname := String.ofList (rs.toList.drop 1)
      if pname.isEmpty then err alt s!"route `{c.getId}` has an empty `:` parameter in path {pathDesc}"
      if seen.contains pname then err alt s!"route `{c.getId}` has duplicate `:{pname}` parameter in path {pathDesc}"
      let bt := (explicitBs.find? (toString ·.1.getId == pname)).getD (mkIdent (Name.mkSimple pname), strTy)
      params := params.push bt; segs := segs.push (.inr bt.1); seen := seen.push pname
  for (b, _) in explicitBs do
    unless seen.contains (toString b.getId) do err b s!"parameter `{b.getId}` on route `{c.getId}` is not referenced as `:{b.getId}` in path {pathDesc}"
  return .mk c params segs marked

@[noinline] private def mkRouterRowPure (tName : Name) (a : RouteAltInfo) : PureQuotM (Term × Term × Term × Term) := do
  let bs := a.params.map (·.1); let ctorId := mkIdent (tName ++ a.ctor.getId)
  let printSeg ← a.segments.mapM fun | .inl s => pure (quote s : Term) | .inr b => `(RouteParam.toSeg $(⟨b.raw⟩))
  let parseSeg : Array Term := a.segments.map fun | .inl s => quote s | .inr b => ⟨b.raw⟩
  let parseBody ← a.params.foldrM (init := ← `(some ($ctorId $bs*))) fun (b, bt) body =>
    let bT : Term := ⟨b.raw⟩; `(match (RouteParam.fromSeg $bT : Option $bt) with | some $bT => $body | none => none)
  return (← `($ctorId $bs*), ← `([$printSeg,*]), ← `([$parseSeg,*]), parseBody)

@[noinline] private def mkRouterCmdPure (t : Ident) (alts : Array RouteAltInfo) (markedCtor : Option Ident) : PureQuotM Syntax := do
  let (printId, parseId, rtId) := (mkIdent (t.getId ++ `print), mkIdent (t.getId ++ `parse), mkIdent (t.getId ++ `round_trip))
  let (toPathId, toUrlId, fromPathId) := (mkIdent (t.getId ++ `toPath), mkIdent (t.getId ++ `toUrl), mkIdent (t.getId ++ `fromPath))
  let (ctorNames, ctorBs, ctorBts) := (alts.map (·.ctor), alts.map (·.params.map (·.1)), alts.map (·.params.map (·.2)))
  let rows ← alts.mapM (mkRouterRowPure t.getId)
  let (printPats, printRhss) := (rows.map (·.1), rows.map (·.2.1))
  let (parsePatsAll, parseRhssAll) := ((rows.map (·.2.2.1)).push (← `(_)), (rows.map (·.2.2.2)).push (← `(none)))
  let inhCmd : TSyntax `command ← markedCtor.elim `(deriving instance Inhabited for $t) fun mc => `(instance : Inhabited $t := ⟨$(mkIdent (t.getId ++ mc.getId))⟩)
  `(inductive $t:ident where $[| $ctorNames:ident $[($ctorBs:ident : $ctorBts:term)]*]*
    deriving Repr, DecidableEq
    $inhCmd:command
    def $printId:ident (r : $t) : List String := match r with $[| $printPats:term => $printRhss:term]*
    def $parseId:ident (p : List String) : Option $t := match p with $[| $parsePatsAll:term => $parseRhssAll:term]*
    theorem $rtId:ident : ∀ a, $parseId:ident ($printId:ident a) = some a := by
      intro a; cases a <;>
        (try simp only [$printId:ident, $parseId:ident, RouteParam.round_trip, RouteParam.toSeg_string, RouteParam.fromSeg_string]) <;>
        (try simp [$printId:ident, $parseId:ident, RouteParam.round_trip])
    instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩
    @[inline, simp] def $toPathId:ident (r : $t) : String := Router.toURL r
    @[inline, simp] def $toUrlId:ident (r : $t) : Url := Router.toUrl r
    @[inline, simp] def $fromPathId:ident (p : String) : Option $t := Router.fromURL p
    instance : ToString $t:ident := ⟨$toPathId⟩)

@[noinline, macro routerCmd] def expandRouterCmd : Macro := fun stx => do
  let t : Ident := ⟨stx.getArg 1⟩; let strTy ← runPureQuot `(String)
  let err (s : Syntax) (msg : String) := Macro.throwErrorAt s s!"router `{t.getId}`: {msg}"
  let mut alts := #[]; let mut patShapes : Array (Ident × Array (Option String)) := #[]; let mut markedCtor : Option Ident := none
  for alt in (stx.getArg 3).getArgs do
    let info ← parseRouteAlt t.getId strTy alt
    let patShape := info.segments.map fun | .inl s => some s | .inr _ => none
    for (prevC, prevPat) in patShapes do
      if prevPat.size == patShape.size && (prevPat.zip patShape).all (fun | (some a, some b) => a == b | _ => true) then
        err info.ctor s!"route `{info.ctor.getId}` overlaps with earlier route `{prevC.getId}` (both match {patShape.size}-segment paths)"
    if info.marked then
      if let some prevC := markedCtor then err info.ctor s!"duplicate fallback route `*` on `{info.ctor.getId}` (already marked on `{prevC.getId}`)"
      if !info.params.isEmpty then err info.ctor s!"fallback route `{info.ctor.getId}` (marked `*`) must take no arguments because it handles arbitrary unmatched URLs"
      markedCtor := some info.ctor
    alts := alts.push info; patShapes := patShapes.push (info.ctor, patShape)
  runPureQuot (mkRouterCmdPure t alts markedCtor)
end RouterElab

private def decodeRouteSegs [Router R] (segs : List String) : Except String R := (Router.parse segs).elim (.error "invalid route") .ok
instance [Router R] : ToJson R := .ofEquiv Router.print
instance [Router R] : FromJson R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulJson R := .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]
instance [Router R] : NonNullJson R := ⟨nofun⟩
instance [Router R] : ToProto R := .ofEquiv Router.print
instance [Router R] : FromProto R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulProto R := .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]
instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := Except.ok.inj <|
    (h ▸ LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)).symm.trans
      (LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _))

private theorem unhex_hexDigit (n : UInt8) (hn : n.toNat < 16) : unhex (hexDigit n) = some n := by
  simp only [unhex, hexDigit, Option.map_eq_some_iff]; exact ⟨n.toNat, unhexNat?_hexDigitUpper hn, UInt8.ofNat_toNat⟩
private theorem bitvec8_nibbles : ∀ x : BitVec 8,
    (((x >>> 4) <<< 4) ||| (x &&& 0x0F#8) = x) ∧ (x >>> 4#8).toNat < 16 ∧ (x &&& 0x0F#8).toNat < 16 := by decide
private theorem encodeUTF8Loop_toList (bs : ByteArray) (i : Nat) :
    ∀ acc, (encodeUTF8Loop bs i acc).toList = acc.toList ++ (encodeUTF8Loop bs i "").toList := by
  induction hfuel : bs.size - i generalizing i with
  | zero => intro acc; rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]; simp [show ¬ i < bs.size by omega]
  | succ _ ih =>
      intro acc; have h : i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := ""), dite_eq_left h, dite_eq_left h]
      by_cases hu : isUnreserved bs[i] <;>
        (simp only [hu, Bool.false_eq_true, ↓reduceIte]; conv => rhs; rw [ih (i + 1) (by omega)]
         rw [ih (i + 1) (by omega)]; simp [String.toList_push, List.append_assoc])
private theorem decodeBytes_unreserved {b : UInt8} (hu : isUnreserved b = true) (rest : List Char) (acc : ByteArray) :
    decodeBytes (Char.ofNat b.toNat :: rest) acc = decodeBytes rest (acc.push b) := by
  have ⟨hle, hne37, htn⟩ := unreserved_toNat hu
  have hne : Char.ofNat b.toNat ≠ '%' := fun h => hne37 (htn ▸ congrArg Char.toNat h)
  have hstep : decodeBytes (Char.ofNat b.toNat :: rest) acc = decodeBytes rest (acc ++ (Char.ofNat b.toNat).toString.toUTF8) := by
    cases rest with | nil => simp [decodeBytes] | cons _ r => cases r <;> simp [decodeBytes, hne]
  have hutf : (Char.ofNat b.toNat).toString.toUTF8 = ByteArray.mk #[b] := by
    apply ByteArray.ext; change (String.ofList [Char.ofNat b.toNat]).toByteArray.data = #[b]
    rw [String.toByteArray_ofList, List.utf8Encode_singleton, String.utf8EncodeChar]
    simp only [show (Char.ofNat b.toNat).val.toNat = b.toNat from htn, show b.toNat ≤ 127 by omega, ↓reduceIte, UInt8.ofNat_toNat]; rfl
  rw [hstep, hutf]; congr 1; exact ByteArray.ext (by simp [ByteArray.push])
private theorem decodeBytes_encodeUTF8Loop (bs : ByteArray) (i : Nat) :
    ∀ (acc : ByteArray), i ≤ bs.size →
      (decodeBytes (encodeUTF8Loop bs i "").toList acc).data.toList = acc.data.toList ++ bs.data.toList.drop i := by
  induction hfuel : bs.size - i generalizing i with
  | zero => intro acc hi; obtain rfl : i = bs.size := (by omega); rw [encodeUTF8Loop.eq_1, dite_eq_right (Nat.lt_irrefl _)]; simp [List.drop_eq_nil_iff, decodeBytes]
  | succ _ ih =>
      intro acc hi; have hlt : i < bs.size := (by omega)
      have hdrop : bs.data.toList.drop i = bs[i] :: bs.data.toList.drop (i + 1) := (List.getElem_cons_drop (by simpa using hlt)).symm
      suffices h : decodeBytes (encodeUTF8Loop bs i "").toList acc = decodeBytes (encodeUTF8Loop bs (i + 1) "").toList (acc.push bs[i]) by
        rw [h, ih (i + 1) (by omega) (acc.push bs[i]) (by omega), hdrop]; simp [ByteArray.push, List.append_assoc]
      rw [encodeUTF8Loop.eq_1 (acc := ""), dite_eq_left hlt, encodeUTF8Loop_toList]
      by_cases hu : isUnreserved bs[i]
      · simp only [hu, ↓reduceIte, String.toList_push, String.toList_empty, List.nil_append, List.singleton_append]; exact decodeBytes_unreserved hu _ _
      · have ⟨hrecBV, hhiLt, hloLt⟩ := bitvec8_nibbles bs[i].toBitVec
        simp only [hu, Bool.false_eq_true, ↓reduceIte, String.toList_push, String.toList_empty, List.nil_append, List.cons_append]
        rw [decodeBytes.eq_def]
        simp only [unhex_hexDigit (bs[i] >>> 4) hhiLt, unhex_hexDigit (bs[i] &&& 0x0F) hloLt]
        exact congrArg (fun x => decodeBytes _ (acc.push x)) (UInt8.eq_of_toBitVec_eq hrecBV)
@[simp] theorem decodeSeg_encodeSeg (s : String) : decodeSeg (encodeSeg s) = s := by
  have hdata := decodeBytes_encodeUTF8Loop s.toUTF8 0 .empty (Nat.zero_le _); simp only [List.drop_zero, ByteArray.empty] at hdata
  have hba : decodeBytes (encodeSeg s).toList .empty = s.toUTF8 := ByteArray.ext (congrArg List.toArray (by simpa [encodeSeg] using hdata))
  rw [decodeSeg, hba, String.toUTF8, String.fromUTF8?, dite_eq_left s.isValidUTF8]; rfl

private theorem isPctEncodedChar_props {c : Char} (h : isPctEncodedChar c = true) : c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' := by
  simp only [isPctEncodedChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> simp at h
private theorem not_slash_of_pct {cs : List Char} (hp : cs.all isPctEncodedChar = true) : '/' ∉ cs := fun hm =>
  (isPctEncodedChar_props (List.all_eq_true.1 hp '/' hm)).1 rfl
private theorem splitSlash_joinSlash : ∀ (segs : List String),
    (∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true) → (Str.splitCharAux '/' [] [] (joinSlash segs).toList).filter (· ≠ "") = segs
  | [], _ => rfl
  | [s], hs => by
      have ⟨hne, hp⟩ := hs s (.head _)
      rw [joinSlash, Str.splitCharAux_not_mem '/' s.toList [] [] (not_slash_of_pct hp)]
      simp [String.ofList_toList, hne]
  | s₁ :: s₂ :: rest, hs => by
      have ⟨hne1, hp1⟩ := hs s₁ (.head _)
      rw [show (joinSlash (s₁ :: s₂ :: rest)).toList = s₁.toList ++ ('/' :: (joinSlash (s₂ :: rest)).toList) by simp [joinSlash, String.toList_append],
        Str.splitCharAux_append_not_mem '/' s₁.toList _ [] [] (not_slash_of_pct hp1),
        Str.splitCharAux_acc '/' _ [] _]
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList, List.reverse_singleton, List.singleton_append,
        List.filter_cons, decide_eq_true hne1, ↓reduceIte]
      exact congrArg (s₁ :: ·) (splitSlash_joinSlash (s₂ :: rest) fun x hx => hs x (.tail _ hx))
theorem Router.fromURL_toURL {α : Type} [Router α] (a : α) (hne : ∀ s ∈ Router.print a, s ≠ "") :
    Router.fromURL (Router.toURL a) = some a := by
  unfold Router.fromURL Router.toURL splitSlash Str.splitChar stripQueryAndHash; rw [String.toList_ofList]
  let segs := (Router.print a).map encodeSeg
  have hnonempty : ∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true := fun s hs => by
    rcases List.mem_map.1 hs with ⟨raw, hraw, rfl⟩
    exact ⟨fun h => hne raw hraw (by rw [← decodeSeg_encodeSeg raw, h]; rfl), encodeSeg_pct raw⟩
  have hdrop : (joinSlash segs).toList.dropWhile (· == '/') = (joinSlash segs).toList := by
    cases hxs : segs with | nil => rfl | cons x xs =>
      have ⟨hxne, hxpct⟩ := hnonempty x (by simp [hxs])
      cases hxl : x.toList with
      | nil => exact absurd (by simpa [String.ofList_toList] using congrArg String.ofList hxl) hxne
      | cons c _ =>
          have hc := beq_eq_false_iff_ne.2 (isPctEncodedChar_props (List.all_eq_true.1 hxpct c (by simp [hxl]))).1
          cases xs <;> simp [joinSlash, String.toList_append, hxl, hc]
  have hall : (joinSlash segs).toList.all (fun c => c != '#' && c != '?') = true :=
    joinSlash_all _ rfl _ fun s hs => List.all_eq_true.2 fun c hc => by
      have ⟨_, hq, hh⟩ := isPctEncodedChar_props (List.all_eq_true.1 (hnonempty s hs).2 c hc); simp [bne_iff_ne, hq, hh]
  rw [hdrop, String.toList_ofList, List.takeWhile_cons, ite_eq_left (by decide : ('/' != '#' && '/' != '?') = true),
    list_takeWhile_eq_self _ fun c hc => List.all_eq_true.1 hall c hc,
    show Str.splitCharAux '/' [] [] ('/' :: (joinSlash segs).toList) = "" :: Str.splitCharAux '/' [] [] (joinSlash segs).toList by
      simp only [Str.splitCharAux, beq_self_eq_true, ↓reduceIte]; rw [Str.splitCharAux_acc]; rfl]
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, splitSlash_joinSlash _ hnonempty]
  simp [segs, List.map_map, Function.comp_def, decodeSeg_encodeSeg, Router.round_trip]
theorem Router.canonical_reparse {α : Type} [Router α] (segs : List String) (a : α) (_h : Router.parse segs = some a) :
    Router.parse (Router.print a) = some a := Router.round_trip a
end Qed
