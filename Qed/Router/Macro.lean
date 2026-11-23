import Qed.Router.Basic
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
def routeParamP : Parser := node `Qed.routeParam (ident >> optional (":" >> categoryParser `qedType 0))
def routeAltP : Parser := node `Qed.routeAlt (withPosition
  (optional (symbol "*") >> ident >> optional (checkLineEq >> "(" >> sepBy1 routeParamP "," >> ")") >> optional ("=" >> strLit)))
@[command_parser] def routerCmd : Parser := leading_parser withPosition
  ("router " >> ident >> ":" >> checkColGt "expected indented `router` routes" >> many1Indent routeAltP)
end RouterParsers

section RouterElab
open Lean
@[macro routeEnumCmd] def expandRouteEnumCmd : Macro := fun stx => do
  let t : Ident := ⟨stx.getArg 1⟩
  let (toSegId, fromSegId, rtId) := (mkIdent (t.getId ++ `toSeg), mkIdent (t.getId ++ `fromSeg), mkIdent (t.getId ++ `round_trip))
  let rows ← (stx.getArg 3).getArgs.mapM fun alt => do
    let c : Ident := ⟨alt.getArg 0⟩; let ctorId := mkIdent (t.getId ++ c.getId)
    let slug : TSyntax `term := if (alt.getArg 1).getNumArgs == 2 then ⟨(alt.getArg 1).getArg 1⟩ else quote (toString c.getId)
    pure (c, (ctorId : TSyntax `term), slug, ← `(some $ctorId))
  let (ctors, ctorPats, slugs) := (rows.map (·.1), rows.map (·.2.1), rows.map (·.2.2.1))
  let parsePats := slugs.push (← `(_)); let parseRhss := (rows.map (·.2.2.2)).push (← `(none))
  `(inductive $t:ident where $[| $ctors:ident]*
    deriving Repr, DecidableEq, Inhabited
    def $toSegId:ident (x : $t) : String := match x with $[| $ctorPats:term => $slugs:term]*
    def $fromSegId:ident (s : String) : Option $t := match s with $[| $parsePats:term => $parseRhss:term]*
    theorem $rtId:ident : ∀ a, $fromSegId:ident ($toSegId:ident a) = some a := by intro a; cases a <;> rfl
    instance : RouteParam $t:ident := ⟨$toSegId, $fromSegId, $rtId⟩)

private abbrev RouteRow := TSyntax `ident × Array (TSyntax `ident) × Array (TSyntax `term) × TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term
@[macro routerCmd] def expandRouterCmd : Macro := fun stx => do
  let t : Ident := ⟨stx.getArg 1⟩
  let err (s : Syntax) (msg : String) := Macro.throwErrorAt s s!"router `{t.getId}`: {msg}"
  let (printId, parseId, rtId) := (mkIdent (t.getId ++ `print), mkIdent (t.getId ++ `parse), mkIdent (t.getId ++ `round_trip))
  let (rows, _, markedCtor) ← (stx.getArg 3).getArgs.foldlM
    (init := ((#[], #[], none) : Array RouteRow × Array (TSyntax `ident × Array (Option String)) × Option (TSyntax `ident)))
    fun (rows, patShapes, markedCtor) alt => do
      let (marked, c) := ((alt.getArg 0).getNumArgs == 1, (⟨alt.getArg 1⟩ : Ident))
      let rawBs := if (alt.getArg 2).getNumArgs == 3 then ((alt.getArg 2).getArg 1).getSepArgs else #[]
      let seg : Option (TSyntax `str) := if (alt.getArg 3).getNumArgs == 2 then some ⟨(alt.getArg 3).getArg 1⟩ else none
      let explicitBs : Array (Ident × Term) ← rawBs.mapM fun b => do
        return (⟨b.getArg 0⟩, ← if (b.getArg 1).getNumArgs == 2 then do pure (← Qed.Lang.lowerQedType ((b.getArg 1).getArg 1) false).1 else `(String))
      let rawSegs := seg.elim #[toString c.getId] fun s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray
      let pathDesc := seg.elim s!"`/{c.getId}`" fun s => s!"`{s.getString}`"
      let (bs, bts, segments) ← if rawSegs.any (·.startsWith ":") then do
        let (bs, bts, segs, seen) ← rawSegs.foldlM (init := (#[], #[], (#[] : Array (Sum String Ident)), #[])) fun (bs, bts, segs, seen) rs => do
          if !rs.startsWith ":" then return (bs, bts, segs.push (.inl rs), seen)
          let pname := String.ofList (rs.toList.drop 1)
          if pname.isEmpty then err alt s!"route `{c.getId}` has an empty `:` parameter in path {pathDesc}"
          if seen.contains pname then err alt s!"route `{c.getId}` has duplicate `:{pname}` parameter in path {pathDesc}"
          let (b, bt) ← (explicitBs.find? (toString ·.1.getId == pname)).elim (do pure (mkIdent (Name.mkSimple pname), ← `(String))) pure
          return (bs.push b, bts.push bt, segs.push (.inr b), seen.push pname)
        for (b, _) in explicitBs do
          unless seen.contains (toString b.getId) do err b s!"parameter `{b.getId}` on route `{c.getId}` is not referenced as `:{b.getId}` in path {pathDesc}"
        pure (bs, bts, segs)
      else pure (explicitBs.map (·.1), explicitBs.map (·.2), rawSegs.map Sum.inl ++ (explicitBs.map (·.1)).map Sum.inr)
      let patShape := segments.map fun | .inl s => some s | .inr _ => none
      for (prevC, prevPat) in patShapes do
        if prevPat.size == patShape.size && (prevPat.zip patShape).all (fun | (some a, some b) => a == b | _ => true) then
          err c s!"route `{c.getId}` overlaps with earlier route `{prevC.getId}` (both match {patShape.size}-segment paths)"
      let ctorId := mkIdent (t.getId ++ c.getId)
      let printSeg ← segments.mapM fun | .inl s => pure (quote s : TSyntax `term) | .inr b => `(RouteParam.toSeg $(⟨b.raw⟩))
      let parseSeg : Array (TSyntax `term) := segments.map fun | .inl s => quote s | .inr b => ⟨b.raw⟩
      let parseBody ← (bs.zip bts).foldrM (init := ← `(some ($ctorId $bs*))) fun (b, bt) body =>
        let bT : TSyntax `term := ⟨b.raw⟩; `(match (RouteParam.fromSeg $bT : Option $bt) with | some $bT => $body | none => none)
      let markedCtor' ← if marked then
        if let some prevC := markedCtor then err c s!"duplicate fallback route `*` on `{c.getId}` (already marked on `{prevC.getId}`)"
        if bs.size != 0 then err c s!"fallback route `{c.getId}` (marked `*`) must take no arguments because it handles arbitrary unmatched URLs"
        pure (some c)
      else pure markedCtor
      let row : RouteRow := (c, bs, bts, ← `($ctorId $bs*), ← `([$printSeg,*]), ← `([$parseSeg,*]), parseBody)
      pure (rows.push row, patShapes.push (c, patShape), markedCtor')
  let (ctorNames, ctorBs, ctorBts) := (rows.map (·.1), rows.map (·.2.1), rows.map (·.2.2.1))
  let (printPats, printRhss) := (rows.map (·.2.2.2.1), rows.map (·.2.2.2.2.1))
  let parsePatsAll := (rows.map (·.2.2.2.2.2.1)).push (← `(_)); let parseRhssAll := (rows.map (·.2.2.2.2.2.2)).push (← `(none))
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
    instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩)
end RouterElab
end Qed
