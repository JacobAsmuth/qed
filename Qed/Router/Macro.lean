import Qed.Router.Basic
import Qed.Lang
import Lean

namespace Qed

syntax:max (name := qedArrType) term:max noWs "[" "]" : term
syntax:max (name := qedOptType) term:max noWs "?" : term
@[macro qedArrType] def expandQedArrType : Lean.Macro := fun stx => `(Array $(⟨(stx.getArg 0)⟩))
@[macro qedOptType] def expandQedOptType : Lean.Macro := fun stx => `(Option $(⟨(stx.getArg 0)⟩))

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

open Lean in
@[macro routeEnumCmd] def expandRouteEnumCmd : Macro
  | stx => do
      let t : Ident := ⟨(stx.getArg 1)⟩
      let alts := (stx.getArg 3).getArgs
      let toSegId   := mkIdent (t.getId ++ `toSeg)
      let fromSegId := mkIdent (t.getId ++ `fromSeg)
      let rtId      := mkIdent (t.getId ++ `round_trip)
      let mut ctors : Array (TSyntax `ident) := #[]
      let mut ctorPats : Array (TSyntax `term) := #[]
      let mut slugs : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      for alt in alts do
        let c : Ident := ⟨(alt.getArg 0)⟩
        let seg : Option (TSyntax `str) := if (alt.getArg 1).getNumArgs == 2 then some ⟨((alt.getArg 1).getArg 1)⟩ else none
        let ctorId := mkIdent (t.getId ++ c.getId)
        let slugLit : TSyntax `term := match seg with
          | some s => ⟨s.raw⟩
          | none   => quote (toString c.getId)
        ctors     := ctors.push c
        ctorPats  := ctorPats.push ctorId
        slugs     := slugs.push slugLit
        parseRhss := parseRhss.push (← `(some $ctorId))
      let parsePatsAll := slugs.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      `(inductive $t:ident where
          $[| $ctors:ident]*
        deriving Repr, DecidableEq, Inhabited
        def $toSegId:ident (x : $t) : String :=
          match x with
          $[| $ctorPats:term => $slugs:term]*
        def $fromSegId:ident (s : String) : Option $t :=
          match s with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $fromSegId:ident ($toSegId:ident a) = some a := by
          intro a; cases a <;> rfl
        instance : RouteParam $t:ident := ⟨$toSegId, $fromSegId, $rtId⟩)

open Lean in
private def parseRouteParam (b : Syntax) : MacroM (TSyntax `ident × TSyntax `term) := do
  let ty ← if (b.getArg 1).getNumArgs == 2 then do pure (← Qed.Lang.lowerQedType ((b.getArg 1).getArg 1) false).1 else `(String)
  pure (⟨(b.getArg 0)⟩, ty)

open Lean in
private def routePatternsOverlap (p₁ p₂ : Array (Option String)) : Bool :=
  p₁.size == p₂.size &&
  (List.range p₁.size).all fun i =>
    match p₁[i]!, p₂[i]! with
    | some a, some b => a == b
    | _, _           => true

open Lean in
@[macro routerCmd] def expandRouterCmd : Macro
  | stx => do
      let t : Ident := ⟨(stx.getArg 1)⟩
      let alts := (stx.getArg 3).getArgs
      let printId := mkIdent (t.getId ++ `print)
      let parseId := mkIdent (t.getId ++ `parse)
      let rtId    := mkIdent (t.getId ++ `round_trip)
      let mut ctorNames : Array (TSyntax `ident) := #[]
      let mut ctorBs    : Array (Array (TSyntax `ident)) := #[]
      let mut ctorBts   : Array (Array (TSyntax `term))  := #[]
      let mut printPats : Array (TSyntax `term) := #[]
      let mut printRhss : Array (TSyntax `term) := #[]
      let mut parsePats : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      let mut patShapes : Array (TSyntax `ident × Array (Option String)) := #[]
      let mut markedCtor : Option (TSyntax `ident) := none
      for alt in alts do
        let marked := (alt.getArg 0).getNumArgs == 1
        let c : Ident := ⟨(alt.getArg 1)⟩
        let rawBinders := if (alt.getArg 2).getNumArgs == 3 then ((alt.getArg 2).getArg 1).getSepArgs else #[]
        let seg : Option (TSyntax `str) := if (alt.getArg 3).getNumArgs == 2 then some ⟨((alt.getArg 3).getArg 1)⟩ else none
        let explicitBinders ← rawBinders.mapM parseRouteParam
        let rawSegs : Array String := match seg with
          | some s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray
          | none   => #[toString c.getId]
        let hasPlaceholders := rawSegs.any (·.startsWith ":")
        let mut bs     : Array (TSyntax `ident) := #[]
        let mut btsArr : Array (TSyntax `term)  := #[]
        let mut segments : Array (Sum String (TSyntax `ident)) := #[]
        let pathDesc := match seg with | some s => s!"`{s.getString}`" | none => s!"`/{c.getId}`"
        if hasPlaceholders then
          let mut seenPlaceholders : Array String := #[]
          for rs in rawSegs do
            if rs.startsWith ":" then
              let pname := String.ofList (rs.toList.drop 1)
              if pname.isEmpty then
                Macro.throwErrorAt alt s!"router `{t.getId}`: route `{c.getId}` has an empty `:` parameter in path {pathDesc}"
              if seenPlaceholders.contains pname then
                Macro.throwErrorAt alt s!"router `{t.getId}`: route `{c.getId}` has duplicate `:{pname}` parameter in path {pathDesc}"
              seenPlaceholders := seenPlaceholders.push pname
              let (b, bt) ← match explicitBinders.find? (fun (b, _) => toString b.getId == pname) with
                | some pair => pure pair
                | none => pure (mkIdent (Name.mkSimple pname), ← `(String))
              bs := bs.push b; btsArr := btsArr.push bt; segments := segments.push (.inr b)
            else
              segments := segments.push (.inl rs)
          for (b, _) in explicitBinders do
            unless seenPlaceholders.contains (toString b.getId) do
              Macro.throwErrorAt b s!"router `{t.getId}`: parameter `{b.getId}` on route `{c.getId}` is not referenced as `:{b.getId}` in path {pathDesc}"
        else
          bs := explicitBinders.map (·.1)
          btsArr := explicitBinders.map (·.2)
          segments := rawSegs.map .inl ++ bs.map .inr
        let ctorId := mkIdent (t.getId ++ c.getId)
        let patShape : Array (Option String) := segments.map fun | .inl s => some s | .inr _ => none
        for (prevC, prevPat) in patShapes do
          if routePatternsOverlap prevPat patShape then
            Macro.throwErrorAt c
              s!"router `{t.getId}`: route `{c.getId}` overlaps with earlier route `{prevC.getId}` (both match {patShape.size}-segment paths)"
        patShapes := patShapes.push (c, patShape)
        let printSeg ← segments.mapM fun
          | .inl s => pure (quote s : TSyntax `term)
          | .inr b => let bTerm : TSyntax `term := ⟨b.raw⟩; `(RouteParam.toSeg $bTerm)
        let parseSeg : Array (TSyntax `term) := segments.map fun
          | .inl s => quote s
          | .inr b => ⟨b.raw⟩
        let mut parseBody : TSyntax `term ← `(some ($ctorId $bs*))
        for i in (List.range bs.size).reverse do
          let bTerm : TSyntax `term := ⟨bs[i]!.raw⟩
          let bt := btsArr[i]!
          parseBody ← `(match (RouteParam.fromSeg $bTerm : Option $bt) with | some $bTerm => $parseBody | none => none)
        if marked then
          if let some prevC := markedCtor then
            Macro.throwErrorAt c s!"router `{t.getId}`: duplicate fallback route `*` on `{c.getId}` (already marked on `{prevC.getId}`)"
          if bs.size != 0 then
            Macro.throwErrorAt c s!"router `{t.getId}`: fallback route `{c.getId}` (marked `*`) must take no arguments because it handles arbitrary unmatched URLs"
          markedCtor := some c
        ctorNames := ctorNames.push c
        ctorBs    := ctorBs.push bs
        ctorBts   := ctorBts.push btsArr
        printPats := printPats.push (← `($ctorId $bs*))
        printRhss := printRhss.push (← `([$printSeg,*]))
        parsePats := parsePats.push (← `([$parseSeg,*]))
        parseRhss := parseRhss.push parseBody
      let parsePatsAll := parsePats.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      let inhCmd : TSyntax `command ← match markedCtor with
        | some mc => `(instance : Inhabited $t := ⟨$(mkIdent (t.getId ++ mc.getId))⟩)
        | none    => `(deriving instance Inhabited for $t)
      `(inductive $t:ident where
          $[| $ctorNames:ident $[($ctorBs:ident : $ctorBts:term)]*]*
        deriving Repr, DecidableEq
        $inhCmd:command
        def $printId:ident (r : $t) : List String :=
          match r with
          $[| $printPats:term => $printRhss:term]*
        def $parseId:ident (p : List String) : Option $t :=
          match p with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $parseId:ident ($printId:ident a) = some a := by
          intro a; cases a <;>
            (try simp only [$printId:ident, $parseId:ident, RouteParam.round_trip, RouteParam.toSeg_string]) <;>
            (try simp [$printId:ident, $parseId:ident, RouteParam.round_trip])
        instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩)

end Qed
