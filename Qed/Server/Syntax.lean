import Lean
import Qed.Server.Core

namespace Qed.Server

/-- Marker wrapper for binary Protocol Buffers request/response bodies on `external` endpoints. -/
structure ProtoBody (α : Type) where
  val : α
deriving Inhabited, DecidableEq, Repr

/-- Projects `Qed.Field p` to its underlying value `α` on both sides of server operators while
    leaving ordinary types untouched (`id`), enabling seamless arithmetic and `omega` proofs. -/
class SrvVal (α : Type) (β : outParam Type) where
  val : α → β

@[inline] instance {α : Type} {p : α → Prop} : SrvVal (Qed.Field p) α := ⟨Qed.Field.val⟩
@[inline] instance (priority := low) {α : Type} : SrvVal α α := ⟨id⟩

@[simp] theorem SrvVal.val_field {α : Type} {p : α → Prop} (f : Qed.Field p) :
    SrvVal.val f = f.val := rfl

@[simp] theorem SrvVal.val_id {α : Type} (x : α) :
    SrvVal.val x = x := rfl

/-! ## Brace-Free Indentation Grammar (`srvType`, `srvExpr`, `srvStmt`, `external`, `server`, `fullstack`) -/

declare_syntax_cat srvType
declare_syntax_cat srvTypeMod
declare_syntax_cat srvExpr
declare_syntax_cat srvCallArg
declare_syntax_cat srvStmt
declare_syntax_cat extClause
declare_syntax_cat extParam
declare_syntax_cat srvClause
declare_syntax_cat fullstackClause

section SrvParsers
open Lean Parser

private def kw (s : String) : Parser :=
  nonReservedSymbol s (includeIdent := true)

-- Postfix type modifiers: `T`, `T[]`, `T?`, `T!`
@[srvTypeMod_parser] def srvTypeModArr : Parser := leading_parser atomic ("[" >> "]")
@[srvTypeMod_parser] def srvTypeModOpt : Parser := leading_parser symbol "?"
@[srvTypeMod_parser] def srvTypeModErr : Parser := leading_parser symbol "!"

@[srvType_parser] def srvTypeProto : Parser := leading_parser
  atomic (identEq `Proto >> checkNoWsBefore "" >> "(") >> ident >> ")" >> many (categoryParser `srvTypeMod 0)

@[srvType_parser] def srvTypePlain : Parser := leading_parser
  ident >> many (categoryParser `srvTypeMod 0)

-- Call arguments (named `field = val` or positional `val`)
@[srvCallArg_parser] def srvCallArgNamed : Parser := leading_parser
  atomic (ident >> " = ") >> categoryParser `srvExpr 0

@[srvCallArg_parser] def srvCallArgPos : Parser := leading_parser
  categoryParser `srvExpr 0

-- Expression atoms (note `true`, `false`, `none`, `old(...)`, `fail(...)` are handled cleanly via `ident` / `srvCall` without reserving global keywords!)
@[srvExpr_parser] def srvLitNum  : Parser := leading_parser:maxPrec numLit
@[srvExpr_parser] def srvLitSci  : Parser := leading_parser:maxPrec scientificLit
@[srvExpr_parser] def srvLitStr  : Parser := leading_parser:maxPrec strLit
@[srvExpr_parser] def srvLitChar : Parser := leading_parser:maxPrec charLit
@[srvExpr_parser] def srvInterp  : Parser := leading_parser:maxPrec
  atomic (symbol "s!" >> checkNoWsBefore "") >> interpolatedStr (categoryParser `srvExpr 0)
@[srvExpr_parser] def srvArrLit  : Parser := leading_parser:maxPrec "[" >> sepBy (categoryParser `srvExpr 0) "," >> "]"
@[srvExpr_parser] def srvParen   : Parser := leading_parser:maxPrec "(" >> sepBy (categoryParser `srvExpr 0) "," >> ")"
@[srvExpr_parser] def srvIdent   : Parser := leading_parser:maxPrec ident

-- Postfix operators (`noWs` prevents cross-line ambiguity in indentation blocks!)
syntax:90 (name := srvCall)   srvExpr:90 noWs "(" srvCallArg,* ")" : srvExpr
syntax:90 (name := srvIndex)  srvExpr:90 noWs "[" srvExpr "]" : srvExpr
syntax:90 (name := srvProj)   srvExpr:90 noWs "." noWs ident : srvExpr
syntax:90 (name := srvUnwrap) srvExpr:90 noWs "?" : srvExpr

-- Prefix operators (`!`, `-`)
syntax:80 (name := srvNot) "!" srvExpr:80 : srvExpr
syntax:80 (name := srvNeg) "-" srvExpr:80 : srvExpr

-- Multiplicative & additive
syntax:70 (name := srvMul) srvExpr:70 " * "  srvExpr:71 : srvExpr
syntax:70 (name := srvDiv) srvExpr:70 " / "  srvExpr:71 : srvExpr
syntax:70 (name := srvMod) srvExpr:70 " % "  srvExpr:71 : srvExpr
syntax:65 (name := srvAdd) srvExpr:65 " + "  srvExpr:66 : srvExpr
syntax:65 (name := srvSub) srvExpr:65 " - "  srvExpr:66 : srvExpr
syntax:65 (name := srvCat) srvExpr:65 " ++ " srvExpr:66 : srvExpr

-- Comparisons
syntax:50 (name := srvEq) srvExpr:51 " == " srvExpr:51 : srvExpr
syntax:50 (name := srvNe) srvExpr:51 " != " srvExpr:51 : srvExpr
syntax:50 (name := srvLe) srvExpr:51 " <= " srvExpr:51 : srvExpr
syntax:50 (name := srvGe) srvExpr:51 " >= " srvExpr:51 : srvExpr
syntax:50 (name := srvLt) srvExpr:51 " < "  srvExpr:51 : srvExpr
syntax:50 (name := srvGt) srvExpr:51 " > "  srvExpr:51 : srvExpr

-- Logical connectives
syntax:35 (name := srvAnd) srvExpr:36 " && " srvExpr:35 : srvExpr
syntax:30 (name := srvOr)  srvExpr:31 " || " srvExpr:30 : srvExpr

@[srvExpr_parser] def srvAwait : Parser := leading_parser:75
  atomic (kw "await") >> categoryParser `srvExpr 75

@[srvExpr_parser] def srvLam1 : Parser := leading_parser:20
  atomic (ident >> " => ") >> categoryParser `srvExpr 20

@[srvExpr_parser] def srvLamN : Parser := leading_parser:20
  atomic ("(" >> sepBy ident "," >> ")" >> " => ") >> categoryParser `srvExpr 20

@[srvExpr_parser] def srvForall : Parser := leading_parser:15
  atomic (kw "forall" >> ident >> kw "in") >> categoryParser `srvExpr 50 >> ", " >> categoryParser `srvExpr 15

-- Statements inside `server` functions
def srvCatchBinder : Parser := ident <|> symbol "_"

def srvBlock : Parser :=
  checkColGt "expected indented block" >> many1Indent (categoryParser `srvStmt 0)

@[srvStmt_parser] def srvStmtReturn : Parser := leading_parser
  withPosition ("return" >> optional (checkLineEq >> categoryParser `srvExpr 0))

@[srvStmt_parser] def srvStmtAtomic : Parser := leading_parser
  withPosition (atomic (kw "atomic") >> srvBlock)

@[srvStmt_parser] def srvStmtLetAtomic : Parser := leading_parser
  withPosition (atomic ("let " >> ident >> " = " >> kw "atomic") >> srvBlock)

@[srvStmt_parser] def srvStmtLetCatch : Parser := leading_parser
  withPosition (
    atomic ("let " >> srvCatchBinder >> " = " >> categoryParser `srvExpr 0 >> kw "catch") >>
    srvCatchBinder >> srvBlock)

@[srvStmt_parser] def srvStmtLet : Parser := leading_parser
  withPosition ("let " >> srvCatchBinder >> " = " >> categoryParser `srvExpr 0)

@[srvStmt_parser] def srvStmtIfLet : Parser := leading_parser
  withPosition (
    atomic ("if " >> "let ") >> ident >> " = " >> categoryParser `srvExpr 0 >>
    srvBlock >>
    optional (atomic (checkColEq >> "else") >>
      ((checkLineEq >> categoryParser `srvStmt 0) <|> srvBlock)))

@[srvStmt_parser] def srvStmtIf : Parser := leading_parser
  withPosition (
    "if " >> categoryParser `srvExpr 0 >>
    srvBlock >>
    optional (atomic (checkColEq >> "else") >>
      ((checkLineEq >> categoryParser `srvStmt 0) <|> srvBlock)))

@[srvStmt_parser] def srvStmtAssign : Parser := leading_parser
  withPosition (
    atomic (categoryParser `srvExpr 90 >>
      (symbol " = " <|> symbol " += " <|> symbol " -= ")) >>
    categoryParser `srvExpr 0)

@[srvStmt_parser] def srvStmtExpr : Parser := leading_parser
  withPosition (categoryParser `srvExpr 0)

-- `external` clauses & command
@[extParam_parser] def extParamHeader : Parser := leading_parser
  atomic (identEq `header >> checkNoWsBefore "" >> "(") >> strLit >> ")" >> ident >> ":" >> categoryParser `srvType 0

@[extParam_parser] def extParamPlain : Parser := leading_parser
  ident >> ":" >> categoryParser `srvType 0

@[extClause_parser] def extBaseClause : Parser := leading_parser
  withPosition (atomic (identEq `base) >> strLit)

@[extClause_parser] def extAuthBearer : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `bearer) >>
    "(" >> identEq `secret >> "(" >> strLit >> ")" >> ")")

@[extClause_parser] def extAuthHeader : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `header) >>
    "(" >> strLit >> ", " >> identEq `secret >> "(" >> strLit >> ")" >> ")")

@[extClause_parser] def extAuthGcp : Parser := leading_parser
  withPosition (
    atomic (identEq `auth >> identEq `gcpServiceAccount) >>
    "(" >> identEq `secret >> "(" >> strLit >> ")" >>
    optional (", " >> strLit) >> ")")

def extHttpMethod : Parser :=
  identEq `get <|> identEq `post <|> identEq `put <|> identEq `patch <|> identEq `delete

@[extClause_parser] def extEndpointClause : Parser := leading_parser
  withPosition (
    extHttpMethod >> strLit >>
    checkColGt "expected endpoint signature" >>
    ident >> checkNoWsBefore "" >> "(" >> sepBy (categoryParser `extParam 0) "," >> ")" >>
    " -> " >> categoryParser `srvType 0)

@[command_parser] def externalCmd : Parser := leading_parser
  withPosition (
    "external " >> ident >>
    checkColGt "expected indented `external` clauses" >>
    many1Indent (categoryParser `extClause 0))

-- `server` & `fullstack` clauses & commands
def srvParam : Parser :=
  node `Qed.Server.srvParam (ident >> ":" >> categoryParser `srvType 0)

@[srvClause_parser] def srvEnvClause : Parser := leading_parser
  withPosition (atomic (identEq `env) >> ident >> " = " >> strLit >> optional (" ?? " >> strLit))

@[srvClause_parser] def srvStateClause : Parser := leading_parser
  withPosition (atomic (identEq `state) >> ident >> ":" >> categoryParser `srvType 0 >> " = " >> categoryParser `srvExpr 0)

@[srvClause_parser] def srvInvMutatingClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> identEq `mutating) >>
    ident >> kw "requires" >> categoryParser `srvExpr 0)

@[srvClause_parser] def srvInvClause : Parser := leading_parser
  withPosition ("invariant " >> categoryParser `srvExpr 0)

def srvRequiresLine : Parser :=
  node `Qed.Server.srvRequiresLine (withPosition (atomic (identEq `requires) >> categoryParser `srvExpr 0))

@[srvClause_parser] def srvFnClause : Parser := leading_parser
  withPosition (
    atomic (identEq `fn) >> ident >> checkNoWsBefore "" >> "(" >> sepBy srvParam "," >> ")" >>
    " -> " >> categoryParser `srvType 0 >>
    checkColGt "expected indented function body" >>
    withPosition (
      many (atomic (checkColGe "requires" >> srvRequiresLine)) >>
      many1 (checkColGe "statement" >> categoryParser `srvStmt 0)))

@[command_parser] def serverCmd : Parser := leading_parser
  withPosition (
    "server " >> ident >>
    checkColGt "expected indented `server` body" >>
    many1Indent (categoryParser `srvClause 0))

@[fullstackClause_parser] def fsServerClause : Parser := leading_parser
  withPosition ("server " >> ident)

@[fullstackClause_parser] def fsClientClause : Parser := leading_parser
  withPosition (atomic (identEq `client) >> ident)

@[fullstackClause_parser] def fsTitleClause : Parser := leading_parser
  withPosition (atomic (identEq `title) >> strLit)

@[command_parser] def fullstackCmd : Parser := leading_parser
  withPosition (
    "fullstack " >> ident >>
    checkColGt "expected indented `fullstack` clauses" >>
    many1Indent (categoryParser `fullstackClause 0))

end SrvParsers

/-! ## Parsed Type Representation & Lowering Helpers -/

inductive SrvTypeMod where
  | array    -- T[]
  | option   -- T?
  | fallible -- T!
deriving Inhabited, DecidableEq, Repr

structure ParsedSrvType where
  ref       : Lean.Syntax
  baseIdent : Lean.Ident
  isProto   : Bool := false
  mods      : Array SrvTypeMod := #[]

namespace ParsedSrvType

/-- Splits trailing `?` and `!` characters that Lean's lexer attaches to identifiers (`Book?`, `Book!`). -/
private def splitIdentMods (id : Lean.Ident) : Lean.MacroM (Lean.Ident × Array SrvTypeMod) := do
  let raw := id.getId.toString
  let chars := raw.toList
  let revMods := chars.reverse.takeWhile (fun c => c == '?' || c == '!')
  let baseChars := chars.take (chars.length - revMods.length)
  if baseChars.isEmpty then
    Lean.Macro.throwErrorAt id s!"invalid type `{raw}`"
  let mut mods : Array SrvTypeMod := #[]
  for c in revMods.reverse do
    if c == '?' then mods := mods.push SrvTypeMod.option
    else if c == '!' then mods := mods.push SrvTypeMod.fallible
  let baseStr := String.ofList baseChars
  let baseName := (baseStr.splitOn ".").foldl (fun acc seg => Lean.Name.str acc seg) .anonymous
  return (Lean.mkIdentFrom id baseName, mods)

private def parseModNode (m : Lean.Syntax) : Lean.MacroM SrvTypeMod := do
  let k := m.getKind
  if k == ``srvTypeModArr then return SrvTypeMod.array
  else if k == ``srvTypeModOpt then return SrvTypeMod.option
  else if k == ``srvTypeModErr then return SrvTypeMod.fallible
  else
    let s := (m.reprint.getD "").trimAscii.toString
    if s == "[]" then return SrvTypeMod.array
    else if s == "?" then return SrvTypeMod.option
    else if s == "!" then return SrvTypeMod.fallible
    else Lean.Macro.throwErrorAt m s!"unknown type modifier `{s}`"

def parse (stx : Lean.Syntax) : Lean.MacroM ParsedSrvType := do
  let k := stx.getKind
  if k == ``srvTypeProto then
    -- args: `Proto`, `(`, ident, `)`, many mods
    let id : Lean.Ident := ⟨stx[2]⟩
    let (baseId, initMods) ← splitIdentMods id
    let extraMods ← stx[4].getArgs.mapM parseModNode
    return { ref := stx, baseIdent := baseId, isProto := true, mods := initMods ++ extraMods }
  else if k == ``srvTypePlain then
    -- args: ident, many mods
    let id : Lean.Ident := ⟨stx[0]⟩
    let (baseId, initMods) ← splitIdentMods id
    let extraMods ← stx[1].getArgs.mapM parseModNode
    return { ref := stx, baseIdent := baseId, isProto := false, mods := initMods ++ extraMods }
  else
    Lean.Macro.throwErrorAt stx "expected a type (`T`, `T[]`, `T?`, `T!`, or `Proto(T)`)"

def hasFallible (t : ParsedSrvType) : Bool :=
  t.mods.contains SrvTypeMod.fallible

def isOuterOption (t : ParsedSrvType) : Bool :=
  t.mods.back? == some SrvTypeMod.option

/-- Validates that `!` only appears at the outermost position when permitted. -/
def validate (t : ParsedSrvType) (allowFallible : Bool) (ctxDesc : String) : Lean.MacroM Unit := do
  if !allowFallible && t.hasFallible then
    Lean.Macro.throwErrorAt t.ref s!"fallible `!` modifier is not allowed on {ctxDesc}; only `fn` return types may use `T!`"
  for i in [0:t.mods.size] do
    if t.mods[i]! == SrvTypeMod.fallible && i + 1 < t.mods.size then
      Lean.Macro.throwErrorAt t.ref "place `!` last on fallible return types (for example `Book[]!` instead of `Book![]`)"

/-- Lowers the non-`!` payload type (e.g. `Book[]!` → `Array Book`, `Book?` → `Option Book`). -/
def toPayloadTerm (t : ParsedSrvType) : Lean.MacroM Lean.Term := do
  let initAcc : Lean.Term ←
    if t.baseIdent.getId == `Bytes then `(Qed.Bytes)
    else if t.baseIdent.getId == `Json then `(Qed.Json)
    else if t.baseIdent.getId == `WebhookUrl then `(Qed.Server.WebhookUrl)
    else pure ⟨t.baseIdent.raw⟩
  let mut acc : Lean.Term := initAcc
  for m in t.mods do
    match m with
    | SrvTypeMod.array    => acc ← `(Array $acc)
    | SrvTypeMod.option   => acc ← `(Option $acc)
    | SrvTypeMod.fallible => pure ()
  return acc

/-- Lowers the full return type including `Except ApiError` if `!` is present. -/
def toFullTerm (t : ParsedSrvType) : Lean.MacroM Lean.Term := do
  let payload ← t.toPayloadTerm
  if t.hasFallible then
    `(Except Qed.Server.ApiError $payload)
  else
    return payload

end ParsedSrvType

end Qed.Server
