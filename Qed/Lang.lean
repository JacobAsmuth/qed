import Lean

namespace Qed.Lang

/-! ## Shared Runtime Typeclasses & Proof Helpers (Kernel-Reducible, Zero Overhead) -/

/-- Projects proof-carrying wrappers (`Qed.Field`, `Qed.Ensured`) to their underlying value `α`
    on operators while leaving plain values untouched (`id`). -/
class QedVal (α : Type) (β : outParam Type) where
  val : α → β

@[reducible, inline] instance (priority := low) {α : Type} : QedVal α α := ⟨id⟩
@[simp] theorem QedVal.val_id {α : Type} (x : α) : QedVal.val x = x := rfl

/-- Overloads Python-style `[a, b, c]` literals to produce `Array α` by default and `List α` when expected. -/
class QedSeqLit (α : Type) (C : Type) where
  ofList : List α → C

@[default_instance, reducible, inline] instance {α : Type} : QedSeqLit α (Array α) := ⟨List.toArray⟩
@[reducible, inline] instance {α : Type} : QedSeqLit α (List α) := ⟨id⟩
@[simp] theorem QedSeqLit.ofList_array {α : Type} (xs : List α) : (QedSeqLit.ofList xs : Array α) = xs.toArray := rfl
@[simp] theorem QedSeqLit.ofList_list {α : Type} (xs : List α) : (QedSeqLit.ofList xs : List α) = xs := rfl

/-- Boolean membership (`x in xs`) for runtime expressions. -/
class QedMem (α : Type) (C : Type) where
  mem : α → C → Bool

@[inline] instance {α : Type} [BEq α] : QedMem α (Array α) := ⟨fun x xs => xs.contains x⟩
@[inline] instance {α : Type} [BEq α] : QedMem α (List α) := ⟨fun x xs => xs.contains x⟩
@[inline] instance : QedMem Char String := ⟨fun c s => s.contains c⟩
@[simp] theorem QedMem.mem_array {α : Type} [BEq α] (x : α) (xs : Array α) : QedMem.mem x xs = xs.contains x := rfl
@[simp] theorem QedMem.mem_list {α : Type} [BEq α] (x : α) (xs : List α) : QedMem.mem x xs = xs.contains x := rfl
@[simp] theorem QedMem.mem_string (c : Char) (s : String) : QedMem.mem c s = s.contains c := rfl

/-- Propositional membership (`x in xs`) for invariants, guards, and schema `where` clauses. -/
class QedMemProp (α : Type) (C : Type) where
  memProp : α → C → Prop

@[reducible] instance {α : Type} : QedMemProp α (Array α) := ⟨fun x xs => x ∈ xs⟩
@[reducible] instance {α : Type} : QedMemProp α (List α) := ⟨fun x xs => x ∈ xs⟩
@[reducible] instance : QedMemProp Char String := ⟨fun c s => s.contains c = true⟩
@[simp] theorem QedMemProp.memProp_array {α : Type} (x : α) (xs : Array α) : QedMemProp.memProp x xs = (x ∈ xs) := rfl
@[simp] theorem QedMemProp.memProp_list {α : Type} (x : α) (xs : List α) : QedMemProp.memProp x xs = (x ∈ xs) := rfl
@[simp] theorem QedMemProp.memProp_string (c : Char) (s : String) : QedMemProp.memProp c s = (s.contains c = true) := rfl

instance {α : Type} [DecidableEq α] (x : α) (xs : Array α) : Decidable (QedMemProp.memProp x xs) :=
  inferInstanceAs (Decidable (x ∈ xs))
instance {α : Type} [DecidableEq α] (x : α) (xs : List α) : Decidable (QedMemProp.memProp x xs) :=
  inferInstanceAs (Decidable (x ∈ xs))
instance (c : Char) (s : String) : Decidable (QedMemProp.memProp c s) :=
  inferInstanceAs (Decidable (s.contains c = true))

/-- Dependent short-circuit conjunction preserving earlier index bounds hypotheses in `Prop`. -/
structure QedAndProp (P : Prop) (Q : P → Prop) : Prop where
  fst : P
  snd : Q fst

instance {P : Prop} {Q : P → Prop} [Decidable P] [∀ h, Decidable (Q h)] : Decidable (QedAndProp P Q) :=
  if hp : P then if hq : Q hp then isTrue ⟨hp, hq⟩ else isFalse fun ⟨_, hq'⟩ => hq hq'
  else isFalse fun ⟨hp', _⟩ => hp hp'

@[simp] theorem not_qedAndProp {P : Prop} {Q : P → Prop} : (¬ QedAndProp P Q) ↔ ∀ h : P, ¬ Q h :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

/-- Dependent short-circuit disjunction in `Prop`. -/
inductive QedOrProp (P : Prop) (Q : ¬ P → Prop) : Prop where
  | inl (h : P) : QedOrProp P Q
  | inr (hnp : ¬ P) (hq : Q hnp) : QedOrProp P Q

instance {P : Prop} {Q : ¬ P → Prop} [Decidable P] [∀ h, Decidable (Q h)] : Decidable (QedOrProp P Q) :=
  if hp : P then isTrue (.inl hp)
  else if hq : Q hp then isTrue (.inr hp hq)
  else isFalse fun | .inl hp' => hp hp' | .inr _ hq' => hq hq'

@[simp] theorem not_qedOrProp {P : Prop} {Q : ¬ P → Prop} : (¬ QedOrProp P Q) ↔ ¬ P ∧ ∀ h : ¬ P, ¬ Q h :=
  ⟨fun h => ⟨fun hp => h (.inl hp), fun hnp hq => h (.inr hnp hq)⟩,
   fun ⟨hnp, hnq⟩ => fun | .inl hp => hnp hp | .inr hnp' hq => hnq hnp' hq⟩

/-- Equality predicate helper: elaborates to decidable `a = b` when available, else `(a == b) = true`. -/
syntax (name := qedEqPropStx) "qedEqProp(" term ", " term ")" : term
/-- Lifts a `Bool` expression to `e = true` while leaving an already-`Prop` expression untouched. -/
syntax (name := qedAsPropStx) "qedAsProp(" term ")" : term

open Lean Meta Elab Term in
@[term_elab qedAsPropStx]
def elabQedAsProp : TermElab := fun stx _ => do
  let e ← instantiateMVars (← elabTerm (stx.getArg 1) none)
  let ty ← whnf (← inferType e)
  if ty.isProp then return e
  else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true)
  else ensureHasType (mkSort Level.zero) e

open Lean Meta Elab Term in
@[term_elab qedEqPropStx]
def elabQedEqProp : TermElab := fun stx _ => do
  let (aStx, bStx) : Term × Term := (⟨(stx.getArg 1)⟩, ⟨(stx.getArg 3)⟩)
  let savedMsgs ← Core.getMessageLog
  Core.resetMessageLog
  let eqTry? ← try
      let e ← elabTerm (← `(($aStx = $bStx))) (some (mkSort Level.zero))
      let newMsgs ← Core.getMessageLog
      if newMsgs.hasErrors then Core.setMessageLog savedMsgs; pure none
      else
        Core.setMessageLog (savedMsgs ++ newMsgs)
        if (← try synthInstance? (← mkAppM ``Decidable #[e]) catch _ => pure none).isSome then pure (some e)
        else pure none
    catch _ => Core.setMessageLog savedMsgs; pure none
  if let some e := eqTry? then return e
  elabTerm (← `(($aStx == $bStx) = true)) (some (mkSort Level.zero))

/-! ## Unified Python-esque Grammar (`qedType`, `qedPat`, `qedExpr`, `qedStmt`, `qedSuite`) -/

declare_syntax_cat qedType
declare_syntax_cat qedTypeMod
declare_syntax_cat qedCallArg
declare_syntax_cat qedPat
declare_syntax_cat qedExpr
declare_syntax_cat qedStmt

section Parsers
open Lean Parser

/-- Non-reserved keyword parser so English keywords never pollute Lean's global token table. -/
def kw (s : String) : Parser := nonReservedSymbol s (includeIdent := true)
def qedBinder : Parser := ident <|> symbol "_"

-- Types (`qedType`)
@[qedTypeMod_parser] def qedTypeModArr : Parser := leading_parser atomic ("[" >> "]")
@[qedTypeMod_parser] def qedTypeModOpt : Parser := leading_parser symbol "?"
@[qedTypeMod_parser] def qedTypeModErr : Parser := leading_parser symbol "!"

@[qedType_parser] def qedTypeProto : Parser := leading_parser:maxPrec
  atomic (kw "Proto" >> "(") >> ident >> ")" >> many (categoryParser `qedTypeMod 0)
@[qedType_parser] def qedTypeParen : Parser := leading_parser:maxPrec
  "(" >> sepBy1 (categoryParser `qedType 0) "," >> ")" >> many (categoryParser `qedTypeMod 0)
@[qedType_parser] def qedTypeAtom : Parser := leading_parser:maxPrec
  ident >> many (categoryParser `qedTypeMod 0)
@[qedType_parser 90] def qedTypeApp : TrailingParser := trailing_parser:90
  checkLineEq >> categoryParser `qedType 91
@[qedType_parser 25] def qedTypeArrow : TrailingParser := trailing_parser:25
  symbol "->" >> categoryParser `qedType 25

-- Patterns (`qedPat`)
@[qedPat_parser] def qedPatWild  : Parser := leading_parser:maxPrec symbol "_"
@[qedPat_parser] def qedPatNum   : Parser := leading_parser:maxPrec numLit
@[qedPat_parser] def qedPatStr   : Parser := leading_parser:maxPrec strLit
@[qedPat_parser] def qedPatChar  : Parser := leading_parser:maxPrec charLit
@[qedPat_parser] def qedPatParen : Parser := leading_parser:maxPrec "(" >> sepBy (categoryParser `qedPat 0) "," >> ")"
@[qedPat_parser] def qedPatDot   : Parser := leading_parser:maxPrec
  atomic ("." >> checkNoWsBefore "") >> ident >> optional (checkNoWsBefore "" >> "(" >> sepBy (categoryParser `qedPat 0) "," >> ")")
@[qedPat_parser] def qedPatIdent : Parser := leading_parser:maxPrec
  ident >> optional (checkNoWsBefore "" >> "(" >> sepBy (categoryParser `qedPat 0) "," >> ")")

-- Expressions (`qedExpr`)
@[qedCallArg_parser] def qedCallArgNamed : Parser := leading_parser
  atomic (ident >> "=" >> notFollowedBy (symbol "=") "=") >> categoryParser `qedExpr 0
@[qedCallArg_parser] def qedCallArgPos : Parser := leading_parser categoryParser `qedExpr 0

def qedRecField : Parser := node `Qed.Lang.recField (atomic (ident >> "=") >> categoryParser `qedExpr 0)
def qedExprCase : Parser := leading_parser
  withPosition (atomic (kw "case") >> sepBy1 (categoryParser `qedPat 0) "," >> ":" >> categoryParser `qedExpr 0)
def qedLamParam : Parser := node `Qed.Lang.lamParam (qedBinder >> optional (":" >> categoryParser `qedType 0))

private def notReservedExprKw : Parser :=
  notFollowedBy (
    kw "and" <|> kw "or" <|> kw "not" <|> kw "is" <|> kw "pass" <|> kw "elif" <|>
    kw "case" <|> kw "catch" <|> kw "atomic" <|>
    symbol "in" <|> symbol "if" <|> symbol "else" <|> symbol "match" <|>
    symbol "for" <|> symbol "return" <|> symbol "let") "expression"

@[qedExpr_parser] def qedRawTerm     : Parser := leading_parser:maxPrec "qedRaw%(" >> termParser >> ")"
@[qedExpr_parser] def qedLitNum      : Parser := leading_parser:maxPrec numLit
@[qedExpr_parser] def qedLitSci      : Parser := leading_parser:maxPrec scientificLit
@[qedExpr_parser] def qedLitStr      : Parser := leading_parser:maxPrec strLit
@[qedExpr_parser] def qedLitChar     : Parser := leading_parser:maxPrec charLit
@[qedExpr_parser] def qedFStr        : Parser := leading_parser:maxPrec atomic (kw "f" >> checkNoWsBefore "") >> interpolatedStr (categoryParser `qedExpr 0)
@[qedExpr_parser] def qedArrLit      : Parser := leading_parser:maxPrec "[" >> sepBy (categoryParser `qedExpr 0) "," >> "]"
@[qedExpr_parser] def qedRecLit      : Parser := leading_parser:maxPrec "{" >> optional (atomic (categoryParser `qedExpr 0 >> symbol "with")) >> sepBy qedRecField "," >> "}"
@[qedExpr_parser] def qedFieldSetter : Parser := leading_parser:maxPrec atomic ("(" >> ident >> "=" >> symbol "_" >> ")")
@[qedExpr_parser] def qedTypeAscr    : Parser := leading_parser:maxPrec atomic ("(" >> categoryParser `qedExpr 0 >> ":" >> categoryParser `qedType 0 >> ")")
@[qedExpr_parser] def qedParen       : Parser := leading_parser:maxPrec "(" >> sepBy (categoryParser `qedExpr 0) "," >> ")"
@[qedExpr_parser] def qedPlaceholder : Parser := leading_parser:maxPrec symbol "_"
@[qedExpr_parser] def qedDotIdent    : Parser := leading_parser:maxPrec atomic ("." >> checkNoWsBefore "") >> ident
@[qedExpr_parser] def qedIdent       : Parser := leading_parser:maxPrec notReservedExprKw >> ident

-- Postfix (`noWs` prevents cross-line ambiguity in indentation blocks)
@[qedExpr_parser 90] def qedCall   : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "(" >> sepBy (categoryParser `qedCallArg 0) "," >> ")"
@[qedExpr_parser 90] def qedIndex  : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "[" >> categoryParser `qedExpr 0 >> "]"
@[qedExpr_parser 90] def qedProj   : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "." >> checkNoWsBefore "" >> ident
@[qedExpr_parser 90] def qedUnwrap : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> symbol "?"

-- Prefix unary, arithmetic, comparisons, logic, ternary, lambdas, quantifiers, expression control flow
@[qedExpr_parser 80] def qedNeg      : Parser := leading_parser:80 "-" >> categoryParser `qedExpr 80
@[qedExpr_parser 75] def qedAwait    : Parser := leading_parser:75 atomic (kw "await") >> categoryParser `qedExpr 75

@[qedExpr_parser 70] def qedMul : TrailingParser := trailing_parser:70 symbol "*"  >> categoryParser `qedExpr 71
@[qedExpr_parser 70] def qedDiv : TrailingParser := trailing_parser:70 symbol "/"  >> categoryParser `qedExpr 71
@[qedExpr_parser 70] def qedMod : TrailingParser := trailing_parser:70 symbol "%"  >> categoryParser `qedExpr 71
@[qedExpr_parser 65] def qedAdd : TrailingParser := trailing_parser:65 symbol "+"  >> categoryParser `qedExpr 66
@[qedExpr_parser 65] def qedSub : TrailingParser := trailing_parser:65 symbol "-"  >> categoryParser `qedExpr 66
@[qedExpr_parser 65] def qedCat : TrailingParser := trailing_parser:65 symbol "++" >> categoryParser `qedExpr 66

def qedCmpOp : Parser :=
  node `Qed.Lang.cmpOp (
    symbol "==" <|> symbol "!=" <|> symbol "<=" <|> symbol ">=" <|> symbol "<" <|> symbol ">" <|>
    symbol "in" <|> atomic (kw "not" >> symbol "in") <|> atomic (kw "is" >> kw "not") <|> kw "is")
def qedCmpLink : Parser := node `Qed.Lang.cmpLink (qedCmpOp >> categoryParser `qedExpr 55)
@[qedExpr_parser 50] def qedCmp : TrailingParser := trailing_parser:50 many1 qedCmpLink

@[qedExpr_parser 40] def qedNot : Parser         := leading_parser:40 atomic (kw "not") >> categoryParser `qedExpr 40
@[qedExpr_parser 35] def qedAnd : TrailingParser := trailing_parser:35 atomic (kw "and") >> categoryParser `qedExpr 35
@[qedExpr_parser 30] def qedOr  : TrailingParser := trailing_parser:30 atomic (kw "or") >> categoryParser `qedExpr 30
@[qedExpr_parser 25] def qedImp : TrailingParser := trailing_parser:25 symbol "->" >> categoryParser `qedExpr 25

-- `checkColGt` prevents postfix `if`/`else` from eating a next-line statement
@[qedExpr_parser 20] def qedTernary : TrailingParser := trailing_parser:20
  atomic (checkColGt >> symbol "if") >> categoryParser `qedExpr 21 >>
  optional (atomic (checkColGt >> symbol "else") >> categoryParser `qedExpr 20)

@[qedExpr_parser 18] def qedLam1 : Parser := leading_parser:18 atomic (qedBinder >> " => ") >> categoryParser `qedExpr 18
@[qedExpr_parser 18] def qedLamN : Parser := leading_parser:18 atomic ("(" >> sepBy qedLamParam "," >> ")" >> " => ") >> categoryParser `qedExpr 18

@[qedExpr_parser 15] def qedAllIn   : Parser := leading_parser:15 atomic (kw "all" >> ident >> symbol "in") >> categoryParser `qedExpr 55 >> ":" >> categoryParser `qedExpr 15
@[qedExpr_parser 15] def qedAnyIn   : Parser := leading_parser:15 atomic (kw "any" >> ident >> symbol "in") >> categoryParser `qedExpr 55 >> ":" >> categoryParser `qedExpr 15
@[qedExpr_parser 15] def qedAllVars : Parser := leading_parser:15 atomic (kw "all" >> sepBy1 ident "," >> ":") >> categoryParser `qedExpr 15

@[qedExpr_parser 10] def qedExprIfLet : Parser := leading_parser:10
  withPosition (atomic (symbol "if" >> symbol "let") >> categoryParser `qedPat 0 >> "=" >> categoryParser `qedExpr 0 >> ":" >>
    categoryParser `qedExpr 0 >> optional (atomic (checkColGe >> symbol "else" >> ":") >> categoryParser `qedExpr 0))
@[qedExpr_parser 10] def qedExprIf : Parser := leading_parser:10
  withPosition (symbol "if" >> notFollowedBy (symbol "let") "let" >> categoryParser `qedExpr 0 >> ":" >>
    categoryParser `qedExpr 0 >> optional (atomic (checkColGe >> symbol "else" >> ":") >> categoryParser `qedExpr 0))
@[qedExpr_parser 10] def qedExprFor : Parser := leading_parser:10
  withPosition (atomic (symbol "for" >> ident >> symbol "in") >> categoryParser `qedExpr 0 >> ":" >> categoryParser `qedExpr 0)
@[qedExpr_parser 10] def qedExprMatch : Parser := leading_parser:10
  withPosition (symbol "match" >> sepBy1 (categoryParser `qedExpr 0) "," >> ":" >> many1 (checkColGt >> qedExprCase))

-- Statements & indented suites (`qedStmt`, `qedSuite`, `qedStmtCase`)
def qedSuite : Parser :=
  node `Qed.Lang.suite (
    (checkLineEq >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
    (checkColGt "expected indented block" >> withPosition (many1 (checkColEq "expected aligned statement" >> categoryParser `qedStmt 0))))
def qedStmtCase   : Parser := leading_parser withPosition (atomic (kw "case") >> sepBy1 (categoryParser `qedPat 0) "," >> ":" >> qedSuite)
def qedElifClause : Parser := node `Qed.Lang.elifClause (atomic (checkColEq >> kw "elif") >> categoryParser `qedExpr 0 >> ":" >> qedSuite)
def qedCatchArms       : Parser := node `Qed.Lang.catchArms (":" >> many1 (checkColGt >> qedStmtCase))
def qedCatchSingle     : Parser := node `Qed.Lang.catchSingle (qedBinder >> ":" >> qedSuite)
def qedLetCatch        : Parser := node `Qed.Lang.letCatch
  (atomic (checkColGe >> kw "catch" >> notFollowedBy (symbol "=" <|> symbol "+=" <|> symbol "-=") "assignment") >>
    (qedCatchArms <|> qedCatchSingle))
def qedLetPredictBlock : Parser := node `Qed.Lang.letPredictBlock
  (checkColGe >> withPosition (atomic (kw "predict" >> ":") >> qedSuite))
def qedLetPredictExpr  : Parser := node `Qed.Lang.letPredictExpr
  (checkColGe >> withPosition (atomic (kw "predict" >> notFollowedBy (symbol ":" <|> symbol "=" <|> symbol "+=" <|> symbol "-=") "predict") >>
    categoryParser `qedExpr 0))
def qedLetPredict      : Parser := qedLetPredictBlock <|> qedLetPredictExpr
def qedLetOnConfirm    : Parser := node `Qed.Lang.letOnConfirm
  (checkColGe >> withPosition (atomic (kw "on_confirm" >> ":") >> qedSuite))
def qedLetRollback     : Parser := node `Qed.Lang.letRollback
  (checkColGe >> withPosition (atomic (kw "rollback" >> optional (checkLineEq >> "(" >> qedBinder >> ")") >> ":") >> qedSuite))
def qedLetClause       : Parser := qedLetPredict <|> qedLetOnConfirm <|> qedLetRollback <|> qedLetCatch

@[qedStmt_parser] def qedStmtPass         : Parser := leading_parser withPosition (atomic (kw "pass"))
@[qedStmt_parser] def qedStmtReturn       : Parser := leading_parser
  withPosition (symbol "return" >> optional (checkLineEq >> categoryParser `qedExpr 0))
@[qedStmt_parser] def qedStmtAtomic       : Parser := leading_parser withPosition (atomic (kw "atomic" >> ":") >> qedSuite)
@[qedStmt_parser] def qedStmtLet          : Parser := leading_parser
  withPosition (symbol "let" >> qedBinder >> optional (":" >> categoryParser `qedType 0) >> "=" >>
    categoryParser `qedExpr 0 >> many qedLetClause)
@[qedStmt_parser] def qedStmtIfLet        : Parser := leading_parser
  withPosition (atomic (symbol "if" >> symbol "let") >> categoryParser `qedPat 0 >> "=" >> categoryParser `qedExpr 0 >> ":" >>
    qedSuite >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
@[qedStmt_parser] def qedStmtIf           : Parser := leading_parser
  withPosition (symbol "if" >> notFollowedBy (symbol "let") "let" >> categoryParser `qedExpr 0 >> ":" >>
    qedSuite >> many qedElifClause >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
@[qedStmt_parser] def qedStmtMatch        : Parser := leading_parser
  withPosition (symbol "match" >> sepBy1 (categoryParser `qedExpr 0) "," >> ":" >> many1 (checkColGt >> qedStmtCase))
@[qedStmt_parser] def qedStmtAssign       : Parser := leading_parser
  withPosition (atomic (categoryParser `qedExpr 90 >> ((symbol "=" >> notFollowedBy (symbol "=") "=") <|> symbol "+=" <|> symbol "-=")) >>
    categoryParser `qedExpr 0 >> optional qedLetPredict)
@[qedStmt_parser] def qedStmtExpr         : Parser := leading_parser
  withPosition (notFollowedBy (
    symbol "if" <|> symbol "match" <|> symbol "return" <|> symbol "let" <|>
    kw "atomic" <|> kw "pass") "statement" >> categoryParser `qedExpr 0)

end Parsers

/-! ## Unified AST Unpacking, Type & Pattern Lowering -/

open Lean

/-- Extracts statements from a `qedSuite` (handles both `;`-separated single-line and multi-line indented suites). -/
partial def suiteStmts (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Qed.Lang.suite then
    let body := (stx.getArg 0)
    if body.getKind == nullKind then body.getArgs.filter (!·.isAtom) else #[body]
  else if stx.getKind == nullKind then stx.getArgs.filter (!·.isAtom)
  else #[stx]

/-- Unwraps single-element parenthesized `qedExpr` nodes. -/
partial def unwrapParens1 (stx : Syntax) : Syntax :=
  if stx.getKind == ``qedParen && (stx.getArg 1).getSepArgs.size == 1 then unwrapParens1 (stx.getArg 1).getSepArgs[0]! else stx

/-- Extracts the optional `else:` suite from `qedStmtIf` / `qedStmtIfLet`. -/
def extractElseSuite (optElse : Syntax) : Option (Array Syntax) :=
  if optElse.getNumArgs == 3 then some (suiteStmts (optElse.getArg 2)) else none

/-- Desugars `elif` chains on `qedStmtIf` into nested `qedStmtIf` nodes for the `else` branch. -/
def desugarElifs (elifs : Array Syntax) (optElse : Syntax) : Option (Array Syntax) :=
  if elifs.isEmpty then extractElseSuite optElse
  else
    let first := elifs[0]!
    let info := first.getHeadInfo
    some #[Syntax.node info ``qedStmtIf
      #[Syntax.atom info "if", (first.getArg 1), (first.getArg 2), (first.getArg 3),
        Syntax.node info nullKind (elifs.extract 1 elifs.size), optElse]]

/-- Matches a method call `target.method(args...)`, returning `(targetExpr, methodName, rawCallArgs)`. -/
def matchMethodCall? (stx : Syntax) : Option (Syntax × String × Array Syntax) := do
  let u := unwrapParens1 stx
  guard (u.getKind == ``qedCall)
  let rawArgs := (u.getArg 2).getSepArgs
  let callee := (u.getArg 0)
  if callee.getKind == ``qedProj then
    return ((callee.getArg 0), (callee.getArg 2).getId.toString, rawArgs)
  else if callee.getKind == ``qedIdent then
    let parts := (callee.getArg 0).getId.toString.splitOn "."
    guard (parts.length >= 2)
    let meth := parts.getLast!
    let baseName := (parts.take (parts.length - 1)).foldl (fun acc seg => Name.str acc seg) .anonymous
    let info := SourceInfo.fromRef (callee.getArg 0)
    return (Syntax.node info ``qedIdent #[mkIdentFrom (callee.getArg 0) baseName], meth, rawArgs)
  else failure

/-- Matches a single-segment `ident.method(args...)` call, returning `(targetIdent, methodName, rawCallArgs)`. -/
def matchIdentMethodCall? (stx : Syntax) : Option (Ident × String × Array Syntax) := do
  let (target, meth, rawArgs) ← matchMethodCall? stx
  guard (target.getKind == ``qedIdent)
  let id : Ident := ⟨(target.getArg 0)⟩
  match id.getId.eraseMacroScopes with
  | .str .anonymous _ => return (id, meth, rawArgs)
  | _ => failure

/-- Matches a standalone `target.push(elem)` call expression, returning `(targetExpr, elemExpr)`. -/
def matchPushCall? (stx : Syntax) : Option (Syntax × Syntax) := do
  let (target, meth, rawArgs) ← matchMethodCall? stx
  guard (meth == "push" && rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos)
  return (target, rawArgs[0]![0])

inductive TypeMod where | array | option | fallible deriving Inhabited, DecidableEq, Repr

/-- Pretty source snippet of a syntax node without trailing comments/newlines. -/
def stxSnippet (stx : Syntax) : String :=
  let raw := (stx.unsetTrailing.reprint.getD "").trimAscii.toString
  match raw.splitOn "\n" with
  | []      => ""
  | [single] => single.trimAscii.toString
  | first :: _ => first.trimAscii.toString ++ " ..."

def splitIdentMods (id : Ident) : MacroM (Ident × Array TypeMod) := do
  let raw := id.getId.toString
  let chars := raw.toList
  let revMods := chars.reverse.takeWhile (fun c => c == '?' || c == '!')
  let baseChars := chars.take (chars.length - revMods.length)
  if baseChars.isEmpty then Macro.throwErrorAt id s!"invalid type `{raw}`"
  let mods := revMods.reverse.toArray.filterMap fun c =>
    if c == '?' then some .option else if c == '!' then some .fallible else none
  let baseName := (String.ofList baseChars |>.splitOn ".").foldl Name.str .anonymous
  return (mkIdentFrom id baseName, mods)

def parseTypeModNode (m : Syntax) : MacroM TypeMod := do
  let k := m.getKind
  if k == ``qedTypeModArr then return .array
  else if k == ``qedTypeModOpt then return .option
  else if k == ``qedTypeModErr then return .fallible
  else
    let s := (m.reprint.getD "").trimAscii.toString
    if s == "[]" then return .array else if s == "?" then return .option else if s == "!" then return .fallible
    else Macro.throwErrorAt m s!"unknown type modifier `{s}`"

def resolveBaseTypeTerm (baseId : Ident) : Term :=
  if baseId.getId == `Bytes then mkIdentFrom baseId `Qed.Bytes
  else if baseId.getId == `Json then mkIdentFrom baseId `Qed.Json
  else if baseId.getId == `WebhookUrl then mkIdentFrom baseId `Qed.Server.WebhookUrl
  else ⟨baseId.raw⟩

def applyTypeMods (base : Term) (mods : Array TypeMod) (allowFallible : Bool) (ref : Syntax) :
    MacroM (Term × Bool) := do
  let mut acc := base
  let mut isFallible := false
  for i in [0:mods.size] do
    match mods[i]! with
    | .array    => acc ← `(Array $acc)
    | .option   => acc ← `(Option $acc)
    | .fallible =>
        if !allowFallible then Macro.throwErrorAt ref "fallible `!` modifier is only allowed on server `def` return types"
        if i + 1 < mods.size then Macro.throwErrorAt ref "place `!` last on fallible return types (for example `Book[]!` instead of `Book![]`)"
        isFallible := true
  return (acc, isFallible)

/-- Lowers a unified `qedType` syntax node to a Lean type `Term`, rejecting `Array T` / `Option T`. -/
partial def lowerQedType (stx : Syntax) (allowFallible := false) : MacroM (Term × Bool) := do
  let k := stx.getKind
  if k == ``qedTypeProto then
    let (baseId, initMods) ← splitIdentMods ⟨(stx.getArg 2)⟩
    applyTypeMods ⟨baseId.raw⟩ (initMods ++ (← (stx.getArg 4).getArgs.mapM parseTypeModNode)) allowFallible stx
  else if k == ``qedTypeParen then
    let lowered ← (stx.getArg 1).getSepArgs.mapM fun p => return (← lowerQedType p false).1
    let baseT ← if lowered.size == 1 then pure lowered[0]!
      else lowered.foldrM (init := lowered.back!) (start := lowered.size - 1) fun a acc => `($a × $acc)
    applyTypeMods baseT (← (stx.getArg 3).getArgs.mapM parseTypeModNode) allowFallible stx
  else if k == ``qedTypeAtom then
    let (baseId, initMods) ← splitIdentMods ⟨(stx.getArg 0)⟩
    applyTypeMods (resolveBaseTypeTerm baseId) (initMods ++ (← (stx.getArg 1).getArgs.mapM parseTypeModNode)) allowFallible stx
  else if k == ``qedTypeApp then
    if (stx.getArg 0).getKind == ``qedTypeAtom && ((stx.getArg 0).getArg 1).getArgs.isEmpty then
      let fnName := ((stx.getArg 0).getArg 0).getId.eraseMacroScopes
      let argStr := let s := stxSnippet (stx.getArg 1); if s.isEmpty then "T" else s
      if fnName == `Array || fnName == `Option then
        Macro.throwErrorAt stx s!"use `{argStr}{if fnName == `Array then "[]" else "?"}` instead of `{fnName} {argStr}`"
      if fnName == `jsonOnly then
        Macro.throwErrorAt stx s!"use `jsonOnly({argStr})` with parentheses instead of `jsonOnly {argStr}`"
    return (← `($((← lowerQedType (stx.getArg 0) false).1) $((← lowerQedType (stx.getArg 1) false).1)), false)
  else if k == ``qedTypeArrow then
    return (← `($((← lowerQedType (stx.getArg 0) false).1) → $((← lowerQedType (stx.getArg 2) false).1)), false)
  else
    let sn := stxSnippet stx
    let what := if sn.isEmpty then "" else s!" `{sn}`"
    Macro.throwErrorAt stx s!"invalid Qed type{what}; expected a type such as `T`, `T[]`, `T?`, `T!`, `Resource T`, or `A -> B`"

/-- Infers automatic defaults for `qedType` state fields (`T[]` → `#[]`, `T?` → `none`, `Resource T` → `.idle`, `Cached T` → `{}`). -/
partial def inferQedTypeDefault? (stx : Syntax) : MacroM (Option Term) := do
  let k := stx.getKind
  let modDef (mods : Array TypeMod) : MacroM (Option Term) :=
    match mods.back? with | some .array => some <$> `(#[]) | some .option => some <$> `(none) | _ => pure none
  if k == ``qedTypeParen then
    if let some d ← modDef (← (stx.getArg 3).getArgs.mapM parseTypeModNode) then return some d
    if (stx.getArg 1).getSepArgs.size == 1 then inferQedTypeDefault? (stx.getArg 1).getSepArgs[0]! else return none
  else if k == ``qedTypeAtom then
    let (_, initMods) ← splitIdentMods ⟨(stx.getArg 0)⟩
    modDef (initMods ++ (← (stx.getArg 1).getArgs.mapM parseTypeModNode))
  else if k == ``qedTypeApp && (stx.getArg 0).getKind == ``qedTypeAtom && ((stx.getArg 0).getArg 1).getArgs.isEmpty then
    let head := ((stx.getArg 0).getArg 0).getId.eraseMacroScopes
    if head == `Resource then some <$> `(.idle) else if head == `Cached then some <$> `({}) else return none
  else return none

/-- Lowers a unified `qedPat` into a Lean pattern `Term`. -/
partial def lowerQedPat (stx : Syntax) : MacroM Term := do
  let k := stx.getKind
  if k == ``qedPatWild then `(_)
  else if k == ``qedPatNum || k == ``qedPatStr || k == ``qedPatChar then return ⟨(stx.getArg 0)⟩
  else if k == ``qedPatParen then
    let elems := (stx.getArg 1).getSepArgs
    if elems.isEmpty then `(())
    else if elems.size == 1 then lowerQedPat elems[0]!
    else
      let ps ← elems.mapM lowerQedPat
      ps.foldrM (init := ps.back!) (start := ps.size - 1) fun a acc => `(($a, $acc))
  else if k == ``qedPatDot || k == ``qedPatIdent then
    let headT : Term := if k == ``qedPatDot then
        ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", (stx.getArg 1)]⟩
      else ⟨(stx.getArg 0)⟩
    let argsNode := if k == ``qedPatDot then (stx.getArg 2) else (stx.getArg 1)
    if argsNode.getNumArgs == 3 then `($headT $(← (argsNode.getArg 1).getSepArgs.mapM lowerQedPat)*)
    else return headT
  else
    let sn := stxSnippet stx
    let what := if sn.isEmpty then "" else s!" `{sn}`"
    Macro.throwErrorAt stx s!"unsupported pattern{what}; expected `_`, a literal, an identifier, `.ctor(a, b)`, or a tuple `(a, b)`"

/-- Collects bound variable names introduced by a `qedPat`. -/
partial def collectQedPatIds (stx : Syntax) : Array Name :=
  let k := stx.getKind
  if k == ``qedPatIdent then
    if (stx.getArg 1).getNumArgs == 3 then ((stx.getArg 1).getArg 1).getSepArgs.flatMap collectQedPatIds
    else
      let vn := (stx.getArg 0).getId.eraseMacroScopes
      if vn.isAtomic && vn.toString != "_" && vn != `none && vn != `true && vn != `false &&
          !vn.toString.front.isUpper then #[vn] else #[]
  else if k == ``qedPatDot then
    if (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs.flatMap collectQedPatIds else #[]
  else if k == ``qedPatParen then (stx.getArg 1).getSepArgs.flatMap collectQedPatIds
  else #[]

/-! ## Unified Expression Lowering (`ExprMode`, `lowerQedExpr`, `lowerSimpleQedExpr`) -/

inductive ExprMode where | val | boolCond | propGuard | propInv deriving BEq, DecidableEq

partial def exprHasIndex (stx : Syntax) : Bool :=
  stx.getKind == ``qedIndex || stx.getArgs.any exprHasIndex

/-- Checks whether a `qedExpr` AST is already a plain value (never `Qed.Field` or `Qed.Ensured`). -/
def isPlainLiteralOrCtor (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  let k := u.getKind
  let isPlainField (f : String) : Bool :=
    f == "size" || f == "length" || f == "isSome" || f == "isNone" || f == "isEmpty" || f == "val"
  if k == ``qedLitNum || k == ``qedLitSci || k == ``qedLitStr || k == ``qedLitChar ||
      k == ``qedFStr || k == ``qedArrLit || k == ``qedRecLit || k == ``qedDotIdent ||
      k == ``qedNeg || k == ``qedMul || k == ``qedDiv || k == ``qedMod ||
      k == ``qedAdd || k == ``qedSub || k == ``qedCat then true
  else if k == ``qedIdent then
    let nm := (u.getArg 0).getId
    let s := nm.toString
    s == "true" || s == "false" || s == "none" ||
      (nm.isStr && nm.getPrefix != .anonymous && isPlainField (match nm with | .str _ f => f | _ => s))
  else if k == ``qedProj then isPlainField (u.getArg 2).getId.toString
  else k == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.toString == "some"

def isNoneExpr (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedIdent && (u.getArg 0).getId.toString == "none"

def cmpOpKind (opStx : Syntax) : String :=
  let raw := (opStx.reprint.getD "").trimAscii.toString
  if raw.contains ' ' then String.intercalate " " ((raw.splitOn " ").filter (!·.isEmpty)) else raw

def mkRawExpr (t : Term) : Syntax :=
  Syntax.node .none ``qedRawTerm #[Syntax.atom .none "qedRaw%(", t.raw, Syntax.atom .none ")"]

structure LowerHooks (m : Type → Type) where
  lowerIdent       : Syntax → Ident → ExprMode → m Term
  lowerProj        : Syntax → Term → Ident → ExprMode → m Term
  lowerIndex       : Syntax → Term → Term → ExprMode → m Term
  lowerCall        : Syntax → Syntax → Array Syntax → ExprMode → (ExprMode → Syntax → m Term) → m (Option Term)
  lowerUnwrap      : Syntax → Syntax → ExprMode → m Term
  lowerAwait       : Syntax → Syntax → ExprMode → m Term
  lowerFieldSetter : Syntax → Ident → m Term
  lowerJsx         : Syntax → ExprMode → m Term
  lowerArrElem     : Term → m Term
  wrapNamedField   : Term → m Term
  lowerType        : Syntax → m Term
  lowerPat         : Syntax → m Term
  withLocals       : Array String → m Term → m Term
  useDirectArray   : Bool := false
  allowOptElse     : Bool := false
  optElseFallback  : m Term
  freshIdent       : String → m Ident
  throwErr         : Syntax → String → m Term

def finishTermMode (mode : ExprMode) (t : Term) : MacroM Term :=
  if mode == .propInv || mode == .propGuard then `(qedAsProp($t)) else return t

def buildTupleVal (vals : Array Term) : MacroM Term :=
  if vals.isEmpty then `(())
  else if vals.size == 1 then return vals[0]!
  else vals.foldrM (init := vals.back!) (start := vals.size - 1) fun a acc => `(($a, $acc))

/-- Unified lowerer for all `qedExpr` nodes across `server`, `component`, `schema`, `invariant`, and JSX. -/
@[noinline, nospecialize]
partial def lowerQedExpr {m : Type → Type} [Monad m] [MonadQuotation m]
    (hooks : LowerHooks m) (mode : ExprMode) (stx : Syntax) : m Term := do
  let rec go (mode : ExprMode) (stx : Syntax) : m Term := do
    let lowerValOp (s : Syntax) : m Term := do
      let t ← go .val s
      if isPlainLiteralOrCtor s then return t else `(Qed.Lang.QedVal.val $t)
    let finish (t : Term) : m Term :=
      if mode == .propInv || mode == .propGuard then `(qedAsProp($t)) else return t
    let lowerOptElse (ref : Syntax) (optNode : Syntax) (errMsg : String) : m Term :=
      if optNode.getNumArgs == 2 then go mode (optNode.getArg 1)
      else if hooks.allowOptElse then hooks.optElseFallback
      else hooks.throwErr ref errMsg
    match stx.getKind with
    | .str (.str (.str .anonymous "Qed") "Lang") k =>
      match k with
      | "qedRawTerm" => return ⟨(stx.getArg 1)⟩
      | "qedLitNum" | "qedLitSci" | "qedLitStr" | "qedLitChar" => return ⟨(stx.getArg 0)⟩
      | "qedFStr" =>
        let mut parts : Array Term := #[]
        for ch in (stx.getArg 1).getArgs do
          if let some litStr := ch.isInterpolatedStrLit? then
            if !litStr.isEmpty then parts := parts.push (Syntax.mkStrLit litStr)
          else parts := parts.push (← `(toString (Qed.Lang.QedVal.val $(← go .val ch))))
        match parts.toList with
        | []      => return Syntax.mkStrLit ""
        | p :: ps => ps.foldlM (init := p) fun acc q => `($acc ++ $q)
      | "qedArrLit" =>
        let elems ← (stx.getArg 1).getSepArgs.mapM fun e => do hooks.lowerArrElem (← go .val e)
        if hooks.useDirectArray then `(#[$[$elems],*]) else `(Qed.Lang.QedSeqLit.ofList [$[$elems],*])
      | "qedRecLit" =>
        let fields := (stx.getArg 2).getSepArgs
        let fIds : Array Ident := fields.map (⟨·[0]⟩)
        let fVals ← fields.mapM fun f => do hooks.wrapNamedField (← go .val (f.getArg 2))
        if (stx.getArg 1).getNumArgs == 2 then `({ $(← go .val ((stx.getArg 1).getArg 0)) with $[$fIds:ident := $fVals:term],* })
        else if fIds.isEmpty then `({}) else `({ $[$fIds:ident := $fVals:term],* })
      | "qedFieldSetter" => hooks.lowerFieldSetter stx ⟨(stx.getArg 1)⟩
      | "qedTypeAscr" => `(($(← go mode (stx.getArg 1)) : $(← hooks.lowerType (stx.getArg 3))))
      | "qedParen" =>
        let elems := (stx.getArg 1).getSepArgs
        if elems.isEmpty then `(())
        else if elems.size == 1 then go mode elems[0]!
        else
          let vs ← elems.mapM (go .val)
          vs.foldrM (init := vs.back!) (start := vs.size - 1) fun a acc => `(($a, $acc))
      | "qedPlaceholder" => `(_)
      | "qedDotIdent" =>
        finish ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", (stx.getArg 1)]⟩
      | "qedIdent" => hooks.lowerIdent stx ⟨(stx.getArg 0)⟩ mode
      | "qedUnwrap" => hooks.lowerUnwrap stx (stx.getArg 0) mode
      | "qedAwait" => hooks.lowerAwait stx (stx.getArg 1) mode
      | "qedIndex" => hooks.lowerIndex stx (← go .val (stx.getArg 0)) (← go .val (stx.getArg 2)) mode
      | "qedProj" => hooks.lowerProj stx (← go .val (stx.getArg 0)) ⟨(stx.getArg 2)⟩ mode
      | "qedCall" =>
        let (calleeStx, rawArgs) := ((stx.getArg 0), (stx.getArg 2).getSepArgs)
        if let some custom ← hooks.lowerCall stx calleeStx rawArgs mode go then return custom
        if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId.eraseMacroScopes == `url &&
            rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos && (rawArgs[0]!.getArg 0).getKind == ``qedLitStr then
          let info := SourceInfo.fromRef stx
          let strLit := (rawArgs[0]!.getArg 0).getArg 0
          return ← finish ⟨Syntax.node info `Qed.Jsx.qedUrlLit #[calleeStx.getArg 0, Syntax.atom info "(", strLit, Syntax.atom info ")"]⟩
        if !rawArgs.isEmpty && rawArgs.any (·.getKind == ``qedCallArgNamed) then
          unless rawArgs.all (·.getKind == ``qedCallArgNamed) do
            let calleeStr := stxSnippet calleeStx
            let inCall := if calleeStr.isEmpty then "the same call" else s!"call `{calleeStr}(...)`"
            return ← hooks.throwErr stx s!"cannot mix named (`field=val`) and positional arguments in {inCall}"
          let tyTerm ← go .val calleeStx
          let fIds : Array Ident := rawArgs.map (⟨·[0]⟩)
          let fVals ← rawArgs.mapM fun a => do hooks.wrapNamedField (← go .val (a.getArg 2))
          return ← `(({ $[$fIds:ident := $fVals:term],* } : $tyTerm))
        let calleeTerm ← go .val calleeStx
        let isPropAllCall := (mode == .propInv || mode == .propGuard) &&
          ((calleeStx.getKind == ``qedProj && ((calleeStx.getArg 2).getId == `all || (calleeStx.getArg 2).getId == `any)) ||
           (calleeStx.getKind == ``qedIdent &&
             match (calleeStx.getArg 0).getId with | .str _ "all" | .str _ "any" => true | _ => false))
        let argTerms ← rawArgs.mapM fun a => do
          let uArg := unwrapParens1 (a.getArg 0)
          let argMode := if isPropAllCall && (uArg.getKind == ``qedLam1 || uArg.getKind == ``qedLamN) then .propInv else .val
          go argMode (a.getArg 0)
        let callRes ← if argTerms.isEmpty then pure calleeTerm else `($calleeTerm $argTerms*)
        finish callRes
      | "qedNeg" => `(-($(← lowerValOp (stx.getArg 1))))
      | "qedMul" | "qedDiv" | "qedMod" | "qedAdd" | "qedSub" | "qedCat" =>
        let (a, b) := (← lowerValOp (stx.getArg 0), ← lowerValOp (stx.getArg 2))
        match k with
        | "qedMul" => `(($a) * ($b)) | "qedDiv" => `(($a) / ($b))
        | "qedMod" => `(($a) % ($b)) | "qedAdd" => `(($a) + ($b))
        | "qedSub" => `(($a) - ($b)) | _        => `(($a) ++ ($b))
      | "qedCmp" =>
        let isPropMode := mode == .propInv || mode == .propGuard
        let lowerSingleCmp (lhsStx : Syntax) (opStr : String) (rhsStx : Syntax) : m Term := do
          if opStr == "==" || opStr == "!=" || opStr == "is" || opStr == "is not" then
            let isEq := opStr == "==" || opStr == "is"
            let (lS, rS) := if isNoneExpr lhsStx && !isNoneExpr rhsStx then (rhsStx, lhsStx) else (lhsStx, rhsStx)
            let (a, b) := (← lowerValOp lS, ← lowerValOp rS)
            match isEq, mode with
            | true,  .propInv   => `(($a) = ($b))
            | true,  .propGuard => `(qedEqProp($a, $b))
            | true,  _          => `(($a) == ($b))
            | false, .propInv   => `(($a) ≠ ($b))
            | false, .propGuard => `(¬ qedEqProp($a, $b))
            | false, _          => `(($a) != ($b))
          else if opStr == "in" || opStr == "not in" then
            let (a, b, isIn) := (← lowerValOp lhsStx, ← lowerValOp rhsStx, opStr == "in")
            if isPropMode then if isIn then `(Qed.Lang.QedMemProp.memProp ($a) ($b)) else `(¬ Qed.Lang.QedMemProp.memProp ($a) ($b))
            else if isIn then `(Qed.Lang.QedMem.mem ($a) ($b)) else `(!(Qed.Lang.QedMem.mem ($a) ($b)))
          else
            let (a, b) := (← lowerValOp lhsStx, ← lowerValOp rhsStx)
            let p ← match opStr with
              | "<=" => `(($a) ≤ ($b)) | ">=" => `(($a) ≥ ($b))
              | "<"  => `(($a) < ($b)) | _    => `(($a) > ($b))
            if isPropMode then return p else `(decide ($p))
        let mut prev := (stx.getArg 0)
        let mut terms : Array Term := #[]
        for lk in (stx.getArg 1).getArgs do
          terms := terms.push (← lowerSingleCmp prev (cmpOpKind (lk.getArg 0)) (lk.getArg 1))
          prev := (lk.getArg 1)
        match terms.toList with
        | []      => hooks.throwErr stx "empty comparison"
        | t :: ts => ts.foldlM (init := t) fun acc x => if isPropMode then `($acc ∧ $x) else `($acc && $x)
      | "qedNot" =>
        if mode == .propInv || mode == .propGuard then `(¬ ($(← go mode (stx.getArg 1)))) else `(!($(← go .boolCond (stx.getArg 1))))
      | "qedAnd" | "qedOr" =>
        let isAnd := k == "qedAnd"
        match mode with
        | .propInv =>
            let (a, b) := (← go .propInv (stx.getArg 0), ← go .propInv (stx.getArg 2))
            if isAnd then `($a ∧ $b) else `($a ∨ $b)
        | .propGuard =>
            let (a, b) := (← go .propGuard (stx.getArg 0), ← go .propGuard (stx.getArg 2))
            if exprHasIndex (stx.getArg 2) then
              let h ← hooks.freshIdent (if isAnd then "_qedAnd" else "_qedOr")
              if isAnd then `(Qed.Lang.QedAndProp ($a) (fun ($h:ident : $a) => $b))
              else `(Qed.Lang.QedOrProp ($a) (fun ($h:ident : ¬ ($a)) => $b))
            else if isAnd then `($a ∧ $b) else `($a ∨ $b)
        | _ =>
            let (a, b) := (← go .boolCond (stx.getArg 0), ← go .boolCond (stx.getArg 2))
            if isAnd && exprHasIndex (stx.getArg 2) then
              let h ← hooks.freshIdent "_qedAnd"
              `(if $h:ident : ($a) = true then $b else false)
            else if isAnd then `($a && $b) else `($a || $b)
      | "qedImp" =>
        if mode == .propInv || mode == .propGuard then `($(← go mode (stx.getArg 0)) → $(← go mode (stx.getArg 2)))
        else `(!$(← go .boolCond (stx.getArg 0)) || $(← go .boolCond (stx.getArg 2)))
      | "qedTernary" =>
        let (hIf, condT, thenT) := (← hooks.freshIdent "_qedIf", ← go .propGuard (stx.getArg 2), ← go mode (stx.getArg 0))
        let elseT ← lowerOptElse stx (stx.getArg 3) "conditional expression `a if cond else b` requires an `else` branch here"
        `(if $hIf:ident : $condT then $thenT else $elseT)
      | "qedLam1" | "qedLamN" =>
        let pEntries : Array (Syntax × Option Syntax) :=
          if k == "qedLam1" then #[((stx.getArg 0), none)]
          else (stx.getArg 1).getSepArgs.map fun p => ((p.getArg 0), if (p.getArg 1).getNumArgs == 2 then some ((p.getArg 1).getArg 1) else none)
        let bodyStx := if k == "qedLam1" then (stx.getArg 2) else (stx.getArg 4)
        let pNames := pEntries.filterMap fun (b, _) => if b.isIdent then some b.getId.toString else none
        let body ← hooks.withLocals pNames (go (if mode == .propInv then .propInv else .val) bodyStx)
        pEntries.foldrM (init := body) fun (b, tyOpt?) acc => do
          match tyOpt? with
          | some tyStx =>
              let tyT ← hooks.lowerType tyStx
              if b.isIdent then let bid : Ident := ⟨b⟩; `(fun ($bid:ident : $tyT) => $acc)
              else `(fun (_ : $tyT) => $acc)
          | none =>
              if b.isIdent then let bid : Ident := ⟨b⟩; `(fun $bid:ident => $acc)
              else `(fun _ => $acc)
      | "qedAllIn" | "qedAnyIn" =>
        let (bId, arrT) : Ident × Term := (⟨(stx.getArg 1)⟩, ← go .val (stx.getArg 3))
        let isPropMode := mode == .propInv || mode == .propGuard
        let bodyT ← hooks.withLocals #[bId.getId.toString] (go (if isPropMode then mode else .boolCond) (stx.getArg 5))
        if k == "qedAllIn" then
          if isPropMode then `(∀ $bId:ident ∈ $arrT, $bodyT) else `(($arrT).all (fun $bId:ident => $bodyT))
        else
          if isPropMode then `(∃ $bId:ident ∈ $arrT, $bodyT) else `(($arrT).any (fun $bId:ident => $bodyT))
      | "qedAllVars" =>
        unless mode == .propInv || mode == .propGuard do
          return ← hooks.throwErr stx "`all x, y: ...` without `in` is only valid in invariants and logical propositions; for a runtime check over a collection, write `all x in items: ...`"
        let vIds : Array Ident := (stx.getArg 1).getSepArgs.map (⟨·⟩)
        let bodyT ← hooks.withLocals (vIds.map (·.getId.toString)) (go mode (stx.getArg 3))
        vIds.foldrM (init := bodyT) fun vid acc => `(∀ $vid:ident, $acc)
      | "qedExprIf" =>
        let (hIf, condT, thenT) := (← hooks.freshIdent "_qedIf", ← go .propGuard (stx.getArg 1), ← go mode (stx.getArg 3))
        let elseT ← lowerOptElse stx (stx.getArg 4) "`if cond: ...` expression requires `else:` here"
        `(if $hIf:ident : $condT then $thenT else $elseT)
      | "qedExprIfLet" =>
        let elseT ← lowerOptElse stx (stx.getArg 7) "`if let pat = expr: ...` expression requires `else:` here"
        `(if let $(← hooks.lowerPat (stx.getArg 2)) := $(← go .val (stx.getArg 4)) then $(← go mode (stx.getArg 6)) else $elseT)
      | "qedExprMatch" =>
        let scruts ← (stx.getArg 1).getSepArgs.mapM (go .val)
        let alts ← (stx.getArg 3).getArgs.mapM fun c => do
          `(Lean.Parser.Term.matchAltExpr| | $[$(← (c.getArg 1).getSepArgs.mapM hooks.lowerPat):term],* => $(← go mode (c.getArg 3)))
        `(match $[$scruts:term],* with $[$alts:matchAlt]*)
      | "qedExprFor" =>
        let xId : Ident := ⟨(stx.getArg 1)⟩
        `(Qed.mapList (Qed.ForEachItems.toList $(← go .val (stx.getArg 3))) (fun $xId:ident => $(← go .val (stx.getArg 5))))
      | _ => hooks.lowerJsx stx mode
    | _ => hooks.lowerJsx stx mode
  go mode stx

/-- MacroM-level unified expression lowerer for `schema`, `component`, `invariant`, and JSX. -/
def lowerSimpleQedExpr (mode : ExprMode) (stx : Syntax)
    (allowOptElse := false) (optElseFallback : MacroM Term := `(()))
    (lowerJsx? : Option (Syntax → ExprMode → MacroM Term) := none)
    (lowerFieldSetter? : Option (Syntax → Ident → MacroM Term) := none)
    (wrapNamedField : Term → MacroM Term := pure)
    (lowerIndex? : Option (Syntax → Term → Term → ExprMode → MacroM Term) := none) : MacroM Term :=
  lowerQedExpr {
    lowerIdent := fun _ id m => finishTermMode m ⟨id.raw⟩
    lowerProj := fun _ obj fld m => do finishTermMode m (← `(($obj).$fld:ident))
    lowerIndex := fun ref arr idx m => match lowerIndex? with
      | some f => f ref arr idx m
      | none   => do finishTermMode m (← `($arr[$idx]))
    lowerCall := fun _ _ _ _ _ => pure none
    lowerUnwrap := fun ref _ _ => Macro.throwErrorAt ref "operator `?` is only supported inside `server` functions with a fallible (`T!`) or optional (`T?`) return type"
    lowerAwait := fun ref _ _ => Macro.throwErrorAt ref "`await` is only supported in statements (`let x = await ...` or `field = await ...`)"
    lowerFieldSetter := fun ref fid => match lowerFieldSetter? with | some f => f ref fid | none => Macro.throwErrorAt ref s!"`({fid.getId} = _)` is a component field setter and can only be used inside a `component`"
    lowerJsx := fun ref m => match lowerJsx? with
      | some f => f ref m
      | none =>
          if ref.getKind.toString.contains "Jsx" then
            Macro.throwErrorAt ref "JSX elements are only allowed inside view expressions"
          else
            let sn := stxSnippet ref
            let what := if sn.isEmpty then s!"({ref.getKind})" else s!" `{sn}`"
            Macro.throwErrorAt ref s!"unsupported Qed expression{what}"
    lowerArrElem := pure, wrapNamedField
    lowerType := fun t => return (← lowerQedType t false).1
    lowerPat := lowerQedPat, withLocals := fun _ k => k
    allowOptElse, optElseFallback
    freshIdent := fun pfx => pure (mkIdent (Name.mkSimple pfx))
    throwErr := Macro.throwErrorAt
  } mode stx

end Qed.Lang
