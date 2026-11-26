import Lean
import Qed.Dict
import Qed.Field
import Qed.Diag

namespace Qed.Lang

/-! ## Shared Runtime Typeclasses & Proof Helpers (Kernel-Reducible, Zero Overhead) -/

class QedVal (α : Type) (β : outParam Type) where val : α → β
@[reducible, inline] instance (priority := low) {α : Type} : QedVal α α := ⟨id⟩
@[simp] theorem QedVal.val_id {α : Type} (x : α) : QedVal.val x = x := rfl

class QedSeqLit (α : Type) (C : Type) where ofList : List α → C
@[default_instance, reducible, inline] instance {α : Type} : QedSeqLit α (Array α) := ⟨List.toArray⟩
@[reducible, inline] instance {α : Type} : QedSeqLit α (List α) := ⟨id⟩
@[simp] theorem QedSeqLit.ofList_array {α : Type} (xs : List α) : (QedSeqLit.ofList xs : Array α) = xs.toArray := rfl
@[simp] theorem QedSeqLit.ofList_list {α : Type} (xs : List α) : (QedSeqLit.ofList xs : List α) = xs := rfl

class QedMem (α : Type) (C : Type) where mem : α → C → Bool
class QedMemProp (α : Type) (C : Type) where memProp : α → C → Prop

local macro "def_mem " bs:bracketedBinder* "|" e:term "," c:term "," bf:term "," bt:ident "|" pbs:bracketedBinder* "|" dbs:bracketedBinder* "|" pf:term "," pt:ident : command =>
  `(@[inline] instance $[$bs]* : QedMem $e $c := ⟨$bf⟩
    @[simp] theorem $bt $[$bs]* (x : $e) (xs : $c) : QedMem.mem x xs = ($bf) x xs := rfl
    @[reducible] instance $[$pbs]* : QedMemProp $e $c := ⟨$pf⟩
    @[simp] theorem $pt $[$pbs]* (x : $e) (xs : $c) : QedMemProp.memProp x xs = ($pf) x xs := rfl
    instance $[$dbs]* (x : $e) (xs : $c) : Decidable (QedMemProp.memProp x xs) := inferInstanceAs (Decidable (($pf) x xs)))

def_mem {α : Type} [BEq α] | α, Array α, (fun x xs => xs.contains x), QedMem.mem_array | {α : Type} | {α : Type} [DecidableEq α] | (fun x xs => x ∈ xs), QedMemProp.memProp_array
def_mem {α : Type} [BEq α] | α, List α, (fun x xs => xs.contains x), QedMem.mem_list | {α : Type} | {α : Type} [DecidableEq α] | (fun x xs => x ∈ xs), QedMemProp.memProp_list
def_mem | Char, String, (fun c s => s.contains c), QedMem.mem_string | | | (fun c s => s.contains c = true), QedMemProp.memProp_string
def_mem {K V : Type} [BEq K] | K, Qed.Dict K V, (fun k d => d.contains k), QedMem.mem_dict | {K V : Type} [BEq K] | {K V : Type} [BEq K] | (fun k d => d.contains k = true), QedMemProp.memProp_dict

structure QedAndProp (P : Prop) (Q : P → Prop) : Prop where mk :: (fst : P) (snd : Q fst)
instance {P : Prop} {Q : P → Prop} [Decidable P] [∀ h, Decidable (Q h)] : Decidable (QedAndProp P Q) :=
  if hp : P then if hq : Q hp then isTrue ⟨hp, hq⟩ else isFalse fun ⟨_, hq'⟩ => hq hq' else isFalse fun ⟨hp', _⟩ => hp hp'
@[simp] theorem not_qedAndProp {P : Prop} {Q : P → Prop} : (¬ QedAndProp P Q) ↔ ∀ h : P, ¬ Q h :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

inductive QedOrProp (P : Prop) (Q : ¬ P → Prop) : Prop where | inl (h : P) | inr (hnp : ¬ P) (hq : Q hnp)
instance {P : Prop} {Q : ¬ P → Prop} [Decidable P] [∀ h, Decidable (Q h)] : Decidable (QedOrProp P Q) :=
  if hp : P then isTrue (.inl hp) else if hq : Q hp then isTrue (.inr hp hq) else isFalse fun | .inl h => hp h | .inr _ h => hq h
@[simp] theorem not_qedOrProp {P : Prop} {Q : ¬ P → Prop} : (¬ QedOrProp P Q) ↔ ¬ P ∧ ∀ h : ¬ P, ¬ Q h :=
  ⟨fun h => ⟨fun hp => h (.inl hp), fun hnp hq => h (.inr hnp hq)⟩, fun ⟨hnp, hnq⟩ => fun | .inl hp => hnp hp | .inr hnp' hq => hnq hnp' hq⟩

syntax (name := qedEqPropStx) "qedEqProp(" term ", " term ")" : term
syntax (name := qedAsPropStx) "qedAsProp(" term ")" : term

open Lean Meta Elab Term in
@[term_elab qedAsPropStx] def elabQedAsProp : TermElab := fun stx _ => do
  let e ← instantiateMVars (← elabTerm (stx.getArg 1) none); let ty ← whnf (← inferType e)
  if ty.isProp then return e else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true) else ensureHasType (mkSort Level.zero) e

open Lean Meta Elab Term in
@[term_elab qedEqPropStx] def elabQedEqProp : TermElab := fun stx _ => do
  let (aStx, bStx) : Term × Term := (⟨stx.getArg 1⟩, ⟨stx.getArg 3⟩); let savedMsgs ← Core.getMessageLog; Core.resetMessageLog
  let eqTry? ← try
      let e ← elabTerm (← `(($aStx = $bStx))) (some (mkSort Level.zero)); let newMsgs ← Core.getMessageLog
      if newMsgs.hasErrors then Core.setMessageLog savedMsgs; pure none
      else
        Core.setMessageLog (savedMsgs ++ newMsgs)
        if (← try synthInstance? (← mkAppM ``Decidable #[e]) catch _ => pure none).isSome then pure (some e) else pure none
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

private abbrev pExpr (p : Nat := 0) : Parser := categoryParser `qedExpr p
private abbrev pType (p : Nat := 0) : Parser := categoryParser `qedType p
private abbrev pPat  (p : Nat := 0) : Parser := categoryParser `qedPat p

/-- Non-reserved keyword parser so English keywords never pollute Lean's global token table. -/
def kw (s : String) : Parser := nonReservedSymbol s (includeIdent := true)
def qedBinder : Parser := ident <|> symbol "_"
def qedEnvRef : Parser := node `Qed.Lang.envRef ((identEq `secret <|> identEq `env) >> "(" >> strLit >> ")" >> optional (" ?? " >> strLit))

@[qedTypeMod_parser] def qedTypeModArr : Parser := leading_parser atomic ("[" >> "]")
@[qedTypeMod_parser] def qedTypeModOpt : Parser := leading_parser symbol "?"
@[qedTypeMod_parser] def qedTypeModErr : Parser := leading_parser symbol "!"

private abbrev pTypeMods : Parser := many (categoryParser `qedTypeMod 0)
@[qedType_parser] def qedTypeProto : Parser := leading_parser:maxPrec atomic (kw "Proto" >> "(") >> ident >> ")" >> pTypeMods
@[qedType_parser] def qedTypeForm  : Parser := leading_parser:maxPrec atomic (identEq `Form >> "(") >> pType >> ")" >> pTypeMods
@[qedType_parser] def qedTypeDict  : Parser := leading_parser:maxPrec atomic ("{" >> pType >> ":") >> pType >> "}" >> pTypeMods
@[qedType_parser] def qedTypeParen : Parser := leading_parser:maxPrec "(" >> sepBy1 pType "," >> ")" >> pTypeMods
@[qedType_parser] def qedTypeAtom  : Parser := leading_parser:maxPrec ident >> pTypeMods
@[qedType_parser] def qedTypeNum   : Parser := leading_parser:maxPrec numLit
@[qedType_parser 90] def qedTypeApp   : TrailingParser := trailing_parser:90 checkLineEq >> notFollowedBy (atomic (identEq `ok >> "[")) "ok" >> pType 91
@[qedType_parser 25] def qedTypeArrow : TrailingParser := trailing_parser:25 symbol "->" >> pType 25

private abbrev pPatArgsOpt : Parser := optional (checkNoWsBefore "" >> "(" >> sepBy pPat "," >> ")")
@[qedPat_parser] def qedPatWild  : Parser := leading_parser:maxPrec symbol "_"
@[qedPat_parser] def qedPatNum   : Parser := leading_parser:maxPrec numLit
@[qedPat_parser] def qedPatStr   : Parser := leading_parser:maxPrec strLit
@[qedPat_parser] def qedPatChar  : Parser := leading_parser:maxPrec charLit
@[qedPat_parser] def qedPatParen : Parser := leading_parser:maxPrec "(" >> sepBy pPat "," >> ")"
@[qedPat_parser] def qedPatList  : Parser := leading_parser:maxPrec "[" >> sepBy pPat "," >> "]"
@[qedPat_parser] def qedPatDot   : Parser := leading_parser:maxPrec atomic ("." >> checkNoWsBefore "") >> ident >> pPatArgsOpt
@[qedPat_parser] def qedPatIdent : Parser := leading_parser:maxPrec ident >> pPatArgsOpt

@[qedCallArg_parser] def qedCallArgNamed : Parser := leading_parser atomic (ident >> "=" >> notFollowedBy (symbol "=") "=") >> pExpr
@[qedCallArg_parser] def qedCallArgWhere : Parser := leading_parser atomic (symbol "where" >> "=" >> notFollowedBy (symbol "=") "=") >> pExpr
@[qedCallArg_parser] def qedCallArgPos   : Parser := leading_parser pExpr

def qedRecField  : Parser := node `Qed.Lang.recField  (atomic (ident >> ((symbol "=" >> notFollowedBy (symbol "=") "=") <|> symbol "+=" <|> symbol "-=")) >> pExpr)
def qedDictEntry : Parser := node `Qed.Lang.dictEntry (pExpr >> ":" >> pExpr)
def qedPatAlt    : Parser := node `Qed.Lang.qedPatAlt (sepBy1 pPat ",")
def qedCasePats  : Parser := sepBy1 qedPatAlt "|"
def qedExprCase  : Parser := leading_parser withPosition (atomic (kw "case") >> qedCasePats >> ":" >> pExpr)
def qedLamParam  : Parser := node `Qed.Lang.lamParam  (qedBinder >> optional (":" >> pType))

private def notReservedExprKw : Parser := notFollowedBy (
  kw "and" <|> kw "or" <|> kw "not" <|> kw "is" <|> kw "pass" <|> kw "elif" <|> kw "case" <|> kw "catch" <|> kw "atomic" <|>
  symbol "in" <|> symbol "if" <|> symbol "else" <|> symbol "match" <|> symbol "for" <|> symbol "return" <|> symbol "let") "expression"

@[qedExpr_parser] def qedRawTerm     : Parser := leading_parser:maxPrec "qedRaw%(" >> termParser >> ")"
@[qedExpr_parser] def qedLitNum      : Parser := leading_parser:maxPrec numLit
@[qedExpr_parser] def qedLitSci      : Parser := leading_parser:maxPrec scientificLit
@[qedExpr_parser] def qedLitStr      : Parser := leading_parser:maxPrec strLit
@[qedExpr_parser] def qedLitChar     : Parser := leading_parser:maxPrec charLit
@[qedExpr_parser] def qedFStr        : Parser := leading_parser:maxPrec atomic (kw "f" >> checkNoWsBefore "") >> interpolatedStr (categoryParser `qedExpr 0)
@[qedExpr_parser] def qedArrLit      : Parser := leading_parser:maxPrec "[" >> sepBy pExpr "," >> "]"
@[qedExpr_parser] def qedDictLit     : Parser := leading_parser:maxPrec atomic ("{" >> pExpr >> ":") >> pExpr >> many ("," >> qedDictEntry) >> optional "," >> "}"
@[qedExpr_parser] def qedRecLit      : Parser := leading_parser:maxPrec "{" >> optional (atomic (pExpr >> symbol "with")) >> sepBy qedRecField "," >> "}"
@[qedExpr_parser] def qedFieldSetter : Parser := leading_parser:maxPrec atomic ("(" >> ident >> "=" >> symbol "_" >> ")")
@[qedExpr_parser] def qedTypeAscr    : Parser := leading_parser:maxPrec atomic ("(" >> pExpr >> ":" >> pType >> ")")
@[qedExpr_parser] def qedParen       : Parser := leading_parser:maxPrec "(" >> sepBy pExpr "," >> ")"
@[qedExpr_parser] def qedPlaceholder : Parser := leading_parser:maxPrec symbol "_"
@[qedExpr_parser] def qedDotIdent    : Parser := leading_parser:maxPrec atomic ("." >> checkNoWsBefore "") >> ident
@[qedExpr_parser] def qedIdent       : Parser := leading_parser:maxPrec notReservedExprKw >> ident

@[qedExpr_parser 90] def qedCall   : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "(" >> sepBy (categoryParser `qedCallArg 0) "," >> ")"
@[qedExpr_parser 90] def qedIndex  : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "[" >> pExpr >> "]"
@[qedExpr_parser 90] def qedProj   : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> "." >> checkNoWsBefore "" >> ident
@[qedExpr_parser 90] def qedUnwrap : TrailingParser := trailing_parser:90 checkNoWsBefore "" >> symbol "?"

@[qedExpr_parser 80] def qedNeg   : Parser         := leading_parser:80  "-" >> pExpr 80
@[qedExpr_parser 75] def qedAwait : Parser         := leading_parser:75  atomic (kw "await") >> pExpr 75
@[qedExpr_parser 70] def qedMul   : TrailingParser := trailing_parser:70 symbol "*"  >> pExpr 71
@[qedExpr_parser 70] def qedDiv   : TrailingParser := trailing_parser:70 symbol "/"  >> pExpr 71
@[qedExpr_parser 70] def qedMod   : TrailingParser := trailing_parser:70 symbol "%"  >> pExpr 71
@[qedExpr_parser 65] def qedAdd   : TrailingParser := trailing_parser:65 symbol "+"  >> pExpr 66
@[qedExpr_parser 65] def qedSub   : TrailingParser := trailing_parser:65 symbol "-"  >> pExpr 66
@[qedExpr_parser 65] def qedCat   : TrailingParser := trailing_parser:65 symbol "++" >> pExpr 66

def qedCmpOp : Parser := node `Qed.Lang.cmpOp (
  symbol "==" <|> symbol "!=" <|> symbol "<=" <|> symbol ">=" <|> symbol "<" <|> symbol ">" <|>
  symbol "in" <|> atomic (kw "not" >> symbol "in") <|> atomic (kw "is" >> kw "not") <|> kw "is")
def qedCmpLink : Parser := node `Qed.Lang.cmpLink (qedCmpOp >> pExpr 55)
@[qedExpr_parser 50] def qedCmp : TrailingParser := trailing_parser:50 many1 qedCmpLink

@[qedExpr_parser 40] def qedNot : Parser         := leading_parser:40  atomic (kw "not") >> pExpr 40
@[qedExpr_parser 35] def qedAnd : TrailingParser := trailing_parser:35 atomic (kw "and") >> pExpr 35
@[qedExpr_parser 30] def qedOr  : TrailingParser := trailing_parser:30 atomic (kw "or")  >> pExpr 30
@[qedExpr_parser 25] def qedImp : TrailingParser := trailing_parser:25 symbol "->" >> pExpr 25

@[qedExpr_parser 20] def qedTernary : TrailingParser := trailing_parser:20 atomic (checkColGt >> symbol "if") >> pExpr 21 >> optional (atomic (checkColGt >> symbol "else") >> pExpr 20)
@[qedExpr_parser 18] def qedLam1    : Parser := leading_parser:18 atomic (qedBinder >> " => ") >> pExpr 15
@[qedExpr_parser 18] def qedLamN    : Parser := leading_parser:18 atomic ("(" >> sepBy qedLamParam "," >> ")" >> " => ") >> pExpr 15
@[qedExpr_parser 15] def qedAllIn   : Parser := leading_parser:15 atomic (kw "all" >> ident >> symbol "in") >> pExpr 55 >> ":" >> pExpr 15
@[qedExpr_parser 15] def qedAnyIn   : Parser := leading_parser:15 atomic (kw "any" >> ident >> symbol "in") >> pExpr 55 >> ":" >> pExpr 15
@[qedExpr_parser 15] def qedAllVars : Parser := leading_parser:15 atomic (kw "all" >> sepBy1 ident "," >> ":") >> pExpr 15

@[qedExpr_parser 10] def qedExprLet   : Parser := leading_parser:10 withPosition (symbol "let" >> qedBinder >> optional (":" >> pType) >> "=" >> pExpr >> ";" >> pExpr)
@[qedExpr_parser 10] def qedExprIfLet : Parser := leading_parser:10 withPosition (atomic (symbol "if" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> pExpr >> optional (atomic (checkColGe >> symbol "else" >> ":") >> pExpr))
@[qedExpr_parser 10] def qedExprIf    : Parser := leading_parser:10 withPosition (symbol "if" >> notFollowedBy (symbol "let") "let" >> pExpr >> ":" >> pExpr >> optional (atomic (checkColGe >> symbol "else" >> ":") >> pExpr))
@[qedExpr_parser 10] def qedExprFor   : Parser := leading_parser:10 withPosition (atomic (symbol "for" >> pPat >> symbol "in") >> pExpr >> ":" >> pExpr)
@[qedExpr_parser 10] def qedExprMatch : Parser := leading_parser:10 withPosition (symbol "match" >> sepBy1 pExpr "," >> ":" >> many1 (checkColGt >> qedExprCase))

def qedSuite : Parser := node `Qed.Lang.suite (
  (checkLineEq >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
  (checkColGt "expected indented block" >> withPosition (many1 (checkColEq "expected aligned statement" >> categoryParser `qedStmt 0))))
def qedStmtCase        : Parser := leading_parser withPosition (atomic (kw "case") >> qedCasePats >> ":" >> qedSuite)
def qedElifClause      : Parser := node `Qed.Lang.elifClause      (atomic (checkColEq >> kw "elif") >> pExpr >> ":" >> qedSuite)
def qedCatchArms       : Parser := node `Qed.Lang.catchArms       (":" >> many1 (checkColGt >> qedStmtCase))
def qedCatchSingle     : Parser := node `Qed.Lang.catchSingle     (qedBinder >> ":" >> qedSuite)
def qedLetCatch        : Parser := node `Qed.Lang.letCatch        (atomic (checkColGe >> kw "catch" >> notFollowedBy (symbol "=" <|> symbol "+=" <|> symbol "-=") "assignment") >> (qedCatchArms <|> qedCatchSingle))
def qedLetPredictBlock : Parser := node `Qed.Lang.letPredictBlock (checkColGe >> withPosition (atomic (kw "predict" >> ":") >> qedSuite))
def qedLetPredictExpr  : Parser := node `Qed.Lang.letPredictExpr  (checkColGe >> withPosition (atomic (kw "predict" >> notFollowedBy (symbol ":" <|> symbol "=" <|> symbol "+=" <|> symbol "-=") "predict") >> pExpr))
def qedLetPredict      : Parser := qedLetPredictBlock <|> qedLetPredictExpr
def qedLetOnConfirm    : Parser := node `Qed.Lang.letOnConfirm    (checkColGe >> withPosition (atomic (kw "on_confirm" >> ":") >> qedSuite))
def qedLetRollback     : Parser := node `Qed.Lang.letRollback     (checkColGe >> withPosition (atomic (kw "rollback" >> optional (checkLineEq >> "(" >> qedBinder >> ")") >> ":") >> qedSuite))
def qedLetClause       : Parser := qedLetPredict <|> qedLetOnConfirm <|> qedLetRollback <|> qedLetCatch

def qedLetElseBlock : Parser := node `Qed.Lang.letElseBlock (":" >> qedSuite)
def qedLetElseInline : Parser := node `Qed.Lang.letElseInline (checkLineEq >> categoryParser `qedStmt 0)

@[qedStmt_parser] def qedStmtPass    : Parser := leading_parser withPosition (atomic (kw "pass"))
@[qedStmt_parser] def qedStmtReturn  : Parser := leading_parser withPosition (symbol "return" >> optional (checkLineEq >> pExpr))
@[qedStmt_parser] def qedStmtAtomic  : Parser := leading_parser withPosition (atomic (kw "atomic" >> ":") >> qedSuite)
@[qedStmt_parser] def qedStmtLetElse : Parser := leading_parser withPosition (
  atomic (symbol "let" >> pPat >> "=" >> pExpr >> checkColGe >> symbol "else") >> (qedLetElseBlock <|> qedLetElseInline))
@[qedStmt_parser] def qedStmtLet     : Parser := leading_parser withPosition (symbol "let" >> qedBinder >> optional (":" >> pType) >> "=" >> pExpr >> many qedLetClause)
@[qedStmt_parser] def qedStmtIfLet  : Parser := leading_parser withPosition (atomic (symbol "if" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> qedSuite >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
@[qedStmt_parser] def qedStmtIf     : Parser := leading_parser withPosition (symbol "if" >> notFollowedBy (symbol "let") "let" >> pExpr >> ":" >> qedSuite >> many qedElifClause >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
@[qedStmt_parser] def qedStmtMatch  : Parser := leading_parser withPosition (symbol "match" >> sepBy1 pExpr "," >> ":" >> many1 (checkColGt >> qedStmtCase))
@[qedStmt_parser] def qedStmtAssign : Parser := leading_parser withPosition (atomic (pExpr 90 >> ((symbol "=" >> notFollowedBy (symbol "=") "=") <|> symbol "+=" <|> symbol "-=")) >> pExpr >> optional qedLetPredict)
@[qedStmt_parser] def qedStmtExpr   : Parser := leading_parser withPosition (notFollowedBy (symbol "if" <|> symbol "match" <|> symbol "return" <|> symbol "let" <|> kw "atomic" <|> kw "pass") "statement" >> pExpr)

end Parsers

/-! ## Unified AST Unpacking, Type & Pattern Lowering -/

open Lean

def pushUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α := if xs.contains x then xs else xs.push x
partial def stxAny (p : Syntax → Bool) (stx : Syntax) : Bool := p stx || stx.getArgs.any (stxAny p)

def splitCallArgsPure (callName : String) (rawArgs : Array Syntax) (validKeys : Option (List String) := none)
    (allowWhere : Bool := false) (errRef : Syntax := Syntax.missing) : Except (Syntax × String) (Array Syntax × Array (String × Syntax)) := do
  let mut posArgs : Array Syntax := #[]; let mut namedArgs : Array (String × Syntax) := #[]
  for a in rawArgs do
    let k := a.getKind
    if k == ``qedCallArgPos then posArgs := posArgs.push (a.getArg 0)
    else if allowWhere && k == ``qedCallArgWhere then namedArgs := namedArgs.push ("where", a.getArg 2)
    else if k == ``qedCallArgNamed then
      let key := (a.getArg 0).getId.eraseMacroScopes.toString
      if let some allowed := validKeys then unless allowed.contains key do
        throw (if errRef.isMissing then a else errRef, s!"unknown argument `{key}` in `{callName}(...)`{Qed.Diag.didYouMean key allowed} (supported: {String.intercalate ", " allowed})")
      namedArgs := namedArgs.push (key, a.getArg 2)
    else throw (a, s!"unexpected argument in `{callName}(...)`")
  return (posArgs, namedArgs)

def splitCallArgs {m : Type → Type} [Monad m] [MonadError m] (callName : String) (rawArgs : Array Syntax)
    (validKeys : Option (List String) := none) (allowWhere : Bool := false) (errRef : Syntax := Syntax.missing) : m (Array Syntax × Array (String × Syntax)) :=
  match splitCallArgsPure callName rawArgs validKeys allowWhere errRef with | .ok r => pure r | .error (r, mg) => throwErrorAt r mg

def splitCallArgsMacro (callName : String) (rawArgs : Array Syntax) (validKeys : Option (List String) := none)
    (allowWhere : Bool := false) (errRef : Syntax := Syntax.missing) : MacroM (Array Syntax × Array (String × Syntax)) :=
  match splitCallArgsPure callName rawArgs validKeys allowWhere errRef with | .ok r => pure r | .error (r, mg) => Macro.throwErrorAt r mg

structure ParsedEnvRef where mk :: (isSecret : Bool) (envKey : String) (default? : Option String) deriving Inhabited, Repr

def parseQedEnvRef {m : Type → Type} [Monad m] [MonadError m] (ctxDesc : String) (stx : Syntax) : m ParsedEnvRef := do
  let envKey := (⟨stx.getArg 2⟩ : TSyntax `str).getString
  if envKey.isEmpty then throwErrorAt stx s!"environment variable name in {ctxDesc} must not be empty"
  let defOpt := stx.getArg 4
  return .mk ((stx.getArg 0).getId.eraseMacroScopes == `secret) envKey (if defOpt.getNumArgs == 2 then some (⟨defOpt.getArg 1⟩ : TSyntax `str).getString else none)

partial def suiteStmts (stx : Syntax) : Array Syntax :=
  let body := if stx.getKind == `Qed.Lang.suite then stx.getArg 0 else stx; if body.getKind == nullKind then body.getArgs.filter (!·.isAtom) else #[body]
partial def unwrapParens1 (stx : Syntax) : Syntax :=
  if stx.getKind == ``qedParen && (stx.getArg 1).getSepArgs.size == 1 then unwrapParens1 (stx.getArg 1).getSepArgs[0]! else stx
partial def extractDottedChain? (stx : Syntax) : Option (List String) :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent then some ((u.getArg 0).getId.eraseMacroScopes.components.map (·.toString))
  else if u.getKind == ``qedProj then (extractDottedChain? (u.getArg 0)).map (· ++ [(u.getArg 2).getId.eraseMacroScopes.toString]) else none
partial def splitAndStx (stx : Syntax) : Array Syntax :=
  let u := unwrapParens1 stx; if u.getKind == ``qedAnd then splitAndStx (u.getArg 0) ++ splitAndStx (u.getArg 2) else #[u]

partial def collectQedPatIds (stx : Syntax) : Array Name :=
  let k := stx.getKind
  if k == ``qedPatIdent then
    if (stx.getArg 1).getNumArgs == 3 then ((stx.getArg 1).getArg 1).getSepArgs.flatMap collectQedPatIds
    else let vn := (stx.getArg 0).getId.eraseMacroScopes; let s := vn.toString
         if vn.isAtomic && !["_", "none", "true", "false"].contains s && !s.front.isUpper then #[vn] else #[]
  else if k == ``qedPatDot && (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs.flatMap collectQedPatIds
  else if k == ``qedPatParen || k == ``qedPatList then (stx.getArg 1).getSepArgs.flatMap collectQedPatIds else #[]

def extractCasePatAlts (patsNode : Syntax) : Array (Array Syntax) :=
  let items := patsNode.getSepArgs
  if items.any (·.getKind == `Qed.Lang.qedPatAlt) then
    items.map fun alt => if alt.getKind == `Qed.Lang.qedPatAlt then (alt.getArg 0).getSepArgs else #[alt]
  else
    #[items]

def collectCasePatIds (altStxs : Array (Array Syntax)) : Array Name :=
  altStxs.foldl (init := #[]) fun acc ps => acc ++ ps.flatMap collectQedPatIds

@[noinline, nospecialize]
def mkMatchAltFromAlts {m : Type → Type} [Monad m] [MonadQuotation m]
    (altPatTerms : Array (Array Term)) (rhs : Term) : m (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  if h : altPatTerms.size = 1 then
    let ps := altPatTerms[0]
    `(Lean.Parser.Term.matchAltExpr| | $[$ps:term],* => $rhs)
  else
    let groups : Array Syntax ← altPatTerms.mapM fun ps => do
      let a ← `(Lean.Parser.Term.matchAltExpr| | $[$ps:term],* => $rhs)
      pure ((a.raw.getArg 1).getArg 0)
    let mut sepArgs : Array Syntax := #[]
    for (g, i) in groups.zipIdx do
      if i > 0 then sepArgs := sepArgs.push (Syntax.atom .none "|")
      sepArgs := sepArgs.push g
    let base ← `(Lean.Parser.Term.matchAltExpr| | _ => $rhs)
    return ⟨base.raw.setArg 1 (Syntax.node .none nullKind sepArgs)⟩

partial def stxMentionsVar (v : String) (stx : Syntax) : Bool :=
  let k := stx.getKind; let isB (b : Syntax) := b.isIdent && b.getId.eraseMacroScopes.toString == v
  if k == ``qedIdent then match (stx.getArg 0).getId.eraseMacroScopes.components with | root :: _ => root.toString == v | [] => false
  else if k == ``qedLam1 then !isB (stx.getArg 0) && stxMentionsVar v (stx.getArg 2)
  else if k == ``qedLamN then !(stx.getArg 1).getSepArgs.any (fun p => isB (p.getArg 0)) && stxMentionsVar v (stx.getArg 4)
  else if k == ``qedExprLet then stxMentionsVar v (stx.getArg 4) || (!isB (stx.getArg 1) && stxMentionsVar v (stx.getArg 6))
  else if k == ``qedExprFor then stxMentionsVar v (stx.getArg 3) || (!(collectQedPatIds (stx.getArg 1)).any (·.toString == v) && stxMentionsVar v (stx.getArg 5))
  else stx.getArgs.any (stxMentionsVar v)

def extractElseSuite (optElse : Syntax) : Option (Array Syntax) := if optElse.getNumArgs == 3 then some (suiteStmts (optElse.getArg 2)) else none
def extractLetElseStmts (stmt : Syntax) : Array Syntax :=
  let tail := stmt.getArg 5
  if tail.getKind == `Qed.Lang.letElseBlock then suiteStmts (tail.getArg 1) else #[tail.getArg 0]
def extractOptElseExpr? (optElse : Syntax) : Option Syntax :=
  if optElse.getNumArgs == 2 then some (optElse.getArg 1) else if optElse.getNumArgs == 3 then some (optElse.getArg 2) else none
def desugarElifs (elifs : Array Syntax) (optElse : Syntax) : Option (Array Syntax) :=
  if elifs.isEmpty then extractElseSuite optElse else
  let f := elifs[0]!; let i := f.getHeadInfo
  some #[Syntax.node i ``qedStmtIf #[Syntax.atom i "if", f.getArg 1, f.getArg 2, f.getArg 3, Syntax.node i nullKind (elifs.extract 1 elifs.size), optElse]]

def matchMethodCall? (stx : Syntax) : Option (Syntax × String × Array Syntax) := do
  let u := unwrapParens1 stx; guard (u.getKind == ``qedCall); let (callee, rawArgs) := (u.getArg 0, (u.getArg 2).getSepArgs)
  if callee.getKind == ``qedProj then return (callee.getArg 0, (callee.getArg 2).getId.toString, rawArgs)
  else if callee.getKind == ``qedIdent then
    let parts := (callee.getArg 0).getId.toString.splitOn "."; guard (parts.length >= 2)
    return (Syntax.node (SourceInfo.fromRef (callee.getArg 0)) ``qedIdent #[mkIdentFrom (callee.getArg 0) ((parts.take (parts.length - 1)).foldl Name.str .anonymous)], parts.getLast!, rawArgs)
  else failure

def matchIdentMethodCall? (stx : Syntax) : Option (Ident × String × Array Syntax) := do
  let (target, meth, rawArgs) ← matchMethodCall? stx; guard (target.getKind == ``qedIdent)
  let id : Ident := ⟨target.getArg 0⟩; match id.getId.eraseMacroScopes with | .str .anonymous _ => return (id, meth, rawArgs) | _ => failure

private def matchUnaryMethodCall? (expected : String) (stx : Syntax) : Option (Syntax × Syntax) := do
  let (target, meth, rawArgs) ← matchMethodCall? stx; guard (meth == expected && rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos); return (target, rawArgs[0]![0])

def matchPushCall?   : Syntax → Option (Syntax × Syntax) := matchUnaryMethodCall? "push"
def matchRemoveCall? : Syntax → Option (Syntax × Syntax) := matchUnaryMethodCall? "remove"

inductive TypeMod where | array | option | fallible deriving Inhabited, DecidableEq, Repr

def stxSnippet (stx : Syntax) : String :=
  match ((stx.unsetTrailing.reprint.getD "").trimAscii.toString).splitOn "\n" with | [] => "" | [s] => s.trimAscii.toString | f :: _ => f.trimAscii.toString ++ " ..."

def splitIdentMods (id : Ident) : MacroM (Ident × Array TypeMod) := do
  let chars := id.getId.toString.toList; let revMods := chars.reverse.takeWhile fun c => c == '?' || c == '!'
  let baseChars := chars.take (chars.length - revMods.length)
  if baseChars.isEmpty then Macro.throwErrorAt id s!"invalid type `{id.getId}`"
  return (mkIdentFrom id ((String.ofList baseChars |>.splitOn ".").foldl Name.str .anonymous),
          revMods.reverse.toArray.filterMap fun c => if c == '?' then some .option else if c == '!' then some .fallible else none)

def parseTypeModNode (m : Syntax) : MacroM TypeMod :=
  let k := m.getKind
  if k == ``qedTypeModArr then pure .array else if k == ``qedTypeModOpt then pure .option else if k == ``qedTypeModErr then pure .fallible
  else match (m.reprint.getD "").trimAscii.toString with
    | "[]" => pure .array | "?" => pure .option | "!" => pure .fallible | s => Macro.throwErrorAt m s!"unknown type modifier `{s}`"

def resolveBaseTypeTerm (baseId : Ident) : Term := match baseId.getId with
  | `Bytes => mkIdentFrom baseId `Qed.Bytes | `Json => mkIdentFrom baseId `Qed.Json | `Secret => mkIdentFrom baseId `Qed.Secret | `WebhookUrl => mkIdentFrom baseId `Qed.Server.WebhookUrl | _ => ⟨baseId.raw⟩

private def foldRight1M {m : Type → Type} [Monad m] (empty : m Term) (combine : Term → Term → m Term) (xs : Array Term) : m Term :=
  if xs.isEmpty then empty else if xs.size == 1 then pure xs[0]! else xs.foldrM (init := xs.back!) (start := xs.size - 1) combine

def buildProdType {m : Type → Type} [Monad m] [MonadQuotation m] : Array Term → m Term := foldRight1M `(Unit) fun a b => `($a × $b)
def buildTupleVal {m : Type → Type} [Monad m] [MonadQuotation m] : Array Term → m Term := foldRight1M `(()) fun a b => `(($a, $b))
def mkAppTerms {m : Type → Type} [Monad m] [MonadQuotation m] (fn : Term) (args : Array Term) : m Term :=
  if args.isEmpty then pure fn else `($fn $args*)

def extractTupleProjections {m : Type → Type} [Monad m] [MonadQuotation m] (tupleVar : Ident) (n : Nat) : m (Array Term) := do
  if n == 0 then return #[]
  let mut out : Array Term := #[]; let mut cur : Term := ⟨tupleVar.raw⟩
  for i in [0:n] do if i + 1 < n then out := out.push (← `(($cur).1)); cur ← `(($cur).2) else out := out.push cur
  return out

structure LoweredQedType where mk ::
  (term : Term) (isFallible isProto isForm isOption : Bool := false) (innerOpt? : Option Term := none) (baseName : Name := .anonymous) (mods : Array TypeMod := #[])
deriving Inhabited

private def applyTypeModsInfo (base : Term) (mods : Array TypeMod) (allowFallible : Bool)
    (ref : Syntax) (ctxDesc? : Option String := none) (nestedErr? : Option String := none) : MacroM (Term × Bool × Option Term) := do
  let mut acc := base; let mut isFallible := false; let mut innerOpt? : Option Term := none
  for (md, i) in mods.zipIdx do match md with
    | .array  => acc ← `(Array $acc); innerOpt? := none
    | .option => innerOpt? := some acc; acc ← `(Option $acc)
    | .fallible =>
        if !allowFallible then Macro.throwErrorAt ref (nestedErr?.getD <| match ctxDesc? with
          | some d => s!"fallible `!` modifier is not allowed on {d}; only server `def` return types may use `T!`"
          | none   => "fallible `!` modifier is only allowed on server `def` return types")
        if i + 1 < mods.size then Macro.throwErrorAt ref "place `!` last on fallible return types (for example `Book[]!` instead of `Book![]`)"
        isFallible := true
  return (acc, isFallible, innerOpt?)

partial def lowerQedTypeInfo (stx : Syntax) (allowFallible := false) (allowHigherOrder := true) (ctxDesc? : Option String := none) : MacroM LoweredQedType := do
  let rec go (s : Syntax) (allowFall : Bool) (nestedErr? : Option String) : MacroM LoweredQedType := do
    let mkInvalidErr (node : Syntax) : MacroM LoweredQedType := do
      let sn := stxSnippet node; let what := if sn.isEmpty then "" else s!" `{sn}`"
      Macro.throwErrorAt node <| if allowHigherOrder then s!"invalid Qed type{what}; expected a type such as `T`, `T[]`, `T?`, `T!`, `Resource T`, or `A -> B`"
        else s!"invalid server type{what}; expected `T`, `T[]`, `T?`, `T!`, `(T, U)`, `Proto(T)`, or `Form(T)`"
    let finishMods (base : Term) (mods : Array TypeMod) (baseName : Name) (isProto := false) (isForm := false) : MacroM LoweredQedType := do
      let (term, isFallible, innerOpt?) ← applyTypeModsInfo base mods allowFall s ctxDesc? nestedErr?
      return .mk term isFallible isProto isForm innerOpt?.isSome innerOpt? baseName mods
    let parseMods (n : Syntax) := n.getArgs.mapM parseTypeModNode
    let k := s.getKind
    if k == ``qedTypeProto then let (baseId, initMods) ← splitIdentMods ⟨s.getArg 2⟩; finishMods ⟨baseId.raw⟩ (initMods ++ (← parseMods (s.getArg 4))) baseId.getId.eraseMacroScopes (isProto := true)
    else if k == ``qedTypeForm then
      let inner ← go (s.getArg 2) false (some "fallible `!` modifier cannot appear inside `Form(...)`")
      let extraMods ← parseMods (s.getArg 4)
      let (term, isFallible, innerOpt?) ← applyTypeModsInfo inner.term extraMods allowFall s ctxDesc? nestedErr?
      let opt? := innerOpt? <|> (if extraMods.isEmpty then inner.innerOpt? else none)
      return .mk term isFallible inner.isProto true opt?.isSome opt? inner.baseName (inner.mods ++ extraMods)
    else if k == ``qedTypeDict then
      let kI ← go (s.getArg 1) false (some "fallible `!` modifier cannot appear inside a dictionary key type")
      let vI ← go (s.getArg 3) false (some "fallible `!` modifier cannot appear inside a dictionary value type")
      finishMods (← `($(mkIdentFrom s `Qed.Dict) $(kI.term) $(vI.term))) (← parseMods (s.getArg 5)) `Qed.Dict
    else if k == ``qedTypeParen then
      let ls ← (s.getArg 1).getSepArgs.mapM fun p => return (← go p false (some "fallible `!` modifier cannot appear inside a tuple type")).term
      finishMods (← buildProdType ls) (← parseMods (s.getArg 3)) `Prod
    else if k == ``qedTypeAtom then let (baseId, initMods) ← splitIdentMods ⟨s.getArg 0⟩; finishMods (resolveBaseTypeTerm baseId) (initMods ++ (← parseMods (s.getArg 1))) baseId.getId.eraseMacroScopes
    else if k == ``qedTypeNum then return { term := ⟨s.getArg 0⟩ }
    else if k == ``qedTypeApp || k == ``qedTypeArrow then
      if k == ``qedTypeApp && (s.getArg 0).getKind == ``qedTypeAtom && ((s.getArg 0).getArg 1).getArgs.isEmpty then
        let fnName := ((s.getArg 0).getArg 0).getId.eraseMacroScopes; let argStr := let sn := stxSnippet (s.getArg 1); if sn.isEmpty then "T" else sn
        if fnName == `Array || fnName == `Option then Macro.throwErrorAt s s!"use `{argStr}{if fnName == `Array then "[]" else "?"}` instead of `{fnName} {argStr}`"
        if allowHigherOrder && fnName == `jsonOnly then Macro.throwErrorAt s s!"use `jsonOnly({argStr})` with parentheses instead of `jsonOnly {argStr}`"
      if k == ``qedTypeArrow && !allowHigherOrder then return ← mkInvalidErr s
      let (l, r) := ((← go (s.getArg 0) false none).term, (← go (s.getArg (if k == ``qedTypeApp then 1 else 2)) false none).term)
      return { term := ← if k == ``qedTypeApp then `($l $r) else `($l → $r) }
    else mkInvalidErr s
  go stx allowFallible none

def lowerQedType (stx : Syntax) (allowFallible := false) : MacroM (Term × Bool) := do let info ← lowerQedTypeInfo stx allowFallible; return (info.term, info.isFallible)

partial def inferQedTypeDefault? (stx : Syntax) : MacroM (Option Term) := do
  let modDef (n : Syntax) (init : Array TypeMod := #[]) : MacroM (Option Term) := do
    match (init ++ (← n.getArgs.mapM parseTypeModNode)).back? with | some .array => some <$> `(#[]) | some .option => some <$> `(none) | _ => pure none
  let k := stx.getKind
  if k == ``qedTypeDict then if let some d ← modDef (stx.getArg 5) then return some d else some <$> `($(mkIdentFrom stx `Qed.Dict.empty))
  else if k == ``qedTypeParen then
    if let some d ← modDef (stx.getArg 3) then return some d
    if (stx.getArg 1).getSepArgs.size == 1 then inferQedTypeDefault? (stx.getArg 1).getSepArgs[0]! else return none
  else if k == ``qedTypeAtom then modDef (stx.getArg 1) (← splitIdentMods ⟨stx.getArg 0⟩).2
  else if k == ``qedTypeApp && (stx.getArg 0).getKind == ``qedTypeAtom && ((stx.getArg 0).getArg 1).getArgs.isEmpty then
    match ((stx.getArg 0).getArg 0).getId.eraseMacroScopes with | `Resource => some <$> `(.idle) | `Cached => some <$> `({}) | _ => pure none
  else return none

partial def lowerQedPat (stx : Syntax) : MacroM Term := do
  let k := stx.getKind
  if k == ``qedPatWild then `(_)
  else if k == ``qedPatNum || k == ``qedPatStr || k == ``qedPatChar then return ⟨stx.getArg 0⟩
  else if k == ``qedPatParen then buildTupleVal (← (stx.getArg 1).getSepArgs.mapM lowerQedPat)
  else if k == ``qedPatList then
    let ps ← (stx.getArg 1).getSepArgs.mapM lowerQedPat
    `([$[$ps:term],*])
  else if k == ``qedPatDot || k == ``qedPatIdent then
    let headT : Term := if k == ``qedPatDot then ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", stx.getArg 1]⟩ else ⟨stx.getArg 0⟩
    let argsNode := stx.getArg (if k == ``qedPatDot then 2 else 1)
    if argsNode.getNumArgs == 3 then `($headT $(← (argsNode.getArg 1).getSepArgs.mapM lowerQedPat)*) else return headT
  else let sn := stxSnippet stx; Macro.throwErrorAt stx s!"unsupported pattern{if sn.isEmpty then "" else s!" `{sn}`"}; expected `_`, a literal, an identifier, `.ctor(a, b)`, or a tuple `(a, b)`"

def lowerCasePatAlts (patsNode : Syntax) : MacroM (Array (Array Term)) :=
  (extractCasePatAlts patsNode).mapM (·.mapM lowerQedPat)

/-! ## Unified Expression Lowering (`ExprMode`, `lowerQedExpr`, `lowerSimpleQedExpr`) -/

inductive ExprMode where | val | boolCond | propGuard | propInv deriving BEq, DecidableEq
def ExprMode.isProp (m : ExprMode) : Bool := m == .propInv || m == .propGuard
def exprHasIndex (stx : Syntax) : Bool := stxAny (·.getKind == ``qedIndex) stx

def isPlainLiteralOrCtor (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx; let k := u.getKind; let plainFields := ["size", "length", "isSome", "isNone", "isEmpty", "val"]
  if [``qedLitNum, ``qedLitSci, ``qedLitStr, ``qedLitChar, ``qedFStr, ``qedArrLit, ``qedDictLit, ``qedRecLit, ``qedDotIdent, ``qedNeg, ``qedMul, ``qedDiv, ``qedMod, ``qedAdd, ``qedSub, ``qedCat].contains k then true
  else if k == ``qedIdent then
    let nm := (u.getArg 0).getId; let s := nm.toString
    ["true", "false", "none"].contains s || (nm.isStr && nm.getPrefix != .anonymous && plainFields.contains (match nm with | .str _ f => f | _ => s))
  else if k == ``qedProj then plainFields.contains (u.getArg 2).getId.toString
  else k == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.toString == "some"

def isNoneExpr (stx : Syntax) : Bool := let u := unwrapParens1 stx; u.getKind == ``qedIdent && (u.getArg 0).getId.toString == "none"
def cmpOpKind (opStx : Syntax) : String := let raw := (opStx.reprint.getD "").trimAscii.toString; if raw.contains ' ' then String.intercalate " " ((raw.splitOn " ").filter (!·.isEmpty)) else raw
def mkRawExpr (t : Term) : Syntax :=
  let info := t.raw.getHeadInfo
  Syntax.node info ``qedRawTerm #[Syntax.atom info "qedRaw%(", t.raw, Syntax.atom info ")"]

structure LowerHooks (m : Type → Type) where mk ::
  (lowerIdent : Syntax → Ident → ExprMode → m Term) (lowerProj : Syntax → Term → Ident → ExprMode → m Term)
  (lowerIndex : Syntax → Term → Term → ExprMode → m Term)
  (lowerCall : Syntax → Syntax → Array Syntax → ExprMode → (ExprMode → Syntax → m Term) → m (Option Term))
  (lowerUnwrap lowerAwait : Syntax → Syntax → ExprMode → m Term) (lowerJsx : Syntax → ExprMode → m Term)
  (lowerArrElem wrapNamedField : Term → m Term) (lowerType lowerPat : Syntax → m Term)
  (withLocals : Array String → m Term → m Term) (useDirectArray allowOptElse : Bool := false)
  (optElseFallback : Syntax → Term → m Term) (wrapForMap : Syntax → Term → Term → m Term)
  (freshIdent : String → m Ident) (throwErr : Syntax → String → m Term)

def finishTermMode {m : Type → Type} [Monad m] [MonadQuotation m] (mode : ExprMode) (t : Term) : m Term :=
  if mode.isProp then `(qedAsProp($t)) else return t

def LowerHooks.mkDefault {m : Type → Type} [Monad m] [MonadQuotation m] (throwErr : Syntax → String → m Term) : LowerHooks m := {
  lowerIdent := fun _ id mode => finishTermMode mode ⟨id.raw⟩
  lowerProj  := fun _ obj fld mode => do finishTermMode mode (← `(($obj).$fld:ident))
  lowerIndex := fun _ arr idx mode => do finishTermMode mode (← `($arr[$idx]))
  lowerCall  := fun _ _ _ _ _ => pure none
  lowerUnwrap := fun ref _ _ => throwErr ref "operator `?` is only supported inside `server` functions with a fallible (`T!`) or optional (`T?`) return type"
  lowerAwait  := fun ref _ _ => throwErr ref "`await` is only supported in statements (`let x = await ...` or `field = await ...`)"
  lowerJsx    := fun ref _ =>
    if ref.getKind.toString.contains "Jsx" then throwErr ref "JSX elements are only allowed inside view expressions"
    else let sn := stxSnippet ref; throwErr ref s!"unsupported Qed expression{if sn.isEmpty then s!"({ref.getKind})" else s!" `{sn}`"}"
  lowerArrElem := pure, wrapNamedField := pure
  lowerType := fun ref => throwErr ref "type annotations are not supported here"
  lowerPat  := fun ref => throwErr ref "patterns are not supported here"
  withLocals := fun _ k => k, optElseFallback := fun _ _ => `(())
  wrapForMap := fun _ _ t => pure t, freshIdent := fun pfx => pure (mkIdent (Name.mkSimple pfx)), throwErr
}

private def lowerCallExpr {m : Type → Type} [Monad m] [MonadQuotation m]
    (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (finish : Term → m Term) (mode : ExprMode) (stx : Syntax) : m Term := do
  let (calleeStx, rawArgs) := (stx.getArg 0, (stx.getArg 2).getSepArgs)
  if let some custom ← hooks.lowerCall stx calleeStx rawArgs mode go then return custom
  if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId.eraseMacroScopes == `url &&
      rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos && (rawArgs[0]!.getArg 0).getKind == ``qedLitStr then
    let info := SourceInfo.fromRef stx
    return ← finish ⟨Syntax.node info `Qed.Jsx.qedUrlLit #[calleeStx.getArg 0, Syntax.atom info "(", (rawArgs[0]!.getArg 0).getArg 0, Syntax.atom info ")"]⟩
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then
    unless rawArgs.all (·.getKind == ``qedCallArgNamed) do
      let cs := stxSnippet calleeStx; return ← hooks.throwErr stx s!"cannot mix named (`field=val`) and positional arguments in {if cs.isEmpty then "the same call" else s!"call `{cs}(...)`"}"
    let fIds : Array Ident := rawArgs.map (⟨·[0]⟩); let fVals ← rawArgs.mapM fun a => do hooks.wrapNamedField (← go .val (a.getArg 2))
    return ← `(({ $[$fIds:ident := $fVals:term],* } : $(← go .val calleeStx)))
  let calleeTerm ← go .val calleeStx
  let isPropAll := mode.isProp && ((calleeStx.getKind == ``qedProj && [`all, `any].contains (calleeStx.getArg 2).getId) ||
    (calleeStx.getKind == ``qedIdent && match (calleeStx.getArg 0).getId with | .str _ "all" | .str _ "any" => true | _ => false))
  let argTerms ← rawArgs.mapM fun a => let u := unwrapParens1 (a.getArg 0); go (if isPropAll && (u.getKind == ``qedLam1 || u.getKind == ``qedLamN) then .propInv else .val) (a.getArg 0)
  finish (← if argTerms.isEmpty then pure calleeTerm else `($calleeTerm $argTerms*))

private def lowerCmpExpr {m : Type → Type} [Monad m] [MonadQuotation m]
    (hooks : LowerHooks m) (lowerValOp : Syntax → m Term) (mode : ExprMode) (stx : Syntax) : m Term := do
  let lowerSingle (lhsStx : Syntax) (opStr : String) (rhsStx : Syntax) : m Term := do
    let (lS, rS) := if ["==", "!=", "is", "is not"].contains opStr && isNoneExpr lhsStx && !isNoneExpr rhsStx then (rhsStx, lhsStx) else (lhsStx, rhsStx)
    let (a, b) := (← lowerValOp lS, ← lowerValOp rS)
    if ["==", "!=", "is", "is not"].contains opStr then match opStr == "==" || opStr == "is", mode with
      | true,  .propInv => `(($a) = ($b)) | true,  .propGuard => `(qedEqProp($a, $b))   | true,  _ => `(($a) == ($b))
      | false, .propInv => `(($a) ≠ ($b)) | false, .propGuard => `(¬ qedEqProp($a, $b)) | false, _ => `(($a) != ($b))
    else if opStr == "in" || opStr == "not in" then match opStr == "in", mode.isProp with
      | true,  true  => `(Qed.Lang.QedMemProp.memProp ($a) ($b))   | false, true  => `(¬ Qed.Lang.QedMemProp.memProp ($a) ($b))
      | true,  false => `(Qed.Lang.QedMem.mem ($a) ($b))           | false, false => `(!(Qed.Lang.QedMem.mem ($a) ($b)))
    else
      let p ← match opStr with | "<=" => `(($a) ≤ ($b)) | ">=" => `(($a) ≥ ($b)) | "<" => `(($a) < ($b)) | _ => `(($a) > ($b))
      if mode.isProp then return p else `(decide ($p))
  let mut prev := stx.getArg 0; let mut terms : Array Term := #[]
  for lk in (stx.getArg 1).getArgs do terms := terms.push (← lowerSingle prev (cmpOpKind (lk.getArg 0)) (lk.getArg 1)); prev := lk.getArg 1
  match terms.toList with | [] => hooks.throwErr stx "empty comparison" | t :: ts => ts.foldlM (init := t) fun acc x => if mode.isProp then `($acc ∧ $x) else `($acc && $x)

private def lowerAndOrExpr {m : Type → Type} [Monad m] [MonadQuotation m]
    (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (isAnd : Bool) (mode : ExprMode) (stx : Syntax) : m Term := do
  let subMode := if mode.isProp then mode else .boolCond; let (a, b) := (← go subMode (stx.getArg 0), ← go subMode (stx.getArg 2))
  if mode == .propGuard && exprHasIndex (stx.getArg 2) then
    let h ← hooks.freshIdent (if isAnd then "_qedAnd" else "_qedOr")
    if isAnd then `(Qed.Lang.QedAndProp ($a) (fun ($h:ident : $a) => $b)) else `(Qed.Lang.QedOrProp ($a) (fun ($h:ident : ¬ ($a)) => $b))
  else if !mode.isProp && isAnd && exprHasIndex (stx.getArg 2) then let h ← hooks.freshIdent "_qedAnd"; `(if $h:ident : ($a) = true then $b else false)
  else if mode.isProp then (if isAnd then `($a ∧ $b) else `($a ∨ $b)) else (if isAnd then `($a && $b) else `($a || $b))

private def lowerLamExpr {m : Type → Type} [Monad m] [MonadQuotation m]
    (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (isLam1 : Bool) (mode : ExprMode) (stx : Syntax) : m Term := do
  let pEntries : Array (Syntax × Option Syntax) := if isLam1 then #[(stx.getArg 0, none)]
    else (stx.getArg 1).getSepArgs.map fun p => (p.getArg 0, if (p.getArg 1).getNumArgs == 2 then some ((p.getArg 1).getArg 1) else none)
  let body ← hooks.withLocals (pEntries.filterMap fun (b, _) => if b.isIdent then some b.getId.toString else none)
    (go (if mode == .propInv then .propInv else .val) (stx.getArg (if isLam1 then 2 else 4)))
  pEntries.foldrM (init := body) fun (b, tyOpt?) acc => do match tyOpt?, b.isIdent with
    | some tyStx, true  => `(fun ($(⟨b⟩):ident : $(← hooks.lowerType tyStx)) => $acc) | some tyStx, false => `(fun (_ : $(← hooks.lowerType tyStx)) => $acc)
    | none,       true  => `(fun $(⟨b⟩):ident => $acc) | none, false => `(fun _ => $acc)

/-- Unified lowerer for all `qedExpr` nodes across `server`, `component`, `schema`, `invariant`, and JSX. -/
@[noinline, nospecialize]
partial def lowerQedExpr {m : Type → Type} [Monad m] [MonadQuotation m] (hooks : LowerHooks m) (mode : ExprMode) (stx : Syntax) : m Term := do
  let rec go (mode : ExprMode) (stx : Syntax) : m Term := withRef stx do
    let lowerValOp (s : Syntax) : m Term := do let t ← go .val s; if isPlainLiteralOrCtor s then return t else `(Qed.Lang.QedVal.val $t)
    let finish := finishTermMode mode
    let lowerOptElse (ref optNode thenStx : Syntax) (thenT : Term) (errMsg : String) : m Term :=
      if let some elseStx := extractOptElseExpr? optNode then go mode elseStx
      else if hooks.allowOptElse then hooks.optElseFallback thenStx thenT else hooks.throwErr ref errMsg
    match stx.getKind with
    | .str (.str (.str .anonymous "Qed") "Lang") k =>
      match k with
      | "qedRawTerm" => return ⟨stx.getArg 1⟩
      | "qedLitNum" | "qedLitSci" | "qedLitStr" | "qedLitChar" => return ⟨stx.getArg 0⟩
      | "qedFStr" =>
        let mut parts : Array Term := #[]
        for ch in (stx.getArg 1).getArgs do
          if let some litStr := ch.isInterpolatedStrLit? then
            if !litStr.isEmpty then parts := parts.push (Syntax.mkStrLit litStr)
          else parts := parts.push (← `(toString (Qed.Lang.QedVal.val $(← go .val ch))))
        match parts.toList with | [] => return Syntax.mkStrLit "" | p :: ps => ps.foldlM (init := p) fun acc q => `($acc ++ $q)
      | "qedArrLit" =>
        let elems ← (stx.getArg 1).getSepArgs.mapM fun e => do hooks.lowerArrElem (← go .val e)
        if hooks.useDirectArray then `(#[$[$elems],*]) else `(Qed.Lang.QedSeqLit.ofList [$[$elems],*])
      | "qedDictLit" =>
        let mkPair (ks vs : Syntax) : m Term := do `(($(← go .val ks), $(← go .val vs)))
        let pairs := #[← mkPair (stx.getArg 1) (stx.getArg 3)] ++ (← (stx.getArg 4).getArgs.mapM fun r => let e := r.getArg 1; mkPair (e.getArg 0) (e.getArg 2))
        `($(mkIdentFrom stx `Qed.Dict.ofList) [$[$pairs],*])
      | "qedRecLit" =>
        let fields := (stx.getArg 2).getSepArgs; let fIds : Array Ident := fields.map (⟨·[0]⟩)
        let fVals ← fields.mapM fun f => do
          let op := (f.getArg 1).getAtomVal
          if op != "=" then return ← hooks.throwErr f s!"`{op}` in record literal is only supported inside database `update(..., set = \{ ... })`"
          hooks.wrapNamedField (← go .val (f.getArg 2))
        if (stx.getArg 1).getNumArgs == 2 then `({ $(← go .val ((stx.getArg 1).getArg 0)) with $[$fIds:ident := $fVals:term],* })
        else if fIds.isEmpty then `({}) else `({ $[$fIds:ident := $fVals:term],* })
      | "qedFieldSetter" => hooks.throwErr stx s!"`({(stx.getArg 1).getId} = _)` is a component field setter and can only be used inside a `component`"
      | "qedTypeAscr"    => `(($(← go mode (stx.getArg 1)) : $(← hooks.lowerType (stx.getArg 3))))
      | "qedParen"       => let elems := (stx.getArg 1).getSepArgs; if elems.size == 1 then go mode elems[0]! else buildTupleVal (← elems.mapM (go .val))
      | "qedPlaceholder" => `(_)
      | "qedDotIdent"    => finish ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", stx.getArg 1]⟩
      | "qedIdent"  => hooks.lowerIdent stx ⟨stx.getArg 0⟩ mode
      | "qedUnwrap" => hooks.lowerUnwrap stx (stx.getArg 0) mode
      | "qedAwait"  => hooks.lowerAwait stx (stx.getArg 1) mode
      | "qedIndex"  => hooks.lowerIndex stx (← go .val (stx.getArg 0)) (← go .val (stx.getArg 2)) mode
      | "qedProj"   => hooks.lowerProj stx (← go .val (stx.getArg 0)) ⟨stx.getArg 2⟩ mode
      | "qedCall"   => lowerCallExpr hooks go finish mode stx
      | "qedNeg"    => `(-($(← lowerValOp (stx.getArg 1))))
      | "qedMul" | "qedDiv" | "qedMod" | "qedAdd" | "qedSub" | "qedCat" =>
        let (a, b) := (← lowerValOp (stx.getArg 0), ← lowerValOp (stx.getArg 2))
        match k with | "qedMul" => `(($a) * ($b)) | "qedDiv" => `(($a) / ($b)) | "qedMod" => `(($a) % ($b))
                     | "qedAdd" => `(($a) + ($b)) | "qedSub" => `(($a) - ($b)) | _        => `(($a) ++ ($b))
      | "qedCmp" => lowerCmpExpr hooks lowerValOp mode stx
      | "qedNot" => if mode.isProp then `(¬ ($(← go mode (stx.getArg 1)))) else `(!($(← go .boolCond (stx.getArg 1))))
      | "qedAnd" | "qedOr" => lowerAndOrExpr hooks go (k == "qedAnd") mode stx
      | "qedImp" => if mode.isProp then `($(← go mode (stx.getArg 0)) → $(← go mode (stx.getArg 2))) else `(!$(← go .boolCond (stx.getArg 0)) || $(← go .boolCond (stx.getArg 2)))
      | "qedTernary" | "qedExprIf" =>
        let (cI, tI, eI, err) := if k == "qedTernary" then (2, 0, 3, "conditional expression `a if cond else b` requires an `else` branch here") else (1, 3, 4, "`if cond: ...` expression requires `else:` here")
        let (hIf, condT, thenT) := (← hooks.freshIdent "_qedIf", ← go .propGuard (stx.getArg cI), ← go mode (stx.getArg tI))
        let elseT ← lowerOptElse stx (stx.getArg eI) (stx.getArg tI) thenT err
        `(if $hIf:ident : $condT then $thenT else $elseT)
      | "qedLam1" | "qedLamN" => lowerLamExpr hooks go (k == "qedLam1") mode stx
      | "qedAllIn" | "qedAnyIn" =>
        let (bId, arrT) : Ident × Term := (⟨stx.getArg 1⟩, ← go .val (stx.getArg 3))
        let bodyT ← hooks.withLocals #[bId.getId.toString] (go (if mode.isProp then mode else .boolCond) (stx.getArg 5))
        match k == "qedAllIn", mode.isProp with
        | true,  true  => `(∀ $bId:ident ∈ $arrT, $bodyT) | true,  false => `(($arrT).all (fun $bId:ident => $bodyT))
        | false, true  => `(∃ $bId:ident ∈ $arrT, $bodyT) | false, false => `(($arrT).any (fun $bId:ident => $bodyT))
      | "qedAllVars" =>
        unless mode.isProp do return ← hooks.throwErr stx "`all x, y: ...` without `in` is only valid in invariants and logical propositions; for a runtime check over a collection, write `all x in items: ...`"
        let vIds : Array Ident := (stx.getArg 1).getSepArgs.map (⟨·⟩)
        let bodyT ← hooks.withLocals (vIds.map (·.getId.toString)) (go mode (stx.getArg 3))
        vIds.foldrM (init := bodyT) fun vid acc => `(∀ $vid:ident, $acc)
      | "qedExprLet" =>
        let bStx := stx.getArg 1; let valT ← go .val (stx.getArg 4); let optTy := stx.getArg 2
        let bodyLocals := if bStx.isIdent then #[bStx.getId.eraseMacroScopes.toString] else #[]
        let bodyT ← hooks.withLocals bodyLocals (go mode (stx.getArg 6))
        if bStx.isIdent then
          let bId : Ident := ⟨bStx⟩
          if optTy.getNumArgs == 2 then `(let $bId:ident : $(← hooks.lowerType (optTy.getArg 1)) := $valT; $bodyT)
          else `(let $bId:ident := $valT; $bodyT)
        else `(let _ := $valT; $bodyT)
      | "qedExprIfLet" =>
        let (patT, scrutT, thenT) := (← hooks.lowerPat (stx.getArg 2), ← go .val (stx.getArg 4), ← go mode (stx.getArg 6))
        let elseT ← lowerOptElse stx (stx.getArg 7) (stx.getArg 6) thenT "`if let pat = expr: ...` expression requires `else:` here"
        `(if let $patT := $scrutT then $thenT else $elseT)
      | "qedExprMatch" =>
        let scruts ← (stx.getArg 1).getSepArgs.mapM (go .val)
        let alts ← (stx.getArg 3).getArgs.mapM fun c => do
          let altStxs := extractCasePatAlts (c.getArg 1)
          let altTerms ← altStxs.mapM (·.mapM hooks.lowerPat)
          let rhs ← hooks.withLocals ((collectCasePatIds altStxs).map (·.toString)) (go mode (c.getArg 3))
          mkMatchAltFromAlts altTerms rhs
        `(match $[$scruts:term],* with $[$alts:matchAlt]*)
      | "qedExprFor" =>
        let (patStx, bodyStx) := (stx.getArg 1, stx.getArg 5); let xsT ← go .val (stx.getArg 3)
        let bodyT ← hooks.withLocals ((collectQedPatIds patStx).map (·.toString)) (go .val bodyStx)
        let fnT ← if patStx.getKind == ``qedPatIdent && (patStx.getArg 1).getNumArgs == 0 then `(fun $(⟨patStx.getArg 0⟩):ident => $bodyT)
          else `(fun _qed_fe => match _qed_fe with | $(← hooks.lowerPat patStx) => $bodyT)
        hooks.wrapForMap bodyStx bodyT (← `($(mkIdentFrom stx `Qed.mapList) ($(mkIdentFrom stx `Qed.ForEachItems.toList) $xsT) $fnT))
      | _ => hooks.lowerJsx stx mode
    | _ => hooks.lowerJsx stx mode
  go mode stx

def lowerSimpleQedExpr (mode : ExprMode) (stx : Syntax) (allowOptElse := false) (optElseFallback : MacroM Term := `(()))
    (lowerJsx? : Option (Syntax → ExprMode → MacroM Term) := none) (wrapNamedField : Term → MacroM Term := pure)
    (lowerIndex? : Option (Syntax → Term → Term → ExprMode → MacroM Term) := none) : MacroM Term :=
  let base := LowerHooks.mkDefault Macro.throwErrorAt
  lowerQedExpr { base with
    lowerIndex := lowerIndex?.getD base.lowerIndex, lowerJsx := lowerJsx?.getD base.lowerJsx,
    wrapNamedField, lowerType := fun t => return (← lowerQedType t false).1, lowerPat := lowerQedPat,
    allowOptElse, optElseFallback := fun _ _ => optElseFallback } mode stx

end Qed.Lang

namespace Qed

@[reducible, inline] instance {α : Type} {p : α → Prop} : Qed.Lang.QedVal (Field p) α := ⟨Field.val⟩
@[simp] theorem QedVal.val_field {α : Type} {p : α → Prop} (f : Field p) : Qed.Lang.QedVal.val f = f.val := rfl

open Lean Meta Elab Tactic Command Term PrettyPrinter

def qedLooksGenerated (n : Name) : Bool := match n with
  | .str _ s => !["_qed_render", "_qed_renderTag", "_qed_mount", "_qed_mountWithOpt"].contains s && (n.isInternalDetail ||
      ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion", "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg", "toJson", "fromJson"].contains s ||
      ["match_", "eq_", "inst", "_wsKey_"].any (s.startsWith ·) || ["_key", "_sub", "_unsub", "_send"].any (s.endsWith ·))
  | _ => n.isInternalDetail

def qedIsHelper (env : Environment) (n : Name) : Bool :=
  !Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n n) (includeQed := true) &&
  (match env.find? n with | some (.defnInfo d) => !d.type.isConstOf `Qed.Style | _ => false) && !qedLooksGenerated n

def qedUnfoldHelperLoop (maxIters : Nat) (keep : Environment → Name → MetaM Bool)
    (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (includeLCtx useSimpAll tryRfl : Bool := false) : TacticM Unit := do
  for _ in [0:maxIters] do
    if (← getGoals).isEmpty then break
    let env ← getEnv
    let present ← withMainContext do
      let mut cs := (← instantiateMVars (← getMainTarget)).getUsedConstants
      if includeLCtx then for ldecl in (← getLCtx) do if !ldecl.isImplementationDetail then
        for c in (← instantiateMVars ldecl.type).getUsedConstants do cs := Qed.Lang.pushUnique cs c
      cs.filterM (fun n => liftM (keep env n))
    if present.isEmpty then
      if useSimpAll && !extraLemmas.isEmpty then try evalTactic (← `(tactic| simp_all only [$[$extraLemmas],*])) catch _ => pure ()
      break
    let combined := (← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)) ++ extraLemmas
    let tac ← match useSimpAll, includeLCtx, tryRfl with
      | true, _, _ => `(tactic| simp_all only [$[$combined],*])
      | false, true, true => `(tactic| (simp only [$[$combined],*] at *; try rfl)) | false, true, false => `(tactic| simp only [$[$combined],*] at *)
      | false, false, true => `(tactic| (simp only [$[$combined],*]; try rfl)) | false, false, false => `(tactic| simp only [$[$combined],*])
    unless (← try evalTactic tac; pure true catch _ => pure false) do break

def mkConjBody {m : Type → Type} [Monad m] [MonadQuotation m] (clauses : Array Term) (ascribeProp : Bool := true) : m Term := do
  let props ← if ascribeProp then clauses.mapM fun c => `(($c : Prop)) else pure clauses
  match props.toList with | [] => `(True) | p :: ps => ps.foldlM (init := p) fun acc x => `($acc ∧ $x)

def extractInvPred (id : Ident) : TermElabM (TSyntax `term) := do
  let cTy := (← getConstInfo (← realizeGlobalConstNoOverload id)).type
  forallTelescope (if cTy.isAppOfArity ``And 2 then cTy.appArg! else cTy) fun args _ => do
    let some hIdx ← (List.range args.size).findM? fun i => do if i ≥ 2 then isProp (← inferType args[i]!) else pure false
      | throwErrorAt id "`{id}` doesn't look like a state invariant, so its predicate can't be inferred; write it explicitly (`<pred> for_each … using {id}`)."
    delab (← mkLambdaFVars #[args[hIdx - 2]!] (← inferType args[hIdx]!)).eta

end Qed
