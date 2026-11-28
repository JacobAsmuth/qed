import Lean
import Qed.Diag

namespace Qed.Lang

/-! ## Shared Proof Helpers (`QedAndProp`, `QedOrProp`, `qedAsProp`, `qedEqProp`) -/

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
syntax (name := qedSeqLitStx) "qedSeqLit%[" term,* "]" : term

open Lean Meta Elab Term in
@[term_elab qedAsPropStx] def elabQedAsProp : TermElab := fun stx _ => do
  let e ← instantiateMVars (← elabTerm (stx.getArg 1) none); let ty ← whnf (← inferType e)
  if ty.isProp then return e else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true) else ensureHasType (mkSort Level.zero) e

open Lean Meta Elab Term in
@[noinline, term_elab qedSeqLitStx] def elabQedSeqLit : TermElab := fun stx expectedType? => do
  let elems : Array Term := (stx.getArg 1).getSepArgs.map (⟨·⟩)
  if let some expTy := expectedType? then
    tryPostponeIfMVar expTy
    let expTy ← instantiateMVars expTy
    if !expTy.getAppFn.isMVar then
      let expWhnf ← if expTy.isAppOfArity ``List 1 || expTy.isAppOfArity ``Array 1 then pure expTy else withTransparency .reducible (whnf expTy)
      if expWhnf.isAppOfArity ``List 1 then
        return ← elabTerm (← `([$[$elems:term],*])) (some expTy)
      if expWhnf.isAppOfArity ``Array 1 then
        return ← elabTerm (← `(#[$[$elems:term],*])) (some expTy)
  elabTerm (← `($(mkCIdent `Qed.Lang.QedSeqLit.ofList) [$[$elems:term],*])) expectedType?

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

/-! ## Shared Opaque Parser Wrapper & Unified Python-esque Grammar -/

section OpaqueParser
open Lean Parser PrettyPrinter Parenthesizer Formatter
def opaqueP (p : Parser) : Parser := p
@[combinator_parenthesizer opaqueP] def opaqueP.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter opaqueP] def opaqueP.formatter : Formatter := pure ()
end OpaqueParser

declare_syntax_cat qedType
declare_syntax_cat qedCallArg
declare_syntax_cat qedPat
declare_syntax_cat qedExpr
declare_syntax_cat qedStmt

section Parsers
open Lean Parser PrettyPrinter Parenthesizer Formatter

private abbrev pExpr (p : Nat := 0) : Parser := categoryParser `qedExpr p
private abbrev pType (p : Nat := 0) : Parser := if p == 0 then withPosition (categoryParser `qedType 0) else categoryParser `qedType p
private abbrev pPat  (p : Nat := 0) : Parser := categoryParser `qedPat p
private def leadP  (k : Name) (p : Parser) (prec : Nat := maxPrec) : Parser := leadingNode k prec p
private def trailP (k : Name) (prec : Nat) (p : Parser) : TrailingParser := trailingNode k prec 0 p
private def binOpP (k : Name) (prec rPrec : Nat) (sym : String) : TrailingParser := trailP k prec (symbol sym >> pExpr rPrec)
private def stmtP  (k : Name) (p : Parser) : Parser := leadP k (withPosition p)

/-- Non-reserved keyword parser so English keywords never pollute Lean's global token table. -/
def kw (s : String) : Parser := nonReservedSymbol s (includeIdent := true)
@[combinator_parenthesizer kw] def kw.parenthesizer (_ : String) : Parenthesizer := pure ()
@[combinator_formatter kw] def kw.formatter (_ : String) : Formatter := pure ()
def commaSep (p : Parser) : Parser := sepBy p "," (symbol ",") true
@[combinator_parenthesizer commaSep] def commaSep.parenthesizer (_ : Parenthesizer) : Parenthesizer := pure ()
@[combinator_formatter commaSep] def commaSep.formatter (_ : Formatter) : Formatter := pure ()
def commaSep1 (p : Parser) : Parser := sepBy1 p "," (symbol ",") true
@[combinator_parenthesizer commaSep1] def commaSep1.parenthesizer (_ : Parenthesizer) : Parenthesizer := pure ()
@[combinator_formatter commaSep1] def commaSep1.formatter (_ : Formatter) : Formatter := pure ()
def qedAssignOp : Parser :=
  (symbol "=" >> notFollowedBy (symbol "=") "=") <|>
  symbol "+=" <|> symbol "-=" <|> symbol "*=" <|> symbol "/=" <|> symbol "%=" <|>
  symbol "&=" <|> symbol "|=" <|> symbol "^=" <|> symbol "<<=" <|> symbol ">>="
@[combinator_parenthesizer qedAssignOp] def qedAssignOp.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedAssignOp] def qedAssignOp.formatter : Formatter := pure ()
def qedBinder : Parser := ident <|> symbol "_"
@[combinator_parenthesizer qedBinder] def qedBinder.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedBinder] def qedBinder.formatter : Formatter := pure ()
private def qedLetPatFuel : Nat → Parser
  | 0 => node `Qed.Lang.qedLetPatIdent ident <|> node `Qed.Lang.qedLetPatWild (symbol "_")
  | n + 1 => node `Qed.Lang.qedLetPatIdent ident <|> node `Qed.Lang.qedLetPatWild (symbol "_") <|>
      node `Qed.Lang.qedLetPatTuple ("(" >> commaSep1 { fn := fun c s => (qedLetPatFuel n).fn c s } >> ")")
def qedLetPatTuple : Parser := node `Qed.Lang.qedLetPatTuple ("(" >> commaSep1 (qedLetPatFuel 16) >> ")")
def qedLetBinder : Parser := ident <|> symbol "_" <|> qedLetPatTuple
@[combinator_parenthesizer qedLetBinder] def qedLetBinder.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedLetBinder] def qedLetBinder.formatter : Formatter := pure ()
@[run_parser_attribute_hooks]
def qedEnvRef : Parser := opaqueP (group ((identEq `secret <|> identEq `env) >> "(" >> strLit >> ")" >> optional (" ?? " >> strLit)))

private def pTypeMods : Parser := many (node `Qed.Lang.qedTypeModArr (atomic ("[" >> "]")) <|> node `Qed.Lang.qedTypeModOpt (symbol "?") <|> node `Qed.Lang.qedTypeModErr (symbol "!"))
def qedTypeAtom : Parser := leadP `Qed.Lang.qedTypeAtom (ident >> pTypeMods)
@[qedType_parser] def qedTypeLeadP : Parser := opaqueP (
  leadP `Qed.Lang.qedTypeProto (atomic (kw "Proto" >> "(") >> ident >> ")" >> pTypeMods) <|>
  leadP `Qed.Lang.qedTypeForm  (atomic (identEq `Form >> "(") >> pType >> ")" >> pTypeMods) <|>
  leadP `Qed.Lang.qedTypeDict  (atomic ("{" >> pType >> ":") >> pType >> "}" >> pTypeMods) <|>
  leadP `Qed.Lang.qedTypeParen ("(" >> commaSep1 pType >> ")" >> pTypeMods) <|>
  qedTypeAtom <|> leadP `Qed.Lang.qedTypeNum numLit)
@[qedType_parser 90] def qedTypeApp   : TrailingParser := opaqueP (trailP `Qed.Lang.qedTypeApp   90 (checkLineEq >> notFollowedBy (atomic (identEq `ok >> "[")) "ok" >> pType 91))
@[qedType_parser 25] def qedTypeArrow : TrailingParser := opaqueP (trailP `Qed.Lang.qedTypeArrow 25 (symbol "->" >> pType 25))

private abbrev pPatArgsOpt : Parser := optional (checkNoWsBefore "" >> "(" >> commaSep pPat >> ")")
def qedPatWild  : Parser := leadP `Qed.Lang.qedPatWild  (symbol "_")
def qedPatParen : Parser := leadP `Qed.Lang.qedPatParen ("(" >> commaSep pPat >> ")")
def qedPatList  : Parser := leadP `Qed.Lang.qedPatList  ("[" >> commaSep pPat >> "]")
def qedPatDot   : Parser := leadP `Qed.Lang.qedPatDot   (atomic ("." >> checkNoWsBefore "") >> ident >> pPatArgsOpt)
def qedPatIdent : Parser := leadP `Qed.Lang.qedPatIdent (ident >> pPatArgsOpt)
@[qedPat_parser] def qedPatLeadP : Parser := opaqueP (
  qedPatWild <|> leadP `Qed.Lang.qedPatNum numLit <|> leadP `Qed.Lang.qedPatStr strLit <|> leadP `Qed.Lang.qedPatChar charLit <|>
  qedPatParen <|> qedPatList <|> qedPatDot <|> qedPatIdent)
@[qedPat_parser 67] def qedPatCons : TrailingParser := opaqueP (trailP `Qed.Lang.qedPatCons 67 (symbol "::" >> pPat 67))

def qedCallArgNamed : Parser := node `Qed.Lang.qedCallArgNamed (atomic (rawIdent >> "=" >> notFollowedBy (symbol "=") "=") >> pExpr)
def qedCallArgPos   : Parser := node `Qed.Lang.qedCallArgPos pExpr
@[qedCallArg_parser] def qedCallArgP : Parser := opaqueP (
  node `Qed.Lang.qedCallArgWhere (atomic (symbol "where" >> "=" >> notFollowedBy (symbol "=") "=") >> pExpr) <|> qedCallArgNamed <|> qedCallArgPos)

def qedCasePats : Parser := sepBy1 (node `Qed.Lang.qedPatAlt (sepBy1 pPat ",")) "|"
@[combinator_parenthesizer qedCasePats] def qedCasePats.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedCasePats] def qedCasePats.formatter : Formatter := pure ()

private def notReservedExprKw : Parser := notFollowedBy (
  kw "and" <|> kw "or" <|> kw "not" <|> kw "is" <|> kw "pass" <|> kw "break" <|> kw "continue" <|> kw "elif" <|> kw "case" <|> kw "catch" <|> kw "atomic" <|>
  symbol "in" <|> symbol "if" <|> symbol "else" <|> symbol "match" <|> symbol "for" <|> symbol "return" <|> symbol "let") "expression"

def qedRawTerm     : Parser := leadP `Qed.Lang.qedRawTerm     ("qedRaw%(" >> termParser >> ")")
def qedSqlIdentLit : Parser := leadP `Qed.Lang.qedSqlIdentLit (atomic (symbol "sql!" >> checkNoWsBefore "") >> strLit)
def qedLitNum      : Parser := leadP `Qed.Lang.qedLitNum      numLit
def qedLitStr      : Parser := leadP `Qed.Lang.qedLitStr      strLit
@[qedExpr_parser] def qedFStr        : Parser := leading_parser:maxPrec atomic (kw "f" >> checkNoWsBefore "") >> interpolatedStr (categoryParser `qedExpr 0)
def qedArrLit      : Parser := leadP `Qed.Lang.qedArrLit      ("[" >> commaSep pExpr >> "]")
def qedRecLit      : Parser := leadP `Qed.Lang.qedRecLit      ("{" >> optional (atomic (pExpr >> symbol "with")) >> commaSep (node `Qed.Lang.recField (atomic (ident >> qedAssignOp) >> pExpr)) >> "}")
def qedFieldSetter : Parser := leadP `Qed.Lang.qedFieldSetter (atomic ("(" >> ident >> "=" >> symbol "_" >> ")"))
def qedParen       : Parser := leadP `Qed.Lang.qedParen       ("(" >> commaSep pExpr >> ")")
def qedPlaceholder : Parser := leadP `Qed.Lang.qedPlaceholder (symbol "_")
def qedDotIdent    : Parser := leadP `Qed.Lang.qedDotIdent    (atomic ("." >> checkNoWsBefore "") >> ident)
def qedIdent       : Parser := leadP `Qed.Lang.qedIdent       (notReservedExprKw >> ident)
@[qedExpr_parser] def qedExprAtomP : Parser := opaqueP (
  qedRawTerm <|> qedSqlIdentLit <|> leadP `Qed.Lang.qedLitSci scientificLit <|> qedLitNum <|> qedLitStr <|> leadP `Qed.Lang.qedLitChar charLit <|> qedArrLit <|>
  leadP `Qed.Lang.qedDictLit (atomic ("{" >> pExpr >> ":") >> pExpr >> many ("," >> node `Qed.Lang.dictEntry (pExpr >> ":" >> pExpr)) >> optional "," >> "}") <|>
  qedRecLit <|> qedFieldSetter <|> leadP `Qed.Lang.qedTypeAscr (atomic ("(" >> pExpr >> ":" >> pType >> ")")) <|> qedParen <|> qedPlaceholder <|> qedDotIdent <|> qedIdent)

@[qedExpr_parser 90] def qedCall   : TrailingParser := opaqueP (trailP `Qed.Lang.qedCall   90 (checkNoWsBefore "" >> "(" >> commaSep (categoryParser `qedCallArg 0) >> ")"))
@[qedExpr_parser 90] def qedIndex  : TrailingParser := opaqueP (trailP `Qed.Lang.qedIndex  90 (checkNoWsBefore "" >> "[" >> pExpr >> "]" >> optional (atomic (checkNoWsBefore "" >> symbol "?"))))
@[qedExpr_parser 90] def qedProj   : TrailingParser := opaqueP (trailP `Qed.Lang.qedProj   90 (checkNoWsBefore "" >> "." >> checkNoWsBefore "" >> (ident <|> fieldIdx)))
@[qedExpr_parser 90] def qedUnwrap : TrailingParser := opaqueP (trailP `Qed.Lang.qedUnwrap 90 (checkNoWsBefore "" >> symbol "?"))

@[qedExpr_parser 85] def qedPow    : TrailingParser := opaqueP (binOpP `Qed.Lang.qedPow 85 80 "**")
@[qedExpr_parser 80] def qedNeg    : Parser         := opaqueP (leadP `Qed.Lang.qedNeg ("-" >> pExpr 80) 80)
@[qedExpr_parser 80] def qedBitNot : Parser         := opaqueP (leadP `Qed.Lang.qedBitNot ("~" >> pExpr 80) 80)
@[qedExpr_parser 75] def qedAwait  : Parser         := opaqueP (leadP `Qed.Lang.qedAwait (atomic (kw "await") >> pExpr 75) 75)
@[qedExpr_parser 70] def qedMul      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedMul 70 71 "*")
@[qedExpr_parser 70] def qedDiv      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedDiv 70 71 "/")
@[qedExpr_parser 70] def qedMod      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedMod 70 71 "%")
@[qedExpr_parser 65] def qedAdd      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedAdd 65 66 "+")
@[qedExpr_parser 65] def qedSub      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedSub 65 66 "-")
@[qedExpr_parser 65] def qedCat      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedCat 65 66 "++")
@[qedExpr_parser 64] def qedShl      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedShl 64 65 "<<")
@[qedExpr_parser 64] def qedShr      : TrailingParser := opaqueP (binOpP `Qed.Lang.qedShr 64 65 ">>")
@[qedExpr_parser 63] def qedCons     : TrailingParser := opaqueP (binOpP `Qed.Lang.qedCons 63 63 "::")
@[qedExpr_parser 62] def qedBitAnd   : TrailingParser := opaqueP (binOpP `Qed.Lang.qedBitAnd 62 63 "&")
@[qedExpr_parser 61] def qedBitXor   : TrailingParser := opaqueP (binOpP `Qed.Lang.qedBitXor 61 62 "^")
@[qedExpr_parser 60] def qedBitOr    : TrailingParser := opaqueP (binOpP `Qed.Lang.qedBitOr 60 61 "|")
@[qedExpr_parser 57] def qedCoalesce : TrailingParser := opaqueP (binOpP `Qed.Lang.qedCoalesce 57 57 "??")

@[qedExpr_parser 50] def qedCmp : TrailingParser := opaqueP (trailP `Qed.Lang.qedCmp 50 (many1 (node `Qed.Lang.cmpLink (
  node `Qed.Lang.cmpOp (symbol "==" <|> symbol "!=" <|> symbol "<=" <|> symbol ">=" <|> symbol "<" <|> symbol ">" <|>
    symbol "in" <|> atomic (kw "not" >> symbol "in") <|> atomic (kw "is" >> kw "not") <|> kw "is") >> pExpr 55))))

@[qedExpr_parser 40] def qedNot : Parser         := opaqueP (leadP  `Qed.Lang.qedNot (atomic (kw "not") >> pExpr 40) 40)
@[qedExpr_parser 35] def qedAnd : TrailingParser := opaqueP (trailP `Qed.Lang.qedAnd 35 (atomic (kw "and") >> pExpr 35))
@[qedExpr_parser 30] def qedOr  : TrailingParser := opaqueP (trailP `Qed.Lang.qedOr  30 (atomic (kw "or")  >> pExpr 30))
@[qedExpr_parser 25] def qedImp : TrailingParser := opaqueP (binOpP `Qed.Lang.qedImp 25 25 "->")
@[qedExpr_parser 20] def qedTernary : TrailingParser := opaqueP (trailP `Qed.Lang.qedTernary 20 (atomic (checkColGt >> symbol "if") >> pExpr 21 >> optional (atomic (checkColGt >> symbol "else") >> pExpr 20)))

def qedLam1 : Parser := leadP `Qed.Lang.qedLam1 (atomic (qedBinder >> " => ") >> pExpr 10) 18
def qedLamN : Parser := leadP `Qed.Lang.qedLamN (atomic ("(" >> commaSep (node `Qed.Lang.lamParam (qedLetBinder >> optional (":" >> pType))) >> ")" >> " => ") >> pExpr 10) 18
@[qedExpr_parser 18] def qedExprLamP : Parser := opaqueP (qedLam1 <|> qedLamN)

private def qedQuantVarList : Parser :=
  atomic (sepBy1 (node `Qed.Lang.qedAllVarTyped (ident >> ":" >> notFollowedBy (kw "all" <|> kw "any") "quantifier" >> pType)) "," >> lookahead (symbol ":")) <|>
  sepBy1 ident ","
def qedAllIn   : Parser := leadP `Qed.Lang.qedAllIn   (atomic (kw "all" >> qedLetBinder >> symbol "in") >> pExpr 55 >> ":" >> pExpr 15) 15
def qedAnyIn   : Parser := leadP `Qed.Lang.qedAnyIn   (atomic (kw "any" >> qedLetBinder >> symbol "in") >> pExpr 55 >> ":" >> pExpr 15) 15
def qedAllVars : Parser := leadP `Qed.Lang.qedAllVars (atomic (kw "all" >> qedQuantVarList >> ":") >> pExpr 10) 15
def qedAnyVars : Parser := leadP `Qed.Lang.qedAnyVars (atomic (kw "any" >> qedQuantVarList >> ":") >> pExpr 10) 15
@[qedExpr_parser 15] def qedExprQuantP : Parser := opaqueP (qedAllIn <|> qedAnyIn <|> qedAllVars <|> qedAnyVars)

private def qedExprElif : Parser :=
  node `Qed.Lang.exprElifLet (atomic (checkColGe >> kw "elif" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> pExpr) <|>
  node `Qed.Lang.exprElif (atomic (checkColGe >> kw "elif" >> notFollowedBy (symbol "let") "let") >> pExpr >> ":" >> pExpr)
def qedExprLet   : Parser := leadP `Qed.Lang.qedExprLet   (withPosition (symbol "let" >> qedLetBinder >> optional (":" >> pType) >> "=" >> pExpr >> ";" >> pExpr)) 10
def qedExprIfLet : Parser := leadP `Qed.Lang.qedExprIfLet (withPositionAfterLinebreak (atomic (symbol "if" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> pExpr >> many qedExprElif >> optional (atomic (checkColGe >> symbol "else" >> ":") >> pExpr))) 10
def qedExprIf    : Parser := leadP `Qed.Lang.qedExprIf    (withPositionAfterLinebreak (symbol "if" >> notFollowedBy (symbol "let") "let" >> pExpr >> ":" >> pExpr >> many qedExprElif >> optional (atomic (checkColGe >> symbol "else" >> ":") >> pExpr))) 10
def qedExprFor   : Parser := leadP `Qed.Lang.qedExprFor   (withPosition (atomic (symbol "for" >> pPat >> symbol "in") >> pExpr >> ":" >> pExpr)) 10
def qedExprMatch : Parser := leadP `Qed.Lang.qedExprMatch (withPosition (symbol "match" >> sepBy1 pExpr "," >> ":" >> many1 (checkColGt >> node `Qed.Lang.qedExprCase (withPosition (atomic (kw "case") >> qedCasePats >> ":" >> pExpr))))) 10
@[qedExpr_parser 10] def qedExprCtrlP : Parser := opaqueP (qedExprLet <|> qedExprIfLet <|> qedExprIf <|> qedExprFor <|> qedExprMatch)

def qedOptProof : Parser := optional (
  node `Qed.fnProofProve (atomic (checkColGt "expected indented `prove:` block" >> identEq `prove >> ":") >> checkColGt "expected indented proof tactics" >> Parser.Tactic.tacticSeq))
@[combinator_parenthesizer qedOptProof] def qedOptProof.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedOptProof] def qedOptProof.formatter : Formatter := pure ()

def qedSuite : Parser := node `Qed.Lang.suite (
  (checkLineEq >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
  (checkColGt "expected indented block" >> withPosition (many1 (checkColEq "expected aligned statement" >> categoryParser `qedStmt 0))))
@[combinator_parenthesizer qedSuite] def qedSuite.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedSuite] def qedSuite.formatter : Formatter := pure ()

private def qedForInvStart : Parser := kw "invariant" >> notFollowedBy (qedAssignOp <|> symbol "(" <|> symbol ".") "invariant"
def qedForInv : Parser := node `Qed.Lang.qedForInv (withPosition (qedForInvStart >> sepBy1 pExpr "," >> qedOptProof))
def qedForSuite : Parser := node `Qed.Lang.forSuite (
  (checkLineEq >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
  (checkColGt "expected indented block" >> withPosition (
    many (atomic (checkColEq "invariant" >> lookahead qedForInvStart) >> qedForInv) >>
    many1 (checkColEq "expected aligned statement" >> categoryParser `qedStmt 0))))
@[combinator_parenthesizer qedForSuite] def qedForSuite.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedForSuite] def qedForSuite.formatter : Formatter := pure ()
def qedStmtCase : Parser := node `Qed.Lang.qedStmtCase (withPosition (atomic (kw "case") >> qedCasePats >> ":" >> qedSuite))
@[combinator_parenthesizer qedStmtCase] def qedStmtCase.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter qedStmtCase] def qedStmtCase.formatter : Formatter := pure ()
private def qedLetPredict : Parser :=
  node `Qed.Lang.letPredictBlock (checkColGe >> withPosition (atomic (kw "predict" >> ":") >> qedSuite)) <|>
  node `Qed.Lang.letPredictExpr  (checkColGe >> withPosition (atomic (kw "predict" >> notFollowedBy (symbol ":" <|> qedAssignOp) "predict") >> pExpr))
private def qedLetClause : Parser := qedLetPredict <|>
  node `Qed.Lang.letOnConfirm (checkColGe >> withPosition (atomic (kw "on_confirm" >> ":") >> qedSuite)) <|>
  node `Qed.Lang.letRollback  (checkColGe >> withPosition (atomic (kw "rollback" >> optional (checkLineEq >> "(" >> qedBinder >> ")") >> ":") >> qedSuite)) <|>
  node `Qed.Lang.letCatch     (atomic (checkColGe >> kw "catch" >> notFollowedBy qedAssignOp "assignment") >>
    (node `Qed.Lang.catchArms (":" >> many1 (checkColGt >> qedStmtCase)) <|> node `Qed.Lang.catchSingle (qedBinder >> ":" >> qedSuite)))
private def qedStmtElif : Parser :=
  node `Qed.Lang.elifLetClause (atomic (checkColEq >> kw "elif" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> qedSuite) <|>
  node `Qed.Lang.elifClause (atomic (checkColEq >> kw "elif" >> notFollowedBy (symbol "let") "let") >> pExpr >> ":" >> qedSuite)

def qedStmtPass     : Parser := stmtP `Qed.Lang.qedStmtPass     (atomic (kw "pass"))
def qedStmtBreak    : Parser := stmtP `Qed.Lang.qedStmtBreak    (atomic (kw "break"))
def qedStmtContinue : Parser := stmtP `Qed.Lang.qedStmtContinue (atomic (kw "continue"))
def qedStmtReturn   : Parser := stmtP `Qed.Lang.qedStmtReturn   (symbol "return" >> optional (checkLineEq >> pExpr))
def qedStmtAtomic   : Parser := stmtP `Qed.Lang.qedStmtAtomic   (atomic (kw "atomic" >> ":") >> qedSuite)
def qedStmtLetMut   : Parser := stmtP `Qed.Lang.qedStmtLetMut   (atomic (symbol "let" >> kw "mut" >> ident) >> optional (":" >> pType) >> "=" >> pExpr)
def qedStmtLetElse  : Parser := stmtP `Qed.Lang.qedStmtLetElse  (atomic (symbol "let" >> pPat >> "=" >> pExpr >> checkColGe >> symbol "else") >> (node `Qed.Lang.letElseBlock (":" >> qedSuite) <|> node `Qed.Lang.letElseInline (checkLineEq >> categoryParser `qedStmt 0)))
def qedStmtLet      : Parser := stmtP `Qed.Lang.qedStmtLet      (symbol "let" >> qedLetBinder >> optional (":" >> pType) >> "=" >> pExpr >> many qedLetClause)
def qedStmtIfLet    : Parser := stmtP `Qed.Lang.qedStmtIfLet    (atomic (symbol "if" >> symbol "let") >> pPat >> "=" >> pExpr >> ":" >> qedSuite >> many qedStmtElif >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
def qedStmtIf       : Parser := stmtP `Qed.Lang.qedStmtIf       (symbol "if" >> notFollowedBy (symbol "let") "let" >> pExpr >> ":" >> qedSuite >> many qedStmtElif >> optional (atomic (checkColEq >> symbol "else" >> ":") >> qedSuite))
def qedStmtMatch    : Parser := stmtP `Qed.Lang.qedStmtMatch    (symbol "match" >> sepBy1 pExpr "," >> ":" >> many1 (checkColGt >> qedStmtCase))
def qedStmtFor      : Parser := stmtP `Qed.Lang.qedStmtFor      (atomic (symbol "for" >> qedLetBinder >> symbol "in") >> pExpr >> ":" >> qedForSuite)
def qedStmtAssign   : Parser := stmtP `Qed.Lang.qedStmtAssign   (atomic (pExpr 90 >> qedAssignOp) >> pExpr >> optional qedLetPredict)
def qedStmtExpr     : Parser := stmtP `Qed.Lang.qedStmtExpr     (notFollowedBy (symbol "if" <|> symbol "match" <|> symbol "for" <|> symbol "return" <|> symbol "let" <|> kw "atomic" <|> kw "pass" <|> kw "break" <|> kw "continue") "statement" >> pExpr)
@[qedStmt_parser] def qedStmtP : Parser := opaqueP (
  qedStmtPass <|> qedStmtBreak <|> qedStmtContinue <|> qedStmtReturn <|> qedStmtAtomic <|>
  qedStmtLetMut <|> qedStmtLetElse <|> qedStmtLet <|> qedStmtIfLet <|> qedStmtIf <|>
  qedStmtMatch <|> qedStmtFor <|> qedStmtAssign <|> qedStmtExpr)

end Parsers

/-! ## Zero-Branch Quotation Monad (`PureQuotM`), Shared Loop Combinators & Unified AST Helpers -/

open Lean

structure PureQuotCtx where
  ref            : Syntax
  currMacroScope : MacroScope
  mainModule     : Name

abbrev PureQuotM := ReaderT PureQuotCtx Id

instance : MonadRef PureQuotM where
  getRef := return (← read).ref
  withRef ref k := withReader (fun c => { c with ref }) k

instance : MonadQuotation PureQuotM where
  getCurrMacroScope := return (← read).currMacroScope
  getContext := return (← read).mainModule
  withFreshMacroScope k := withReader (fun c => { c with currMacroScope := c.currMacroScope + 1 }) k

@[inline] def PureQuotCtx.runPure {α : Type} (ctx : PureQuotCtx) (k : PureQuotM α) : α := k.run ctx
@[noinline, nospecialize] def runPureQuot {m : Type → Type} [Monad m] [MonadQuotation m] {α : Type} (k : PureQuotM α) : m α := do
  return k.run { ref := ← getRef, currMacroScope := ← getCurrMacroScope, mainModule := ← MonadQuotation.getContext }
@[noinline, nospecialize] def getPureQuotCtx {m : Type → Type} [Monad m] [MonadQuotation m] : m PureQuotCtx := runPureQuot read

@[noinline] protected def runPQ {α : Type} (k : PureQuotM α) : Elab.Command.CommandElabM α := do
  return k.run { ref := ← getRef, currMacroScope := ← getCurrMacroScope, mainModule := ← MonadQuotation.getContext }
@[noinline] def runPQTactic {α : Type} (k : PureQuotM α) : Elab.Tactic.TacticM α := do
  return k.run { ref := ← getRef, currMacroScope := ← getCurrMacroScope, mainModule := ← MonadQuotation.getContext }
@[noinline] def runPQMacro {α : Type} (k : PureQuotM α) : MacroM α := do
  return k.run { ref := ← getRef, currMacroScope := ← getCurrMacroScope, mainModule := ← MonadQuotation.getContext }
@[noinline] def getPureQuotCtxCmd : Elab.Command.CommandElabM PureQuotCtx := Lang.runPQ read
@[noinline] def getPureQuotCtxMacro : MacroM PureQuotCtx := runPQMacro read
@[noinline] protected def foldlPQ {α β : Type} (xs : Array α) (init : β) (f : β → α → PureQuotM β) : PureQuotM β :=
  let rec go : Nat → β → PureQuotM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] protected def foldrPQ {α β : Type} (xs : Array α) (init : β) (f : α → β → PureQuotM β) : PureQuotM β :=
  let rec go : Nat → β → PureQuotM β | 0, acc => pure acc | j + 1, acc => do if h : j < xs.size then go j (← f xs[j] acc) else pure acc
  go xs.size init
@[noinline] protected def mapPQ {α β : Type} (xs : Array α) (f : α → PureQuotM β) : PureQuotM (Array β) :=
  Lang.foldlPQ xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)
@[noinline] protected def mapIdxPQ {α β : Type} (xs : Array α) (f : α → Nat → PureQuotM β) : PureQuotM (Array β) :=
  let rec go : Nat → Array β → PureQuotM (Array β) | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (acc.push (← f xs[i] i)) else pure acc
  go xs.size (Array.mkEmpty xs.size)
@[noinline] protected def foldlCmd {α β : Type} (xs : Array α) (init : β) (f : β → α → Elab.Command.CommandElabM β) : Elab.Command.CommandElabM β :=
  let rec go : Nat → β → Elab.Command.CommandElabM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] protected def mapCmd {α β : Type} (xs : Array α) (f : α → Elab.Command.CommandElabM β) : Elab.Command.CommandElabM (Array β) :=
  Lang.foldlCmd xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)
@[noinline] protected def elabPureCmd (k : PureQuotM (TSyntax `command)) : Elab.Command.CommandElabM Unit := do Elab.Command.elabCommand (← Lang.runPQ k)
@[noinline] protected def elabPureCmds (k : PureQuotM (Array (TSyntax `command))) : Elab.Command.CommandElabM Unit := do Lang.foldlCmd (← Lang.runPQ k) () fun _ c => Elab.Command.elabCommand c
@[noinline] protected def noUnusedVarsPure (cmd : TSyntax `command) : PureQuotM (TSyntax `command) := `(command| set_option linter.unusedVariables false in $cmd)
@[noinline] protected def mkMarkerThmPure (id : Ident) : PureQuotM (TSyntax `command) := `(command| theorem $id : True := True.intro)
@[noinline] protected def mkStrArrDefPure (id : Ident) (xs : Array String) : PureQuotM (TSyntax `command) := do
  let lits : Array Term := xs.map (Syntax.mkStrLit ·); `(command| @[noinline] def $id : Array String := #[$[$lits],*])

@[noinline] private def foldlIdxExcept {ε α β : Type} (xs : Array α) (init : β) (f : β → α → Nat → Except ε β) : Except ε β :=
  let rec go : Nat → β → Except ε β
    | 0, acc => .ok acc
    | r + 1, acc => let i := xs.size - (r + 1); if h : i < xs.size then match f acc xs[i] i with | .ok b => go r b | .error e => .error e else .ok acc
  go xs.size init
@[noinline] private def mapExcept {ε α β : Type} (xs : Array α) (f : α → Except ε β) : Except ε (Array β) :=
  foldlIdxExcept xs (Array.mkEmpty xs.size) fun acc x _ => match f x with | .ok b => .ok (acc.push b) | .error e => .error e
@[noinline, nospecialize] def mapArrM {m : Type → Type} [Monad m] {α β : Type} (xs : Array α) (f : α → m β) : m (Array β) :=
  let rec go : Nat → Array β → m (Array β)
    | 0, acc => pure acc
    | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (acc.push (← f xs[i])) else pure acc
  go xs.size (Array.mkEmpty xs.size)
@[noinline, nospecialize] def liftPureErr {m : Type → Type} [Monad m] [MonadError m] {α : Type} : Except (Syntax × String) α → m α
  | .ok v => pure v | .error (ref, msg) => throwErrorAt ref msg
@[noinline] private def runPureErrMacro {α : Type} (k : PureQuotCtx → Except (Syntax × String) α) : MacroM α := do
  match k (← getPureQuotCtxMacro) with | .ok v => pure v | .error (ref, msg) => Macro.throwErrorAt ref msg

private def qValId     : Ident := mkCIdent `Qed.Lang.QedVal.val
private def qMemId       : Ident := mkCIdent `Qed.Lang.QedMem.mem
private def qMemPropId   : Ident := mkCIdent `Qed.Lang.QedMemProp.memProp
private def qInListId    : Ident := mkCIdent `Qed.Lang.qedInList
private def qInListPrId  : Ident := mkCIdent `Qed.Lang.qedInListProp
private def qRange1Id  : Ident := mkCIdent `Qed.QedRange.mk1
private def qRange2Id  : Ident := mkCIdent `Qed.QedRange.mk2
private def qRange3Id  : Ident := mkCIdent `Qed.QedRange.mk3
private def qCoalId    : Ident := mkCIdent `Qed.QedCoalesce.toOption

def pushUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α := if xs.contains x then xs else xs.push x
partial def stxAny (p : Syntax → Bool) (stx : Syntax) : Bool := p stx || stx.getArgs.any (stxAny p)

def splitCallArgsPure (callName : String) (rawArgs : Array Syntax) (validKeys : Option (List String) := none)
    (allowWhere : Bool := false) (errRef : Syntax := Syntax.missing) : Except (Syntax × String) (Array Syntax × Array (String × Syntax)) :=
  foldlIdxExcept rawArgs (#[], #[]) fun (posArgs, namedArgs) a _ =>
    let k := a.getKind
    if k == ``qedCallArgPos then .ok (posArgs.push (a.getArg 0), namedArgs)
    else if allowWhere && k == `Qed.Lang.qedCallArgWhere then .ok (posArgs, namedArgs.push ("where", a.getArg 2))
    else if k == ``qedCallArgNamed then
      let key := (a.getArg 0).getId.eraseMacroScopes.toString
      match validKeys with
      | some allowed =>
          if allowed.contains key then .ok (posArgs, namedArgs.push (key, a.getArg 2))
          else .error (if errRef.isMissing then a else errRef, s!"unknown argument `{key}` in `{callName}(...)`{Qed.Diag.didYouMean key allowed} (supported: {String.intercalate ", " allowed})")
      | none => .ok (posArgs, namedArgs.push (key, a.getArg 2))
    else .error (a, s!"unexpected argument in `{callName}(...)`")

@[noinline, nospecialize] def splitCallArgs {m : Type → Type} [Monad m] [MonadError m] (callName : String) (rawArgs : Array Syntax)
    (validKeys : Option (List String) := none) (allowWhere : Bool := false) (errRef : Syntax := Syntax.missing) : m (Array Syntax × Array (String × Syntax)) :=
  liftPureErr (splitCallArgsPure callName rawArgs validKeys allowWhere errRef)

structure ParsedEnvRef where mk :: (isSecret : Bool) (envKey : String) (default? : Option String) deriving Inhabited, Repr

@[noinline, nospecialize] def parseQedEnvRef {m : Type → Type} [Monad m] [MonadError m] (ctxDesc : String) (stx : Syntax) : m ParsedEnvRef := do
  let envKey := (⟨stx.getArg 2⟩ : TSyntax `str).getString
  if envKey.isEmpty then throwErrorAt stx s!"environment variable name in {ctxDesc} must not be empty"
  let defOpt := stx.getArg 4
  return .mk ((stx.getArg 0).getId.eraseMacroScopes == `secret) envKey (if defOpt.getNumArgs == 2 then some (⟨defOpt.getArg 1⟩ : TSyntax `str).getString else none)

partial def suiteStmts (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Qed.Lang.forSuite then
    if stx.getNumArgs == 2 then (stx.getArg 1).getArgs else (stx.getArg 0).getSepArgs
  else let body := if stx.getKind == `Qed.Lang.suite then stx.getArg 0 else stx; if body.getKind == nullKind then body.getArgs.filter (!·.isAtom) else #[body]
def forSuiteInvs (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Qed.Lang.forSuite && stx.getNumArgs == 2 then (stx.getArg 0).getArgs else #[]
def parseOptTacSeq (optNode : Syntax) : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  if optNode.getNumArgs == 1 then
    let i := optNode.getArg 0; if i.getKind == `Qed.fnProofProve then some ⟨i.getArg 2⟩ else none
  else none
partial def unwrapParens1 (stx : Syntax) : Syntax :=
  if stx.getKind == ``qedParen && (stx.getArg 1).getSepArgs.size == 1 then unwrapParens1 (stx.getArg 1).getSepArgs[0]! else stx
partial def extractDottedChain? (stx : Syntax) : Option (List String) :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent then some ((u.getArg 0).getId.eraseMacroScopes.components.map (·.toString))
  else if u.getKind == ``qedProj && (u.getArg 2).isIdent then (extractDottedChain? (u.getArg 0)).map (· ++ [(u.getArg 2).getId.eraseMacroScopes.toString]) else none
partial def splitAndStx (stx : Syntax) : Array Syntax :=
  let u := unwrapParens1 stx; if u.getKind == ``qedAnd then splitAndStx (u.getArg 0) ++ splitAndStx (u.getArg 2) else #[u]

partial def collectQedPatIds (stx : Syntax) : Array Name :=
  let k := stx.getKind
  if k == ``qedPatIdent then
    if (stx.getArg 1).getNumArgs == 3 then ((stx.getArg 1).getArg 1).getSepArgs.flatMap collectQedPatIds
    else let vn := (stx.getArg 0).getId.eraseMacroScopes; let s := vn.toString
         if vn.isAtomic && !["_", "none", "true", "false"].contains s && !s.front.isUpper then #[vn] else #[]
  else if k == ``qedPatDot && (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs.flatMap collectQedPatIds
  else if k == ``qedPatParen || k == ``qedPatList then (stx.getArg 1).getSepArgs.flatMap collectQedPatIds
  else if k == ``qedPatCons then collectQedPatIds (stx.getArg 0) ++ collectQedPatIds (stx.getArg 2) else #[]

partial def collectLetBinderIds (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId.eraseMacroScopes]
  else let k := stx.getKind
       if k == `Qed.Lang.qedLetPatIdent then #[(stx.getArg 0).getId.eraseMacroScopes]
       else if k == ``qedLetPatTuple then (stx.getArg 1).getSepArgs.flatMap collectLetBinderIds else #[]

def extractCasePatAlts (patsNode : Syntax) : Array (Array Syntax) :=
  let items := patsNode.getSepArgs
  if items.any (·.getKind == `Qed.Lang.qedPatAlt) then items.map fun alt => if alt.getKind == `Qed.Lang.qedPatAlt then (alt.getArg 0).getSepArgs else #[alt] else #[items]

def collectCasePatIds (altStxs : Array (Array Syntax)) : Array Name := altStxs.foldl (init := #[]) fun acc ps => acc ++ ps.flatMap collectQedPatIds

@[noinline] def mkMatchAltFromAlts (altPatTerms : Array (Array Term)) (rhs : Term) : PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  if h : altPatTerms.size = 1 then
    let ps := altPatTerms[0]; `(Lean.Parser.Term.matchAltExpr| | $[$ps:term],* => $rhs)
  else
    let groups ← Lang.mapPQ altPatTerms fun ps => do return ((← `(Lean.Parser.Term.matchAltExpr| | $[$ps:term],* => $rhs)).raw.getArg 1).getArg 0
    let sepArgs := groups.foldl (init := #[]) fun acc g => (if acc.isEmpty then acc else acc.push (Syntax.atom .none "|")).push g
    return ⟨(← `(Lean.Parser.Term.matchAltExpr| | _ => $rhs)).raw.setArg 1 (Syntax.node .none nullKind sepArgs)⟩

def qedAllVarIdent (s : Syntax) : Ident := if s.getKind == `Qed.Lang.qedAllVarTyped then ⟨s.getArg 0⟩ else ⟨s⟩

partial def stxMentionsVar (v : String) (stx : Syntax) : Bool :=
  let k := stx.getKind; let isB (b : Syntax) := b.isIdent && b.getId.eraseMacroScopes.toString == v
  if k == ``qedIdent then match (stx.getArg 0).getId.eraseMacroScopes.components with | root :: _ => root.toString == v | [] => false
  else if k == ``qedLam1 then !isB (stx.getArg 0) && stxMentionsVar v (stx.getArg 2)
  else if k == ``qedLamN then !(stx.getArg 1).getSepArgs.any (fun p => (collectLetBinderIds (p.getArg 0)).any (·.toString == v)) && stxMentionsVar v (stx.getArg 4)
  else if k == ``qedAllIn || k == ``qedAnyIn then stxMentionsVar v (stx.getArg 3) || (!(collectLetBinderIds (stx.getArg 1)).any (·.toString == v) && stxMentionsVar v (stx.getArg 5))
  else if k == ``qedAllVars || k == ``qedAnyVars then !(stx.getArg 1).getSepArgs.any (fun b => isB (qedAllVarIdent b).raw) && stxMentionsVar v (stx.getArg 3)
  else if k == ``qedExprLet then stxMentionsVar v (stx.getArg 4) || (!(collectLetBinderIds (stx.getArg 1)).any (·.toString == v) && stxMentionsVar v (stx.getArg 6))
  else if k == ``qedExprFor then stxMentionsVar v (stx.getArg 3) || (!(collectQedPatIds (stx.getArg 1)).any (·.toString == v) && stxMentionsVar v (stx.getArg 5))
  else stx.getArgs.any (stxMentionsVar v)

def extractElseSuite (optElse : Syntax) : Option (Array Syntax) := if optElse.getNumArgs == 3 then some (suiteStmts (optElse.getArg 2)) else none
def extractLetElseStmts (stmt : Syntax) : Array Syntax :=
  let tail := stmt.getArg 5; if tail.getKind == `Qed.Lang.letElseBlock then suiteStmts (tail.getArg 1) else #[tail.getArg 0]
def extractOptElseExpr? (optElse : Syntax) : Option Syntax :=
  if optElse.getNumArgs == 2 then some (optElse.getArg 1) else if optElse.getNumArgs == 3 then some (optElse.getArg 2) else none
def desugarElifs (elifs : Array Syntax) (optElse : Syntax) : Option (Array Syntax) :=
  if elifs.isEmpty then extractElseSuite optElse else
  let f := elifs[0]!; let i := f.getHeadInfo; let rest := Syntax.node i nullKind (elifs.extract 1 elifs.size)
  if f.getKind == `Qed.Lang.elifLetClause then
    some #[Syntax.node i ``qedStmtIfLet #[Syntax.atom i "if", f.getArg 1, f.getArg 2, f.getArg 3, f.getArg 4, f.getArg 5, f.getArg 6, rest, optElse]]
  else
    some #[Syntax.node i ``qedStmtIf #[Syntax.atom i "if", f.getArg 1, f.getArg 2, f.getArg 3, rest, optElse]]
def desugarExprElifs? (elifs : Array Syntax) (optElse : Syntax) : Option Syntax :=
  if elifs.isEmpty then extractOptElseExpr? optElse else
  let f := elifs[0]!; let i := f.getHeadInfo; let rest := Syntax.node i nullKind (elifs.extract 1 elifs.size)
  if f.getKind == `Qed.Lang.exprElifLet then
    some (Syntax.node i ``qedExprIfLet #[Syntax.atom i "if", f.getArg 1, f.getArg 2, f.getArg 3, f.getArg 4, f.getArg 5, f.getArg 6, rest, optElse])
  else
    some (Syntax.node i ``qedExprIf #[Syntax.atom i "if", f.getArg 1, f.getArg 2, f.getArg 3, rest, optElse])

def matchMethodCall? (stx : Syntax) : Option (Syntax × String × Array Syntax) := do
  let u := unwrapParens1 stx; guard (u.getKind == ``qedCall); let (callee, rawArgs) := (u.getArg 0, (u.getArg 2).getSepArgs)
  if callee.getKind == ``qedProj && (callee.getArg 2).isIdent then return (callee.getArg 0, (callee.getArg 2).getId.toString, rawArgs)
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

private def splitIdentMods (id : Ident) : Except (Syntax × String) (Ident × Array TypeMod) :=
  let chars := id.getId.toString.toList; let revMods := chars.reverse.takeWhile fun c => c == '?' || c == '!'
  let baseChars := chars.take (chars.length - revMods.length)
  if baseChars.isEmpty then .error (id, s!"invalid type `{id.getId}`")
  else .ok (mkIdentFrom id ((String.ofList baseChars |>.splitOn ".").foldl Name.str .anonymous),
            revMods.reverse.toArray.filterMap fun c => if c == '?' then some .option else if c == '!' then some .fallible else none)

private def parseTypeModNode (m : Syntax) : Except (Syntax × String) TypeMod :=
  let k := m.getKind
  if k == `Qed.Lang.qedTypeModArr then .ok .array else if k == `Qed.Lang.qedTypeModOpt then .ok .option else if k == `Qed.Lang.qedTypeModErr then .ok .fallible
  else match (m.reprint.getD "").trimAscii.toString with | "[]" => .ok .array | "?" => .ok .option | "!" => .ok .fallible | s => .error (m, s!"unknown type modifier `{s}`")

private def resolveBaseTypeTerm (baseId : Ident) : Term := match baseId.getId with
  | `Bytes => mkIdentFrom baseId `Qed.Bytes | `Json => mkIdentFrom baseId `Qed.Json | `Secret => mkIdentFrom baseId `Qed.Secret
  | `WebhookUrl => mkIdentFrom baseId `Qed.Server.WebhookUrl | `ProcOutput => mkIdentFrom baseId `Qed.Server.ProcOutput | `OutboundResp => mkIdentFrom baseId `Qed.Server.OutboundResp
  | `SqlIdent => mkIdentFrom baseId `Qed.Server.Db.SqlIdent | `SqlVal => mkIdentFrom baseId `Qed.Server.Db.SqlVal | `DbRow => mkIdentFrom baseId `Qed.Server.Db.DbRow
  | `PgHandle => mkIdentFrom baseId `Qed.Server.Db.PgHandle | `PgTableInfo => mkIdentFrom baseId `Qed.Server.Db.PgTableInfo
  | `PgColumnInfo => mkIdentFrom baseId `Qed.Server.Db.PgColumnInfo | `PgIndexInfo => mkIdentFrom baseId `Qed.Server.Db.PgIndexInfo
  | `PgConstraintInfo => mkIdentFrom baseId `Qed.Server.Db.PgConstraintInfo | `PgTableStat => mkIdentFrom baseId `Qed.Server.Db.PgTableStat
  | _ => ⟨baseId.raw⟩

@[noinline] private def foldRight1PQ (empty : PureQuotM Term) (combine : Term → Term → PureQuotM Term) (xs : Array Term) : PureQuotM Term :=
  if xs.isEmpty then empty else if xs.size == 1 then pure xs[0]! else Lang.foldrPQ (xs.extract 0 (xs.size - 1)) xs.back! combine

@[noinline] def buildProdTypePure (xs : Array Term) : PureQuotM Term := foldRight1PQ `(Unit) (fun a b => `($a × $b)) xs
@[noinline] def buildTupleValPure (xs : Array Term) : PureQuotM Term := foldRight1PQ `(()) (fun a b => `(($a, $b))) xs
@[noinline, nospecialize] def buildProdType {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array Term) : m Term := runPureQuot (buildProdTypePure xs)
@[noinline, nospecialize] def buildTupleVal {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array Term) : m Term := runPureQuot (buildTupleValPure xs)

@[noinline] partial def lowerLetBinderPatPure (stx : Syntax) : PureQuotM Term := do
  if stx.isIdent then return ⟨stx⟩
  let k := stx.getKind
  if k == `Qed.Lang.qedLetPatIdent then return ⟨stx.getArg 0⟩
  else if k == ``qedLetPatTuple then buildTupleValPure (← Lang.mapPQ (stx.getArg 1).getSepArgs lowerLetBinderPatPure)
  else `(_)

@[noinline, nospecialize] def lowerLetBinderPat {m : Type → Type} [Monad m] [MonadQuotation m] (stx : Syntax) : m Term := runPureQuot (lowerLetBinderPatPure stx)

@[noinline] def mkLetBindTerm (bStx : Syntax) (ty? : Option Term) (val body : Term) : PureQuotM Term := do
  if bStx.isIdent then
    let id : Ident := ⟨bStx⟩
    match ty? with | some ty => `(let $id:ident : $ty := $val; $body) | none => `(let $id:ident := $val; $body)
  else if bStx.getKind == ``qedLetPatTuple then
    let pat ← lowerLetBinderPatPure bStx
    match ty? with | some ty => `(let $pat:term := ($val : $ty); $body) | none => `(let $pat:term := $val; $body)
  else match ty? with | some ty => `(let _ : $ty := $val; $body) | none => `(let _ := $val; $body)

@[noinline] def mkAppTermsPure (fn : Term) (args : Array Term) : PureQuotM Term := if args.isEmpty then pure fn else `($fn $args*)
@[noinline, nospecialize] def mkAppTerms {m : Type → Type} [Monad m] [MonadQuotation m] (fn : Term) (args : Array Term) : m Term := runPureQuot (mkAppTermsPure fn args)

@[noinline] def extractTupleProjectionsPure (tupleVar : Ident) (n : Nat) : PureQuotM (Array Term) :=
  let rec go : Nat → Term → Array Term → PureQuotM (Array Term)
    | 0, _, out => pure out
    | 1, cur, out => pure (out.push cur)
    | r + 2, cur, out => do go (r + 1) (← `(($cur).2)) (out.push (← `(($cur).1)))
  go n ⟨tupleVar.raw⟩ (Array.mkEmpty n)

@[noinline, nospecialize] def extractTupleProjections {m : Type → Type} [Monad m] [MonadQuotation m] (tupleVar : Ident) (n : Nat) : m (Array Term) :=
  runPureQuot (extractTupleProjectionsPure tupleVar n)

structure LoweredQedType where mk ::
  (term : Term) (isFallible isProto isForm isOption : Bool := false) (innerOpt? : Option Term := none) (baseName : Name := .anonymous) (mods : Array TypeMod := #[])
deriving Inhabited

@[noinline] private def applyTypeModsInfoPure (qctx : PureQuotCtx) (base : Term) (mods : Array TypeMod) (allowFallible : Bool)
    (ref : Syntax) (ctxDesc? : Option String := none) (nestedErr? : Option String := none) : Except (Syntax × String) (Term × Bool × Option Term) :=
  foldlIdxExcept mods (base, false, none) fun (acc, isFallible, innerOpt?) md i =>
    match md with
    | .array  => .ok (qctx.runPure `(Array $acc), isFallible, none)
    | .option => .ok (qctx.runPure `(Option $acc), isFallible, some acc)
    | .fallible =>
        if !allowFallible then .error (ref, nestedErr?.getD <| match ctxDesc? with
          | some d => s!"fallible `!` modifier is not allowed on {d}; only server `def` return types may use `T!`"
          | none   => "fallible `!` modifier is only allowed on server `def` return types")
        else if i + 1 < mods.size then .error (ref, "place `!` last on fallible return types (for example `Book[]!` instead of `Book![]`)")
        else .ok (acc, true, innerOpt?)

@[noinline] partial def lowerQedTypeInfoPure (qctx : PureQuotCtx) (stx : Syntax) (allowFallible := false) (allowHigherOrder := true) (ctxDesc? : Option String := none) : Except (Syntax × String) LoweredQedType :=
  let rec go (s : Syntax) (allowFall : Bool) (nestedErr? : Option String) : Except (Syntax × String) LoweredQedType := do
    let mkInvalidErr (node : Syntax) : Except (Syntax × String) LoweredQedType :=
      let sn := stxSnippet node; let what := if sn.isEmpty then "" else s!" `{sn}`"
      .error (node, if allowHigherOrder then s!"invalid Qed type{what}; expected a type such as `T`, `T[]`, `T?`, `T!`, `Resource T`, or `A -> B`"
        else s!"invalid server type{what}; expected `T`, `T[]`, `T?`, `T!`, `(T, U)`, `Proto(T)`, or `Form(T)`")
    let finishMods (base : Term) (mods : Array TypeMod) (baseName : Name) (isProto := false) (isForm := false) : Except (Syntax × String) LoweredQedType := do
      let (term, isFallible, innerOpt?) ← applyTypeModsInfoPure qctx base mods allowFall s ctxDesc? nestedErr?
      return .mk term isFallible isProto isForm innerOpt?.isSome innerOpt? baseName mods
    let parseMods (n : Syntax) := mapExcept n.getArgs parseTypeModNode
    let k := s.getKind
    if k == `Qed.Lang.qedTypeProto then
      let (baseId, initMods) ← splitIdentMods ⟨s.getArg 2⟩
      finishMods ⟨baseId.raw⟩ (initMods ++ (← parseMods (s.getArg 4))) baseId.getId.eraseMacroScopes (isProto := true)
    else if k == `Qed.Lang.qedTypeForm then
      let inner ← go (s.getArg 2) false (some "fallible `!` modifier cannot appear inside `Form(...)`")
      let extraMods ← parseMods (s.getArg 4)
      let (term, isFallible, innerOpt?) ← applyTypeModsInfoPure qctx inner.term extraMods allowFall s ctxDesc? nestedErr?
      let opt? := innerOpt? <|> (if extraMods.isEmpty then inner.innerOpt? else none)
      return .mk term isFallible inner.isProto true opt?.isSome opt? inner.baseName (inner.mods ++ extraMods)
    else if k == `Qed.Lang.qedTypeDict then
      let kI ← go (s.getArg 1) false (some "fallible `!` modifier cannot appear inside a dictionary key type")
      let vI ← go (s.getArg 3) false (some "fallible `!` modifier cannot appear inside a dictionary value type")
      finishMods (qctx.runPure `($(mkIdentFrom s `Qed.Dict) $(kI.term) $(vI.term))) (← parseMods (s.getArg 5)) `Qed.Dict
    else if k == `Qed.Lang.qedTypeParen then
      let ls ← mapExcept (s.getArg 1).getSepArgs fun p => return (← go p false (some "fallible `!` modifier cannot appear inside a tuple type")).term
      finishMods (qctx.runPure (buildProdTypePure ls)) (← parseMods (s.getArg 3)) `Prod
    else if k == ``qedTypeAtom then
      let (baseId, initMods) ← splitIdentMods ⟨s.getArg 0⟩
      finishMods (resolveBaseTypeTerm baseId) (initMods ++ (← parseMods (s.getArg 1))) baseId.getId.eraseMacroScopes
    else if k == `Qed.Lang.qedTypeNum then return { term := ⟨s.getArg 0⟩ }
    else if k == ``qedTypeApp || k == ``qedTypeArrow then
      if k == ``qedTypeApp && (s.getArg 0).getKind == ``qedTypeAtom && ((s.getArg 0).getArg 1).getArgs.isEmpty then
        let fnName := ((s.getArg 0).getArg 0).getId.eraseMacroScopes; let argStr := let sn := stxSnippet (s.getArg 1); if sn.isEmpty then "T" else sn
        if fnName == `Array || fnName == `Option then return ← .error (s, s!"use `{argStr}{if fnName == `Array then "[]" else "?"}` instead of `{fnName} {argStr}`")
        if allowHigherOrder && fnName == `jsonOnly then return ← .error (s, s!"use `jsonOnly({argStr})` with parentheses instead of `jsonOnly {argStr}`")
      if k == ``qedTypeArrow && !allowHigherOrder then return ← mkInvalidErr s
      let (l, r) := ((← go (s.getArg 0) false none).term, (← go (s.getArg (if k == ``qedTypeApp then 1 else 2)) false none).term)
      return { term := qctx.runPure (if k == ``qedTypeApp then `($l $r) else `($l → $r)) }
    else mkInvalidErr s
  go stx allowFallible none

def lowerQedTypePure (qctx : PureQuotCtx) (stx : Syntax) (allowFallible := false) : Except (Syntax × String) (Term × Bool) := do
  let info ← lowerQedTypeInfoPure qctx stx allowFallible; return (info.term, info.isFallible)
def lowerQedTypeInfo (stx : Syntax) (allowFallible := false) (allowHigherOrder := true) (ctxDesc? : Option String := none) : MacroM LoweredQedType :=
  runPureErrMacro (lowerQedTypeInfoPure · stx allowFallible allowHigherOrder ctxDesc?)
def lowerQedType (stx : Syntax) (allowFallible := false) : MacroM (Term × Bool) :=
  runPureErrMacro (lowerQedTypePure · stx allowFallible)

@[noinline] partial def inferQedTypeDefaultPure? (qctx : PureQuotCtx) (stx : Syntax) : Except (Syntax × String) (Option Term) := do
  let modDef (n : Syntax) (init : Array TypeMod := #[]) : Except (Syntax × String) (Option Term) := do
    match (init ++ (← mapExcept n.getArgs parseTypeModNode)).back? with
    | some .array => return some (qctx.runPure `(#[])) | some .option => return some (mkIdent `none) | _ => return none
  let k := stx.getKind
  if k == `Qed.Lang.qedTypeDict then if let some d ← modDef (stx.getArg 5) then return some d else return some ⟨(mkIdentFrom stx `Qed.Dict.empty).raw⟩
  else if k == `Qed.Lang.qedTypeParen then
    if let some d ← modDef (stx.getArg 3) then return some d
    if (stx.getArg 1).getSepArgs.size == 1 then inferQedTypeDefaultPure? qctx (stx.getArg 1).getSepArgs[0]! else return none
  else if k == ``qedTypeAtom then modDef (stx.getArg 1) (← splitIdentMods ⟨stx.getArg 0⟩).2
  else if k == ``qedTypeApp && (stx.getArg 0).getKind == ``qedTypeAtom && ((stx.getArg 0).getArg 1).getArgs.isEmpty then
    match ((stx.getArg 0).getArg 0).getId.eraseMacroScopes with
    | `Resource => return some ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent #[Syntax.atom .none ".", mkIdent `idle]⟩
    | `Cached => return some (qctx.runPure `({})) | _ => return none
  else return none

def inferQedTypeDefault? (stx : Syntax) : MacroM (Option Term) := runPureErrMacro (inferQedTypeDefaultPure? · stx)

@[noinline] partial def lowerQedPatPure (qctx : PureQuotCtx) (stx : Syntax) : Except (Syntax × String) Term := do
  let k := stx.getKind
  if k == ``qedPatWild then return qctx.runPure `(_)
  else if k == `Qed.Lang.qedPatNum || k == `Qed.Lang.qedPatStr || k == `Qed.Lang.qedPatChar then return ⟨stx.getArg 0⟩
  else if k == ``qedPatParen then return qctx.runPure (buildTupleValPure (← mapExcept (stx.getArg 1).getSepArgs (lowerQedPatPure qctx)))
  else if k == ``qedPatList then let ps ← mapExcept (stx.getArg 1).getSepArgs (lowerQedPatPure qctx); return qctx.runPure `([$[$ps:term],*])
  else if k == ``qedPatCons then return qctx.runPure `(List.cons $(← lowerQedPatPure qctx (stx.getArg 0)) $(← lowerQedPatPure qctx (stx.getArg 2)))
  else if k == ``qedPatDot || k == ``qedPatIdent then
    let headT : Term := if k == ``qedPatDot then ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", stx.getArg 1]⟩ else ⟨stx.getArg 0⟩
    let argsNode := stx.getArg (if k == ``qedPatDot then 2 else 1)
    if argsNode.getNumArgs == 3 then return qctx.runPure (mkAppTermsPure headT (← mapExcept (argsNode.getArg 1).getSepArgs (lowerQedPatPure qctx)))
    else return headT
  else let sn := stxSnippet stx; .error (stx, s!"unsupported pattern{if sn.isEmpty then "" else s!" `{sn}`"}; expected `_`, a literal, an identifier, `.ctor(a, b)`, or a tuple `(a, b)`")

def lowerCasePatAltsPure (qctx : PureQuotCtx) (patsNode : Syntax) : Except (Syntax × String) (Array (Array Term)) :=
  mapExcept (extractCasePatAlts patsNode) (mapExcept · (lowerQedPatPure qctx))
def lowerQedPat (stx : Syntax) : MacroM Term := runPureErrMacro (lowerQedPatPure · stx)
def lowerCasePatAlts (patsNode : Syntax) : MacroM (Array (Array Term)) := runPureErrMacro (lowerCasePatAltsPure · patsNode)

/-! ## Unified Expression Lowering (`ExprMode`, `lowerQedExpr`, `lowerSimpleQedExpr`) -/

inductive ExprMode where | val | boolCond | propGuard | propInv deriving BEq, DecidableEq
def ExprMode.isProp (m : ExprMode) : Bool := m == .propInv || m == .propGuard
private def exprHasIndex (stx : Syntax) : Bool := stxAny (fun s => s.getKind == ``qedIndex && (s.getArg 4).getNumArgs == 0) stx

private def isPlainLiteralOrCtor (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx; let k := u.getKind; let plainFields := ["size", "length", "isSome", "isNone", "isEmpty", "val"]
  if [``qedLitNum, `Qed.Lang.qedLitSci, ``qedLitStr, `Qed.Lang.qedLitChar, ``qedFStr, ``qedArrLit, `Qed.Lang.qedDictLit, ``qedRecLit, ``qedDotIdent, ``qedNeg, ``qedMul, ``qedDiv, ``qedMod, ``qedAdd, ``qedSub, ``qedCat, ``qedCons].contains k then true
  else if k == ``qedIdent then
    let nm := (u.getArg 0).getId; let s := nm.toString
    ["true", "false", "none"].contains s || (nm.isStr && nm.getPrefix != .anonymous && plainFields.contains (match nm with | .str _ f => f | _ => s))
  else if k == ``qedProj then (u.getArg 2).isIdent && plainFields.contains (u.getArg 2).getId.toString
  else k == ``qedCall && ((u.getArg 0).getKind == ``qedDotIdent || ((u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.toString == "some"))

private def isNoneExpr (stx : Syntax) : Bool := let u := unwrapParens1 stx; u.getKind == ``qedIdent && (u.getArg 0).getId.toString == "none"
def cmpOpKind (opStx : Syntax) : String := let raw := (opStx.reprint.getD "").trimAscii.toString; if raw.contains ' ' then String.intercalate " " ((raw.splitOn " ").filter (!·.isEmpty)) else raw
def mkRawExpr (t : Term) : Syntax := let info := t.raw.getHeadInfo; Syntax.node info ``qedRawTerm #[Syntax.atom info "qedRaw%(", t.raw, Syntax.atom info ")"]

structure LowerHooks (m : Type → Type) where mk ::
  (lowerIdent : Syntax → Ident → ExprMode → m Term) (lowerProj : Syntax → Term → Syntax → ExprMode → m Term)
  (lowerIndex lowerIndexOpt : Syntax → Term → Term → ExprMode → m Term)
  (lowerCall : Syntax → Syntax → Array Syntax → ExprMode → (ExprMode → Syntax → m Term) → m (Option Term))
  (lowerUnwrap lowerAwait : Syntax → Syntax → ExprMode → m Term) (lowerJsx : Syntax → ExprMode → m Term)
  (lowerArrElem wrapNamedField : Term → m Term) (lowerType lowerPat : Syntax → m Term)
  (withLocals : Array String → m Term → m Term) (useDirectArray allowOptElse : Bool := false)
  (optElseFallback : Syntax → Term → m Term) (wrapForMap : Syntax → Term → Term → m Term)
  (freshIdent : String → m Ident) (throwErr : Syntax → String → m Term)

inductive LocalMutAction where | assign (id : Ident) (op : String) (rhsStx : Syntax) | push (id : Ident) (elemStx : Syntax) | remove (id : Ident) (keyStx : Syntax)
def LocalMutAction.targetIdent : LocalMutAction → Ident | .assign id _ _ | .push id _ | .remove id _ => id
def LocalMutAction.rhsSyntax : LocalMutAction → Syntax | .assign _ _ s | .push _ s | .remove _ s => s

@[noinline] def finishTermModePure (mode : ExprMode) (t : Term) : PureQuotM Term := if mode.isProp then `(qedAsProp($t)) else return t
@[noinline, nospecialize] def finishTermMode {m : Type → Type} [Monad m] [MonadQuotation m] (mode : ExprMode) (t : Term) : m Term := runPureQuot (finishTermModePure mode t)

@[noinline] def mkProjTermPure (obj : Term) (fld : Syntax) : PureQuotM Term := do
  if fld.isIdent then `(($obj).$(⟨fld⟩):ident)
  else
    let info := SourceInfo.fromRef fld
    return ⟨Syntax.node info ``Lean.Parser.Term.proj #[(← `(($obj))).raw, Syntax.atom info ".", fld]⟩
@[noinline] private def mkDefaultProjPure (obj : Term) (fld : Syntax) (mode : ExprMode) : PureQuotM Term := do finishTermModePure mode (← mkProjTermPure obj fld)
@[noinline] private def mkDefaultIndexPure (opt : Bool) (arr idx : Term) (mode : ExprMode) : PureQuotM Term := do finishTermModePure mode (← if opt then `($arr[$idx]?) else `($arr[$idx]))

@[noinline] private def defaultJsxErrMsg (ref : Syntax) : String :=
  if ref.getKind.getPrefix == `Qed.Jsx then "JSX elements are only allowed inside view expressions"
  else let sn := stxSnippet ref; s!"unsupported Qed expression{if sn.isEmpty then s!"({ref.getKind})" else s!" `{sn}`"}"

@[noinline, nospecialize] def LowerHooks.mkDefault {m : Type → Type} [Monad m] [MonadQuotation m] (throwErr : Syntax → String → m Term) : LowerHooks m := {
  lowerIdent := fun _ id mode => finishTermMode mode ⟨id.raw⟩
  lowerProj  := fun _ obj fld mode => runPureQuot (mkDefaultProjPure obj fld mode)
  lowerIndex := fun _ arr idx mode => runPureQuot (mkDefaultIndexPure false arr idx mode)
  lowerIndexOpt := fun _ arr idx mode => runPureQuot (mkDefaultIndexPure true arr idx mode)
  lowerCall  := fun _ _ _ _ _ => pure none
  lowerUnwrap := fun ref _ _ => throwErr ref "operator `?` is only supported inside `server` functions with a fallible (`T!`) or optional (`T?`) return type"
  lowerAwait  := fun ref _ _ => throwErr ref "`await` is only supported in statements (`let x = await ...` or `field = await ...`)"
  lowerJsx    := fun ref _ => throwErr ref (defaultJsxErrMsg ref)
  lowerArrElem := pure, wrapNamedField := pure
  lowerType := fun ref => throwErr ref "type annotations are not supported here"
  lowerPat  := fun ref => throwErr ref "patterns are not supported here"
  withLocals := fun _ k => k, optElseFallback := fun _ _ => runPureQuot (buildTupleValPure #[])
  wrapForMap := fun _ _ t => pure t, freshIdent := fun pfx => pure (mkIdent (Name.mkSimple pfx)), throwErr
}

@[noinline] private def mkParen (t : Term) : PureQuotM Term := `(($t))

@[noinline] private def mkBinNode (kind : Name) (tok : String) (a b : Term) (paren : Bool := true) : PureQuotM Term := do
  let info := SourceInfo.fromRef (← getRef)
  let a' ← if paren then mkParen a else pure a
  let b' ← if paren then mkParen b else pure b
  return ⟨Syntax.node info kind #[a'.raw, Syntax.atom info tok, b'.raw]⟩

@[noinline] private def mkUnNode (kind : Name) (tok : String) (a : Term) : PureQuotM Term := do
  let info := SourceInfo.fromRef (← getRef)
  return ⟨Syntax.node info kind #[Syntax.atom info tok, (← mkParen a).raw]⟩

@[noinline] private def mkBinOpPure (k : String) (a b : Term) : PureQuotM Term :=
  let (kind, tok) := match k with
    | "qedPow"    => (`«term_^_», "^")     | "qedMul"    => (`«term_*_», "*")   | "qedDiv"    => (`«term_/_», "/")
    | "qedMod"    => (`«term_%_», "%")     | "qedAdd"    => (`«term_+_», "+")   | "qedSub"    => (`«term_-_», "-")
    | "qedShl"    => (`«term_<<<_», "<<<") | "qedShr"    => (`«term_>>>_», ">>>")
    | "qedBitAnd" => (`«term_&&&_», "&&&") | "qedBitXor" => (`«term_^^^_», "^^^")
    | "qedBitOr"  => (`«term_|||_», "|||") | _           => (`«term_++_», "++")
  mkBinNode kind tok a b

private def assignOpToBinKind? : String → Option String
  | "+=" => some "qedAdd"    | "-=" => some "qedSub"    | "*=" => some "qedMul"
  | "/=" => some "qedDiv"    | "%=" => some "qedMod"    | "&=" => some "qedBitAnd"
  | "|=" => some "qedBitOr"  | "^=" => some "qedBitXor" | "<<=" => some "qedShl"
  | ">>=" => some "qedShr"   | _ => none

@[noinline] def applyAssignOpPure (qctx : PureQuotCtx) (ref : Syntax) (op : String) (lhs rhs : Term) : Except (Syntax × String) Term :=
  if op == "=" then .ok rhs
  else match assignOpToBinKind? op with
    | some bk => .ok (qctx.runPure do mkBinOpPure bk (← `($qValId $lhs)) (← `($qValId $rhs)))
    | none    => .error (ref, s!"unsupported assignment operator `{op}`")

@[noinline] private def mkCmpSinglePure (mode : ExprMode) (opStr : String) (a b : Term) (rhsIsListLit : Bool := false) : PureQuotM Term := do
  if ["==", "!=", "is", "is not"].contains opStr then
    let isEq := opStr == "==" || opStr == "is"
    match mode with
    | .propInv   => if isEq then mkBinNode `«term_=_» "=" a b else mkBinNode `«term_≠_» "≠" a b
    | .propGuard => let p ← `(qedEqProp($a, $b)); if isEq then pure p else mkUnNode `«term¬_» "¬" p
    | _          => if isEq then mkBinNode `«term_==_» "==" a b else mkBinNode `«term_!=_» "!=" a b
  else if opStr == "in" || opStr == "not in" then
    let mem ← if rhsIsListLit then
        if mode.isProp then `($qInListPrId ($a) ($b)) else `($qInListId ($a) ($b))
      else
        if mode.isProp then `($qMemPropId ($a) ($b)) else `($qMemId ($a) ($b))
    if opStr == "in" then pure mem else if mode.isProp then mkUnNode `«term¬_» "¬" mem else mkUnNode `term!_ "!" mem
  else
    let (kind, tok) := match opStr with | "<=" => (`«term_≤_», "≤") | ">=" => (`«term_≥_», "≥") | "<" => (`«term_<_», "<") | _ => (`«term_>_», ">")
    let p ← mkBinNode kind tok a b
    if mode.isProp then pure p else `(decide ($p))

@[noinline] private def mkAndOrPure (isAnd : Bool) (mode : ExprMode) (h? : Option Ident) (a b : Term) : PureQuotM Term :=
  match h? with
  | some h =>
      if mode == .propGuard then if isAnd then `(Qed.Lang.QedAndProp ($a) (fun ($h:ident : $a) => $b)) else `(Qed.Lang.QedOrProp ($a) (fun ($h:ident : ¬ ($a)) => $b))
      else `(if $h:ident : ($a) = true then $b else false)
  | none =>
      let (kind, tok) := match mode.isProp, isAnd with
        | true, true => (`«term_∧_», "∧") | true, false => (`«term_∨_», "∨")
        | false, true => (`«term_&&_», "&&") | false, false => (`«term_||_», "||")
      mkBinNode kind tok a b (paren := false)

@[noinline] private def mkArrLitPure (direct : Bool) (elems : Array Term) : PureQuotM Term :=
  if direct then `(#[$[$elems],*]) else `(qedSeqLit%[$[$elems],*])
@[noinline] private def mkDictLitPure (stx : Syntax) (pairs : Array Term) : PureQuotM Term :=
  `($(mkIdentFrom stx `Qed.Dict.ofList) [$[$pairs],*])
@[noinline] private def mkCoalescePure (a b : Term) : PureQuotM Term :=
  `(match ($qCoalId ($a)) with | Option.some _qedC => _qedC | Option.none => $b)
@[noinline] private def mkIfTermPure (hIf : Ident) (condT thenT elseT : Term) : PureQuotM Term :=
  `(if $hIf:ident : $condT then $thenT else $elseT)
@[noinline] private def mkIfLetTermPure (patT scrutT thenT elseT : Term) : PureQuotM Term :=
  `(if let $patT := $scrutT then $thenT else $elseT)
@[noinline] private def mkMatchTermPure (scruts : Array Term) (alts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) : PureQuotM Term :=
  `(match $[$scruts:term],* with $[$alts:matchAlt]*)
@[noinline] private def mkForMapTermPure (stx : Syntax) (xsT bodyT : Term) (patId? : Option Ident) (patT? : Option Term) : PureQuotM Term := do
  let fnT ← match patId?, patT? with
    | some pid, _ => `(fun $pid:ident => $bodyT)
    | none, some pT => `(fun _qed_fe => match _qed_fe with | $pT => $bodyT)
    | none, none => `(fun _ => $bodyT)
  `($(mkIdentFrom stx `Qed.mapList) ($(mkIdentFrom stx `Qed.ForEachItems.toList) $xsT) $fnT)

@[noinline] private def mkLamPure (entries : Array (Syntax × Option Term)) (body : Term) : PureQuotM Term :=
  Lang.foldrPQ entries.zipIdx body fun ((b, ty?), idx) acc =>
    if b.getKind == ``qedLetPatTuple then do
      let pid := mkIdent (Name.mkSimple s!"_qedLam{idx}")
      let pat ← lowerLetBinderPatPure b
      let inner ← `(let $pat:term := $pid:ident; $acc)
      match ty? with | some ty => `(fun ($pid:ident : $ty) => $inner) | none => `(fun $pid:ident => $inner)
    else match ty?, b.isIdent with
      | some ty, true => `(fun ($(⟨b⟩):ident : $ty) => $acc) | some ty, false => `(fun (_ : $ty) => $acc)
      | none, true => `(fun $(⟨b⟩):ident => $acc) | none, false => `(fun _ => $acc)

@[noinline] private def mkAllAnyInPure (isAll : Bool) (mode : ExprMode) (bId : Ident) (bStx : Syntax) (arrT bodyT : Term) : PureQuotM Term := do
  let body ← if bStx.getKind == ``qedLetPatTuple then do
      let pat ← lowerLetBinderPatPure bStx
      `(let $pat:term := $bId:ident; $bodyT)
    else pure bodyT
  match isAll, mode.isProp with
  | true,  true  => `(∀ $bId:ident ∈ $arrT, $body) | true,  false => `(($arrT).all (fun $bId:ident => $body))
  | false, true  => `(∃ $bId:ident ∈ $arrT, $body) | false, false => `(($arrT).any (fun $bId:ident => $body))

@[noinline] private def mkQuantVarsPure (isAll : Bool) (entries : Array (Ident × Option Term)) (bodyT : Term) : PureQuotM Term :=
  Lang.foldrPQ entries bodyT fun (vid, ty?) acc => match isAll, ty? with
    | true,  some ty => `(∀ ($vid:ident : $ty), $acc) | true,  none => `(∀ $vid:ident, $acc)
    | false, some ty => `(∃ ($vid:ident : $ty), $acc) | false, none => `(∃ $vid:ident, $acc)

@[noinline] private def mkRangeCallPure (argTs : Array Term) : PureQuotM (Option Term) :=
  match argTs with
  | #[s] => some <$> `($qRange1Id $s) | #[a, b] => some <$> `($qRange2Id $a $b) | #[a, b, c] => some <$> `($qRange3Id $a $b $c) | _ => pure none

private inductive CollArgKind where | lam1 | lam2 | other deriving BEq

private def classifyCollArgStx (argStx : Syntax) : CollArgKind :=
  let u := unwrapParens1 (argStx.getArg 0)
  if u.getKind == ``qedLam1 then .lam1
  else if u.getKind == ``qedLamN then
    if (u.getArg 1).getSepArgs.size == 2 then .lam2 else .lam1
  else .other

private def nameRootStartsLower : Name → Bool
  | .str .anonymous s => match s.toList.head? with | some c => c.isLower || c == '_' | none => false
  | .str p _ => nameRootStartsLower p
  | _ => false

private structure CollOrdSpec where
  takesRes : Bool
  keyFn    : Name
  cmpFn    : Name
  argFn    : Name

private def collOrdSpec? (nm : Name) (isProp : Bool) : Option CollOrdSpec :=
  match nm with
  | `min          => some ⟨false, `Qed.qedMinKey, `Qed.qedMinCmp, `Qed.QedOrdArg.minFn⟩
  | `max          => some ⟨false, `Qed.qedMaxKey, `Qed.qedMaxCmp, `Qed.QedOrdArg.maxFn⟩
  | `sort         => some ⟨false, `Qed.qedSortKey, `Qed.qedSortCmp, `Qed.QedOrdArg.sortFn⟩
  | `sortDesc     => some ⟨false, `Qed.qedSortDescKey, `Qed.qedSortDescCmp, `Qed.QedOrdArg.sortDescFn⟩
  | `isSorted     => some ⟨false,
      if isProp then `Qed.qedIsSortedKey else `Qed.qedIsSortedKeyB,
      if isProp then `Qed.qedIsSortedCmp else `Qed.qedIsSortedCmpB,
      if isProp then `Qed.QedOrdArg.isSortedFn else `Qed.QedOrdArg.isSortedBFn⟩
  | `isSortedDesc => some ⟨false,
      if isProp then `Qed.qedIsSortedDescKey else `Qed.qedIsSortedDescKeyB,
      if isProp then `Qed.qedIsSortedDescCmp else `Qed.qedIsSortedDescCmpB,
      if isProp then `Qed.QedOrdArg.isSortedDescFn else `Qed.QedOrdArg.isSortedDescBFn⟩
  | `isMinOf      => some ⟨true, `Qed.qedIsMinOfKey, `Qed.qedIsMinOfCmp, `Qed.QedOrdArg.isMinOfFn⟩
  | `isMaxOf      => some ⟨true, `Qed.qedIsMaxOfKey, `Qed.qedIsMaxOfCmp, `Qed.QedOrdArg.isMaxOfFn⟩
  | _             => none

@[noinline] private def mkCollOrdAppPure (spec : CollOrdSpec) (recv : Term) (extraPrefix? : Option Term)
    (optArg? : Option (Term × CollArgKind)) : PureQuotM Term := do
  let (fnId, keyT) := match optArg? with
    | none              => (mkCIdent spec.keyFn, mkCIdent `id)
    | some (t, .lam1)   => (mkCIdent spec.keyFn, t)
    | some (t, .lam2)   => (mkCIdent spec.cmpFn, t)
    | some (t, .other)  => (mkCIdent spec.argFn, t)
  match extraPrefix? with
  | some pfx => `($fnId $pfx $recv $keyT)
  | none     => `($fnId $recv $keyT)

@[noinline, nospecialize] private def tryLowerCollectionCall {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (go : ExprMode → Syntax → m Term) (finish : Term → Term) (mode : ExprMode)
    (calleeStx : Syntax) (rawArgs : Array Syntax) : m (Option Term) := do
  if !rawArgs.all (·.getKind == ``qedCallArgPos) then return none
  let lowerOptKey (a? : Option Syntax) : m (Option (Term × CollArgKind)) := match a? with
    | none => pure none
    | some a => return some (← go .val (a.getArg 0), classifyCollArgStx a)
  let methodRecv? : Option (Syntax × Name) :=
    if calleeStx.getKind == ``qedProj && (calleeStx.getArg 2).isIdent then
      some (calleeStx.getArg 0, (calleeStx.getArg 2).getId.eraseMacroScopes)
    else if calleeStx.getKind == ``qedIdent then
      match (calleeStx.getArg 0).getId.eraseMacroScopes with
      | .str pfx s =>
          if pfx != .anonymous && nameRootStartsLower pfx then
            some (calleeStx.setArg 0 (mkIdentFrom (calleeStx.getArg 0) pfx), Name.mkSimple s)
          else none
      | _ => none
    else none
  if let some (recvStx, nm) := methodRecv? then
    let some spec := collOrdSpec? nm mode.isProp | return none
    if !spec.takesRes && (rawArgs.size == 0 || rawArgs.size == 1) then
      let recvT ← go .val recvStx
      let optK ← lowerOptKey rawArgs[0]?
      return some (finish (qctx.runPure (mkCollOrdAppPure spec recvT none optK)))
    if spec.takesRes && (rawArgs.size == 1 || rawArgs.size == 2) then
      let resT ← go .val recvStx
      let xsT ← go .val (rawArgs[0]!.getArg 0)
      let optK ← lowerOptKey rawArgs[1]?
      return some (finish (qctx.runPure (mkCollOrdAppPure spec xsT (some resT) optK)))
    return none
  if calleeStx.getKind == ``qedIdent then
    let nm := (calleeStx.getArg 0).getId.eraseMacroScopes
    if (nm == `filter || nm == `map) && rawArgs.size == 2 then
      let xsT ← go .val (rawArgs[0]!.getArg 0)
      let fnT ← go .val (rawArgs[1]!.getArg 0)
      let mId := mkIdent nm
      return some (finish (qctx.runPure `(($xsT).$mId:ident $fnT)))
    if (nm == `min || nm == `max) && rawArgs.size == 2 && classifyCollArgStx rawArgs[1]! == .other then
      let aT ← go .val (rawArgs[0]!.getArg 0)
      let bT ← go .val (rawArgs[1]!.getArg 0)
      let runId := mkCIdent (if nm == `min then `Qed.QedMin2.run else `Qed.QedMax2.run)
      return some (finish (qctx.runPure `($runId $aT $bT)))
    let some spec := collOrdSpec? nm mode.isProp | return none
    if !spec.takesRes && (rawArgs.size == 1 || rawArgs.size == 2) then
      let xsT ← go .val (rawArgs[0]!.getArg 0)
      let optK ← lowerOptKey rawArgs[1]?
      return some (finish (qctx.runPure (mkCollOrdAppPure spec xsT none optK)))
    if spec.takesRes && (rawArgs.size == 2 || rawArgs.size == 3) then
      let resT ← go .val (rawArgs[0]!.getArg 0)
      let xsT ← go .val (rawArgs[1]!.getArg 0)
      let optK ← lowerOptKey rawArgs[2]?
      return some (finish (qctx.runPure (mkCollOrdAppPure spec xsT (some resT) optK)))
  return none

@[noinline] private def mkRecLitPure (base? : Option Term) (fIds : Array Ident) (fVals : Array Term) : PureQuotM Term :=
  match base? with | some b => `({ $b with $[$fIds:ident := $fVals:term],* }) | none => if fIds.isEmpty then `({}) else `({ $[$fIds:ident := $fVals:term],* })

private def builtinQualCall? : Name → Option (Name × Nat)
  | `Db.sqlIdent? | `SqlIdent.ofString? => some (`Qed.Server.Db.SqlIdent.ofString?, 1)
  | `Bytes.ctEq => some (`Qed.Bytes.ctEq, 2)
  | `Str.ctEq   => some (`Qed.Str.ctEq, 2)
  | _ => none

@[noinline, nospecialize] private def lowerCallExpr {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (finish : Term → Term) (mode : ExprMode) (stx : Syntax) : m Term := do
  let (calleeStx, rawArgs) := (stx.getArg 0, (stx.getArg 2).getSepArgs)
  if let some custom ← hooks.lowerCall stx calleeStx rawArgs mode go then return custom
  if let some collT ← tryLowerCollectionCall qctx go finish mode calleeStx rawArgs then return collT
  if calleeStx.getKind == ``qedIdent then
    if let some (targetNm, arity) := builtinQualCall? (calleeStx.getArg 0).getId.eraseMacroScopes then
      if rawArgs.size == arity && rawArgs.all (·.getKind == ``qedCallArgPos) then
        let argTs ← mapArrM rawArgs fun a => go .val (a.getArg 0)
        return finish (qctx.runPure `($(mkCIdent targetNm) $argTs*))
  if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId.eraseMacroScopes == `url &&
      rawArgs.size == 1 && rawArgs[0]!.getKind == ``qedCallArgPos && (rawArgs[0]!.getArg 0).getKind == ``qedLitStr then
    let info := SourceInfo.fromRef stx
    return finish ⟨Syntax.node info `Qed.Jsx.qedUrlLit #[calleeStx.getArg 0, Syntax.atom info "(", (rawArgs[0]!.getArg 0).getArg 0, Syntax.atom info ")"]⟩
  if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId.eraseMacroScopes == `range && rawArgs.all (·.getKind == ``qedCallArgPos) then
    let argTs ← mapArrM rawArgs fun a => go .val (a.getArg 0)
    match qctx.runPure (mkRangeCallPure argTs) with
    | some t => return finish t
    | none => return ← hooks.throwErr stx "`range(...)` expects 1, 2, or 3 arguments: `range(stop)`, `range(start, stop)`, or `range(start, stop, step)`"
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then
    unless rawArgs.all (·.getKind == ``qedCallArgNamed) do
      let cs := stxSnippet calleeStx; return ← hooks.throwErr stx s!"cannot mix named (`field=val`) and positional arguments in {if cs.isEmpty then "the same call" else s!"call `{cs}(...)`"}"
    let fIds : Array Ident := rawArgs.map (⟨·[0]⟩)
    let fVals ← mapArrM rawArgs fun a => do hooks.wrapNamedField (← go .val (a.getArg 2))
    let calleeT ← go .val calleeStx
    return qctx.runPure `(({ $[$fIds:ident := $fVals:term],* } : $calleeT))
  let calleeTerm ← go .val calleeStx
  let isPropAll := mode == .propInv && ((calleeStx.getKind == ``qedProj && (calleeStx.getArg 2).isIdent && [`all, `any].contains (calleeStx.getArg 2).getId) ||
    (calleeStx.getKind == ``qedIdent && match (calleeStx.getArg 0).getId with | .str _ "all" | .str _ "any" => true | _ => false))
  let argTerms ← mapArrM rawArgs fun a => let u := unwrapParens1 (a.getArg 0); go (if isPropAll && (u.getKind == ``qedLam1 || u.getKind == ``qedLamN) then .propInv else .val) (a.getArg 0)
  return finish (qctx.runPure (mkAppTermsPure calleeTerm argTerms))

@[noinline, nospecialize] private def lowerCmpExpr {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (hooks : LowerHooks m) (lowerValOp : Syntax → m Term) (mode : ExprMode) (stx : Syntax) : m Term := do
  let rec goLinks (prev : Syntax) (acc? : Option Term) : List Syntax → m Term
    | [] => match acc? with | some t => pure t | none => hooks.throwErr stx "empty comparison"
    | lk :: rest => do
        let opStr := cmpOpKind (lk.getArg 0); let rhsStx := lk.getArg 1
        let (lS, rS) := if ["==", "!=", "is", "is not"].contains opStr && isNoneExpr prev && !isNoneExpr rhsStx then (rhsStx, prev) else (prev, rhsStx)
        let uR := unwrapParens1 rS
        let cur ← if (opStr == "in" || opStr == "not in") && uR.getKind == ``qedArrLit then do
            let aT ← lowerValOp lS
            let elems ← mapArrM (uR.getArg 1).getSepArgs lowerValOp
            pure (qctx.runPure do mkCmpSinglePure mode opStr aT (← `([$[$elems],*])) true)
          else pure (qctx.runPure (mkCmpSinglePure mode opStr (← lowerValOp lS) (← lowerValOp rS)))
        let next := match acc? with | none => cur | some acc => qctx.runPure (if mode.isProp then mkBinNode `«term_∧_» "∧" acc cur false else mkBinNode `«term_&&_» "&&" acc cur false)
        goLinks rhsStx (some next) rest
  goLinks (stx.getArg 0) none (stx.getArg 1).getArgs.toList

@[noinline, nospecialize] private def lowerFStrExpr {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (go : ExprMode → Syntax → m Term) (args : Array Syntax) : m Term := do
  let rec loop (acc? : Option Term) : List Syntax → m Term
    | [] => pure (acc?.getD (Syntax.mkStrLit ""))
    | ch :: rest => do
        let part? : Option Term ← if let some litStr := ch.isInterpolatedStrLit? then
            pure (if litStr.isEmpty then none else some (Syntax.mkStrLit litStr))
          else let t ← go .val ch; pure (some (qctx.runPure `(toString ($qValId $t))))
        let next? := match acc?, part? with | _, none => acc? | none, some p => some p | some acc, some p => some (qctx.runPure `($acc ++ $p))
        loop next? rest
  loop none args.toList

@[noinline, nospecialize] private def lowerAndOrExpr {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (isAnd : Bool) (mode : ExprMode) (stx : Syntax) : m Term := do
  let subMode := if mode.isProp then mode else .boolCond
  let (a, b) := (← go subMode (stx.getArg 0), ← go subMode (stx.getArg 2))
  let h? ← if (mode == .propGuard || (!mode.isProp && isAnd)) && exprHasIndex (stx.getArg 2) then some <$> hooks.freshIdent (if isAnd then "_qedAnd" else "_qedOr") else pure none
  return qctx.runPure (mkAndOrPure isAnd mode h? a b)

@[noinline, nospecialize] private def lowerLamExpr {m : Type → Type} [Monad m]
    (qctx : PureQuotCtx) (hooks : LowerHooks m) (go : ExprMode → Syntax → m Term) (isLam1 : Bool) (mode : ExprMode) (stx : Syntax) : m Term := do
  let pRaw : Array (Syntax × Option Syntax) := if isLam1 then #[(stx.getArg 0, none)]
    else (stx.getArg 1).getSepArgs.map fun p => (p.getArg 0, if (p.getArg 1).getNumArgs == 2 then some ((p.getArg 1).getArg 1) else none)
  let body ← hooks.withLocals (pRaw.flatMap fun (b, _) => (collectLetBinderIds b).map (·.toString))
    (go (if mode == .propInv then .propInv else .val) (stx.getArg (if isLam1 then 2 else 4)))
  let entries ← mapArrM pRaw fun (b, tyOpt?) => match tyOpt? with | some tyStx => return (b, some (← hooks.lowerType tyStx)) | none => pure (b, none)
  return qctx.runPure (mkLamPure entries body)

@[noinline, nospecialize] private partial def lowerQedExprGo {m : Type → Type} [Monad m] [MonadRef m]
    (qctx0 : PureQuotCtx) (hooks : LowerHooks m) (mode : ExprMode) (stx : Syntax) : m Term := withRef stx do
  let qctx := { qctx0 with ref := stx }; let go := lowerQedExprGo qctx hooks
  let lowerValOp (s : Syntax) : m Term := do let t ← go .val s; return if isPlainLiteralOrCtor s then t else qctx.runPure `($qValId $t)
  let finish (t : Term) : Term := qctx.runPure (finishTermModePure mode t)
  let lowerOptElse (ref : Syntax) (elseExpr? : Option Syntax) (thenStx : Syntax) (thenT : Term) (errMsg : String) : m Term :=
    if let some elseStx := elseExpr? then go mode elseStx
    else if hooks.allowOptElse then hooks.optElseFallback thenStx thenT else hooks.throwErr ref errMsg
  match stx.getKind with
  | .str (.str (.str .anonymous "Qed") "Lang") k =>
    match k with
    | "qedRawTerm" => return ⟨stx.getArg 1⟩
    | "qedSqlIdentLit" => return qctx.runPure `($(mkCIdent `Qed.Server.Db.SqlIdent.mk) $(⟨stx.getArg 1⟩) rfl)
    | "qedLitNum" | "qedLitSci" | "qedLitStr" | "qedLitChar" => return ⟨stx.getArg 0⟩
    | "qedFStr" => lowerFStrExpr qctx go (stx.getArg 1).getArgs
    | "qedArrLit" =>
      let elems ← mapArrM (stx.getArg 1).getSepArgs fun e => do hooks.lowerArrElem (← go .val e)
      return qctx.runPure (mkArrLitPure hooks.useDirectArray elems)
    | "qedDictLit" =>
      let mkPair (ks vs : Syntax) : m Term := do let (kt, vt) := (← go .val ks, ← go .val vs); return qctx.runPure (buildTupleValPure #[kt, vt])
      let pairs := #[← mkPair (stx.getArg 1) (stx.getArg 3)] ++ (← mapArrM (stx.getArg 4).getArgs fun r => let e := r.getArg 1; mkPair (e.getArg 0) (e.getArg 2))
      return qctx.runPure (mkDictLitPure stx pairs)
    | "qedRecLit" =>
      let fields := (stx.getArg 2).getSepArgs; let fIds : Array Ident := fields.map (⟨·[0]⟩)
      let hasBase := (stx.getArg 1).getNumArgs == 2
      let ops := fields.map fun f => ((f.getArg 1).reprint.getD "=").trimAscii.toString
      let hasCompound := ops.any (· != "=")
      if hasCompound && !hasBase then
        let badIdx := (ops.findIdx? (· != "=")).getD 0
        return ← hooks.throwErr fields[badIdx]! s!"`{ops[badIdx]!}` in record literal requires a base record (`\{ base with field {ops[badIdx]!} val }`) or database `update(..., set = \{ ... })`"
      let base? ← if hasBase then some <$> go .val ((stx.getArg 1).getArg 0) else pure none
      if hasCompound then
        let baseId ← hooks.freshIdent "_qedRec"
        let fVals ← mapArrM (fields.zip ops) fun (f, op) => do
          let rhsT ← go .val (f.getArg 2)
          let combined ← if op == "=" then pure rhsT else
            match applyAssignOpPure qctx (f.getArg 1) op (qctx.runPure `(($baseId).$(⟨f.getArg 0⟩):ident)) rhsT with
            | .ok t => pure t | .error (ref, msg) => hooks.throwErr ref msg
          hooks.wrapNamedField combined
        let baseT := base?.get!
        return qctx.runPure do let recT ← mkRecLitPure (some ⟨baseId.raw⟩) fIds fVals; `(let $baseId:ident := $baseT; $recT)
      else
        let fVals ← mapArrM fields fun f => do hooks.wrapNamedField (← go .val (f.getArg 2))
        return qctx.runPure (mkRecLitPure base? fIds fVals)
    | "qedFieldSetter" => hooks.throwErr stx s!"`({(stx.getArg 1).getId} = _)` is a component field setter and can only be used inside a `component`"
    | "qedTypeAscr"    => let (eT, tyT) := (← go mode (stx.getArg 1), ← hooks.lowerType (stx.getArg 3)); return qctx.runPure `(($eT : $tyT))
    | "qedParen"       => let elems := (stx.getArg 1).getSepArgs; if elems.size == 1 then go mode elems[0]! else return qctx.runPure (buildTupleValPure (← mapArrM elems (go .val)))
    | "qedPlaceholder" => return qctx.runPure `(_)
    | "qedDotIdent"    => return finish ⟨Syntax.node (.fromRef stx) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef stx) ".", stx.getArg 1]⟩
    | "qedIdent"  => hooks.lowerIdent stx ⟨stx.getArg 0⟩ mode
    | "qedUnwrap" => hooks.lowerUnwrap stx (stx.getArg 0) mode
    | "qedAwait"  => hooks.lowerAwait stx (stx.getArg 1) mode
    | "qedIndex"  =>
      let (arrT, idxT) := (← go .val (stx.getArg 0), ← go .val (stx.getArg 2))
      if (stx.getArg 4).getNumArgs > 0 then hooks.lowerIndexOpt stx arrT idxT mode else hooks.lowerIndex stx arrT idxT mode
    | "qedProj"   => hooks.lowerProj stx (← go .val (stx.getArg 0)) (stx.getArg 2) mode
    | "qedCall"   => lowerCallExpr qctx hooks go finish mode stx
    | "qedNeg"    => let a ← lowerValOp (stx.getArg 1); return qctx.runPure (mkUnNode `«term-_» "-" a)
    | "qedBitNot" => let a ← lowerValOp (stx.getArg 1); return qctx.runPure (mkUnNode `«term~~~_» "~~~" a)
    | "qedPow" | "qedMul" | "qedDiv" | "qedMod" | "qedAdd" | "qedSub" | "qedCat"
    | "qedShl" | "qedShr" | "qedBitAnd" | "qedBitXor" | "qedBitOr" =>
      return qctx.runPure (mkBinOpPure k (← lowerValOp (stx.getArg 0)) (← lowerValOp (stx.getArg 2)))
    | "qedCons" =>
      let (hd, tl) := (← go .val (stx.getArg 0), ← go .val (stx.getArg 2))
      return qctx.runPure `(List.cons $hd $tl)
    | "qedCoalesce" =>
      let (a, b) := (← go .val (stx.getArg 0), ← go .val (stx.getArg 2))
      return finish (qctx.runPure (mkCoalescePure a b))
    | "qedCmp" => lowerCmpExpr qctx hooks lowerValOp mode stx
    | "qedNot" =>
      let a ← go (if mode.isProp then mode else .boolCond) (stx.getArg 1)
      return qctx.runPure (if mode.isProp then mkUnNode `«term¬_» "¬" a else mkUnNode `term!_ "!" a)
    | "qedAnd" | "qedOr" => lowerAndOrExpr qctx hooks go (k == "qedAnd") mode stx
    | "qedImp" =>
      let sub := if mode.isProp then mode else .boolCond; let (a, b) := (← go sub (stx.getArg 0), ← go sub (stx.getArg 2))
      return qctx.runPure (if mode.isProp then mkBinNode ``Lean.Parser.Term.arrow "→" a b false else do mkBinNode `«term_||_» "||" (← mkUnNode `term!_ "!" a) b false)
    | "qedTernary" | "qedExprIf" =>
      let (cI, tI, elseExpr?, err) := if k == "qedTernary" then
          (2, 0, extractOptElseExpr? (stx.getArg 3), "conditional expression `a if cond else b` requires an `else` branch here")
        else (1, 3, desugarExprElifs? (stx.getArg 4).getArgs (stx.getArg 5), "`if cond: ...` expression requires `else:` here")
      if k == "qedExprIf" && mode.isProp && elseExpr?.isNone && hooks.allowOptElse then
        let (condT, thenT) := (← go .propInv (stx.getArg cI), ← go mode (stx.getArg tI)); return qctx.runPure (mkBinNode ``Lean.Parser.Term.arrow "→" condT thenT false)
      else
        let (hIf, condT, thenT) := (← hooks.freshIdent "_qedIf", ← go .propGuard (stx.getArg cI), ← go mode (stx.getArg tI))
        let elseT ← lowerOptElse stx elseExpr? (stx.getArg tI) thenT err
        return qctx.runPure (mkIfTermPure hIf condT thenT elseT)
    | "qedLam1" | "qedLamN" => lowerLamExpr qctx hooks go (k == "qedLam1") mode stx
    | "qedAllIn" | "qedAnyIn" =>
      let (bStx, arrT) := (stx.getArg 1, ← go .val (stx.getArg 3))
      let bId ← if bStx.isIdent then pure ⟨bStx⟩ else hooks.freshIdent "_qedEl"
      let bodyT ← hooks.withLocals ((collectLetBinderIds bStx).map (·.toString)) (go (if mode.isProp then mode else .boolCond) (stx.getArg 5))
      return qctx.runPure (mkAllAnyInPure (k == "qedAllIn") mode bId bStx arrT bodyT)
    | "qedAllVars" | "qedAnyVars" =>
      let isAll := k == "qedAllVars"
      unless mode.isProp do return ← hooks.throwErr stx s!"`{if isAll then "all" else "any"} x, y: ...` without `in` is only valid in invariants and logical propositions; for a runtime check over a collection, write `{if isAll then "all" else "any"} x in items: ...`"
      let rawVs := (stx.getArg 1).getSepArgs
      let bodyT ← hooks.withLocals (rawVs.map fun v => (qedAllVarIdent v).getId.toString) (go mode (stx.getArg 3))
      let entries ← mapArrM rawVs fun vStx => do
        let vid := qedAllVarIdent vStx
        if vStx.getKind == `Qed.Lang.qedAllVarTyped then return (vid, some (← hooks.lowerType (vStx.getArg 2))) else pure (vid, none)
      return qctx.runPure (mkQuantVarsPure isAll entries bodyT)
    | "qedExprLet" =>
      let bStx := stx.getArg 1; let valT ← go .val (stx.getArg 4); let optTy := stx.getArg 2
      let ty? ← if optTy.getNumArgs == 2 then some <$> hooks.lowerType (optTy.getArg 1) else pure none
      let bodyT ← hooks.withLocals ((collectLetBinderIds bStx).map (·.toString)) (go mode (stx.getArg 6))
      return qctx.runPure (mkLetBindTerm bStx ty? valT bodyT)
    | "qedExprIfLet" =>
      let (patT, scrutT, thenT) := (← hooks.lowerPat (stx.getArg 2), ← go .val (stx.getArg 4), ← go mode (stx.getArg 6))
      let elseT ← lowerOptElse stx (desugarExprElifs? (stx.getArg 7).getArgs (stx.getArg 8)) (stx.getArg 6) thenT "`if let pat = expr: ...` expression requires `else:` here"
      return qctx.runPure (mkIfLetTermPure patT scrutT thenT elseT)
    | "qedExprMatch" =>
      let scruts ← mapArrM (stx.getArg 1).getSepArgs (go .val)
      let alts ← mapArrM (stx.getArg 3).getArgs fun c => do
        let altStxs := extractCasePatAlts (c.getArg 1)
        let altTerms ← mapArrM altStxs (mapArrM · hooks.lowerPat)
        let rhs ← hooks.withLocals ((collectCasePatIds altStxs).map (·.toString)) (go mode (c.getArg 3))
        return qctx.runPure (mkMatchAltFromAlts altTerms rhs)
      return qctx.runPure (mkMatchTermPure scruts alts)
    | "qedExprFor" =>
      let (patStx, bodyStx) := (stx.getArg 1, stx.getArg 5); let xsT ← go .val (stx.getArg 3)
      let bodyT ← hooks.withLocals ((collectQedPatIds patStx).map (·.toString)) (go .val bodyStx)
      let t ← if patStx.getKind == ``qedPatIdent && (patStx.getArg 1).getNumArgs == 0 then
          pure (qctx.runPure (mkForMapTermPure stx xsT bodyT (some ⟨patStx.getArg 0⟩) none))
        else pure (qctx.runPure (mkForMapTermPure stx xsT bodyT none (some (← hooks.lowerPat patStx))))
      hooks.wrapForMap bodyStx bodyT t
    | _ => hooks.lowerJsx stx mode
  | _ => hooks.lowerJsx stx mode

/-- Unified lowerer for all `qedExpr` nodes across `server`, `component`, `schema`, `invariant`, and JSX. -/
@[noinline, nospecialize] def lowerQedExpr {m : Type → Type} [Monad m] [MonadQuotation m] (hooks : LowerHooks m) (mode : ExprMode) (stx : Syntax) : m Term := do
  lowerQedExprGo (← getPureQuotCtx) hooks mode stx

@[noinline] def lowerSimpleQedExpr (mode : ExprMode) (stx : Syntax) (allowOptElse := false) (optElseFallback : MacroM Term := `(()))
    (lowerJsx? : Option (Syntax → ExprMode → MacroM Term) := none) (wrapNamedField : Term → MacroM Term := pure)
    (lowerIndex? : Option (Syntax → Term → Term → ExprMode → MacroM Term) := none) : MacroM Term :=
  let base := LowerHooks.mkDefault Macro.throwErrorAt
  lowerQedExpr { base with
    lowerIndex := lowerIndex?.getD base.lowerIndex, lowerJsx := lowerJsx?.getD base.lowerJsx,
    wrapNamedField, lowerType := fun t => return (← lowerQedType t false).1, lowerPat := lowerQedPat,
    allowOptElse, optElseFallback := fun _ _ => optElseFallback } mode stx

/-! ## Shared Visibility & Mutable-Local / Loop Lowering Helpers -/

@[noinline] private partial def markCmdPrivatePure (cmd : TSyntax `command) : PureQuotM (TSyntax `command) := do
  let raw := cmd.raw
  if raw.getKind == ``Lean.Parser.Command.declaration then
    let mods := raw.getArg 0
    if mods.getKind == ``Lean.Parser.Command.declModifiers then
      let vis := mods.getArg 2
      if vis.getNumArgs == 0 then return ⟨raw.setArg 0 (mods.setArg 2 (vis.setArgs #[(← `(Lean.Parser.Command.visibility| private)).raw]))⟩
  else if raw.getKind == ``Lean.Parser.Command.in then
    return ⟨raw.setArg 2 (← markCmdPrivatePure ⟨raw.getArg 2⟩).raw⟩
  return cmd

@[noinline] def markCmdPrivate (cmd : TSyntax `command) : Elab.Command.CommandElabM (TSyntax `command) := Lang.runPQ (markCmdPrivatePure cmd)
@[noinline] def elabCmdWithVis (isPrivate : Bool) (cmd : TSyntax `command) : Elab.Command.CommandElabM Unit := do
  let c ← if isPrivate then markCmdPrivate cmd else pure cmd
  Elab.Command.elabCommand c
def extractOptDoc (optDoc : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) :=
  if optDoc.getNumArgs == 1 then some ⟨optDoc.getArg 0⟩ else none

def isRangeCallExpr (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `range

def tryMatchLocalMut? (muts : Array Ident) (stmt : Syntax) : Option LocalMutAction :=
  let asPlainMutId (e : Syntax) : Option Ident :=
    let u := unwrapParens1 e
    if u.getKind == ``qedIdent then
      let id : Ident := ⟨u.getArg 0⟩; let nm := id.getId.eraseMacroScopes
      if nm.isAtomic && muts.any (·.getId.eraseMacroScopes == nm) then some id else none
    else none
  match stmt.getKind with
  | ``qedStmtAssign => (asPlainMutId (stmt.getArg 0)).map (.assign · (((stmt.getArg 1).reprint.getD "=").trimAscii.toString) (stmt.getArg 2))
  | ``qedStmtExpr =>
      let e := stmt.getArg 0
      match matchPushCall? e with
      | some (tgt, arg) => (asPlainMutId tgt).map (.push · arg)
      | none => (matchRemoveCall? e).bind fun (tgt, arg) => (asPlainMutId tgt).map (.remove · arg)
  | _ => none

@[noinline] def applyLocalMutRhsPure (qctx : PureQuotCtx) (act : LocalMutAction) (rhsTerm : Term) : Except (Syntax × String) Term :=
  match act with
  | .assign id op _ => applyAssignOpPure qctx id op ⟨id.raw⟩ rhsTerm
  | .push id _   => .ok (qctx.runPure `(($id).push $rhsTerm))
  | .remove id _ => .ok (qctx.runPure `(($id).remove $rhsTerm))

def applyLocalMutRhs (act : LocalMutAction) (rhsTerm : Term) : MacroM Term := runPureErrMacro (applyLocalMutRhsPure · act rhsTerm)

@[noinline] def mkForLoopLamPure (elemPfx : String) (stParam : Ident) (bStx : Syntax) (bodyWithUnpack : Term) : PureQuotM Term := do
  if bStx.isIdent then `(fun $stParam:ident $(⟨bStx⟩):ident => $bodyWithUnpack)
  else if bStx.getKind == `Qed.Lang.qedLetPatTuple then
    let elemId := mkIdent (Name.mkSimple elemPfx)
    let pat ← lowerLetBinderPatPure bStx
    `(fun $stParam:ident $elemId:ident => let $pat:term := $elemId:ident; $bodyWithUnpack)
  else `(fun $stParam:ident _ => $bodyWithUnpack)

private partial def collectMutatedInNode (shadowed : Std.HashSet Name) (node : Syntax) (acc : Std.HashSet Name) : Std.HashSet Name :=
  if node.getKind == `Qed.Lang.suite then collectMutatedInStmts shadowed (suiteStmts node) 0 acc
  else node.getArgs.foldl (fun a ch => collectMutatedInNode shadowed ch a) acc
where
  addNames (s : Std.HashSet Name) (ns : Array Name) : Std.HashSet Name := ns.foldl (·.insert ·) s
  collectMutatedInStmts (shadowed : Std.HashSet Name) (stmts : Array Syntax) (i : Nat) (acc : Std.HashSet Name) : Std.HashSet Name :=
    if h : i < stmts.size then
      let st := stmts[i]
      let recordTarget (tgt : Syntax) (a : Std.HashSet Name) : Std.HashSet Name :=
        let u := unwrapParens1 tgt
        if u.getKind == ``qedIdent then let nm := (u.getArg 0).getId.eraseMacroScopes; if nm.isAtomic && !shadowed.contains nm then a.insert nm else a else a
      match st.getKind with
      | ``qedStmtLet     => collectMutatedInStmts (addNames shadowed (collectLetBinderIds (st.getArg 1))) stmts (i + 1) (collectMutatedInNode shadowed (st.getArg 5) acc)
      | ``qedStmtLetMut  => collectMutatedInStmts (shadowed.insert (st.getArg 2).getId.eraseMacroScopes) stmts (i + 1) acc
      | ``qedStmtLetElse => collectMutatedInStmts (addNames shadowed (collectQedPatIds (st.getArg 1))) stmts (i + 1) (collectMutatedInStmts shadowed (extractLetElseStmts st) 0 acc)
      | ``qedStmtAssign  => collectMutatedInStmts shadowed stmts (i + 1) (recordTarget (st.getArg 0) acc)
      | ``qedStmtExpr    =>
          let acc1 := match matchPushCall? (st.getArg 0) <|> matchRemoveCall? (st.getArg 0) with | some (t, _) => recordTarget t acc | none => acc
          collectMutatedInStmts shadowed stmts (i + 1) acc1
      | ``qedStmtFor     =>
          let shBody := addNames shadowed (collectLetBinderIds (st.getArg 1))
          collectMutatedInStmts shadowed stmts (i + 1) (collectMutatedInStmts shBody (suiteStmts (st.getArg 5)) 0 acc)
      | ``qedStmtIf      =>
          let acc1 := collectMutatedInStmts shadowed (suiteStmts (st.getArg 3)) 0 acc
          let acc2 := match desugarElifs (st.getArg 4).getArgs (st.getArg 5) with | some es => collectMutatedInStmts shadowed es 0 acc1 | none => acc1
          collectMutatedInStmts shadowed stmts (i + 1) acc2
      | ``qedStmtIfLet   =>
          let acc1 := collectMutatedInStmts (addNames shadowed (collectQedPatIds (st.getArg 2))) (suiteStmts (st.getArg 6)) 0 acc
          let acc2 := match desugarElifs (st.getArg 7).getArgs (st.getArg 8) with | some es => collectMutatedInStmts shadowed es 0 acc1 | none => acc1
          collectMutatedInStmts shadowed stmts (i + 1) acc2
      | ``qedStmtMatch   =>
          let acc1 := (st.getArg 3).getArgs.foldl (init := acc) fun a c =>
            collectMutatedInStmts (addNames shadowed (collectCasePatIds (extractCasePatAlts (c.getArg 1)))) (suiteStmts (c.getArg 3)) 0 a
          collectMutatedInStmts shadowed stmts (i + 1) acc1
      | _ => collectMutatedInStmts shadowed stmts (i + 1) (collectMutatedInNode shadowed st acc)
    else acc

def collectMutatedIds (stmts : Array Syntax) : Std.HashSet Name := collectMutatedInNode.collectMutatedInStmts {} stmts 0 {}
@[noinline] def mkMutPack (ids : List Ident) : PureQuotM Term := buildTupleValPure (ids.toArray.map (⟨·.raw⟩))
@[noinline] def wrapMutUnpack (stId : Ident) (ids : List Ident) (body : Term) : PureQuotM Term :=
  match ids with
  | [] => pure body
  | [x] => if x.getId.eraseMacroScopes == stId.getId.eraseMacroScopes then pure body else `(let $x:ident := $stId:ident; $body)
  | _ => do let pat ← mkMutPack ids; `(let $pat:term := $stId:ident; $body)

end Qed.Lang

namespace Qed

export Qed.Lang (PureQuotCtx PureQuotM runPureQuot parseOptTacSeq)

open Lean Meta Elab Tactic Command Term PrettyPrinter

def qedLooksGenerated (n : Name) : Bool := match n with
  | .str _ s => !["_qed_render", "_qed_renderTag", "_qed_mount", "_qed_mountWithOpt"].contains s && (n.isInternalDetail ||
      ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion", "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg", "toJson", "fromJson"].contains s ||
      ["match_", "eq_", "inst", "_wsKey_"].any (s.startsWith ·) || ["_key", "_sub", "_unsub", "_send"].any (s.endsWith ·))
  | _ => n.isInternalDetail

def qedIsHelper (env : Environment) (n : Name) : Bool :=
  !Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n n) (includeQed := true) &&
  (match env.find? n with | some (.defnInfo d) => !d.type.isConstOf `Qed.Style | _ => false) && !qedLooksGenerated n

@[noinline] private def mkUnfoldSimpTac (present : Array Name) (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (includeLCtx useSimpAll tryRfl : Bool) : PureQuotM (TSyntax `tactic) := do
  let combined := (← Lang.mapPQ present fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)) ++ extraLemmas
  if useSimpAll then `(tactic| simp_all only [$[$combined],*])
  else
    let base ← if includeLCtx then `(tactic| simp only [$[$combined],*] at *) else `(tactic| simp only [$[$combined],*])
    if tryRfl then `(tactic| ($base:tactic; try rfl)) else pure base

@[noinline] def qedUnfoldHelperLoop (maxIters : Nat) (keep : Environment → Name → MetaM Bool)
    (extraLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (includeLCtx useSimpAll tryRfl : Bool := false) : TacticM Unit := do
  let rec go : Nat → TacticM Unit
    | 0 => pure ()
    | n + 1 => do
        if (← getGoals).isEmpty then return
        let env ← getEnv
        let present ← withMainContext do
          let mut cs := (← instantiateMVars (← getMainTarget)).getUsedConstants
          if includeLCtx then
            let tys := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.type
            let rec addTys : Nat → Array Name → MetaM (Array Name)
              | 0, acc => pure acc
              | r + 1, acc => do let i := tys.size - (r + 1); if h : i < tys.size then addTys r ((← instantiateMVars tys[i]).getUsedConstants.foldl Qed.Lang.pushUnique acc) else pure acc
            cs ← addTys tys.size cs
          let rec filt : Nat → Array Name → MetaM (Array Name)
            | 0, acc => pure acc
            | r + 1, acc => do let i := cs.size - (r + 1); if h : i < cs.size then let nm := cs[i]; filt r (if ← keep env nm then acc.push nm else acc) else pure acc
          filt cs.size #[]
        if present.isEmpty then
          if useSimpAll && !extraLemmas.isEmpty then
            try evalTactic (← Qed.Lang.runPQTactic `(tactic| simp_all only [$[$extraLemmas],*])) catch _ => pure ()
        else
          let tac ← Qed.Lang.runPQTactic (mkUnfoldSimpTac present extraLemmas includeLCtx useSimpAll tryRfl)
          if ← try evalTactic tac; pure true catch _ => pure false then go n
  go maxIters

@[noinline] def mkConjBodyPure (clauses : Array Term) (ascribeProp : Bool := true) : PureQuotM Term := do
  let props ← if ascribeProp then Lang.mapPQ clauses fun c => `(($c : Prop)) else pure clauses
  if h : props.size = 0 then `(True) else Lang.foldlPQ (props.extract 1 props.size) props[0] fun acc x => `($acc ∧ $x)
@[noinline, nospecialize] def mkConjBody {m : Type → Type} [Monad m] [MonadQuotation m] (clauses : Array Term) (ascribeProp : Bool := true) : m Term :=
  runPureQuot (mkConjBodyPure clauses ascribeProp)

@[noinline] def extractInvPred (id : Ident) : TermElabM (TSyntax `term) := do
  let cTy := (← getConstInfo (← realizeGlobalConstNoOverload id)).type
  forallTelescope (if cTy.isAppOfArity ``And 2 then cTy.appArg! else cTy) fun args _ => do
    let some hIdx ← (List.range args.size).findM? fun i => do if i ≥ 2 then isProp (← inferType args[i]!) else pure false
      | throwErrorAt id "`{id}` doesn't look like a state invariant, so its predicate can't be inferred; write it explicitly (`<pred> for_each … using {id}`)."
    delab (← mkLambdaFVars #[args[hIdx - 2]!] (← inferType args[hIdx]!)).eta

/-- If `ty` is a non-recursive zero-param/zero-index inductive with all nullary constructors, return its constructor count. -/
def nullaryEnumCtorCount? (env : Environment) (ty : Expr) : Option Nat :=
  match ty.getAppFn with
  | .const nm _ => match env.find? nm with
      | some (.inductInfo iv) =>
          if iv.numParams == 0 && iv.numIndices == 0 && !iv.isRec &&
             iv.ctors.all (fun c => match env.find? c with | some (.ctorInfo ci) => ci.numFields == 0 | _ => false)
          then some iv.ctors.length else none
      | _ => none
  | _ => none

/-! ## Pure `fn` Surface Syntax (`qedFnContract`, `fnCmd`, `fnOptProof`, `fnBlindTarget`) -/

declare_syntax_cat qedFnContract

section FnParsers
open Lean Parser PrettyPrinter Parenthesizer Formatter Qed.Lang

private abbrev fExpr : Parser := categoryParser `qedExpr 0
private abbrev fType : Parser := withPosition (categoryParser `qedType 0)
private abbrev fContract : Parser := categoryParser `qedFnContract 0

def fnBlindTarget : Parser := node `Qed.fnBlindTarget (ident >> optional (checkNoWsBefore "" >> ".{" >> sepBy1 ident "," >> "}"))
@[combinator_parenthesizer fnBlindTarget] def fnBlindTarget.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter fnBlindTarget] def fnBlindTarget.formatter : Formatter := pure ()
def fnOptProof : Parser := qedOptProof
@[combinator_parenthesizer fnOptProof] def fnOptProof.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter fnOptProof] def fnOptProof.formatter : Formatter := pure ()

def fnRequiresClause : Parser := leadingNode `Qed.fnRequiresClause maxPrec (withPosition (atomic (identEq `requires) >> sepBy1 fExpr ","))
def fnEnsuresClause  : Parser := leadingNode `Qed.fnEnsuresClause  maxPrec (withPosition (atomic (identEq `ensures) >> sepBy1 fExpr "," >> fnOptProof))
def fnBlindToClause  : Parser := leadingNode `Qed.fnBlindToClause  maxPrec (withPosition (atomic (identEq `blindTo) >> sepBy1 fnBlindTarget "," >> fnOptProof))
def fnExampleClause  : Parser := leadingNode `Qed.fnExampleClause  maxPrec (withPosition (atomic (symbol "example" >> ident) >>
  optional (checkNoWsBefore "" >> "(" >> sepBy1 (node `Qed.fnExParam (ident >> ":" >> fType)) "," >> ")") >>
  optional (symbol "where" >> sepBy1 fExpr ",") >> ":" >> sepBy1 fExpr "," >> fnOptProof))
def fnContractIf     : Parser := leadingNode `Qed.fnContractIf     maxPrec (withPosition (atomic (symbol "if" >> notFollowedBy (symbol "let") "let" >> sepBy1 fExpr "," >> ":" >>
  checkColGt "expected indented contract clauses" >> many1Indent fContract)))
@[qedFnContract_parser] def qedFnContractP : Parser := opaqueP (fnRequiresClause <|> fnEnsuresClause <|> fnBlindToClause <|> fnExampleClause <|> fnContractIf)

@[command_parser] def fnCmd : Parser := opaqueP (node `Qed.fnCmd (
  optional Command.docComment >>
  withPosition (atomic (optional (symbol "private") >> identEq `fn >> ident >> "(") >>
    commaSep (node `Qed.fnParam (ident >> ":" >> fType >> optional ("=" >> fExpr))) >> ")" >>
    optional (" -> " >> fType) >> ":" >>
    ((checkLineEq >> pushNone >> sepBy1 (categoryParser `qedStmt 0) ";") <|>
     (checkColGt "expected indented `fn` body" >>
      withPosition (many (atomic (checkColEq "contract" >> fContract)) >> many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))))))

end FnParsers

/-! ## Shared Pure Statement Lowering (`lowerPureStmtsM`, `lowerPureFnStmts`) -/

section PureStmtLower
open Qed.Lang

structure PureStmtHooks (m : Type → Type) (σ : Type) where
  withVal         : σ → Syntax → (Term → m Term) → m Term
  withGuard       : σ → Syntax → (Term → m Term) → m Term
  extendLocals    : σ → Array Name → σ
  onEmpty         : σ → m Term
  onReturn        : σ → Syntax → List Syntax → m Term
  onExpr          : σ → Syntax → List Syntax → m Term
  onCustom?       : Option (σ → Syntax → List Syntax → (σ → List Syntax → m Term) → m (Option Term)) := none
  onMissingElse   : Syntax → String → m Term
  onUnsupported   : Syntax → m Term
  freshIfId?      : Option (m Ident) := none
  depIfLet        : Bool := true
  appendRest      : Bool := true
  letClauseErr    : String := "`predict`/`catch` clauses are not supported here"

@[noinline, nospecialize] private partial def lowerPureStmtsGo {m : Type → Type} {σ : Type} [Monad m] [MonadError m]
    (qctx : PureQuotCtx) (h : PureStmtHooks m σ) (env : σ) (stmts : List Syntax) : m Term := do
  let go := lowerPureStmtsGo qctx h
  let lowerBranchElse (st : Syntax) (kindName : String) (elseSuite? : Option (Array Syntax)) (rest : List Syntax) : m Term :=
    match elseSuite?, h.appendRest with
    | some es, true => go env (es.toList ++ rest) | some es, false => go env es.toList
    | none, true => go env rest | none, false => if rest.isEmpty then h.onMissingElse st kindName else go env rest
  match stmts with
  | [] => h.onEmpty env
  | s :: rest =>
      match s.getKind with
      | ``qedStmtPass => go env rest
      | ``qedStmtReturn => h.onReturn env s rest
      | ``qedStmtLet =>
        if (s.getArg 5).getNumArgs > 0 then throwErrorAt ((s.getArg 5).getArg 0) h.letClauseErr
        let bStx := s.getArg 1
        let ty? ← if (s.getArg 2).getNumArgs == 2 then some <$> (return (← liftPureErr (lowerQedTypePure qctx ((s.getArg 2).getArg 1) false)).1) else pure none
        h.withVal env (s.getArg 4) fun rhsT => do
          let cont ← go (h.extendLocals env (collectLetBinderIds bStx)) rest
          return qctx.runPure (mkLetBindTerm bStx ty? rhsT cont)
      | ``qedStmtIf =>
        h.withGuard env (s.getArg 1) fun condT => do
          let thenT ← go env ((suiteStmts (s.getArg 3)).toList ++ if h.appendRest then rest else [])
          let elseT ← lowerBranchElse s "if" (desugarElifs (s.getArg 4).getArgs (s.getArg 5)) rest
          let hIf ← match h.freshIfId? with | some mk => mk | none => pure (mkIdent `_qedIf)
          return qctx.runPure (mkIfTermPure hIf condT thenT elseT)
      | ``qedStmtIfLet =>
        let pat ← liftPureErr (lowerQedPatPure qctx (s.getArg 2))
        h.withVal env (s.getArg 4) fun scrT => do
          let thenT ← go (h.extendLocals env (collectQedPatIds (s.getArg 2))) ((suiteStmts (s.getArg 6)).toList ++ if h.appendRest then rest else [])
          let elseT ← lowerBranchElse s "if let" (desugarElifs (s.getArg 7).getArgs (s.getArg 8)) rest
          return qctx.runPure (if h.depIfLet then `(match $(mkIdent `_qedIfLet):ident : $scrT:term with | $pat:term => $thenT | _ => $elseT)
                               else `(match $scrT:term with | $pat:term => $thenT | _ => $elseT))
      | ``qedStmtMatch =>
        let rec lowerScrs (rem : List Syntax) (acc : Array Term) : m Term := do
          match rem with
          | scr :: more => h.withVal env scr fun t => lowerScrs more (acc.push t)
          | [] =>
            let alts ← mapArrM (s.getArg 3).getArgs fun alt => do
              let altTerms ← liftPureErr (lowerCasePatAltsPure qctx (alt.getArg 1))
              let body ← go (h.extendLocals env (collectCasePatIds (extractCasePatAlts (alt.getArg 1)))) ((suiteStmts (alt.getArg 3)).toList ++ if h.appendRest then rest else [])
              return qctx.runPure (mkMatchAltFromAlts altTerms body)
            return qctx.runPure (mkMatchTermPure acc alts)
        lowerScrs (s.getArg 1).getSepArgs.toList #[]
      | sk =>
        if let some customFn := h.onCustom? then if let some custom ← customFn env s rest go then return custom
        if sk == ``qedStmtExpr then h.onExpr env s rest else h.onUnsupported s

@[noinline, nospecialize] def lowerPureStmtsM {m : Type → Type} {σ : Type} [Monad m] [MonadQuotation m] [MonadError m]
    [MonadLiftT CommandElabM m] (h : PureStmtHooks m σ) (env : σ) (stmts : List Syntax) : m Term := do
  lowerPureStmtsGo (← getPureQuotCtx) h env stmts

private structure PureFnEnv where
  locals    : Array String := #[]
  muts      : Array Ident := #[]
  loopMuts? : Option (Array Ident) := none
  depth     : Nat := 0

@[noinline] private def mkPureForTerm (depth : Nat) (bStx iterStx : Syntax) (usedMuts : Array Ident)
    (outerMuts? : Option (Array Ident)) (iterTerm bodyInner restTerm : Term) (invBody? : Option Term := none) : PureQuotM Term := do
  let initSt ← mkMutPack usedMuts.toList
  let stParam := if usedMuts.size == 1 then usedMuts[0]! else mkIdent (Name.mkSimple s!"_qedSt{depth}")
  let (resSt, resRet, retValId) := (mkIdent (Name.mkSimple s!"_qedLoopSt{depth}"),
    mkIdent (Name.mkSimple s!"_qedLoopRet{depth}"), mkIdent (Name.mkSimple s!"_qedRet{depth}"))
  let bodyWithUnpack ← wrapMutUnpack stParam usedMuts.toList bodyInner
  let lam ← mkForLoopLamPure s!"_qedElem{depth}" stParam bStx bodyWithUnpack
  let isRange := isRangeCallExpr iterStx
  let loopCall ← match invBody? with
    | none =>
        let loopFn := if isRange then mkCIdent `Qed.qedForRange else mkCIdent `Qed.qedForFold
        `($loopFn $iterTerm $initSt $lam)
    | some invBody =>
        let invWithUnpack ← wrapMutUnpack stParam usedMuts.toList invBody
        let invLam ← `(fun $(mkIdent `seen):ident $stParam:ident => $invWithUnpack)
        if isRange then `($(mkCIdent `Qed.qedForRangeAnn) $iterTerm $initSt $lam $invLam)
        else `($(mkCIdent `Qed.qedForFoldAnn) ($(mkCIdent `Qed.QedIterable.toList) $iterTerm) $initSt $lam $invLam)
  let someArm ← match outerMuts? with | none => pure (⟨retValId.raw⟩ : Term) | some om => `($(mkCIdent `Qed.QedLoopStep.ret) $(← mkMutPack om.toList) $retValId)
  let afterLoop ← wrapMutUnpack resSt usedMuts.toList (← `(match $resRet:ident with | Option.some $retValId:ident => $someArm | Option.none => $restTerm))
  `(let ($resSt:ident, $resRet:ident) := $loopCall; $afterLoop)

@[noinline] private def mkLoopStepPure (ctor : Name) (lm : Array Ident) (retVal? : Option Term := none) : PureQuotM Term := do
  let st ← mkMutPack lm.toList; match retVal? with | some v => `($(mkCIdent ctor) $st $v) | none => `($(mkCIdent ctor) $st)

@[noinline] private def lowerPureFnForStmt (qctx : PureQuotCtx) (e : PureFnEnv) (s : Syntax) (rest : List Syntax)
    (lowerVal : Array String → Syntax → CommandElabM Term)
    (lowerInv : Array String → Syntax → CommandElabM Term)
    (onLoopInv? : Option (Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) → CommandElabM Unit))
    (go : PureFnEnv → List Syntax → CommandElabM Term) : CommandElabM Term := do
  let bStx := s.getArg 1; let iterStx := s.getArg 3
  let invStxs := forSuiteInvs (s.getArg 5); let bodyStmts := suiteStmts (s.getArg 5)
  let bNames := collectLetBinderIds bStx
  for bNm in bNames do
    if e.muts.any (·.getId.eraseMacroScopes == bNm) then
      throwErrorAt bStx s!"`for` loop variable `{bNm}` shadows mutable variable `{bNm}`; use a different loop variable name"
  let iterTerm ← lowerVal e.locals iterStx
  let mutated := collectMutatedIds bodyStmts
  let usedMuts := e.muts.filter fun m => mutated.contains m.getId.eraseMacroScopes
  let invBody? ← if invStxs.isEmpty then pure none else do
    let invLocs := e.locals.push "seen"
    let preds ← Lang.foldlCmd invStxs (#[] : Array Term) fun acc iv => do
      if let some cb := onLoopInv? then cb (parseOptTacSeq (iv.getArg 2))
      let ps ← Lang.mapCmd (iv.getArg 1).getSepArgs (lowerInv invLocs)
      return acc ++ ps
    some <$> mkConjBody preds
  let bodyLocs := e.locals ++ bNames.map (·.toString)
  let bodyInner ← go { e with locals := bodyLocs, loopMuts? := some usedMuts, depth := e.depth + 1 } bodyStmts.toList
  let restTerm ← go { e with depth := e.depth + 1 } rest
  return qctx.runPure (mkPureForTerm e.depth bStx iterStx usedMuts e.loopMuts? iterTerm bodyInner restTerm invBody?)

private def extendPureFnEnv (e : PureFnEnv) (names : Array Name) : PureFnEnv :=
  { e with locals := e.locals ++ names.map (·.toString), muts := e.muts.filter fun m => !names.contains m.getId.eraseMacroScopes }

@[noinline] private def lowerPureFnCustomStmt (fnDesc : String) (qctx : PureQuotCtx)
    (lowerVal : Array String → Syntax → CommandElabM Term)
    (lowerInv : Array String → Syntax → CommandElabM Term)
    (onLoopInv? : Option (Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) → CommandElabM Unit))
    (e : PureFnEnv) (s : Syntax) (rest : List Syntax) (go : PureFnEnv → List Syntax → CommandElabM Term) : CommandElabM (Option Term) := do
  let lowerMutAct (act : LocalMutAction) : CommandElabM (Option Term) := do
    let newVal ← liftPureErr (applyLocalMutRhsPure qctx act (← lowerVal e.locals act.rhsSyntax))
    let cont ← go e rest
    return some (qctx.runPure (mkLetBindTerm act.targetIdent.raw none newVal cont))
  match s.getKind with
  | ``qedStmtBreak | ``qedStmtContinue =>
    let isBrk := s.getKind == ``qedStmtBreak
    let some lm := e.loopMuts? | throwErrorAt s s!"`{if isBrk then "break" else "continue"}` can only be used inside a `for` loop"
    return some (qctx.runPure (mkLoopStepPure (if isBrk then `Qed.QedLoopStep.breakLoop else `Qed.QedLoopStep.next) lm))
  | ``qedStmtLetMut =>
    let lId : Ident := ⟨s.getArg 2⟩; let nm := lId.getId.eraseMacroScopes
    if e.muts.any (·.getId.eraseMacroScopes == nm) then
      throwErrorAt lId s!"mutable variable `{nm}` is already declared in this scope; update it with `{nm} = ...`"
    let rhsT ← lowerVal e.locals (s.getArg 5)
    let cont ← go { e with locals := e.locals.push nm.toString, muts := e.muts.push lId } rest
    let ty? ← if (s.getArg 3).getNumArgs == 2 then some <$> (return (← liftPureErr (lowerQedTypePure qctx ((s.getArg 3).getArg 1) false)).1) else pure none
    return some (qctx.runPure (mkLetBindTerm lId.raw ty? rhsT cont))
  | ``qedStmtFor => some <$> lowerPureFnForStmt qctx e s rest lowerVal lowerInv onLoopInv? go
  | ``qedStmtLetElse =>
    let pat ← liftPureErr (lowerQedPatPure qctx (s.getArg 1)); let scrut ← lowerVal e.locals (s.getArg 3)
    let elseT ← go e (extractLetElseStmts s).toList; let thenT ← go (extendPureFnEnv e (collectQedPatIds (s.getArg 1))) rest
    return some (qctx.runPure `(match $(mkIdent `_qedLetElse):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT))
  | ``qedStmtAssign =>
    if let some act := tryMatchLocalMut? e.muts s then
      if s.getNumArgs > 3 && (s.getArg 3).getNumArgs > 0 then throwErrorAt ((s.getArg 3).getArg 0) s!"`predict` is not supported in pure `{fnDesc}`"
      lowerMutAct act
    else let lhsStr := stxSnippet (s.getArg 0); throwErrorAt s s!"cannot assign to `{lhsStr}` in pure `{fnDesc}`; declare local variables with `let mut {lhsStr} = ...` to mutate them"
  | ``qedStmtExpr => if let some act := tryMatchLocalMut? e.muts s then lowerMutAct act else pure none
  | _ => pure none

@[noinline] private def lowerPureFnStmtsAux (fnDesc : String)
    (lowerVal : Array String → Syntax → CommandElabM Term) (lowerGuard : Array String → Syntax → CommandElabM Term)
    (lowerInv : Array String → Syntax → CommandElabM Term)
    (onLoopInv? : Option (Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) → CommandElabM Unit))
    (allowImplicitUnit : Bool)
    (stmts : List Syntax) : CommandElabM Term := do
  let qctx ← getPureQuotCtxCmd
  let hooks : PureStmtHooks CommandElabM PureFnEnv := {
    withVal := fun e s k => do k (← lowerVal e.locals s), withGuard := fun e s k => do k (← lowerGuard e.locals s), extendLocals := extendPureFnEnv
    onEmpty := fun e => match e.loopMuts? with
      | none => if allowImplicitUnit then pure (qctx.runPure `(())) else throwError s!"missing `return` on fallthrough path of `{fnDesc}`"
      | some lm => pure (qctx.runPure (mkLoopStepPure `Qed.QedLoopStep.next lm))
    onReturn := fun e s _ => do
      let v ← if (s.getArg 1).getNumArgs == 1 then lowerVal e.locals ((s.getArg 1).getArg 0)
        else if allowImplicitUnit then pure (qctx.runPure `(()))
        else throwErrorAt s s!"`return` inside `{fnDesc}` must return a value"
      match e.loopMuts? with | none => pure v | some lm => pure (qctx.runPure (mkLoopStepPure `Qed.QedLoopStep.ret lm (some v)))
    onExpr := fun e s rest => do
      if rest.isEmpty && e.loopMuts?.isNone then lowerVal e.locals (s.getArg 0)
      else throwErrorAt s s!"unexpected bare expression statement in pure `{fnDesc}`; bind it with `let _ = ...` or return it"
    onMissingElse := fun _ _ => if allowImplicitUnit then pure (qctx.runPure `(())) else throwError s!"missing `return` on fallthrough path of `{fnDesc}`"
    onUnsupported := fun s => let sn := stxSnippet s; throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in pure `{fnDesc}`"
    letClauseErr := s!"`predict`/`catch` clauses are not supported in pure `{fnDesc}`"
    onCustom? := some (lowerPureFnCustomStmt fnDesc qctx lowerVal lowerInv onLoopInv?)
  }
  lowerPureStmtsGo qctx hooks {} stmts

@[noinline] def lowerPureFnStmts (fnDesc : String) (stmts : List Syntax)
    (lowerVal : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .val s))
    (lowerGuard : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .propGuard s))
    (lowerWithLocals? : Option (Array String → ExprMode → Syntax → CommandElabM Term) := none)
    (onLoopInv? : Option (Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) → CommandElabM Unit) := none)
    (allowImplicitUnit : Bool := false) : CommandElabM Term :=
  let defaultInv (_ : Array String) (s : Syntax) : CommandElabM Term :=
    liftMacroM (lowerSimpleQedExpr .propInv s (allowOptElse := true) (optElseFallback := `(True)))
  match lowerWithLocals? with
  | some f => lowerPureFnStmtsAux fnDesc (fun ls s => f ls .val s) (fun ls s => f ls .propGuard s) (fun ls s => f ls .propInv s) onLoopInv? allowImplicitUnit stmts
  | none   => lowerPureFnStmtsAux fnDesc (fun _ s => lowerVal s) (fun _ s => lowerGuard s) defaultInv onLoopInv? allowImplicitUnit stmts

end PureStmtLower

end Qed
