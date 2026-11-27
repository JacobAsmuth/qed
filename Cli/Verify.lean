import Cli.Common
import Std.Data.HashMap
import Std.Data.HashSet

open System (FilePath)

namespace Qed.Cli

-- Keyword/marker bitmask flags:
-- 1=interp0, 2=interp1, 4=interp2, 8=syntaxDecl, 16=nonRuleDecl, 32=declMod,
-- 64=syntaxGen, 128=localAstGen, 256=parserDef, 512=parserChoice, 1024=cmdSynKw, 2048=interpStr
private def kwFlags : Std.HashMap String UInt32 :=
  [(1,    ["s!", "f!", "dbg_trace", "println!", "m!", "throwError", "logInfo", "logWarning", "logError",
           "reportIssue!", "reportDbgIssue!", "reportEMatchIssue!", "v!"]),
   (2,    ["throwErrorAt", "logInfoAt", "logWarningAt", "logErrorAt", "throwNamedError", "logNamedWarning", "logNamedError"]),
   (4,    ["throwNamedErrorAt", "logNamedWarningAt", "logNamedErrorAt"]),
   (8,    ["syntax", "macro", "notation", "prefix", "infix", "infixl", "infixr", "postfix", "elab"]),
   (16,   ["def", "theorem", "example", "structure", "inductive", "class", "instance", "namespace", "section", "end",
           "open", "import", "variable", "universe", "axiom", "opaque", "abbrev", "where", "macro_rules", "elab_rules",
           "attribute", "private", "protected", "partial", "unsafe", "noncomputable", "mutual", "set_option", "export",
           "deriving", "initialize", "builtin_initialize", "declare_syntax_cat"]),
   (32,   ["local", "scoped", "private", "protected", "in"]),
   (64,   ["mkAtom", "addToken", "register_parser_alias"]),
   (128,  ["mkStrLit", "elabCommand", "elabCommandTopLevel", "mkStr3", "mkStr4", "mkStr5"]),
   (256,  ["symbol", "symbolNoAntiquot", "nonReservedSymbol", "nonReservedSymbolNoAntiquot",
           "unicodeSymbol", "unicodeSymbolNoAntiquot", "leading_parser", "trailing_parser"]),
   (512,  ["optional", "many", "many1", "sepBy", "sepBy1"]),
   (1024, ["syntax", "notation", "macro", "mixfix", "elab"]),
   (2048, ["interpolatedStr", "interpolatedStrNoAntiquot", "interpolatedStrFn"])
  ].foldl (init := {}) fun m (bit, ws) => ws.foldl (init := m) fun acc w => acc.insert w ((acc.getD w 0) ||| bit)

private def builtinQedFStrLine : String :=
  "@[qedExpr_parser] def qedFStr        : Parser := leading_parser:maxPrec atomic (kw \"f\" >> checkNoWsBefore \"\") >> interpolatedStr (categoryParser `qedExpr 0)"

private structure DelimBalance where
  seen : Bool := false
  cur : Int := 0
  minD : Int := 0

private def DelimBalance.step (b : DelimBalance) (openCh closeCh : Char) (s : String) : DelimBalance :=
  s.foldl (init := b) fun acc ch =>
    if ch == openCh then { acc with seen := true, cur := acc.cur + 1 }
    else if ch == closeCh then let c := acc.cur - 1; { seen := true, cur := c, minD := min acc.minD c }
    else acc

@[inline] private def DelimBalance.isUnbalanced (b : DelimBalance) (hasChoice : Bool) : Bool :=
  b.cur != 0 || b.minD < 0 || (b.seen && hasChoice)

private structure SyntaxScanInfo where
  headerTokens : Array String := #[]
  allLexerStrings : Array String := #[]
  interpCount : Nat := 0
  qedFStrInterpMatches : Nat := 0
  hasAtInterpMacro : Bool := false
  hasSyntaxGen : Bool := false
  hasUnbalancedBrace : Bool := false
  hasUnbalancedDelim : Bool := false
deriving Inhabited

private structure CustomTokenMap where
  byPair : Std.HashMap (Char × Char) (Array (Array Char × Bool)) := {}
  pairMask : Array UInt64 := #[]
  hasNonAscii : Bool := false
  hasSingleCloseGuillemet : Bool := false
  hasExactDocOpener : Bool := false
  hasCloseBraceToken : Bool := false

/-! ### Shared Lean 4 Lexical Primitives -/

private def sliceStr (cs : Array Char) (s e : Nat) : String := Id.run do
  let mut out := ""; for k in [s:e] do out := out.push cs[k]!
  return out

@[inline] private def at2 (cs : Array Char) (n i : Nat) (a b : Char) : Bool := i + 1 < n && cs[i]! == a && cs[i + 1]! == b

private partial def skipLine (cs : Array Char) (n i : Nat) : Nat :=
  if i < n && cs[i]! != '\n' then skipLine cs n (i + 1) else i

private partial def scanIdentEnd (cs : Array Char) (n i : Nat) : Nat :=
  if i < n && Lean.isIdRest cs[i]! then scanIdentEnd cs n (i + 1) else i

private partial def skipDigits (cs : Array Char) (n i : Nat) (alnum : Bool) : Nat :=
  if i < n && (if alnum then cs[i]!.isAlphanum || cs[i]! == '_' else cs[i]!.isDigit) then skipDigits cs n (i + 1) alnum else i

private partial def countHashes (cs : Array Char) (n pos k : Nat) : Nat :=
  if pos + k < n && cs[pos + k]! == '#' then countHashes cs n pos (k + 1) else k

private def rawStrHashesAt (cs : Array Char) (n pos : Nat) : Option Nat :=
  if pos >= n || cs[pos]! != 'r' then none
  else let k := countHashes cs n (pos + 1) 0; if pos + 1 + k < n && cs[pos + 1 + k]! == '"' then some k else none

@[inline] private def isRawStrStart (cs : Array Char) (n i : Nat) (prevIdent : Bool) : Bool :=
  cs[i]! == 'r' && !prevIdent && (i == 0 || (cs[i - 1]! != '.' && cs[i - 1]! != '`')) && (rawStrHashesAt cs n i).isSome

private partial def skipBlockComment (cs : Array Char) (n j ln ls depth : Nat) : Nat × Nat × Nat :=
  if j >= n || depth == 0 then (j, ln, ls)
  else if cs[j]! == '\n' then skipBlockComment cs n (j + 1) (ln + 1) (j + 1) depth
  else if at2 cs n j '/' '-' then skipBlockComment cs n (j + 2) ln ls (depth + 1)
  else if at2 cs n j '-' '/' then skipBlockComment cs n (j + 2) ln ls (depth - 1)
  else skipBlockComment cs n (j + 1) ln ls depth

@[inline] private def enterBlockComment (cs : Array Char) (n i ln ls : Nat) : Nat × Nat × Nat :=
  if i + 2 < n then
    if cs[i + 2]! == '\n' then skipBlockComment cs n (i + 3) (ln + 1) (i + 3) 1 else skipBlockComment cs n (i + 3) ln ls 1
  else (n, ln, ls)

private partial def scanRawStrLoop (cs : Array Char) (n k bs j ln ls : Nat) : Nat × Nat × Nat × Nat × Nat :=
  if j >= n then (j, bs, n, ln, ls)
  else if cs[j]! == '\n' then scanRawStrLoop cs n k bs (j + 1) (ln + 1) (j + 1)
  else if cs[j]! == '"' && j + k < n && countHashes cs n (j + 1) 0 >= k then (j + 1 + k, bs, j, ln, ls)
  else scanRawStrLoop cs n k bs (j + 1) ln ls

@[inline] private def scanRawStr (cs : Array Char) (n i ln ls : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let k := (rawStrHashesAt cs n i).getD 0; scanRawStrLoop cs n k (i + 2 + k) (i + 2 + k) ln ls

private def scanCharLit (cs : Array Char) (n i : Nat) : Nat := Id.run do
  let mut j := i + 1
  if j < n && cs[j]! == '\\' then
    j := j + 2
    while j < n && j < i + 10 && cs[j]! != '\n' do
      if cs[j]! == '\'' then return j + 1
      j := j + 1
  else if j + 1 < n && cs[j]! != '\n' && cs[j]! != '\'' && cs[j + 1]! == '\'' then return j + 2
  return i + 1

private partial def scanGuillemetLoop (cs : Array Char) (n j ln ls : Nat) : Nat × Nat × Nat × Nat :=
  if j >= n || cs[j]! == '»' then (j, if j < n then j + 1 else j, ln, ls)
  else if cs[j]! == '\n' then scanGuillemetLoop cs n (j + 1) (ln + 1) (j + 1)
  else scanGuillemetLoop cs n (j + 1) ln ls

private def matchWord (cs : Array Char) (s e : Nat) (w : String) : Bool :=
  e - s == w.length && Id.run do
    let mut k := s
    for c in w.toList do
      if cs[k]! != c then return false
      k := k + 1
    return true

private def forbiddenAt? (cs : Array Char) (s e : Nat) : Option String :=
  match e - s, cs[s]! with
  | 5,  's' => if cs[s+1]! == 'o' && cs[s+2]! == 'r' && cs[s+3]! == 'r' && cs[s+4]! == 'y' then some "sorry" else none
  | 5,  'a' => if cs[s+1]! == 'd' && cs[s+2]! == 'm' && cs[s+3]! == 'i' && cs[s+4]! == 't' then some "admit" else none
  | 7,  's' => if cs[s+1]! == 'o' && cs[s+2]! == 'r' && cs[s+3]! == 'r' && cs[s+4]! == 'y' && cs[s+5]! == 'A' && cs[s+6]! == 'x' then some "sorryAx" else none
  | 13, 'n' => if matchWord cs s e "native_decide" then some "native_decide" else none
  | _,  _   => none

private def hasForbiddenSubstr (s : String) : Bool :=
  s.contains "sorry" || s.contains "admit" || s.contains "native_decide" || s.contains "#guard"

private partial def skipSpaces (cs : Array Char) (stop i : Nat) : Nat :=
  if i < stop && (cs[i]! == ' ' || cs[i]! == '\t') then skipSpaces cs stop (i + 1) else i

private partial def decodeLeanStrLoop (cs : Array Char) (stop : Nat) (stopAtQuote : Bool) (i ls : Nat) (out : String) : String × Nat × Nat :=
  if i >= stop then (out, i, ls)
  else
    let ch := cs[i]!
    if ch == '\\' && i + 1 < stop then
      let nxt := cs[i + 1]!
      if nxt == '\n' || (nxt == '\r' && i + 2 < stop && cs[i + 2]! == '\n') then
        let i' := i + (if nxt == '\r' then 3 else 2)
        decodeLeanStrLoop cs stop stopAtQuote (skipSpaces cs stop i') i' out
      else if nxt == 'x' && i + 3 < stop then
        match Qed.unhexNat? cs[i + 2]!, Qed.unhexNat? cs[i + 3]! with
        | some a, some b => decodeLeanStrLoop cs stop stopAtQuote (i + 4) ls (out.push (Char.ofNat (a * 16 + b)))
        | _, _           => decodeLeanStrLoop cs stop stopAtQuote (i + 2) ls (out.push nxt)
      else if nxt == 'u' && i + 5 < stop then
        match Qed.unhexNat? cs[i + 2]!, Qed.unhexNat? cs[i + 3]!, Qed.unhexNat? cs[i + 4]!, Qed.unhexNat? cs[i + 5]! with
        | some a, some b, some d, some e => decodeLeanStrLoop cs stop stopAtQuote (i + 6) ls (out.push (Char.ofNat (((a * 16 + b) * 16 + d) * 16 + e)))
        | _, _, _, _                     => decodeLeanStrLoop cs stop stopAtQuote (i + 2) ls (out.push nxt)
      else decodeLeanStrLoop cs stop stopAtQuote (i + 2) ls (out.push (match nxt with | 'n' => '\n' | 'r' => '\r' | 't' => '\t' | _ => nxt))
    else if stopAtQuote && ch == '"' then (out, i + 1, ls)
    else decodeLeanStrLoop cs stop stopAtQuote (i + 1) (if ch == '\n' then i + 1 else ls) (out.push ch)

private def isLexerCustomToken (tok : String) : Bool := Id.run do
  let cs := tok.toList.toArray; let n := cs.size
  if n == 0 || tok == "/-" || (rawStrHashesAt cs n 0).isSome then return false
  let c0 := cs[0]!; if c0 == '"' || c0 == '\'' || c0 == '«' then return false
  let mut hasSpecial := false
  for k in [0:n] do
    let c := cs[k]!
    if c == '\n' || c == '\r' then return false
    if c == '"' || c == '\'' || c == '«' || c == '»' then hasSpecial := true
    else if n > 1 && (c == '{' || c == '}' || c == '(' || c == ')' || c == '[' || c == ']' || c == '⟨' || c == '⟩') then hasSpecial := true
    else if k + 1 < n && ((c == '-' && (cs[k+1]! == '-' || cs[k+1]! == '/')) || (c == '/' && cs[k+1]! == '-')) then hasSpecial := true
  if hasSpecial then return true
  let mut m := n; while m > 0 && cs[m - 1]! == '#' do m := m - 1
  return m >= 2 && cs[m - 1]! == 'r' && !Lean.isIdRest cs[m - 2]!

private def prepareCustomTokens (toks : Array String) : CustomTokenMap := Id.run do
  let mut byPair : Std.HashMap (Char × Char) (Array (Array Char × Bool)) := {}
  let mut pairMask : Array UInt64 := Array.replicate 256 0
  let mut hasNonAscii := false; let mut hasSingleCloseGuillemet := false
  let mut hasExactDocOpener := false; let mut hasCloseBraceToken := false
  for s in toks.qsort (·.length > ·.length) do
    let arr := s.toList.toArray
    if arr.size == 1 && arr[0]! == '»' then hasSingleCloseGuillemet := true
    else if arr.size >= 2 then
      let (c0, c1) := (arr[0]!, arr[1]!)
      if c0.toNat < 128 && c1.toNat < 128 then
        let idx := (c0.toNat <<< 7) ||| c1.toNat
        pairMask := pairMask.set! (idx >>> 6) (pairMask[idx >>> 6]! ||| (1 <<< (idx &&& 63).toUInt64))
      else hasNonAscii := true
      if arr.size == 3 && c0 == '/' && c1 == '-' && (arr[2]! == '-' || arr[2]! == '!') then hasExactDocOpener := true
      if c0 == '}' then hasCloseBraceToken := true
      byPair := byPair.insert (c0, c1) ((byPair.getD (c0, c1) #[]).push (arr, arr.all Lean.isIdRest))
  return { byPair, pairMask, hasNonAscii, hasSingleCloseGuillemet, hasExactDocOpener, hasCloseBraceToken }

private def matchCustomTokenAt (cs : Array Char) (n : Nat) (toks : CustomTokenMap)
    (pos : Nat) (prevIdent prevIdentEnd : Bool) (blockCloseBrace : Bool := false) : Option Nat := Id.run do
  if pos >= n then return none
  let c0 := cs[pos]!
  if toks.byPair.isEmpty then return if toks.hasSingleCloseGuillemet && c0 == '»' then some 1 else none
  if blockCloseBrace && c0 == '}' then return none
  if pos + 1 < n then
    let c1 := cs[pos + 1]!
    let mayMatch := if c0.toNat < 128 && c1.toNat < 128 then
        let idx := (c0.toNat <<< 7) ||| c1.toNat; ((toks.pairMask[idx >>> 6]! >>> (idx &&& 63).toUInt64) &&& 1) != 0
      else toks.hasNonAscii
    if mayMatch then
      if let some bucket := toks.byPair.get? (c0, c1) then
        if c0 == '.' && prevIdentEnd && (Lean.isIdFirst c1 || c1 == '«') then return none
        if c0 == '`' then
          let after := if c1 == '`' then pos + 2 else pos + 1
          if after < n && (Lean.isIdFirst cs[after]! || cs[after]! == '«') then return none
        if Lean.isIdFirst c0 && (prevIdent || (pos > 0 && (cs[pos - 1]! == '.' || cs[pos - 1]! == '`'))) then return none
        for (tok, allIdRest) in bucket do
          let m := tok.size
          if pos + m <= n then
            if Lean.isIdFirst c0 && allIdRest && pos + m < n && Lean.isIdRest cs[pos + m]! then continue
            let mut ok := true
            for k in [2:m] do if cs[pos + k]! != tok[k]! then ok := false; break
            if ok then return some m
  return if toks.hasSingleCloseGuillemet && c0 == '»' then some 1 else none

private def prevQualifierAt (cs : Array Char) (tokStart : Nat) : Option String := Id.run do
  if tokStart == 0 || cs[tokStart - 1]! != '.' then return none
  let e := tokStart - 1
  if e > 0 && cs[e - 1]! == '»' then
    let mut s := e - 1; while s > 0 && cs[s - 1]! != '«' do s := s - 1
    return if s > 0 && cs[s - 1]! == '«' then some (sliceStr cs s (e - 1)) else none
  let mut s := e; while s > 0 && Lean.isIdRest cs[s - 1]! do s := s - 1
  return if s < e then some (sliceStr cs s e) else none

@[inline] private def isDocCommentOverridden (cs : Array Char) (n i : Nat) (toks : CustomTokenMap)
    (prevIdent prevIdentEnd treatDoc : Bool) : Bool :=
  i + 2 < n && (cs[i + 2]! == '-' || cs[i + 2]! == '!') &&
  match matchCustomTokenAt cs n toks i prevIdent prevIdentEnd with | some m => m >= 4 || (treatDoc && m == 3) | none => false

private def countNewlines (cs : Array Char) (i len ls : Nat) (asLineStart : Bool) : Nat := Id.run do
  let mut cur := ls
  for k in [0:len] do if cs[i + k]! == '\n' then cur := if asLineStart then i + k + 1 else cur + 1
  return cur

/-! ### Pass A: Tail-Recursive Register-Pure Syntax & Custom Token Extractor -/

private structure ExtractCtx where
  cs : Array Char
  n : Nat
  known : CustomTokenMap
  ignoreDelim : Bool

private structure ExtractAcc where
  headerTokens : Array String := #[]
  headerSet : Std.HashSet String := {}
  allLexerStrings : Array String := #[]
  allLexerSet : Std.HashSet String := {}
  hdrB : DelimBalance := {}
  hdrK : DelimBalance := {}
  hdrP : DelimBalance := {}

private def pushDedup (raw : String) (acc : Array String) (seen : Std.HashSet String) : Array String × Std.HashSet String :=
  let t := raw.cliTrim; if !seen.contains t && isLexerCustomToken t then (acc.push t, seen.insert t) else (acc, seen)

-- `fl : UInt32`: 1=prevId, 2=prevEnd, 4=inRuleHdr, 8=atStmtStart, 16=atDeclPrefix, 32=hasAtInterp,
-- 64=hasSynGen, 128=hasLocalAst, 256=hasCmdStr, 512=hasSynKwStr, 1024=hasParserDef,
-- 2048=hasUB, 4096=hasUD, 8192=fileHasBrace, 16384=hdrHasChoice
@[inline] private def flushHdr (fl : UInt32) (acc : ExtractAcc) : UInt32 × ExtractAcc :=
  if (fl &&& 4) == 0 then (fl, acc)
  else
    let ch := (fl &&& 16384) != 0
    let ub := acc.hdrB.isUnbalanced ch; let ud := ub || acc.hdrK.isUnbalanced ch || acc.hdrP.isUnbalanced ch
    ((fl &&& ~~~16384) ||| (if ub then 2048 else 0) ||| (if ud then 4096 else 0), { acc with hdrB := {}, hdrK := {}, hdrP := {} })

private def recordStr (fl : UInt32) (acc : ExtractAcc) (s : String) : UInt32 × ExtractAcc :=
  let trimmed := s.cliTrim; let inHdr := (fl &&& 4) != 0
  let (al1, as1) := pushDedup s acc.allLexerStrings acc.allLexerSet
  let (al', as') := if trimmed.length >= 2 && trimmed.startsWith "\"" && trimmed.endsWith "\"" then
      let tcs := trimmed.toList.toArray; pushDedup (decodeLeanStrLoop tcs (tcs.size - 1) false 1 0 "").1 al1 as1
    else (al1, as1)
  let (ht', hs') := if inHdr then pushDedup s acc.headerTokens acc.headerSet else (acc.headerTokens, acc.headerSet)
  let fl' := fl ||| (if trimmed == "{" || trimmed == "}" then 8192 else 0) |||
    (if !inHdr && trimmed == "Command" then 256 else 0) ||| (if !inHdr && (kwFlags.getD trimmed 0 &&& 8) != 0 then 512 else 0)
  (fl', {
    headerTokens := ht', headerSet := hs', allLexerStrings := al', allLexerSet := as',
    hdrB := if inHdr then acc.hdrB.step '{' '}' trimmed else acc.hdrB,
    hdrK := if inHdr then acc.hdrK.step '[' ']' trimmed else acc.hdrK,
    hdrP := if inHdr then acc.hdrP.step '(' ')' trimmed else acc.hdrP })

private partial def extractLoop (ctx : ExtractCtx) (i ls ic qm attrD delimD quoteD : Nat)
    (fl : UInt32) (qp : Array Bool) (acc : ExtractAcc) : SyntaxScanInfo :=
  let (cs, n) := (ctx.cs, ctx.n)
  if i >= n then
    let (fl, acc) := flushHdr fl acc
    let hasSynGen := (fl &&& 64) != 0 || ((fl &&& 128) != 0 && (fl &&& 256) != 0 && (fl &&& 512) != 0)
    let hasPDef := (fl &&& 1024) != 0
    let ht := if hasPDef || (fl &&& 128) != 0 then
        (acc.allLexerStrings.foldl (init := (acc.headerTokens, acc.headerSet)) fun (a, s) t =>
          if s.contains t then (a, s) else (a.push t, s.insert t)).1
      else acc.headerTokens
    { headerTokens := ht, allLexerStrings := acc.allLexerStrings, interpCount := ic, qedFStrInterpMatches := qm,
      hasAtInterpMacro := (fl &&& 32) != 0, hasSyntaxGen := hasSynGen,
      hasUnbalancedBrace := (fl &&& 2048) != 0 || ((hasSynGen || hasPDef) && (fl &&& 8192) != 0),
      hasUnbalancedDelim := (fl &&& 4096) != 0 }
  else
    let c := cs[i]!; let prevId := (fl &&& 1) != 0; let prevEnd := (fl &&& 2) != 0; let fl0 := fl &&& ~~~3
    match c with
    | '\n' => extractLoop ctx (i + 1) (i + 1) ic qm attrD delimD quoteD (fl0 ||| 24) qp acc
    | ' ' | '\t' | '\r' => extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD fl0 qp acc
    | '"' =>
      let (s, ni, nls) := decodeLeanStrLoop cs n true (i + 1) ls ""; let (fl', acc') := recordStr (fl0 &&& ~~~24) acc s
      extractLoop ctx ni nls ic qm attrD delimD quoteD fl' qp acc'
    | _ =>
      if c.isWhitespace then extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD fl0 qp acc
      else if at2 cs n i '-' '-' then extractLoop ctx (skipLine cs n (i + 2)) ls ic qm attrD delimD quoteD fl0 qp acc
      else if at2 cs n i '/' '-' && !isDocCommentOverridden cs n i ctx.known prevId prevEnd false then
        let (ni, _, nls) := enterBlockComment cs n i 0 ls; extractLoop ctx ni nls ic qm attrD delimD quoteD fl0 qp acc
      else if isRawStrStart cs n i prevId then
        let (ni, bs, be, _, nls) := scanRawStr cs n i 0 ls; let (fl', acc') := recordStr (fl0 &&& ~~~24) acc (sliceStr cs bs be)
        extractLoop ctx ni nls ic qm attrD delimD quoteD fl' qp acc'
      else if let some cLen := matchCustomTokenAt cs n ctx.known i prevId prevEnd then
        extractLoop ctx (i + cLen) (countNewlines cs i cLen ls true) ic qm attrD delimD quoteD (fl0 &&& ~~~24) qp acc
      else match c with
      | '=' =>
        let fl1 := fl0 &&& ~~~24
        if i + 1 < n && cs[i + 1]! == '>' then
          if delimD == 0 || quoteD == 0 then
            let (fl2, acc') := flushHdr fl1 acc
            extractLoop ctx (i + 2) ls ic qm attrD delimD quoteD (if delimD == 0 || ctx.ignoreDelim then fl2 &&& ~~~4 else fl2) qp acc'
          else extractLoop ctx (i + 2) ls ic qm attrD delimD quoteD fl1 qp acc
        else extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD fl1 qp acc
      | '@' =>
        let isAttr := i + 1 < n && cs[i + 1]! == '[' && (fl0 &&& 16) != 0
        extractLoop ctx (i + if isAttr then 2 else 1) ls ic qm (if isAttr then 1 else attrD) (if isAttr then delimD + 1 else delimD) quoteD (fl0 &&& ~~~24) qp acc
      | '(' | '[' | '{' =>
        let isQ := c == '(' && i > 0 && cs[i - 1]! == '`'
        extractLoop ctx (i + 1) ls ic qm (if c == '[' && attrD > 0 then attrD + 1 else attrD) (delimD + 1)
          (if isQ then quoteD + 1 else quoteD) (fl0 &&& ~~~24) (if c == '(' then qp.push isQ else qp) acc
      | ')' | ']' | '}' =>
        let (qp', qd') := if c == ')' && !qp.isEmpty then (qp.pop, if qp.back! then quoteD - 1 else quoteD) else (qp, quoteD)
        let (ad', fl') := if c == ']' && attrD > 0 then (attrD - 1, if attrD == 1 then (fl0 &&& ~~~8) ||| 16 else fl0 &&& ~~~24) else (attrD, fl0 &&& ~~~24)
        extractLoop ctx (i + 1) ls ic qm ad' (if delimD > 0 then delimD - 1 else 0) qd' fl' qp' acc
      | ';' => extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD (fl0 ||| 24) qp acc
      | '\'' =>
        let ni := if !prevId && i + 1 < n && cs[i + 1]! != '\'' then scanCharLit cs n i else i + 1
        extractLoop ctx ni ls ic qm attrD delimD quoteD (fl0 &&& ~~~24) qp acc
      | '#' =>
        if (fl0 &&& 8) != 0 && (delimD == 0 || quoteD == 0) then
          let (fl2, acc') := flushHdr (fl0 &&& ~~~24) acc; extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD (fl2 &&& ~~~4) qp acc'
        else extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD (fl0 &&& ~~~24) qp acc
      | '?' | '*' | '+' | '<' =>
        let mark := (fl0 &&& 4) != 0 && (c != '<' || (i + 2 < n && cs[i + 1]! == '|' && cs[i + 2]! == '>'))
        extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD ((if mark then fl0 ||| 16384 else fl0) &&& ~~~24) qp acc
      | _ =>
        if c == '«' || Lean.isIdFirst c then
          let isGuil := c == '«'
          let (tokS, tokE, ni, nls) := if isGuil then
              let (ge, ni, _, nls) := scanGuillemetLoop cs n (i + 1) 0 ls; (i + 1, ge, ni, nls)
            else let ni := scanIdentEnd cs n (i + 1); (i, ni, ni, ls)
          let len := tokE - tokS; let flBase := (fl0 &&& ~~~24) ||| (if isGuil then 2 else 3)
          let maybeP := (fl0 &&& 1024) == 0 && len >= 7 && cs[tokE - 1]! == 'r' && cs[tokE - 7]! == '_'
          let shortSkip := !isGuil && ((len == 2 && cs[tokS + 1]! != '!' && !(c == 'i' && cs[tokS + 1]! == 'n')) || (len == 3 && c != 'd' && c != 'e'))
          if len < 2 || shortSkip || (!isGuil && !('a' ≤ c && c ≤ 'z') && !maybeP) then
            extractLoop ctx ni nls ic qm attrD delimD quoteD flBase qp acc
          else
            let tok := sliceStr cs tokS tokE; let kw := kwFlags.getD tok 0
            let (ic', qm') := if (kw &&& 2048) != 0 then
                (ic + 1, qm + (if (sliceStr cs nls (skipLine cs n nls)).cliTrim == builtinQedFStrLine then 1 else 0)) else (ic, qm)
            let fl1 := flBase ||| (if (kw &&& 6) != 0 then 32 else 0) |||
              (if (kw &&& 256) != 0 || (maybeP && tok.endsWith "_parser") then 1024 else 0) |||
              (if (flBase &&& 64) == 0 && ((kw &&& 64) != 0 || ((kw &&& 1024) != 0 && prevQualifierAt cs i == some "Command")) then 64 else 0) |||
              (if (flBase &&& 128) == 0 && ((kw &&& 128) != 0 || ((tok == "atom" || tok == "mkStrLit") && prevQualifierAt cs i == some "Syntax")) then 128 else 0)
            if isGuil || (i > 0 && (cs[i - 1]! == '.' || cs[i - 1]! == '`')) then
              extractLoop ctx ni nls ic' qm' attrD delimD quoteD fl1 qp acc
            else
              let fl2 := if (fl1 &&& 4) != 0 && (kw &&& 512) != 0 then fl1 ||| 16384 else fl1
              let (tokAtStmt, tokAtDecl) := ((fl0 &&& 8) != 0, (fl0 &&& 16) != 0)
              if quoteD > 0 && (kw &&& 8) != 0 then extractLoop ctx ni nls ic' qm' attrD delimD quoteD (fl2 ||| 64) qp acc
              else if (delimD == 0 || (quoteD == 0 && (tokAtDecl || ctx.ignoreDelim))) && (kw &&& 8) != 0 then
                let (fl3, acc') := flushHdr fl2 acc; extractLoop ctx ni nls ic' qm' attrD delimD quoteD (fl3 ||| 4) qp acc'
              else if (delimD == 0 || quoteD == 0) && tokAtStmt && (kw &&& 16) != 0 then
                let (fl3, acc') := flushHdr fl2 acc
                extractLoop ctx ni nls ic' qm' attrD delimD quoteD ((fl3 &&& ~~~4) ||| (if (kw &&& 32) != 0 then 16 else 0)) qp acc'
              else extractLoop ctx ni nls ic' qm' attrD delimD quoteD (if tok == "in" || (tokAtDecl && (kw &&& 32) != 0) then fl2 ||| 16 else fl2) qp acc
        else extractLoop ctx (i + 1) ls ic qm attrD delimD quoteD (fl0 &&& ~~~24) qp acc

/-! ### Pass B: Tail-Recursive Register-Pure Forbidden Token Scanner -/

private structure ScanCtx where
  cs : Array Char
  n : Nat
  incInterp : Bool
  toks : CustomTokenMap
  allInterp : Bool
  treatDoc : Bool
  braceMode : Nat
  allowCb : Bool

-- `ic : UInt32`: bit 0=prevInterp, bit 1=afterTrace, bit 2=inAtRefTail, bit 3=inAtField, bits 4..31=pendingAtArgs
@[inline] private def mkIc (p : UInt32 := 0) (prev after tail field : Bool := false) : UInt32 :=
  (p <<< 4) ||| (if prev then 1 else 0) ||| (if after then 2 else 0) ||| (if tail then 4 else 0) ||| (if field then 8 else 0)
@[inline] private def consumeAtArg (ic : UInt32) : UInt32 :=
  let p := ic >>> 4; if p > 0 then mkIc (p - 1) (prev := p == 1) (tail := true) else 0
@[inline] private def finishAtField (ic : UInt32) : UInt32 :=
  let p := ic >>> 4; mkIc p (prev := p == 0) (tail := true)

private def pushGroup (gs : Array (Char × UInt32)) (closeCh : Char) (ic : UInt32) (forBracket : Bool := false) : Array (Char × UInt32) :=
  let p := ic >>> 4
  if forBracket && (ic &&& 4) != 0 then gs.push (']', mkIc p (prev := p == 0) (tail := true))
  else if forBracket && (ic &&& 2) != 0 then gs.push (']', 1)
  else if p > 0 then gs.push (closeCh, mkIc (p - 1) (prev := p == 1) (tail := true))
  else if !gs.isEmpty then gs.push (closeCh, 0) else gs

private partial def scanStrLoop (cs : Array Char) (n : Nat) (interp : Bool) (k ln : Nat) : Nat × Nat × Bool :=
  if k >= n then (k, ln, false)
  else
    let ch := cs[k]!
    if ch == '\\' then scanStrLoop cs n interp (min (k + 2) n) (if k + 1 < n && cs[k + 1]! == '\n' then ln + 1 else ln)
    else if ch == '"' then (k + 1, ln, false)
    else if interp && ch == '{' then (k + 1, ln, true)
    else scanStrLoop cs n interp (k + 1) (if ch == '\n' then ln + 1 else ln)

private partial def popToSize (gs : Array (Char × UInt32)) (sz : Nat) : Array (Char × UInt32) :=
  if gs.size > sz then popToSize gs.pop sz else gs

-- `sfl : UInt32`: bit 0=prevWasIdent, bit 1=prevIdentEnd, bit 2=inInterpStr
private partial def scanForbiddenLoop (ctx : ScanCtx) (i line : Nat) (sfl ic : UInt32)
    (gs : Array (Char × UInt32)) (ib : Array (Nat × Nat)) (hits : Array (Nat × String)) : Array (Nat × String) :=
  let (cs, n, inc) := (ctx.cs, ctx.n, ctx.incInterp)
  if i >= n then hits
  else if (sfl &&& 4) != 0 then
    let (ni, nl, enterB) := scanStrLoop cs n true i line
    scanForbiddenLoop ctx ni nl 0 0 gs (if enterB then ib.push (0, gs.size) else ib) hits
  else
    let c := cs[i]!; let prevId := (sfl &&& 1) != 0; let prevEnd := (sfl &&& 2) != 0
    match c with
    | '\n' => scanForbiddenLoop ctx (i + 1) (line + 1) 0 (ic &&& ~~~4) gs ib hits
    | ' ' | '\t' | '\r' => scanForbiddenLoop ctx (i + 1) line 0 (ic &&& ~~~4) gs ib hits
    | _ =>
      if c.isWhitespace then scanForbiddenLoop ctx (i + 1) line 0 (ic &&& ~~~4) gs ib hits
      else if at2 cs n i '-' '-' then scanForbiddenLoop ctx (skipLine cs n (i + 2)) line 0 (ic &&& ~~~4) gs ib hits
      else if at2 cs n i '/' '-' && !isDocCommentOverridden cs n i ctx.toks prevId prevEnd ctx.treatDoc then
        let (ni, nl, _) := enterBlockComment cs n i line 0; scanForbiddenLoop ctx ni nl 0 (ic &&& ~~~4) gs ib hits
      else if isRawStrStart cs n i prevId then
        let (ni, _, _, nl, _) := scanRawStr cs n i line 0; scanForbiddenLoop ctx ni nl 0 0 gs ib hits
      else if let some cLen := matchCustomTokenAt cs n ctx.toks i prevId prevEnd (!ctx.allowCb && !ib.isEmpty && ib.back!.1 == 0) then
        scanForbiddenLoop ctx (i + cLen) (countNewlines cs i cLen line false) 0 (if inc then consumeAtArg ic else 0) gs ib hits
      else match c with
      | '«' =>
        let ic' := if !inc then 0 else if (ic &&& 8) != 0 then finishAtField ic else consumeAtArg ic
        let (ge, ni, nl, _) := scanGuillemetLoop cs n (i + 1) line 0
        scanForbiddenLoop ctx ni nl 2 ic' gs ib (match forbiddenAt? cs (i + 1) ge with | some f => hits.push (line, f) | none => hits)
      | '$' | '@' | '↑' | '⇑' | '↥' | '`' =>
        scanForbiddenLoop ctx (i + 1) line 0 (if inc && (ic >>> 4) > 0 then ic &&& ~~~15 else 0) gs ib hits
      | '!' | '?' =>
        let ic' := if !inc then 0
          else if c == '!' && (ic >>> 4) > 0 && (ic &&& 4) == 0 then ic &&& ~~~15
          else if (ic &&& 4) != 0 then (if (ic >>> 4) == 0 then ic ||| 1 else ic &&& ~~~1) else 0
        scanForbiddenLoop ctx (i + 1) line 0 ic' gs ib hits
      | ':' =>
        let ic' := if inc && (ic &&& 4) != 0 && i + 1 < n && (Lean.isIdFirst cs[i + 1]! || cs[i + 1]! == '«') then mkIc (ic >>> 4) (field := true) else 0
        scanForbiddenLoop ctx (i + 1) line 0 ic' gs ib hits
      | '.' =>
        let ic' := if inc && ((ic &&& 4) != 0 || (ic >>> 4) > 0) then mkIc (if (ic &&& 4) != 0 then ic >>> 4 else (ic >>> 4) - 1) (field := true) else 0
        scanForbiddenLoop ctx (i + 1) line 0 ic' gs ib hits
      | '#' =>
        if inc && i + 1 < n && cs[i + 1]! == '[' then scanForbiddenLoop ctx (i + 2) line 0 0 (pushGroup gs ']' ic) ib hits
        else if i + 6 <= n && matchWord cs i (i + 6) "#guard" && (i + 6 >= n || !Lean.isIdRest cs[i + 6]!) then
          scanForbiddenLoop ctx (i + 6) line 0 0 gs ib (hits.push (line, "#guard"))
        else scanForbiddenLoop ctx (i + 1) line 0 0 gs ib hits
      | '(' | '[' | '⟨' =>
        let gs' := if inc then pushGroup gs (if c == '(' then ')' else if c == '[' then ']' else '⟩') ic (c == '[') else gs
        scanForbiddenLoop ctx (i + 1) line 0 0 gs' ib hits
      | '{' =>
        if !ib.isEmpty then
          let (top, savedGs) := ib.back!
          if ctx.braceMode >= 2 then scanForbiddenLoop ctx (i + 1) line 0 0 gs ib hits
          else scanForbiddenLoop ctx (i + 1) line 0 0 (if inc then pushGroup gs '}' ic else gs) (if ctx.braceMode == 0 then ib.pop.push (top + 1, savedGs) else ib) hits
        else scanForbiddenLoop ctx (i + 1) line 0 0 (if inc then pushGroup gs '}' ic else gs) ib hits
      | '}' =>
        if !ib.isEmpty then
          let (top, savedGs) := ib.back!
          if ctx.braceMode >= 2 then scanForbiddenLoop ctx (i + 1) line 0 0 gs ib hits
          else if top == 0 then scanForbiddenLoop ctx (i + 1) line 4 0 (popToSize gs savedGs) ib.pop hits
          else
            let (gs', ic') := if inc && !gs.isEmpty && gs.back!.1 == '}' then (gs.pop, gs.back!.2) else (gs, 0)
            scanForbiddenLoop ctx (i + 1) line 0 ic' gs' (ib.pop.push (top - 1, savedGs)) hits
        else
          let (gs', ic') := if inc && !gs.isEmpty && gs.back!.1 == '}' then (gs.pop, gs.back!.2) else (gs, 0)
          scanForbiddenLoop ctx (i + 1) line 0 ic' gs' ib hits
      | ')' | ']' | '⟩' =>
        let (gs', ic') := if inc && !gs.isEmpty && gs.back!.1 == c then (gs.pop, gs.back!.2) else (gs, 0)
        scanForbiddenLoop ctx (i + 1) line 0 ic' gs' ib hits
      | '"' =>
        if ctx.braceMode >= 2 && !ib.isEmpty then
          let (ni, nl, _) := if ctx.braceMode == 2 then (0, 0, false) else scanStrLoop cs n false (i + 1) line
          if ctx.braceMode >= 3 && ni <= n && ni > i + 1 && cs[ni - 1]! == '"' && (ctx.braceMode == 4 || nl == line) then
            scanForbiddenLoop ctx ni nl 0 0 gs ib hits
          else scanForbiddenLoop ctx (i + 1) line 0 0 (popToSize gs ib.back!.2) ib.pop hits
        else
          let (ni, nl, enterB) := scanStrLoop cs n (inc && (ctx.allInterp || (ic &&& 1) != 0)) (i + 1) line
          scanForbiddenLoop ctx ni nl 0 0 gs (if enterB then ib.push (0, gs.size) else ib) hits
      | '\'' =>
        scanForbiddenLoop ctx (if !prevId && i + 1 < n && cs[i + 1]! != '\'' then scanCharLit cs n i else i + 1) line 0 0 gs ib hits
      | _ =>
        if inc && (ic &&& 8) != 0 && c.isDigit then scanForbiddenLoop ctx (skipDigits cs n (i + 1) false) line 0 (finishAtField ic) gs ib hits
        else if inc && (ic >>> 4) > 0 && c.isDigit then scanForbiddenLoop ctx (skipDigits cs n (i + 1) true) line 0 (consumeAtArg ic) gs ib hits
        else if Lean.isIdFirst c then
          let ni := scanIdentEnd cs n (i + 1)
          let hits' := match forbiddenAt? cs i ni with | some f => hits.push (line, f) | none => hits
          let ic' : UInt32 := if !inc then 0
            else if (ic &&& 8) != 0 then finishAtField ic
            else if (ic >>> 4) > 0 then consumeAtArg ic
            else if i >= 6 && cs[i - 1]! == '.' && matchWord cs i ni "trace" && matchWord cs (i - 6) (i - 1) "Macro" && (i == 6 || !Lean.isIdRest cs[i - 7]!) then 2
            else if i > 0 && (cs[i - 1]! == '.' || cs[i - 1]! == '`') then 0
            else if c == 'f' && ni == i + 1 && ni < n && cs[ni]! == '"' then 1
            else if ni - i >= 2 && 'a' ≤ c && c ≤ 'z' then
              let tok := sliceStr cs i ni; let kw := kwFlags.getD tok 0
              if (kw &&& 4) != 0 then mkIc 2 else if (kw &&& 2) != 0 then mkIc 1
              else mkIc (prev := (kw &&& 1) != 0) (after := tok == "trace" || tok == "trace_goal")
            else 0
          scanForbiddenLoop ctx ni line 3 ic' gs ib hits'
        else scanForbiddenLoop ctx (i + 1) line 0 0 gs ib hits

private def mergeHits (a b : Array (Nat × String)) : Array (Nat × String) :=
  b.foldl (init := a) fun acc h => if acc.contains h then acc else acc.push h

private def findForbiddenTokensWith (cs : Array Char) (toks : CustomTokenMap)
    (allStringsInterp : Bool) (unbalancedBrace : Bool := false) : Array (Nat × String) :=
  let runForDoc (treatDoc : Bool) :=
    let runs := [(false, false, 0, false), (true, allStringsInterp, 0, false)] ++
      (if toks.hasCloseBraceToken then [(true, allStringsInterp, 0, true)] else []) ++
      (if unbalancedBrace then [1, 2, 3, 4].map (true, allStringsInterp, ·, false) else [])
    runs.foldl (init := #[]) fun acc (incInterp, allInterp, braceMode, allowCb) =>
      mergeHits acc (scanForbiddenLoop { cs, n := cs.size, incInterp, toks, allInterp, treatDoc, braceMode, allowCb } 0 1 0 0 #[] #[] #[])
  let base := runForDoc false
  if toks.hasExactDocOpener then mergeHits base (runForDoc true) else base

private def isBuiltinQedFStrOnly (inRepo : Bool) (f : FilePath) (info : SyntaxScanInfo) : Bool :=
  inRepo && (f.toString == "Qed/Lang.lean" || f.toString == "./Qed/Lang.lean") && info.interpCount == 1 && info.qedFStrInterpMatches == 1

private def addAllUnique (src arr : Array String) (seen : Std.HashSet String) : Array String × Std.HashSet String × Bool :=
  src.foldl (init := (arr, seen, false)) fun (a, s, ch) t => if s.contains t then (a, s, ch) else (a.push t, s.insert t, true)

private def scanFilesForbidden (fileSrcs : Array (FilePath × String)) (inRepo : Bool) : Array (FilePath × Nat × String) := Id.run do
  if !fileSrcs.any (fun (_, s) => hasForbiddenSubstr s) then return #[]
  let filesCs := fileSrcs.map fun (f, s) => (f, s, s.toList.toArray)
  let maxIters := max 64 (max (fileSrcs.size * 8) ((fileSrcs.foldl (init := 0) fun a (_, s) => a + s.length) / 8))
  let mut known : Array String := #[]; let mut knownSet : Std.HashSet String := {}
  let mut prepared : CustomTokenMap := {}; let mut loaded : Array (FilePath × String × Array Char × SyntaxScanInfo) := #[]
  let mut projInterp := false; let mut projSynGen := false; let mut projUnbalBrace := false; let mut projUnbalDelim := false
  for _ in [0:maxIters] do
    let mut iterLoaded : Array (FilePath × String × Array Char × SyntaxScanInfo) := Array.mkEmpty filesCs.size
    let mut allHdr : Array String := #[]; let mut hdrSet : Std.HashSet String := {}
    let mut allLex : Array String := #[]; let mut lexSet : Std.HashSet String := {}
    let mut hasInterp := false; let mut hasSynGen := projSynGen; let mut hasUB := projUnbalBrace; let mut hasUD := projUnbalDelim
    for (f, src, cs) in filesCs do
      let info := extractLoop { cs, n := cs.size, known := prepared, ignoreDelim := projUnbalDelim } 0 0 0 0 0 0 0 24 #[] {}
      let (h', hs', _) := addAllUnique info.headerTokens allHdr hdrSet; allHdr := h'; hdrSet := hs'
      let (l', ls', _) := addAllUnique info.allLexerStrings allLex lexSet; allLex := l'; lexSet := ls'
      hasSynGen := hasSynGen || info.hasSyntaxGen; hasUB := hasUB || info.hasUnbalancedBrace; hasUD := hasUD || info.hasUnbalancedDelim
      if info.interpCount > 0 && !isBuiltinQedFStrOnly inRepo f info then hasInterp := true
      iterLoaded := iterLoaded.push (f, src, cs, info)
    loaded := iterLoaded; projInterp := hasInterp; projSynGen := hasSynGen; projUnbalBrace := hasUB
    let delimFlipped := !projUnbalDelim && hasUD; projUnbalDelim := hasUD
    let (k', ks', added) := addAllUnique (if hasSynGen then allLex else allHdr) known knownSet
    known := k'; knownSet := ks'
    if !added && !delimFlipped then break
    if added then prepared := prepareCustomTokens known
  let mut allHits : Array (FilePath × Nat × String) := #[]
  for (f, src, cs, info) in loaded do
    if !hasForbiddenSubstr src then continue
    let useAllInterp := projInterp || info.hasAtInterpMacro || (info.interpCount > 0 && !isBuiltinQedFStrOnly inRepo f info)
    for (ln, tok) in findForbiddenTokensWith cs prepared useAllInterp projUnbalBrace do allHits := allHits.push (f, ln, tok)
  return allHits

def findForbiddenTokens (src : String) : Array (Nat × String) :=
  (scanFilesForbidden #[(⟨""⟩, src)] false).map fun (_, ln, tok) => (ln, tok)

def grepForbidden : IO Bool := do
  let inRepo ← isInRepo
  let files := (← collect "." "lean" [".lake", ".qed", "dist", "scratch", "toolchains", "node_modules", ".git", "scripts", "Cli"]).filter
    (·.fileName != some "Cli.lean")
  let hits := scanFilesForbidden (← files.mapM fun f => return (f, ← IO.FS.readFile f)) inRepo
  for (f, ln, tok) in hits do IO.eprintln (red s!"  forbidden token `{tok}` in {f}:{ln}")
  return hits.isEmpty

/-! ### Axiom, Effect, Build-Graph, Kernel-Env & Extern Gates -/

def axiomClean (leanPath? : Option String := none) : IO Bool := do
  if !(← axiomsManifest.pathExists) then return true
  let (code, out) ← match leanPath? with
    | some lp => shOut "lean" #["--root=.", axiomsManifest.toString] #[("LEAN_PATH", some lp)]
    | none    => shOut "lake" #["env", "lean", "--root=.", axiomsManifest.toString]
  let clean := code == 0 && !["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"].any (out.contains ·)
  if !clean then IO.eprint out
  return clean

def effectsCovered : IO Bool := do
  let qh ← frameworkHome; let (qedDir, hostPath) := (qh / "Qed", qh / "runtime" / "qed_host.mjs")
  unless ← andB (← qedDir.pathExists) hostPath.pathExists do return true
  let after (marker close src : String) : List String :=
    match src.splitOn marker with | _ :: rest => rest.map fun c => (c.splitOn close).headD "" | [] => []
  let mut emitted : List String := []
  for f in ← collect qedDir "lean" do
    let src ← IO.FS.readFile f
    for marker in [".fx \"", ".fxResult \"", "Dom.effect \"", "Dom.effectResult \""] do
      for k in after marker "\"" src do if k != "" && !emitted.contains k then emitted := k :: emitted
  let handled := after "case '" "'" (← IO.FS.readFile hostPath)
  let missing := emitted.filter (!handled.contains ·)
  for k in missing do IO.eprintln (red s!"  effect kind \"{k}\" is emitted by a Cmd but no qed_host.mjs case handles it")
  return missing.isEmpty

private def pathToModule (base p : FilePath) : Option String :=
  let (s, pref) := (p.toString, base.toString ++ "/")
  let rel := if s.startsWith pref then (s.drop pref.length).toString else s
  if rel.endsWith ".lean" then some ((rel.dropEnd 5).toString.replace "/" ".") else none

def buildGraphClean : IO Bool := do
  let qh ← frameworkHome; let qedDir := qh / "Qed"
  unless ← qedDir.pathExists do return true
  let mut files ← collect qedDir "lean"
  if ← (qh / "Qed.lean").pathExists then files := files.push (qh / "Qed.lean")
  let mut adj : Std.HashMap String (Array String) := {}
  for f in files do if let some mod := pathToModule qh f then adj := adj.insert mod (parseLeanImports (← IO.FS.readFile f))
  let reaches (start target : String) : Bool := Id.run do
    let mut visited : Std.HashSet String := {}; let mut stack : Array String := #[start]
    while !stack.isEmpty do
      let cur := stack.back!; stack := stack.pop
      if !visited.contains cur then
        visited := visited.insert cur
        for dep in adj.getD cur #[] do
          if dep == target || (target == "Lean" && dep.startsWith "Lean.") then return true
          if !visited.contains dep && adj.contains dep then stack := stack.push dep
    return false
  let mut ok := true
  let pureExact := #["Qed.Html", "Qed.Render", "Qed.View.Core", "Qed.Ssr", "Qed.Resource", "Qed.Socket", "Qed.Driver", "Qed.Speculative",
    "Qed.Schema.Codec", "Qed.Runtime.AppCore", "Qed.Runtime.LocalCore", "Qed.Runtime.Cmd", "Qed.Server.Core", "Qed.Server.Eval", "Qed.Server.Http", "Qed.Server.Net",
    "Qed.Server.Prim", "Qed.Server.Native", "Qed.Server.Db.Core", "Qed.Server.Db.Runtime", "Qed.Server.Db.HttpSql", "Qed.Server.Db.PgWire"]
  for (mod, _) in adj.toList do
    if (pureExact.contains mod || #["Qed.Driver.", "Qed.Socket.", "Qed.Speculative.", "Qed.Proofs."].any (mod.startsWith ·)) && reaches mod "Lean" then
      IO.eprintln (red s!"  build-graph regression: pure module `{mod}` transitively imports `Lean`"); ok := false
  for (src, dst) in #[
      ("Qed.Style.Syntax", "Qed.Style.Proofs"), ("Qed.Component.Speculative", "Qed.Speculative.Proofs"),
      ("Qed.Server.Core", "Qed.Json.Proofs"), ("Qed.Socket.Basic", "Qed.Json.Proofs"),
      ("Qed.Server.Syntax", "Qed.Server.Core"), ("Qed.Server.FnElab", "Qed.Server.Invariant"),
      ("Qed.Server.FnElab", "Qed.Server.External"), ("Qed.Invariant.State", "Qed.Runtime.App"),
      ("Qed.Invariant.View", "Qed.Runtime.App"), ("Qed.Invariant.ForEach", "Qed.Runtime.App"),
      ("Qed.Invariant.View", "Qed.Invariant.State"), ("Qed.Schema", "Qed.Runtime.Verify"),
      ("Qed.Mapping", "Qed.Runtime.Verify"), ("Qed.Component.Rewrite", "Qed.Runtime.Verify")] do
    if adj.contains src && reaches src dst then
      IO.eprintln (red s!"  build-graph regression: `{src}` reaches forbidden dependency `{dst}`"); ok := false
  let lockPath := qh / "rust" / "qed_server" / "Cargo.lock"
  if ← lockPath.pathExists then
    let lockSrc ← IO.FS.readFile lockPath
    let pkgCount := (lockSrc.splitOn "\n[[package]]\n").length - 1 + (if lockSrc.startsWith "[[package]]\n" then 1 else 0)
    if pkgCount > 50 then IO.eprintln (red s!"  build-graph regression: rust/qed_server/Cargo.lock has {pkgCount} packages (budget ≤ 50)"); ok := false
  return ok

private def ensureQedjsEnv (q? : Option QedjsEnv) (needBuild : Bool := true) : IO (Option QedjsEnv) :=
  match q? with | some e => pure (some e) | none => resolveQedjsEnv (needBuild := needBuild)

private def addUniq (xs : Array String) (m : String) : Array String := if xs.contains m then xs else xs.push m

def kernelEnvClean (q? : Option QedjsEnv := none) (alreadyBuilt : Bool := false) (targetMod? : Option String := none) : IO Bool := do
  let (root, hasExamples) := (← webRoot, ← isInRepo)
  let some q ← ensureQedjsEnv q? (!hasExamples) | return false
  if hasExamples then
    let mods := targetMod?.elim id (fun tm ms => addUniq ms tm) (addUniq #[
      "Qed", "Qed.Driver", "Qed.Server.Native", "Qed.Cloud.Proofs", "Qed.Cloud.GcpApi", "Qed.Cloud.Executor",
      "Qed.Proofs.DomArena", "Qed.Proofs.ViewPatch", "Qed.Proofs.KeyedReconcile", "Qed.Proofs.Hydration", "Js.Backend", "Js.Proofs",
      "Examples.Counter", "Examples.Todo", "Examples.Signup", "Examples.Chat", "Examples.Bookshelf", "Examples.CloudBooks", "Examples.LiveRoom",
      "QedTests.ServerChecks", "QedTests.DbChecks", "QedTests.SpeculativeChecks", "QedTests.JsGate", "QedTests.VerificationChecks", "QedTests.CloudChecks"] root)
    q.run (#["--verify-env"] ++ mods) (quiet := true)
  else
    let jsMod ← jsRoot; let mut mods := #[root]
    if ← (modLeanPath jsMod).pathExists then mods := addUniq mods jsMod
    if let some tm := targetMod? then mods := addUniq mods tm
    if !alreadyBuilt then if (← shQuiet "lake" (#["build"] ++ mods)) != 0 then return false
    q.run (#["--verify-env", "--skip-qed"] ++ mods) (quiet := true)

def externsCovered (q? : Option QedjsEnv := none) (alreadyBuilt : Bool := false) : IO Bool := do
  let rtPath ← runtimeFile "qed_rt.mjs"
  unless ← rtPath.pathExists do return true
  let (mod, hasExamples) := (← jsRoot, ← isInRepo)
  let mut mods : Array String := #[]; let mut entries : Array String := #[]
  if ← (modLeanPath mod).pathExists then
    if !alreadyBuilt && !hasExamples then
      if mod != (← webRoot) then if (← shQuiet "lake" #["build", mod]) != 0 then return false
    let noMain := driverEntries.filter (!·.startsWith "main:")
    let (m, e) := match ← resolveAppMode mod with
      | .fullstack fs => (#[mod, "Qed.Driver"], #[s!"{fs}.clientApp", "Qed.run"] ++ noMain)
      | .ssr a        => (#[mod], driverEntries ++ #[s!"{a}:app", "Qed.App.ssrStep:ssrStep"])
      | .component a  => (#[mod, "Qed.Driver"], #["Qed.run"] ++ noMain ++ #[s!"{a}:app", "Qed.App.ssrStep:ssrStep"])
      | .raw          => (#[mod], driverEntries)
    mods := m; entries := e
  if hasExamples then
    mods := mods.push "QedTests.JsGate"
    entries := entries ++ #["JsGate.run", "JsGate.counts", "JsGate.probeCount", "JsGate.names"]
  if entries.isEmpty then return true
  let some q ← ensureQedjsEnv q? | return false
  q.run (#["--check-externs", rtPath.toString] ++ mods ++ #["--"] ++ entries) (quiet := true)

private def spawnIf (cond : Bool) (act : IO Bool) : IO (Task (Except IO.Error Bool)) := IO.asTask (if cond then act else pure true)
private def waitAllOk (tasks : List (Task (Except IO.Error Bool))) : IO Bool :=
  tasks.foldlM (init := true) fun ok t => return ((← IO.wait t).toOption.getD false) && ok

def verify (checkExterns : Bool := true) (extraLakeTargets : Array String := #[]) (targetMod? : Option String := none) : IO Bool := do
  step "verifying proofs & axioms"
  let hasExamples ← isInRepo
  let tGrep ← IO.asTask grepForbidden; let tEff ← spawnIf hasExamples effectsCovered
  let tGraph ← spawnIf hasExamples buildGraphClean; let tLp ← IO.asTask lakeEnvLeanPath
  let base ← if hasExamples then pure #["Qed", "Qed.Driver", "QedServer", "QedProofs", "JsProofs", "qedjs", "Examples", "QedTests"]
    else do let (root, jsMod) := (← webRoot, ← jsRoot); pure (if checkExterns && jsMod != root then #[root, jsMod] else #[root])
  let extra := targetMod?.elim extraLakeTargets (addUniq extraLakeTargets ·)
  if (← shLakeBuild (#["build"] ++ base ++ extra.filter (!base.contains ·))) != 0 then
    discard <| waitAllOk [tGrep, tEff, tGraph]; discard <| IO.wait tLp; return false
  let lp? := (← IO.wait tLp).toOption.join
  let q? ← match ← resolveQedjsBin (needBuild := false), lp? with
    | some bin, some leanPath => pure (some { bin, leanPath : QedjsEnv }) | _, _ => resolveQedjsEnv (needBuild := false)
  let tAxiom ← IO.asTask (axiomClean (q?.map (·.leanPath)))
  let tExt ← spawnIf checkExterns (externsCovered q? (alreadyBuilt := true))
  let okKernel ← kernelEnvClean q? (alreadyBuilt := true) (targetMod? := targetMod?)
  return (← waitAllOk [tGrep, tEff, tGraph, tAxiom, tExt]) && okKernel

def cmdCheck : IO UInt32 := do
  if ← verify (checkExterns := true) then IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

def cmdTest : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  step "building native test runner"
  let targets := #["qedtest", "qed/QedServer:static", "qed/Qed:static", "qed/libqed_server"] ++
    (if ← isInRepo then #["+QedTests.CheckHelper:c.o", "+QedTests.AuthChecks:c.o",
      "+QedTests.DbChecks:c.o", "+QedTests.WebEssentialsFixture:c.o", "+Examples.CloudBooks:c.o", "+Examples.LiveRoom:c.o"] else #[])
  if (← shLakeBuild (#["build"] ++ targets)) != 0 then IO.eprintln (red "✗ failed to build native test runner"); return 1
  step "running tests"
  let some lp ← lakeEnvLeanPath | return 1
  sh (FilePath.mk ".lake" / "build" / "bin" / "qedtest").toString #[] #[("QED_SKIP_VERIFY", some "1"), ("QED_PREBUILT", some "1"), ("LEAN_PATH", some lp)]

end Qed.Cli
