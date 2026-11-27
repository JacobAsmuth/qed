import Lean
import Qed.Lang
import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Registry

namespace Qed.Auth

section AuthParsers
open Lean Parser Qed.Lang PrettyPrinter Parenthesizer Formatter
private def opaqueP (p : Parser) : Parser := p
@[combinator_parenthesizer opaqueP] private def opaqueP.parenthesizer : Parenthesizer := pure ()
@[combinator_formatter opaqueP] private def opaqueP.formatter : Formatter := pure ()
private def kwNode (k kw : Name) (p : Parser) : Parser := node k (withPosition (atomic (identEq kw) >> p))
private def authClaimLineP : Parser :=
  node `Qed.Auth.authClaimLine (withPosition (ident >> ":" >> categoryParser `qedType 91 >> optional (checkLineEq >> "=" >> categoryParser `qedExpr 0)))
private def authClauseP : Parser :=
  node `Qed.Auth.authEnvClause (withPosition (atomic (identEq `issuer <|> identEq `audience <|> identEq `clientId <|> identEq `clientSecret) >> qedEnvRef)) <|>
  kwNode `Qed.Auth.authManagedClause `managed ("[" >> sepBy1 ident "," >> "]") <|>
  kwNode `Qed.Auth.authProvidersClause `providers ("[" >> sepBy ident "," >> "]") <|>
  kwNode `Qed.Auth.authSessionClause `session (identEq `ttl >> "=" >> numLit) <|>
  kwNode `Qed.Auth.authClaimsClause `claims (":" >> checkColGt "expected indented `claims:` fields" >> many1Indent authClaimLineP)
@[command_parser] def authCmd : Parser := opaqueP (
  node `Qed.Auth.authCmd (withPosition (atomic (identEq `auth >> ident >> ":") >> checkColGt "expected indented `auth` clauses" >> many1Indent authClauseP)))
end AuthParsers

open Lean Elab Command Qed.Lang Qed.Server

private inductive AuthClaimKind where | str | bool | nat | int | optStr deriving DecidableEq
private structure ParsedClaimDecl where
  ident      : Ident
  name       : String
  kind       : AuthClaimKind
  typeName   : String
  tyTm       : Term
  defaultStr : String
  defaultTm  : Term

@[noinline] private def claimTyDefPure : AuthClaimKind → PureQuotM (Term × Term)
  | .str => do return (← `(String), ← `((""))) | .bool => do return (← `(Bool), ← `(false))
  | .nat => do return (← `(Nat), ← `((0 : Nat))) | .int => do return (← `(Int), ← `((0 : Int)))
  | .optStr => do return (← `(Option String), ← `((Option.none : Option String)))

@[noinline] private def parseClaimDecl (stx : Syntax) : CommandElabM ParsedClaimDecl := do
  let id : Ident := ⟨stx.getArg 0⟩; let name := id.getId.eraseMacroScopes.toString
  if name == "id" then errAt id "claim name `id` is reserved for the OIDC `sub` subject identifier"
  if name == "emailVerified" then errAt id "claim name `emailVerified` is built-in on `<Auth>.User` (populated from OIDC `email_verified`)"
  let tyStx := stx.getArg 2; let tyRepr := ((tyStx.reprint.getD "").replace " " "").trimAscii.toString
  let some (kind, typeName, defStr0) := (match tyRepr with
    | "String" => some (AuthClaimKind.str, "String", "\"\"") | "Bool" => some (.bool, "Bool", "false")
    | "Nat" => some (.nat, "Nat", "0") | "Int" => some (.int, "Int", "0") | "String?" | "OptionString" => some (.optStr, "Option String", "none") | _ => none)
    | errAt tyStx s!"unsupported `auth` claim type `{tyRepr}` (supported: `String`, `Bool`, `Nat`, `Int`, `String?`)"
  let (tyTm, defTm0) ← runPQ (claimTyDefPure kind); let defOpt := stx.getArg 3
  let (defaultStr, defaultTm) ← if defOpt.getNumArgs == 2 then
      let valStx := defOpt.getArg 1; pure ((valStx.reprint.getD "").trimAscii.toString, ← liftMacroCmd (lowerSimpleQedExpr .val valStx))
    else pure (defStr0, defTm0)
  return { ident := id, name, kind, typeName, tyTm, defaultStr, defaultTm }

@[noinline] private def oidcAuthSpecToTermPure (s : OidcAuthSpec) : PureQuotM Term := do
  let provs : Array Term := s.providers.toArray.map quote
  let claimTms ← mapPQ s.claims.toArray fun cl => `({ name := $(quote cl.name), typeName := $(quote cl.typeName), defaultValue := $(quote cl.defaultValue) : Qed.Auth.AuthClaimSpec })
  `({ name := $(quote s.name), isManaged := $(quote s.isManaged), issuerEnv := $(quote s.issuerEnv), issuerDefault? := $(quote s.issuerDefault?),
      audienceEnv := $(quote s.audienceEnv), audienceDefault? := $(quote s.audienceDefault?), clientIdEnv? := $(quote s.clientIdEnv?),
      clientIdDefault? := $(quote s.clientIdDefault?), clientSecretEnv? := $(quote s.clientSecretEnv?), providers := [$[$provs],*],
      sessionTtlSec := $(quote s.sessionTtlSec), claims := [$[$claimTms],*] : Qed.Auth.OidcAuthSpec })

@[noinline] private def claimExtractTermPure (c : ParsedClaimDecl) (lookupFn : Term) : PureQuotM Term := do
  let (kLit, defTm) := (Syntax.mkStrLit c.name, c.defaultTm)
  match c.kind with
  | .str => `(($lookupFn $kLit).getD $defTm) | .bool => `(Qed.Auth.parseBoolClaim ($lookupFn $kLit) $defTm)
  | .nat => `(Qed.Auth.parseNatClaim ($lookupFn $kLit) $defTm) | .int => `(Qed.Auth.parseIntClaim ($lookupFn $kLit) $defTm)
  | .optStr => `(($lookupFn $kLit).orElse (fun _ => $defTm))

private abbrev UserFieldsAcc :=
  Array (TSyntax `Lean.Parser.Command.structSimpleBinder) × Term × Term × Term × Array (TSyntax `Lean.Parser.Term.structInstField) × Array (TSyntax `Lean.Parser.Term.structInstField)

@[noinline] private def addClaimFieldPure (lookupTm : Term) (acc : UserFieldsAcc) (clIdx : ParsedClaimDecl × Nat) : PureQuotM UserFieldsAcc := do
  let ((cl, idx), (fStxs, tTy, tVal, tPat, fInits, lInits)) := (clIdx, acc)
  let (fId, v) := (mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes, mkIdent (Name.mkSimple s!"_f{idx + 2}"))
  return (fStxs.push (← `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $(cl.tyTm) := $(cl.defaultTm))),
    ← `($tTy × $(cl.tyTm)), ← `(($tVal, u.$fId)), ← `(($tPat, $v)),
    fInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $v)),
    lInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $(← claimExtractTermPure cl lookupTm))))

@[noinline] private def mkAuthCmdsPure (authIdent : Ident) (authName : Name) (claims : Array ParsedClaimDecl)
    (secrets : Array String) (spec : OidcAuthSpec) : PureQuotM (Array (TSyntax `command)) := do
  let mkSub (leaf : Name) := mkIdentFrom authIdent (authName ++ leaf)
  let (userTyId, fromLookupId, fromClaimsId, fromCtxId, lookupTm) := (mkSub `User, mkSub `fromLookup, mkSub `fromClaims, mkSub `fromCtx, ← `(lookup))
  let initAcc : UserFieldsAcc := (
    #[← `(Lean.Parser.Command.structSimpleBinder| id : String := ""), ← `(Lean.Parser.Command.structSimpleBinder| emailVerified : Bool := false)],
    ← `(String × Bool), ← `((u.id, u.emailVerified)), ← `(($(mkIdent `_f0), $(mkIdent `_f1))),
    #[← `(Lean.Parser.Term.structInstField| id := $(mkIdent `_f0)), ← `(Lean.Parser.Term.structInstField| emailVerified := $(mkIdent `_f1))],
    #[← `(Lean.Parser.Term.structInstField| id := uid), ← `(Lean.Parser.Term.structInstField| emailVerified := Qed.Auth.parseBoolClaim (lookup "email_verified") false)])
  let (fStxs, tTy, tVal, tPat, fInits, lInits) ← foldlPQ claims.zipIdx initAcc (addClaimFieldPure lookupTm)
  let (toFn, fromFn, leftInv) := (← `(fun (u : $userTyId) => ($tVal : $tTy)), ← `(fun ($tPat : $tTy) => ({ $[$fInits:structInstField],* } : $userTyId)), ← `(fun u => by cases u; rfl))
  let mkUrlCmd (leaf : Name) (pfx : String) := `(command| def $(mkSub leaf) (returnTo : Qed.HrefTarget := Qed.HrefTarget.root) : Qed.Url :=
    (Qed.Url.parse? ($(Syntax.mkStrLit pfx) ++ Qed.Auth.urlEncodeComponent (Qed.Auth.sanitizeReturnTo (some returnTo.raw)))).getD Qed.Url.root)
  return #[
    ← `(command| structure $userTyId where $[$fStxs]* deriving Inhabited, DecidableEq, Repr),
    ← `(command| instance $(mkSub `instLawfulJsonUser):ident : Qed.LawfulJson $userTyId := Qed.LawfulJson.iso inferInstance $toFn $fromFn $leftInv),
    ← `(command| instance $(mkSub `instLawfulProtoUser):ident : Qed.LawfulProto $userTyId := Qed.LawfulProto.ofEquiv $toFn $fromFn $leftInv),
    ← noUnusedVarsPure (← `(command| private def $fromLookupId (uid : String) (lookup : String → Option String) : $userTyId := { $[$lInits:structInstField],* })),
    ← `(command| def $fromClaimsId (c : Qed.Auth.JwtClaims) : $userTyId := $fromLookupId c.sub c.claim),
    ← `(command| def $fromCtxId (ctx : Qed.Server.RequestCtx) : Option $userTyId := ctx.userId.map ($fromLookupId · ctx.claim)),
    ← `(command| theorem $(mkSub `fromCtx_userId) (ctx : Qed.Server.RequestCtx) (u : $userTyId) (h : $fromCtxId ctx = some u) : some u.id = ctx.userId := Qed.Auth.option_map_eq_some_elim h fun _ hu hf => hf ▸ hu.symm),
    ← `(command| theorem $(mkSub `fromCtx_emailVerified) (ctx : Qed.Server.RequestCtx) (u : $userTyId) (h : $fromCtxId ctx = some u) : u.emailVerified = Qed.Auth.parseBoolClaim (ctx.claim "email_verified") false := Qed.Auth.option_map_eq_some_elim h fun _ _ hf => hf ▸ rfl),
    ← mkUrlCmd `loginUrl "/_qed/auth/login?returnTo=", ← mkUrlCmd `logoutUrl "/_qed/auth/logout?returnTo=",
    ← mkMarkerThmPure (mkSub `_qed_auth_marker), ← mkStrArrDefPure (mkSub `secrets) secrets,
    ← `(command| @[noinline] def $(mkSub `config) : Qed.Auth.OidcAuthSpec := $(← oidcAuthSpecToTermPure spec))]

private structure AuthParseAcc where
  isManaged       : Bool := false
  hasExplicitOidc : Bool := false
  envRefs         : Array (Name × String × Option String) := #[]
  sessionTtlSec   : Nat := 86400
  seen            : Array Name := #[]
  providers       : Array String := #[]
  claims          : Array ParsedClaimDecl := #[]
  secrets         : Array String := #[]

@[noinline] private def parseOneAuthClause (authShort : String) (acc : AuthParseAcc) (c : Syntax) : CommandElabM AuthParseAcc := do
  let k := c.getKind; let seenKey := if k == `Qed.Auth.authEnvClause then (c.getArg 0).getId.eraseMacroScopes else k
  if acc.seen.contains seenKey then errAt c s!"duplicate clause in `auth {authShort}`"
  let acc := { acc with seen := acc.seen.push seenKey }
  let pushProvs (args : Array Syntax) := args.foldl (init := acc.providers) fun ps p => Lang.pushUnique ps p.getId.eraseMacroScopes.toString
  match k with
  | `Qed.Auth.authManagedClause =>
      if acc.hasExplicitOidc then errAt c s!"cannot combine `managed [...]` with explicit OIDC clauses in `auth {authShort}`"
      return { acc with isManaged := true, secrets := acc.secrets.push "QED_AUTH_CLIENT_SECRET", providers := pushProvs (c.getArg 2).getSepArgs }
  | `Qed.Auth.authEnvClause | `Qed.Auth.authProvidersClause =>
      let isProv := k == `Qed.Auth.authProvidersClause
      if acc.isManaged then errAt c s!"cannot combine `managed [...]` with {if isProv then "`providers`" else "explicit OIDC clauses"} in `auth {authShort}`"
      if isProv then return { acc with hasExplicitOidc := true, providers := pushProvs (c.getArg 2).getSepArgs }
      let r ← parseQedEnvRef "`auth`" (c.getArg 1)
      return { acc with hasExplicitOidc := true, envRefs := acc.envRefs.push (seenKey, r.envKey, r.default?), secrets := if r.isSecret then Lang.pushUnique acc.secrets r.envKey else acc.secrets }
  | `Qed.Auth.authSessionClause =>
      let ttl := (⟨c.getArg 3⟩ : TSyntax `num).getNat
      if ttl == 0 then errAt (c.getArg 3) s!"`auth {authShort}` session `ttl` must be positive"
      return { acc with sessionTtlSec := ttl }
  | `Qed.Auth.authClaimsClause =>
      let claims ← foldlCmd (c.getArg 2).getArgs acc.claims fun cs cl => do
        let decl ← parseClaimDecl cl
        if cs.any (·.name == decl.name) then errAt decl.ident s!"duplicate claim `{decl.name}` in `auth {authShort}`"
        return cs.push decl
      return { acc with claims }
  | _ => errAt c s!"unexpected clause in `auth {authShort}`"

@[noinline, command_elab authCmd] def elabAuthCmd : CommandElab := fun stx => do
  let authIdent : Ident := ⟨stx.getArg 1⟩; let authName := authIdent.getId.eraseMacroScopes
  let (fullAuthName, authShort) := ((← getCurrNamespace) ++ authName, authName.toString)
  let acc ← foldlCmd (stx.getArg 3).getArgs ({} : AuthParseAcc) (parseOneAuthClause authShort)
  let findEnv (k : Name) := (acc.envRefs.find? (·.1 == k)).map Prod.snd
  let (iss?, aud?, cid?, csec?) := (findEnv `issuer, findEnv `audience, findEnv `clientId, findEnv `clientSecret)
  let spec : OidcAuthSpec := {
    name := authShort, isManaged := acc.isManaged,
    issuerEnv := iss?.map (·.1) |>.getD "QED_AUTH_ISSUER", issuerDefault? := iss?.bind (·.2),
    audienceEnv := aud?.map (·.1) |>.getD "QED_AUTH_AUDIENCE", audienceDefault? := if acc.isManaged then none else aud?.elim (some authShort) (·.2),
    clientIdEnv? := some (cid?.map (·.1) |>.getD "QED_AUTH_CLIENT_ID"), clientIdDefault? := if acc.isManaged then none else cid?.elim (some authShort) (·.2),
    clientSecretEnv? := if acc.isManaged then some "QED_AUTH_CLIENT_SECRET" else csec?.map (·.1),
    providers := acc.providers.toList, sessionTtlSec := acc.sessionTtlSec,
    claims := acc.claims.toList.map fun cl => { name := cl.name, typeName := cl.typeName, defaultValue := cl.defaultStr } }
  elabPureCmds (mkAuthCmdsPure authIdent authName acc.claims acc.secrets spec)
  modifyEnv fun env => authRegistry.addEntry env { authName := fullAuthName, shortName := authShort, configConst := fullAuthName ++ `config, secrets := acc.secrets, spec }

end Qed.Auth
