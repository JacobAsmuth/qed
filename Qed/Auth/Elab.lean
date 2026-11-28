import Lean
import Qed.Lang
import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Registry
import Qed.Verify.Core

namespace Qed.Auth

section AuthParsers
open Lean Parser Qed.Lang
private def kwNode (k kw : Name) (p : Parser) : Parser := node k (withPosition (atomic (identEq kw) >> p))
private def authClaimLineP : Parser :=
  node `Qed.Auth.authClaimLine (withPosition (ident >> ":" >> categoryParser `qedType 91 >> optional (checkLineEq >> "=" >> categoryParser `qedExpr 0)))
private def authClauseP : Parser :=
  node `Qed.Auth.authEnvClause (withPosition (atomic (identEq `issuer <|> identEq `audience <|> identEq `clientId <|> identEq `clientSecret) >> qedEnvRef)) <|>
  kwNode `Qed.Auth.authManagedClause `managed ("[" >> commaSep1 ident >> "]") <|>
  kwNode `Qed.Auth.authProvidersClause `providers ("[" >> commaSep ident >> "]") <|>
  kwNode `Qed.Auth.authSessionClause `session (identEq `ttl >> "=" >> numLit) <|>
  kwNode `Qed.Auth.authClaimsClause `claims (":" >> checkColGt "expected indented `claims:` fields" >> many1Indent authClaimLineP) <|>
  node `Qed.Auth.authInvClause (withPosition (atomic (identEq `invariant >> ident >> ":") >> sepBy1 (categoryParser `qedExpr 0) ","))
@[command_parser] def authCmd : Parser := opaqueP (
  node `Qed.Auth.authCmd (optional Command.docComment >> withPosition (atomic (identEq `auth >> ident >> ":") >> checkColGt "expected indented `auth` clauses" >> many1Indent authClauseP)))
end AuthParsers

open Lean Elab Command Qed.Lang Qed.Server

private inductive AuthClaimKind where | str | bool | nat | int | optStr
private structure ParsedClaimDecl where
  (ident : Ident) (name typeName defaultStr : String) (kind : AuthClaimKind) (tyTm defaultTm : Term)

private def claimTypeSpecs : Array (String × AuthClaimKind × String × String) := #[
  ("String", .str, "String", "\"\""), ("Bool", .bool, "Bool", "false"),
  ("Nat", .nat, "Nat", "0"), ("Int", .int, "Int", "0"),
  ("String?", .optStr, "Option String", "none")]

@[noinline] private def claimTyDefPure : AuthClaimKind → PureQuotM (Term × Term)
  | .str => pure (mkCIdent ``String, Syntax.mkStrLit "") | .bool => pure (mkCIdent ``Bool, mkCIdent ``Bool.false)
  | .nat => do return (mkCIdent ``Nat, ← mkAscribePure (Syntax.mkNumLit "0") (mkCIdent ``Nat))
  | .int => do return (mkCIdent ``Int, ← mkAscribePure (Syntax.mkNumLit "0") (mkCIdent ``Int))
  | .optStr => do let ty ← mkAppC ``Option #[mkCIdent ``String]; return (ty, ← mkAscribePure (mkCIdent ``Option.none) ty)

@[noinline] private def parseClaimDecl (stx : Syntax) : CommandElabM ParsedClaimDecl := do
  let id : Ident := ⟨stx.getArg 0⟩; let name := id.getId.eraseMacroScopes.toString
  if name == "id" then errAt id "claim name `id` is reserved for the OIDC `sub` subject identifier"
  if name == "emailVerified" then errAt id "claim name `emailVerified` is built-in on `<Auth>.User` (populated from OIDC `email_verified`)"
  let tyStx := stx.getArg 2; let tyRepr := ((tyStx.reprint.getD "").replace " " "").trimAscii.toString
  let some (_, kind, typeName, defStr0) := claimTypeSpecs.find? (·.1 == tyRepr)
    | errAt tyStx s!"unsupported `auth` claim type `{tyRepr}` (supported: `String`, `Bool`, `Nat`, `Int`, `String?`)"
  let (tyTm, defTm0) ← runPQ (claimTyDefPure kind); let defOpt := stx.getArg 3
  let (defaultStr, defaultTm) ← if defOpt.getNumArgs == 2 then
      let v := defOpt.getArg 1; pure ((v.reprint.getD "").trimAscii.toString, ← liftMacroCmd (lowerSimpleQedExpr .val v))
    else pure (defStr0, defTm0)
  return { ident := id, name, kind, typeName, tyTm, defaultStr, defaultTm }

@[noinline] private def oidcAuthSpecToTermPure (s : OidcAuthSpec) : PureQuotM Term := do
  let claimTms ← mapPQ s.claims.toArray fun cl => mkAppC ``Qed.Auth.AuthClaimSpec.mk #[quote cl.name, quote cl.typeName, quote cl.defaultValue]
  mkAppC ``Qed.Auth.OidcAuthSpec.mk #[
    quote s.name, quote s.isManaged, quote s.issuerEnv, quote s.issuerDefault?, quote s.audienceEnv, quote s.audienceDefault?,
    quote s.clientIdEnv?, quote s.clientIdDefault?, quote s.clientSecretEnv?, ← mkListLitPure (s.providers.toArray.map quote),
    quote s.sessionTtlSec, quote s.loginPath, quote s.callbackPath, quote s.logoutPath, quote s.mePath, ← mkListLitPure claimTms]

@[noinline] private def claimExtractTermPure (c : ParsedClaimDecl) (lookupFn : Term) : PureQuotM Term := do
  let lk ← mkAppTermsPure lookupFn #[Syntax.mkStrLit c.name]
  match c.kind with
  | .str => mkAppC ``Option.getD #[lk, c.defaultTm] | .bool => mkAppC ``Qed.Auth.parseBoolClaim #[lk, c.defaultTm]
  | .nat => mkAppC ``Qed.Auth.parseNatClaim #[lk, c.defaultTm] | .int => mkAppC ``Qed.Auth.parseIntClaim #[lk, c.defaultTm]
  | .optStr => mkAppC ``Option.orElse #[lk, ← `(fun _ => $(c.defaultTm))]

@[noinline] private def mkStructBinderPure (fId : Ident) (tyTm defTm : Term) : PureQuotM (TSyntax `Lean.Parser.Command.structSimpleBinder) :=
  `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $tyTm := $defTm)
@[noinline] private def mkStructFieldPure (id : Ident) (val : Term) : PureQuotM (TSyntax `Lean.Parser.Term.structInstField) :=
  `(Lean.Parser.Term.structInstField| $id:ident := $val)

@[noinline] private def mkAuthCmdsPure (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (authIdent : Ident) (authName : Name) (claims : Array ParsedClaimDecl)
    (secrets : Array String) (spec : OidcAuthSpec) : PureQuotM (Array (TSyntax `command)) := do
  let mkSub (leaf : Name) := mkIdentFrom authIdent (authName ++ leaf)
  let (userTyId, fromLookupId, fromClaimsId, fromCtxId) := (mkSub `User, mkSub `fromLookup, mkSub `fromClaims, mkSub `fromCtx)
  let (uidId, lookupId, uId, f0, f1, ctxId) := (mkIdent `uid, mkIdent `lookup, mkIdent `u, mkIdent `_f0, mkIdent `_f1, mkIdent `ctx)
  let (strTy, boolTy) := (mkCIdent ``String, mkCIdent ``Bool)
  let evExtract ← mkAppC ``Qed.Auth.parseBoolClaim #[← mkAppTermsPure lookupId #[Syntax.mkStrLit "email_verified"], mkCIdent ``Bool.false]
  let initAcc := (
    #[← mkStructBinderPure (mkIdent `id) strTy (Syntax.mkStrLit ""), ← mkStructBinderPure (mkIdent `emailVerified) boolTy (mkCIdent ``Bool.false)],
    ← mkAppC ``Prod #[strTy, boolTy], ← mkPairPure (← `(($uId).id)) (← `(($uId).emailVerified)), ← mkPairPure f0 f1,
    #[← mkStructFieldPure (mkIdent `id) f0, ← mkStructFieldPure (mkIdent `emailVerified) f1],
    #[← mkStructFieldPure (mkIdent `id) uidId, ← mkStructFieldPure (mkIdent `emailVerified) evExtract])
  let (fStxs, tTy, tVal, tPat, fInits, lInits) ← foldlPQ claims.zipIdx initAcc fun (fStxs, tTy, tVal, tPat, fInits, lInits) (cl, idx) => do
    let (fId, v) := (mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes, mkIdent (Name.mkSimple s!"_f{idx + 2}"))
    return (fStxs.push (← mkStructBinderPure fId cl.tyTm cl.defaultTm), ← mkAppC ``Prod #[tTy, cl.tyTm],
      ← mkPairPure tVal (← `(($uId).$fId)), ← mkPairPure tPat v, fInits.push (← mkStructFieldPure fId v), lInits.push (← mkStructFieldPure fId (← claimExtractTermPure cl lookupId)))
  let (toFn, fromFn, leftInv) := (← `(fun ($uId:ident : $userTyId) => ($tVal : $tTy)), ← `(fun ($tPat : $tTy) => ({ $[$fInits:structInstField],* } : $userTyId)), ← `(fun u => by cases u; rfl))
  let mkInst (leaf cls : Name) (rhs : Term) := `(command| instance $(mkSub leaf):ident : $(mkCIdent cls) $userTyId := $rhs)
  let mkUrlCmd (leaf : Name) (pfx : String) := `(command| def $(mkSub leaf) (returnTo : Qed.HrefTarget := Qed.HrefTarget.root) : Qed.Url := Qed.Auth.mkAuthActionUrl $(Syntax.mkStrLit pfx) returnTo)
  let mkCtxThm (leaf : Name) (goal pf : Term) := `(command| theorem $(mkSub leaf) ($ctxId:ident : Qed.Server.RequestCtx) ($uId:ident : $userTyId) (h : $fromCtxId $ctxId = Option.some $uId) : $goal := $pf)
  return #[
    ← `(command| $[$doc?:docComment]? structure $userTyId where $[$fStxs]* deriving Inhabited, DecidableEq, Repr),
    ← mkInst `instLawfulJsonUser ``Qed.LawfulJson (← mkAppC ``Qed.LawfulJson.iso #[mkCIdent ``inferInstance, toFn, fromFn, leftInv]),
    ← mkInst `instLawfulProtoUser ``Qed.LawfulProto (← mkAppC ``Qed.LawfulProto.ofEquiv #[toFn, fromFn, leftInv]),
    ← noUnusedVarsPure (← `(command| private def $fromLookupId ($uidId:ident : String) ($lookupId:ident : String → Option String) : $userTyId := { $[$lInits:structInstField],* })),
    ← `(command| def $fromClaimsId (c : Qed.Auth.JwtClaims) : $userTyId := $fromLookupId c.sub c.claim),
    ← `(command| def $fromCtxId ($ctxId:ident : Qed.Server.RequestCtx) : Option $userTyId := ($ctxId).userId.map ($fromLookupId · ($ctxId).claim)),
    ← mkCtxThm `fromCtx_userId (← `(Option.some ($uId).id = ($ctxId).userId)) (← `(Qed.Auth.option_map_eq_some_elim h fun _ hu hf => hf ▸ hu.symm)),
    ← mkCtxThm `fromCtx_emailVerified (← `(($uId).emailVerified = Qed.Auth.parseBoolClaim (($ctxId).claim "email_verified") false)) (← `(Qed.Auth.option_map_eq_some_elim h fun _ _ hf => hf ▸ rfl)),
    ← mkUrlCmd `loginUrl "/_qed/auth/login?returnTo=", ← mkUrlCmd `logoutUrl "/_qed/auth/logout?returnTo=",
    ← mkMarkerThmPure (mkSub `_qed_auth_marker), ← mkStrArrDefPure (mkSub `secrets) secrets,
    ← mkDefValPure (mkSub `config) #[] (mkCIdent ``Qed.Auth.OidcAuthSpec) (← oidcAuthSpecToTermPure spec)]

private structure AuthParseAcc where
  (isManaged hasExplicitOidc : Bool := false) (sessionTtlSec : Nat := 86400) (envRefs : Array (Name × String × Option String) := #[])
  (seen : Array Name := #[]) (providers secrets : Array String := #[]) (claims : Array ParsedClaimDecl := #[])
  (invs : Array (Ident × Array Syntax) := #[])

@[noinline] private def parseOneAuthClause (authShort : String) (acc : AuthParseAcc) (c : Syntax) : CommandElabM AuthParseAcc := do
  let k := c.getKind; let seenKey := if k == `Qed.Auth.authEnvClause then (c.getArg 0).getId.eraseMacroScopes else k
  let acc ← if k != `Qed.Auth.authInvClause then
      if acc.seen.contains seenKey then errAt c s!"duplicate clause in `auth {authShort}`"
      pure { acc with seen := acc.seen.push seenKey }
    else pure acc
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
  | `Qed.Auth.authInvClause =>
      let invId : Ident := ⟨c.getArg 1⟩; let leaf := invId.getId.eraseMacroScopes
      if [`User, `config, `secrets, `fromClaims, `fromCtx, `loginUrl, `logoutUrl].contains leaf then
        errAt invId s!"invariant name `{leaf}` is reserved in `auth {authShort}`"
      if acc.invs.any (·.1.getId.eraseMacroScopes == leaf) then errAt invId s!"duplicate invariant `{leaf}` in `auth {authShort}`"
      return { acc with invs := acc.invs.push (invId, (c.getArg 3).getSepArgs) }
  | _ => errAt c s!"unexpected clause in `auth {authShort}`"

@[noinline, command_elab authCmd] def elabAuthCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let authIdent : Ident := ⟨stx.getArg 2⟩; let authName := authIdent.getId.eraseMacroScopes
  let (fullAuthName, authShort) := ((← getCurrNamespace) ++ authName, authName.toString)
  let acc ← foldlCmd (stx.getArg 4).getArgs ({} : AuthParseAcc) (parseOneAuthClause authShort)
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
  elabPureCmds (mkAuthCmdsPure doc? authIdent authName acc.claims acc.secrets spec)
  if !acc.invs.isEmpty then
    let (cfgId, secId) : Term × Term := (mkCIdent (fullAuthName ++ `config), mkCIdent (fullAuthName ++ `secrets))
    let (provT, ttlT, mgdT, clmT) ← runPQ do
      return (← `(($cfgId).providers), ← `(($cfgId).sessionTtlSec), ← `(($cfgId).isManaged), ← `(($cfgId).claims))
    let aliases : Array (String × Term) := #[
      ("secrets", secId), ("config", cfgId), ("providers", provT),
      ("session_ttl", ttlT), ("is_managed", mgdT), ("claims", clmT)]
    let unfolds := #[fullAuthName ++ `secrets, fullAuthName ++ `config]
    foldlCmd acc.invs () fun () (invId, exprs) =>
      Qed.Verify.Core.elabStaticMetaInv authShort (fullAuthName ++ invId.getId.eraseMacroScopes) aliases unfolds invId exprs
  modifyEnv fun env => authRegistry.addEntry env { authName := fullAuthName, shortName := authShort, configConst := fullAuthName ++ `config, secrets := acc.secrets, spec }

end Qed.Auth
