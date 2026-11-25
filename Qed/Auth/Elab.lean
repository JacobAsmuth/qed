import Lean
import Qed.Auth.Core
import Qed.Auth.Syntax
import Qed.Server.Core
import Qed.Server.Registry

namespace Qed.Auth

open Lean Elab Command Qed.Lang Qed.Server

/-! ## `auth` Block Elaborator -/

private inductive AuthClaimKind where | str | bool | nat | int | optStr
deriving DecidableEq

private structure ParsedClaimDecl where
  ident : Ident
  name : String
  kind : AuthClaimKind
  typeName : String
  tyTm : Term
  defaultStr : String
  defaultTm : Term

private def parseClaimDecl (stx : Syntax) : CommandElabM ParsedClaimDecl := do
  let id : Ident := ⟨stx.getArg 0⟩; let name := id.getId.eraseMacroScopes.toString
  if name == "id" then throwErrorAt id "claim name `id` is reserved for the OIDC `sub` subject identifier"
  let tyStx := stx.getArg 2; let tyRepr := ((tyStx.reprint.getD "").replace " " "").trimAscii.toString
  let (kind, typeName, tyTm, defStr0, defTm0) ← match tyRepr with
    | "String" => pure (.str, "String", ← `(String), "\"\"", ← `(("")))
    | "Bool"   => pure (.bool, "Bool", ← `(Bool), "false", ← `(false))
    | "Nat"    => pure (.nat, "Nat", ← `(Nat), "0", ← `((0 : Nat)))
    | "Int"    => pure (.int, "Int", ← `(Int), "0", ← `((0 : Int)))
    | "String?" | "OptionString" => pure (.optStr, "Option String", ← `(Option String), "none", ← `((Option.none : Option String)))
    | _ => throwErrorAt tyStx s!"unsupported `auth` claim type `{tyRepr}` (supported: `String`, `Bool`, `Nat`, `Int`, `String?`)"
  let defOpt := stx.getArg 3
  let (defaultStr, defaultTm) ← if defOpt.getNumArgs == 2 then
      let valStx := defOpt.getArg 1; pure ((valStx.reprint.getD "").trimAscii.toString, ← liftMacroM <| lowerSimpleQedExpr .val valStx)
    else pure (defStr0, defTm0)
  return { ident := id, name, kind, typeName, tyTm, defaultStr, defaultTm }

private def claimExtractTerm (c : ParsedClaimDecl) (lookupFn : Term) : CommandElabM Term := do
  let (kLit, defTm) := (Syntax.mkStrLit c.name, c.defaultTm)
  match c.kind with
  | .str => `(($lookupFn $kLit).getD $defTm) | .bool => `(Qed.Auth.parseBoolClaim ($lookupFn $kLit) $defTm)
  | .nat => `(Qed.Auth.parseNatClaim ($lookupFn $kLit) $defTm) | .int => `(Qed.Auth.parseIntClaim ($lookupFn $kLit) $defTm)
  | .optStr => `(($lookupFn $kLit).orElse (fun _ => $defTm))

private def oidcAuthSpecToTerm (s : OidcAuthSpec) : CommandElabM Term := do
  let provs : Array Term := s.providers.toArray.map quote
  let claimTms ← s.claims.toArray.mapM fun cl =>
    `({ name := $(quote cl.name), typeName := $(quote cl.typeName), defaultValue := $(quote cl.defaultValue) : Qed.Auth.AuthClaimSpec })
  `({ name := $(quote s.name), isManaged := $(quote s.isManaged), issuerEnv := $(quote s.issuerEnv), issuerDefault? := $(quote s.issuerDefault?),
      audienceEnv := $(quote s.audienceEnv), audienceDefault? := $(quote s.audienceDefault?), clientIdEnv? := $(quote s.clientIdEnv?),
      clientIdDefault? := $(quote s.clientIdDefault?), clientSecretEnv? := $(quote s.clientSecretEnv?), providers := [$[$provs],*],
      sessionTtlSec := $(quote s.sessionTtlSec), claims := [$[$claimTms],*] : Qed.Auth.OidcAuthSpec })

@[command_elab authCmd]
def elabAuthCmd : CommandElab := fun stx => do
  let authIdent : Ident := ⟨stx.getArg 1⟩; let authName := authIdent.getId.eraseMacroScopes
  let (fullAuthName, authShort) := ((← getCurrNamespace) ++ authName, authName.toString)
  let mkSub (leaf : Name) := mkIdentFrom authIdent (authName ++ leaf)
  let mut isManaged := false; let mut hasExplicitOidc := false; let mut seen : Array Name := #[]
  let mut issuerEnv := "QED_AUTH_ISSUER"; let mut issuerDefault? : Option String := none
  let mut audienceEnv := "QED_AUTH_AUDIENCE"; let mut audienceDefault? : Option String := some authShort
  let mut clientIdEnv? : Option String := some "QED_AUTH_CLIENT_ID"; let mut clientIdDefault? : Option String := some authShort
  let mut clientSecretEnv? : Option String := none; let mut providers : Array String := #[]
  let mut sessionTtlSec : Nat := 86400; let mut claims : Array ParsedClaimDecl := #[]; let mut secrets : Array String := #[]
  let pushProviders (args : Array Syntax) (cur : Array String) :=
    args.foldl (init := cur) fun acc p => Lang.pushUnique acc p.getId.eraseMacroScopes.toString
  for c in (stx.getArg 3).getArgs do
    let k := c.getKind; let seenKey := if k == ``authEnvClause then (c.getArg 0).getId.eraseMacroScopes else k
    if seen.contains seenKey then throwErrorAt c s!"duplicate clause in `auth {authShort}`"
    seen := seen.push seenKey
    if k == ``authManagedClause then
      if hasExplicitOidc then throwErrorAt c s!"cannot combine `managed [...]` with explicit OIDC/provider clauses in `auth {authShort}`"
      isManaged := true; audienceDefault? := none; clientIdDefault? := none; clientSecretEnv? := some "QED_AUTH_CLIENT_SECRET"
      secrets := secrets.push "QED_AUTH_CLIENT_SECRET"; providers := pushProviders (c.getArg 2).getSepArgs providers
    else if k == ``authEnvClause then
      if isManaged then throwErrorAt c s!"cannot combine `managed [...]` with explicit OIDC clauses in `auth {authShort}`"
      hasExplicitOidc := true; let r ← parseQedEnvRef "`auth`" (c.getArg 1)
      if r.isSecret then secrets := Lang.pushUnique secrets r.envKey
      match seenKey with
      | `issuer => issuerEnv := r.envKey; issuerDefault? := r.default? | `audience => audienceEnv := r.envKey; audienceDefault? := r.default?
      | `clientId => clientIdEnv? := some r.envKey; clientIdDefault? := r.default? | _ => clientSecretEnv? := some r.envKey
    else if k == ``authProvidersClause then
      if isManaged then throwErrorAt c s!"cannot combine `managed [...]` with `providers` in `auth {authShort}`"
      hasExplicitOidc := true; providers := pushProviders (c.getArg 2).getSepArgs providers
    else if k == ``authSessionClause then
      let ttl := (⟨c.getArg 3⟩ : TSyntax `num).getNat
      if ttl == 0 then throwErrorAt (c.getArg 3) s!"`auth {authShort}` session `ttl` must be positive"
      sessionTtlSec := ttl
    else if k == ``authClaimsClause then
      for cl in (c.getArg 2).getArgs do
        let decl ← parseClaimDecl cl
        if claims.any (·.name == decl.name) then throwErrorAt decl.ident s!"duplicate claim `{decl.name}` in `auth {authShort}`"
        claims := claims.push decl
    else throwErrorAt c s!"unexpected clause in `auth {authShort}`"

  let userTyId := mkSub `User
  let mut fieldStxs : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) := #[← `(Lean.Parser.Command.structSimpleBinder| id : String := "")]
  let mut tupleTy : Term ← `(String); let mut toTuple : Term ← `(u.id); let mut tuplePat : Term := mkIdent `_f0
  let mut fieldInits : Array (TSyntax `Lean.Parser.Term.structInstField) := #[← `(Lean.Parser.Term.structInstField| id := $(mkIdent `_f0))]
  let mut lookupInits : Array (TSyntax `Lean.Parser.Term.structInstField) := #[← `(Lean.Parser.Term.structInstField| id := uid)]
  for (cl, idx) in claims.zipIdx do
    let (fId, v) := (mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes, mkIdent (Name.mkSimple s!"_f{idx + 1}"))
    fieldStxs := fieldStxs.push (← `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $(cl.tyTm) := $(cl.defaultTm)))
    tupleTy ← `($tupleTy × $(cl.tyTm)); toTuple ← `(($toTuple, u.$fId)); tuplePat ← `(($tuplePat, $v))
    fieldInits := fieldInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $v))
    lookupInits := lookupInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $(← claimExtractTerm cl (← `(lookup)))))
  let (toFn, fromFn, leftInv) := (← `(fun (u : $userTyId) => ($toTuple : $tupleTy)), ← `(fun ($tuplePat : $tupleTy) => ({ $[$fieldInits:structInstField],* } : $userTyId)), ← `(fun u => by cases u; rfl))
  let (fromLookupId, fromClaimsId, fromCtxId) := (mkSub `fromLookup, mkSub `fromClaims, mkSub `fromCtx)
  elabCommand (← `(command| structure $userTyId where $[$fieldStxs]* deriving Inhabited, DecidableEq, Repr))
  elabCommand (← `(command| instance $(mkSub `instLawfulJsonUser):ident : Qed.LawfulJson $userTyId := Qed.LawfulJson.iso inferInstance $toFn $fromFn $leftInv))
  elabCommand (← `(command| instance $(mkSub `instLawfulProtoUser):ident : Qed.LawfulProto $userTyId := Qed.LawfulProto.ofEquiv $toFn $fromFn $leftInv))
  elabCommand (← `(command| set_option linter.unusedVariables false in
    private def $fromLookupId (uid : String) (lookup : String → Option String) : $userTyId := { $[$lookupInits:structInstField],* }))
  elabCommand (← `(command| def $fromClaimsId (c : Qed.Auth.JwtClaims) : $userTyId := $fromLookupId c.sub c.claim))
  elabCommand (← `(command| def $fromCtxId (ctx : Qed.Server.RequestCtx) : Option $userTyId := ctx.userId.map ($fromLookupId · ctx.claim)))
  elabCommand (← `(command| theorem $(mkSub `fromCtx_userId) (ctx : Qed.Server.RequestCtx) (u : $userTyId) (h : $fromCtxId ctx = some u) : some u.id = ctx.userId := by
    unfold $fromCtxId at h; cases hUid : ctx.userId <;> simp [hUid] at h; cases h; rfl))
  for (fnLeaf, pfx) in [(`loginUrl, "/_qed/auth/login?returnTo="), (`logoutUrl, "/_qed/auth/logout?returnTo=")] do
    elabCommand (← `(command| def $(mkSub fnLeaf) (returnTo : Qed.HrefTarget := Qed.HrefTarget.root) : Qed.Url :=
      (Qed.Url.parse? ($(Syntax.mkStrLit pfx) ++ Qed.Auth.urlEncodeComponent (Qed.Auth.sanitizeReturnTo (some returnTo.raw)))).getD Qed.Url.root))
  let secLits : Array Term := secrets.map (Syntax.mkStrLit ·)
  let spec : OidcAuthSpec := {
    name := authShort, isManaged, issuerEnv, issuerDefault?, audienceEnv, audienceDefault?,
    clientIdEnv?, clientIdDefault?, clientSecretEnv?, providers := providers.toList, sessionTtlSec,
    claims := claims.toList.map fun cl => { name := cl.name, typeName := cl.typeName, defaultValue := cl.defaultStr } }
  elabCommand (← `(command| theorem $(mkSub `_qed_auth_marker) : True := True.intro))
  elabCommand (← `(command| @[noinline] def $(mkSub `secrets) : Array String := #[$[$secLits],*]))
  elabCommand (← `(command| @[noinline] def $(mkSub `config) : Qed.Auth.OidcAuthSpec := $(← oidcAuthSpecToTerm spec)))
  modifyEnv fun env => authRegistry.addEntry env { authName := fullAuthName, shortName := authShort, configConst := fullAuthName ++ `config, secrets, spec }

end Qed.Auth
