import Lean
import Qed.Auth.Core
import Qed.Auth.Syntax
import Qed.Server.Core
import Qed.Server.Registry

namespace Qed.Auth

open Lean Elab Command Qed.Lang Qed.Server

/-! ## `auth` Block Elaborator
    Generates:
    - `<Auth>.User` struct (`id : String` + typed claim fields) with `LawfulJson` & `LawfulProto`
    - `<Auth>.fromClaims : JwtClaims → <Auth>.User`
    - `<Auth>.fromCtx : RequestCtx → Option <Auth>.User`
    - `<Auth>.loginUrl` / `<Auth>.logoutUrl` (client-safe URL helpers)
    - `<Auth>.config : OidcAuthSpec` & `<Auth>.secrets : Array String` (server-only, leak-gated)
    - Persistent `authRegistry` entry consumed by `server` (`use auth : ...`), `fullstack`,
      `qed dev`, and `qed_deploy.json` manifest generation. -/

private structure ParsedAuthEnvRef where
  isSecret : Bool
  envKey   : String
  default? : Option String

private def parseAuthEnvRef (stx : Syntax) : CommandElabM ParsedAuthEnvRef := do
  let kindStr := (stx.getArg 0).getId.eraseMacroScopes.toString
  let keyStr  := (⟨stx.getArg 2⟩ : TSyntax `str).getString
  let defOpt  := stx.getArg 4
  let def? : Option String :=
    if defOpt.getNumArgs == 2 then some (⟨defOpt.getArg 1⟩ : TSyntax `str).getString
    else none
  if keyStr.isEmpty then
    throwErrorAt stx "environment variable name in `auth` cannot be empty"
  return { isSecret := kindStr == "secret", envKey := keyStr, default? := def? }

private inductive AuthClaimKind where
  | str
  | bool
  | nat
  | int
  | optStr
deriving DecidableEq

private structure ParsedClaimDecl where
  ref        : Syntax
  ident      : Ident
  name       : String
  kind       : AuthClaimKind
  defaultStr : String
  defaultTm  : Term

private def parseClaimDecl (stx : Syntax) : CommandElabM ParsedClaimDecl := do
  let id : Ident := ⟨stx.getArg 0⟩
  let name := id.getId.eraseMacroScopes.toString
  if name == "id" then
    throwErrorAt id "claim name `id` is reserved for the OIDC `sub` subject identifier"
  let tyStx := stx.getArg 2
  let tyRepr := ((tyStx.reprint.getD "").replace " " "").trimAscii.toString
  let kind ← match tyRepr with
    | "String"        => pure AuthClaimKind.str
    | "Bool"          => pure AuthClaimKind.bool
    | "Nat"           => pure AuthClaimKind.nat
    | "Int"           => pure AuthClaimKind.int
    | "String?"       => pure AuthClaimKind.optStr
    | "OptionString"  => pure AuthClaimKind.optStr
    | _ => throwErrorAt tyStx s!"unsupported `auth` claim type `{tyRepr}` (supported: `String`, `Bool`, `Nat`, `Int`, `String?`)"
  let defOpt := stx.getArg 3
  let (defStr, defTm) ←
    if defOpt.getNumArgs == 2 then
      let valStx := defOpt.getArg 1
      let raw := (valStx.reprint.getD "").trimAscii.toString
      let tm ← liftMacroM <| lowerSimpleQedExpr .val valStx
      pure (raw, tm)
    else
      match kind with
      | .str    => pure ("\"\"", ← `(("")) )
      | .bool   => pure ("false", ← `(false))
      | .nat    => pure ("0", ← `((0 : Nat)))
      | .int    => pure ("0", ← `((0 : Int)))
      | .optStr => pure ("none", ← `((Option.none : Option String)))
  return { ref := stx, ident := id, name, kind, defaultStr := defStr, defaultTm := defTm }

private def claimKindTypeName : AuthClaimKind → String
  | .str    => "String"
  | .bool   => "Bool"
  | .nat    => "Nat"
  | .int    => "Int"
  | .optStr => "Option String"

private def claimKindTypeTerm : AuthClaimKind → CommandElabM Term
  | .str    => `(String)
  | .bool   => `(Bool)
  | .nat    => `(Nat)
  | .int    => `(Int)
  | .optStr => `(Option String)

private def claimExtractTerm (c : ParsedClaimDecl) (lookupFn : Term) : CommandElabM Term := do
  let kLit := Syntax.mkStrLit c.name
  let defTm := c.defaultTm
  match c.kind with
  | .str    => `(($lookupFn $kLit).getD $defTm)
  | .bool   => `(Qed.Auth.parseBoolClaim ($lookupFn $kLit) $defTm)
  | .nat    => `(Qed.Auth.parseNatClaim ($lookupFn $kLit) $defTm)
  | .int    => `(Qed.Auth.parseIntClaim ($lookupFn $kLit) $defTm)
  | .optStr => `(($lookupFn $kLit).orElse (fun _ => $defTm))

private def mkOptStrTerm : Option String → CommandElabM Term
  | none   => `(Option.none)
  | some s => let lit := Syntax.mkStrLit s; `(Option.some $lit)

@[command_elab authCmd]
def elabAuthCmd : CommandElab := fun stx => do
  let authIdent : Ident := ⟨stx.getArg 1⟩
  let authName := authIdent.getId.eraseMacroScopes
  let currNs ← getCurrNamespace
  let fullAuthName := currNs ++ authName
  let authShort := authName.toString
  let clauses := (stx.getArg 3).getArgs

  let mut issuerEnv : String := "QED_AUTH_ISSUER"
  let mut issuerDefault? : Option String := none
  let mut audienceEnv : String := "QED_AUTH_AUDIENCE"
  let mut audienceDefault? : Option String := some authShort
  let mut clientIdEnv? : Option String := some "QED_AUTH_CLIENT_ID"
  let mut clientIdDefault? : Option String := some authShort
  let mut clientSecretEnv? : Option String := none
  let mut providers : Array String := #[]
  let mut sessionTtlSec : Nat := 86400
  let mut claims : Array ParsedClaimDecl := #[]
  let mut secrets : Array String := #[]

  for c in clauses do
    let k := c.getKind
    if k == ``authIssuerClause then
      let r ← parseAuthEnvRef (c.getArg 1)
      issuerEnv := r.envKey
      issuerDefault? := r.default?
      if r.isSecret && !secrets.contains r.envKey then secrets := secrets.push r.envKey
    else if k == ``authAudienceClause then
      let r ← parseAuthEnvRef (c.getArg 1)
      audienceEnv := r.envKey
      audienceDefault? := r.default?
      if r.isSecret && !secrets.contains r.envKey then secrets := secrets.push r.envKey
    else if k == ``authClientIdClause then
      let r ← parseAuthEnvRef (c.getArg 1)
      clientIdEnv? := some r.envKey
      clientIdDefault? := r.default?
      if r.isSecret && !secrets.contains r.envKey then secrets := secrets.push r.envKey
    else if k == ``authClientSecretClause then
      let r ← parseAuthEnvRef (c.getArg 1)
      clientSecretEnv? := some r.envKey
      if r.isSecret && !secrets.contains r.envKey then secrets := secrets.push r.envKey
    else if k == ``authProvidersClause then
      for p in (c.getArg 2).getSepArgs do
        let ps := p.getId.eraseMacroScopes.toString
        if !providers.contains ps then providers := providers.push ps
    else if k == ``authSessionClause then
      let ttl := (⟨c.getArg 3⟩ : TSyntax `num).getNat
      if ttl == 0 then
        throwErrorAt (c.getArg 3) s!"`auth {authShort}` session `ttl` must be positive"
      sessionTtlSec := ttl
    else if k == ``authClaimsClause then
      for cl in (c.getArg 2).getArgs do
        let decl ← parseClaimDecl cl
        if claims.any (·.name == decl.name) then
          throwErrorAt decl.ident s!"duplicate claim `{decl.name}` in `auth {authShort}`"
        claims := claims.push decl
    else
      throwErrorAt c s!"unexpected clause in `auth {authShort}`"

  -- 1. Generate `<Auth>.User` struct with `id : String` + all declared claim fields
  let userTyId := mkIdentFrom authIdent (authName ++ `User)
  let mut fieldStxs : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) := #[]
  fieldStxs := fieldStxs.push (← `(Lean.Parser.Command.structSimpleBinder| id : String := ""))
  for cl in claims do
    let tyTm ← claimKindTypeTerm cl.kind
    let fId := mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes
    let defTm := cl.defaultTm
    fieldStxs := fieldStxs.push (← `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $tyTm := $defTm))

  elabCommand (← `(command|
    structure $userTyId where
      $[$fieldStxs]*
    deriving Inhabited, DecidableEq, Repr))

  -- 2. Generate `ToJson`, `FromJson`, `LawfulJson`, `ToProto`, `FromProto`, `LawfulProto` for `<Auth>.User`
  let mut tupleTy : Term ← `(String)
  let mut toTuple : Term ← `(u.id)
  let mut fieldIds : Array Ident := #[mkIdent `id]
  for cl in claims do
    let tyTm ← claimKindTypeTerm cl.kind
    let fId := mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes
    fieldIds := fieldIds.push fId
    tupleTy ← `($tupleTy × $tyTm)
    toTuple ← `(($toTuple, u.$fId))

  -- Build nested pair pattern for `fromTuple`
  let nFields := fieldIds.size
  let mut patVars : Array Ident := #[]
  for i in [0:nFields] do
    patVars := patVars.push (mkIdent (Name.mkSimple s!"_f{i}"))
  let mut tuplePat : Term := patVars[0]!
  for i in [1:nFields] do
    let v := patVars[i]!
    tuplePat ← `(($tuplePat, $v))
  let mut fieldInits : Array (TSyntax `Lean.Parser.Term.structInstField) := #[]
  for i in [0:nFields] do
    let fid := fieldIds[i]!
    let v := patVars[i]!
    fieldInits := fieldInits.push (← `(Lean.Parser.Term.structInstField| $fid:ident := $v))

  let toJsonInstId := mkIdentFrom authIdent (authName ++ `instToJsonUser)
  let fromJsonInstId := mkIdentFrom authIdent (authName ++ `instFromJsonUser)
  let lawfulJsonInstId := mkIdentFrom authIdent (authName ++ `instLawfulJsonUser)
  let toProtoInstId := mkIdentFrom authIdent (authName ++ `instToProtoUser)
  let fromProtoInstId := mkIdentFrom authIdent (authName ++ `instFromProtoUser)
  let lawfulProtoInstId := mkIdentFrom authIdent (authName ++ `instLawfulProtoUser)

  elabCommand (← `(command|
    instance $toJsonInstId:ident : Qed.ToJson $userTyId where
      toJson u := Qed.ToJson.toJson (α := $tupleTy) $toTuple))
  elabCommand (← `(command|
    instance $fromJsonInstId:ident : Qed.FromJson $userTyId where
      fromJson j := (Qed.FromJson.fromJson (α := $tupleTy) j).map fun $tuplePat => { $[$fieldInits:structInstField],* }))
  elabCommand (← `(command|
    instance $lawfulJsonInstId:ident : Qed.LawfulJson $userTyId where
      depthBound := Qed.LawfulJson.depthBound $tupleTy
      depth_toJson u := Qed.LawfulJson.depth_toJson ($toTuple : $tupleTy)
      fromJson_toJson u := by
        change (Qed.FromJson.fromJson (α := $tupleTy) (Qed.ToJson.toJson (α := $tupleTy) $toTuple)).map
          (fun $tuplePat => ({ $[$fieldInits:structInstField],* } : $userTyId)) = Except.ok u
        rw [Qed.LawfulJson.fromJson_toJson]
        cases u
        rfl))
  elabCommand (← `(command|
    instance $toProtoInstId:ident : Qed.ToProto $userTyId :=
      Qed.ToProto.ofEquiv (fun (u : $userTyId) => ($toTuple : $tupleTy))))
  elabCommand (← `(command|
    instance $fromProtoInstId:ident : Qed.FromProto $userTyId :=
      Qed.FromProto.ofEquiv (fun ($tuplePat : $tupleTy) => ({ $[$fieldInits:structInstField],* } : $userTyId))))
  elabCommand (← `(command|
    instance $lawfulProtoInstId:ident : Qed.LawfulProto $userTyId :=
      Qed.LawfulProto.ofEquiv
        (fun (u : $userTyId) => ($toTuple : $tupleTy))
        (fun ($tuplePat : $tupleTy) => ({ $[$fieldInits:structInstField],* } : $userTyId))
        (fun u => by cases u; rfl)))

  -- 3. Generate `<Auth>.fromClaims`, `<Auth>.fromCtx`, and `<Auth>.fromCtx_userId`
  let fromClaimsId := mkIdentFrom authIdent (authName ++ `fromClaims)
  let fromCtxId := mkIdentFrom authIdent (authName ++ `fromCtx)
  let fromCtxUserIdThm := mkIdentFrom authIdent (authName ++ `fromCtx_userId)
  let mut claimsInits : Array (TSyntax `Lean.Parser.Term.structInstField) := #[
    ← `(Lean.Parser.Term.structInstField| id := c.sub)
  ]
  let mut ctxInits : Array (TSyntax `Lean.Parser.Term.structInstField) := #[
    ← `(Lean.Parser.Term.structInstField| id := uid)
  ]
  for cl in claims do
    let fId := mkIdentFrom cl.ident cl.ident.getId.eraseMacroScopes
    let cVal ← claimExtractTerm cl (← `(c.claim))
    let rVal ← claimExtractTerm cl (← `(ctx.claim))
    claimsInits := claimsInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $cVal))
    ctxInits := ctxInits.push (← `(Lean.Parser.Term.structInstField| $fId:ident := $rVal))

  elabCommand (← `(command|
    def $fromClaimsId (c : Qed.Auth.JwtClaims) : $userTyId :=
      { $[$claimsInits:structInstField],* }))
  elabCommand (← `(command|
    def $fromCtxId (ctx : Qed.Server.RequestCtx) : Option $userTyId :=
      match ctx.userId with
      | some uid => some { $[$ctxInits:structInstField],* }
      | none     => none))
  elabCommand (← `(command|
    theorem $fromCtxUserIdThm (ctx : Qed.Server.RequestCtx) (u : $userTyId)
        (h : $fromCtxId ctx = some u) : some u.id = ctx.userId := by
      unfold $fromCtxId at h
      cases hUid : ctx.userId <;> simp [hUid] at h
      cases h; rfl))

  -- 4. Client-safe `Qed.Url` helpers (`loginUrl`, `logoutUrl`) usable directly in `<a href={...}>`
  let loginUrlId := mkIdentFrom authIdent (authName ++ `loginUrl)
  let logoutUrlId := mkIdentFrom authIdent (authName ++ `logoutUrl)
  elabCommand (← `(command|
    def $loginUrlId (returnTo : String := "/") : Qed.Url :=
      let safe := Qed.Auth.sanitizeReturnTo (some returnTo)
      (Qed.Url.parse? ("/_qed/auth/login?returnTo=" ++ Qed.Auth.urlEncodeComponent safe)).getD Qed.Url.root))
  elabCommand (← `(command|
    def $logoutUrlId (returnTo : String := "/") : Qed.Url :=
      let safe := Qed.Auth.sanitizeReturnTo (some returnTo)
      (Qed.Url.parse? ("/_qed/auth/logout?returnTo=" ++ Qed.Auth.urlEncodeComponent safe)).getD Qed.Url.root))

  -- 5. Server-only config, secrets & leak-gate marker
  let markerId := mkIdentFrom authIdent (authName ++ `_qed_auth_marker)
  elabCommand (← `(command| theorem $markerId : True := True.intro))

  let secretsId := mkIdentFrom authIdent (authName ++ `secrets)
  let secLits : Array Term := secrets.map fun s => (Syntax.mkStrLit s : Term)
  elabCommand (← `(command| def $secretsId : Array String := #[$[$secLits],*]))

  let configId := mkIdentFrom authIdent (authName ++ `config)
  let nameLit := Syntax.mkStrLit authShort
  let issEnvLit := Syntax.mkStrLit issuerEnv
  let issDefTm ← mkOptStrTerm issuerDefault?
  let audEnvLit := Syntax.mkStrLit audienceEnv
  let audDefTm ← mkOptStrTerm audienceDefault?
  let cidEnvTm ← mkOptStrTerm clientIdEnv?
  let cidDefTm ← mkOptStrTerm clientIdDefault?
  let csecEnvTm ← mkOptStrTerm clientSecretEnv?
  let provLits : Array Term := providers.map fun p => (Syntax.mkStrLit p : Term)
  let ttlLit := Syntax.mkNumLit (toString sessionTtlSec)
  let mut claimSpecTms : Array Term := #[]
  for cl in claims do
    let cn := Syntax.mkStrLit cl.name
    let ct := Syntax.mkStrLit (claimKindTypeName cl.kind)
    let cd := Syntax.mkStrLit cl.defaultStr
    claimSpecTms := claimSpecTms.push (← `({ name := $cn, typeName := $ct, defaultValue := $cd : Qed.Auth.AuthClaimSpec }))

  elabCommand (← `(command|
    def $configId : Qed.Auth.OidcAuthSpec := {
      name := $nameLit
      issuerEnv := $issEnvLit
      issuerDefault? := $issDefTm
      audienceEnv := $audEnvLit
      audienceDefault? := $audDefTm
      clientIdEnv? := $cidEnvTm
      clientIdDefault? := $cidDefTm
      clientSecretEnv? := $csecEnvTm
      providers := [$[$provLits],*]
      sessionTtlSec := $ttlLit
      claims := [$[$claimSpecTms],*]
    }))

  -- 6. Register in persistent `authRegistry`
  let claimInfos : Array AuthClaimInfo := claims.map fun cl =>
    { name := cl.name, typeName := claimKindTypeName cl.kind, defaultValue := cl.defaultStr }
  modifyEnv fun env => authRegistry.addEntry env {
    authName := fullAuthName
    shortName := authShort
    userTypeConst := fullAuthName ++ `User
    fromCtxConst := fullAuthName ++ `fromCtx
    configConst := fullAuthName ++ `config
    secrets
    issuerEnv
    issuerDefault?
    audienceEnv
    audienceDefault?
    clientIdEnv?
    clientIdDefault?
    clientSecretEnv?
    providers
    sessionTtlSec
    claims := claimInfos
  }

end Qed.Auth
