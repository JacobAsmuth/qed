import Qed.Cloud.Executor
import Qed.Cloud.Protocol
import Qed.Server.Http
import Qed.Auth.Oidc
import Cli.Verify
import Cli.Build
import Cli.Cloud
import QedTests.Native.Harness
open Qed Qed.Cloud Qed.Cloud.Protocol QedTests.Native

namespace QedTests.Native.CloudDeploy

private def forbiddenTokenCases : Array (String × Array (Nat × String)) :=
  let hit (n : Nat) (tok := "sorry") (xs : Array String) := xs.map fun s => (s, #[(n, tok)])
  let ls (s : String) : Array String := (s.splitOn "\n").toArray
  let ss (s : String) : Array String := (s.splitOn "\n§§\n").toArray
  let ps (s : String) : Array (String × String) := (ls s).map fun l => match l.splitOn "§" with | [a, b] => (a, b) | _ => (l, "")
  let mk (tpl : String) (a : String) (b := "") := ((tpl.replace "§A" a).replace "§B" b)
  hit 1 "sorry" (
    (ls "stx[0]\nx.1\n(x).1\nSyntax.«missing»\n.«missing»").map (mk "def t := throwErrorAt §A \"{(sorry : String)}\"\n") ++
    (ls ".missing\nrs[0]!").map (mk "def f := throwErrorAt §A \"{(sorry : String)}\"\n") ++
    (ls "@ref\n{ raw := ref : TSyntax `term }\n⟨ref⟩\n#[ref]").map (mk "def f (ref : Syntax) := throwErrorAt §A \"{(sorry : Nat)}\"\n") ++
    (ls "'a'\n\"a\"\ns!\"a\"\n∅\n?_").map (mk "def p := throwErrorAt §A \"{(sorry : Nat)}\"\n") ++
    (ls "s! \ns! /- c -/ \ndbg_trace \ntrace[Elab.step] ").map (mk "def t := §A\"{(by sorry : Nat)}\"\n") ++
    (ls "lean.unknownIdentifier\n«lean».«unknownIdentifier»").map (mk "def t := throwNamedError §A \"{(sorry : String)}\"\n") ++
    (ps "(t : Syntax)§↑t\n§`(foo)\n(x : Bool)§!x").map (fun (a, b) => mk "def f §A := throwErrorAt §B \"{(sorry : Nat)}\"\n" a b) ++
    (ss "def t := throwErrorAt Syntax.missing \"err {(by sorry : Nat)}\"\n\n§§\ndef p : CoreM Unit := (throwErrorAt · \"{(sorry : Nat)}\") Syntax.missing\n\n§§\ndef f : Std.Format := f!\"{(sorry : Nat)}\"\n\n§§\ndef h : String := s!\"{{ x := (by sorry : Nat) : Box }}\"\n\n§§\ndef f : IO Unit := println! \"{(sorry : String)}\"\n\n§§\ndef f : Lean.MacroM Unit := Macro.trace[a] \"{(sorry : String)}\"\n\n§§\ndef w := «sorry»\n\n§§\ndef q := f\"{qedRaw%((sorry : String))}\"\n\n§§\ndef bad1 (trace : Array String) : String := trace[if s!\"{(sorry : Nat)}\" == \"\" then 0 else 0]!\n\n§§\ndef bad2 (logInfoAt : String → String) : String := logInfoAt (s!\"{(sorry : Nat)}\")\n\n§§\ndef t := throwNamedErrorAt Syntax.«missing» lean.unknownIdentifier \"{(sorry : String)}\"\n\n§§\nmacro \"evil\" stx:term : term => `(throwErrorAt $stx:term \"{(sorry : String)}\")\n\n§§\ndef x : String := s!\"{\"\"++r\"\\\"++(sorry : String)++\"\"}\"\n")) ++
  hit 1 "admit" (
    (ls "t§stx[0] lean.unknownIdentifier§String\nf§.missing foo§String\nf (ref : Syntax)§@ref lean.unknownIdentifier§Nat").map
      (fun l => match l.splitOn "§" with | [a, x, y] => ((mk "def §A := throwNamedErrorAt §B \"{(admit : §C)}\"\n" a x).replace "§C" y) | _ => "") ++
    (ss "def t := m! \"{(by admit : Nat)}\"\n\n§§\ndef t := logInfoAt (← getRef) \"err {(by admit : Nat)}\"\n\n§§\nmacro \"evil2\" stx:term : term => `(throwErrorAt $stx \"{(admit : String)}\")\n")) ++
  hit 2 "sorry" (
    (ps "--§x--\n/-§x/-\n\\\"§x\"\n«§x«\n\\x2d\\x2d§x--").map (fun (a, b) => mk "notation \"x§A\" => 0\ndef a : Nat := §B + sorry\n" a b) ++
    (ps "r\\\"§f1 : Nat := (r\"hi\").length\nr#\\\"§f1 : Nat := (r#\"hi\"#).length\n.x\\\"§f1 : Nat := a.x\"hi\"\n.x\\\"§f1 : Nat := «a».x\"hi\"\nx\\\"§f2 : Nat := `x\"hi\"\n`x\\\"§f3 : Nat := `x\"hi\"\n}x§f : String := s!\"{1}x\"").map (fun (a, b) => mk "syntax \"§A\" : term\ndef §B + sorry -- \"\n" a b) ++
    (ls "x?'\nα'").map (mk "def t := §A '\"'\ntheorem e : False := sorry\n") ++ (ls "/-\n\"").map (mk "def «§A» := 1\ntheorem bad : False := sorry\n") ++
    (ls "/--\n/-!").map (mk "macro \"§A\" t:term \"-/\" : term => `($t)\ndef p : Nat := §A sorry -/\n") ++
    (ps "unbal\" \"}§unbal }\n}a§}a").map (fun (a, b) => mk "macro \"§A\" : term => `(0)\ndef f : String := s!\"{ let _ := (§B); (sorry : Nat) }\"\n" a b) ++
    (ls "def x : String := r#\"\\\"#\ndef z := r\"\\\"").map (mk "§A\ntheorem bad : False := sorry\n") ++
    (ls "def ok2 := f \"{\"\ndef t := Nat ×''\"'\ndef x:=r\"\\\"").map (mk "§A\ntheorem pwn : False := sorry\n-- \"\n") ++
    (ss "/--/ \" -/\ntheorem e : False := sorry\n\n§§\n/-/-/\ndef bypass : Nat := sorry\n\n§§\ndef a := Foo.s! \"{\"\ntheorem evil : False := sorry\n-- \"\n\n§§\ndef t1 := g `s! \"{\"\ntheorem evil1 : False := sorry\n-- \"\n\n§§\ndef poison : String := logInfoAt (let _ := s!\"{\"(\"}\"; \"\")\ndef sep : String := s!\"{(sorry : Nat)}\"\n\n§§\nsyntax \"q!\" interpolatedStr(term) : term\ndef c : String := q!\"{(sorry : Nat)}\"\n\n§§\ndef myRef.{u} : Syntax := .missing\ndef p : CoreM Unit := throwErrorAt myRef.{0} \"{(sorry : Nat)}\"\n\n§§\nmacro \"m\" : command => pure (Syntax.node .none ``Lean.Parser.Command.«syntax» #[Syntax.atom .none \"syntax\", Syntax.mkStrLit \"!--\"])\nexample : False := !-- sorry\n\n§§\nmacro \"xbr\" \"}\" \"(\" x:term \")\" \"{\" : term => `($x)\ndef testBr : String := s!\"{(xbr } (sorry) { : Nat)}\"\n\n§§\nmacro \"xbr2\" optional(\"{\") \"}\" : term => `(0)\ndef testBr2 : String := s!\"{let _ := xbr2 }; (sorry : Nat)}\"\n")) ++
  hit 3 "sorry" (
    (ps "M.r#§M.r#\"\\\" \"\nM.r§M.r\"\\\" \"\n+r§+r\"\\\" \"\n(r§(r\"\\\" \")").map (fun (a, b) => mk "macro \"§A\" s:str : term => `(0)\ndef x := §B\ntheorem pwn : False := sorry\n" a b) ++
    (ls "/--\n/-!\n/-").map (mk "syntax \"§A\" : term\n§A hi \" -/\ndef f1 : Nat := sorry -- \"\n") ++
    #["\n  ", "\r\n\t"].map (mk "notation \"foo\\§A\\\"\" => 1\ndef x : Nat := foo\" + sorry + foo\"\n") ++
    (ss "def logInfo (_ : String) : Nat := 0\ndef _a : Nat := logInfo \"{\"\ntheorem pwn : False := sorry\ndef _b : String := \"}\"\n\n§§\nnotation \"''\" c:max => c\ndef b : Char := '''\"'\ntheorem pwn : False := sorry\n-- \"\n\n§§\nsyntax \"x\\\"a\" term \"b\\\"x\" : term\nmacro_rules | `(x\"a $t b\"x) => `($t)\ndef p : Nat := x\"asorry b\"x\n\n§§\nsyntax (name := lemma) \"x/-\" term \"-/x\" : term\nmacro_rules | `(x/- $t -/x) => `($t)\ndef p : Nat := x/- sorry -/x\n\n§§\n@[term_parser] def mySym := leading_parser symbol \"foo\\\"\"\n@[macro mySym] def mySymMacro : Macro := fun _ => `(1)\ndef x : Nat := foo\" + sorry + foo\"\n\n§§\nsyntax \"x}\" : term\nmacro_rules | `(x}) => `(0)\ndef f : String := s!\"{x} + (sorry : Nat)}\"\n\n§§\nsyntax \"mykw\" \"{\" : term\nmacro_rules | `(mykw {) => `(1)\nexample : String := s!\"{ mykw { } -- {(sorry : Nat)}\"\n\n§§\nelab \"e\" : command => elabCommand (Syntax.node .none (Name.mkStr4 \"Lean\" \"Parser\" \"Command\" \"syntax\") #[«Syntax».atom .none \"\\\"a\\\\\\\"\\\"\"])\nmacro_rules | `(a\") => `(0)\ntheorem boom : False := sorry\n-- \"\n\n§§\nmacro \"xb\" \"[\" : term => `(0)\ndef t := xb [ macro \"foo\\\"\" : term => `(0)\ntheorem pwn : False := by let _ := foo\"; have : False := sorry; let _ := foo\"; exact this\n\n§§\nmacro \"xclose\" \"}\" : term => `(0)\ndef testAllModes : String := s!\"{let _ := xclose }; let _ := \"hello\nworld\"; (sorry : Nat)}\"\n")) ++
  hit 4 "sorry" (
    (ss "notation \"a/-\" => 1\ndef t := a/-\n§§\nnotation \"a«\" => 1\ndef t := a«\n§§\nnotation \"a--\" => 1\ndef t := a-- + 1\n§§\nsyntax \"/--a\" : term\ndef t := /--a").map (mk "§A\nnotation \"b\\\"\" => 1\ndef x : Nat := b\" + sorry + b\"\n") ++
    (ss "macro \"xopen\" (\"(\" <|> \")\") : term => `(0)\ndef trigger := xopen (\n§§\nmacro \"xrev\" \")\" \"(\" : term => `(0)\ndef triggerRev := xrev ) (").map (mk "§A\nmacro \"foo\\\"\" : term => `(0)\ntheorem pwn : False := by let _ := foo\"; have : False := sorry; let _ := foo\"; exact this\n") ++
    (ss "syntax \"![\" : term\nmacro_rules | `(![) => `(1)\nsyntax \"!--\" : term\nexample : False := !-- sorry\n\n§§\nstructure S where a : Nat\nmacro \"unbal\" \"{\" : term => `(0)\ndef f : String := s!\"{ let _ : S := { a := 1 }; let _ := '\"'; unbal { }\"\ntheorem boom : False := sorry\n-- \"\n")) ++
  hit 5 "sorry" (ss "macro \"mk\" a:str b:str : command => `(syntax $a:str term $b:str : term)\ndef dummy := 0\nmk \"x/-\" \"-/x\"\nmacro_rules | `(x/- $t -/x) => `($t)\ndef p : Nat := x/- sorry -/x\n\n§§\nsyntax \"[\" : term\nmacro_rules | `([) => `(1)\nsyntax \"!--\" : term\nmacro_rules | `(!--) => `(fun (x : False) => x)\nexample : False := !-- sorry\n\n§§\nmacro \"open_b\" \"[\" : term => `(0)\ndef u : Nat := open_b [\nopen Nat in syntax \"a\\\"\" : term\nmacro_rules | `(a\") => `(0)\ntheorem boom : False := sorry\n-- \"\n") ++
  ((ss "def y := r##\"sorry \"# still raw\"##\n\n§§\ndef sorry? := 1\ndef sorry! := 2\n\n§§\ndef ok := f \"sorry\"\n\n§§\ndef t := '\\''\ndef ok := \"sorry\"\n\n§§\nmacro \"(r\" s:str : term => `(0)\ndef ok := (return \"sorry\")\n\n§§\n/-- doc comment mentioning sorry -/\ndef ok : Nat := 1\n").map (·, #[])) ++
  #[("def n := f! \"{(by native_decide : Bool)}\"\n", #[(1, "native_decide")]),
    ("#guard true\n", #[(1, "#guard")]),
    ("-- eof\n#guard 1 + 1 == 2", #[(2, "#guard")]),
    ("def s := s!\"{#guard true}\"\n", #[(1, "#guard")]),
    ("#guard_msgs in def ok : Nat := 1\n", #[]),
    ("-- #guard true\n/- #guard false -/\ndef s := \"#guard true\"\n", #[]),
    ("syntax \"t1/-\" : term\ndef a1 := t1/-\nsyntax \"t2/-\" : term\ndef a2 := t2/-\nsyntax \"t3/-\" : term\ndef a3 := t3/-\nsyntax \"t4/-\" : term\ndef a4 := t4/-\nsyntax \"t5/-\" : term\ndef a5 : Nat := t5/- + sorry -- -/\n", #[(10, "sorry")])]

private structure MockReq where
  method : String
  target : String
  body   : String
deriving Inhabited

private structure MockSvc where
  live : String × Nat := ("", 0)
  cand : String × Nat := ("", 0)
  conc : Nat := 0
  invokerIamDisabled : Bool := false
  strs : List (String × String) := []
  jls  : List (String × List Json) := []
  uris : Option String × Option String := (none, none)
  revs : Option String × Option String := (none, none)
deriving Inhabited

private structure MockUpload where
  bucket : String
  name : String
  cacheControl : String
  content : String
  boundary : String
deriving Inhabited, BEq, Repr

private structure MockGcpState where
  reqs : Array MockReq := #[]
  etagSeq : Nat := 1
  force412Once : Bool := false
  pending : Bool × Bool × Bool := (false, false, false)
  pendingOpName? : Option String := none
  sql409InProgOnce : Bool := false
  failShiftRegion? : Option String := none
  sas : List String := []
  iamPolicies : List (String × IamPolicyDoc) := []
  denyPolicies : List (String × Json) := []
  secrets : List (String × String) := []
  dbs : List (String × String) := []
  sqlUsers : List (String × String) := []
  uploads : List MockUpload := []
  egress : List (String × Json) := []
  services : List (String × MockSvc) := []
  healthStatus : Nat := 200

private def setAssoc {α : Type} (xs : List (String × α)) (k : String) (v : α) : List (String × α) := (xs.filter (·.1 != k)) ++ [(k, v)]
private def setAssocs {α : Type} (xs : List (String × α)) (ps : List (String × α)) : List (String × α) := ps.foldl (fun a (k, v) => setAssoc a k v) xs
private def MockSvc.s (sv : MockSvc) (k : String) : String := (sv.strs.lookup k).getD ""
private def MockSvc.jl (sv : MockSvc) (k : String) : List Json := (sv.jls.lookup k).getD []
private def modSvc (s : MockGcpState) (k : String) (f : MockSvc → MockSvc) : MockGcpState := match s.services.lookup k with | some sv => { s with services := setAssoc s.services k (f sv) } | none => s
private def pathSegAfter (path seg : String) : String := match (path.splitOn "/").dropWhile (· != seg) with | _ :: v :: _ => v | _ => ""
private def iamPolicyKey (path : String) : String := if path.endsWith ":getIamPolicy" || path.endsWith ":setIamPolicy" then (path.dropEnd 13).toString else path
private def lookupOr404 {α : Type} (xs : List (String × α)) (k : String) (f : α → Json) (msg := "not found") := match xs.lookup k with | some v => jsonResp 200 (f v) | none => jsonErrResp 404 msg

private def parseMultipartUpload (hdrs : Array (String × String)) (bodyStr : String) : String × String × String × String :=
  let boundary := match ((getHeader? hdrs "content-type").getD "").splitOn "boundary=" with | _ :: rest :: _ => ((rest.splitOn ";").headD "").trimAscii.toString | _ => ""
  if boundary.isEmpty then ("", "", "", "")
  else
    let parts := bodyStr.splitOn s!"--{boundary}"
    let partBody (idx : Nat) : String := match (parts.getD idx "").splitOn "\r\n\r\n" with
      | _ :: rest => let s := String.intercalate "\r\n\r\n" rest; if s.endsWith "\r\n" then (s.dropEnd 2).toString else s | [] => ""
    let m := partBody 1; (Json.pathStr m "name", Json.pathStr m "cacheControl", partBody 2, boundary)

private def handleMockGcp (stRef : IO.Ref MockGcpState) (portRef : IO.Ref UInt16)
    (method target : String) (hdrs : Array (String × String)) (body : ByteArray) : IO (Nat × String × ByteArray) := do
  let bodyStr := utf8Str body; let (path, query) := splitPathQuery target; let qParams := Qed.Auth.parseQueryParams query
  let lastSeg := (path.splitOn "/").getLastD ""; let jo (ps : List (String × Json)) := jsonResp 200 (.obj ps)
  let addUniq {α : Type} [BEq α] (get : MockGcpState → List α) (set : MockGcpState → List α → MockGcpState) (v : α) (resp : List (String × Json)) : IO (Nat × String × ByteArray) := do
    if (get (← stRef.get)).contains v then return jsonErrResp 409 "exists"
    stRef.modify fun s => set s (get s ++ [v]); return jo resp
  stRef.modify fun s => { s with reqs := s.reqs.push { method, target, body := bodyStr } }
  if path == "/_qed/health" then let st := (← stRef.get).healthStatus; return txtResp st (if st == 200 then "ok" else "unhealthy")
  if path.endsWith ":getIamPolicy" || (method == "GET" && path.endsWith "/iam") then
    let k := iamPolicyKey path; let cur ← stRef.get
    if k.contains "/services/" && (cur.services.lookup k).isNone then return jsonErrResp 404 "service not found"
    return lookupOr404 cur.iamPolicies k IamPolicyDoc.toJson
  if path.endsWith ":setIamPolicy" || (method == "PUT" && path.endsWith "/iam") then
    let k := iamPolicyKey path; let cur ← stRef.get
    if k.contains "/services/" && (cur.services.lookup k).isNone then return jsonErrResp 404 "service not found"
    let .ok j := Json.parse bodyStr | return jsonErrResp 400 "bad json"
    let .ok incoming := IamPolicyDoc.fromJson ((j.get? "policy").getD j) | return jsonErrResp 400 "bad policy"
    if cur.force412Once then stRef.set { cur with force412Once := false }; return jsonErrResp 412 "simulated etag contention"
    if let some existing := cur.iamPolicies.lookup k then
      if !existing.etag.isEmpty && incoming.etag != existing.etag then return jsonErrResp 412 s!"etag mismatch: got `{incoming.etag}`, want `{existing.etag}`"
    let saved : IamPolicyDoc := { incoming with etag := s!"etag-{cur.etagSeq}" }
    stRef.set { cur with etagSeq := cur.etagSeq + 1, iamPolicies := setAssoc cur.iamPolicies k saved }; return jsonResp 200 saved.toJson
  if path.contains "/serviceAccounts" then
    if method == "POST" then let e := s!"{Json.pathStr bodyStr "accountId"}@{pathSegAfter path "projects"}.iam.gserviceaccount.com"; return ← addUniq (·.sas) (fun s xs => { s with sas := xs }) e [("email", .str e)]
    if method == "DELETE" then stRef.modify fun s => { s with sas := s.sas.filter (· != lastSeg.replace "%40" "@") }; return jsonResp
  if path.contains "/denypolicies" && !path.contains "/operations/" then
    let denyKey := if method == "POST" then s!"{path}/{(qParams.lookup "policyId").getD ""}" else path
    if method == "GET" then return lookupOr404 (← stRef.get).denyPolicies denyKey id
    if method == "POST" || method == "PUT" then
      let .ok j := Json.parse bodyStr | return jsonErrResp 400 "bad json"
      let cur ← stRef.get; let saved := match j with | .obj ms => Json.obj (("etag", .str s!"deny-{cur.etagSeq}") :: ms.filter (·.1 != "etag")) | other => other
      stRef.set { cur with etagSeq := cur.etagSeq + 1, denyPolicies := setAssoc cur.denyPolicies denyKey saved }; return jsonResp 200 saved
  if method == "GET" && path.contains "/operations/" then
    return if path.startsWith "/v1/projects/" then jo [("kind", .str "sql#operation"), ("name", .str lastSeg), ("status", .str "DONE")] else jo [("name", .str (trimLeadingSlash path)), ("done", .bool true)]
  if path.contains "/secrets" then
    let proj := pathSegAfter path "projects"
    if method == "GET" then return jo [("secrets", .arr (((← stRef.get).secrets.filter (·.1 == proj)).map fun (_, sid) => .obj [("name", .str s!"projects/{proj}/secrets/{sid}")]))]
    if method == "POST" then let sid := (qParams.lookup "secretId").getD ""; return ← addUniq (·.secrets) (fun s xs => { s with secrets := xs }) (proj, sid) [("name", .str s!"projects/{proj}/secrets/{sid}")]
    if method == "DELETE" then stRef.modify fun s => { s with secrets := s.secrets.filter (· != (proj, lastSeg)) }; return jsonResp
  if method == "POST" && path.startsWith "/upload/storage/v1/b/" then
    let (name, cacheControl, content, boundary) := parseMultipartUpload hdrs bodyStr
    stRef.modify fun s => { s with uploads := s.uploads ++ [{ bucket := pathSegAfter path "b", name, cacheControl, content, boundary }] }; return jo [("name", .str name)]
  if path.contains "/instances/" && path.contains "/users" then
    let inst := pathSegAfter path "instances"
    if method == "POST" then let u := Json.pathStr bodyStr "name"; return ← addUniq (·.sqlUsers) (fun s xs => { s with sqlUsers := xs }) (inst, u) [("name", .str u)]
    if method == "DELETE" then stRef.modify fun s => { s with sqlUsers := s.sqlUsers.filter (· != (inst, (qParams.lookup "name").getD "")) }; return jsonResp
  if path.contains "/instances/" && path.contains "/databases" then
    let inst := pathSegAfter path "instances"
    if method == "GET" then return jo [("items", .arr (((← stRef.get).dbs.filter (·.1 == inst)).map fun (_, d) => .obj [("name", .str d)]))]
    if method == "POST" then
      if (← stRef.get).sql409InProgOnce then stRef.modify fun s => { s with sql409InProgOnce := false }; return jsonErrResp 409 "operationInProgress: another operation is running"
      let dbName := Json.pathStr bodyStr "name"
      let r ← addUniq (·.dbs) (fun s xs => { s with dbs := xs }) (inst, dbName) [("name", .str dbName)]
      if r.1 == 200 then
        if (← stRef.get).pending.2.2 then stRef.modify fun s => { s with pending := (s.pending.1, s.pending.2.1, false) }; return jo [("kind", .str "sql#operation"), ("name", .str "sql-op-1"), ("status", .str "RUNNING")]
      return r
    if method == "DELETE" then stRef.modify fun s => { s with dbs := s.dbs.filter (· != (inst, lastSeg)) }; return jsonResp
  if path.contains "/gatewaySecurityPolicies/" then
    if method == "GET" then return lookupOr404 (← stRef.get).egress path id
    if method == "PUT" then let .ok j := Json.parse bodyStr | return jsonErrResp 400 "bad json"
                            stRef.modify fun s => { s with egress := setAssoc s.egress path j }; return jsonResp 200 j
    if method == "DELETE" then stRef.modify fun s => { s with egress := s.egress.filter (·.1 != path) }; return jsonResp
  if path.contains "/services/" then
    if method == "GET" then
      let some svc := (← stRef.get).services.lookup path | return jsonErrResp 404 "service not found"
      let port ← portRef.get; let baseUrl := svc.uris.2.getD s!"http://127.0.0.1:{port}"; let candUrl := svc.uris.1.getD baseUrl
      let statusesJ := if !svc.cand.1.isEmpty then [Json.obj [("tag", .str "candidate"), ("revision", .str svc.cand.1), ("uri", .str candUrl)]] else []
      let optStr (k : String) (o : Option String) := o.map (fun r => [(k, Json.str r)]) |>.getD []
      let optArr (k : String) (xs : List Json) := if xs.isEmpty then [] else [(k, Json.arr xs)]
      let c0 := [("env", .arr (svc.jl "env"))] ++ optArr "command" (svc.jl "cmd") ++ optArr "args" (svc.jl "args") ++ optArr "volumeMounts" (svc.jl "mnt")
      return jo ([("uri", .str baseUrl), ("ingress", .str (svc.s "ing")), ("invokerIamDisabled", .bool svc.invokerIamDisabled),
        ("template", .obj [("serviceAccount", .str (svc.s "sa")), ("vpcAccess", .obj [("egress", .str (svc.s "vpc")), ("networkInterfaces", .arr (svc.jl "vpc"))]),
          ("volumes", .arr (svc.jl "vol")), ("containers", .arr (.obj c0 :: svc.jl "extra"))]),
        ("traffic", .arr (svc.jl "tr")), ("trafficStatuses", .arr statusesJ)] ++ optStr "latestReadyRevision" svc.revs.1 ++ optStr "latestCreatedRevision" svc.revs.2)
    if method == "PATCH" then
      let cur ← stRef.get
      if query.contains "updateMask=traffic" then
        if let some failReg := cur.failShiftRegion? then if path.contains s!"/locations/{failReg}/" then return jsonErrResp 500 s!"simulated traffic shift failure in {failReg}"
      let .ok j := Json.parse bodyStr | return jsonErrResp 400 "bad json"
      let targets := j.arrAt "traffic"; let pctSum := targets.foldl (init := 0) fun acc t => acc + (t.natAt? "percent").getD 0
      if pctSum != 100 then return jsonErrResp 400 s!"traffic percentages must sum to 100 (got {pctSum})"
      let prev := (cur.services.lookup path).getD {}
      let cand? := targets.find? (·.strAt? "tag" == some "candidate")
      let live? := targets.find? fun t => (t.strAt? "tag").isNone && (t.natAt? "percent").getD 0 == 100
      let (live, cand) := match live?, cand? with
        | some lv, none    => (((lv.strAt? "revision").getD prev.live.1, 100), ("", 0))
        | some lv, some cv => (((lv.strAt? "revision").getD prev.live.1, 100), ((cv.strAt? "revision").getD "", (cv.natAt? "percent").getD 0))
        | none,    some cv => let r := (cv.strAt? "revision").getD ""; ((r, 100), (r, 100))
        | none,    none    => (prev.live, prev.cand)
      let arrOr (p k : String) := ((j.atPath p).bind (·.arr?)).getD (prev.jl k)
      let envJson := arrOr "template.containers.0.env" "env"
      let deployEnv := (envJson.findSome? fun e => if e.strAt? "name" == some "QED_DEPLOY_ENV" then e.strAt? "value" else none).getD (prev.s "env")
      let nextSvc : MockSvc := { prev with
        live, cand, conc := ((j.get? "template").bind (·.natAt? "maxInstanceRequestConcurrency")).getD prev.conc,
        strs := setAssocs prev.strs [("env", deployEnv), ("ing", (j.strAt? "ingress").getD (prev.s "ing")),
          ("sa", (j.pathStr? "template.serviceAccount").getD (prev.s "sa")), ("vpc", (j.pathStr? "template.vpcAccess.egress").getD (prev.s "vpc"))],
        jls := setAssocs prev.jls [("env", envJson), ("tr", targets), ("vpc", arrOr "template.vpcAccess.networkInterfaces" "vpc"), ("vol", arrOr "template.volumes" "vol")] }
      stRef.modify fun s => { s with services := setAssoc s.services path nextSvc }
      if (← stRef.get).pending.1 then
        let opNm := (← stRef.get).pendingOpName?.getD "projects/qed-prod/locations/us-central1/operations/op-1"
        stRef.modify fun s => { s with pending := (false, s.pending.2.1, s.pending.2.2), pendingOpName? := none }; return jo [("name", .str opNm)]
      return jo [("done", .bool true)]
    if method == "DELETE" then
      stRef.modify fun s => { s with services := s.services.filter (·.1 != path) }
      if (← stRef.get).pending.2.1 then
        stRef.modify fun s => { s with pending := (s.pending.1, false, s.pending.2.2) }
        return jo [("name", .str s!"projects/{pathSegAfter path "projects"}/locations/us-central1/operations/del-op-1")]
      return jsonResp
  return jsonErrResp 404 s!"unhandled mock route {method} {target}"

private def mkTestPlan (key : DeployKey) (buildHash : String) (regions : List GcpRegion) (egress secrets dbs assets : List String) (previewProtection : PreviewProtection := .pub) : GcpPlan :=
  let dbInfos : List Qed.Server.DatabaseInfo := dbs.map fun nm =>
    { dbName := nm.toName, shortName := nm, configConst := nm.toName ++ `config, ensureSchemaConst := nm.toName ++ `ensureSchema, secrets := #[], tables := #[], isManaged := true, envSpecs := managedPostgresTargets nm }
  compileInfra key buildHash { name := "Demo", appName := "DemoApp", regions, compute := .performance, preview := { protection := previewProtection } } {
    rootModule := "Demo", mode := "fullstack", secrets, egress, databases := dbInfos,
    server? := some { serverName := `DemoApi, shortName := "DemoApi", hasState := false, secrets := secrets.toArray, ownSecrets := secrets.toArray, envVars := #[], externalServices := #[], databases := (dbInfos.map (·.configConst)).toArray, methods := #[] },
    assets := assets.map fun p => { path := p, mime := assetMimeType p, bytes := 16 } }

private def denyKeyFor (projId denyId : String) : String :=
  s!"/v2/policies/{Qed.encodeSeg s!"cloudresourcemanager.googleapis.com/projects/{projId}"}/denypolicies/{denyId}"

private def testPureCloudValidators (c : TestChecker) (cfg : GcpExecConfig) (prodKey : DeployKey) (plan : GcpPlan) : IO Unit := do
  c.checkEq "GcpPlan JSON round-trip" (GcpPlan.fromJson plan.toJson) (.ok plan)
  let (parseUrl, fmtReq) := (Qed.Server.Net.parseHttpUrl, Qed.Server.Net.formatOutboundRequest)
  let (bearerCfg, aud) := ({ cfg with auth := .bearerToken "ya29.secret-oauth" }, some "https://svc-uc.a.run.app")
  let mkJwt (a : String) := s!"{Qed.Auth.base64UrlEncode "{\"alg\":\"RS256\"}".toUTF8}.{Qed.Auth.base64UrlEncode (Json.render (.obj [("aud", .str a)])).toUTF8}.sig"
  let (goodJwt, bRun, svc) := (mkJwt "https://svc-uc.a.run.app", "https://svc-abc-uc.a.run.app", renderCloudRunName prodKey)
  let resTok (tok? : Option String) := resolveToken { bearerCfg with healthIdToken? := tok? } aud
  c.check "resolveToken refuses raw .bearerToken on /_qed/health audience" (!(← resTok none).isOk)
  c.checkEq "resolveToken accepts healthIdToken? with matching JWT aud" (← resTok (some goodJwt)) (.ok (some goodJwt))
  let badAud ← resTok (some (mkJwt "https://other-uc.a.run.app")); let badJwt ← resTok (some "eyJ.not-a-jwt")
  c.check "resolveToken rejects healthIdToken? with mismatched JWT aud or malformed JWT" (!badAud.isOk && !badJwt.isOk)
  let prevKeyCheck : DeployKey := { prodKey with env := .preview ⟨9, by decide⟩ }
  let basePrevPlan := mkTestPlan prevKeyCheck "forged123" [.us_central1] [] [] [] []
  let badPlans (ps : List GcpPlan) := ps.all fun p => !(GcpPlan.fromJson p.toJson).isOk
  let xssHtml := Qed.Cli.indexHtml true true ["/x.css\"><script>alert(1)</script><link"] "/app\".mjs" "/s\".css" "http://127.0.0.1\"<script>"
  let latestTgt := Json.obj [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST"), ("percent", toJson (100 : Nat))]
  for (lbl, ok) in [
      ("isSafeRelativeAssetPath rejects traversal, empty segs, trailing slash, ctrl, query/frag, & internal manifests",
        ["/../etc/passwd", "//etc/passwd", "/a//b.mjs", "/dir/", "/bad\n.mjs", "/app.mjs?v=1", "/app.mjs#top", "/qed_deploy.json", "/sub/QED_DEPLOY.JSON", "/qed_manifest.json"].all (!isSafeRelativeAssetPath ·) && isSafeRelativeAssetPath "/app.0123456789ab.mjs"),
      ("formatOutboundRequest strips Transfer-Encoding & rejects CRLF/space in ParsedUrl; parseHttpUrl rejects multi-colon/backslash",
        (match parseUrl "https://example.com/api" |>.bind (fmtReq "POST" · #[("Transfer-Encoding", "chunked"), ("X-Ok", "1")] "hello".toUTF8) with | .ok raw => let s := utf8Str raw; !s.toLower.contains "transfer-encoding" && s.contains "Content-Length: 5" && s.contains "X-Ok: 1" | .error _ => false) &&
        [("example.com\r\nX: 1", "/"), ("example.com", "/a HTTP/1.1")].all (fun (h, p) => !(fmtReq "GET" { isTls := false, isIpv6 := false, host := h, port := 80, pathAndQuery := p } #[] ByteArray.empty).isOk) &&
        ["http://example.com:80:443/ok", "http://example.com\\evil/ok"].all fun u => !(parseUrl u).isOk),
      ("isValidCloudRunCandidatePair validates strict 4-label https://*.a.run.app pairs & candidate tag",
        [("https://candidate---svc-abc-uc.a.run.app", bRun), (bRun, bRun)].all (fun (x, y) => isValidCloudRunCandidatePair x y) &&
        [("https://evil---svc-abc-uc.a.run.app", bRun), ("https://svc.run.app", "https://svc.run.app"), ("https://evil.example", bRun), ("https://candidate---other.a.run.app", bRun), ("http://candidate---svc-abc-uc.a.run.app", bRun), ("https://svc-abc-uc.a.run.app@evil.example", bRun)].all fun (x, y) => !isValidCloudRunCandidatePair x y),
      ("isValidCloudRunCandidateForService binds baseHost to renderCloudRunName & region",
        isValidCloudRunCandidateForService prodKey .us_central1 s!"https://candidate---{svc}-xyz-uc.a.run.app" s!"https://{svc}-xyz-uc.a.run.app" &&
        isValidCloudRunCandidateForService prodKey .us_central1 s!"https://{svc}-123.us-central1.run.app" s!"https://{svc}-123.us-central1.run.app" &&
        !isValidCloudRunCandidateForService prodKey .us_central1 "https://candidate---attacker-xyz-uc.a.run.app" "https://attacker-xyz-uc.a.run.app" &&
        !isValidCloudRunCandidateForService prodKey .us_central1 s!"https://{svc}-123.europe-west1.run.app" s!"https://{svc}-123.europe-west1.run.app"),
      ("parsePendingLro accepts project ID & numeric project number LROs and rejects injection",
        ["projects/qed-prod/locations/us-central1/operations/../../evil", "projects/qed-prod/locations/us-central1/operations/op1?x=1"].all (fun s => !(parsePendingLro (.obj [("name", .str s)])).isOk) &&
        ["projects/qed-prod/locations/us-central1/operations/op-1", "projects/123456789012/locations/us-central1/operations/op-num-1", "policies/cloudresourcemanager.googleapis.com%2Fprojects%2F123456789012/denypolicies/deny-qed-run-public/operations/op-2"].all fun s => parsePendingLro (.obj [("name", .str s)]) == .ok (some s)),
      ("GcpPlan.fromJson rejects forged preview prodCluster binding & runtimeSa storageObjectAdmin",
        badPlans [{ basePrevPlan with bindings := basePrevPlan.bindings ++ [{ principal := .runtimeSa prevKeyCheck, role := .cloudSqlClient, resource := .cloudSqlDb .prodCluster prevKeyCheck "app" }] },
          { plan with bindings := plan.bindings ++ [{ principal := .runtimeSa prodKey, role := .storageObjectAdmin, resource := .assetPrefix prodKey "abc123def456" true }] }]),
      ("GcpPlan.fromJson rejects poisoned denies (secretAccessor on cloudRun / extra assetPrefix deny)",
        badPlans [{ plan with denies := plan.denies ++ [{ principals := [.allUsers, .allAuthenticatedUsers], permissions := [.runInvoke, .secretAccessor], resource := .cloudRun prodKey }] },
          { plan with denies := plan.denies ++ [{ principals := [.allUsers, .allAuthenticatedUsers], permissions := [.runInvoke], resource := .assetPrefix prodKey "abc123def456" true }] }]),
      ("indexHtml escapes stylesheets, hostScript, stylesHref, and sseUrl against HTML injection", !xssHtml.contains "<script>alert(1)" && !xssHtml.contains "\"<script>" && xssHtml.contains "&quot;"),
      ("isValidEnvVarName blocks dangerous QED_*/HOST vars while allowing managed DB & auth client secret",
        ["QED_INSECURE_SKIP_TLS_VERIFY", "QED_CA_CERT_FILE", "QED_GCP_TOKEN_URL", "QED_CSP", "QED_EXT_API", "QED_AUTH_SECRET", "QED_AUTH_SECRET_PREV", "HOST"].all (!Qed.Server.isValidEnvVarName ·) &&
        ["QED_MANAGED_DB_NOTESDB", "QED_AUTH_CLIENT_SECRET"].all Qed.Server.isValidEnvVarName),
      ("isQedRuntimeSaEmailInProject enforces canonical renderSaId grammar",
        isQedRuntimeSaEmailInProject "qed-prod" (renderSaEmail prodKey) && ["q-backdoor@qed-prod.iam.gserviceaccount.com", "q-07-3-p@qed-prod.iam.gserviceaccount.com", "q-7-3-p@qed-nonprod.iam.gserviceaccount.com"].all (!isQedRuntimeSaEmailInProject "qed-prod" ·)),
      ("parseLiveTrafficTargets pins LATEST to serving revision and rejects unresolvable LATEST",
        (match parseLiveTrafficTargets (.obj [("traffic", .arr [latestTgt]), ("trafficStatuses", .arr [.obj [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST"), ("revision", .str "cr-7-3-p-oldrev"), ("percent", toJson (100 : Nat))]])]) with | .ok [t] => t.strAt? "type" == some "TRAFFIC_TARGET_ALLOCATION_TYPE_REVISION" && t.strAt? "revision" == some "cr-7-3-p-oldrev" | _ => false) &&
        !(parseLiveTrafficTargets (.obj [("traffic", .arr [latestTgt])])).isOk),
      ("reqUpsertDenyRule strips poisoned exceptionPrincipals",
        let req := reqUpsertDenyRule cfg.endpoints cfg.edgeSaEmail cfg.builderSaEmail { principals := [.allUsers, .allAuthenticatedUsers], permissions := [.secretAccessor], resource := .secret prodKey "STRIPE_KEY" }
          (some "etag-1") ["principalSet://goog/public:all", "principal://goog/subject/attacker@evil.com", s!"principal://iam.googleapis.com/projects/-/serviceAccounts/{renderSaEmail prodKey}"]
        !req.body.contains "attacker@evil.com" && !(parseDenyExceptionPrincipals ((Json.parse req.body).toOption.getD (.obj []))).contains "principalSet://goog/public:all" && req.body.contains (renderSaEmail prodKey)),
      ("classifyStaticPath blocks GET/HEAD /qed_deploy.json, /qed_manifest.json, & /./ dot-segment bypasses",
        [("GET", "/qed_deploy.json", false), ("GET", "/qed_deploy.json", true), ("HEAD", "/qed_deploy.json", false), ("GET", "/QED_DEPLOY.JSON?v=1", false), ("GET", "/qed_manifest.json", false), ("GET", "/./app.0123456789ab.mjs", false), ("GET", "/./_qed/secret.json", false), ("GET", "//app.0123456789ab.mjs", false)].all fun (m, p, d) => Qed.Server.Http.classifyStaticPath m p d == none),
      ("reqUploadAsset rejects colliding boundary bytes", !(reqUploadAsset cfg.endpoints prodKey "abc" "/app.mjs" "hi --fixed_b-- bye".toUTF8 "fixed_b").isOk)] do
    c.check lbl ok
  let badTok := forbiddenTokenCases.find? fun (src, want) => Qed.Cli.findForbiddenTokens src != want
  c.check "findForbiddenTokens parses Lean 4 raw strings, interpolations, comments, custom syntax/macros, and unbalanced brackets" badTok.isNone (badTok.map (fun (s, w) => s!"got {Qed.Cli.findForbiddenTokens s}, want {w} for {s}") |>.getD "")

private def testCliDeployChecks (c : TestChecker) (baseUrl : String) : IO Unit := do
  let qedBin ← qedBinPath
  let runDeploy (extra : Array String) : IO (UInt32 × String) := do let (code, o, e) ← runCmd qedBin (#["deploy", "--mod", "QedTests.CloudChecks", "--skip-build"] ++ extra); return (code, o ++ e)
  for (lbl, args, wantOk, has, omits) in [
      ("qed deploy NotesDeploy --dry-run exits 0 with 4-phase plan", #["--deploy", "NotesDeploy", "--dry-run"], true, ["concurrency=1000", "2000m/4096Mi", "Phase 1", "Phase 3"], []),
      ("StaticShellDeploy --dry-run leaks 0 DBs and 0 secrets", #["--deploy", "StaticShellDeploy", "--dry-run"], true, [], ["ensureSecret", "ensureDb"]),
      ("StatefulDeploy --dry-run pins max=1 and leaks 0 DBs/secrets", #["--deploy", "StatefulDeploy", "--dry-run"], true, ["instances=0..1"], ["ensureSecret", "ensureDb"]),
      ("qed deploy --check-drift exits non-zero with findings", #["--deploy", "NotesDeploy", "--check-drift", "--project", "qed-test", "--api-base", baseUrl], false, ["drift finding"], []),
      ("qed deploy --teardown --env prod is safe no-op", #["--deploy", "NotesDeploy", "--teardown", "--env", "prod", "--project", "qed-test", "--api-base", baseUrl], true, ["safe no-op"], []),
      ("qed deploy --env preview without --pr exits non-zero", #["--deploy", "NotesDeploy", "--dry-run", "--env", "preview"], false, [], []),
      ("qed deploy rejects identical --prod-project and --nonprod-project", #["--deploy", "NotesDeploy", "--dry-run", "--prod-project", "acme-same", "--nonprod-project", "acme-same"], false, [], []),
      ("qed deploy rejects ambiguous multiple deploy blocks without --deploy", #["--dry-run"], false, [], []),
      ("qed deploy rejects leading-dash --dist", #["--deploy", "NotesDeploy", "--dry-run", "--dist", "-rf"], false, [], [])] do
    let (rc, out) ← runDeploy args; c.check lbl ((rc == 0) == wantOk && has.all (out.contains ·) && omits.all (!out.contains ·)) out
  for badUrl in ["http://127.evil.com", "https://evil.example", "https://googleapis.com@evil.example", "https://storage.googleapis.com/attacker-bucket/poison.json#",
      "https://storage.googleapis.com", "https://attacker-bucket.storage.googleapis.com", "https://commondatastorage.googleapis.com", "https://bucket.commondatastorage.googleapis.com",
      "https://storage-download.googleapis.com", "https://storage-upload.googleapis.com", "https://storage.us-central1.rep.googleapis.com", "https://googleapis.com",
      "https://firebasestorage.googleapis.com", "https://www.googleapis.com", "https://run.googleapis.com/v2/evil", "https://run.googleapis.com?x=1", "https://run.googleapis.com#frag"] do
    c.check s!"qed deploy rejects --api-base ({badUrl})" ((← runDeploy #["--deploy", "NotesDeploy", "--dry-run", "--api-base", badUrl]).1 != 0)

private def testCloudDeployEndToEnd (c : TestChecker) : IO Unit := do
  let (stRef, portRef) := (← IO.mkRef ({} : MockGcpState), ← IO.mkRef (0 : UInt16))
  withMockServer c "mock GCP REST server started" (startMockHttpServer (handleMockGcp stRef portRef)) (·.2) fun (port, _) => do
    portRef.set port; let baseUrl := s!"http://127.0.0.1:{port}"
    let cfg : GcpExecConfig := { endpoints := GcpEndpoints.allLocal baseUrl, auth := .none, region := .us_central1, ssrfGuard := false }
    let shard : ShardProject := ⟨"qed-prod", "qed-nonprod", by decide⟩
    let prodKey : DeployKey := { shard, tenant := ⟨7, by decide⟩, app := ⟨3, by decide⟩, env := .prod }
    let plan := mkTestPlan prodKey "abc123def456" [.us_central1] ["https://api.stripe.com"] ["STRIPE_KEY"] ["DemoDb"] ["/app.0123456789ab.mjs", "/index.html"]
    let svcPath (k : DeployKey) (r : GcpRegion := .us_central1) := s!"/v2/{cloudRunServicePath k r}"
    let hasBind (pol : IamPolicyDoc) (role member : String) := pol.bindings.any fun e => e.role == role && e.members.contains member
    let hasReq (st : MockGcpState) (m sub : String) := st.reqs.any fun r => r.method == m && r.target.contains sub
    let polOf (st : MockGcpState) (k : String) := (st.iamPolicies.lookup k).getD {}
    let obs (p := plan) (k := prodKey) := observeGcpState cfg k p.managedDbs p.regions p.assetsArePublic
    let edgeMember := s!"serviceAccount:{cfg.edgeSaEmail}"
    testPureCloudValidators c cfg prodKey plan
    withTempDir "qed-cloud-deploy" fun tmpDir => do
      let roll (p : GcpPlan) (img : String) (o : GcpObservedState := { key := p.key }) := executeRollout cfg p img tmpDir (planRollout o p)
      let boundaryPayload := "console.log('--qed_gcs_multipart_boundary--');\n"
      IO.FS.writeFile (System.FilePath.mk tmpDir / "app.0123456789ab.mjs") boundaryPayload
      IO.FS.writeFile (System.FilePath.mk tmpDir / "index.html") "<!doctype html><html></html>\n"
      let staleSecId := secretId prodKey "OLD_KEY"
      let (staleSecPath, projIamPath, bucketIamPath, egPath) := (s!"/v1/{secretResourcePath prodKey "OLD_KEY"}",
        s!"/v3/projects/{prodKey.shard.prodProjectId}", s!"/storage/v1/b/{assetBucketName prodKey true}/iam", s!"/v1/{egressPolicyPath prodKey .us_central1}")
      stRef.modify fun s => { s with
        force412Once := true, pending := (true, false, true), sql409InProgOnce := true, secrets := [(prodKey.shard.prodProjectId, staleSecId)],
        iamPolicies := [(staleSecPath, { etag := "etag-seed-0", bindings := [{ role := GcpRole.secretManagerAccessor.gcpName, members := [s!"serviceAccount:{renderSaEmail prodKey}"] }] }),
          (projIamPath, {
            etag := "etag-proj-0", auditConfigs? := some (.arr [.obj [("service", .str "allServices")]]),
            bindings := [{ role := "roles/logging.viewer", members := ["user:ops@qed.dev"], condition? := some (.obj [("title", .str "temp-access"), ("expression", .str "request.time < timestamp('2030-01-01T00:00:00Z')")]) }] })],
        egress := [(egPath, .obj [("allowedOrigins", toJson (["https://legacy.example.com"] : List String))])] }
      -- 1. Full 4-phase rollout
      c.expectOk "observeGcpState before rollout" (← obs) fun snap0 => do
        let actions := planRollout snap0.observed plan
        c.expectOk "executeRollout 4-phase prod succeeds (including 412 ETag retry)" (← executeRollout cfg plan "img:v1" tmpDir actions) fun n => do
          c.checkEq "executed all planned actions" n actions.length; let st ← stRef.get; let projPol := polOf st projIamPath
          for (lbl, ok) in [
              ("GCS collision-free multipart hashed asset uploaded intact (with old boundary string inside)", st.uploads.any fun u => u.bucket == assetBucketName prodKey true && u.name.endsWith "app.0123456789ab.mjs" && u.cacheControl == "public, max-age=31536000, immutable" && u.content == boundaryPayload && u.boundary != "qed_gcs_multipart_boundary"),
              ("GCS multipart index.html has must-revalidate", st.uploads.any fun u => u.name.endsWith "index.html" && u.cacheControl == "public, max-age=0, must-revalidate"),
              ("GCS public bucket binds allUsers roles/storage.legacyObjectReader (not objectViewer)", hasBind (polOf st bucketIamPath) "roles/storage.legacyObjectReader" "allUsers"),
              ("Cloud Run final state (livePct=100, concurrency=1000, env=prod, VPC_EGRESS_ALL_TRAFFIC)", match st.services.lookup (svcPath prodKey) with | some sv => sv.live.2 == 100 && sv.conc == 1000 && sv.s "env" == "prod" && sv.s "vpc" == "VPC_EGRESS_ALL_TRAFFIC" | none => false),
              ("Cloud SQL IAM service account user provisioned for prodKey", st.sqlUsers.any fun (_, u) => u == sqlIamUserName prodKey),
              ("Phase 4 deleted stale OLD_KEY & narrowed egress with SWP CEL sessionMatcher", !st.secrets.contains (prodKey.shard.prodProjectId, staleSecId) && match st.egress.lookup egPath with | some egJ => parseEgressPolicy egJ == ["https://api.stripe.com"] && (Json.render egJ).contains "host() == 'api.stripe.com'" | none => false),
              ("IAM condition & auditConfigs preserved across setIamPolicy", projPol.auditConfigs?.isSome && projPol.bindings.any fun e => e.role == "roles/logging.viewer" && e.condition?.isSome),
              ("proto3 default-omitted `done` Cloud Run LRO polled before healthCheck", hasReq st "GET" "/operations/op-1"),
              ("Cloud SQL v1 sql#operation LRO polled (after 409 operationInProgress retry)", st.reqs.any fun r => r.method == "GET" && r.target.contains "/v1/projects/" && r.target.endsWith "/operations/sql-op-1")] do c.check lbl ok
          let idxs := [fun r : MockReq => r.method == "PUT" && r.target == egPath && r.body.contains "legacy.example.com",
            fun r => r.method == "PATCH" && r.target.contains "allowMissing=true", fun r => r.method == "GET" && r.target == "/_qed/health",
            fun r => r.method == "PATCH" && r.target.contains "updateMask=traffic", fun r => r.method == "DELETE" && r.target.endsWith staleSecId,
            fun r => r.method == "PUT" && r.target == egPath && !r.body.contains "legacy.example.com"].map st.reqs.findIdx?
          match idxs with
          | [some w, some d, some h, some s, some del, some nr] => c.check "strict 4-phase wire order (P1 widen < P2 deploy < P2 health < P3 shift < P4 delete & narrow)" (w < d && d < h && h < s && s < del && s < nr)
          | _ => c.check "all 4-phase wire requests recorded" false
      -- 2. Comprehensive Drift Detection (Clean + Round 1 + Round 2 + 404 deleted egress)
      c.expectOk "observeGcpState post-rollout clean" (← obs) fun snapClean => c.checkEq "zero drift on clean post-rollout state" (checkDriftLive snapClean plan) []
      let (runKey, runDenyKey, secDenyKey) := (svcPath prodKey, denyKeyFor prodKey.shard.prodProjectId "deny-qed-run-public", denyKeyFor prodKey.shard.prodProjectId "deny-qed-secrets-public")
      let cleanSnap ← stRef.get
      stRef.modify fun s =>
        let runPol := (polOf s runKey).addBinding GcpRole.runInvoker.gcpName "allUsers" |>.addBinding "roles/run.admin" "user:attacker@evil.dev"
        let runPolCond : IamPolicyDoc := { runPol with bindings := runPol.bindings ++ [{ role := GcpRole.runInvoker.gcpName, members := ["allUsers"], condition? := some (.obj [("title", .str "backdoor"), ("expression", .str "true")]) }] }
        { modSvc s runKey (fun sv => { sv with invokerIamDisabled := true }) with
          iamPolicies := setAssocs s.iamPolicies [(runKey, runPolCond), (projIamPath, (polOf s projIamPath).addBinding "roles/owner" "user:backdoor@evil.dev"), (bucketIamPath, (polOf s bucketIamPath).addBinding GcpRole.storageObjectAdmin.gcpName "allUsers")]
          denyPolicies := s.denyPolicies.filter (·.1 != runDenyKey), secrets := s.secrets ++ [(prodKey.shard.prodProjectId, secretId prodKey "ROGUE_SECRET")] }
      c.expectOk "observeGcpState after comprehensive drift injection" (← obs) fun snapDrift => do
        let fs := checkDriftLive snapDrift plan
        for (lbl, want) in [("allUsers run.invoker", DriftFinding.unauthorizedBinding { principal := .allUsers, role := .runInvoker, resource := .cloudRun prodKey }),
            ("conditional allUsers backdoor on Cloud Run", .unauthorizedRawBinding "allUsers" "roles/run.invoker[conditional]" (.cloudRun prodKey)),
            ("unrecognized privileged roles/run.admin", .unauthorizedRawBinding "user:attacker@evil.dev" "roles/run.admin" (.cloudRun prodKey)),
            ("project-level roles/owner", .unauthorizedRawBinding "user:backdoor@evil.dev" "roles/owner" (.project prodKey.shard.prodProjectId)),
            ("Cloud Run invokerIamDisabled: true", .unsafeCloudRunSpec .us_central1 "invokerIamDisabled is true"),
            ("GCS allUsers storageObjectAdmin", .unauthorizedBinding { principal := .allUsers, role := .storageObjectAdmin, resource := .assetPrefix prodKey "_bucket" true }),
            ("deleted deny-qed-run-public policy", .missingDenyPolicy "deny-qed-run-public"), ("rogue secret", .extraSecret "ROGUE_SECRET")] do
          c.check s!"checkDriftLive catches {lbl}" (fs.contains want)
      let mkDeny (etag perm : String) (extra : List (String × Json)) : Json :=
        .obj [("etag", .str etag), ("rules", .arr [.obj [("denyRule", .obj ([("deniedPrincipals", toJson (["principalSet://goog/public:all"] : List String)), ("deniedPermissions", toJson ([perm] : List String))] ++ extra))]])]
      let mkVol (nm k : String) (v : Json) : Json := .obj [("name", .str nm), (k, v)]
      let jRule (m : String) (extra : List (String × Json) := []) : Json := .obj ([("enabled", .bool true), ("basicProfile", .str "ALLOW"), ("sessionMatcher", .str m)] ++ extra)
      stRef.modify fun s =>
        let projPol := [(GcpRole.cloudSqlClient.gcpName, "serviceAccount:q-7-3-r42@qed-nonprod.iam.gserviceaccount.com"), ("projects/qed-prod/roles/backdoor", "user:custom@evil.dev"),
          ("roles/iam.serviceAccountTokenCreator", "user:impersonator@evil.dev"), ("roles/artifactregistry.writer", "user:supplychain@evil.dev"), ("roles/viewer", "user:snooper@evil.dev")].foldl (fun p (r, m) => p.addBinding r m) (polOf s projIamPath)
        { modSvc s runKey (fun sv => { sv with
            invokerIamDisabled := false, revs := (some "cr-7-3-p-newrev", some "cr-7-3-p-newrev"),
            jls := setAssocs sv.jls [("vpc", [.obj [("network", .str "default"), ("subnetwork", .str "default")]]),
              ("vol", [mkVol "leak" "secret" (.obj [("secret", .str "LEAKED_VOL_SECRET")]), mkVol "exfil-secret-to-dist" "secret" (.obj [("secret", .str (secretId prodKey "STRIPE_KEY"))]),
                mkVol "sql-backdoor" "cloudSqlInstance" (.obj [("instances", .arr [.str "other-prod:us-central1:victim-db"])]),
                mkVol "gcs-backdoor" "gcs" (.obj [("bucket", .str "sensitive-prod-bucket")]), mkVol "nfs-backdoor" "nfs" (.obj [("server", .str "10.0.0.5"), ("path", .str "/export")])]),
              ("mnt", [.obj [("name", .str "exfil-secret-to-dist"), ("mountPath", .str "/app/dist")]]),
              ("cmd", [.str "/bin/sh", .str "-c"]), ("args", [.str "cat /secrets/*"]), ("extra", [.obj [("image", .str "evil/sidecar:latest")]]),
              ("env", [("QED_DEPLOY_ENV", "preview"), ("QED_INSECURE_SKIP_TLS_VERIFY", "1"), ("QED_AUTH_SECRET", "forged-hmac-key"), ("QED_AUTH_ISSUER", "https://attacker.example"),
                ("DATABASE_URL", "postgres://attacker.example/db"), ("HOST", "127.0.0.1"), ("STRIPE_KEY", "sk_attacker_plaintext")].map fun (k, v) => .obj [("name", .str k), ("value", .str v)]),
              ("tr", sv.jl "tr" ++ [.obj [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_REVISION"), ("revision", .str "cr-7-3-p-old-unsafe"), ("percent", toJson (0 : Nat)), ("tag", .str "backdoor")]])] }) with
          iamPolicies := setAssoc s.iamPolicies projIamPath projPol
          denyPolicies := setAssocs s.denyPolicies [(runDenyKey, mkDeny "deny-bad-1" GcpPermission.runInvoke.gcpV2Name [("denialCondition", .obj [("expression", .str "false")])]),
            (secDenyKey, mkDeny "deny-bad-2" GcpPermission.secretAccessor.gcpV2Name [("exceptionPrincipals", toJson (["principalSet://goog/public:all"] : List String))])]
          egress := setAssoc s.egress egPath (.obj [("rules", .arr [jRule "host() == 'api.stripe.com'" [("description", .str "https://api.stripe.com")], jRule "true"])]) }
      c.expectOk "observeGcpState after Round 2 drift injection" (← obs) fun snapR2 => do
        let fsR2 := checkDriftLive snapR2 plan; let hasUnsafe (sub : String) := fsR2.any fun | .unsafeCloudRunSpec .us_central1 d => d.contains sub | _ => false
        for (lbl, want) in [("poisoned denialCondition on deny-qed-run-public", DriftFinding.missingDenyPolicy "deny-qed-run-public"),
            ("poisoned public exceptionPrincipals on deny-qed-secrets-public", .missingDenyPolicy "deny-qed-secrets-public"), ("wildcard CEL ALLOW rule in SWP egress", .extraEgress "<unsafe-cel-rule:true>")] do
          c.check s!"checkDriftLive catches {lbl}" (fsR2.contains want)
        c.check "checkDriftLive catches cross-project q-* SA granted roles/cloudsql.client on prod" (fsR2.any fun | .unauthorizedBinding b => b.role == .cloudSqlClient && b.principal == .external "serviceAccount:q-7-3-r42@qed-nonprod.iam.gserviceaccount.com" | _ => false)
        c.check "checkDriftLive catches custom project role, serviceAccountTokenCreator, artifactregistry.writer, & roles/viewer"
          ([("user:custom@evil.dev", "projects/qed-prod/roles/backdoor"), ("user:impersonator@evil.dev", "roles/iam.serviceAccountTokenCreator"),
            ("user:supplychain@evil.dev", "roles/artifactregistry.writer"), ("user:snooper@evil.dev", "roles/viewer")].all fun (m, r) => fsR2.contains (.unauthorizedRawBinding m r (.project prodKey.shard.prodProjectId)))
        c.check "checkDriftLive catches vpcAccess, volumes/mounts, command/args, sidecar, stale rev, forbidden envs, tagged route, & QED_DEPLOY_ENV"
          (["vpcAccess.networkInterfaces", "LEAKED_VOL_SECRET", "secret:exfil-secret-to-dist", "exfil-secret-to-dist:/app/dist", "cloudSqlInstance:sql-backdoor", "gcs:gcs-backdoor", "nfs:nfs-backdoor", "command/args override", "container",
            "QED_INSECURE_SKIP_TLS_VERIFY", "QED_AUTH_SECRET", "QED_AUTH_ISSUER", "DATABASE_URL", "HOST", "STRIPE_KEY", "QED_DEPLOY_ENV"].all hasUnsafe &&
           (hasUnsafe "latestReadyRevision" || hasUnsafe "serving traffic") && fsR2.any fun | .unsafeCloudRunSpec .us_central1 d => d.contains "backdoor" && d.contains "tagged traffic route" | _ => false)
      stRef.modify fun s => { s with egress := s.egress.filter (·.1 != egPath) }
      let planNoEgress := mkTestPlan prodKey "abc123def456" [.us_central1] [] ["STRIPE_KEY"] ["DemoDb"] []
      c.expectOk "observeGcpState with deleted egress policy" (← obs planNoEgress) fun snapNoEg => c.check "checkDriftLive catches 404 deleted egress policy even with empty egressAllow" ((checkDriftLive snapNoEg planNoEgress).contains (.missingRegionalEgressPolicy .us_central1))
      stRef.modify fun s => { s with services := cleanSnap.services, denyPolicies := cleanSnap.denyPolicies, egress := cleanSnap.egress, iamPolicies := cleanSnap.iamPolicies, secrets := cleanSnap.secrets }
      -- 3. Multi-region drift, 1 -> 2 scaling, & partial Phase 3 compensating rollback
      let plan2Reg := mkTestPlan prodKey "rev2reg" [.us_central1, .europe_west1] ["https://api.stripe.com"] ["STRIPE_KEY"] ["DemoDb"] []
      c.expectOk "observe 2-region state before scaling" (← obs plan2Reg) fun snap2 => do
        let fs2 := checkDriftLive snap2 plan2Reg
        c.check "multi-region drift catches missing europe_west1 Cloud Run binding & egress" (fs2.contains (.missingRegionalBinding .europe_west1 { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun prodKey }) && fs2.contains (.missingRegionalEgress .europe_west1 "https://api.stripe.com"))
        c.expectOk "scale rollout to europe_west1 provisions IAM & service" (← roll plan2Reg "img:v2" snap2.observed) fun _ => do
          c.check "europe_west1 granted edgeRouter run.invoker" (hasBind (polOf (← stRef.get) (svcPath prodKey .europe_west1)) GcpRole.runInvoker.gcpName edgeMember)
      stRef.modify fun s => { s with failShiftRegion? := some "europe-west1" }
      let rbRes ← roll (mkTestPlan prodKey "rev3fail" [.us_central1, .europe_west1] ["https://api.stripe.com"] ["STRIPE_KEY"] ["DemoDb"] []) "img:v3"
      stRef.modify fun s => { s with failShiftRegion? := none }
      c.checkErrContains "multi-region partial Phase 3 failure returns error with compensating rollback note" rbRes "compensating rollback"
      c.check "compensating rollback restored us-central1 traffic back to rev2reg at 100%" (match (← stRef.get).services.lookup (svcPath prodKey .us_central1) with | some sv => sv.live == (cloudRunRevisionName prodKey "rev2reg", 100) | none => false)
      -- 4. Tampered candidate URI & 5. Symlink escape rejected
      stRef.modify (modSvc · runKey fun sv => { sv with cand := (cloudRunRevisionName prodKey "rev2reg", sv.cand.2), uris := (some "https://evil.example", sv.uris.2) })
      c.checkErrContains "executeAction healthCheck rejects tampered candUrl (https://evil.example)" (← executeAction { cfg with healthBaseUrl? := none } plan2Reg "img:v2" tmpDir none (.healthCheck prodKey "rev2reg")) "untrusted candidate/base URI"
      stRef.modify (modSvc · runKey fun sv => { sv with uris := (none, sv.uris.2) })
      withTempDir "qed-outside-secret" fun outsideDir => do
        IO.FS.writeFile (System.FilePath.mk outsideDir / "secret.mjs") "export const secret = 'LEAKED';\n"
        withSymlink s!"{outsideDir}/secret.mjs" s!"{tmpDir}/evil.mjs" do
          c.checkErrContains "uploadAssets blocks symlink resolving outside distDir" (← executeAction cfg plan "img:v1" tmpDir none (.uploadAssets prodKey "abc123def456" ["/evil.mjs"])) "symlink/path escape blocked"
      -- 6. Partial DB removal preserves runtimeSa roles/cloudsql.client & revokes allUsers
      let (plan2Db, plan1Db) := (mkTestPlan prodKey "db2" [.us_central1] [] [] ["Db1", "Db2"] [], mkTestPlan prodKey "db1" [.us_central1] [] [] ["Db1"] [])
      c.expectOk "deploy 2-DB plan" (← roll plan2Db "img:db2") fun _ => do
        stRef.modify fun s => { s with iamPolicies := setAssoc s.iamPolicies projIamPath ((polOf s projIamPath).addBinding GcpRole.cloudSqlClient.gcpName "allUsers") }
        c.expectOk "observe 2-DB state" (← obs plan2Db) fun snapDb => do
          c.expectOk "drop Db2 while keeping Db1" (← roll plan1Db "img:db1" snapDb.observed) fun _ => do
            let projPol := polOf (← stRef.get) projIamPath
            c.check "partial DB removal keeps runtimeSa roles/cloudsql.client AND revokes allUsers" (hasBind projPol GcpRole.cloudSqlClient.gcpName s!"serviceAccount:{renderSaEmail prodKey}" && !hasBind projPol GcpRole.cloudSqlClient.gcpName "allUsers")
      -- 7. Abort-on-failed-healthcheck (existing service + first-deploy & retry)
      stRef.modify fun s => { s with reqs := #[], healthStatus := 500 }
      let planBad := mkTestPlan prodKey "bad999" [.us_central1] ["https://api.stripe.com"] ["STRIPE_KEY"] ["DemoDb"] []
      c.check "executeRollout aborts on /_qed/health 500" (!(← roll planBad "img:bad" { key := prodKey, secretNames := ["OLD_ABORT_SECRET"], egressAllow := ["https://old-abort.example.com"] }).isOk)
      let stAbort ← stRef.get
      c.check "aborted rollout NEVER shifts traffic or deletes old secrets" (!hasReq stAbort "PATCH" "updateMask=traffic" && !hasReq stAbort "DELETE" "OLD_ABORT_SECRET")
      c.check "aborted rollout keeps existing live revision at 100% and candidate at 0%" (match stAbort.services.lookup runKey with | some sv => sv.live.2 == 100 && sv.cand == (cloudRunRevisionName prodKey "bad999", 0) | none => false)
      let freshKey : DeployKey := { shard, tenant := ⟨99, by decide⟩, app := ⟨1, by decide⟩, env := .prod }
      for (lbl, rev) in [("first-deploy", "firstfail1"), ("retry after failed first-deploy", "firstfail2")] do
        c.check s!"{lbl} aborts on /_qed/health 500" (!(← roll (mkTestPlan freshKey rev [.us_central1] [] ["FIRST_KEY"] [] []) s!"img:{rev}").isOk)
        c.check s!"{lbl} leaves edgeRouter ungranted" (!hasBind (polOf (← stRef.get) (svcPath freshKey)) GcpRole.runInvoker.gcpName edgeMember)
      -- 8. Private team_only preview + sibling PR #43 + PR #42 preview teardown + prod teardown no-op
      stRef.modify fun s => { s with reqs := #[], uploads := [], healthStatus := 200 }
      let (prevKey42, prevKey43) : DeployKey × DeployKey := ({ prodKey with env := .preview ⟨42, by decide⟩ }, { prodKey with env := .preview ⟨43, by decide⟩ })
      let prevPlan42 := mkTestPlan prevKey42 "prev42aa" [.us_central1] ["https://api.stripe.com"] ["PREV_TOKEN"] ["DemoDb", "ExtraDb"] ["/app.0123456789ab.mjs"] .team_only
      let prevPlan43 := mkTestPlan prevKey43 "prev43bb" [.us_central1] [] ["PREV_TOKEN"] [] []
      c.check "team_only preview plan uses private assets" (!prevPlan42.assetsArePublic)
      c.expectOk "deploy PR #42 team_only preview" (← roll prevPlan42 "img:pr42") fun _ => do
        let st42 ← stRef.get; let privBucket := assetBucketName prevKey42 false
        c.check "team_only preview uploads to private bucket with private Cache-Control" (st42.uploads.any fun u => u.bucket == privBucket && u.cacheControl.startsWith "private,")
        let privPol := polOf st42 s!"/storage/v1/b/{privBucket}/iam"
        c.check "team_only preview binds edgeRouter (NOT allUsers) on private bucket" (hasBind privPol "roles/storage.legacyObjectReader" edgeMember && !privPol.bindings.any (·.members.contains "allUsers"))
        c.expectOk "deploy PR #43 preview" (← roll prevPlan43 "img:pr43") fun _ => do
          let nonProdSecDenyKey := denyKeyFor prodKey.shard.nonProdProjectId "deny-qed-secrets-public"
          let getExcs (st : MockGcpState) := (st.denyPolicies.lookup nonProdSecDenyKey).map parseDenyExceptionPrincipals |>.getD []
          let excsBefore := getExcs (← stRef.get)
          c.check "non-prod deny-qed-secrets-public contains both PR #42 and PR #43 SAs" (excsBefore.any (·.contains (renderSaEmail prevKey42)) && excsBefore.any (·.contains (renderSaEmail prevKey43)))
          c.expectOk "observe PR #42 preview" (← obs prevPlan42 prevKey42) fun prevSnap => do
            stRef.modify fun s => { s with reqs := #[], pending := (s.pending.1, true, s.pending.2.2) }
            c.expectOk "execute PR #42 preview teardown" (← executeRollout cfg { prevPlan42 with managedDbs := [] } "" tmpDir (planPreviewTeardown prevSnap.observed)) fun _ => do
              let stTd ← stRef.get; let excsAfter := getExcs stTd
              let dbDropIdxs := stTd.reqs.zipIdx.filterMap fun (r, idx) => if r.method == "DELETE" && r.target.contains "/databases/" then some idx else none
              let userDropIdxs := stTd.reqs.zipIdx.filterMap fun (r, idx) => if r.method == "DELETE" && r.target.contains "/users?name=" then some idx else none
              for (lbl, ok) in [
                  ("preview service, secret, both DBs, SQL IAM user, egress policy, & runtime SA all deleted",
                    (stTd.services.lookup (svcPath prevKey42)).isNone && !stTd.secrets.contains (prevKey42.shard.nonProdProjectId, secretId prevKey42 "PREV_TOKEN") &&
                    !stTd.dbs.any (fun (_, d) => d == sqlDbName prevKey42 "DemoDb" || d == sqlDbName prevKey42 "ExtraDb") &&
                    !stTd.sqlUsers.any (fun (_, u) => u == sqlIamUserName prevKey42) && (stTd.egress.lookup s!"/v1/{egressPolicyPath prevKey42 .us_central1}").isNone && !stTd.sas.contains (renderSaEmail prevKey42)),
                  ("preview teardown polls Cloud Run deleteService LRO", hasReq stTd "GET" "/operations/del-op-1"),
                  ("multi-DB preview teardown deletes SQL IAM user once AFTER last DB drop", dbDropIdxs.size == 2 && userDropIdxs.size == 1 && dbDropIdxs.all (· < userDropIdxs[0]!)),
                  ("preview teardown prunes PR #42 SA from deny-qed-secrets-public while keeping PR #43 SA", !excsAfter.any (·.contains (renderSaEmail prevKey42)) && excsAfter.any (·.contains (renderSaEmail prevKey43)))] do c.check lbl ok
      stRef.modify fun s => { s with reqs := #[] }
      let prodTd := planPreviewTeardown { key := prodKey, secretNames := ["STRIPE_KEY"], managedDbs := ["DemoDb"] }
      c.checkEq "prod teardown is strict no-op (0 actions)" prodTd []
      c.expectOk "prod teardown executes 0 steps / 0 HTTP calls" (← executeRollout cfg plan "" tmpDir prodTd) fun n => do c.checkEq "prod teardown 0 steps & 0 reqs" (n, (← stRef.get).reqs.size) (0, 0)
      testCliDeployChecks c baseUrl

private structure MockCloudState where
  reqs          : Array (String × String × Option String × String) := #[]
  failRevoke    : Bool := false
  lastSecretSet : Option SecretSetReq := none
  lastSecretDel : Option SecretDeleteReq := none
  lastCancel    : Option CancelDeployReq := none
deriving Inhabited

private def handleMockCloudApi (stRef : IO.Ref MockCloudState)
    (method target : String) (hdrs : Array (String × String)) (body : ByteArray) : IO (Nat × String × ByteArray) := do
  let bodyStr := utf8Str body
  let authHdr := getHeader? hdrs "authorization"
  let (path, query) := splitPathQuery target
  stRef.modify fun s => { s with reqs := s.reqs.push (method, target, authHdr, bodyStr) }
  if authHdr.isNone then return jsonErrResp 401 "missing bearer token"
  if method == "GET" && path == "/api/v1/whoami" then
    return jsonResp 200 (toJson ({ userId := "u_ci", email := "ci@qed.cloud", tenantId := 7, appsCount := 2 } : WhoamiResp))
  if method == "POST" && path == "/api/v1/tokens/revoke-current" then
    if (← stRef.get).failRevoke then return jsonErrResp 500 "simulated revoke outage"
    return jsonResp 200 (toJson ({ revoked := true } : TokenRevokeResp))
  if method == "GET" && path == "/api/v1/secrets" then
    let q := Qed.Auth.parseQueryParams query
    let slug := (q.lookup "app").getD ""
    return jsonResp 200 (toJson ({ appSlug := slug, names := #["prod:API_KEY", "staging:STAGE_KEY"] } : SecretsListResp))
  if method == "POST" && path == "/api/v1/secrets" then
    match Json.parse bodyStr >>= (fromJson : Json → Except String SecretSetReq) with
    | .ok req => stRef.modify fun s => { s with lastSecretSet := some req }; return jsonResp 200 (.obj [("ok", .bool true)])
    | .error e => return jsonErrResp 400 e
  if method == "POST" && path == "/api/v1/secrets/delete" then
    match Json.parse bodyStr >>= (fromJson : Json → Except String SecretDeleteReq) with
    | .ok req => stRef.modify fun s => { s with lastSecretDel := some req }; return jsonResp 200 (.obj [("ok", .bool true)])
    | .error e => return jsonErrResp 400 e
  if method == "POST" && path == "/api/v1/deployment/cancel" then
    match Json.parse bodyStr >>= (fromJson : Json → Except String CancelDeployReq) with
    | .ok req => stRef.modify fun s => { s with lastCancel := some req }; return jsonResp 200 (.obj [("ok", .bool true), ("status", .str "canceled")])
    | .error e => return jsonErrResp 400 e
  if method == "GET" && path == "/api/v1/deployment" then
    let depId := ((Qed.Auth.parseQueryParams query).lookup "id").getD "dep_canceled_1"
    return jsonResp 200 (toJson ({
      id := depId, appSlug := "my-app", env := "prod", pr := 0, status := "canceled",
      url := "", buildHash := "", verifiedDecls := 0, errorMsg := "canceled by user",
      createdAt := 1, updatedAt := 2, logs := #[{ seq := 1, ts := 2, level := "error", message := "Deployment canceled" }] } : DeploymentView))
  if method == "GET" && path == "/api/v1/logs/runtime" then
    let q := Qed.Auth.parseQueryParams query
    let resp : RuntimeLogsResp := {
      appSlug := (q.lookup "app").getD "my-app", env := (q.lookup "env").getD "prod",
      pr := ((q.lookup "pr").bind String.toNat?).getD 0,
      logs := #[{ id := "rt_1", timestamp := "2026-11-25 12:00:00 UTC", severity := "error", source := "http", message := "GET /boom -> 500 (12ms)" }],
      nextPageToken := some "next_tok" }
    return jsonResp 200 (toJson resp)
  return jsonErrResp 404 s!"unhandled mock cloud route {method} {target}"

private def testCloudProtocolAndCli (c : TestChecker) : IO Unit := do
  -- 1. Pure Protocol tests: base64, static assets, SourceBundle, new request/response types
  let b64LengthsOk := (List.range 65).all fun n =>
    let bs := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat ((i * 73 + 19) % 256))
    decodeBase64? (encodeBase64 bs) == some bs
  let pngMagic := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0xFF, 0xFE]
  let legacySfJson := "{\"path\":\"App.lean\",\"content\":\"def x := 1\"}"
  let legacySf : Except String SourceFile := Json.parse legacySfJson >>= fromJson
  let binSf : SourceFile := { path := "public/logo.png", content := encodeBase64 pngMagic, encoding := "base64" }
  let mixedBundle : SourceBundle := { files := #[{ path := "App.lean", content := "def x := 1" }, binSf] }
  let delReq : SecretDeleteReq := { appSlug := "my-app", env := "staging", name := "API_KEY" }
  let cancelReq : CancelDeployReq := { deploymentId := "dep_abc123" }
  let rtResp : RuntimeLogsResp := {
    appSlug := "my-app", env := "preview", pr := 42,
    logs := #[{ id := "l1", timestamp := "2026-11-25 12:00:00 UTC", severity := "warn", source := "stderr", message := "slow query" }],
    nextPageToken := some "p2" }
  let rtMinJson := "{\"appSlug\":\"my-app\",\"env\":\"prod\",\"logs\":[]}"
  let rtMinDec : Except String RuntimeLogsResp := Json.parse rtMinJson >>= fromJson
  let revResp : TokenRevokeResp := { revoked := true }
  for (lbl, ok) in [
      ("encodeBase64/decodeBase64? round-trips lengths 0..64 & PNG magic bytes", b64LengthsOk && decodeBase64? (encodeBase64 pngMagic) == some pngMagic),
      ("decodeBase64? rejects invalid & non-canonical padded base64 inputs",
        ["abc", "a", "ab!d", "AA==AAAA", "====", "ab cd", "AB==", "AP==", "AAB=", "///=", "//=="].all fun s => (decodeBase64? s).isNone),
      ("maxSourceFileBytes = 2 MiB & maxTotalSourceBytes = 16 MiB", maxSourceFileBytes == 2 * 1024 * 1024 && maxTotalSourceBytes == 16 * 1024 * 1024),
      ("isValidDeployStatus accepts canceled and rejects invalid", isValidDeployStatus "canceled" && isValidDeployStatus "live" && !isValidDeployStatus "bogus"),
      ("isValidDeploymentId requires ASCII alphanumeric start and rejects leading `-`",
        ["dep_abc-1", "0123", "A_b-9"].all isValidDeploymentId && ["", "-bad", "--help", "_bad", "dep/bad"].all (!isValidDeploymentId ·)),
      ("isValidSourceRelPath allows all static web assets and config files",
        ["App.lean", "a.css", "a.html", "a.js", "a.mjs", "a.json", "a.txt", "a.xml", "site.webmanifest",
         "a.png", "A.PNG", "a.jpg", "a.jpeg", "a.gif", "a.svg", "a.webp", "a.ico",
         "f.woff", "f.woff2", "f.ttf", "f.otf", "lean-toolchain", "lakefile.lean", "lakefile.toml",
         "lake-manifest.json", "qed.json", "robots.txt", "sitemap.xml", "manifest.json"].all isValidSourceRelPath),
      ("isValidSourceRelPath enforces all security blocks & rejects all dotfiles/dot-dirs",
        ["../a.png", "a/../b.png", "./a.png", ".env", ".env.prod", ".env.json", ".ENV.local",
         ".git/HEAD.txt", ".lake/a.lean", ".qed/x.json", ".config/qed/credentials.json",
         ".docker/config.json", ".ssh/id_rsa.txt", ".htaccess.txt", "..png", ".a.png",
         "public/.png", "public/.a.png", "dist/a.js", "sub/dist/a.js",
         "node_modules/p/i.js", "target/a.txt", "/abs.png", "a\\b.png", "a.png?v=1", "a.png#h",
         "a:b.png", "a\nb.png", ".png", ".lean"].all (!isValidSourceRelPath ·)),
      ("isBinarySourceExt inspects leaf segment and rejects dotfile stems",
        ["a.png", "public/logo.png", "a.woff2", "a.ico", "A.JPG"].all isBinarySourceExt &&
        ["App.lean", "a.css", "a.svg", "a.json", "robots.txt", ".png", "public/.png", "public/.a.png"].all (!isBinarySourceExt ·)),
      ("SourceFile backwards-compat FromJson defaults omitted encoding to utf8",
        legacySf == .ok { path := "App.lean", content := "def x := 1", encoding := "utf8" }),
      ("SourceBundle mixed utf8 + base64 JSON round-trip & decodedBytes",
        (Json.parse (toJson mixedBundle).render >>= fromJson) == .ok mixedBundle && binSf.decodedBytes == .ok pngMagic),
      ("SourceBundle.validate rejects bad encoding, bad base64, & empty/no-lean bundles",
        !({ files := #[{ path := "App.lean", content := "x", encoding := "hex" }] } : SourceBundle).validate.isOk &&
        !({ files := #[{ path := "App.lean", content := "x" }, { path := "logo.png", content := "not!b64", encoding := "base64" }] } : SourceBundle).validate.isOk &&
        !({ files := #[{ path := "App.lean", content := "x" }, { path := "logo.png", content := "AB==", encoding := "base64" }] } : SourceBundle).validate.isOk &&
        !({ files := #[binSf] } : SourceBundle).validate.isOk),
      ("SecretDeleteReq JSON round-trip, default env, & validation",
        (Json.parse (toJson delReq).render >>= fromJson) == .ok delReq &&
        (Json.parse "{\"appSlug\":\"my-app\",\"name\":\"API_KEY\"}" >>= (fromJson : Json → Except String SecretDeleteReq)) == .ok { appSlug := "my-app", env := "prod", name := "API_KEY" } &&
        !(Json.parse "{\"appSlug\":\"BAD\",\"env\":\"prod\",\"name\":\"API_KEY\"}" >>= (fromJson : Json → Except String SecretDeleteReq)).isOk &&
        !(Json.parse "{\"appSlug\":\"my-app\",\"env\":\"dev\",\"name\":\"API_KEY\"}" >>= (fromJson : Json → Except String SecretDeleteReq)).isOk &&
        !(Json.parse "{\"appSlug\":\"my-app\",\"env\":\"prod\",\"name\":\"bad_key\"}" >>= (fromJson : Json → Except String SecretDeleteReq)).isOk),
      ("CancelDeployReq JSON round-trip & validation",
        (Json.parse (toJson cancelReq).render >>= fromJson) == .ok cancelReq &&
        !(Json.parse "{\"deploymentId\":\"\"}" >>= (fromJson : Json → Except String CancelDeployReq)).isOk &&
        !(Json.parse "{\"deploymentId\":\"-bad\"}" >>= (fromJson : Json → Except String CancelDeployReq)).isOk &&
        !(Json.parse "{\"deploymentId\":\"dep/bad?x=1\"}" >>= (fromJson : Json → Except String CancelDeployReq)).isOk),
      ("RuntimeLogsResp & TokenRevokeResp JSON round-trips (incl. omitted optional fields)",
        (Json.parse (toJson rtResp).render >>= fromJson) == .ok rtResp &&
        rtMinDec == .ok { appSlug := "my-app", env := "prod", pr := 0, logs := #[], nextPageToken := none } &&
        (Json.parse (toJson revResp).render >>= fromJson) == .ok revResp),
      ("defaultCloudApiUrl? is https://api.qed.cloud and passes isValidCloudApiUrl",
        Qed.Cli.defaultCloudApiUrl? == some "https://api.qed.cloud" && isValidCloudApiUrl "https://api.qed.cloud"),
      ("splitSecretAssignment preserves `=` inside secret values",
        Qed.Cli.splitSecretAssignment "API_KEY=sk_123" == some ("API_KEY", "sk_123") &&
        Qed.Cli.splitSecretAssignment "DB_URL=postgres://u:p@h/d?a=1&b=2" == some ("DB_URL", "postgres://u:p@h/d?a=1&b=2") &&
        Qed.Cli.splitSecretAssignment "B64=AAEC/w==" == some ("B64", "AAEC/w==") &&
        Qed.Cli.splitSecretAssignment "NO_EQUALS" == none),
      ("parseSecretsSetArgs handles all CLI forms, --value=, redaction, & ambiguous --value",
        Qed.Cli.parseSecretsSetArgs ["my-app", "KEY", "--env", "staging", "--value", "v1"] == .ok { appSlug := "my-app", env := "staging", name := "KEY", value? := some "v1" } &&
        Qed.Cli.parseSecretsSetArgs ["my-app", "KEY", "--value=v1=eq"] == .ok { appSlug := "my-app", env := "prod", name := "KEY", value? := some "v1=eq" } &&
        Qed.Cli.parseSecretsSetArgs ["my-app", "KEY=a=b", "--env", "prod"] == .ok { appSlug := "my-app", env := "prod", name := "KEY", value? := some "a=b" } &&
        Qed.Cli.parseSecretsSetArgs ["--app", "my-app", "KEY=val", "--env", "preview"] == .ok { appSlug := "my-app", env := "preview", name := "KEY", value? := some "val" } &&
        Qed.Cli.parseSecretsSetArgs ["my-app", "KEY"] == .ok { appSlug := "my-app", env := "prod", name := "KEY", value? := none } &&
        !(Qed.Cli.parseSecretsSetArgs ["my-app", "KEY=v1", "--value", "v2"]).isOk &&
        match Qed.Cli.parseSecretsSetArgs ["my-app", "-BAD=SECRET"] with | .error e => !e.contains "SECRET" && e.contains "-BAD=<redacted>" | .ok _ => false),
      ("parseCloudFlags extracts --api/--token (space & `=` forms) without clobbering --value/--search",
        Qed.Cli.parseCloudFlags ["--api", "http://127.0.0.1:8080", "--token", "t1", "set", "app", "K", "--value", "--token"] ==
          .ok (some "http://127.0.0.1:8080", some "t1", ["set", "app", "K", "--value", "--token"]) &&
        Qed.Cli.parseCloudFlags ["--api=http://127.0.0.1:8080", "--token=SECRET_TOK", "whoami"] ==
          .ok (some "http://127.0.0.1:8080", some "SECRET_TOK", ["whoami"])),
      ("parseLogsArgs & buildRuntimeLogsPath handle deploy/runtime logs, explicit --pr 0, URL encoding, & validation",
        Qed.Cli.parseLogsArgs ["dep_123", "--follow"] == .ok { target := "dep_123", follow := true } &&
        Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--env", "preview", "--pr", "7", "--severity", "ERROR", "--search", "a b&c=1", "-f"] ==
          .ok { target := "my-app", runtime := true, envStr := "preview", pr := 7, severity? := some "error", search? := some "a b&c=1", follow := true } &&
        Qed.Cli.buildRuntimeLogsPath "my-app" "preview" 7 (some "error") (some "a b&c=1") ==
          "/api/v1/logs/runtime?app=my-app&env=preview&pr=7&severity=error&search=a%20b%26c%3D1" &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--severity", "error"]).isOk &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--env", "preview"]).isOk &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--env", "prod", "--pr", "0"]).isOk &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--env", "staging", "--pr", "0"]).isOk &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--env", "prod", "--pr", "5"]).isOk &&
        !(Qed.Cli.parseLogsArgs ["my-app", "--runtime", "--severity", "trace"]).isOk),
      ("filterNewRuntimeLogs deduplicates polled batches by id",
        let e1 : RuntimeLogView := { id := "rt_1", timestamp := "t1", severity := "info", source := "http", message := "a" }
        let e2 : RuntimeLogView := { id := "rt_2", timestamp := "t2", severity := "error", source := "stderr", message := "b" }
        let (b1, s1) := Qed.Cli.filterNewRuntimeLogs #[e1] {}
        let (b2, _) := Qed.Cli.filterNewRuntimeLogs #[e1, e2] s1
        b1 == #[e1] && b2 == #[e2])] do
    c.check lbl ok
  -- 2. Filesystem collectSourceBundle test with binary assets & security exclusions
  withTempDir "qed-bundle-test" fun projDir => do
    let root := System.FilePath.mk projDir
    for sub in ["public", "fonts", ".git", ".lake", ".qed", "dist", "node_modules/pkg", "target"] do
      IO.FS.createDirAll (root / sub)
    IO.FS.writeFile (root / "App.lean") "def main := 1\n"
    IO.FS.writeFile (root / "robots.txt") "User-agent: *\n"
    IO.FS.writeFile (root / "manifest.json") "{\"name\":\"demo\"}\n"
    let woffBytes := ByteArray.mk #[0x77, 0x4F, 0x46, 0x32, 0x00, 0xFF, 0x80]
    let icoBytes := ByteArray.mk #[0x00, 0x00, 0x01, 0x00]
    IO.FS.writeBinFile (root / "public" / "logo.png") pngMagic
    IO.FS.writeBinFile (root / "fonts" / "inter.woff2") woffBytes
    IO.FS.writeBinFile (root / "public" / "favicon.ico") icoBytes
    for (p, txt) in [(".env", "SECRET=1"), (".env.local", "SECRET=2"), (".git/config.txt", "x"), (".lake/a.lean", "x"),
        (".qed/x.json", "{}"), ("dist/app.js", "x"), ("node_modules/pkg/a.js", "x"), ("target/a.txt", "x")] do
      IO.FS.writeFile (root / p) txt
    withTempDir "qed-bundle-outside" fun outDir => do
      IO.FS.writeBinFile (System.FilePath.mk outDir / "outside.png") pngMagic
      withSymlink s!"{outDir}/outside.png" s!"{projDir}/public/escape.png" do
        c.expectOk "collectSourceBundle bundles text + binary static assets and excludes secrets/symlinks" (← (Qed.Cli.collectSourceBundle root).run) fun b => do
          let byPath (p : String) := b.files.find? (·.path == p)
          let hasBin (p : String) (want : ByteArray) := match byPath p with
            | some f => f.encoding == "base64" && decodeBase64? f.content == some want
            | none   => false
          let hasTxt (p : String) := match byPath p with | some f => f.encoding == "utf8" | none => false
          c.check "collectSourceBundle encodes png/woff2/ico as base64 with exact byte round-trip"
            (hasBin "public/logo.png" pngMagic && hasBin "fonts/inter.woff2" woffBytes && hasBin "public/favicon.ico" icoBytes)
          c.check "collectSourceBundle keeps lean/robots.txt/manifest.json as utf8"
            (hasTxt "App.lean" && hasTxt "robots.txt" && hasTxt "manifest.json")
          c.check "collectSourceBundle excludes .env*, .git, .lake, .qed, dist, node_modules, target, and symlinks"
            ([".env", ".env.local", ".git/config.txt", ".lake/a.lean", ".qed/x.json", "dist/app.js", "node_modules/pkg/a.js", "target/a.txt", "public/escape.png"].all fun p => (byPath p).isNone)
    -- Oversized file (> 2 MiB) & invalid UTF-8 .LEAN rejected cleanly
    IO.FS.writeBinFile (root / "public" / "huge.png") (ByteArray.mk (Array.replicate (maxSourceFileBytes + 1) 0))
    c.checkErrContains "collectSourceBundle rejects >2 MiB file before reading" (← (Qed.Cli.collectSourceBundle root).run) "exceeds"
    IO.FS.removeFile (root / "public" / "huge.png")
    IO.FS.writeBinFile (root / "Bad.LEAN") (ByteArray.mk #[0xFF, 0xFE, 0x80])
    c.checkErrContains "collectSourceBundle rejects non-UTF-8 .LEAN file" (← (Qed.Cli.collectSourceBundle root).run) "not valid UTF-8"
  -- 3. End-to-end mock Qed Cloud server + real `qed` CLI tests
  let stRef ← IO.mkRef ({} : MockCloudState)
  withMockServer c "mock Qed Cloud API server started" (startMockHttpServer (handleMockCloudApi stRef)) (·.2) fun (port, _) => do
    let apiUrl := s!"http://127.0.0.1:{port}"
    let qedBin ← qedBinPath
    withTempDir "qed-cloud-cli-e2e" fun tmpDir => do
      let credsFile := s!"{tmpDir}/credentials.json"
      let baseEnv : Array (String × Option String) := #[("QED_CREDENTIALS_FILE", some credsFile), ("QED_CLOUD_TOKEN", none), ("QED_CLOUD_API", none), ("QED_SECRET_VALUE", none)]
      let runCli (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO (UInt32 × String) := do
        let (code, o, e) ← runCmd qedBin args (env := baseEnv ++ extraEnv); return (code, o ++ e)
      -- CI auth via --token, --token=, & QED_CLOUD_TOKEN without credentials.json (never echoing token)
      let (rc1, out1) ← runCli #["whoami", "--api", apiUrl, "--token", "tok_flag_999"]
      c.check "qed whoami --token authenticates without credentials.json and never echoes token"
        (rc1 == 0 && out1.contains "ci@qed.cloud" && !out1.contains "tok_flag_999" && (← stRef.get).reqs.any fun r => r.2.1 == "/api/v1/whoami" && r.2.2.1 == some "Bearer tok_flag_999") out1
      let (rc1Eq, out1Eq) ← runCli #["whoami", s!"--api={apiUrl}", "--token=tok_eq_SECRET"]
      c.check "qed whoami --api=... --token=... works and never echoes token"
        (rc1Eq == 0 && out1Eq.contains "ci@qed.cloud" && !out1Eq.contains "tok_eq_SECRET" && (← stRef.get).reqs.any fun r => r.2.1 == "/api/v1/whoami" && r.2.2.1 == some "Bearer tok_eq_SECRET") out1Eq
      let (rc2, out2) ← runCli #["whoami", "--api", apiUrl] #[("QED_CLOUD_TOKEN", some "tok_env_888")]
      c.check "qed whoami with QED_CLOUD_TOKEN authenticates without credentials.json and never echoes token"
        (rc2 == 0 && out2.contains "ci@qed.cloud" && !out2.contains "tok_env_888" && (← stRef.get).reqs.any fun r => r.2.1 == "/api/v1/whoami" && r.2.2.1 == some "Bearer tok_env_888") out2
      -- Secrets list, set (KEY=VALUE, --app KEY=VALUE, --value=, QED_SECRET_VALUE with whitespace), & delete
      let (rcList, outList) ← runCli #["secrets", "list", "my-app", "--env", "staging", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed secrets list --env filters staging secrets and passes env query param"
        (rcList == 0 && outList.contains "staging:STAGE_KEY" && !outList.contains "prod:API_KEY" &&
          (← stRef.get).reqs.any fun r => r.2.1 == "/api/v1/secrets?app=my-app&env=staging") outList
      let (rcSet1, outSet1) ← runCli #["secrets", "set", "my-app", "STRIPE_KEY=sk_live=abc==", "--env", "prod", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed secrets set <app> KEY=VALUE preserves `=` and never echoes value"
        (rcSet1 == 0 && !outSet1.contains "sk_live=abc==" && (← stRef.get).lastSecretSet == some { appSlug := "my-app", env := "prod", name := "STRIPE_KEY", value := "sk_live=abc==" }) outSet1
      let (rcSet2, outSet2) ← runCli #["secrets", "set", "--app", "my-app", "DB_URL=postgres://u:p@h/d?ssl=1", "--env", "staging", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed secrets set --app <app> KEY=VALUE works and never echoes value"
        (rcSet2 == 0 && !outSet2.contains "postgres://" && (← stRef.get).lastSecretSet == some { appSlug := "my-app", env := "staging", name := "DB_URL", value := "postgres://u:p@h/d?ssl=1" }) outSet2
      let (rcSetValEq, outSetValEq) ← runCli #["secrets", "set", "my-app", "EQ_SEC", "--value=VAL_SECRET_EQ", "--api", apiUrl, "--token=tok_1"]
      c.check "qed secrets set --value=SECRET works and never echoes value"
        (rcSetValEq == 0 && !outSetValEq.contains "VAL_SECRET_EQ" && (← stRef.get).lastSecretSet == some { appSlug := "my-app", env := "prod", name := "EQ_SEC", value := "VAL_SECRET_EQ" }) outSetValEq
      let rawWsSecret := "  secret val \n"
      let (rcSet3, outSet3) ← runCli #["secrets", "set", "my-app", "ENV_SEC", "--env", "preview", "--api", apiUrl, "--token", "tok_1"] #[("QED_SECRET_VALUE", some rawWsSecret)]
      c.check "qed secrets set preserves leading/trailing whitespace & newline in QED_SECRET_VALUE"
        (rcSet3 == 0 && !outSet3.contains "secret val" && (← stRef.get).lastSecretSet == some { appSlug := "my-app", env := "preview", name := "ENV_SEC", value := rawWsSecret }) outSet3
      let (rcDel, outDel) ← runCli #["secrets", "delete", "my-app", "STRIPE_KEY", "--env", "prod", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed secrets delete sends SecretDeleteReq to /api/v1/secrets/delete"
        (rcDel == 0 && (← stRef.get).lastSecretDel == some { appSlug := "my-app", env := "prod", name := "STRIPE_KEY" }) outDel
      -- Redaction & leading-dash unknown flag rejection (NEVER echo secrets/tokens on errors)
      for (lbl, args, forbidden) in [
          ("whoami --token=SECRET --bad=LEAK redacts errors", #["whoami", "--token=SECRET", "--bad=LEAK"], ["SECRET", "LEAK"]),
          ("secrets set -BAD=SECRET redacts flag", #["secrets", "set", "my-app", "-BAD=SECRET"], ["SECRET"]),
          ("secrets set KEY1=SECRET1 KEY2=SECRET2 never leaks secrets", #["secrets", "set", "KEY1=SECRET1", "KEY2=SECRET2"], ["SECRET1", "SECRET2"]),
          ("secrets set --value=SECRET with invalid slug never leaks value", #["secrets", "set", "BAD_SLUG", "KEY", "--value=SECRET"], ["SECRET"]),
          ("cancel rejects leading-dash unknown flag", #["cancel", "--bad=SECRET", "--api", apiUrl, "--token", "tok_1"], ["SECRET"]),
          ("rollback rejects leading-dash unknown flag", #["rollback", "my-app", "-bad=SECRET", "--api", apiUrl, "--token", "tok_1"], ["SECRET"]),
          ("status rejects leading-dash unknown flag", #["status", "--bad=SECRET", "--api", apiUrl, "--token", "tok_1"], ["SECRET"]),
          ("status rejects invalid app slug", #["status", "BAD_SLUG=SECRET", "--api", apiUrl, "--token", "tok_1"], ["SECRET"])] do
        let (rcBad, outBad) ← runCli args
        c.check lbl (rcBad != 0 && forbidden.all (!outBad.contains ·)) outBad
      -- Runtime logs & cancel & canceled build log --follow
      let (rcRt, outRt) ← runCli #["logs", "my-app", "--runtime", "--env", "prod", "--severity", "error", "--search", "hello world&x=1", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed logs --runtime URL-encodes query params and formats runtime logs"
        (rcRt == 0 && outRt.contains "GET /boom -> 500" &&
          (← stRef.get).reqs.any fun r => r.2.1 == "/api/v1/logs/runtime?app=my-app&env=prod&severity=error&search=hello%20world%26x%3D1") outRt
      let (rcCan, outCan) ← runCli #["cancel", "dep_abc123", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed cancel sends CancelDeployReq to /api/v1/deployment/cancel"
        (rcCan == 0 && (← stRef.get).lastCancel == some { deploymentId := "dep_abc123" }) outCan
      let (rcFol, outFol) ← runCli #["logs", "dep_canceled_1", "--follow", "--api", apiUrl, "--token", "tok_1"]
      c.check "qed logs <id> --follow exits cleanly on canceled status" (rcFol != 0 && outFol.contains "Deployment canceled") outFol
      -- Logout: --token without credentials.json, --token preserving existing credentials.json, stored creds, mismatched --api, & server failure
      stRef.modify fun s => { s with reqs := #[], failRevoke := false }
      let (rcLoTok0, outLoTok0) ← runCli #["logout", "--api", apiUrl, "--token", "tok_ci_only"]
      c.check "qed logout --token revokes explicit token when no credentials file exists"
        (rcLoTok0 == 0 && !outLoTok0.contains "tok_ci_only" &&
          (← stRef.get).reqs.any fun r => r.1 == "POST" && r.2.1 == "/api/v1/tokens/revoke-current" && r.2.2.1 == some "Bearer tok_ci_only") outLoTok0
      let seedCreds : Qed.Cli.CloudCredentials := { apiBase := apiUrl, token := "tok_stored_777", userId := "u1", email := "u1@qed.cloud" }
      IO.FS.writeFile (System.FilePath.mk credsFile) ((toJson seedCreds).render ++ "\n")
      stRef.modify fun s => { s with reqs := #[] }
      let (rcLoTok1, outLoTok1) ← runCli #["logout", "--api", apiUrl, "--token=tok_ci_keep_file"]
      c.check "qed logout --token revokes explicit token without deleting unrelated credentials.json"
        (rcLoTok1 == 0 && !outLoTok1.contains "tok_ci_keep_file" && (← (System.FilePath.mk credsFile).pathExists) &&
          (← stRef.get).reqs.any (fun r => r.2.2.1 == some "Bearer tok_ci_keep_file") &&
          !(← stRef.get).reqs.any (fun r => r.2.2.1 == some "Bearer tok_stored_777")) outLoTok1
      -- Mismatched --api with stored credentials: warns, does NOT send stored token to wrong host, removes local credentials
      stRef.modify fun s => { s with reqs := #[] }
      let (rcLoMis, outLoMis) ← runCli #["logout", "--api", "http://127.0.0.1:1"]
      c.check "qed logout with mismatched --api warns, skips remote revoke, and removes local credentials"
        (rcLoMis == 0 && outLoMis.contains "warning:" && !(← (System.FilePath.mk credsFile).pathExists) && (← stRef.get).reqs.isEmpty) outLoMis
      -- Matching stored credentials: revokes remotely and removes local credentials
      IO.FS.writeFile (System.FilePath.mk credsFile) ((toJson seedCreds).render ++ "\n")
      let (rcLo1, outLo1) ← runCli #["logout", "--api", apiUrl]
      c.check "qed logout calls POST /api/v1/tokens/revoke-current and removes credentials file"
        (rcLo1 == 0 && !outLo1.contains "tok_stored_777" && !(← (System.FilePath.mk credsFile).pathExists) &&
          (← stRef.get).reqs.any fun r => r.1 == "POST" && r.2.1 == "/api/v1/tokens/revoke-current" && r.2.2.1 == some "Bearer tok_stored_777") outLo1
      -- Server error on revoke: stored-creds logout warns & removes local file; explicit --token fails non-zero
      stRef.modify fun s => { s with failRevoke := true }
      IO.FS.writeFile (System.FilePath.mk credsFile) ((toJson seedCreds).render ++ "\n")
      let (rcLo2, outLo2) ← runCli #["logout", "--api", apiUrl]
      c.check "qed logout warns and still removes local credentials when remote revoke fails"
        (rcLo2 == 0 && outLo2.contains "warning:" && !(← (System.FilePath.mk credsFile).pathExists)) outLo2
      let (rcLoTokFail, outLoTokFail) ← runCli #["logout", "--api", apiUrl, "--token", "tok_fail_secret"]
      c.check "qed logout --token fails non-zero on server error without printing success or token"
        (rcLoTokFail != 0 && !outLoTokFail.contains "token revoked" && !outLoTokFail.contains "tok_fail_secret") outLoTokFail

def run : IO Bool := do let c ← mkChecker "cloud-deploy"; testCloudDeployEndToEnd c; testCloudProtocolAndCli c; c.finish

end QedTests.Native.CloudDeploy
