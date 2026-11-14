import Cli.Verify

open System (FilePath)

namespace Qed.Cli

def jsRoot : IO String := do
  match ← env "QED_JS_ROOT" with
  | some r => return r
  | none   => webRoot

def indexHtml (dev : Bool) : String :=
  let reload := if dev then
    "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n"
  else ""
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title></head>\n" ++
  "<body><div id=\"app\">loading…</div>\n" ++ reload ++
  "<script type=\"module\" src=\"/qed_host.mjs\"></script>\n</body>\n</html>\n"

def ssrAppName (mod : String) : IO (Option String) := do
  let path := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  if !(← path.pathExists) then return none
  let src ← IO.FS.readFile path
  match src.splitOn "Qed.run " with
  | _ :: rest :: _ =>
      let name := ((rest.dropWhile (· == ' ')).takeWhile fun c =>
        c.isAlphanum || c == '.' || c == '_' || c == '\'').toString
      return if name.isEmpty then none else some name
  | _ => return none

def ssrWrapper (appName : String) (cacheKey : String := "") : String :=
  let title := (appName.splitOn ".").headD "qed"
  let appImport := "./ssr_app.mjs" ++ (if cacheKey.isEmpty then "" else s!"?build={cacheKey}")
  "import * as mod from '" ++ appImport ++ "';\n" ++
  "import * as rt from './qed_rt.mjs';\n" ++
  "import { makeHandler } from './qed_ssr_host.mjs';\n" ++
  "rt.assertExterns(mod.__externs, rt);\n" ++
  "export { makeHandler, mod };\n" ++
  "export default makeHandler(mod, { title: '" ++ title ++ "', script: '/qed_host.mjs' });\n"

def driverEntries : Array String := #[
  "main:__main",
  "Qed.qedInit:qed_init", "Qed.qedDispatch:qed_dispatch", "Qed.qedDispatchStr:qed_dispatch_str",
  "Qed.qedStreamChunk:qed_stream_chunk", "Qed.qedStreamDone:qed_stream_done",
  "Qed.qedHttpDone:qed_http_done", "Qed.qedUrlChanged:qed_url_changed",
  "Qed.qedLocalDispatch:qed_local_dispatch", "Qed.qedLocalDispatchStr:qed_local_dispatch_str",
  "Qed.qedLocalSnapshot:qed_local_snapshot", "Qed.qedLocalRestore:qed_local_restore",
  "Qed.qedEffectDone:qed_effect_done", "Qed.qedPortRecv:qed_port_recv"]

def buildJs (outDir : FilePath) (prod : Bool) : IO Bool := do
  let mod ← jsRoot
  if (← sh "lake" #["build", mod, "qedjs"]) != 0 then return false
  IO.FS.createDirAll outDir
  let appOut := (outDir / "app.mjs").toString
  let minArgs := if prod then #["--min"] else #[]
  if (← sh "lake" (#["exe", "qedjs"] ++ minArgs ++ #[appOut, mod, "--"] ++ driverEntries)) != 0 then
    return false
  for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
    IO.FS.writeFile (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  IO.FS.writeFile (outDir / "index.html") (indexHtml (dev := !prod))
  match ← ssrAppName mod with
  | some appName =>
      let ssrOut := (outDir / "ssr_app.mjs").toString
      if (← sh "lake" (#["exe", "qedjs"] ++ minArgs ++ #[ssrOut, mod, "--"] ++
            #[s!"{appName}:app", "Qed.App.ssrStep:ssrStep"])) != 0 then return false
      IO.FS.writeFile (outDir / "qed_ssr_host.mjs") (← IO.FS.readFile (← runtimeFile "qed_ssr_host.mjs"))
      -- Bust Node's ESM module cache on dev rebuilds so reloaded SSR wrappers pick up the new app.
      let cacheKey ← if prod then pure "" else toString <$> IO.monoMsNow
      IO.FS.writeFile (outDir / "ssr.mjs") (ssrWrapper appName cacheKey)
  | none =>
      IO.println s!"  note: no `Qed.run <app>` found in {mod}, skipping the SSR handler (ssr.mjs)"
  if prod then
    if (← onPath "esbuild") then
      for f in ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"] do
        let p := outDir / f
        if (← p.pathExists) then
          discard <| sh "bash" #["-c", s!"esbuild {p} --minify --format=esm --outfile={p}.min && mv {p}.min {p}"]
  return true

def cmdBuild (prod : Bool) (skipVerify : Bool := false) : IO UInt32 := do
  let skip := !prod && (skipVerify || (← env "QED_SKIP_VERIFY") == some "1")
  if !skip then
    if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  let outDir := if prod then distDir else devDir
  step s!"transpiling Lean → JavaScript → {outDir}/"
  if !(← buildJs outDir prod) then IO.eprintln (red "✗ build failed"); return 1
  let (_, sz) ← shOut "bash" #["-c",
    s!"cat {outDir}/app.mjs {outDir}/qed_rt.mjs {outDir}/qed_dom.mjs {outDir}/qed_host.mjs | gzip -c | wc -c"]
  IO.println (green s!"✓ build complete → {outDir}, {sz.trimmed} bytes gzipped to the client")
  return 0

def serveDir (dir : FilePath) (dev : Bool := false) : IO UInt32 := do
  if (← (dir / "ssr.mjs").pathExists) && (← onPath "node") then
    let args := #[(← runtimeFile "qed_serve.mjs").toString, dir.toString, devPort]
    sh "node" (if dev then args.push "--dev" else args)
  else
    IO.println s!"serving {dir} → http://localhost:{devPort}"
    sh "python3" #["-m", "http.server", devPort, "--directory", dir.toString]

def cmdStart : IO UInt32 := do
  if !(← (distDir / "app.mjs").pathExists) then
    IO.eprintln (red "no production build found, run `qed build` first"); return 1
  serveDir distDir

def cmdClean : IO UInt32 := do
  let _ ← sh "lake" #["clean"]
  let _ ← sh "rm" #["-rf", distDir.toString, (FilePath.mk ".qed").toString]
  IO.println (green "✓ cleaned")
  return 0

partial def watchLoop (marker : FilePath) : IO Unit := do
  IO.sleep 400
  let qh ← frameworkHome
  let find := s!"find . -name '*.lean' -newer {marker} -not -path './.lake/*' -not -path './.qed/*' 2>/dev/null | head -1; " ++
              s!"find {qh}/runtime -newer {marker} 2>/dev/null | head -1"
  let (_, out) ← shOut "bash" #["-c", find]
  if out.trimmed != "" then
    let _ ← sh "touch" #[marker.toString]
    step "change detected, rebuilding"
    if (← buildJs devDir (prod := false)) then
      writeBuildId devDir
      let _ ← effectsCovered
      IO.println (green "✓ reloaded")
    else
      IO.eprintln (red "✗ build failed, fix and save again")
  watchLoop marker

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir
  let marker := devDir / ".watch"
  let _ ← sh "touch" #[marker.toString]
  step "initial build"
  unless (← buildJs devDir (prod := false)) do
    IO.eprintln (red "initial build failed, fix the error and save; dev will rebuild")
  writeBuildId devDir
  let ssr := (← (devDir / "ssr.mjs").pathExists) && (← onPath "node")
  let serveJs ← runtimeFile "qed_serve.mjs"
  let _server ← IO.Process.spawn <|
    if ssr then
      { cmd := "node",
        args := #[serveJs.toString, devDir.toString, devPort, "--dev"],
        stdin := .null, stdout := .null, stderr := .inherit }
    else
      { cmd := "python3", args := #["-m", "http.server", devPort, "--directory", devDir.toString],
        stdin := .null, stdout := .null, stderr := .inherit }
  let ssrTag := if ssr then "   (SSR)" else ""
  IO.println (green s!"\nqed dev → http://localhost:{devPort}{ssrTag}   (watching; Ctrl-C to stop)\n")
  watchLoop marker
  return 0

end Qed.Cli
