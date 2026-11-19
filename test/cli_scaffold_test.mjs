import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { mkdtemp, mkdir, readFile, symlink, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { ROOT, getFreePort, rawHttpReq, sleep, stopProc } from './harness.mjs';

const cli = path.join(ROOT, '.lake/build/bin/qed');
const env = { ...process.env, QED_HOME: ROOT };
for (const k of ['QED_WEB_ROOT', 'QED_JS_ROOT', 'QED_SKIP_VERIFY', 'LEAN_PATH', 'QED_PREBUILT', 'QED_OUT_DIR']) delete env[k];

const run = (command, args, cwd = ROOT) => spawnSync(command, args, { cwd, env, encoding: 'utf8', timeout: 120000 });
const succeeds = (result) => {
  assert.equal(result.status, 0, `${result.error ?? ''}\n${result.stdout}\n${result.stderr}`);
  return result;
};

if (!existsSync(cli)) succeeds(run('lake', ['build', 'qed']));
const scratch = await mkdtemp(path.join(tmpdir(), 'qed-scaffold-test-'));
const app = path.join(scratch, 'app');
try {
  succeeds(run(cli, ['new', app]));
  assert.equal(await readFile(path.join(app, 'lean-toolchain'), 'utf8'),
    await readFile(path.join(ROOT, 'lean-toolchain'), 'utf8'));

  const lakefile = path.join(app, 'lakefile.lean');
  await writeFile(lakefile, (await readFile(lakefile, 'utf8')).replace(
    'from git "https://github.com/JacobAsmuth/qed" @ "main"',
    `from ${JSON.stringify(ROOT)}`,
  ));
  succeeds(run(cli, ['build'], app));

  const { default: render } = await import(pathToFileURL(path.join(app, 'dist', 'ssr.mjs')));
  const response = await render(new Request('http://localhost/'));
  assert.equal(response.status, 200);
  const html = await response.text();
  assert.match(html, /<span[^>]*>1<\/span>/);
  assert.match(html, /qed_host\.mjs/);
  assert.match(await readFile(path.join(app, 'dist', 'app.mjs'), 'utf8'), /qed_init/);

  const strippedRt = path.join(scratch, 'stripped_rt.mjs');
  const rtSrc = await readFile(path.join(ROOT, 'runtime/qed_rt.mjs'), 'utf8');
  await writeFile(strippedRt, rtSrc.replace('export const Array_push', 'export const Removed_Array_push'));
  const missingExternRes = run('lake', [
    'env', path.join(ROOT, '.lake/build/bin/qedjs'), '--check-externs', strippedRt, 'Web', '--', 'Quantity.app:app', 'Qed.App.ssrStep:ssrStep',
  ], app);
  assert.notEqual(missingExternRes.status, 0);
  assert.match(missingExternRes.stdout + missingExternRes.stderr, /qed_rt: missing externs: .*Array_push/);

  const appPath = path.join(app, 'App.lean');
  const valid = await readFile(appPath, 'utf8');

  // Verify lexical `grepForbidden` + exact `verifyNoServerLeakInClient`:
  // comments, string literals containing "sorry"/"admit", and client helpers named
  // `initState`/`my_handler`/`my_step` must NOT trigger false positives.
  await writeFile(appPath, valid
    .replace('<span>{quantity}</span>', '<span>{my_handler(my_step(quantity + initState - 1))}</span>\n      <small>{admitted_sorry_msg}</small>')
    .replace('open Qed\n',
      'open Qed\n\n-- comments mentioning sorry, admit, native_decide must be ignored\n' +
      '/- nested /- block comment with sorry and admit -/ still comment -/\n' +
      'def initState : Nat := 1\n' +
      'def my_handler (n : Nat) : Nat := n\n' +
      'def my_step (n : Nat) : Nat := n\n' +
      'def admitted_sorry_msg : String := "We are sorry, please admit this item"\n'));
  succeeds(run(cli, ['build'], app));

  // Verify `qed_serve.mjs` blocks sibling-prefix path traversal, percent-encoded `..`, and symlinks.
  const secretDir = path.join(app, 'dist-secret');
  await mkdir(secretDir, { recursive: true });
  await writeFile(path.join(secretDir, 'leak.txt'), 'TOP_SECRET_SIBLING');
  await symlink(path.join(secretDir, 'leak.txt'), path.join(app, 'dist', 'escape.txt'));
  const freePort = await getFreePort();
  const serveProc = spawn(process.execPath, [path.join(ROOT, 'runtime/qed_serve.mjs'), path.join(app, 'dist'), String(freePort)], {
    cwd: app, env, stdio: ['ignore', 'pipe', 'pipe'],
  });
  try {
    let up = false;
    for (let i = 0; i < 40 && !up; i++) {
      try { up = (await fetch(`http://127.0.0.1:${freePort}/app.mjs`)).status === 200; } catch {}
      if (!up) await sleep(50);
    }
    assert.equal(up, true, 'qed_serve.mjs failed to start');
    const getRaw = (reqPath) => rawHttpReq(freePort, `GET ${reqPath} HTTP/1.1\r\nHost: 127.0.0.1:${freePort}\r\nConnection: close\r\n\r\n`);
    assert.equal((await getRaw('/../dist-secret/leak.txt')).includes('TOP_SECRET_SIBLING'), false);
    assert.equal((await getRaw('/%2e%2e%2fdist-secret/leak.txt')).includes('TOP_SECRET_SIBLING'), false);
    assert.equal((await getRaw('/escape.txt')).includes('TOP_SECRET_SIBLING'), false);
    assert.equal((await getRaw('/%ZZ')).startsWith('HTTP/1.1 400 '), true);
  } finally {
    await stopProc(serveProc, 1000);
  }

  // Verify real `sorry` inside interpolated string or with magic comment is still caught.
  await writeFile(appPath, valid + '\ndef badInterp : String := s!"{(by sorry : Nat)}" -- never emit\n');
  const sorryRes = run(cli, ['check'], app);
  assert.notEqual(sorryRes.status, 0);
  assert.match(sorryRes.stdout + sorryRes.stderr, /forbidden token `sorry`/);

  await writeFile(appPath, valid + '\npartial def spin (n : Nat) : Nat := spin n\n');
  const partialRes = run(cli, ['check'], app);
  assert.notEqual(partialRes.status, 0);
  assert.match(partialRes.stdout + partialRes.stderr, /kernel gate: `partial` or `opaque` declaration `spin`/);

  console.log('  ✓ cli-scaffold');
} finally {
  await rm(scratch, { recursive: true, force: true });
}
