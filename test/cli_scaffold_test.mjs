import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));
const cli = path.join(root, '.lake/build/bin/qed');
const env = { ...process.env, QED_HOME: root };
delete env.QED_WEB_ROOT;
delete env.QED_JS_ROOT;
delete env.QED_SKIP_VERIFY;
delete env.LEAN_PATH;
delete env.QED_PREBUILT;
delete env.QED_OUT_DIR;

const run = (command, args, cwd = root) => spawnSync(command, args, {
  cwd, env, encoding: 'utf8', timeout: 120000,
});
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
    await readFile(path.join(root, 'lean-toolchain'), 'utf8'));

  const lakefile = path.join(app, 'lakefile.lean');
  const source = await readFile(lakefile, 'utf8');
  await writeFile(lakefile, source.replace(
    'from git "https://github.com/JacobAsmuth/qed" @ "main"',
    `from ${JSON.stringify(root)}`,
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
  const rtSrc = await readFile(path.join(root, 'runtime/qed_rt.mjs'), 'utf8');
  await writeFile(strippedRt, rtSrc.replace('export const Array_push', 'export const Removed_Array_push'));
  const missingExternRes = run('lake', [
    'env', path.join(root, '.lake/build/bin/qedjs'), '--check-externs', strippedRt, 'Web', '--', 'Quantity.app:app', 'Qed.App.ssrStep:ssrStep',
  ], app);
  assert.notEqual(missingExternRes.status, 0);
  assert.match(missingExternRes.stdout + missingExternRes.stderr,
    /qed_rt: missing externs: .*Array_push/);

  const appPath = path.join(app, 'App.lean');
  const valid = await readFile(appPath, 'utf8');
  await writeFile(appPath, valid + '\npartial def spin (n : Nat) : Nat := spin n\n');
  const partialRes = run(cli, ['check'], app);
  assert.notEqual(partialRes.status, 0);
  assert.match(partialRes.stdout + partialRes.stderr, /kernel gate: `partial` or `opaque` declaration `spin`/);

  console.log('  ✓ cli-scaffold');
} finally {
  await rm(scratch, { recursive: true, force: true });
}
