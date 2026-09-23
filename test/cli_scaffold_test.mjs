// Exercise the README quickstart as a separate app, with this checkout as its
// dependency so the regression test needs no GitHub access or second toolchain.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));
const cli = path.join(root, '.lake/build/bin/qed');
const env = { ...process.env, QED_HOME: root };
delete env.QED_WEB_ROOT;
delete env.QED_JS_ROOT;
const run = (command, args, cwd = root) => spawnSync(command, args, {
  cwd, env, encoding: 'utf8', timeout: 120000,
});
const succeeds = (result) => {
  assert.equal(result.status, 0, `${result.error ?? ''}\n${result.stdout}\n${result.stderr}`);
  return result;
};

succeeds(run('lake', ['build', 'qed']));
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
  succeeds(run(cli, ['build', '--dev'], app));
  succeeds(run(cli, ['build'], app));

  // Both build modes must find the dependency's transpiler and emit working SSR.
  for (const dir of ['.qed/dev', 'dist']) {
    const { default: render } = await import(pathToFileURL(path.join(app, dir, 'ssr.mjs')));
    const response = await render(new Request('http://localhost/'));
    assert.equal(response.status, 200);
    const html = await response.text();
    assert.match(html, /<span[^>]*>1<\/span>/);
    assert.match(html, /qed_host\.mjs/);
    assert.match(await readFile(path.join(app, dir, 'app.mjs'), 'utf8'), /qed_init/);
  }

  const appPath = path.join(app, 'App.lean');
  const valid = await readFile(appPath, 'utf8');

  // Reloading the SSR wrapper after a dev build must also reload the app it imports.
  // Otherwise the browser receives old static markup even though compilation succeeds.
  await writeFile(appPath, valid.replace('>+</button>', '>Add</button>'));
  succeeds(run(cli, ['build', '--dev'], app));
  const updatedUrl = pathToFileURL(path.join(app, '.qed/dev/ssr.mjs'));
  updatedUrl.search = '?after-edit';
  const { default: updated } = await import(updatedUrl);
  assert.match(await (await updated(new Request('http://localhost/'))).text(), />Add<\/button>/);

  // The README's deliberate mistake must fail with the responsible action named.
  await writeFile(appPath, valid.replace('decrease when (1 < quantity)', 'decrease'));
  const broken = run(cli, ['check'], app);
  assert.notEqual(broken.status, 0);
  assert.match(broken.stdout + broken.stderr, /case `decrease` still needs/);
  await writeFile(appPath, valid);
  succeeds(run(cli, ['check'], app));
  console.log('PASS: scaffold toolchain, dependency transpiler, dev/production SSR, SSR reload, broken guard, and recovery.');
} finally {
  await rm(scratch, { recursive: true, force: true });
}
