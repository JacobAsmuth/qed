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
delete env.QED_SKIP_VERIFY;
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

  await writeFile(appPath, valid.replace('>+</button>', '>Add</button>'));
  succeeds(run(cli, ['build', '--dev'], app));
  const updatedUrl = pathToFileURL(path.join(app, '.qed/dev/ssr.mjs'));
  updatedUrl.search = '?after-edit';
  const { default: updated } = await import(updatedUrl);
  assert.match(await (await updated(new Request('http://localhost/'))).text(), />Add<\/button>/);

  await writeFile(appPath, valid.replace('decrease when 1 < quantity', 'decrease'));
  const broken = run(cli, ['check'], app);
  assert.notEqual(broken.status, 0);
  assert.match(broken.stdout + broken.stderr, /case `decrease` still needs/);

  await writeFile(path.join(app, 'Child.lean'),
    'import Qed\nopen Qed\nnamespace Site\ncomponent Badge where\n  prop label : String := "ok"\n  state count : Int := 7\n  view => <span class="badge">{label}:{count}</span>\nend Site\n');
  await writeFile(lakefile, (await readFile(lakefile, 'utf8')).replace(
    '@[default_target] lean_lib App where',
    '@[default_target] lean_lib Child where\nlean_lib App where',
  ));
  await writeFile(appPath,
    'import Qed\nimport Child\nopen Qed\nnamespace Site\n' +
    'component Quantity where\n  state quantity : Int := 1\n' +
    '  view => <div><style>{".a > .b { color: red; }"}</style><br/><a href={url% "/guide"}><b>safe</b></a><Badge key="b"/><span>{quantity}</span></div>\n' +
    'end Site\nabbrev Quantity.app := Site.Quantity.app\n');
  succeeds(run(cli, ['build', '--dev'], app));
  const multiUrl = pathToFileURL(path.join(app, '.qed/dev/ssr.mjs'));
  multiUrl.search = '?multi-file';
  const { default: renderMulti } = await import(multiUrl);
  const multiHtml = await (await renderMulti(new Request('http://localhost/'))).text();
  assert.match(multiHtml, /\.a > \.b \{ color: red; \}/);
  assert.doesNotMatch(multiHtml, /<\/br>/);
  assert.match(multiHtml, /href="\/guide"><b>safe<\/b><\/a>/);
  assert.match(multiHtml, /class="badge">ok:7<\/span>/);

  await writeFile(appPath,
    'import Qed\nopen Qed\ncomponent RawBad where\n  state x : Int := 0\n  view => <div {Attr.rawHtml "<b>raw</b>"}/>\n');
  const rawRes = run(cli, ['check'], app);
  assert.notEqual(rawRes.status, 0);

  await writeFile(appPath, valid + '\npartial def spin (n : Nat) : Nat := spin n\n');
  const partialRes = run(cli, ['check'], app);
  assert.notEqual(partialRes.status, 0);
  assert.match(partialRes.stdout + partialRes.stderr, /kernel gate: `partial` or `opaque` declaration `spin`/);

  await writeFile(appPath, valid);
  succeeds(run(cli, ['check'], app));
  console.log('  ✓ cli-scaffold');
} finally {
  await rm(scratch, { recursive: true, force: true });
}
