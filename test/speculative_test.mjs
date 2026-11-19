import {
  buildDevAsync, checker, signSessionToken, sleep, startNativeServer, varintField, withPage,
} from './harness.mjs';

const { check, fail, finish } = checker('Speculative');

const dir = await buildDevAsync('Tests.SpeculativeApp');
const authSecret = 'spec-test-hmac-secret';
const validToken = signSessionToken(authSecret, 'alice');
const srv = await startNativeServer(dir, { QED_WORKERS: '2', QED_AUTH_SECRET: authSecret });

try {
  check('native server healthy', srv.healthy, true);

  const postOrder = (qty) => fetch(`${srv.baseUrl}/_qed/rpc/SpecDemoSrv/placeOrder`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-protobuf', Authorization: `Bearer ${validToken}` },
    body: varintField(1, qty),
  });

  await withPage(async (page) => {
    page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));

    let holdNextRpc = false, heldResolve = null, heldArrived = null;
    const armHold = () => {
      holdNextRpc = true;
      return new Promise((resolve) => { heldArrived = resolve; });
    };
    const releaseHold = () => {
      if (heldResolve) { const r = heldResolve; heldResolve = null; r(); }
    };

    await page.setRequestInterception(true);
    page.on('request', async (req) => {
      if (holdNextRpc && req.url().includes('/_qed/rpc/SpecDemoSrv/')) {
        holdNextRpc = false;
        const gate = new Promise((resolve) => { heldResolve = resolve; });
        if (heldArrived) { const a = heldArrived; heldArrived = null; a(); }
        await gate;
      }
      req.continue();
    });

    await page.setCookie({ name: 'qed_session', value: validToken, domain: '127.0.0.1', path: '/' });
    await page.goto(`${srv.baseUrl}/`, { waitUntil: 'load' });
    await page.waitForSelector('.spec-demo', { timeout: 10000 });

    const readText = (sel) => page.$eval(sel, (el) => el.textContent.trim());

    // Flow 1: Prediction Hit + `on_confirm:`
    let arrived = armHold();
    await page.click('.buy-2');
    await arrived;
    check('hit flow: 0ms predicted remaining is 8 before RPC resolves', await readText('.rem'), '8');
    check('hit flow: 0ms predicted status is Pending: 8', await readText('.status'), 'Pending: 8');
    check('hit flow: pre-await clicks incremented to 1', await readText('.clicks'), '1');
    check('hit flow: on_confirm not yet run (confirmed=0)', await readText('.confirmed'), '0');
    releaseHold();
    await page.waitForFunction(() => document.querySelector('.status')?.textContent?.trim() === 'Confirmed: 8', { timeout: 5000 });
    check('hit flow: confirmed remaining stays 8', await readText('.rem'), '8');
    check('hit flow: on_confirm incremented confirmed to 1', await readText('.confirmed'), '1');

    // Flow 2: Prediction Mismatch -> Rollback + Re-apply with `actual` + `on_confirm:`
    check('background order(3) succeeded', (await postOrder(3)).status, 200);
    arrived = armHold();
    await page.click('.buy-1');
    await arrived;
    check('mismatch flow: 0ms predicted remaining is 7', await readText('.rem'), '7');
    check('mismatch flow: 0ms predicted status is Pending: 7', await readText('.status'), 'Pending: 7');
    releaseHold();
    await page.waitForFunction(() => document.querySelector('.status')?.textContent?.trim() === 'Confirmed: 4', { timeout: 5000 });
    check('mismatch flow: reconciled remaining to server truth 4', await readText('.rem'), '4');
    check('mismatch flow: on_confirm ran once (confirmed=2)', await readText('.confirmed'), '2');

    // Flow 3: Error Rollback (.outOfStock) preserving concurrent user input
    check('background order(4) succeeded', (await postOrder(4)).status, 200);
    arrived = armHold();
    await page.click('.buy-4');
    await arrived;
    check('error flow: 0ms predicted remaining is 0', await readText('.rem'), '0');
    check('error flow: 0ms predicted status is Pending: 0', await readText('.status'), 'Pending: 0');
    await page.type('.note-input', 'keep my note');
    check('error flow: concurrent note updated while in flight', await readText('.note-mirror'), 'keep my note');
    releaseHold();
    await page.waitForFunction(() => document.querySelector('.status')?.textContent?.trim() === 'Out of stock', { timeout: 5000 });
    check('error flow: remaining rolled back to 4', await readText('.rem'), '4');
    check('error flow: pre-await clicks preserved at 3', await readText('.clicks'), '3');
    check('error flow: concurrent user input preserved across rollback', await readText('.note-mirror'), 'keep my note');
    check('error flow: on_confirm skipped on error (confirmed=2)', await readText('.confirmed'), '2');

    // Flow 4: Explicit `rollback(actual):` override
    await page.click('.claim-ok');
    await page.waitForFunction(() => document.querySelector('.confirmed')?.textContent?.trim() === '3', { timeout: 5000 });
    check('claim hit: owned count is 1', await readText('.owned-count'), '1');
    check('claim hit: claimStatus is Claimed', await readText('.claim-status'), 'Claimed');

    arrived = armHold();
    await page.click('.claim-miss');
    await arrived;
    check('claim mismatch: 0ms predicted owned count is 2', await readText('.owned-count'), '2');
    releaseHold();
    await page.waitForFunction(() => document.querySelector('.claim-status')?.textContent?.trim() === 'Mismatch:2', { timeout: 5000 });
    check('claim mismatch: owned count rolled back to 1', await readText('.owned-count'), '1');
    check('claim mismatch: on_confirm skipped (confirmed stays 3)', await readText('.confirmed'), '3');

    // Flow 5: `Resource` shorthand `items = await ... predict [1, 2, 3]`
    arrived = armHold();
    await page.click('.refresh-items');
    await arrived;
    check('resource predict: 0ms items size is 3 (no loading flash)', await readText('.items-val'), '3');
    releaseHold();
    await sleep(100);
    check('resource predict: reconciled items size is 3', await readText('.items-val'), '3');
  });
} finally {
  await srv.stop();
}

finish();
