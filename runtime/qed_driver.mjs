// qed_driver.mjs — a small driver that drives the *transpiled, verified* view/diff
// into a real DOM. The pure pieces (view, diff, applyPatch, update) are Lean,
// compiled to JS; this file is the impure FFI shell (build DOM, apply a patch,
// delegate events) — the part that was always hand-written (cf. host.js).
//
// Html ctors:  text(0)[s]  element(1)[tag, attrs, kids]  lazy(2)[key, sub]
// Attr ctors:  cls(0) attr(1)[k,v] flag(2)[k,on] key(3) on(4)[ev,msg]
//              onValue(5)[ev,fn] localCell(6) signalBind(7)[n] signalAttr(8)[n,a,v]
// Patch ctors: replace(0)[h] setText(1)[s] patchElement(2)[attrs,steps]
//              lazyReuse(3)[k,sub] lazyPatch(4)[k,patch]
// Step ctors:  reuse(0)[oldIdx, patch]  create(1)[html]
import * as $ from './qed_rt.mjs';

const list = (l) => { const a = []; while (typeof l === 'object' && l !== null) { a.push(l.f[0]); l = l.f[1]; } return a; };

function applyAttrs(el, attrsList) {
  const classes = [];
  for (const a of list(attrsList)) {
    switch (a.t) {
      case 0: classes.push(a.f[0]); break;                                   // cls
      case 1: if (a.f[0] === 'value') { if (el.value !== a.f[1]) el.value = a.f[1]; }
              else el.setAttribute(a.f[0], a.f[1]); break;                   // attr
      case 2: if (a.f[1]) el.setAttribute(a.f[0], a.f[0]); else el.removeAttribute(a.f[0]); break; // flag
      case 3: break;                                                         // key (vdom-only)
      case 4: el['__on_' + a.f[0]] = a.f[1]; break;                          // on event msg
      case 5: el['__onv_' + a.f[0]] = a.f[1]; break;                         // onValue event fn
      case 7: el.setAttribute('data-qed-signal', a.f[0]); break;             // signalBind
      case 8: el.setAttribute(a.f[1], a.f[2]); break;                        // signalAttr
    }
  }
  el.setAttribute('class', classes.filter((c) => c !== '').join(' '));
}

function build(html, doc) {
  switch (html.t) {
    case 0: return doc.createTextNode(html.f[0]);
    case 1: { const el = doc.createElement(html.f[0]); applyAttrs(el, html.f[1]);
              for (const c of list(html.f[2])) el.appendChild(build(c, doc)); return el; }
    case 2: return build(html.f[1], doc);                                    // lazy: build sub
  }
}

function patchDom(node, patch, doc) {
  switch (patch.t) {
    case 0: { const fresh = build(patch.f[0], doc); node.parentNode.replaceChild(fresh, node); return fresh; } // replace
    case 1: node.textContent = patch.f[0]; return node;                      // setText
    case 2: {                                                                // patchElement
      applyAttrs(node, patch.f[0]);
      let j = 0;
      for (const st of list(patch.f[1])) {
        if (st.t === 0) { patchDom(node.childNodes[j], st.f[1], doc); j++; }  // reuse
        else { const fresh = build(st.f[0], doc);                            // create
               if (j < node.childNodes.length) node.insertBefore(fresh, node.childNodes[j]);
               else node.appendChild(fresh); j++; }
      }
      while (node.childNodes.length > j) node.removeChild(node.childNodes[node.childNodes.length - 1]);
      return node;
    }
    case 3: return node;                                                     // lazyReuse: skip
    case 4: return patchDom(node, patch.f[1], doc);                          // lazyPatch
  }
}

// `app` = { initModel, step, view, diff, applyPatch } (all transpiled Lean).
export function mount(app, root, doc) {
  let model = app.initModel();
  let cur = app.view(model);
  while (root.firstChild) root.removeChild(root.firstChild);
  root.appendChild(build(cur, doc));

  const dispatch = (msg) => {
    model = app.step(model, msg);
    const next = app.view(model);
    const p = app.diff(cur, next);         // the VERIFIED diff
    patchDom(root.firstChild, p, doc);
    cur = app.patch(p, cur);               // keep the vdom mirror in sync (verified applyPatch)
  };

  const delegate = (evName, key, payload) => root.addEventListener(evName, (ev) => {
    let t = ev.target;
    while (t && t !== root.parentNode) {
      if (key in t) { dispatch(payload ? payload(t) : t[key]); return; }
      t = t.parentNode;
    }
  });
  delegate('click', '__on_click');
  delegate('input', '__onv_input', (t) => $.app(t['__onv_input'], [t.value]));
  return { dispatch, getModel: () => model };
}
