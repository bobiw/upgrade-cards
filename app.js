'use strict';
const DAY = 864e5;
const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const uid = () => Math.random().toString(36).slice(2, 10) + Date.now().toString(36);

// ---------- storage: IndexedDB key/value ----------
let idb;
const dbOpen = () => new Promise((res, rej) => {
  const r = indexedDB.open('upgrade-cards', 1);
  r.onupgradeneeded = () => r.result.createObjectStore('kv');
  r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error);
});
const kvGet = k => new Promise((res, rej) => { const q = idb.transaction('kv').objectStore('kv').get(k); q.onsuccess = () => res(q.result); q.onerror = () => rej(q.error); });
const kvSet = (k, v) => new Promise((res, rej) => { const t = idb.transaction('kv', 'readwrite'); t.objectStore('kv').put(v, k); t.oncomplete = res; t.onerror = () => rej(t.error); });

let deck = { meta: {}, cards: [] }, events = [], settings = { newPerDay: 15, checkDate: '', hideDrafts: false, device: '', deck: 'mine', hideDups: true, refDark: 'auto' };
let S = null; // study session
// paused sessions survive closing the app: { study: {...}, quiz: { topic: {...} } }, saved after every answer
let sessions = { study: null, quiz: {} };
const REDO = ' · missed';                       // a missed-only drill is saved beside its quiz
const sessKey = () => S?.quiz ? ['quiz', S.quiz + (S.redo ? REDO : '')] : ['study'];
function saveSess() {
  if (!S) return;
  const v = S.i < S.queue.length ? { ids: S.queue.map(c => c.id), i: S.i, done: S.done, rl: S.rl, total: S.total, qn: S.qn, qok: S.qok, miss: (S.miss || []).map(c => c.id), round: S.round, retry: (S.retry || []).map(c => c.id), redo: S.redo, roundStart: S.roundStart, deck: settings.deck, t: Date.now() } : null;
  const [k, t] = sessKey(); if (t) { if (v) sessions.quiz[t] = v; else delete sessions.quiz[t]; } else sessions.study = v;
  kvSet('sessions', sessions);
}
function resumeSess(saved, quiz) {
  const q = saved.ids.map(byId).filter(Boolean); if (!q.length) return;
  S = { queue: q, i: Math.min(saved.i, q.length), shown: false, t0: Date.now(), total: saved.total, done: saved.done || 0, rl: saved.rl || {}, hist: [] };
  if (quiz) Object.assign(S, { quiz: quiz.replace(REDO, ''), redo: !!saved.redo, round: saved.round || 1, roundStart: saved.roundStart || 0, retry: (saved.retry || []).map(byId).filter(Boolean), qn: saved.qn || 0, qok: saved.qok || 0, miss: (saved.miss || []).map(byId).filter(Boolean) });
  viewStudy();
}
const save = () => kvSet('events', events);

// ---------- scheduler (events -> per-card state; replay is order-independent) ----------
const byTime = (a, b) => a.t - b.t || (a.id < b.id ? -1 : 1);
function maxIvl() {
  if (!settings.checkDate) return Infinity;
  const days = Math.ceil((new Date(settings.checkDate + 'T00:00:00') - Date.now()) / DAY);
  return days > 1 ? Math.max(1, Math.floor(days / 2)) : 1;
}
function step(s, e, cap) {
  s = s || { ease: 2.5, ivl: 0, reps: 0, lapses: 0, n: 0, ok: 0, first: e.t, rl: 0, streak: 0 };
  s.n++; if (e.g >= 2) s.ok++;
  if (e.g === 1) { s.lapses++; s.reps = 0; s.streak = 0; s.rl = 2; s.ivl = 0; s.ease = Math.max(1.3, s.ease - .2); s.due = e.t + 10 * 60e3; }
  else {
    s.streak++;
    if (s.rl > 0) {                      // relearning after a miss: two good answers spaced apart, then tomorrow
      s.rl--;
      if (s.rl > 0) s.due = e.t + 10 * 60e3;
      else { s.ivl = Math.min(cap, e.g === 4 ? 2 : 1); s.reps = 1; s.due = e.t + s.ivl * DAY; }
    } else {
      s.reps++;
      let i = s.reps === 1 ? { 2: 1, 3: 1, 4: 3 }[e.g] : s.reps === 2 ? { 2: 2, 3: 3, 4: 6 }[e.g]
        : s.ivl * { 2: 1.2, 3: s.ease, 4: s.ease * 1.3 }[e.g];
      if (s.lapses >= 2 && s.streak < 5) i = Math.min(i, Math.max(1, Math.ceil(s.ivl * 1.5)));   // often-missed cards climb slowly
      s.ease = Math.min(3, Math.max(1.3, s.ease + { 2: -.15, 3: 0, 4: .15 }[e.g]));
      s.ivl = Math.min(cap, Math.max(1, Math.round(i)));
      s.due = e.t + s.ivl * DAY;
    }
  }
  s.last = e.t; return s;
}
function replay() {
  const st = {}, cap = maxIvl();
  derive(); for (const e of events.slice().sort(byTime)) if (!e.k && !_undone.has(e.id)) st[e.c] = step(st[e.c], e, cap);
  return st;
}
const endOfToday = () => { const d = new Date(); d.setHours(23, 59, 59, 999); return d.getTime(); };
const sameDay = (a, b) => new Date(a).toDateString() === new Date(b).toDateString();
const deckOf = c => c.deck || (c.id.startsWith('raw-') ? 'mine' : 'claude');
const DECKS = [['mine', 'My cards'], ['claude', "Claude's cards"], ['all', 'All']];
let _dk = -1, _dset = new Set(), _spell = {}, _undone = new Set(), _dupc = {}, _sugg = {}, _ack = {};
function derive() {
  if (_dk === events.length) return; _dk = events.length;
  const d = {}, sp = {}, dc = {}, sg = {}, ak = {}; _undone = new Set(events.filter(e => e.k === 'undo').map(e => e.ref));
  for (const e of events.slice().sort(byTime)) { if (e.k === 'drop') d[e.c] = e.v; else if (e.k === 'spell') (sp[e.c] ||= {})[e.bad] = e.v; else if (e.k === 'dup') dc[e.c + '|' + e.m] = e.v; else if (e.k === 'sugg') sg[e.c] = e.v; else if (e.k === 'ack') ak[e.c] = e.v; }
  _dset = new Set(Object.keys(d).filter(k => d[k])); _spell = sp; _dupc = dc; _sugg = sg; _ack = ak;
}
const isDropped = id => { derive(); return _dset.has(id); };
const spellOf = id => { derive(); return _spell[id] || {}; };
// the card's text with the spelling fixes B approved applied
const suggOf = id => (derive(), _sugg[id]);          // 'ok' (use the suggested answer) | 'no' | undefined
const ackOf = id => (derive(), !!_ack[id]);
function textOf(c, f) { if (f === 'a' && c.suggest?.a && suggOf(c.id) === 'ok') return c.suggest.a; let t = c[f] ?? ''; const m = spellOf(c.id); for (const s of c.spell || []) if (m[s.bad] === 'ok') t = t.split(s.bad).join(s.good); return t; }
const byId = id => deck.cards.find(x => x.id === id);
function dupHidden(c) {
  derive();
  if (deckOf(c) === 'claude') { for (const d of c.dup || []) { const v = _dupc[c.id + '|' + d.id]; if (v === 'mine') return true; if (!v && settings.hideDups && d.sim >= .6) return true; } return false; }
  for (const d of c.dupBy || []) if (_dupc[d.id + '|' + c.id] === 'claude') return true;
  return false;
}
const visible = c => !isDropped(c.id) && c.check !== 'fail' && !dupHidden(c);
const pool = () => deck.cards.filter(c => visible(c) && !(settings.hideDrafts && c.review === 'draft') && (settings.deck === 'all' || deckOf(c) === settings.deck));

function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.random() * (i + 1) | 0; [a[i], a[j]] = [a[j], a[i]]; } return a; }

// full shuffle, with a nudge toward weak areas and cards missed before, and no two same-topic cards in a row
function mix(cards, st) {
  const k = c => Math.random() - (c.weak ? .2 : 0) - Math.min(.3, (st[c.id]?.lapses || 0) * .1) - (st[c.id]?.rl > 0 ? .4 : 0);
  const a = cards.map(c => [k(c), c]).sort((x, y) => x[0] - y[0]).map(x => x[1]), out = [];
  while (a.length) { const last = out[out.length - 1]?.topic; let i = a.findIndex(c => c.topic !== last); if (i < 0) i = 0; out.push(a.splice(i, 1)[0]); }
  return out;
}
function buildQueue(extra) {
  const st = replay(), P = pool(), now = Date.now();
  const due = P.filter(c => st[c.id] && st[c.id].due <= endOfToday());
  const unseen = P.filter(c => !st[c.id]);
  const inPool = new Set(P.map(c => c.id)), newToday = Object.entries(st).filter(([id, s]) => inPool.has(id) && sameDay(s.first, now)).length;
  const allow = extra ? unseen.length : Math.max(0, settings.newPerDay - newToday);
  const fresh = shuffle(unseen.slice()).sort((x, y) => (y.weak ? 1 : 0) - (x.weak ? 1 : 0)).slice(0, allow);
  return { st, queue: mix(due.concat(fresh), st), dueN: due.length, newN: fresh.length, unseenN: unseen.length };
}
function weakQueue() {
  const st = replay();
  return pool().filter(c => st[c.id] && (st[c.id].lapses > 0 || st[c.id].ok / st[c.id].n < .8));
}

// ---------- rendering helpers ----------
const tabs = { study: viewStudy, stats: viewStats, settings: viewSettings };
let tab = 'study';
function deckBar() {
  const n = k => deck.cards.filter(c => visible(c) && (k === 'all' || deckOf(c) === k)).length;
  $('#deckbar').innerHTML = DECKS.map(([k, l]) => `<button data-deck="${k}" class="${settings.deck === k ? 'on' : ''}">${l}<small> ${n(k)}</small></button>`).join('');
  $('#deckbar').querySelectorAll('button').forEach(b => b.onclick = () => { settings.deck = b.dataset.deck; kvSet('settings', settings); S = null; closeRef(); show(tab); });
}
function fitHeader() { document.documentElement.style.setProperty('--hh', document.querySelector('header').offsetHeight + 'px'); }
function studyMode(on) { $('#main').classList.toggle('study', on); document.body.classList.toggle('studying', on); fitHeader(); }
function show(t) {
  tab = t; studyMode(false); deckBar(); $('#deckbar').style.display = t === 'settings' ? 'none' : 'flex'; document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.tab === t));
  tabs[t]();
}
const cloze = (txt, reveal) => esc(txt).replace(/\{\{c\d+::(.*?)\}\}/g, (_, a) => `<span class="blank">${reveal ? a : '[&nbsp;&nbsp;&nbsp;…&nbsp;&nbsp;&nbsp;]'}</span>`);

function head(c) {
  return `<div class="meta"><span class="tag">${esc(c.topic)}</span>${c.review === 'draft' ? '<span class="tag draft">DRAFT</span>' : c.review === 'generated' ? '<span class="tag">AI-written · quote-checked</span>' : ''}${c.weak ? '<span class="tag">weak area</span>' : ''}${c.status === 'flagged' ? '<span class="tag draft">check this card</span>' : ''}</div>`;
}
// answers: lines starting with - • * or 1. 2) become list items; other lines stay paragraphs
function rich(s) {
  const lines = String(s ?? '').split('\n'); let html = '', items = [], ord = false;
  const flush = () => { if (items.length) { html += `<${ord ? 'ol' : 'ul'} class="lst">${items.map(t => `<li>${esc(t)}</li>`).join('')}</${ord ? 'ol' : 'ul'}>`; items = []; } };
  for (const raw of lines) {
    const m = raw.match(/^\s*(?:([-•*])\s+|(\d{1,2})[.)]\s*(?=\D))(.*)$/);
    if (m) { if (!items.length) ord = !!m[2]; items.push(m[3]); } else { flush(); if (raw.trim()) html += `<p>${esc(raw)}</p>`; }
  }
  flush(); return html;
}
const hasList = s => /(^|\n)\s*(?:[-•*]\s+|\d{1,2}[.)]\s*(?=\D))/.test(String(s ?? ''));
const ans = s => `<div class="ans${hasList(s) ? ' list' : ''}">${rich(s)}</div>`;

let curRefs = [];
const REL = { same: 'Also says', adds: 'Adds', conflicts: 'Differs', suggested: 'Suggested answer', diagram: 'Diagram' };
function refsOf(c) {
  const r = [];
  if (c.src && c.page && !c.nosrc) r.push({ src: c.src, page: c.page, cite: c.cite, quote: (c.quotes || []).join(' … '), primary: true });
  for (const x of c.also || []) r.push({ ...x });
  for (const d of c.diagrams || []) r.push({ src: d.src, page: d.page, cite: d.title && d.title !== 'Diagram' ? d.title : 'Diagram', rel: 'diagram' });
  if (c.suggest?.src) r.push({ src: c.suggest.src, page: c.suggest.page, cite: c.suggest.cite, quote: (c.suggest.quotes || []).join(' … '), rel: 'suggested' });
  return r;
}
function srcBlock(c) {
  curRefs = refsOf(c);
  const row = r => r.rel === 'diagram' ? `<div class="ref"><div class="rh"><span class="tag">Diagram</span> <b>${esc(r.cite)}</b> · ${esc(r.src)} p.${r.page} <button class="small" data-open="${esc(r.src)}:${r.page}">Open diagram</button></div></div>` : `<div class="ref${r.primary ? ' pri' : ''}"><div class="rh">${r.primary ? '' : `<span class="tag ${r.rel === 'conflicts' ? 'draft' : ''}">${REL[r.rel] || 'Also'}</span> `}<b>${esc(r.cite || r.src + ' p.' + r.page)}</b>${r.primary ? ' · ' + esc(deck.meta.revs?.[r.src] || '') : ''} <button class="small" data-open="${esc(r.src)}:${r.page}">Open page ${r.page}</button></div>${r.note ? `<div class="rn">${esc(r.note)}</div>` : ''}${r.quote ? `<q>${esc(r.quote)}</q>` : ''}</div>`;
  const shown = curRefs.filter(r => r.rel !== 'suggested');
  const none = !shown.length ? `<div class="ref muted">${esc(c.nolib || 'No source page is attached to this card.')}</div>` : '';
  return `<div class="src">${shown.map(row).join('')}${none}${c.note ? `<div class="rn" style="margin-top:8px">${esc(c.note)}</div>` : ''}</div>`;
}
const clozeQ = c => c.q.replace(/\{\{c\d+::(.*?)\}\}/g, '[…]');
const clozeA = c => [...c.q.matchAll(/\{\{c\d+::(.*?)\}\}/g)].map(m => m[1]).join('; ');
const qOf = c => c.type === 'cloze' ? clozeQ(c) : c.q;
const aOf = c => c.type === 'cloze' ? clozeA(c) : c.type === 'mc' ? c.choices[c.correct] : (c.a || '');
function pairHtml(p) {
  const { cl, me } = p, v = (derive(), _dupc[cl.id + '|' + me.id]), b = `data-cl="${esc(cl.id)}" data-me="${esc(me.id)}"`;
  const card = (c, who) => `<div class="dcard"><b>${who}</b><div class="dq">${esc(qOf(c))}</div><div class="rn"><b>Answer:</b> ${rich(aOf(c)) || '—'}</div>${c.src && !c.nosrc ? `<div class="rn">${esc(c.cite || '')} <button class="small" data-open="${esc(c.src)}:${c.page}">page ${c.page}</button></div>` : ''}</div>`;
  const state = v === 'mine' ? 'You kept yours; Claude’s is hidden.' : v === 'claude' ? 'You kept Claude’s; yours is hidden.' : v === 'both' ? 'You kept both.' : (settings.hideDups && p.sim >= .6 ? 'Not chosen yet: Claude’s is hidden by default.' : 'Not chosen yet: both are showing.');
  return `<div class="pair" ${b}>${card(me, 'Your card')}${card(cl, 'Claude’s card')}<div class="rn">${esc(state)}</div><div class="row2"><button class="small${v === 'mine' ? ' on' : ''}" data-dup="mine" ${b}>Keep mine</button><button class="small${v === 'claude' ? ' on' : ''}" data-dup="claude" ${b}>Keep Claude’s</button><button class="small${v === 'both' ? ' on' : ''}" data-dup="both" ${b}>Keep both</button></div></div>`;
}
const pairsOf = c => deckOf(c) === 'claude' ? (c.dup || []).map(d => ({ cl: c, me: byId(d.id), sim: d.sim })).filter(p => p.me) : (c.dupBy || []).map(d => ({ cl: byId(d.id), me: c, sim: d.sim })).filter(p => p.cl);
// a box B has dealt with shrinks to one line; tap it to open again
const openBoxes = new Set(), bkey = (c, k) => c.id + ':' + k;
const miniBox = (c, k, text, cls = '') => `<div class="alert min ${cls}" id="box-${k}" data-toggle="${esc(bkey(c, k))}" role="button">${text} <span class="muted">· tap to open</span></div>`;
const hideBtn = (c, k) => `<button class="mini" data-toggle="${esc(bkey(c, k))}">hide</button>`;
function dupBox(c) {
  const ps = pairsOf(c); if (!ps.length) return '';
  derive(); const ch = ps.map(p => _dupc[p.cl.id + '|' + p.me.id]), decided = ch.every(Boolean), open = openBoxes.has(bkey(c, 'dup'));
  if (decided && !open) { const v = ch[0]; return miniBox(c, 'dup', v === 'mine' ? '✓ Kept your card (Claude’s hidden)' : v === 'claude' ? '✓ Kept Claude’s card (yours hidden)' : '✓ Kept both cards'); }
  return `<div class="alert" id="box-dup"><b>A similar card exists in the other deck.</b> Choose which one you want:${ps.map(pairHtml).join('')}${decided ? hideBtn(c, 'dup') : ''}</div>`;
}
function spellHtml(c) {
  const m = spellOf(c.id);
  return '<b>Spelling</b>' + c.spell.map((s, i) => {
    const v = m[s.bad], b = `data-c="${esc(c.id)}" data-i="${i}"`;
    return `<div class="fix">${v === 'ok' ? `<span class="okx">✓ applied</span> <s>${esc(s.bad)}</s> → <b>${esc(s.good)}</b> <button class="mini" data-spell="undo" ${b}>undo</button>`
      : v === 'no' ? `<span class="muted">dismissed</span> <s>${esc(s.bad)}</s> → ${esc(s.good)} <button class="mini" data-spell="undo" ${b}>undo</button>`
      : `<s>${esc(s.bad)}</s> → <b>${esc(s.good)}</b> <button class="mini yes" data-spell="ok" ${b} aria-label="approve">✓</button><button class="mini no" data-spell="no" ${b} aria-label="discard">✗</button>`}</div>`;
  }).join('');
}
function spellBox(c) {
  if (!c.spell?.length) return '';
  const m = spellOf(c.id), vs = c.spell.map(s => m[s.bad]), decided = vs.every(Boolean), open = openBoxes.has(bkey(c, 'spell'));
  if (decided && !open) { const ok = vs.filter(v => v === 'ok').length; return miniBox(c, 'spell', ok ? `✓ Spelling: ${ok} fixed${ok < vs.length ? ', ' + (vs.length - ok) + ' kept' : ''}` : 'Spelling: kept as you wrote it'); }
  return `<div class="alert" id="box-spell">${spellHtml(c)}${decided ? hideBtn(c, 'spell') : ''}</div>`;
}
function suggBox(c) {
  if (!c.suggest?.a) return '';
  const v = suggOf(c.id), open = openBoxes.has(bkey(c, 'sugg'));
  if (v && !open) return miniBox(c, 'sugg', v === 'ok' ? '✓ Using the suggested answer' : 'Kept your answer', 'okbox');
  const s = c.suggest, b = `data-c="${esc(c.id)}"`;
  return `<div class="sugg" id="box-sugg"><b>Suggested answer</b>${rich(s.a)}${s.why ? `<div class="rn">${esc(s.why)}</div>` : ''}${s.src ? `<div class="rh"><b>${esc(s.cite || '')}</b> <button class="small" data-open="${esc(s.src)}:${s.page}">Open page ${s.page}</button></div>${s.quotes?.length ? `<q>${esc(s.quotes.join(' … '))}</q>` : ''}` : ''}<div class="row2"><button class="small${v === 'ok' ? ' on' : ''}" data-sugg="ok" ${b}>✓ Use this answer</button><button class="small${v === 'no' ? ' on' : ''}" data-sugg="no" ${b}>✗ Keep mine</button>${v ? hideBtn(c, 'sugg') : ''}</div></div>`;
}
function issueBox(c) {
  if (!(c.status === 'flagged' && c.issue)) return '';
  const decided = ackOf(c.id) || !!suggOf(c.id), open = openBoxes.has(bkey(c, 'issue'));
  if (decided && !open) return miniBox(c, 'issue', 'Noted: this card was flagged', 'badmin');
  return `<div class="alert bad" id="box-issue"><b>Check this card.</b> ${esc(c.issue)}<div class="row2"><button class="small" data-ack="${esc(c.id)}">${decided ? 'Noted' : 'Got it'}</button>${decided ? hideBtn(c, 'issue') : ''}</div></div>`;
}
const BOXES = { dup: dupBox, spell: spellBox, sugg: suggBox, issue: issueBox };
function refreshBox(c, k) { const el = document.getElementById('box-' + k); if (el) el.outerHTML = BOXES[k](c); }
function dupNote(c) { return dupBox(c); }
function mineBlock(c) {
  if (deckOf(c) !== 'mine') return dupBox(c);
  let h = issueBox(c);
  if (c.status === 'unmatched') h += `<div class="alert">The manual page is ${esc(c.src)} p.${c.page}, but the exact wording couldn't be matched there. Worth a look.</div>`;
  h += spellBox(c) + suggBox(c);
  if (!c.suggest?.a && c.nolib) h += `<div class="alert">${esc(c.nolib)}</div>`;
  return h + dupBox(c);
}
const reviewQueue = () => pool().filter(c => deckOf(c) === 'mine' && (c.status === 'flagged' || c.spell?.length || c.suggest?.a));

// diagrams: if a cited page has a large picture, show just that picture under the answer (needs the manual PDF on this device)
const figCache = {};
async function figBox(pg, key) {
  if (key in figCache) return figCache[key];
  const O = pdfjsLib.OPS, U = pdfjsLib.Util, vp = pg.getViewport({ scale: 1 }), ops = await pg.getOperatorList();
  let ctm = vp.transform.slice(), st = [], boxes = [];
  const img = () => { const p = [[0, 0], [1, 0], [0, 1], [1, 1]].map(q => U.applyTransform(q, ctm)), xs = p.map(q => q[0]), ys = p.map(q => q[1]);
    boxes.push([Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)]); };
  ops.fnArray.forEach((fn, i) => {
    const ar = ops.argsArray[i];
    if (fn === O.save) st.push(ctm.slice()); else if (fn === O.restore) ctm = st.pop() || ctm;
    else if (fn === O.transform) ctm = U.transform(ctm, ar);
    else if (fn === O.paintFormXObjectBegin) { st.push(ctm.slice()); if (ar[0]) ctm = U.transform(ctm, ar[0]); } else if (fn === O.paintFormXObjectEnd) ctm = st.pop() || ctm;
    else if (fn === O.paintImageXObject || fn === O.paintInlineImageXObject || fn === O.paintImageMaskXObject) img();
  });
  const pageArea = vp.width * vp.height, big = boxes.filter(b => b[2] - b[0] >= 120 && b[3] - b[1] >= 80 && (b[2] - b[0]) * (b[3] - b[1]) < pageArea * .8);
  if (!big.length) return figCache[key] = null;
  const x0 = Math.max(0, Math.min(...big.map(b => b[0])) - 6), y0 = Math.max(0, Math.min(...big.map(b => b[1])) - 6), x1 = Math.min(vp.width, Math.max(...big.map(b => b[2])) + 6), y1 = Math.min(vp.height, Math.max(...big.map(b => b[3])) + 6);
  return figCache[key] = { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
}
async function showFigs(c) {
  const el = document.getElementById('figs'); if (!el || el.dataset.done) return; el.dataset.done = 1;
  let shown = 0;
  const rs = refsOf(c).filter(r => r.rel !== 'suggested'), list = rs.filter(r => r.rel === 'diagram').concat(rs.filter(r => r.rel !== 'diagram'));
  for (const r of list) {
    if (shown >= 2) break;
    try {
      await ensurePdfLib(); const doc = await getDoc(r.src); if (!doc) continue;
      const pg = await doc.getPage(r.page); let box = await figBox(pg, r.src + ':' + r.page);
      if (!box && r.rel === 'diagram') { const v = pg.getViewport({ scale: 1 }); box = { x: 0, y: 0, w: v.width, h: v.height }; }
      if (!box) continue;
      const w = Math.max(220, el.clientWidth), scale = Math.min(3, w / box.w), d = window.devicePixelRatio || 1;
      const cv = document.createElement('canvas'); cv.width = box.w * scale * d; cv.height = box.h * scale * d; cv.style.width = '100%'; cv.style.height = 'auto';
      const vp = pg.getViewport({ scale, offsetX: -box.x * scale, offsetY: -box.y * scale });
      await pg.render({ canvasContext: cv.getContext('2d'), viewport: vp, transform: d !== 1 ? [d, 0, 0, d, 0, 0] : null }).promise;
      const fig = document.createElement('div'); fig.className = 'fig' + (refIsDark() ? ' dark' : ''); fig.dataset.open = r.src + ':' + r.page;
      fig.innerHTML = `<div class="rn">Diagram · ${esc(r.rel === 'diagram' ? r.cite + ' · ' + r.src + ' p.' + r.page : (r.cite || r.src + ' p.' + r.page))} · tap to open the page</div>`; fig.appendChild(cv); el.appendChild(fig); shown++;
    } catch (_) { /* no PDF or page: skip quietly */ }
  }
}
const gradeBtns = sug => [[1, 'Again'], [2, 'Hard'], [3, 'Good'], [4, 'Easy']]
  .map(([g, l]) => `<button class="g${g}${sug === g ? ' sug' : ''}" data-g="${g}">${l}</button>`).join('');

// ---------- review quizzes: the company review tests, in question order, scored ----------
// every topic of area 'key' is a quiz; the four company reviews first, then the rest by name
const QUIZ_ORDER = ['FOM Ch 4 review', 'FOM Ch 5 review', 'FOM Ch 10 review', 'Upgrade Weather review'];
const quizLabel = t => t.replace(/ review$/, '').replace(/^Upgrade /, '');
const quizTopics = () => [...new Set(deck.cards.filter(c => c.area === 'key').map(c => c.topic))].sort((a, b) => ((QUIZ_ORDER.indexOf(a) + 1 || 99) - (QUIZ_ORDER.indexOf(b) + 1 || 99)) || a.localeCompare(b, undefined, { numeric: true }));
const noScore = c => c.noscore || /^(Not answerable|I don't know)/.test(c.a || '');
const quizCards = t => deck.cards.filter(c => c.topic === t && !isDropped(c.id)).sort((a, b) => a.id.localeCompare(b.id, undefined, { numeric: true }));
const quizState = t => ({ quiz: t, qn: 0, qok: 0, miss: [], retry: [], round: 1, roundStart: 0 });
function startRedo(t, cards) { if (!cards.length) return; delete sessions.quiz[t + REDO]; S = { queue: mix(cards, replay()), i: 0, shown: false, t0: Date.now(), total: cards.length, done: 0, rl: {}, ...quizState(t), redo: true }; viewStudy(); }
function quizBox() {
  const q = quizTopics().map(t => [t, quizLabel(t), quizCards(t).length]).filter(x => x[2]);
  if (!q.length) return '';
  return `<div class="card" style="margin-top:12px"><div class="q" style="font-size:1.05em">Review quizzes</div><p class="muted">The company tests, in order, with a score at the end.</p><div class="qz">${q.map(([t, l, n]) => { const r = settings.quiz?.[t]; const p = sessions.quiz[t]; return `<button data-quiz="${esc(t)}"${p ? ' class="paused"' : ''}><b>${esc(l)}</b><small>${p ? `▶ resume at ${p.i + 1} of ${p.ids.length}` : `${n} questions${r ? ` · last ${r.ok}/${r.n}` : ''}`}</small></button>`; }).join('')}</div>${q.filter(([t]) => sessions.quiz[t]).map(([t, l]) => `<div class="qrs"><span>${esc(l)} paused at ${sessions.quiz[t].i + 1}</span><button class="small" data-qrestart="${esc(t)}">Start over</button></div>`).join('')}${q.filter(([t]) => sessions.quiz[t + REDO] || settings.quizMiss?.[t]?.length).map(([t, l]) => { const p = sessions.quiz[t + REDO]; return `<div class="qrs"><span>${esc(l)}: ${p ? `missed drill paused at ${p.i + 1} of ${p.ids.length}` : `${settings.quizMiss[t].length} missed last time`}</span><button class="small" data-qredo="${esc(t)}">${p ? 'Resume drill' : 'Redo missed'}</button></div>`; }).join('')}</div>`;
}

// ---------- study ----------
function viewStudy() {
  if (!deck.cards.length) return $('#main').innerHTML = `<div class="card"><div class="q">No deck loaded</div><p class="muted">Settings → Load deck file, and pick <b>deck.json</b>.</p></div>`;
  if (!S) {
    const b = buildQueue(false), weak = weakQueue().length;
    const sv = sessions.study && sessions.study.i < sessions.study.ids.length ? sessions.study : null;
    $('#main').innerHTML = (sv ? `<div class="card resume"><div><b>Paused session</b><small>card ${sv.i + 1} of ${sv.ids.length}</small></div><button class="pri" id="rsm">Resume</button><button class="small" id="rsx">Discard</button></div>` : '') + `<div class="grid"><div class="card"><div class="big">${b.dueN}</div><small>due</small></div><div class="card"><div class="big">${b.newN}</div><small>new today</small></div><div class="card"><div class="big">${weak}</div><small>weak</small></div></div>
      ${b.queue.length ? `<button class="pri" style="width:100%" id="go">Start ${b.queue.length} cards</button>` : `<div class="card"><div class="q">Nothing due.</div><p class="muted">${b.unseenN} unseen cards are held back by the daily limit.</p></div>`}
      <div class="row" style="margin-top:10px">${b.unseenN ? `<button id="more">Study unseen (${b.unseenN})</button>` : ''}${weak ? `<button id="wk">Drill weak (${weak})</button>` : ''}${reviewQueue().length ? `<button id="rv">My cards to check (${reviewQueue().length})</button>` : ''}</div>${quizBox()}`;
    const go = (q, extra) => { S = { queue: q.slice(), i: 0, shown: false, t0: Date.now(), total: q.length, done: 0, rl: {}, ...extra }; viewStudy(); };
    if ($('#rsm')) $('#rsm').onclick = () => resumeSess(sessions.study);
    if ($('#rsx')) $('#rsx').onclick = () => { sessions.study = null; kvSet('sessions', sessions); viewStudy(); };
    if ($('#go')) $('#go').onclick = () => go(b.queue);
    if ($('#more')) $('#more').onclick = () => go(buildQueue(true).queue);
    if ($('#wk')) $('#wk').onclick = () => go(mix(weakQueue(), b.st));
    if ($('#rv')) $('#rv').onclick = () => go(mix(reviewQueue(), b.st));
    document.querySelectorAll('[data-quiz]').forEach(x => x.onclick = () => { const t = x.dataset.quiz; if (sessions.quiz[t]) resumeSess(sessions.quiz[t], t); else go(quizCards(t), quizState(t)); });
    document.querySelectorAll('[data-qrestart]').forEach(x => x.onclick = () => { const t = x.dataset.qrestart; delete sessions.quiz[t]; kvSet('sessions', sessions); go(quizCards(t), quizState(t)); });
    document.querySelectorAll('[data-qredo]').forEach(x => x.onclick = () => { const t = x.dataset.qredo, p = sessions.quiz[t + REDO]; if (p) return resumeSess(p, t + REDO); startRedo(t, (settings.quizMiss?.[t] || []).map(byId).filter(Boolean)); });
    return;
  }
  saveSess();
  if (S.i >= S.queue.length) {
    studyMode(false); syncNow(true);
    if (S.quiz) {
      if (!S.redo) (settings.quiz ||= {})[S.quiz] = { ok: S.qok, n: S.qn, t: Date.now() };
      (settings.quizMiss ||= {})[S.quiz] = S.miss.map(c => c.id); if (!S.miss.length) delete settings.quizMiss[S.quiz];
      kvSet('settings', settings);
      const title = S.redo ? `Missed drill (${esc(S.quiz)}): ${S.qok} / ${S.qn} right first time` : `${esc(S.quiz)}: ${S.qok} / ${S.qn}${S.qn ? ` (${Math.round(S.qok / S.qn * 100)}%)` : ''}`;
      $('#main').innerHTML = `<div class="card"><div class="q">${title}</div>${S.round > 1 ? `<p>Every missed question answered right after ${S.round} rounds.</p>` : ''}<p class="muted">The score counts your first answer only. Questions your library can't answer (they need a chart or a manual you don't have) were shown, not scored.</p>${S.miss.length ? `<button class="pri" style="width:100%;margin-bottom:10px" id="rdm">Redo the ${S.miss.length} I missed</button><p><b>Missed</b></p>${S.miss.map(c => `<p class="muted">${esc(c.q.split('\n')[0].slice(0, 140))}<br><b>${esc(c.a || '')}</b> · ${esc(c.cite || '')}</p>`).join('')}` : ''}<button class="${S.miss.length ? '' : 'pri'}" id="fin">Back</button></div>`;
      const t = S.quiz, m = S.miss.slice(); if ($('#rdm')) $('#rdm').onclick = () => startRedo(t, m);
    } else
    $('#main').innerHTML = `<div class="card"><div class="q">Session done</div><p class="muted">${S.done} answers.</p><button class="pri" id="fin">Back</button></div>`;
    $('#fin').onclick = () => { S = null; viewStudy(); }; return;
  }
  studyMode(true); S.cur = null; const c = S.queue[S.i]; S.t0 = Date.now(); S.shown = false; S.errors = 0; S.pos = 0;
  const prog = `<div class="prog"><i style="width:${S.i / S.queue.length * 100}%"></i></div>` + (S.quiz && S.round > 1 ? `<div class="rnd">Round ${S.round}: the ${S.queue.length - S.roundStart} you missed · ${S.queue.length - S.i} left</div>` : S.quiz && S.redo ? `<div class="rnd">Missed drill · ${S.queue.length - S.i} left</div>` : '');
  const body = { flip: rFlip, cloze: rCloze, mc: rMc, typed: rTyped, steps: rSteps }[c.type] || rFlip;
  $('#main').innerHTML = prog + `<div class="card" id="cc">${head(c)}</div><div id="ctl"></div>`;
  body(c);
}
function done(c, g) {
  const ev = { id: uid(), c: c.id, t: Date.now(), g, ms: Date.now() - S.t0, d: settings.device };
  events.push(ev); save(); S.done++;
  const rnd = (lo, hi) => lo + (Math.random() * (hi - lo + 1) | 0);
  S.rl ||= {}; S.hist ||= [];
  const h = { id: ev.id, c, i: S.i, prevRl: S.rl[c.id], pos: null };
  const put = k => { h.pos = Math.min(S.queue.length, S.i + 1 + k); S.queue.splice(h.pos, 0, c); };
  if (S.quiz) {                                 // first answer is scored; a miss comes back in the next round until it is answered right
    h.quiz = !noScore(c) && S.round === 1; if (h.quiz) { S.qn++; if (g > 1) S.qok++; else S.miss.push(c); h.qok = g > 1; }
    if (!noScore(c) && g === 1) { S.retry.push(c); h.retry = true; }
    S.hist.push(h); S.i++;
    if (S.i >= S.queue.length && S.retry.length) { h.roundAdd = S.retry.slice(); S.roundStart = S.queue.length; S.queue.push(...mix(S.retry, replay())); S.retry = []; S.round++; }
    return viewStudy();
  }
  if (g === 1) { S.rl[c.id] = 2; put(rnd(7, 11)); }                                   // missed: back after ~7-11 cards, again after that
  else if (S.rl[c.id] > 0) { S.rl[c.id]--; if (S.rl[c.id] > 0) put(rnd(14, 20)); else delete S.rl[c.id]; }
  S.hist.push(h); S.i++; viewStudy();
}
// go back one card: the answer is undone (kept in the log as an 'undo' so it merges across devices) and the card is shown again
function undoLast() {
  if (!S?.hist?.length) return;
  const h = S.hist.pop();
  events.push({ id: uid(), k: 'undo', c: h.c.id, t: Date.now(), ref: h.id }); save();
  if (h.pos != null && h.pos > h.i && S.queue[h.pos]?.id === h.c.id) S.queue.splice(h.pos, 1);
  if (h.prevRl === undefined) delete S.rl[h.c.id]; else S.rl[h.c.id] = h.prevRl;
  if (h.roundAdd) { S.queue.length -= h.roundAdd.length; S.retry = h.roundAdd; S.round--; }
  if (h.retry) S.retry.pop();
  if (h.quiz) { S.qn--; if (h.qok) S.qok--; else S.miss.pop(); }
  S.done = Math.max(0, S.done - 1); S.i = h.i; viewStudy();
}
function reveal(c, html) {
  $('#cc').insertAdjacentHTML('beforeend', html + mineBlock(c) + '<div id="figs"></div>' + srcBlock(c)); showFigs(c);
}
function flagBtn(c) {
  return `<div class="row2"><button class="small" id="flag">⚑ Flag this card</button><button class="small" id="drop">🗑 Not needed</button><button class="small" id="back"${S?.hist?.length ? '' : ' disabled'}>↶ Undo</button></div>`;
}
function toast(msg, undo) {
  let t = $('#toast'); if (!t) { t = document.createElement('div'); t.id = 'toast'; document.body.appendChild(t); }
  t.innerHTML = `${esc(msg)}${undo ? ' <button class="small" id="tundo">Undo</button>' : ''}`; t.classList.add('on');
  if (undo) $('#tundo').onclick = () => { undo(); t.classList.remove('on'); };
  clearTimeout(t._h); t._h = setTimeout(() => t.classList.remove("on"), 10000);
}
function dropCard(c, v) {
  events.push({ id: uid(), k: 'drop', c: c.id, t: Date.now(), v }); save();
}
function wireFlag(c) {
  const bk = $('#back'); if (bk) bk.onclick = undoLast;
  const dp = $('#drop');
  // two taps on the same button: the first arms it for 3 s, the second discards (no dialog elsewhere on the screen)
  if (dp) dp.onclick = () => {
    if (!dp.classList.contains('arm')) {
      dp.classList.add('arm'); dp.textContent = 'Tap again to discard';
      clearTimeout(dp._h); dp._h = setTimeout(() => { dp.classList.remove('arm'); dp.textContent = '🗑 Not needed'; }, 3000); return;
    }
    clearTimeout(dp._h); dropCard(c, 1);
    if (S) { S.queue = S.queue.filter((x, i) => i < S.i || x.id !== c.id); viewStudy(); }
    toast('Card discarded. Settings → Your edits to restore it.', () => { dropCard(c, 0); if (S) { S.queue.splice(S.i, 0, c); viewStudy(); } });
  };
  const f = $('#flag'); if (!f) return;
  f.onclick = () => { const note = prompt('What is wrong with this card?'); if (note) { events.push({ id: uid(), k: 'flag', c: c.id, t: Date.now(), note }); save(); f.textContent = 'Flagged'; f.disabled = true; } };
}
function gradePanel(c, sug) {
  $('#ctl').innerHTML = `<div class="row">${gradeBtns(sug)}</div>${flagBtn(c)}`;
  $('#ctl').querySelectorAll('[data-g]').forEach(b => b.onclick = () => done(c, +b.dataset.g));
  wireFlag(c);
}
// a question with a blank line: the first part is the question, the rest (options, weather data) a smaller left-aligned block
const qHtml = s => { const i = String(s ?? '').indexOf('\n\n'); return i < 0 ? esc(s) : esc(s.slice(0, i)) + `<span class="qx">${esc(s.slice(i + 2))}</span>`; };
function rFlip(c) { rSwipe(c, `<div class="q" data-f="q">${qHtml(textOf(c, 'q'))}</div>`, `<div data-f="a">${ans(textOf(c, 'a'))}</div>`); }
function rCloze(c) { rSwipe(c, `<div class="q">${cloze(c.q, false)}</div>`, `<div class="q">${cloze(c.q, true)}</div>`); }
// flip card: tap to flip; drag right = got it, left = missed (buttons and arrow keys do the same)
function rSwipe(c, front, back) {
  const cc = $('#cc'); cc.className = 'plain';
  cc.innerHTML = `<div class="swipe"><div class="drag" id="dr"><div class="sc" id="sc">
    <div class="face front">${head(c)}<div class="fc">${front}</div><div class="hint">Tap to flip</div></div>
    <div class="face back">${head(c)}<div class="bs" id="bs">${back}${mineBlock(c)}<div id="figs"></div>${srcBlock(c)}</div></div></div>
    <div class="tint ok" id="tok"></div><div class="tint no" id="tno"></div></div></div>`;
  $('#ctl').innerHTML = `<div class="row"><button class="g1" id="bx">✗ Missed</button><button class="g3" id="bo">✓ Got it</button></div><p class="note kbd" style="text-align:center;margin:6px 0">Keyboard: Space flips · → got it · ← missed</p>${flagBtn(c)}`;
  wireFlag(c);
  const dr = $('#dr'), sc = $('#sc'), tok = $('#tok'), tno = $('#tno'), bs = $('#bs');
  let x0 = null, y0 = 0, off = 0, dx = 0, mode = null, busy = false, raf = 0, mom = 0, hist = [], sc0 = 0, flipped = false;
  const paint = () => { raf = 0; dr.style.transform = `translate3d(${dx}px,0,0) rotate(${dx / 28}deg)`; const t = Math.min(.55, Math.abs(dx) / 240); tok.style.opacity = dx > 0 ? t : 0; tno.style.opacity = dx < 0 ? t : 0; };
  const reset = () => { x0 = null; mode = null; dr.style.transition = 'transform .18s ease-out'; dr.style.transform = ''; tok.style.opacity = 0; tno.style.opacity = 0; };
  const grade = (g, fast) => { if (busy) return; busy = true; cancelAnimationFrame(mom); dr.style.transition = `transform ${fast ? .14 : .2}s ease-in, opacity ${fast ? .14 : .2}s`; dr.style.transform = `translate3d(${g === 3 ? 130 : -130}%,0,0) rotate(${g === 3 ? 16 : -16}deg)`; dr.style.opacity = 0; setTimeout(() => done(c, g), fast ? 120 : 170); };
  const flip = () => { flipped = !flipped; sc.classList.toggle('flipped', flipped); if (flipped) showFigs(c); };
  S.cur = { flip, grade };
  $('#bx').onclick = () => grade(1); $('#bo').onclick = () => grade(3);
  // The card owns every touch (touch-action: none), so a sideways swipe and a scroll of the answer can never fight:
  // after 8 px we decide once. Sideways = swipe the card; up/down = scroll the answer by hand, with a little momentum.
  const skip = t => t.closest('button,input,textarea,select,a');
  const momentum = v => { cancelAnimationFrame(mom); let last = performance.now(); const step = t => { const dt = t - last; last = t; const before = bs.scrollTop; bs.scrollTop += v * dt; v *= Math.pow(.94, dt / 16); if (Math.abs(v) > .02 && bs.scrollTop !== before) mom = requestAnimationFrame(step); }; mom = requestAnimationFrame(step); };
  dr.onpointerdown = e => { if (busy || skip(e.target)) return; cancelAnimationFrame(mom); x0 = e.clientX; y0 = e.clientY; dx = 0; off = 0; mode = null; sc0 = bs.scrollTop; hist = [[e.timeStamp, e.clientX, e.clientY]]; dr.style.transition = 'none'; };
  dr.onpointermove = e => {
    if (x0 === null) return;
    const rx = e.clientX - x0, ry = e.clientY - y0;
    if (!mode) { if (Math.hypot(rx, ry) < 8) return; mode = Math.abs(rx) > Math.abs(ry) * 1.1 ? 'h' : 'v'; if (mode === 'h') off = rx; try { dr.setPointerCapture(e.pointerId); } catch (_) {} }
    hist.push([e.timeStamp, e.clientX, e.clientY]); if (hist.length > 6) hist.shift();
    if (mode === 'h') { dx = rx - off; if (!raf) raf = requestAnimationFrame(paint); }
    else if (flipped) bs.scrollTop = sc0 - ry;
  };
  dr.onpointerup = e => {
    if (x0 === null) return; const m = mode; x0 = null;
    if (!m) { if (!e.target.closest('.fig')) flip(); return; }                       // a tap flips the card
    const a0 = hist[0], a1 = hist[hist.length - 1], dt = a1[0] - a0[0] || 1;
    if (m === 'v') { if (flipped) momentum(-(a1[2] - a0[2]) / dt); return; }
    const v = (a1[1] - a0[1]) / dt;                                                  // px per ms
    if (Math.abs(dx) > 70 || (Math.abs(v) > .5 && Math.abs(dx) > 24)) grade((Math.abs(dx) > 70 ? dx : v) > 0 ? 3 : 1, true); else reset();
  };
  dr.onpointercancel = reset;
}
document.addEventListener('keydown', e => {
  if (!S?.cur || e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
  if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); S.cur.flip(); }
  else if (e.key === 'ArrowRight') S.cur.grade(3); else if (e.key === 'ArrowLeft') S.cur.grade(1);
});
function rMc(c) {
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${qHtml(c.q)}</div><div style="margin-top:12px">${c.choices.map((x, i) => `<button class="choice" data-i="${i}">${esc(x)}</button>`).join('')}</div>`);
  $('#cc').querySelectorAll('.choice').forEach(b => b.onclick = () => {
    const i = +b.dataset.i, ok = i === c.correct;
    $('#cc').querySelectorAll('.choice').forEach((x, j) => { x.disabled = true; if (j === c.correct) x.classList.add('right'); });
    if (!ok) b.classList.add('wrong');
    reveal(c, c.a ? `<div class="a">${rich(c.a)}</div>` : '');
    $('#ctl').innerHTML = `<button class="pri" style="width:100%" id="nx">Next</button>${flagBtn(c)}`;
    $('#nx').onclick = () => done(c, ok ? 3 : 1); wireFlag(c);
  });
}
// typed recall with word diff
const normTxt = s => s.toLowerCase().replace(/^\s*\d+\.\s*/gm, '').replace(/[:.,;()"']/g, ' ').split(/\s+/).filter(Boolean);
function lcsDiff(exp, got) {
  const n = exp.length, m = got.length, L = Array.from({ length: n + 1 }, () => new Array(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) L[i][j] = exp[i] === got[j] ? L[i + 1][j + 1] + 1 : Math.max(L[i + 1][j], L[i][j + 1]);
  const out = []; let i = 0, j = 0;
  while (i < n && j < m) {
    if (exp[i] === got[j]) { out.push(['ok', exp[i]]); i++; j++; }
    else if (L[i + 1][j] >= L[i][j + 1]) { out.push(['miss', exp[i]]); i++; } else { out.push(['extra', got[j]]); j++; }
  }
  while (i < n) out.push(['miss', exp[i++]]); while (j < m) out.push(['extra', got[j++]]);
  return out;
}
function rTyped(c) {
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${qHtml(c.q)}</div><textarea id="ta" rows="6" autocapitalize="off" autocomplete="off" autocorrect="off" spellcheck="false" placeholder="Type it from memory"></textarea>`);
  $('#ctl').innerHTML = `<button class="pri" style="width:100%" id="sh">Check</button>`;
  $('#sh').onclick = () => {
    const exp = normTxt(c.a), got = normTxt($('#ta').value), d = lcsDiff(exp, got);
    const miss = d.filter(x => x[0] !== 'ok').length, sug = miss === 0 ? 3 : miss <= Math.max(1, exp.length * .15) ? 2 : 1;
    $('#ta').disabled = true;
    reveal(c, `<div class="a diff">${d.map(([k, w]) => `<span class="${k}">${esc(w)}</span>`).join(' ')}</div><div class="a">${rich(c.a)}</div>`);
    gradePanel(c, sug);
  };
}
function rSteps(c) {
  const order = shuffle(c.steps.map((s, i) => i));
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${qHtml(c.q)}</div><p class="muted">Tap the steps in order.</p><div id="sl">${order.map(i => `<button class="step" data-i="${i}">${esc(c.steps[i])}</button>`).join('')}</div>`);
  $('#sl').querySelectorAll('.step').forEach(b => b.onclick = () => {
    if (b.classList.contains('done')) return;
    if (+b.dataset.i === S.pos) {
      b.classList.add('done'); S.pos++;
      if (S.pos === c.steps.length) {
        const g = S.errors === 0 ? 3 : S.errors <= 2 ? 2 : 1;
        reveal(c, `<div class="a">${S.errors ? S.errors + ' wrong tap(s).' : 'Clean.'}</div>`);
        $('#ctl').innerHTML = `<button class="pri" style="width:100%" id="nx">Next</button>${flagBtn(c)}`;
        $('#nx').onclick = () => done(c, g); wireFlag(c);
      }
    } else { S.errors++; b.classList.add('shake'); setTimeout(() => b.classList.remove('shake'), 400); }
  });
}

// ---------- progress ----------
function viewStats() {
  const st = replay(), P = pool(), now = Date.now(), rev = (derive(), events.filter(e => !e.k && !_undone.has(e.id)));
  const seen = P.filter(c => st[c.id]).length, dueN = P.filter(c => st[c.id] && st[c.id].due <= endOfToday()).length;
  const days = new Set(rev.map(e => new Date(e.t).toDateString()));
  let streak = 0; for (let d = new Date(); days.has(d.toDateString()); d.setDate(d.getDate() - 1)) streak++;
  const w7 = rev.filter(e => e.t > now - 7 * DAY), acc7 = w7.length ? Math.round(w7.filter(e => e.g >= 2).length / w7.length * 100) : null;
  const topics = {};
  for (const c of P) { const t = topics[c.topic] ||= { n: 0, seen: 0, rv: 0, ok: 0, lap: 0 }; t.n++; const s = st[c.id]; if (s) { t.seen++; t.rv += s.n; t.ok += s.ok; t.lap += s.lapses; } }
  const rows = Object.entries(topics).sort().map(([k, t]) => { const a = t.rv ? Math.round(t.ok / t.rv * 100) : null; return `<tr><td>${esc(k)}<div class="bar ${a === null ? '' : a < 70 ? 'low' : a < 85 ? 'mid' : ''}"><i style="width:${a ?? 0}%"></i></div></td><td class="n">${t.seen}/${t.n}</td><td class="n">${a === null ? '–' : a + '%'}</td><td class="n">${t.lap}</td></tr>`; }).join('');
  const weak = P.filter(c => st[c.id] && st[c.id].ok < st[c.id].n).sort((a, b) => st[b.id].lapses - st[a.id].lapses || st[a.id].ok / st[a.id].n - st[b.id].ok / st[b.id].n).slice(0, 10)
    .map(c => `<tr><td>${esc(c.q.replace(/\{\{c\d+::(.*?)\}\}/g, '[$1]').slice(0, 90))}<div class="muted" style="font-size:13px">${esc(c.cite)}</div></td><td class="n">${Math.round(st[c.id].ok / st[c.id].n * 100)}%</td><td class="n">${st[c.id].lapses}</td></tr>`).join('');
  const flags = events.filter(e => e.k === 'flag').map(e => `<tr><td>${esc(e.c)}<div class="muted">${esc(e.note)}</div></td></tr>`).join('');
  const check = settings.checkDate ? Math.ceil((new Date(settings.checkDate + 'T00:00:00') - now) / DAY) : null;
  $('#main').innerHTML = `<div class="grid"><div class="card"><div class="big">${seen}/${P.length}</div><small>cards seen</small></div><div class="card"><div class="big">${dueN}</div><small>due today</small></div><div class="card"><div class="big">${streak}</div><small>day streak</small></div></div>
    <div class="card"><b>7-day accuracy:</b> ${acc7 === null ? '–' : acc7 + '%'} (${w7.length} answers)${check !== null ? ` · <b>${check}</b> days to check date` : ''}</div>
    <h2>By topic</h2><div class="card"><table><tr><th>Topic</th><th class="n">Seen</th><th class="n">Acc</th><th class="n">Lapses</th></tr>${rows}</table></div>
    <h2>Weakest cards</h2><div class="card">${weak ? `<table><tr><th>Card</th><th class="n">Acc</th><th class="n">Lapses</th></tr>${weak}</table>` : '<span class="muted">No misses yet.</span>'}</div>
    ${(() => { const n = reviewQueue().length; return n ? `<h2>Your cards</h2><div class="card"><b>${n}</b> of your cards need a look: a wrong or incomplete answer, a spelling fix, or a suggested better answer with a reference.<div class="row" style="margin-top:10px"><button id="rv2">Study those ${n}</button></div></div>` : ''; })()}
    ${flags ? `<h2>Flagged</h2><div class="card"><table>${flags}</table></div>` : ''}`;
  if ($('#rv2')) $('#rv2').onclick = () => { S = { queue: mix(reviewQueue(), st), i: 0, shown: false, t0: Date.now(), total: 0, done: 0, rl: {} }; show('study'); };
}

// ---------- settings / import / export ----------
function viewSettings() {
  const dr = deck.cards.filter(c => c.review === 'draft').length, dups = deck.cards.filter(c => c.dup?.some(d => d.sim >= .6)).length;
  $('#main').innerHTML = `<div class="card"><b>Deck</b><p class="note">${deck.cards.length} cards (${dr} draft, ${dups} of Claude's duplicate yours) · built ${esc(deck.meta.built || 'never')}<br>${esc(Object.entries(deck.meta.revs || {}).map(([k, v]) => k + ' ' + v).join(' · '))}</p>
    <label for="df">Load deck file (deck.json)</label><input type="file" id="df" accept=".json,application/json"></div>
    <div class="card"><b>Manuals (for the side-by-side page viewer)</b>
    <p class="note" id="mst">Checking…</p>
    <label for="mf">Load manual PDFs (POH, QRH, FOM, PRM, OpsSpecs, MEL, CDL, QUAL lessons)</label><input type="file" id="mf" accept=".pdf,application/pdf" multiple>
    <p class="note">Stored only on this device. Nothing is uploaded.</p></div>
    <div class="card"><b>Study</b>
    <label for="cd">Check date</label><input type="date" id="cd" value="${esc(settings.checkDate)}">
    <p class="note">Review gaps are capped at half the days left, so nothing is scheduled past the check.</p>
    <label for="np">New cards per day</label><input type="number" id="np" min="0" max="200" value="${settings.newPerDay}">
    <label><input type="checkbox" id="hd" ${settings.hideDrafts ? 'checked' : ''}> Hide DRAFT cards</label>
    <label><input type="checkbox" id="hdup" ${settings.hideDups ? 'checked' : ''}> Hide Claude's cards that duplicate one of mine</label>
    <label for="rdk">Manual page viewer</label><select id="rdk"><option value="auto">Dark when the device is dark</option><option value="on">Always dark</option><option value="off">Always light</option></select></div>
    <div class="card"><b>Pomodoro timer</b><p class="note" id="pmn"></p>
    <div class="row" style="gap:10px"><div style="flex:1"><label for="pf1">Focus (min)</label><input type="number" id="pf1" min="1" max="120"></div><div style="flex:1"><label for="pf2">Short break</label><input type="number" id="pf2" min="1" max="60"></div><div style="flex:1"><label for="pf3">Long break</label><input type="number" id="pf3" min="1" max="90"></div><div style="flex:1"><label for="pf4">Long every</label><input type="number" id="pf4" min="2" max="12"></div></div>
    <div class="row" style="margin-top:10px"><button id="pbeep">Test the sound</button><button id="preset">Reset timer</button></div></div>
    <div class="card"><b>Library (deck and manuals from GitHub)</b><p class="note" id="lbs"></p><div id="lbui"></div></div>
    <div class="card"><b>Sync between devices</b><p class="note" id="syn"></p><div id="synui"></div></div>
    <div class="card"><b>Duplicates</b><p class="note" id="dupn"></p><div class="row"><button id="dupgo">Review similar cards</button></div></div>
    <div class="card"><b>Your edits</b><p class="note" id="edits"></p></div>
    <div class="card"><b>Progress</b><p class="note">${events.length} events · device ${esc(settings.device)}. Export from one device, import on another. Merging is safe to repeat.</p>
    <div class="row"><button id="ex" class="pri">Export / share</button></div>
    <label for="pf">Import progress file</label><input type="file" id="pf" accept=".json,application/json"><p class="note" id="msg"></p></div>
    <div class="card"><span class="muted" id="per"></span></div>`;
  $('#df').onchange = async e => {
    try {
      const d = JSON.parse(await e.target.files[0].text());
      if (!Array.isArray(d.cards)) throw new Error('no cards array');
      deck = d; await kvSet('deck', deck); viewSettings(); $('#msg').textContent = 'Deck loaded.';
    } catch (err) { $('#msg').textContent = 'Not a valid deck: ' + err.message; }
  };
  $('#cd').onchange = e => { settings.checkDate = e.target.value; settings.cfgT = Date.now(); kvSet('settings', settings); };
  $('#np').onchange = e => { settings.newPerDay = Math.max(0, +e.target.value || 0); settings.cfgT = Date.now(); kvSet('settings', settings); };
  $('#hd').onchange = e => { settings.hideDrafts = e.target.checked; kvSet('settings', settings); };
  $('#hdup').onchange = e => { settings.hideDups = e.target.checked; kvSet('settings', settings); deckBar(); };
  $('#rdk').value = settings.refDark; $('#rdk').onchange = e => { settings.refDark = e.target.value; kvSet('settings', settings); };
  $('#ex').onclick = exportProgress;
  (() => {
    const c = PC(), p = PS(), t = p.day === new Date().toDateString() ? p.today : 0;
    $('#pmn').textContent = `Tap the 🍅 in the top bar to start a focus round. When it ends a break starts by itself; every ${c.every}th break is the long one. ${t} 🍅 done today.`;
    [['pf1', 'focus'], ['pf2', 'short'], ['pf3', 'long'], ['pf4', 'every']].forEach(([id, k]) => { $('#' + id).value = c[k]; $('#' + id).onchange = e => { const v = Math.max(1, Math.round(+e.target.value || c[k])); settings.pomoCfg = { ...PC(), [k]: v }; kvSet('settings', settings); e.target.value = v; }; });
    $('#pbeep').onclick = () => beep(2); $('#preset').onclick = () => { Object.assign(PS(), { phase: 'idle', endAt: 0, paused: false, remain: 0 }); pSave(); pPaint(); };
  })();
  (() => {
    const lb = settings.lib, ui = $('#lbui'), st = $('#lbs');
    if (lb?.repo && lb?.token) {
      st.innerHTML = `Repo ${esc(lb.repo)}. ${esc(lb.msg || '')}${lb.built ? '<br>Published: ' + esc(lb.built) : ''}${lb.checked ? '<br>Last checked: ' + new Date(lb.checked).toLocaleString() : ''}<br>The app checks once a day when you open it and asks before downloading.`;
      ui.innerHTML = `<div class="row"><button class="pri" id="ldl">Check and download now</button><button id="lcode">Show library code</button><button id="loff">Turn off here</button></div><div class="prog" style="margin-top:10px;display:none" id="lpg"><i style="width:0"></i></div><p class="note" id="lmsg"></p><textarea id="lbox" rows="3" readonly style="display:none"></textarea>`;
      $('#ldl').onclick = async () => {
        $('#lmsg').textContent = 'Checking…'; const p = await libCheck(); settings.lib.checked = Date.now(); await kvSet('settings', settings);
        if (p === null) { $('#lmsg').textContent = settings.lib.msg; return; }
        if (!p.length) { $('#lmsg').textContent = 'Already up to date.'; return; }
        const pg = $('#lpg'); pg.style.display = 'block';
        try { await libDownload(null, (f, g, t) => { $('#lmsg').textContent = `${f.path}: ${(g / 1048576).toFixed(1)} of ${(t / 1048576).toFixed(1)} MB`; pg.firstChild.style.width = Math.min(100, g / t * 100) + '%'; }); const el = $('#libprompt'); if (el) el.style.display = 'none'; $('#lmsg').textContent = 'Done. ' + settings.lib.msg; deckBar(); } catch (e) { $('#lmsg').textContent = e.message; }
      };
      $('#lcode').onclick = () => { const b = $('#lbox'); b.style.display = 'block'; b.value = btoa(JSON.stringify({ r: lb.repo, t: lb.token })); b.select(); };
      $('#loff').onclick = async () => { settings.lib = null; await kvSet('settings', settings); viewSettings(); };
    } else {
      st.textContent = 'Off. The deck and the manual PDFs can come from a private GitHub repo instead of AirDrop. Checks once a day and asks before it downloads.';
      ui.innerHTML = `<label><b>First device</b></label><p class="note">Make a read-only token for the repo: <a href="https://github.com/settings/personal-access-tokens/new" target="_blank" rel="noopener">github.com/settings/personal-access-tokens/new</a>. Choose “Only select repositories” → upgrade-cards-data, Repository permissions → Contents: Read-only. Paste it here.</p><input type="password" id="ltok" placeholder="github_pat_…" autocomplete="off" style="width:100%;font:16px monospace;padding:10px;border-radius:10px;border:1px solid var(--line);background:var(--bg);color:var(--fg)"><div class="row" style="margin-top:8px"><button class="pri" id="lon1">Turn on</button></div>
        <label style="margin-top:16px"><b>Other devices</b></label><p class="note">Paste the library code from the first device (Settings → Library → Show library code).</p><textarea id="lcode2" rows="3" placeholder="Library code" style="font:14px monospace"></textarea><div class="row" style="margin-top:8px"><button class="pri" id="lon2">Join</button></div><p class="note" id="lmsg"></p>`;
      const turnOn = async (repo, token) => {
        settings.lib = { repo, token }; $('#lmsg').textContent = 'Checking…'; const p = await libCheck();
        if (p === null) { const m = settings.lib.msg; settings.lib = null; await kvSet('settings', settings); $('#lmsg').textContent = m; return; }
        settings.lib.checked = Date.now(); await kvSet('settings', settings); viewSettings(); if (p.length) libPrompt();
      };
      $('#lon1').onclick = () => { const t = $('#ltok').value.trim(); if (t) turnOn('bobiw/upgrade-cards-data', t); };
      $('#lon2').onclick = () => { let o; try { o = JSON.parse(atob($('#lcode2').value.trim())); } catch (_) {} if (!o?.r || !o?.t) { $('#lmsg').textContent = 'That is not a library code.'; return; } turnOn(o.r, o.t); };
    }
  })();
  (() => {
    const sy = settings.sync, ui = $('#synui'), st = $('#syn');
    if (sy?.token && sy?.gist) {
      st.innerHTML = `Sync is on. ${esc(sy.msg || '')}${sy.last ? '<br>Last sync: ' + new Date(sy.last).toLocaleString() : ''}<br>It runs when you open the app, when you leave it and when a session ends.`;
      ui.innerHTML = `<div class="row"><button class="pri" id="sgo">Sync now</button><button id="scode">Show sync code</button><button id="soff">Turn off here</button></div><textarea id="sbox" rows="3" readonly style="display:none;margin-top:8px"></textarea>`;
      $('#sgo').onclick = async () => { await syncNow(false); viewSettings(); };
      $('#scode').onclick = () => { const b = $('#sbox'); b.style.display = 'block'; b.value = btoa(JSON.stringify({ t: sy.token, g: sy.gist })); b.select(); };
      $('#soff').onclick = async () => { settings.sync = null; await kvSet('settings', settings); syncBar(); viewSettings(); };
    } else {
      st.innerHTML = 'Sync is off. Your progress, discards, spelling and duplicate choices would travel through a private GitHub gist (no manual text). Only one device studies at a time, so no conflicts to worry about.';
      ui.innerHTML = `<label><b>First device</b></label><p class="note">Make a token that can only touch gists: <a href="https://github.com/settings/tokens/new?scopes=gist&description=Upgrade%20Cards%20sync" target="_blank" rel="noopener">github.com/settings/tokens/new</a> (tick only “gist”), paste it here.</p><input type="password" id="stok" placeholder="ghp_…" autocomplete="off" style="width:100%;font:16px monospace;padding:10px;border-radius:10px;border:1px solid var(--line);background:var(--bg);color:var(--fg)"><div class="row" style="margin-top:8px"><button class="pri" id="smk">Turn on sync</button></div>
        <label style="margin-top:16px"><b>Other devices</b></label><p class="note">Paste the sync code from the first device (Settings → Show sync code).</p><textarea id="scd" rows="3" placeholder="Sync code" style="font:14px monospace"></textarea><div class="row" style="margin-top:8px"><button class="pri" id="sjn">Join</button></div><p class="note" id="smsg"></p>`;
      $('#smk').onclick = async () => { const t = $('#stok').value.trim(); if (!t) return; $('#smsg').textContent = 'Setting up…'; try { const code = await syncCreate(t); syncBar('✓ synced'); viewSettings(); $('#syn').innerHTML += `<br><b>Copy this sync code to your other devices:</b>`; const b = $('#sbox'); b.style.display = 'block'; b.value = code; b.select(); } catch (e) { $('#smsg').textContent = e.message; } };
      $('#sjn').onclick = async () => { const c = $('#scd').value.trim(); if (!c) return; $('#smsg').textContent = 'Joining…'; try { await syncJoin(c); show('settings'); } catch (e) { $('#smsg').textContent = e.message; } };
    }
  })();
  (() => {
    const all = allPairs(), chosen = all.filter(p => (derive(), _dupc[p.cl.id + '|' + p.me.id])).length;
    $('#dupn').textContent = `${all.length} of Claude's cards are similar to one of yours; you have chosen on ${chosen}. Cards you haven't chosen on follow the "hide duplicates" setting above.`;
    $('#dupgo').onclick = viewDups;
  })();
  (() => {
    derive(); const dt = {}; for (const e of events) if (e.k === 'drop' && e.v) dt[e.c] = e.t;
    const dropped = deck.cards.filter(c => _dset.has(c.id)).sort((a, b) => (dt[b.id] || 0) - (dt[a.id] || 0)), fixes = [];
    for (const c of deck.cards) { const m = spellOf(c.id); for (const s of c.spell || []) if (m[s.bad] === 'ok') fixes.push(`${s.bad} → ${s.good}   (${c.q.slice(0, 50)})`); }
    $('#edits').innerHTML = `<b>${fixes.length}</b> spelling fixes approved${fixes.length ? ` <button class="small" id="cpf">Copy list for my sheets</button><textarea id="fxl" rows="4" readonly style="margin-top:8px">${esc(fixes.join('\\n'))}</textarea>` : ''}<br><b>${dropped.length}</b> cards discarded${dropped.length ? `<div style="margin-top:8px">${dropped.slice(0, 100).map(c => `<div class="fix"><small class="muted">${dt[c.id] ? new Date(dt[c.id]).toLocaleString([], { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit' }) : ''}</small> ${esc(c.q.replace(/\\{\\{c\\d+::(.*?)\\}\\}/g, '$1').slice(0, 80))} <button class="mini" data-restore="${esc(c.id)}">restore</button></div>`).join('')}</div>` : ''}`;
    if ($('#cpf')) $('#cpf').onclick = () => { $('#fxl').select(); navigator.clipboard?.writeText(fixes.join('\\n')).catch(() => {}); };
    document.querySelectorAll('[data-restore]').forEach(b => b.onclick = () => { events.push({ id: uid(), k: 'drop', c: b.dataset.restore, t: Date.now(), v: 0 }); save(); viewSettings(); });
  })();
  manualStatus().then(h => { const el = $('#mst'); if (el) el.innerHTML = h; });
  $('#mf').onchange = async e => { const el = $('#mst'); for (const f of e.target.files) { const k = manualKey(f.name); if (!k) { el.textContent = 'Not recognised: ' + f.name; continue; } el.textContent = 'Saving ' + k + '…'; await kvSet('pdf:' + k, await f.arrayBuffer()); delete docs[k]; } el.innerHTML = await manualStatus(); };
  $('#pf').onchange = async e => {
    try {
      const d = JSON.parse(await e.target.files[0].text()), have = new Set(events.map(x => x.id));
      const add = (d.events || []).filter(x => x.id && !have.has(x.id));
      events.push(...add); await save(); viewSettings(); $('#msg').textContent = `Merged ${add.length} new events.`;
    } catch (err) { $('#msg').textContent = 'Not a progress file: ' + err.message; }
  };
  navigator.storage?.persisted?.().then(p => { const el = $('#per'); if (el) el.textContent = p ? 'Storage: persistent.' : 'Storage: not marked persistent. Export now and then.'; });
}
function allPairs() { const out = []; for (const c of deck.cards) if (deckOf(c) === 'claude') for (const d of c.dup || []) { const me = byId(d.id); if (me) out.push({ cl: c, me, sim: d.sim }); } return out.sort((x, y) => y.sim - x.sim); }
function viewDups() {
  derive(); const all = allPairs(), todo = all.filter(p => !_dupc[p.cl.id + '|' + p.me.id]), done = all.filter(p => _dupc[p.cl.id + '|' + p.me.id]);
  $('#main').innerHTML = `<div class="card"><button class="small" id="dback">‹ Settings</button> <b>Similar cards</b><p class="note">${todo.length} to choose, ${done.length} chosen. Most alike first. A card you do not keep is hidden, not deleted.</p></div>${todo.concat(done).slice(0, 120).map(pairHtml).join('')}`;
  $('#dback').onclick = () => show('settings');
}
async function exportProgress() {
  const name = `progress-${settings.device}-${new Date().toISOString().slice(0, 10)}.json`;
  const blob = new Blob([JSON.stringify({ v: 1, device: settings.device, exported: Date.now(), events }, null, 0)], { type: 'application/json' });
  const f = new File([blob], name, { type: 'application/json' });
  if (navigator.canShare?.({ files: [f] })) { try { await navigator.share({ files: [f] }); return; } catch (e) { if (e.name === 'AbortError') return; } }
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name; a.click();
}


// ---------- reference viewer (pdf.js, manuals kept in IndexedDB on this device) ----------
const MANUALS = ['POH', 'QRH', 'FOM', 'PRM', 'OPSSPECS', 'MEL', 'CDL', 'QUAL1', 'QUAL2', 'QUAL3', 'QUAL4', 'QUAL5', 'QUAL6'];
const docs = {};
const manualKey = n => MANUALS.includes(n.replace(/\.pdf$/i, '').toUpperCase()) ? n.replace(/\.pdf$/i, '').toUpperCase() : /QUAL Lesson (\d)/i.test(n) ? 'QUAL' + n.match(/QUAL Lesson (\d)/i)[1] : /CDL/i.test(n) ? 'CDL' : /MEL/i.test(n) ? 'MEL' : /ops.?specs/i.test(n) ? 'OPSSPECS' : /PRM/i.test(n) ? 'PRM' : /QRH/i.test(n) ? 'QRH' : /FOM/i.test(n) ? 'FOM' : /POH/i.test(n) ? 'POH' : null;
async function manualStatus() {
  const out = [];
  for (const k of MANUALS) { const b = await kvGet('pdf:' + k); out.push(`${b ? '✓' : '–'} ${k}${b ? ' (' + (b.byteLength / 1048576).toFixed(1) + ' MB)' : ''}`); }
  return out.join(' &nbsp; ');
}
async function getDoc(src) {
  if (docs[src]) return docs[src];
  const buf = await kvGet('pdf:' + src); if (!buf) return null;
  pdfjsLib.GlobalWorkerOptions.workerSrc = 'lib/pdf.worker.min.js';
  return docs[src] = await pdfjsLib.getDocument({ data: buf.slice(0) }).promise;
}
let ref = null; // {src, page, zoom}
function ensurePdfLib() {
  return window.pdfjsLib ? Promise.resolve() : new Promise((res, rej) => { const s = document.createElement('script'); s.src = 'lib/pdf.min.js'; s.onload = res; s.onerror = rej; document.head.appendChild(s); });
}
const refIsDark = () => settings.refDark === 'on' || (settings.refDark === 'auto' && matchMedia('(prefers-color-scheme: dark)').matches);
function openRef(src, page) {
  const list = curRefs.slice(); if (!list.some(r => r.src === src && r.page === +page)) list.push({ src, page: +page, cite: src + ' p.' + page, primary: !list.length });
  ref = { src, page: +page, zoom: 1, list }; document.body.classList.add('refopen'); renderRef();
}
function closeRef() { ref = null; document.body.classList.remove('refopen'); const r = $('#ref'); if (r) r.innerHTML = ''; }
async function renderRef() {
  if (!ref) return;
  const el = $('#ref'), { src, page } = ref;
  const dark = refIsDark(); el.classList.toggle('rdark', dark);
  const chips = ref.list.length > 1 ? `<div class="rchips">${ref.list.map(r => `<button class="chip${r.src === src && r.page === page ? ' on' : ''}" data-open="${esc(r.src)}:${r.page}">${esc(r.src)} p.${r.page}${r.primary ? '' : ' · ' + esc((REL[r.rel] || 'also').toLowerCase())}</button>`).join('')}</div>` : '';
  el.innerHTML = `<div class="rbar"><b>${esc(src)} p.${page}<span id="rn" class="muted"></span></b><span class="rbtns"><button class="small" id="rp">‹</button><button class="small" id="rx">›</button><button class="small" id="rz1">−</button><button class="small" id="rz2">+</button><button class="small" id="rd" title="Dark / light page">${dark ? '☀' : '☾'}</button><button class="small" id="rc">✕</button></span></div>${chips}<div class="rbody" id="rb"><div class="note">Loading…</div></div>`;
  $('#rc').onclick = closeRef; $('#rd').onclick = () => { settings.refDark = dark ? 'off' : 'on'; kvSet('settings', settings); document.querySelectorAll('.fig').forEach(f => f.classList.toggle('dark', !dark)); renderRef(); };
  try {
    await ensurePdfLib(); const doc = await getDoc(src);
    if (!doc) { $('#rb').innerHTML = `<div class="card"><p>The ${esc(src)} PDF is not loaded on this device.</p><label>Load it now</label><input type="file" id="lf" accept=".pdf,application/pdf"></div>`; $('#lf').onchange = async e => { const f = e.target.files[0]; if (f) { await kvSet('pdf:' + src, await f.arrayBuffer()); delete docs[src]; renderRef(); } }; return; }
    const n = doc.numPages; ref.page = Math.min(Math.max(1, ref.page), n);
    $('#rn').textContent = ` / ${n}`;
    $('#rp').onclick = () => { ref.page--; renderRef(); }; $('#rx').onclick = () => { ref.page++; renderRef(); };
    $('#rz1').onclick = () => { ref.zoom = Math.max(.5, ref.zoom - .25); renderRef(); }; $('#rz2').onclick = () => { ref.zoom = Math.min(3, ref.zoom + .25); renderRef(); };
    const pg = await doc.getPage(ref.page), body = $('#rb'), w = body.clientWidth - 16;
    const base = pg.getViewport({ scale: 1 }), scale = w / base.width * ref.zoom, vp = pg.getViewport({ scale }), r = window.devicePixelRatio || 1;
    const cv = document.createElement('canvas'); cv.width = vp.width * r; cv.height = vp.height * r; cv.style.width = vp.width + 'px'; cv.style.height = vp.height + 'px';
    body.innerHTML = ''; body.appendChild(cv);
    await pg.render({ canvasContext: cv.getContext('2d'), viewport: vp, transform: r !== 1 ? [r, 0, 0, r, 0, 0] : null }).promise;
    $('#rb').scrollTop = 0;
  } catch (err) { $('#rb').innerHTML = `<div class="card">Could not show the page: ${esc(err.message)}</div>`; }
}
document.addEventListener('click', e => {
  const b = e.target.closest('[data-open]'); if (!b) return; const [s, p] = b.dataset.open.split(':');
  if (ref && b.closest('#ref')) { ref.src = s; ref.page = +p; ref.zoom = 1; renderRef(); } else openRef(s, p);
});
document.addEventListener('keydown', e => { if (e.key === 'Escape' && ref) closeRef(); if (ref && (e.key === '[' || e.key === ']')) { ref.page += e.key === ']' ? 1 : -1; renderRef(); } });
const curCard = () => S && S.queue[S.i];
const cardOf = id => byId(id) || curCard();
function afterDecision(c, k) {                // a decision was made: let the box shrink, and show the new text if it changed
  openBoxes.delete(bkey(c, k)); refreshBox(c, k);
  const q = document.querySelector('[data-f="q"]'), an = document.querySelector('[data-f="a"]');
  if (q) q.innerHTML = qHtml(textOf(c, 'q')); if (an) an.innerHTML = ans(textOf(c, 'a'));
}
document.addEventListener('click', e => {
  let b;
  if ((b = e.target.closest('[data-spell]'))) {
    const c = byId(b.dataset.c), s = c?.spell?.[+b.dataset.i]; if (!s) return;
    events.push({ id: uid(), k: 'spell', c: c.id, t: Date.now(), bad: s.bad, v: b.dataset.spell === 'undo' ? null : b.dataset.spell }); save(); afterDecision(c, 'spell');
  } else if ((b = e.target.closest('[data-sugg]'))) {
    const c = byId(b.dataset.c); if (!c) return;
    events.push({ id: uid(), k: 'sugg', c: c.id, t: Date.now(), v: b.dataset.sugg }); save(); afterDecision(c, 'sugg'); openBoxes.delete(bkey(c, 'issue')); refreshBox(c, 'issue');
  } else if ((b = e.target.closest('[data-ack]'))) {
    const c = byId(b.dataset.ack); if (!c) return;
    events.push({ id: uid(), k: 'ack', c: c.id, t: Date.now(), v: 1 }); save(); afterDecision(c, 'issue');
  } else if ((b = e.target.closest('[data-dup]'))) {
    events.push({ id: uid(), k: 'dup', c: b.dataset.cl, m: b.dataset.me, t: Date.now(), v: b.dataset.dup }); save();
    const inBox = b.closest('#box-dup'), cur = curCard();
    if (inBox && cur) { openBoxes.delete(bkey(cur, 'dup')); refreshBox(cur, 'dup'); }
    else { const pair = b.closest('.pair'); if (pair) { const cl = byId(b.dataset.cl), me = byId(b.dataset.me); pair.outerHTML = pairHtml({ cl, me, sim: (cl.dup || []).find(d => d.id === me.id)?.sim || 0 }); } }
  } else if ((b = e.target.closest('[data-toggle]'))) {
    const key = b.dataset.toggle, [id, k] = key.split(':'), c = byId(id); if (!c) return;
    if (openBoxes.has(key)) openBoxes.delete(key); else openBoxes.add(key); refreshBox(c, k);
  }
});
let rsz; window.addEventListener('resize', () => { clearTimeout(rsz); rsz = setTimeout(renderRef, 250); });

// ---------- sync between devices: a private GitHub gist holds the event log (progress only, no manual text) ----------
let syncing = false;
const ghBase = () => settings.sync?.base || 'https://api.github.com';
const ghFetch = (path, opt = {}) => fetch(ghBase() + path, { ...opt, headers: { Accept: 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28', Authorization: 'Bearer ' + settings.sync.token, ...(opt.headers || {}) } });
const cfgOf = () => ({ checkDate: settings.checkDate, newPerDay: settings.newPerDay, hideDrafts: settings.hideDrafts, hideDups: settings.hideDups, t: settings.cfgT || 0 });
function syncBar(msg) { const el = $('#syncbar'); if (!el) return; if (msg) el.textContent = msg; el.style.display = (settings.sync?.token || msg) ? 'block' : 'none'; }
async function syncNow(quiet) {
  const sy = settings.sync; if (!sy?.token || !sy?.gist || syncing || !navigator.onLine) return false;
  syncing = true; syncBar('↻ syncing…');
  try {
    const r = await ghFetch('/gists/' + sy.gist); if (!r.ok) throw new Error('GitHub answered ' + r.status);
    const g = await r.json(), f = g.files?.['progress.json']; let remote = { events: [] };
    if (f) remote = JSON.parse(f.truncated ? await (await fetch(f.raw_url)).text() : f.content);
    const have = new Set(events.map(e => e.id)), add = (remote.events || []).filter(e => e.id && !have.has(e.id));
    if (add.length) { events.push(...add); await save(); }
    let cfgPulled = false;
    if (remote.cfg && remote.cfg.t > (settings.cfgT || 0)) { const c = remote.cfg; Object.assign(settings, { checkDate: c.checkDate ?? settings.checkDate, newPerDay: c.newPerDay ?? settings.newPerDay, hideDrafts: !!c.hideDrafts, hideDups: c.hideDups !== false, cfgT: c.t }); cfgPulled = true; }
    const rids = new Set((remote.events || []).map(e => e.id)), push = events.some(e => !rids.has(e.id)) || (settings.cfgT || 0) > (remote.cfg?.t || 0);
    if (push) {
      const p = await ghFetch('/gists/' + sy.gist, { method: 'PATCH', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ files: { 'progress.json': { content: JSON.stringify({ v: 1, events, cfg: cfgOf() }) } } }) });
      if (!p.ok) throw new Error('GitHub answered ' + p.status);
    }
    sy.last = Date.now(); sy.msg = `Synced: got ${add.length} new, ${push ? 'sent yours' : 'nothing to send'}.`; await kvSet('settings', settings);
    syncBar('✓ synced'); syncing = false;
    return add.length > 0 || cfgPulled;
  } catch (e) {
    sy.msg = 'Could not sync: ' + e.message; syncBar('sync failed (studying offline is fine)'); syncing = false; return false;
  }
}
async function syncCreate(token) {
  settings.sync = { token: token.trim() };
  const r = await ghFetch('/gists', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ description: 'Upgrade Cards progress (no manual text)', public: false, files: { 'progress.json': { content: JSON.stringify({ v: 1, events, cfg: cfgOf() }) } } }) });
  if (!r.ok) { settings.sync = null; throw new Error('GitHub answered ' + r.status + (r.status === 401 ? ' (token not accepted)' : r.status === 404 || r.status === 403 ? ' (token needs the gist scope)' : '')); }
  const g = await r.json(); settings.sync.gist = g.id; settings.sync.last = Date.now(); settings.sync.msg = 'Sync is on.'; await kvSet('settings', settings);
  return btoa(JSON.stringify({ t: settings.sync.token, g: g.id }));
}
async function syncJoin(code) {
  let o; try { o = JSON.parse(atob(code.trim())); } catch (_) { throw new Error('That is not a sync code'); }
  if (!o.t || !o.g) throw new Error('That is not a sync code');
  settings.sync = { token: o.t, gist: o.g }; await kvSet('settings', settings);
  const changed = await syncNow(true); if (!settings.sync.last) { const m = settings.sync.msg; settings.sync = null; await kvSet('settings', settings); throw new Error(m || 'Could not reach the sync'); }
  return changed;
}
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') syncNow(true); });

// ---------- library: the deck and the manuals, downloaded from a PRIVATE GitHub repo with a read-only token ----------
const libBase = () => settings.lib?.base || 'https://api.github.com';
const libGet = path => fetch(`${libBase()}/repos/${settings.lib.repo}/contents/${path}?ref=main`, { headers: { Authorization: 'Bearer ' + settings.lib.token, Accept: 'application/vnd.github.raw+json', 'X-GitHub-Api-Version': '2022-11-28' } });
async function libBytes(path, onProgress) {
  const r = await libGet(path); if (!r.ok) throw new Error(`${path}: GitHub answered ${r.status}${r.status === 404 ? ' (not found, or the token cannot read this repo)' : r.status === 401 ? ' (token not accepted)' : ''}`);
  const total = +r.headers.get('content-length') || 0; if (!r.body?.getReader) return await r.arrayBuffer();
  const rd = r.body.getReader(), chunks = []; let got = 0;
  for (;;) { const { done, value } = await rd.read(); if (done) break; chunks.push(value); got += value.length; onProgress?.(got, total); }
  const out = new Uint8Array(got); let o = 0; for (const c of chunks) { out.set(c, o); o += c.length; } return out.buffer;
}
const sha256 = async buf => [...new Uint8Array(await crypto.subtle.digest('SHA-256', buf))].map(b => b.toString(16).padStart(2, '0')).join('');
const libKey = p => p === 'deck.json' ? 'deck' : 'pdf:' + p.replace(/^.*\//, '').replace(/\.pdf$/i, '').toUpperCase();
let libPending = [];
async function libCheck() {
  if (!settings.lib?.repo || !navigator.onLine) return null;
  try {
    const m = JSON.parse(new TextDecoder().decode(await libBytes('manifest.json'))), have = settings.libHave || {};
    libPending = Object.entries(m.files).filter(([p, f]) => have[p] !== f.sha).map(([p, f]) => ({ path: p, sha: f.sha, size: f.size }));
    settings.lib.msg = libPending.length ? `${libPending.length} update${libPending.length > 1 ? 's' : ''} available (${(libPending.reduce((s, f) => s + f.size, 0) / 1048576).toFixed(1)} MB)` : 'Library is up to date.'; settings.lib.built = m.built; await kvSet('settings', settings);
    return libPending;
  } catch (e) { settings.lib.msg = 'Could not check: ' + e.message; return null; }
}
async function libDownload(paths, onProgress) {
  settings.libHave ||= {};
  for (const f of libPending.filter(f => !paths || paths.includes(f.path))) {
    const buf = await libBytes(f.path, (g, t) => onProgress?.(f, g, t || f.size));
    if (await sha256(buf) !== f.sha) throw new Error(f.path + ': download did not match its checksum; try again');
    if (f.path === 'deck.json') { const d = JSON.parse(new TextDecoder().decode(buf)); if (!Array.isArray(d.cards)) throw new Error('deck.json has no cards'); deck = d; await kvSet('deck', d); }
    else { const k = libKey(f.path); await kvSet(k, buf); delete docs[k.slice(4)]; }
    settings.libHave[f.path] = f.sha; await kvSet('settings', settings);
  }
  libPending = libPending.filter(f => paths && !paths.includes(f.path));
  settings.lib.msg = libPending.length ? `${libPending.length} update(s) still to download` : 'Library is up to date.'; await kvSet('settings', settings);
}
// once a day (when the app opens) check for updates and ASK; nothing downloads unless B taps Download
async function libDaily(force) {
  if (!settings.lib?.repo || !navigator.onLine) return;
  const last = settings.lib.checked || 0; if (!force && Date.now() - last < 864e5) return;
  const p = await libCheck(); settings.lib.checked = Date.now(); await kvSet('settings', settings);
  if (p?.length) libPrompt();
}
function libPrompt() {
  let el = $('#libprompt'); if (!el) { el = document.createElement('div'); el.id = 'libprompt'; document.querySelector('header').appendChild(el); }
  const mb = (libPending.reduce((s, f) => s + f.size, 0) / 1048576).toFixed(1), names = libPending.map(f => f.path.replace(/^pdf\//, '').replace(/\.pdf$/, '')).join(', ');
  el.innerHTML = `<span>Library update: ${esc(names)} (${mb} MB)</span> <button class="small pri" id="lpy">Download</button><button class="small" id="lpn">Later</button>`; el.style.display = 'flex';
  $('#lpn').onclick = () => { el.style.display = 'none'; };
  $('#lpy').onclick = async () => {
    el.innerHTML = '<span id="lpt">Downloading…</span>';
    try { await libDownload(null, (f, g, t) => { $('#lpt').textContent = `${f.path}: ${(g / 1048576).toFixed(1)} of ${(t / 1048576).toFixed(1)} MB`; }); el.style.display = 'none'; deckBar(); if (!S) show(tab); } catch (e) { el.innerHTML = `<span>${esc(e.message)}</span> <button class="small" id="lpn2">Close</button>`; $('#lpn2').onclick = () => { el.style.display = 'none'; }; }
  };
}

// ---------- pomodoro timer: a chip in the header (tap to start; tap again for pause / skip / reset) ----------
const PC = () => Object.assign({ focus: 25, short: 5, long: 15, every: 4 }, settings.pomoCfg || {});
const PS = () => (settings.pomo ||= { phase: 'idle', endAt: 0, remain: 0, paused: false, n: 0, day: '', today: 0 });
let audioCtx;
function beep(times) {
  try { audioCtx ||= new (window.AudioContext || window.webkitAudioContext)(); audioCtx.resume?.(); const t0 = audioCtx.currentTime;
    for (let i = 0; i < times; i++) { const o = audioCtx.createOscillator(), g = audioCtx.createGain(), s = t0 + i * .35; o.frequency.value = 880; o.connect(g); g.connect(audioCtx.destination); g.gain.setValueAtTime(.0001, s); g.gain.exponentialRampToValueAtTime(.3, s + .02); g.gain.exponentialRampToValueAtTime(.0001, s + .25); o.start(s); o.stop(s + .3); } } catch (_) {}
}
const pLeft = () => { const p = PS(); return p.paused ? p.remain : Math.max(0, p.endAt - Date.now()); };
const pFmt = ms => { const s = Math.ceil(ms / 1000); return String(Math.floor(s / 60)).padStart(2, '0') + ':' + String(s % 60).padStart(2, '0'); };
const pSave = () => kvSet('settings', settings);
function pStart(phase, from) { const p = PS(), m = phase === 'focus' ? PC().focus : phase === 'long' ? PC().long : PC().short; Object.assign(p, { phase, endAt: (from || Date.now()) + m * 60e3, paused: false, remain: 0 }); }
function pNext(counted) {                                   // the current phase ended (or was skipped): focus -> break, break -> idle
  const p = PS(), at = counted ? p.endAt : Date.now();
  if (p.phase === 'focus') { if (counted) { const day = new Date().toDateString(); if (p.day !== day) { p.day = day; p.today = 0; } p.n++; p.today++; } pStart(counted && p.n % PC().every === 0 ? 'long' : 'short', at); }
  else Object.assign(p, { phase: 'idle', endAt: 0, paused: false, remain: 0 });
}
function pPaint() {
  const b = $('#pomo'); if (!b) return; const p = PS();
  b.textContent = p.phase === 'idle' ? '🍅' : (p.paused ? '⏸ ' : p.phase === 'focus' ? '🍅 ' : '☕ ') + pFmt(pLeft()); b.classList.toggle('run', p.phase !== 'idle'); b.classList.toggle('brk', p.phase === 'short' || p.phase === 'long');
}
function pTick() {
  const p = PS(); let ended = null;
  while (p.phase !== 'idle' && !p.paused && Date.now() >= p.endAt) { ended = p.phase; pNext(true); }
  if (ended) { pSave(); beep(ended === 'focus' ? 3 : 2); toast(p.phase === 'idle' ? '☕ Break over. Tap 🍅 when you want the next focus round.' : `🍅 Focus round done. ${p.phase === 'long' ? 'Long' : 'Short'} break: ${pFmt(pLeft())}`); }
  pPaint();
}
function pMenu() {
  const m = $('#pomomenu'); if (m.style.display === 'flex') { m.style.display = 'none'; return; }
  const p = PS(), t = p.day === new Date().toDateString() ? p.today : 0;
  m.innerHTML = `<button class="small" id="pm1">${p.paused ? 'Resume' : 'Pause'}</button><button class="small" id="pm2">${p.phase === 'focus' ? 'Skip to break' : 'End break'}</button><button class="small" id="pm3">Reset</button><span class="muted">${t} 🍅 today</span>`; m.style.display = 'flex'; fitHeader();
  const close = () => { m.style.display = 'none'; fitHeader(); pPaint(); };
  $('#pm1').onclick = () => { if (p.paused) { p.endAt = Date.now() + p.remain; p.paused = false; } else { p.remain = Math.max(0, p.endAt - Date.now()); p.paused = true; } pSave(); close(); };
  $('#pm2').onclick = () => { pNext(false); pSave(); close(); };
  $('#pm3').onclick = () => { Object.assign(p, { phase: 'idle', endAt: 0, paused: false, remain: 0 }); pSave(); close(); };
}
function pomoInit() {
  $('#pomo').onclick = () => { beep(0); const p = PS(); if (p.phase === 'idle') { pStart('focus'); pSave(); pPaint(); } else pMenu(); };
  setInterval(pTick, 1000); document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible') pTick(); }); pTick();
}

// ---------- boot ----------
document.querySelectorAll('#tabs button').forEach(b => b.onclick = () => show(b.dataset.tab));
(async () => {
  idb = await dbOpen();
  deck = (await kvGet('deck')) || deck;
  events = (await kvGet('events')) || [];
  settings = Object.assign(settings, (await kvGet('settings')) || {});
  sessions = Object.assign({ study: null, quiz: {} }, (await kvGet('sessions')) || {});
  if (!settings.device) { settings.device = 'd' + uid().slice(0, 5); await kvSet('settings', settings); }
  navigator.storage?.persist?.();
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(() => {});
  show('study'); syncBar(); pomoInit(); new ResizeObserver(fitHeader).observe(document.querySelector('header'));
  syncNow(true).then(changed => { if (changed && !S) show(tab); });
  libDaily(false);
})();
