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

let deck = { meta: {}, cards: [] }, events = [], settings = { newPerDay: 15, checkDate: '', hideDrafts: false, device: '', deck: 'mine' };
let S = null; // study session
const save = () => kvSet('events', events);

// ---------- scheduler (events -> per-card state; replay is order-independent) ----------
const byTime = (a, b) => a.t - b.t || (a.id < b.id ? -1 : 1);
function maxIvl() {
  if (!settings.checkDate) return Infinity;
  const days = Math.ceil((new Date(settings.checkDate + 'T00:00:00') - Date.now()) / DAY);
  return days > 1 ? Math.max(1, Math.floor(days / 2)) : 1;
}
function step(s, e, cap) {
  s = s || { ease: 2.5, ivl: 0, reps: 0, lapses: 0, n: 0, ok: 0, first: e.t };
  s.n++; if (e.g >= 2) s.ok++;
  if (e.g === 1) { s.lapses++; s.reps = 0; s.ivl = 0; s.ease = Math.max(1.3, s.ease - .2); s.due = e.t + 10 * 60e3; }
  else {
    s.reps++;
    let i = s.reps === 1 ? { 2: 1, 3: 1, 4: 3 }[e.g] : s.reps === 2 ? { 2: 2, 3: 3, 4: 6 }[e.g]
      : s.ivl * { 2: 1.2, 3: s.ease, 4: s.ease * 1.3 }[e.g];
    s.ease = Math.min(3, Math.max(1.3, s.ease + { 2: -.15, 3: 0, 4: .15 }[e.g]));
    s.ivl = Math.min(cap, Math.max(1, Math.round(i)));
    s.due = e.t + s.ivl * DAY;
  }
  s.last = e.t; return s;
}
function replay() {
  const st = {}, cap = maxIvl();
  for (const e of events.slice().sort(byTime)) if (!e.k) st[e.c] = step(st[e.c], e, cap);
  return st;
}
const endOfToday = () => { const d = new Date(); d.setHours(23, 59, 59, 999); return d.getTime(); };
const sameDay = (a, b) => new Date(a).toDateString() === new Date(b).toDateString();
const deckOf = c => c.deck || (c.id.startsWith('raw-') ? 'mine' : 'claude');
const DECKS = [['mine', 'My cards'], ['claude', "Claude's cards"], ['all', 'All']];
const pool = () => deck.cards.filter(c => c.check !== 'fail' && !(settings.hideDrafts && c.review === 'draft') && (settings.deck === 'all' || deckOf(c) === settings.deck));

function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.random() * (i + 1) | 0; [a[i], a[j]] = [a[j], a[i]]; } return a; }

function buildQueue(extra) {
  const st = replay(), P = pool(), now = Date.now();
  const due = P.filter(c => st[c.id] && st[c.id].due <= endOfToday())
    .sort((a, b) => (st[a.id].due - (a.weak ? DAY : 0)) - (st[b.id].due - (b.weak ? DAY : 0)));
  const unseen = P.filter(c => !st[c.id]);
  const inPool = new Set(P.map(c => c.id)), newToday = Object.entries(st).filter(([id, s]) => inPool.has(id) && sameDay(s.first, now)).length;
  const allow = extra ? unseen.length : Math.max(0, settings.newPerDay - newToday);
  const fresh = shuffle(unseen.filter(c => c.weak)).concat(shuffle(unseen.filter(c => !c.weak))).slice(0, allow);
  return { st, queue: due.concat(fresh), dueN: due.length, newN: fresh.length, unseenN: unseen.length };
}
function weakQueue() {
  const st = replay();
  return pool().filter(c => st[c.id] && (st[c.id].lapses > 0 || st[c.id].ok / st[c.id].n < .8));
}

// ---------- rendering helpers ----------
const tabs = { study: viewStudy, stats: viewStats, settings: viewSettings };
let tab = 'study';
function deckBar() {
  const n = k => deck.cards.filter(c => c.check !== 'fail' && (k === 'all' || deckOf(c) === k)).length;
  $('#deckbar').innerHTML = DECKS.map(([k, l]) => `<button data-deck="${k}" class="${settings.deck === k ? 'on' : ''}">${l}<small> ${n(k)}</small></button>`).join('');
  $('#deckbar').querySelectorAll('button').forEach(b => b.onclick = () => { settings.deck = b.dataset.deck; kvSet('settings', settings); S = null; closeRef(); show(tab); });
}
function show(t) {
  tab = t; deckBar(); $('#deckbar').style.display = t === 'settings' ? 'none' : 'flex'; document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.tab === t));
  tabs[t]();
}
const cloze = (txt, reveal) => esc(txt).replace(/\{\{c\d+::(.*?)\}\}/g, (_, a) => `<span class="blank">${reveal ? a : '[&nbsp;&nbsp;&nbsp;…&nbsp;&nbsp;&nbsp;]'}</span>`);

function head(c) {
  return `<div class="meta"><span class="tag">${esc(c.topic)}</span>${c.review === 'draft' ? '<span class="tag draft">DRAFT</span>' : c.review === 'generated' ? '<span class="tag">AI-written · quote-checked</span>' : ''}${c.weak ? '<span class="tag">weak area</span>' : ''}</div>`;
}
function srcBlock(c) {
  return `<div class="src">[${esc(c.cite)}] · ${esc(c.src)} ${esc(deck.meta.revs?.[c.src] || '')} <button class="small" data-open="${esc(c.src)}:${c.page}">Open page ${c.page}</button>${c.quotes?.length ? `<q>${esc(c.quotes.join(' … '))}</q>` : ''}${c.note ? `<div style="margin-top:6px">${esc(c.note)}</div>` : ''}</div>`;
}
const gradeBtns = sug => [[1, 'Again'], [2, 'Hard'], [3, 'Good'], [4, 'Easy']]
  .map(([g, l]) => `<button class="g${g}${sug === g ? ' sug' : ''}" data-g="${g}">${l}</button>`).join('');

// ---------- study ----------
function viewStudy() {
  if (!deck.cards.length) return $('#main').innerHTML = `<div class="card"><div class="q">No deck loaded</div><p class="muted">Settings → Load deck file, and pick <b>deck.json</b>.</p></div>`;
  if (!S) {
    const b = buildQueue(false), weak = weakQueue().length;
    $('#main').innerHTML = `<div class="grid"><div class="card"><div class="big">${b.dueN}</div><small>due</small></div><div class="card"><div class="big">${b.newN}</div><small>new today</small></div><div class="card"><div class="big">${weak}</div><small>weak</small></div></div>
      ${b.queue.length ? `<button class="pri" style="width:100%" id="go">Start ${b.queue.length} cards</button>` : `<div class="card"><div class="q">Nothing due.</div><p class="muted">${b.unseenN} unseen cards are held back by the daily limit.</p></div>`}
      <div class="row" style="margin-top:10px">${b.unseenN ? `<button id="more">Study unseen (${b.unseenN})</button>` : ''}${weak ? `<button id="wk">Drill weak (${weak})</button>` : ''}</div>`;
    const go = q => { S = { queue: q.slice(), i: 0, shown: false, t0: Date.now(), total: q.length, done: 0 }; viewStudy(); };
    if ($('#go')) $('#go').onclick = () => go(b.queue);
    if ($('#more')) $('#more').onclick = () => go(buildQueue(true).queue);
    if ($('#wk')) $('#wk').onclick = () => go(shuffle(weakQueue()));
    return;
  }
  if (S.i >= S.queue.length) {
    $('#main').innerHTML = `<div class="card"><div class="q">Session done</div><p class="muted">${S.done} answers.</p><button class="pri" id="fin">Back</button></div>`;
    $('#fin').onclick = () => { S = null; viewStudy(); }; return;
  }
  S.cur = null; const c = S.queue[S.i]; S.t0 = Date.now(); S.shown = false; S.errors = 0; S.pos = 0;
  const prog = `<div class="prog"><i style="width:${S.i / S.queue.length * 100}%"></i></div>`;
  const body = { flip: rFlip, cloze: rCloze, mc: rMc, typed: rTyped, steps: rSteps }[c.type] || rFlip;
  $('#main').innerHTML = prog + `<div class="card" id="cc">${head(c)}</div><div id="ctl"></div>`;
  body(c);
}
function done(c, g) {
  events.push({ id: uid(), c: c.id, t: Date.now(), g, ms: Date.now() - S.t0, d: settings.device });
  save(); S.done++;
  if (g === 1) { const at = Math.min(S.queue.length, S.i + 5); S.queue.splice(at, 0, c); }
  S.i++; viewStudy();
}
function reveal(c, html) {
  $('#cc').insertAdjacentHTML('beforeend', html + srcBlock(c));
}
function flagBtn(c) {
  return `<button class="small" id="flag" style="margin-top:10px">⚑ Flag this card</button>`;
}
function wireFlag(c) {
  const f = $('#flag'); if (!f) return;
  f.onclick = () => { const note = prompt('What is wrong with this card?'); if (note) { events.push({ id: uid(), k: 'flag', c: c.id, t: Date.now(), note }); save(); f.textContent = 'Flagged'; f.disabled = true; } };
}
function gradePanel(c, sug) {
  $('#ctl').innerHTML = `<div class="row">${gradeBtns(sug)}</div>${flagBtn(c)}`;
  $('#ctl').querySelectorAll('[data-g]').forEach(b => b.onclick = () => done(c, +b.dataset.g));
  wireFlag(c);
}
function rFlip(c) { rSwipe(c, `<div class="q">${esc(c.q)}</div>`, `<div class="q">${esc(c.a)}</div>`); }
function rCloze(c) { rSwipe(c, `<div class="q">${cloze(c.q, false)}</div>`, `<div class="q">${cloze(c.q, true)}</div>`); }
// flip card: tap to flip, swipe right = correct, swipe left = incorrect (buttons and arrow keys too)
function rSwipe(c, front, back) {
  const cc = $('#cc'); cc.className = 'plain';
  cc.innerHTML = `<div class="drag" id="dr"><div class="sc" id="sc">
    <div class="face front">${head(c)}${front}<div class="hint">Tap to flip</div></div>
    <div class="face back">${head(c)}${back}${srcBlock(c)}</div></div><div class="tint" id="tint"></div></div>`;
  $('#ctl').innerHTML = `<div class="row"><button class="g1" id="bx">✗ Missed</button><button class="g3" id="bo">✓ Got it</button></div><p class="note" style="text-align:center;margin:8px 0">Swipe right ✓ · swipe left ✗<span class="kbd">Keyboard: Space flips · → correct · ← missed</span></p>${flagBtn(c)}`;
  wireFlag(c);
  const dr = $('#dr'), sc = $('#sc'), tint = $('#tint');
  let x0 = null, y0 = 0, dx = 0, moved = false, busy = false;
  const grade = g => { if (busy) return; busy = true; dr.style.transition = 'transform .22s, opacity .22s'; dr.style.transform = `translateX(${g === 3 ? 140 : -140}%) rotate(${g === 3 ? 18 : -18}deg)`; dr.style.opacity = 0; setTimeout(() => done(c, g), 200); };
  S.cur = { flip: () => sc.classList.toggle('flipped'), grade };
  $('#bx').onclick = () => grade(1); $('#bo').onclick = () => grade(3);
  dr.onpointerdown = e => { if (e.target.closest('button')) return; x0 = e.clientX; y0 = e.clientY; dx = 0; moved = false; dr.style.transition = 'none'; try { dr.setPointerCapture(e.pointerId); } catch (_) {} };
  dr.onpointermove = e => {
    if (x0 === null) return; dx = e.clientX - x0;
    if (!moved && Math.abs(dx) > 10 && Math.abs(dx) > Math.abs(e.clientY - y0)) moved = true;
    if (!moved) return;
    dr.style.transform = `translateX(${dx}px) rotate(${dx / 25}deg)`;
    tint.style.background = dx > 0 ? `rgba(76,195,138,${Math.min(.45, dx / 300)})` : `rgba(255,123,114,${Math.min(.45, -dx / 300)})`;
  };
  const end = () => {
    if (x0 === null) return; x0 = null; tint.style.background = '';
    if (!moved) { S.cur.flip(); return; }
    if (Math.abs(dx) > 90) grade(dx > 0 ? 3 : 1);
    else { dr.style.transition = 'transform .2s'; dr.style.transform = ''; }
  };
  dr.onpointerup = end; dr.onpointercancel = () => { x0 = null; tint.style.background = ''; dr.style.transition = 'transform .2s'; dr.style.transform = ''; };
}
document.addEventListener('keydown', e => {
  if (!S?.cur || e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
  if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); S.cur.flip(); }
  else if (e.key === 'ArrowRight') S.cur.grade(3); else if (e.key === 'ArrowLeft') S.cur.grade(1);
});
function rMc(c) {
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${esc(c.q)}</div><div style="margin-top:12px">${c.choices.map((x, i) => `<button class="choice" data-i="${i}">${esc(x)}</button>`).join('')}</div>`);
  $('#cc').querySelectorAll('.choice').forEach(b => b.onclick = () => {
    const i = +b.dataset.i, ok = i === c.correct;
    $('#cc').querySelectorAll('.choice').forEach((x, j) => { x.disabled = true; if (j === c.correct) x.classList.add('right'); });
    if (!ok) b.classList.add('wrong');
    reveal(c, c.a ? `<div class="a">${esc(c.a)}</div>` : '');
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
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${esc(c.q)}</div><textarea id="ta" rows="6" autocapitalize="off" autocomplete="off" autocorrect="off" spellcheck="false" placeholder="Type it from memory"></textarea>`);
  $('#ctl').innerHTML = `<button class="pri" style="width:100%" id="sh">Check</button>`;
  $('#sh').onclick = () => {
    const exp = normTxt(c.a), got = normTxt($('#ta').value), d = lcsDiff(exp, got);
    const miss = d.filter(x => x[0] !== 'ok').length, sug = miss === 0 ? 3 : miss <= Math.max(1, exp.length * .15) ? 2 : 1;
    $('#ta').disabled = true;
    reveal(c, `<div class="a diff">${d.map(([k, w]) => `<span class="${k}">${esc(w)}</span>`).join(' ')}</div><div class="a">${esc(c.a)}</div>`);
    gradePanel(c, sug);
  };
}
function rSteps(c) {
  const order = shuffle(c.steps.map((s, i) => i));
  $('#cc').insertAdjacentHTML('beforeend', `<div class="q">${esc(c.q)}</div><p class="muted">Tap the steps in order.</p><div id="sl">${order.map(i => `<button class="step" data-i="${i}">${esc(c.steps[i])}</button>`).join('')}</div>`);
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
  const st = replay(), P = pool(), now = Date.now(), rev = events.filter(e => !e.k);
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
    ${flags ? `<h2>Flagged</h2><div class="card"><table>${flags}</table></div>` : ''}`;
}

// ---------- settings / import / export ----------
function viewSettings() {
  const dr = deck.cards.filter(c => c.review === 'draft').length;
  $('#main').innerHTML = `<div class="card"><b>Deck</b><p class="note">${deck.cards.length} cards (${dr} draft) · built ${esc(deck.meta.built || 'never')}<br>${esc(Object.entries(deck.meta.revs || {}).map(([k, v]) => k + ' ' + v).join(' · '))}</p>
    <label for="df">Load deck file (deck.json)</label><input type="file" id="df" accept=".json,application/json"></div>
    <div class="card"><b>Manuals (for the side-by-side page viewer)</b>
    <p class="note" id="mst">Checking…</p>
    <label for="mf">Load manual PDFs (POH, QRH, FOM, PRM, OpsSpecs, MEL, CDL, QUAL lessons)</label><input type="file" id="mf" accept=".pdf,application/pdf" multiple>
    <p class="note">Stored only on this device. Nothing is uploaded.</p></div>
    <div class="card"><b>Study</b>
    <label for="cd">Check date</label><input type="date" id="cd" value="${esc(settings.checkDate)}">
    <p class="note">Review gaps are capped at half the days left, so nothing is scheduled past the check.</p>
    <label for="np">New cards per day</label><input type="number" id="np" min="0" max="200" value="${settings.newPerDay}">
    <label><input type="checkbox" id="hd" ${settings.hideDrafts ? 'checked' : ''}> Hide DRAFT cards</label></div>
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
  $('#cd').onchange = e => { settings.checkDate = e.target.value; kvSet('settings', settings); };
  $('#np').onchange = e => { settings.newPerDay = Math.max(0, +e.target.value || 0); kvSet('settings', settings); };
  $('#hd').onchange = e => { settings.hideDrafts = e.target.checked; kvSet('settings', settings); };
  $('#ex').onclick = exportProgress;
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
const manualKey = n => /QUAL Lesson (\d)/i.test(n) ? 'QUAL' + n.match(/QUAL Lesson (\d)/i)[1] : /\bMEL\b/i.test(n) ? 'MEL' : /\bCDL\b/i.test(n) ? 'CDL' : /ops.?specs/i.test(n) ? 'OPSSPECS' : /PRM/i.test(n) ? 'PRM' : /QRH/i.test(n) ? 'QRH' : /FOM/i.test(n) ? 'FOM' : /POH/i.test(n) ? 'POH' : null;
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
function openRef(src, page) {
  ref = { src, page: +page, zoom: 1 }; document.body.classList.add('refopen'); renderRef();
}
function closeRef() { ref = null; document.body.classList.remove('refopen'); const r = $('#ref'); if (r) r.innerHTML = ''; }
async function renderRef() {
  if (!ref) return;
  const el = $('#ref'), { src, page } = ref;
  el.innerHTML = `<div class="rbar"><b>${esc(src)} p.${page}<span id="rn" class="muted"></span></b><span class="rbtns"><button class="small" id="rp">‹</button><button class="small" id="rx">›</button><button class="small" id="rz1">−</button><button class="small" id="rz2">+</button><button class="small" id="rc">✕</button></span></div><div class="rbody" id="rb"><div class="note">Loading…</div></div>`;
  $('#rc').onclick = closeRef;
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
document.addEventListener('click', e => { const b = e.target.closest('[data-open]'); if (b) { const [s, p] = b.dataset.open.split(':'); openRef(s, p); } });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && ref) closeRef(); if (ref && (e.key === '[' || e.key === ']')) { ref.page += e.key === ']' ? 1 : -1; renderRef(); } });
let rsz; window.addEventListener('resize', () => { clearTimeout(rsz); rsz = setTimeout(renderRef, 250); });

// ---------- boot ----------
document.querySelectorAll('#tabs button').forEach(b => b.onclick = () => show(b.dataset.tab));
(async () => {
  idb = await dbOpen();
  deck = (await kvGet('deck')) || deck;
  events = (await kvGet('events')) || [];
  settings = Object.assign(settings, (await kvGet('settings')) || {});
  if (!settings.device) { settings.device = 'd' + uid().slice(0, 5); await kvSet('settings', settings); }
  navigator.storage?.persist?.();
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(() => {});
  show('study');
})();
