// The top of the page: the at-a-glance tiles (machine and quota in one row), the Needs-you card (everything
// waiting for a person, gathered from status.json, agents.json and missions.json) and the Missions-in-flight
// card (missions.json, written by the mission tracker; its buttons post to /request), and the Hand-offs card
// (handoffs.json, written by tools/handoff; its buttons post to /request with kind 'handoff').
// Globals used: esc, fmtAt, ago, last, agentsData, sparkSvg, queueLi, store.
let missionsData = null;
let handoffsData = null;
const GLANCE_SPAN = 3 * 3600;

function tileHtml({label, value, sub, href, level, spark, title}){
  return `<a class="gt${level ? ' ' + level : ''}" href="${href}" title="${esc(title || 'Details below')}">
    <span class="gl">${esc(label)}</span><span class="gv">${value}</span>
    <span class="gs">${esc(sub || '')}</span>${spark || ''}</a>`;
}

function drawGlance(){
  const el = document.getElementById('glance');
  if (!el || !last || !last.system) return;
  const sy = last.system, M = sy.machine || [], r = M.length ? M[M.length-1] : null, now = last.updated;
  if (!r) { el.innerHTML = ''; return; }
  const recent = M.filter(x => x.t >= now - GLANCE_SPAN), cores = sy.cores_total || 1;
  const sum = o => Object.values(o || {}).reduce((a, b) => a + b, 0);
  const sp = (ys, top, label) => sparkSvg(recent.map((x, i) => [x.t, ys[i]]).filter(p => p[1] != null), 120, 22, top, label);
  const tiles = [];
  // memory: trouble is memory and swap nearly gone together (the banner's rule), not a full page cache
  const memUsed = sum(r.mem), avail = sy.free_gib, swapFree = sy.swap_free_gib || 0;
  tiles.push({label: 'Memory', value: `${memUsed.toFixed(1)}<small> / ${r.total.toFixed(0)} GiB</small>`,
    sub: `${avail} GiB available`, href: '#t-sys', level: avail + swapFree < 4 ? 'alarm' : avail < 4 ? 'warn' : '',
    spark: sp(recent.map(x => sum(x.mem)), r.total, 'memory in use, last 3 h')});
  const cpu = r.cpu ? sum(r.cpu) : null;
  tiles.push({label: 'CPU', value: cpu == null ? '—' : `${cpu.toFixed(1)}<small> / ${cores} cores</small>`, sub: 'busy now', href: '#t-sys',
    spark: sp(recent.map(x => x.cpu ? sum(x.cpu) : null), null, 'CPU in use, last 3 h')});
  tiles.push({label: 'Load', value: r.load1.toFixed(2), sub: `1-min avg · ${cores} cores`, href: '#t-sys',
    level: r.load1 > cores * 1.5 ? 'warn' : '', spark: sp(recent.map(x => x.load1), null, 'load, last 3 h')});
  if (sy.swap_total_gib) {
    const used = sy.swap_total_gib - sy.swap_free_gib;
    tiles.push({label: 'Swap', value: `${used.toFixed(1)}<small> / ${sy.swap_total_gib.toFixed(0)} GiB</small>`, sub: 'Lean spills here', href: '#t-sys',
      level: used > sy.swap_total_gib * 0.5 ? 'warn' : '', spark: sp(recent.map(x => x.swap ?? null), sy.swap_total_gib, 'swap in use, last 3 h')});
  }
  const P = sy.psi || [], lp = P.length ? P[P.length-1] : null;
  if (lp) {
    const pr = P.filter(x => x[0] >= now - GLANCE_SPAN);
    tiles.push({label: 'Stalls', value: `${Math.max(lp[3], lp[5]).toFixed(1)}<small> %</small>`, sub: `mem ${lp[3].toFixed(1)} · I/O ${lp[5].toFixed(1)}`,
      href: '#t-sys', level: lp[3] > 5 || lp[5] > 20 ? 'alarm' : '', title: 'Share of time every task waited (10 s average); the banner fires at memory 5%, I/O 20%',
      spark: sparkSvg(pr.map(x => [x[0], Math.max(x[3], x[5])]), 120, 22, null, 'worst full stall, last 3 h')});
  }
  const dn = sy.disk && sy.disk.now;
  if (dn) tiles.push({label: 'Disk', value: `${dn.free.toFixed(0)}<small> GiB free</small>`, sub: `${dn.used.toFixed(0)} of ${dn.total.toFixed(0)} GiB used`, href: '#t-disk',
    level: dn.free < 20 ? 'alarm' : dn.free < 40 ? 'warn' : '', title: 'The banner warns below 20 GiB free; the OAI queue stops launching below 40'});
  const q = last.quota ? last.quota.series : [], qn = [...q].reverse().find(x => x[3] != null);
  if (qn) {
    const qs = q.filter(x => x[3] != null && x[0] >= now - 7 * 86400).map(x => [x[0], x[3]]);
    tiles.push({label: 'Quota, 7 days', value: `${qn[3].toFixed(0)}<small> %</small>`, sub: qn[4] ? `resets ${fmtDate(qn[4])}` : '', href: '#t-quota',
      level: qn[3] >= 90 ? 'alarm' : qn[3] >= 75 ? 'warn' : '', spark: sparkSvg(qs, 120, 22, 100, '7-day quota, last 7 days')});
  }
  el.innerHTML = tiles.map(tileHtml).join('');
}

// ---- Needs you ----
const WAITS = {you: ['WAITING FOR YOU', 'warn'], start: ['READY TO START', 'ready'], claude: ['CLAUDE WORKING', 'running'],
               platform: ['WAITING FOR PROVE2.ME', ''], done: ['COMPLETE', 'done']};

function drawNeeds(){
  const el = document.getElementById('needs');
  if (!el || !last) return;
  const rows = [];   // {text (html), sub (html)}
  for (const m of (missionsData && missionsData.missions) || []) {
    const cur = m.steps.find(s => s.state === 'blocked' || s.state === 'failed') || m.steps.find(s => s.state !== 'done');
    if (m.waits === 'you') rows.push({text: `<a href="#m-${esc(m.key)}">${esc(m.title)}</a>: ${esc(cur.detail || cur.title)}`, tag: 'mission'});
    else if (m.waits === 'start') rows.push({text: `<a href="#m-${esc(m.key)}">${esc(m.title)}</a>: ${esc(cur.title)} is ready to start`, tag: 'mission'});
  }
  for (const h of (handoffsData && handoffsData.handoffs) || []) {
    if (['stalled', 'failed', 'blocked'].includes(h.state)) rows.push({text: `<a href="#ho-${esc(h.key)}">${esc(h.title)}</a>: ${esc(h.detail)}`, tag: 'hand-off'});
    else if (h.state === 'ready' && !h.auto) rows.push({text: `<a href="#ho-${esc(h.key)}">${esc(h.title)}</a>: the wait is over; its wrap-up is ready to start`, tag: 'hand-off'});
  }
  for (const s of last.sections || []) {
    for (const a of s.alerts || []) rows.push({text: `<a href="${hrefFor(isLive(s), 'h-' + s.id)}">${esc(carveView(s).title)}</a>${s.state === 'running' ? '' : ' (' + esc(s.state) + ')'}: <span class="atext">${esc(a)}</span>`, tag: 'alert'});
    if (s.stale) rows.push({text: `<a href="${hrefFor(isLive(s), 'h-' + s.id)}">${esc(carveView(s).title)}</a> is stale: no update for ${Math.round(s.age_secs / 60)} min`, tag: 'stale'});
  }
  for (const p of last.problems || []) rows.push({text: 'Unreadable section file: ' + esc(p), tag: 'section'});
  const Q = agentsData && agentsData.queue;
  if (Q && (Q.needs_person || []).length)
    rows.push({text: `OAI queue: ${Q.needs_person.length} group${Q.needs_person.length > 1 ? 's' : ''} the queue will not retry by itself`, tag: 'queue',
               more: `<ul class="nlist">${Q.needs_person.map(queueLi).join('')}</ul>`, k: 'queue'});
  const age = n => n == null ? '' : n < 3600 ? Math.round(n/60) + ' min' : n < 172800 ? Math.round(n/3600) + ' h' : Math.round(n/86400) + ' days';
  (last.inboxes || []).forEach((e, i) => {
    if (e.missing) rows.push({text: `${esc(e.label)}: directory missing (${esc(e.dir)})`, tag: 'inbox'});
    else if (e.count) rows.push({text: `${esc(e.label)}: ${e.count} waiting · oldest ${esc(age(e.oldest_s))}`, tag: 'inbox', k: 'inbox' + i,
      more: `<div class="nitems">${e.items.map(n => `<a href="/inbox/${i}/${encodeURIComponent(n)}" target="_blank" rel="noopener">${esc(n)}</a>`).join(' · ')}${e.count > e.items.length ? ' …' : ''}</div>`});
  });
  const opened = new Set([...el.querySelectorAll('details[open]')].map(d => d.dataset.k));
  el.innerHTML = rows.length ? '<ul class="needs">' + rows.map(r => `<li><span class="ntag">${esc(r.tag)}</span>` +
      (r.more ? `<details data-k="${esc(r.k)}"${opened.has(r.k) ? ' open' : ''}><summary>${r.text}</summary>${r.more}</details>` : `<span>${r.text}</span>`) + '</li>').join('') + '</ul>'
    : '<p class="allclear">Nothing needs you right now.</p>';
  const h = document.getElementById('t-needs');
  h.innerHTML = 'Needs you' + (rows.length ? ` <span class="count">${rows.length}</span>` : '');
}

// ---- Missions in flight ----
const STEP_WHO = {you: 'you', platform: 'prove2.me', claude: 'Claude'};
const pendingClicks = {};   // key -> {action, at}

function missionCard(m){
  const [wtxt, wcls] = WAITS[m.waits] || [m.waits, ''];
  const start = m.startable && m.steps.find(s => s.id === m.startable);
  const startLabel = start ? (start.state === 'ready' ? 'Start: ' : 'Retry: ') + start.title.replace(/:.*/, '') : '';
  const click = pendingClicks[m.key];
  const busy = click && !(m.pending && click.rid && m.pending.rid === click.rid);
  const steps = m.steps.map(s => `<li class="${s.state}" title="${esc(s.title)}: ${esc(s.state)}">
      <span class="sn">${esc(s.title)}</span><span class="sw">${esc(STEP_WHO[s.who] || s.who)} · ${esc(s.state)}</span>
      ${s.detail ? `<span class="sd">${esc(s.detail)}</span>` : ''}</li>`).join('');
  const tasks = start ? `<details class="mtasks"><summary>What ${esc(start.title.replace(/:.*/, ''))} will do (${m.tasks[start.id].length} tasks)</summary><ol>${m.tasks[start.id].map(t => `<li>${esc(t)}</li>`).join('')}</ol></details>` : '';
  const res = m.pending && m.pending.result ? `<p class="mres${/^failed/.test(m.pending.result) ? ' bad' : ''}">Last ${esc(m.pending.action)} ${esc(fmtAt(m.pending.at))}: ${esc(m.pending.result)}</p>` : '';
  const err = m.check_error ? `<p class="mres bad">Last API check failed: ${esc(m.check_error)}</p>` : '';
  return `<article class="ms" id="m-${esc(m.key)}">
    <div class="mhead"><span class="mt">${esc(m.title)}</span><span class="badge ${wcls}">${esc(wtxt)}</span>
      <span class="mbtns">
        <button class="btn" data-key="${esc(m.key)}" data-act="check"${busy ? ' disabled' : ''}>${busy && click.action === 'check' ? 'Checking…' : 'Check now'}</button>
        ${start ? `<button class="btn primary" data-key="${esc(m.key)}" data-act="start" data-step="${esc(start.title)}"${busy ? ' disabled' : ''}>${busy && click.action === 'start' ? 'Starting…' : esc(startLabel)}</button>` : ''}
      </span></div>
    <ol class="msteps">${steps}</ol>
    ${tasks}${res}${err}
    <p class="meta">${m.links.map(l => `<a href="${esc(l.url)}" target="_blank" rel="noopener">${esc(l.label)}</a>`).join(' · ')}
      ${m.repo ? ' · repo <code>' + esc(m.repo.replace(/^\/home\/[^/]+/, '~')) + '</code>' : ''}${m.memory ? ' · memory <code>' + esc(m.memory) + '</code>' : ''}
      · checked ${m.checked ? esc(ago(Math.round(Date.now()/1000 - m.checked))) : 'never'}</p>
  </article>`;
}

function drawMissions(){
  const el = document.getElementById('missions'), sub = document.getElementById('missions-sub');
  if (!el) return;
  const D = missionsData;
  if (!D || !D.updated) {
    sub.textContent = 'The mission tracker has not written anything yet (mission-tracker.service).';
    el.innerHTML = ''; return;
  }
  const stale = Date.now()/1000 - D.updated > 300;
  if (VIEW === 'done') { sub.textContent = 'Missions whose five steps are all done; each leaves this list 3 days after completing.'; }
  else sub.innerHTML = (stale ? `<b class="warntxt">The mission tracker last wrote ${esc(ago(Math.round(Date.now()/1000 - D.updated)))}: is mission-tracker.service running?</b> ` : '') +
    `From hand-over to post-approval cleanup. prove2.me is checked every ${Math.round((D.auto_every || 900) / 60)} min and when you click Check now; ` +
    'Start runs that step as a headless Claude agent (subscription), which marks the step done when it finishes.';
  // complete missions are on the Finished page
  const M = D.missions.filter(m => m.complete === (VIEW === 'done'));
  el.innerHTML = M.length ? M.map(missionCard).join('') : `<p class="empty">${VIEW === 'main' ? 'No mission is between hand-over and cleanup.' : 'No mission completed in the last 3 days.'}</p>`;
}

async function loadMissions(){
  try { missionsData = await (await fetch('/missions.json?' + Date.now())).json(); } catch (e) { return; }
  keepScroll(() => { drawMissions(); drawNeeds(); if (typeof drawFinishedLinks === 'function') drawFinishedLinks(); });
}

document.addEventListener('click', async e => {
  const b = e.target.closest('#missions button[data-act]');
  if (!b) return;
  const key = b.dataset.key, action = b.dataset.act;
  if (action === 'start' && !confirm(`Start a headless Claude agent (on the subscription) for “${b.dataset.step}” of ${key}?`)) return;
  pendingClicks[key] = {action};
  keepScroll(drawMissions);
  try {
    const r = await fetch('/request', {method: 'POST', headers: {'Content-Type': 'application/json', 'X-Monitor-Request': '1'}, body: JSON.stringify({action, key})});
    const j = await r.json();
    if (!r.ok) throw new Error(j.error || r.status);
    pendingClicks[key].rid = j.queued;
  } catch (err) { delete pendingClicks[key]; alert('The request failed: ' + err.message); drawMissions(); return; }
  // the tracker picks requests up within a few seconds; poll until this mission reports the outcome
  for (let i = 0; i < 30; i++) {
    await new Promise(res => setTimeout(res, 2000));
    await loadMissions();
    const m = (missionsData.missions || []).find(x => x.key === key);
    if (m && m.pending && m.pending.rid === pendingClicks[key].rid) break;
  }
  delete pendingClicks[key];
  keepScroll(drawMissions);
});

loadMissions(); setInterval(loadMissions, 30000);

// ---- Hand-offs ----
// An agent whose remaining work is a long wait hands it to tools/handoff and exits; the service watches
// the units (no tokens) and this card offers the wrap-up agent once they end.
const HO_BADGE = {waiting: ['WAITING', ''], stalled: ['STALLED', 'warn'], ready: ['READY TO START', 'ready'],
                  running: ['CLAUDE WORKING', 'running'], failed: ['WRAP-UP FAILED', 'warn'],
                  blocked: ['WAITING FOR YOU', 'warn'], done: ['DONE', 'done']};
const hoClicks = {};

function handoffCard(h){
  const [btxt, bcls] = HO_BADGE[h.state] || [h.state, ''];
  const click = hoClicks[h.key];
  const busy = click && !(h.pending && click.rid && h.pending.rid === click.rid);
  const label = h.state === 'ready' ? 'Start wrap-up' : h.state === 'stalled' ? 'Send a Claude to look' : 'Retry wrap-up';
  const agentLink = n => `<a href="/page/agent.html?name=${encodeURIComponent(n)}">${esc(n)}</a>`;
  const units = Object.entries(h.units || {}).map(([u, a]) => `<code>${esc(u)}</code> ${a ? 'running' : 'ended'}`).join(' · ');
  const res = h.pending && h.pending.result ? `<p class="mres${/^failed/.test(h.pending.result) ? ' bad' : ''}">Last ${esc(h.pending.action)} ${esc(fmtAt(h.pending.at))}: ${esc(h.pending.result)}</p>` : '';
  const prog = h.progress_age != null ? ` · progress file changed ${esc(ago(h.progress_age))}` : '';
  return `<article class="ms" id="ho-${esc(h.key)}">
    <div class="mhead"><span class="mt">${esc(h.title)}</span><span class="badge ${bcls}">${esc(btxt)}</span>
      <span class="mbtns">
        ${h.state !== 'done' ? `<button class="btn" data-key="${esc(h.key)}" data-act="check"${busy ? ' disabled' : ''}>${busy && click.action === 'check' ? 'Checking…' : 'Check now'}</button>` : ''}
        ${h.startable ? `<button class="btn primary" data-key="${esc(h.key)}" data-act="start"${busy ? ' disabled' : ''}>${busy && click.action === 'start' ? 'Starting…' : esc(label)}</button>` : ''}
      </span></div>
    <p class="hod">${esc(h.detail)}</p>
    ${res}
    <p class="meta">${units || 'no units'}${prog}${h.log_line ? ' · log: <code>' + esc(h.log_line) + '</code>' : ''}</p>
    <p class="meta">${h.from ? 'handed off by ' + agentLink(h.from) : ''}${h.agent ? ' · wrap-up ' + agentLink(h.agent) : ''}
      ${h.section ? ` · <a href="/#h-${esc(h.section)}">live progress</a>` : ''}${h.auto ? ' · starts by itself' : ''}
      ${h.repo ? ' · records <code>' + esc(h.repo.replace(/^\/home\/[^/]+/, '~')) + '</code>' : ''}
      · checked ${h.checked ? esc(ago(Math.round(Date.now()/1000 - h.checked))) : 'never'}</p>
  </article>`;
}

function drawHandoffs(){
  const el = document.getElementById('handoffs'), sub = document.getElementById('handoffs-sub');
  if (!el) return;
  const D = handoffsData;
  if (!D || !D.updated) { sub.textContent = 'The hand-off service has not written anything yet (handoff.service).'; el.innerHTML = ''; return; }
  const stale = Date.now()/1000 - D.updated > 600;
  if (VIEW === 'done') sub.textContent = 'Hand-offs whose wrap-up is done; each leaves this list 3 days later.';
  else sub.innerHTML = (stale ? `<b class="warntxt">The hand-off service last wrote ${esc(ago(Math.round(Date.now()/1000 - D.updated)))}: is handoff.service running?</b> ` : '') +
    `Long waits a headless agent handed over before exiting, so no Claude is woken just to read a status line. The units are checked every ${Math.round((D.every || 60) / 60)} min (no tokens); ` +
    'when they end, Start runs a fresh wrap-up agent (subscription), which marks the hand-off done.';
  const L = D.handoffs.filter(h => (h.state === 'done') === (VIEW === 'done'));
  el.innerHTML = L.length ? L.map(handoffCard).join('') : `<p class="empty">${VIEW === 'main' ? 'Nothing handed off.' : 'No hand-off finished in the last 3 days.'}</p>`;
}

async function loadHandoffs(){
  try { handoffsData = await (await fetch('/handoffs.json?' + Date.now())).json(); } catch (e) { return; }
  keepScroll(() => { drawHandoffs(); drawNeeds(); });
}

document.addEventListener('click', async e => {
  const b = e.target.closest('#handoffs button[data-act]');
  if (!b) return;
  const key = b.dataset.key, action = b.dataset.act;
  if (action === 'start' && !confirm(`Start a headless Claude agent (on the subscription) to wrap up ${key}?`)) return;
  hoClicks[key] = {action};
  keepScroll(drawHandoffs);
  try {
    const r = await fetch('/request', {method: 'POST', headers: {'Content-Type': 'application/json', 'X-Monitor-Request': '1'}, body: JSON.stringify({action, key, kind: 'handoff'})});
    const j = await r.json();
    if (!r.ok) throw new Error(j.error || r.status);
    hoClicks[key].rid = j.queued;
  } catch (err) { delete hoClicks[key]; alert('The request failed: ' + err.message); drawHandoffs(); return; }
  for (let i = 0; i < 30; i++) {
    await new Promise(res => setTimeout(res, 2000));
    await loadHandoffs();
    const h = (handoffsData.handoffs || []).find(x => x.key === key);
    if (h && h.pending && h.pending.rid === hoClicks[key].rid) break;
  }
  delete hoClicks[key];
  keepScroll(drawHandoffs);
});

loadHandoffs(); setInterval(loadHandoffs, 30000);
