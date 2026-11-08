// The Publishing page: dbenbenn's prove2.me publish jobs (bundles and statements), from /publish-jobs.json,
// which claude-private/tools/publish-jobs/poll.py rewrites every 2 minutes.
const $id = id => document.getElementById(id);
const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const TZ = 'Europe/Berlin';
const tzName = t => new Intl.DateTimeFormat('en-GB',{timeZone:TZ,timeZoneName:'short'}).formatToParts(new Date(t*1000))
  .find(x => x.type === 'timeZoneName').value.replace('GMT+1','CET').replace('GMT+2','CEST');
const fmtT = t => new Date(t*1000).toLocaleTimeString('de-DE',{timeZone:TZ,hour:'2-digit',minute:'2-digit'});
const fmtDay = t => new Date(t*1000).toLocaleDateString('en-CA',{timeZone:TZ});
const fmtAt = t => t ? (fmtDay(t) === fmtDay(Date.now()/1000) ? '' : fmtDay(t) + ' ') + fmtT(t) + ' ' + tzName(t) : '—';
const dur = s => s < 90 ? `${s} s` : s < 5400 ? `${Math.round(s/60)} min` : `${(s/3600).toFixed(1)} h`;
const ago = s => dur(Math.max(0, Math.round(s))) + ' ago';
const n = x => (x || 0).toLocaleString();
const KIND = {problem: 'statement', definition: 'bundle'};
const store = { get(k, d){ try { return localStorage.getItem('pj-' + k) || d; } catch (e) { return d; } },
                set(k, v){ try { localStorage.setItem('pj-' + k, v); } catch (e) {} } };

let D = null, shown = 150;
const ui = { tab: location.hash === '#published' ? 'published' : location.hash === '#running' ? 'running'
               : location.hash === '#failed' ? 'failed' : store.get('tab', 'failed'),
             kind: store.get('kind', 'all'), res: store.get('res', 'open'), q: '' };

function seg(el, opts, cur, onPick){
  el.innerHTML = opts.map(([v, label]) => `<button type="button" data-v="${v}" aria-pressed="${v === cur}">${label}</button>`).join('');
  el.onclick = e => { const b = e.target.closest('button'); if (b) onPick(b.dataset.v); };
}

function sum(o){ return Object.values(o || {}).reduce((a, b) => a + b, 0); }
function both(rec, st){ return ((rec.problem || {})[st] || 0) + ((rec.definition || {})[st] || 0); }

function tiles(){
  const r24 = D.recent['24h'], bad24 = both(r24, 'FAILED') + both(r24, 'ERROR');
  const tot = D.totals, pub = both(tot, 'PUBLISHED');
  const t = [
    {k: 'In progress', v: D.running.length, d: 'pending or compiling now', tab: 'running'},
    {k: 'Still failing', v: D.open_failures, d: 'names whose latest try failed', tab: 'failed', res: 'open', warn: D.open_failures > 0},
    {k: 'Published, last 24 h', v: both(r24, 'PUBLISHED'), d: `${n((r24.problem||{}).PUBLISHED)} statements · ${n((r24.definition||{}).PUBLISHED)} bundles`, tab: 'published'},
    {k: 'Failed, last 24 h', v: bad24, d: `${n(both(r24,'FAILED'))} failed · ${n(both(r24,'ERROR'))} errored`, tab: 'failed', res: 'all'},
    {k: 'All time', v: pub, d: `published: ${n((tot.problem||{}).PUBLISHED)} statements · ${n((tot.definition||{}).PUBLISHED)} bundles`, tab: 'published'},
  ];
  $id('tiles').innerHTML = t.map((x, i) => `<a class="pj-tile${x.warn ? ' warn' : ''}" href="#t-jobs" data-i="${i}">
    <div class="k">${x.k}</div><div class="v">${n(x.v)}</div><div class="d">${esc(x.d)}</div></a>`).join('');
  $id('tiles').onclick = e => { const a = e.target.closest('a'); if (!a) return; const x = t[+a.dataset.i];
    ui.tab = x.tab; if (x.res) ui.res = x.res; shown = 150; drawList(); };
}

// one stacked bar per day; series [{key, label, color}] read from each daily row
function bars(el, series){
  const rows = D.daily, tot = rows.map(r => series.reduce((a, s) => a + (r[s.key] || 0), 0));
  const max = Math.max(1, ...tot), top = niceTop(max);
  el.innerHTML = `<div class="pj-axis"><span>${n(top)}</span><span>${n(top/2)}</span><span>0</span></div>
    <div class="pj-plot">${rows.map((r, i) => `<div class="pj-col" tabindex="0" data-i="${i}">${series.map(s =>
      r[s.key] ? `<i style="height:calc(${100 * r[s.key] / top}% - 2px);background:var(${s.color})"></i>` : '').join('')}</div>`).join('')}</div>
    <div class="pj-x"><span>${rows[0].day.slice(5)}</span><span>${rows[Math.floor(rows.length/2)].day.slice(5)}</span><span>today</span></div>`;
  const tip = e => { const c = e.target.closest('.pj-col'); if (!c) return hideTip(); const r = rows[+c.dataset.i];
    showTip(c, `<b>${r.day}</b>` + series.map(s => `<span>${s.label}:</span> ${n(r[s.key])}`).join('<br>')); };
  el.onmouseover = tip; el.onfocusin = tip; el.onclick = tip; el.onmouseleave = hideTip; el.onfocusout = hideTip;
}
function niceTop(m){ const p = Math.pow(10, Math.floor(Math.log10(m))); for (const f of [1, 2, 2.5, 5, 10]) if (f * p >= m) return f * p; return 10 * p; }
let tipEl = null;
function showTip(anchor, html){
  if (!tipEl) { tipEl = document.createElement('div'); tipEl.className = 'pj-tip'; document.body.appendChild(tipEl); }
  tipEl.innerHTML = html; tipEl.hidden = false;
  const r = anchor.getBoundingClientRect(), w = tipEl.offsetWidth;
  tipEl.style.left = Math.max(8, Math.min(window.innerWidth - w - 8, r.left + r.width/2 - w/2)) + 'px';
  tipEl.style.top = Math.max(8, r.top - tipEl.offsetHeight - 6) + 'px';
}
function hideTip(){ if (tipEl) tipEl.hidden = true; }

const PUB = [{key: 'problem:PUBLISHED', label: 'Statements', color: '--series-1'},
             {key: 'definition:PUBLISHED', label: 'Bundles', color: '--series-2'}];
const BADS = [{key: 'BAD', label: 'Failed or errored', color: '--warn'}];   // one series: the table splits nothing further

function charts(){
  $id('leg-pub').innerHTML = PUB.map(s => `<span><i style="background:var(${s.color})"></i>${s.label}</span>`).join('');
  bars($id('ch-pub'), PUB);
  for (const r of D.daily) r.BAD = (r['problem:BAD'] || 0) + (r['definition:BAD'] || 0);
  bars($id('ch-bad'), BADS);
  $id('daytab').innerHTML = `<div class="dtab pj"><span class="h">day</span><span class="h r">statements published</span>
    <span class="h r">bundles published</span><span class="h r">failed or errored</span>` +
    D.daily.slice().reverse().map(r => `<span>${r.day}</span><span class="r">${n(r['problem:PUBLISHED'])}</span>
    <span class="r">${n(r['definition:PUBLISHED'])}</span><span class="r">${n(r.BAD)}</span>`).join('') + '</div>';
}

function link(j){
  if (j.status === 'PUBLISHED' && j.tid && j.kind === 'problem')
    return `<a href="https://prove2.me/theorems/${esc(j.tid)}" target="_blank" rel="noopener">${esc(j.name)}</a>`;
  return `<span${j.tid ? ` title="definition id ${esc(j.tid)} (prove2.me has no page for bundles)"` : ''}>${esc(j.name)}</span>`;
}

const RES_LABEL = {open: 'still failing', retrying: 'retrying', fixed: 'fixed'};
function row(j){
  const res = j.res ? `<span class="chip ${j.res}" title="${j.tries} jobs for this name">${RES_LABEL[j.res]}${j.tries > 1 ? ` · ${j.tries} tries` : ''}</span>` : '';
  const when = j.status === 'PENDING' || j.status === 'COMPILING'
    ? `submitted ${fmtAt(j.created)} · ${dur(Math.round(Date.now()/1000 - j.created))}`
    : `${fmtAt(j.updated)} · took ${dur((j.updated || j.created) - j.created)}`;
  const title = j.title && !j.title.startsWith(j.name + ':') ? j.title : (j.title || '').slice(j.name.length + 1).trim();
  return `<div class="pj-row"><div class="nm"><span class="chip ${j.status}">${j.status}</span><span class="chip kind">${KIND[j.kind] || j.kind}</span>${res}${link(j)}${j.vis === 'private' ? ' <span class="chip kind">private</span>' : ''}</div>
    <div class="when">${when}</div>${title ? `<div class="ti">${esc(title)}</div>` : ''}${j.error ? `<div class="err">${esc(j.error)}</div>` : ''}</div>`;
}

function drawList(){
  store.set('tab', ui.tab); store.set('kind', ui.kind); store.set('res', ui.res);
  const nRes = r => D.failed.filter(j => r === 'all' || j.res === r).length;
  seg($id('seg-tab'), [['running', `In progress (${n(D.running.length)})`], ['failed', 'Failed'], ['published', 'Published']], ui.tab,
      v => { ui.tab = v; shown = 150; drawList(); });
  seg($id('seg-kind'), [['all', 'All'], ['problem', 'Statements'], ['definition', 'Bundles']], ui.kind,
      v => { ui.kind = v; shown = 150; drawList(); });
  $id('seg-res').hidden = ui.tab !== 'failed';
  seg($id('seg-res'), [['open', `Still failing`], ['retrying', `Retrying (${n(nRes('retrying'))})`], ['fixed', `Fixed (${n(nRes('fixed'))})`], ['all', 'All']], ui.res,
      v => { ui.res = v; shown = 150; drawList(); });
  let jobs = ui.tab === 'running' ? D.running : ui.tab === 'published' ? D.published : D.failed;
  if (ui.kind !== 'all') jobs = jobs.filter(j => j.kind === ui.kind);
  if (ui.tab === 'failed' && ui.res !== 'all') jobs = jobs.filter(j => j.res === ui.res);
  if (ui.tab === 'failed' && ui.res === 'open') {       // one row per name: its newest failure
    const seen = new Set(); jobs = jobs.filter(j => { const k = j.kind + ' ' + j.name; if (seen.has(k)) return false; seen.add(k); return true; });
  }
  const q = ui.q.trim().toLowerCase();
  if (q) jobs = jobs.filter(j => (j.name + ' ' + j.title + ' ' + j.error).toLowerCase().includes(q));
  const scope = ui.tab === 'published' ? `the newest ${n(D.published.length)} published jobs`
    : ui.tab === 'failed' ? (ui.res === 'open' ? 'one row per name, its newest failure' :
        `failures still unresolved, and those fixed in the last ${D.failed_days} days`)
    : 'jobs prove2.me has not finished';
  $id('list-sub').textContent = `${n(jobs.length)} shown of ${scope}, newest first.`;
  $id('list').innerHTML = jobs.length ? jobs.slice(0, shown).map(row).join('') : '<p class="empty">Nothing here.</p>';
  $id('more').hidden = jobs.length <= shown;
  $id('more').textContent = `Show more (${n(jobs.length - shown)} left)`;
}
$id('more').onclick = () => { shown += 300; drawList(); };
$id('q').oninput = e => { ui.q = e.target.value; shown = 150; drawList(); };

async function load(){
  try {
    const r = await fetch('/publish-jobs.json', {cache: 'no-store'});
    const d = await r.json();
    if (d.missing) { $id('upd').textContent = 'The publish-jobs poller has not written anything yet (user unit publish-jobs.service).'; return; }
    D = d;
  } catch (e) { $id('upd').textContent = 'Could not load /publish-jobs.json: ' + e; return; }
  const age = Date.now()/1000 - D.generated_at;
  $id('upd').textContent = `Polled ${ago(age)} (${fmtAt(D.generated_at)}) · ${n(D.stored)} jobs mirrored` +
    (D.api_total != null && D.api_total !== D.stored ? ` (the API says ${n(D.api_total)})` : '') +
    ` · full reread ${ago(D.generated_at - D.synced_at)}`;
  const stale = age > 900;
  $id('alarm').hidden = !(D.error || stale);
  $id('alarm').innerHTML = D.error ? `<b>The last poll failed</b>${esc(D.error)}. The numbers below are from the poll before.`
    : stale ? `<b>Not updated for ${dur(Math.round(age))}</b>Is publish-jobs.service running?` : '';
  tiles(); charts(); drawList();
}
load();
setInterval(load, 120000);   // the poller writes every 2 min
