// The main page (index.html, data-view="main") and the Finished page (done.html, data-view="done") share this
// script: the main page shows work in progress and the machine, the Finished page what has ended.
const VIEW = document.body.dataset.view || 'main';
const LIVE_STATES = ['running', 'waiting', 'paused'];
const isLive = s => LIVE_STATES.includes(s.state);
const $id = id => document.getElementById(id);
// where a section or card lives: anchors to it work from either page
const hrefFor = (live, anchor) => (live === (VIEW === 'main') ? '' : live ? '/' : '/page/done.html') + '#' + anchor;

// Keep what is on screen in place across a redraw. The page rebuilds its cards every 15-30 s; when a card
// above the reader changes height (or the element the browser anchored to is replaced, and phones do no
// anchoring at all) everything below jumps. So: before the redraw, find the element at the top of the
// viewport, remember the nearest ancestor with an id and the child-index path from it, and its position;
// afterwards, find the same path again and scroll by however far it moved.
function keepScroll(fn){
  if (window.scrollY < 4) { fn(); return; }        // at the top: nothing to keep
  const y = 60, x = Math.min(window.innerWidth / 2, 400);
  let el = document.elementFromPoint(x, y), path = [];
  while (el && el !== document.body && !el.id) { const p = el.parentElement; if (!p) break; path.unshift([...p.children].indexOf(el)); el = p; }
  if (!el || !el.id || el === document.body) { fn(); return; }
  const id = el.id, target = () => { let e = $id(id); for (const i of path) { if (!e || !e.children[i]) break; e = e.children[i]; } return e; };
  const before = target().getBoundingClientRect().top;
  fn();
  const t = target();
  if (t) { const d = t.getBoundingClientRect().top - before; if (Math.abs(d) >= 1) window.scrollBy(0, d); }
}

const TZ = 'Europe/Berlin', tzName = t => new Intl.DateTimeFormat('en-GB',{timeZone:'Europe/Berlin',timeZoneName:'short'}).formatToParts(new Date(t*1000)).find(x=>x.type==='timeZoneName').value.replace('GMT+1','CET').replace('GMT+2','CEST');
const fmtT = t => new Date(t*1000).toLocaleTimeString('de-DE',{timeZone:TZ,hour:'2-digit',minute:'2-digit'});
const fmtDay = t => new Date(t*1000).toLocaleDateString('en-CA',{timeZone:TZ});
const fmtAt = t => (fmtDay(t)===fmtDay(Date.now()/1000) ? '' : fmtDay(t)+' ') + fmtT(t) + ' ' + tzName(t);
const fmtSpan = (a, b) => b - a < 60 ? fmtAt(a) : fmtDay(a)!==fmtDay(b) ? fmtAt(a) + ' – ' + fmtAt(b)
  : (fmtDay(a)===fmtDay(Date.now()/1000) ? '' : fmtDay(a)+' ') + fmtT(a) + '–' + fmtT(b) + ' ' + tzName(b);
const esc = s => String(s??'').replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const ago = s => s<90 ? `${s} s ago` : s<5400 ? `${Math.round(s/60)} min ago` : `${(s/3600).toFixed(1)} h ago`;
const fmtWd = t => new Date(t*1000).toLocaleDateString('en-GB',{timeZone:TZ,weekday:'short'});
const xTicks = (u, splits) => { const span = u.scales.x.max - u.scales.x.min;
  return splits.map(v => span > 18*3600 ? fmtWd(v) + ' ' + fmtT(v) : fmtT(v)); };
const lastIdx = u => u.data[0].length - 1;
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const RANGES = [['30 min',1800],['1 h',3600],['3 h',10800],['12 h',43200],['48 h',172800]];
const store = {get(k,d){ try { return localStorage.getItem(k) ?? d; } catch(e) { return d; } }, set(k,v){ try { localStorage.setItem(k,v); } catch(e) {} }};
let range = +store.get('monitor.range', 3600);
let view = null;            // {min, max} while zoomed in by dragging; null: follow the range
const selected = {};        // section id -> phase shown in its chart
let last = null, charts = {}, chartKey = '';

// ---- range buttons ----
const rbox = $id('ranges') || document.createElement('div');
rbox.innerHTML = RANGES.map(([l,s]) => `<button data-s="${s}" aria-pressed="${s===range}">${l}</button>`).join('');
rbox.onclick = e => { const b = e.target.closest('button'); if (!b) return;
  range = +b.dataset.s; store.set('monitor.range', range); view = null;
  rbox.querySelectorAll('button').forEach(x => x.setAttribute('aria-pressed', x===b)); applyView(); };
if ($id('zoomed')) $id('zoomed').onclick = () => { view = null; applyView(); };

function applyView(){
  const now = last ? last.updated : Date.now()/1000;
  const [min, max] = view ? [view.min, view.max] : [now - range, now];
  for (const u of Object.values(charts)) u.setScale('x', {min, max});
  if ($id('zoomed')) $id('zoomed').hidden = !view;
}

// ---- charts ----
function baseOpts(el, height, series, yRange, fmt){
  return {
    width: Math.max(260, el.clientWidth), height,
    tzDate: ts => uPlot.tzDate(new Date(ts*1e3), TZ),
    cursor: {y: false, sync: {key: 'sys', setSeries: false}, drag: {x: true, y: false, setScale: false}, points: {size: 6}},
    select: {show: true},
    legend: {live: true},
    scales: {x: {time: true}, y: {range: yRange}},
    axes: [
      {stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {stroke: css('--grid')}, font: '11px system-ui', values: xTicks, space: 60},
      {stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {show: false}, font: '11px system-ui', size: 46,
       values: (u, vals) => vals.map(v => fmt(v))},
    ],
    series: [{value: (u, v, si, idx) => idx == null ? 'latest' : fmtAt(v)}, ...series],
    hooks: {
      setSelect: [u => { if (u.select.width < 4) return;
        const min = u.posToVal(u.select.left, 'x'), max = u.posToVal(u.select.left + u.select.width, 'x');
        u.setSelect({left: 0, top: 0, width: 0, height: 0}, false);
        view = {min, max}; applyView(); }],
      ready: [u => u.over.addEventListener('dblclick', () => { view = null; applyView(); })],
    },
  };
}

// stacked areas: series are drawn top first, each filled down to zero, so lower ones paint over
function stacked(el, height, x, groups, raw, labelOf, colorOf, fmt, unit, yRange){
  const cum = []; let acc = x.map(() => 0);
  for (const g of groups) { acc = acc.map((a, i) => raw[g][i] == null ? null : (a ?? 0) + raw[g][i]); cum.push(acc); }
  const order = groups.map((g, i) => i).reverse();
  const series = order.map(i => ({label: labelOf(groups[i]), stroke: css(colorOf(groups[i])), fill: css(colorOf(groups[i])), width: 1,
    // u._raw: upsert reuses a chart and only swaps its data, so the legend must not keep the first build's values
    value: (u, v, si, idx) => { const j = idx ?? lastIdx(u), r = (u._raw || raw)[groups[i]][j]; return r == null ? '—' : fmt(r) + ' ' + unit; }}));
  const data = [x, ...order.map(i => cum[i])];
  return {opts: baseOpts(el, height, series, yRange, fmt), data, raw};
}

function lines(el, height, x, defs, fmt, unit, yRange){
  const series = defs.map(d => ({label: d.label, stroke: css(d.color), width: 2,
    value: (u, v, si, idx) => { const r = idx == null ? u.data[si][lastIdx(u)] : v; return r == null ? '—' : fmt(r) + unit; }}));
  return {opts: baseOpts(el, height, series, yRange, fmt), data: [x, ...defs.map(d => d.ys)]};
}

function upsert(id, built){
  const el = document.getElementById(id);
  if (charts[id] && charts[id]._key === built.key) { charts[id]._raw = built.raw; charts[id].setData(built.data, false); return; }
  if (charts[id]) charts[id].destroy();
  el.innerHTML = '';
  charts[id] = new uPlot(built.opts, built.data, el);
  charts[id]._key = built.key;
  charts[id]._raw = built.raw;
}


function drawSystem(sy){
  if (!$id('c-mem')) return;
  const M = sy.machine || [], lastRow = M.length ? M[M.length-1] : null;
  // fixed categories (monitor.CATS): where a process lives, not which section claims it
  const CAT_COLOR = {lean: '--series-1', queue: '--series-2', claude: '--series-4', rest: '--rest'};
  const groups = ['lean', 'queue', 'claude', 'rest'];
  const labelOf = g => sy.labels[g] || g;
  const colorOf = g => CAT_COLOR[g] || '--rest';
  const key = groups.join('|') + '|' + Object.keys(sy.labels).map(k => sy.labels[k]).join('|') + '|' + document.documentElement.clientWidth + '|' + matchMedia('(prefers-color-scheme: dark)').matches;
  if (key !== chartKey) { for (const u of Object.values(charts)) u.destroy(); charts = {}; chartKey = key; }
  const x = M.map(r => r.t), memTotal = lastRow ? lastRow.total : 64, cores = sy.cores_total || 32;
  const memRaw = {}, cpuRaw = {};
  for (const g of groups) { memRaw[g] = M.map(r => r.mem[g] ?? 0); cpuRaw[g] = M.map(r => r.cpu ? (r.cpu[g] ?? 0) : null); }
  const H = 220;
  let b = stacked(document.getElementById('c-mem'), H, x, groups, memRaw, labelOf, colorOf, v => v.toFixed(1), 'GiB', [0, memTotal]); b.key = key; upsert('c-mem', b);
  // CPU: scaled to what is visible, so a core or two of use is not lost against 32
  b = stacked(document.getElementById('c-cpu'), H, x, groups, cpuRaw, labelOf, colorOf, v => v.toFixed(1), 'cores',
              (u, mn, mx) => [0, Math.min(cores, Math.max(1, Math.ceil((mx || 0) * 1.15)))]); b.key = key; upsert('c-cpu', b);
  // swap: recorded since 2026-10-30, so older rows have none; scale to the swap size
  const swapTotal = sy.swap_total_gib || (lastRow && lastRow.swap_total) || 1;
  b = lines(document.getElementById('c-swap'), H, x, [{label: 'swap used', color: '--series-5', ys: M.map(r => r.swap ?? null)}], v => v.toFixed(1), ' GiB',
            [0, swapTotal]); b.key = key; upsert('c-swap', b);
  b = lines(document.getElementById('c-load'), H, x, [{label: 'load', color: '--series-1', ys: M.map(r => r.load1)}], v => v.toFixed(1), '',
            (u, mn, mx) => [0, Math.max(1, Math.ceil((mx || 0) * 1.15))]); b.key = key; upsert('c-load', b);
  const P = sy.psi || [], lp = P.length ? P[P.length-1] : null;
  b = lines(document.getElementById('c-psi'), H, P.map(r => r[0]), [
        {label: 'memory (full)', color: '--series-4', ys: P.map(r => r[3])},
        {label: 'I/O (full)', color: '--series-2', ys: P.map(r => r[5])},
        {label: 'CPU (some)', color: '--series-1', ys: P.map(r => r[1])}], v => v.toFixed(1), '%',
        (u, mn, mx) => [0, Math.max(5, Math.ceil((mx || 0) * 1.15))]); b.key = key; upsert('c-psi', b);
  applyView();
  if (lp) document.getElementById('s-psi').textContent = `Share of time tasks waited (10 s average). "Full": every task waited, which is what makes the box freeze; the banner fires at memory 5%, I/O 20%. Now: memory ${lp[3].toFixed(1)}%, I/O ${lp[5].toFixed(1)}%, CPU ${lp[1].toFixed(1)}%`;
  if (lastRow){
    const used = Object.values(lastRow.mem).reduce((a,b)=>a+b,0);
    const swap = sy.swap_total_gib ? ` · swap ${(sy.swap_total_gib - sy.swap_free_gib).toFixed(1)} of ${sy.swap_total_gib} GiB used` : '';
    document.getElementById('s-mem').textContent = `now ${used.toFixed(1)} of ${memTotal} GiB in use · ${sy.free_gib} GiB available${swap}`;
    if (lastRow.cpu) document.getElementById('s-cpu').textContent = `now ${Object.values(lastRow.cpu).reduce((a,b)=>a+b,0).toFixed(1)} of ${cores} cores busy (scale fits the visible range)`;
    document.getElementById('s-swap').textContent = sy.swap_total_gib
      ? `now ${(sy.swap_total_gib - sy.swap_free_gib).toFixed(1)} of ${sy.swap_total_gib} GiB used (Lean spills here when RAM fills; history starts 30 Oct)` : 'no swap configured';
    document.getElementById('s-load').textContent = `now ${lastRow.load1.toFixed(2)} on ${cores} cores`;
  }
  const L = sy.lean || [];
  document.getElementById('lean').innerHTML = L.length ? `<p class="chart-sub">${L.filter(r=>/^lean\b/.test(r.what)).length} Lean, ${L.filter(r=>/^lake\b/.test(r.what)).length} lake</p>` + procTable(L, true) : '<p class="empty">No Lean running.</p>';
}

// ---- disk: hourly category rows (monitor.disk_scan), its own range (days, not the system charts' hours) ----
const DISK_GROUPS = ['lean_build', 'lean_lib', 'jobs', 'sources', 'cache', 'rest'];
const DISK_COLOR = {lean_build: '--series-1', lean_lib: '--series-3', jobs: '--series-2', sources: '--series-4', cache: '--disk-5', rest: '--rest'};
const DISK_RANGES = [['2 days',172800],['7 days',604800],['30 days',2592000]];
let diskRange = +store.get('monitor.diskRange', 604800), diskView = null, diskChart = null, diskKey = '';
const dbox = $id('disk-ranges') || document.createElement('div');
dbox.innerHTML = DISK_RANGES.map(([l,s]) => `<button data-s="${s}" aria-pressed="${s===diskRange}">${l}</button>`).join('');
dbox.onclick = e => { const b = e.target.closest('button'); if (!b) return;
  diskRange = +b.dataset.s; store.set('monitor.diskRange', diskRange); diskView = null;
  dbox.querySelectorAll('button').forEach(x => x.setAttribute('aria-pressed', x===b)); diskApply(); };
if ($id('disk-zoomed')) $id('disk-zoomed').onclick = () => { diskView = null; diskApply(); };
function diskApply(){
  if (!diskChart) return;
  const now = last ? last.updated : Date.now()/1000;
  diskChart.setScale('x', diskView || {min: now - diskRange, max: now});
  document.getElementById('disk-zoomed').hidden = !diskView;
}
const fmtDate = t => new Date(t*1000).toLocaleDateString('en-GB',{timeZone:TZ,weekday:'short',day:'numeric',month:'short'});
const diskTicks = (u, splits) => (u.scales.x.max - u.scales.x.min) > 3*86400 ? splits.map(fmtDate) : xTicks(u, splits);
const gib = v => v == null ? '—' : v.toFixed(1) + ' GiB';
const delta = v => v == null ? '—' : (v >= 0.05 ? '+' : v <= -0.05 ? '−' : '±') + Math.abs(v).toFixed(1) + ' GiB';

function drawDisk(d){
  if (!$id('c-disk')) return;
  const R = (d && d.rows) || [], now = d && d.now, labels = (d && d.labels) || {};
  const sub = document.getElementById('disk-sub'), lastR = R.length ? R[R.length-1] : null;
  sub.textContent = (now ? `now ${now.used.toFixed(1)} of ${now.total.toFixed(0)} GiB used · ${now.free.toFixed(1)} GiB free` : 'no reading')
    + (lastR ? ` · categories last measured ${fmtAt(lastR.t)}${lastR.secs != null ? ` (took ${lastR.secs} s)` : ''}` : ' · first category measurement pending (hourly, about 15 s)');
  const el = document.getElementById('c-disk');
  if (!R.length) { el.innerHTML = '<p class="empty">No measurement yet.</p>'; document.getElementById('disk-table').innerHTML = ''; return; }
  const x = R.map(r => r.t), raw = {};
  for (const g of DISK_GROUPS) raw[g] = R.map(r => r.cats[g] ?? null);
  const total = (now && now.total) || lastR.total;
  const b = stacked(el, 240, x, DISK_GROUPS, raw, g => labels[g] || g, g => DISK_COLOR[g], v => v.toFixed(0), 'GiB', [0, total]);
  // its own zoom and no cursor sync: the system charts' range is hours, this one days
  delete b.opts.cursor.sync;
  b.opts.axes[0].values = diskTicks;
  b.opts.axes[0].space = 100;          // a day apart at 7 days, so a date is not printed twice
  b.opts.hooks = {
    setSelect: [u => { if (u.select.width < 4) return;
      diskView = {min: u.posToVal(u.select.left, 'x'), max: u.posToVal(u.select.left + u.select.width, 'x')};
      u.setSelect({left: 0, top: 0, width: 0, height: 0}, false); diskApply(); }],
    ready: [u => u.over.addEventListener('dblclick', () => { diskView = null; diskApply(); })]};
  b.opts.series[0].value = (u, v, si, idx) => idx == null ? 'latest' : fmtAt(v);
  const key = document.documentElement.clientWidth + '|' + matchMedia('(prefers-color-scheme: dark)').matches + '|' + DISK_GROUPS.map(g => labels[g]).join('|');
  if (diskChart && diskKey === key) { diskChart._raw = b.raw; diskChart.setData(b.data, false); }
  else { if (diskChart) diskChart.destroy(); el.innerHTML = ''; diskChart = new uPlot(b.opts, b.data, el); diskKey = key; diskChart._raw = b.raw; }
  diskApply();
  // the table: every category now and its change over a day and a week (also the chart's text view)
  const ago = s => { const t = lastR.t - s; const r = R.find(r => r.t >= t - 1800); return r && r.t <= t + 1800 ? r : null; };
  const d1 = ago(86400), d7 = ago(7*86400);
  const row = (name, sw, v, a, b) => `<span>${sw}${esc(name)}</span><span class="r">${gib(v)}</span><span class="r">${a}</span><span class="r">${b}</span>`;
  const sw = g => `<i class="sw" style="background:var(${DISK_COLOR[g]})"></i>`;
  document.getElementById('disk-table').innerHTML =
    '<span class="h">Category (last measurement)</span><span class="h r">Size</span><span class="h r">Change, 24 h</span><span class="h r">Change, 7 days</span>' +
    DISK_GROUPS.slice().reverse().map(g => row(labels[g] || g, sw(g), lastR.cats[g],
      d1 ? delta(lastR.cats[g] - (d1.cats[g] ?? 0)) : '—', d7 ? delta(lastR.cats[g] - (d7.cats[g] ?? 0)) : '—')).join('') +
    `<span class="tot">In use</span><span class="r tot">${gib(lastR.used)}</span><span class="r tot">${d1 ? delta(lastR.used - d1.used) : '—'}</span><span class="r tot">${d7 ? delta(lastR.used - d7.used) : '—'}</span>`;
}

// redraw for a new width only: phones fire resize when the address bar shows or hides while scrolling
let lastWidth = document.documentElement.clientWidth;
const redrawAll = () => { if (last) keepScroll(() => { chartKey = ''; drawSystem(last.system); drawDisk(last.system.disk); drawSections(last.sections || []); drawQuota(); }); };
window.addEventListener('resize', () => { clearTimeout(window._rz); window._rz = setTimeout(() => {
  const w = document.documentElement.clientWidth; if (w === lastWidth) return; lastWidth = w; redrawAll(); }, 200); });
matchMedia('(prefers-color-scheme: dark)').addEventListener('change', redrawAll);

// ---- page ----
async function load(){
  let s; try { s = await (await fetch('/status.json?'+Date.now())).json(); } catch(e) { return; }
  if (!s.updated) return;
  last = s;
  keepScroll(() => {
    $id('h1').textContent = (s.host||'machine') + (VIEW === 'done' ? ' monitor: finished work' : ' monitor');
    $id('upd').textContent = 'Updated ' + fmtAt(s.updated) + ' · refreshes every 30 s';
    const al = $id('alarm');
    al.hidden = !s.alerts.length;
    $id('favicon').href = s.alerts.length ? '/favicon-alarm.svg' : '/favicon.svg';
    al.innerHTML = s.alerts.length ? `<b>${esc(s.host||'machine')} needs attention</b><ul>${s.alerts.map(a=>`<li>${esc(a)}</li>`).join('')}</ul>` : '';
    const pr = $id('problems'), P = s.problems || [];
    if (pr) { pr.hidden = !P.length; pr.textContent = P.length ? 'Section files the page could not read: ' + P.join('; ') : ''; }
    const C = s.cleared || [];
    if ($id('cleared-box')) {
      $id('cleared-box').hidden = !C.length;
      $id('cleared').innerHTML = C.map(e => `<li><span class="when">${esc(fmtSpan(e.first, e.last))}</span> · ${e.what==='machine'?'':esc(e.what)+': '}${esc(e.text)}${e.what!=='machine' && e.n>1 ? ` · ${e.n} checks` : ''}</li>`).join('');
    }
    drawSystem(s.system);
    drawDisk(s.system.disk);
    drawSections(s.sections||[]);
    if (typeof drawQuota === 'function') drawQuota();
    if (typeof drawGlance === 'function') { drawGlance(); drawNeeds(); }
    if (typeof drawFinishedLinks === 'function') drawFinishedLinks();
  });
}

function procTable(rows, withCwd){
  if (!rows.length) return '';
  return '<div class="run"><span class="h">Process</span><span class="h r">CPU</span><span class="h r" title="Private memory (Pss_Anon)">Own memory</span><span class="h r sh" title="Memory-mapped files such as .olean (Pss_File): shared page cache">+ shared files</span><span class="h r">Running for</span>' +
    rows.map(r => `<span>${esc(r.what)}</span><span class="r">${r.cores==null?'':(r.cores*100).toFixed(0)+'%'}</span><span class="r">${r.own_gib.toFixed(1)} GiB</span><span class="r sh">${r.shared_gib.toFixed(1)} GiB</span><span class="r">${r.age_min<90?r.age_min.toFixed(0)+' min':(r.age_min/60).toFixed(1)+' h'}</span>` +
      (withCwd && r.cwd ? `<span class="c">pid ${r.pid} in ${esc(r.cwd)}</span>` : '')).join('') + '</div>';
}

const secCharts = {}, secZoom = {};   // a progress chart keeps its zoom across refreshes
function drawSections(all){
  const box = $id('sections');
  if (!box) return;
  const secs = all.filter(s => isLive(s) === (VIEW === 'main'));
  for (const k in secCharts) {
    const u = secCharts[k], xs = u.data[0];
    if (xs.length && (u.scales.x.min > xs[0] + 1 || u.scales.x.max < xs[xs.length-1] - 1)) secZoom[k] = {min: u.scales.x.min, max: u.scales.x.max};
    else delete secZoom[k];
    u.destroy(); delete secCharts[k];
  }
  if (!secs.length){ box.innerHTML = `<section class="card"><p class="empty">${VIEW === 'main' ? 'No work in progress has a section right now.' : 'Nothing has finished in the last 24 hours.'}</p></section>`; return; }
  box.innerHTML = secs.map(s => {
    const ph = s.phases||[];
    const cv = carveView(s);
    const meta = [cv.worker, cv.owner ?? (s.owner?esc(s.owner):''), 'updated '+ago(s.age_secs), ...(s.links||[]).map(l=>`<a href="${esc(l.url)}">${esc(cv.relabel(l))}</a>`)].filter(Boolean).join(' · ');
    return `<section class="card" id="sec-${esc(s.id)}" aria-labelledby="h-${esc(s.id)}">
      <h2 id="h-${esc(s.id)}">${esc(cv.title)}<span class="st ${s.state}">${s.state.toUpperCase()}</span>${s.stale?`<span class="st stale" title="No update for ${Math.round(s.age_secs/60)} min: has its producer stopped?">STALE</span>`:''}</h2>
      <p class="meta">${meta}</p>
      ${s.note?`<p class="chart-sub">${esc(s.note)}</p>`:''}
      ${(s.alerts||[]).length?`<ul class="salerts">${s.alerts.map(a=>`<li>${esc(a)}</li>`).join('')}</ul>`:''}
      ${s.superseded?`<div class="swarns"><p>Superseded: ${esc(s.superseded.why)}${s.superseded.by?` · <a href="#sec-${esc(s.superseded.by)}">its section</a> · <a href="/page/agent.html?name=${encodeURIComponent(s.superseded.by)}">its log</a>`:''}</p>${(s.warnings||[]).length?`<ul>${s.warnings.map(a=>`<li>${esc(a)}</li>`).join('')}</ul>`:''}</div>`:''}
      <div class="phases">${ph.map(p => phaseRow(s, p)).join('')}</div>
      ${(s.running||[]).length?'<h3 style="margin-top:10px">Running now</h3>'+procTable(s.running, false):''}
      <div class="chartbox"></div></section>`; }).join('');
  for (const s of secs) {
    const card = document.getElementById('sec-'+s.id);
    card.querySelectorAll('.ph').forEach(el => el.onclick = () => { selected[s.id] = el.dataset.name; keepScroll(() => drawSections(last.sections)); });
    sectionChart(s, card);
  }
}

// A carve's section is written by its driver, named after the batch whose job dir holds the carve. A retry
// batch resumes an earlier batch's carve, so the page titles it by its module and names the batch working on
// it now (from agents.json: a running agent whose card lists this section).
function carveView(s){
  const plain = {title: s.title, worker: '', owner: null, relabel: l => l.label};
  if (!s.id.startsWith('carve-')) return plain;
  const m = /^(?:(\S+) carve |Carve )(\S+): (.+)$/.exec(s.title);
  if (!m) return plain;
  const [, starter, dir, mod] = m;
  const A = typeof agentsData !== 'undefined' && agentsData ? agentsData.running : [];
  const now = A.filter(a => a.phases && a.phases.dirs.some(d => d.section === s.id)).map(a => a.name);
  const link = n => `<a href="/page/agent.html?name=${encodeURIComponent(n)}">${esc(n)}</a>`;
  return {
    title: `Carve of ${mod}`,
    worker: (now.length ? `worked by ${now.map(link).join(', ')} · ` : '') + `in <code>${esc(dir)}</code>` +
            (starter && !now.includes(starter) ? `, started by ${esc(starter)}` : ''),
    owner: esc((s.owner || '').replace(/^queue worker \S+, /, '')),
    relabel: l => l.label === 'worker log' && starter ? `log of ${starter}` + (now.includes(starter) ? '' : ' (started the carve)') : l.label,
  };
}

function phaseRow(s, p){
  const pct = p.total ? Math.min(100, 100*p.done/p.total) : 0;
  const extra = p.state==='running' && p.rate_per_min ? ` · ${p.rate_per_min}/min${p.eta?' · ETA '+fmtAt(p.eta):''}` : '';
  return `<div class="ph${chosenPhase(s)===p.name?' sel':''}" data-name="${esc(p.name)}" title="Click to chart this phase">
    <span class="n">${esc(p.name)}<span class="st ${p.state}">${p.state.toUpperCase()}</span></span>
    <span class="v">${p.done.toLocaleString()} / ${p.total.toLocaleString()} (${pct.toFixed(0)}%)${extra}</span>
    <div class="bar" role="progressbar" aria-label="${esc(p.name)}" aria-valuenow="${pct.toFixed(0)}" aria-valuemin="0" aria-valuemax="100"><i style="width:${pct}%"></i></div>
    ${p.note?`<span class="note">${esc(p.note)}</span>`:''}</div>`;
}

function chosenPhase(s){
  const H = s.history||{}, ph = (s.phases||[]).filter(p => (H[p.name]||[]).length > 1);
  if (selected[s.id] && ph.some(p=>p.name===selected[s.id])) return selected[s.id];
  const p = ph.find(p=>p.state==='running') || ph[ph.length-1];
  return p ? p.name : null;
}

function sectionChart(s, card){
  const name = chosenPhase(s); if (!name) return;
  const p = s.phases.find(x=>x.name===name), h = s.history[name];
  const box = card.querySelector('.chartbox');
  box.innerHTML = `<h3 style="margin-top:12px">${esc(name)}: progress over time</h3><p class="chart-sub">${p.done.toLocaleString()} of ${p.total.toLocaleString()} · drag to zoom, double-click to reset</p><div></div>`;
  const el = box.querySelector('div');
  const opts = {
    width: Math.max(260, el.clientWidth), height: 220,
    tzDate: ts => uPlot.tzDate(new Date(ts*1e3), TZ),
    cursor: {y: false, drag: {x: true, y: false}, points: {size: 6}},
    legend: {live: true},
    scales: {x: {time: true}, y: {range: [0, p.total || 1]}},
    axes: [{stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {stroke: css('--grid')}, font: '11px system-ui', values: xTicks, space: 60},
           {stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {show: false}, font: '11px system-ui', size: 50}],
    series: [{value: (u, v, si, idx) => idx == null ? 'latest' : fmtAt(v)},
             {label: name, stroke: css('--series-1'), width: 2,
              value: (u, v, si, idx) => { const r = idx == null ? u.data[1][lastIdx(u)] : v; return r == null ? '—' : r.toLocaleString() + ' of ' + p.total.toLocaleString(); }}],
  };
  // a step line: the count holds until the next change
  opts.series[1].paths = uPlot.paths.stepped({align: 1});
  secCharts[s.id] = new uPlot(opts, [h.map(x => x[0]), h.map(x => x[1])], el);
  if (secZoom[s.id]) secCharts[s.id].setScale('x', secZoom[s.id]);
}

// the main page's links to the Finished page: a nav entry and a line under the work in progress, with counts
function drawFinishedLinks(){
  if (VIEW !== 'main') return;
  const secs = last ? (last.sections || []).filter(s => !isLive(s)).length : 0;
  const ags = typeof agentsData !== 'undefined' && agentsData ? agentsData.recent.length : 0;
  const ms = typeof missionsData !== 'undefined' && missionsData ? (missionsData.missions || []).filter(m => m.complete).length : 0;
  const parts = [ags && `${ags} headless agent${ags > 1 ? 's' : ''}`, secs && `${secs} work section${secs > 1 ? 's' : ''}`, ms && `${ms} mission${ms > 1 ? 's' : ''}`].filter(Boolean);
  const nav = $id('nav-done'); if (nav) nav.textContent = `Finished (${ags + secs + ms})`;
  const el = $id('done-link');
  if (el) el.innerHTML = parts.length ? `<a href="/page/done.html">Finished in the last 24 h: ${parts.join(', ')} →</a>` : 'Nothing finished in the last 24 h.';
}

load(); setInterval(load, 30000);
