// Agents view and quota charts for index.html. Globals used: esc, fmtAt, ago, css, uPlot, TZ, xTicks, last.
let agentsData = null;
// `top`: the value at the top edge (default the series' maximum); a progress line scaled to its total
// shows a stall as a flat line short of the top
const sparkSvg = (series, w=110, h=24, top=null, label='cost over time') => {
  if (!series || series.length < 2) return '';
  const t0 = series[0][0], t1 = series[series.length-1][0], hi = top || Math.max(...series.map(p=>p[1])) || 1;
  const pts = series.map(p => `${((p[0]-t0)/Math.max(1,t1-t0)*(w-2)+1).toFixed(1)},${(h-1-(p[1]/hi)*(h-2)).toFixed(1)}`).join(' ');
  return `<svg class="spark" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" role="img" aria-label="${esc(label)}"><polyline points="${pts}"/></svg>`;
};
// the carve's publish progress from its monitoring section's phase history (index.html's `last`)
function liveSpark(d){
  const sec = d.section && last && (last.sections || []).find(s => s.id === d.section);
  const h = sec && sec.history && sec.history['Publish (live)'];
  const ph = sec && (sec.phases || []).find(p => p.name === 'Publish (live)');
  if (!h || h.length < 2 || !ph) return '';
  // the phase counts bundles, statements and pieces of the whole plan (the card's own count, the run
  // state's bundles and pieces so far). Scaled to its own maximum: a stall shows as a flat tail
  const [t, n] = h[h.length - 1], first = h.find(p => p[1] > 0);
  const tip = `${n} of ${ph.total} bundles, statements and pieces live at ${fmtAt(t)}` +
    (first ? `; the first went live ${fmtAt(first[0])}` : '') + '. Click for the full chart';
  return `<a class="livespark" href="#h-${esc(d.section)}" title="${esc(tip)}">${sparkSvg(h, 96, 20, null, 'items live over time')}</a>`;
}
const fmtUsd = c => c == null ? '—' : '$' + (c >= 100 ? c.toFixed(0) : c.toFixed(2));
const shortModel = m => (m || '').replace(/^claude-/, '');

function stagesHtml(d){
  const items = d.total != null ? `<span class="items">${liveSpark(d)}${d.live} / ${d.total} items live</span>` : '';
  const lab = d.earlier ? `<span class="lab earlier" title="carve of the earlier batch ${esc(d.earlier)}, which this retry resumes">${esc(d.name)}</span>` : `<span class="lab">${esc(d.name)}</span>`;
  return `<div class="pl">${lab}<div class="stages" role="list">` +
    d.stages.map(s => `<i role="listitem" class="${s.status}${s.name === d.current ? ' cur' : ''}" title="${esc(s.name)}: ${s.status}">${esc(s.name)}</i>`).join('') +
    `</div>${items}</div>`;
}

function agentCard(a){
  const goals = (a.goals || []).map(g => g.url ? `<a href="${esc(g.url)}" target="_blank" rel="noopener">${esc(g.name)}</a>` : `<span>${esc(g.name)}</span>`).join('');
  const when = a.state === 'running' ? `started ${fmtAt(a.started)}` : `${a.started ? fmtAt(a.started) : ''}${a.ended ? ' → ' + fmtAt(a.ended) : ''}`;
  let ph = '';
  if (a.phases) ph = a.phases.dirs.map(stagesHtml).join('');
  else if ((a.goals || []).length) ph = '<div class="pl"><span class="lab">pipeline</span><span class="items">setting up</span></div>';
  const stCls = a.state === 'running' ? 'running' : a.state === 'done' ? 'done' : 'failed';
  return `<article class="ag">
    <div class="head"><a class="name" href="page/agent.html?name=${encodeURIComponent(a.name)}" title="Open the log">${esc(a.name)}</a>
      <span class="badge ${stCls}">${esc(String(a.state).toUpperCase())}</span>
      <span class="badge">${esc(shortModel(a.model) || '?')}</span>
      <span class="badge ${a.auth === 'key' ? 'key' : 'sub'}" title="${a.auth === 'key' ? 'API key: pays per token' : 'Claude subscription'}">${a.auth === 'key' ? 'API KEY' : 'SUBSCRIPTION'}</span>
      <span class="when">${esc(when)}</span></div>
    <div class="cost">${fmtUsd(a.cost)}<small>${a.cost_exact === false ? 'estimate' : a.budget ? 'of $' + a.budget : ''}</small></div>
    ${a.last_text ? `<div class="last" title="${esc(a.last_text)}">${esc(a.last_text)}</div>` : ''}
    ${goals ? `<div class="goals"><span>goal${a.goals.length > 1 ? 's' : ''}:</span>${goals}</div>` : ''}
    ${ph}
    ${a.cost_series && a.cost_series.length > 1 ? `<div style="grid-column:1/3">${sparkSvg(a.cost_series, 140, 22)}</div>` : ''}
  </article>`;
}

function drawAgents(){
  const box = document.getElementById('agents-box');
  if (!box || !agentsData) return;
  const A = agentsData, grp = (t, rows) => rows.length ? `<div class="agrp">${t} (${rows.length})</div>` + rows.map(agentCard).join('') : '';
  box.innerHTML = grp('Running', A.running) + grp('Finished in the last 24 h', A.recent) ||
    '<p class="empty">No headless agents are running or finished in the last 24 h.</p>';
  if (!A.running.length && !A.recent.length) box.innerHTML = '<p class="empty">No headless agents are running or finished in the last 24 h.</p>';
  drawQueue(A.queue);
  document.getElementById('agents-sub').textContent = `${A.running.length} running · ${A.recent.length} finished in 24 h${A.hidden ? ' · ' + A.hidden + ' older hidden' : ''} · cost is list price (estimate until the run ends)`;
}

// the OAI queue's overview.json: what waits to be picked up and what the queue will not retry by itself
function drawQueue(Q){
  const el = document.getElementById('queue-ov');
  if (!el) return;
  if (!Q || !Q.counts) { el.hidden = true; return; }
  el.hidden = false;
  const c = Q.counts, slots = Q.retry_slots || [0, 0];
  const tile = (n, lab, title, warn) => `<div class="tile${warn ? ' warn' : ''}" title="${esc(title)}"><div class="num">${n}</div><div class="lab">${esc(lab)}</div></div>`;
  const li = r => `<li><b>${esc(r.label)}</b> <small>${esc(r.module)}</small>` +
    (r.why ? ` · ${esc(r.why)}` : '') + (r.held_by ? ` · held by overlap with ${esc(r.held_by)}` : '') +
    (r.last_batch ? ` · last batch <a href="page/agent.html?name=${encodeURIComponent(r.last_batch)}">${esc(r.last_batch)}</a>` : '') +
    (r.goals && r.goals.length ? ` · ${r.goals.length} goal${r.goals.length > 1 ? 's' : ''} open` : '') +
    (r.resume ? `<br><small>notes: ${esc(r.resume)}</small>` : '') + '</li>';
  const opened = new Set([...el.querySelectorAll('details[open]')].map(d => d.dataset.k));
  const list = (rows, t) => rows && rows.length ? `<details data-k="${esc(t)}"${opened.has(t) ? ' open' : ''}><summary>${esc(t)} (${rows.length})</summary><ul>${rows.map(li).join('')}</ul></details>` : '';
  el.innerHTML =
    tile(c.waiting, 'new groups waiting', 'Open target groups not yet tried, in queue order') +
    tile(c.retry_waiting, `retries waiting · ${slots[0]}/${slots[1]} retry slots busy`, `Attempted groups with notes and a retry left (${Q.retry_attempts} allowed); they launch on the retry model once nothing new waits and a retry slot is free`) +
    tile(c.running, 'batches running', (Q.running || []).map(b => b.name).join(', ')) +
    tile(c.needs_person, 'need a person', 'Attempted, still Open, and the queue will not retry them by itself: retry spent, no notes, or on no_retry', c.needs_person > 0) +
    tile(c.proved, 'groups proved', 'Target groups whose goals are all Proved') +
    list(Q.needs_person, 'Need a person: the queue will not retry these by itself') +
    list(Q.retry_waiting, 'Retries waiting') + list(Q.waiting, 'New groups waiting') +
    `<p class="hint" style="grid-column:1/-1;margin:0">OAI queue ${Q.stop ? '<b>STOP set</b> · ' : ''}as of ${esc(fmtAt(Q.updated))}</p>`;
}

async function loadAgents(){
  try { agentsData = await (await fetch('agents.json?' + Date.now())).json(); } catch (e) { return; }
  drawAgents();
}

// ---- quota ----
const quotaCharts = {};
function quotaChart(id, col, spanSecs, title){
  const q = last && last.quota ? last.quota.series : [];
  const el = document.getElementById(id);
  if (quotaCharts[id]) { quotaCharts[id].destroy(); delete quotaCharts[id]; }
  // a window the records stopped reporting (the 5-hour one since 2026-10-31) is null: no line, no stale value
  const now = last.updated, rows = q.filter(r => r[0] >= now - spanSecs && r[col] != null);
  if (!rows.length) {
    const seen = q.filter(r => r[col] != null), at = seen.length ? seen[seen.length-1][0] : null;
    el.innerHTML = at ? `<p class="empty">Not reported by the agents' rate-limit records since ${esc(fmtAt(at))}.</p>`
                      : '<p class="empty">No quota data yet: the sampler reads rate-limit records from the agents\' transcripts.</p>';
    return;
  }
  el.innerHTML = '';
  const newest = rows[rows.length-1], resetCol = col + 1;
  const resets = [...new Set(q.map(r => r[resetCol]))].filter(t => t != null && t > now - spanSecs);
  const next = newest[resetCol];
  const xmax = Math.max(now, next), xmin = xmax - spanSecs;
  const xs = rows.map(r => r[0]), ys = rows.map(r => r[col]);
  // carry the latest value to now, or end on a gap (legend "—") once the window stopped being reported
  if (xs[xs.length-1] < now) { xs.push(now); ys.push(q[q.length-1][col] != null ? ys[ys.length-1] : null); }
  const opts = {
    width: Math.max(260, el.clientWidth), height: 190,
    tzDate: ts => uPlot.tzDate(new Date(ts*1e3), TZ),
    cursor: {y: false, points: {size: 6}}, legend: {live: true},
    scales: {x: {time: true, range: () => [xmin, xmax]}, y: {range: [0, 100]}},
    axes: [{stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {stroke: css('--grid')}, font: '11px system-ui', values: xTicks, space: 60},
           {stroke: css('--text-muted'), grid: {stroke: css('--grid'), width: 1}, ticks: {show: false}, font: '11px system-ui', size: 46, values: (u, v) => v.map(x => x + '%')}],
    series: [{value: (u, v, si, idx) => idx == null ? 'latest' : fmtAt(v)},
             {label: title, stroke: css('--series-1'), fill: css('--series-1') + '22', width: 2, paths: uPlot.paths.stepped({align: 1}),
              // not hovering: the latest sample, as the other charts show
              value: (u, v, si, idx) => { const r = idx == null ? u.data[1][lastIdx(u)] : v; return r == null ? '—' : r.toFixed(1) + '%'; }}],
    hooks: {draw: [u => {         // reset markers: solid for past resets, dashed for the coming one
      const c = u.ctx; c.save(); c.lineWidth = 1; c.strokeStyle = css('--text-muted'); c.fillStyle = css('--text-muted'); c.font = '11px system-ui';
      for (const t of resets) { const x = Math.round(u.valToPos(t, 'x', true)); if (x < u.bbox.left || x > u.bbox.left + u.bbox.width) continue;
        c.setLineDash(t === next ? [4, 4] : []); c.beginPath(); c.moveTo(x, u.bbox.top); c.lineTo(x, u.bbox.top + u.bbox.height); c.stroke();
        c.setLineDash([]); c.textAlign = x > u.bbox.left + u.bbox.width - 60 ? 'right' : 'left'; c.fillText('reset', x + (c.textAlign === 'left' ? 4 : -4), u.bbox.top + 12); }
      c.restore(); }]},
  };
  quotaCharts[id] = new uPlot(opts, [xs, ys], el);
}

function drawQuota(){
  if (!last) return;
  const q = last.quota ? last.quota.series : [], n = q.length ? q[q.length-1] : null;
  const sub = document.getElementById('quota-sub');
  if (!n) { sub.textContent = 'No data yet.'; }
  else {
    const since = col => { const s = q.filter(r => r[col] != null); return s.length ? ` since ${fmtAt(s[s.length-1][0])}` : ''; };
    const win = (name, p, r, col) => p == null ? `${name} not reported${since(col)}` : `${name} ${p.toFixed(0)}% used, resets ${fmtAt(r)}`;
    sub.textContent = `${win('5-hour window', n[1], n[2], 1)} · ${win('7-day window', n[3], n[4], 3)} · newest record across the agents' transcripts (last sample ${ago(Math.round(last.updated - n[0]))})`;
  }
  quotaChart('c-q5', 1, 48*3600, '5-hour window');
  quotaChart('c-q7', 3, 7*86400, '7-day window');
}

loadAgents(); setInterval(loadAgents, 15000);
