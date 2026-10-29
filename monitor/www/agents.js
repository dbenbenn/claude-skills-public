// Agents view and quota charts for index.html. Globals used: esc, fmtAt, ago, css, uPlot, TZ, xTicks, last.
let agentsData = null;
const sparkSvg = (series, w=110, h=24) => {
  if (!series || series.length < 2) return '';
  const t0 = series[0][0], t1 = series[series.length-1][0], hi = Math.max(...series.map(p=>p[1])) || 1;
  const pts = series.map(p => `${((p[0]-t0)/Math.max(1,t1-t0)*(w-2)+1).toFixed(1)},${(h-1-(p[1]/hi)*(h-2)).toFixed(1)}`).join(' ');
  return `<svg class="spark" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" role="img" aria-label="cost over time"><polyline points="${pts}"/></svg>`;
};
const fmtUsd = c => c == null ? '—' : '$' + (c >= 100 ? c.toFixed(0) : c.toFixed(2));
const shortModel = m => (m || '').replace(/^claude-/, '');

function stagesHtml(d){
  const items = d.total != null ? `<span class="items">${d.live} / ${d.total} items live</span>` : '';
  return `<div class="pl"><span class="lab">${esc(d.name)}</span><div class="stages" role="list">` +
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
  document.getElementById('agents-sub').textContent = `${A.running.length} running · ${A.recent.length} finished in 24 h${A.hidden ? ' · ' + A.hidden + ' older hidden' : ''} · cost is list price (estimate until the run ends)`;
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
  const now = last.updated, rows = q.filter(r => r[0] >= now - spanSecs);
  if (!rows.length) { el.innerHTML = '<p class="empty">No quota data yet: the sampler reads rate-limit records from the agents\' transcripts.</p>'; return; }
  el.innerHTML = '';
  const newest = rows[rows.length-1], resetCol = col + 1;
  const resets = [...new Set(q.map(r => r[resetCol]))].filter(t => t > now - spanSecs);
  const next = newest[resetCol];
  const xmax = Math.max(now, next), xmin = xmax - spanSecs;
  const xs = rows.map(r => r[0]), ys = rows.map(r => r[col]);
  if (xs[xs.length-1] < now) { xs.push(now); ys.push(ys[ys.length-1]); }
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
  else sub.textContent = `5-hour window ${n[1].toFixed(0)}% used, resets ${fmtAt(n[2])} · 7-day window ${n[3].toFixed(0)}% used, resets ${fmtAt(n[4])} · newest record across the agents' transcripts (last sample ${ago(Math.round(last.updated - n[0]))})`;
  quotaChart('c-q5', 1, 48*3600, '5-hour window');
  quotaChart('c-q7', 3, 7*86400, '7-day window');
}

loadAgents(); setInterval(loadAgents, 15000);
