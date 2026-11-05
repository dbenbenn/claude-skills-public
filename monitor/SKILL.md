---
name: monitor
description: The machine's monitoring page at http://<hostname>:8765/ (on dbenbenn's NixOS box https://nixos.taila1b358.ts.net/ through tailscale serve; 8765 itself is firewalled there) — system resources (memory, CPU, load, stall pressure, Lean processes) on top, then one section per piece of work in progress. Use whenever you start background or long-running work on the machine (a publisher, a batch of builds or provers, a watcher, anything expected to run more than about 15 minutes or past the end of your turn) so it publishes its progress in its own section; also when asked about the monitoring page, the machine's load or memory, or why the machine feels slow.
---

# The monitoring page

https://nixos.taila1b358.ts.net/ (`tailscale serve` of port 8765 with a Let's Encrypt certificate Tailscale renews; since 2026-10-29 the firewall closes 8765 to other machines, so http://nixos:8765/ no longer works, while http://localhost:8765/ on the box itself does) is dbenbenn's one place to see what the machine is doing. On top: the whole
machine's memory and CPU (split into four categories, below), load, kernel
stall pressure, every Lean/lake process with its working directory, and a red banner for machine trouble.
Below: **one section per piece of work**, written by whoever runs that work.

It is one process, `monitor.py`, run as a service that starts at boot and runs as dbenbenn: the NixOS
system unit `monitor.service`, declared in `~/nixos-config/configuration.nix`
(`systemd.services.monitor`, `User = "dbenbenn"`). It samples every 30 s, keeps 48 h, and serves the
page itself. No Claude involvement.

## Publishing your work's section

**When:** any background work that dbenbenn might want to watch: it runs unattended, or for more than
about 15 minutes, or past the end of your turn. Set the section up when the work starts, not at
the end.

A section is one JSON file, `~/claude/monitor/sections/<id>.json`. You only report current counts:
the monitor keeps each phase's history and works out the rate, the ETA and a chart.

From a shell, which suits a Claude session updating as it goes. `set` merges into the existing file
and matches phases by name:

```
S=~/.claude/skills/monitor/section.py
python3 $S set artin-l63 --title 'Artin: Lemma 6.3 provers' --owner 'Claude session 9a003216' \
    --phase 'Provers finished=2/6' --process 'prover=python3 .*artin.*prove' --heartbeat 900
python3 $S set artin-l63 --phase 'Provers finished=3/6:running:L3Z_Lower closed'
python3 $S set artin-l63 --alert 'NEEDS A PERSON: Prop 8.2 statement looks false'
python3 $S set artin-l63 --state done --clear-alerts
python3 $S remove artin-l63          # or let it expire: done/failed sections leave after 24 h
python3 $S list
```

From Python, which suits a long-running producer. It writes the whole section each time:

```python
sys.path.insert(0, os.path.expanduser('~/.claude/skills/monitor'))
import section
section.publish('erdos3-v2', title='Erdős 3 v2: publishing to prove2.me', state='running',
                phases=[{'name': 'Bundles', 'done': 241, 'total': 311, 'note': '9 in flight'}],
                alerts=[], processes=[{'label': 'publisher', 'match': r'python3\s+\S*split_run\.py'}],
                owner='Claude session 777b33f5', heartbeat_secs=60)
```

**Fields** (`section.validate` checks them; a bad file is listed under the sections instead of shown):

| field | meaning |
|---|---|
| `title` | the section's heading, also its name in the machine charts |
| `state` | `running`, `waiting`, `paused`, `done` or `failed` |
| `phases` | `[{name, done, total, state?, note?}]`, one progress bar each; pick one to chart by clicking it |
| `alerts` | strings that need a person, shown in red in the section. Only real stops belong here, never routine retries. The top banner is reserved for machine trouble, so it never shows these |
| `processes` | `[{label, match}]`: a Python regex searched in each process's command line. Matching processes are listed under the section (the charts use the categories below, not sections) |
| `owner`, `note`, `links` | who runs it (e.g. the Claude session id, the systemd unit); one line of context; `[{label, url}]` |
| `heartbeat_secs` | how often you update (default 300). A running or waiting section with no update for 3 heartbeats gets a STALE badge, so set it honestly: a Claude session that updates once per turn wants 900 or more |
| `expires_secs` | how long a done or failed section stays (default 86400) |

**Keeping it current when you are not there.** A Claude session's updates stop when its turn ends.
For work that outlives the turn, write a small producer that reads the work's own state files and
calls `section.publish` every 30–60 s. Run it as a systemd user unit next to the work. The Erdős 3
producer is the model: `~/claude/p2m-standalone/openai-erdos3-split-v2/progress/gen.py` with
`e3v2-gen.service`. Do not start another web server or port: there is one page.

**When the work ends:** set `--state done` (or `failed`, with an alert saying why), stop its
producer unit, and let the section expire.

## Reading it from a shell

`~/claude/monitor/state/status.json` is exactly what the page shows: `alerts`; `system.machine` rows
`{t, total, mem: {group: GiB}, cpu: {group: cores}, load1, swap, swap_total, disk}` (swap in GiB, recorded since 2026-10-30 and charted as "Swap in use"; `disk` = GiB used on /, since 2026-11-02); `system.psi` rows `[t, cpu some, memory
some, memory full, io some, io full]` (avg10, %); `system.free_gib`, `swap_free_gib`, `swap_total_gib`; `system.lean`; and `sections` with history, rates
and ETAs; `system.disk` = `{now: {used, total, free}, rows, labels, every_secs}` (the Disk card, below). The top banner is for machine trouble only (dbenbenn 2026-10-18): memory full > 5%, I/O full >
20%, CPU some > 50%, less than 4 GiB of memory and swap available together (low free RAM alone is
normal on a box where Lean may fill RAM and spill to swap), less than 20 GiB of disk free (`DISK_LOW_GIB`, since
2026-11-02), and Lean health flags from `lean-health.timer`
and lean-cap's race reports. **The banner and the red favicon show only trouble going on now**
(dbenbenn 2026-10-26): a pressure alert in the current sample; a Lean health flag that the latest check
still reports (checks run every 10 min, so it counts as current for 15); a race while both jobs still run
(`/proc/<pid>/cmdline` still names the module); an OOM kill for its first hour. Everything else from the
last 24 h is `cleared` in status.json (`{what, text, first, last, n}`, newest first), listed in grey under
"Cleared alerts" below the Lean processes. Repeats of one flag (the same text apart from its numbers;
pids kept) less than 25 min apart (10 min for pressure alerts) count as one episode, shown with its worst
reading. Pressure episodes persist across samples in `state/resources.json` (`trouble`). Project alerts
and STALE badges stay in their sections; unreadable section files are listed under the sections
(`problems` in status.json).

## Disk (2026-11-02)

Added after the disk filled on 2026-11-01 and nothing on the page said so (four agents died, the OAI queue
crash-looped for 23 h). The **Disk** card below System resources: a stacked chart of disk in use by category
with its own range (2 / 7 / 30 days; the system charts' range stops at 48 h), and a table of each category's
size and its change over 24 h and 7 days (also the chart's text view). Categories (`monitor.DISK_CATS`,
`disk_scan`): **Lean build output** (every outermost `.lake` under ~/claude except its `packages`), **Lean
libraries and toolchains** (`.lake/packages`, ~/.elan, ~/.cache/mathlib), **agent job scratch** (~/.claude/jobs),
**repos and sources** (~/claude outside `.lake`), **caches, /tmp, transcripts** (the rest of ~/.cache, /tmp,
~/.claude outside jobs); grey **Nix store, swap file and the rest** is what statvfs counts beyond them (the
32 GiB /var/lib/swapfile, /nix, other home dirs). The scan runs hourly in its own thread (`disk_loop`) with
`du -x -B1` and `find` under `ionice -c3 nice -n19` (ionice by its full NixOS path: the system unit's PATH
lacks util-linux); about 15 s and under 2% I/O pressure on this box. Rows `{t, used, total, secs, cats}` in
`state/disk.json`, 30 days. The total and free space come from statvfs every 30 s. The disk-only fifth hue
`--disk-5` is the reference palette's dark yellow step `#c98500` (validated light and dark); `--series-5`'s dark
step is above the dark lightness band and stays as it is for the swap chart.

## Headless agents, quota and logs (no tokens)

The main page has two more cards (their order is in "Page layout" below):

- **Subscription quota**: the 7-day window (last 7 days) as a step chart (the 5-hour window, not reported
  by the agents' records since 2026-10-31, was dropped from the page on 2026-11-05; status.json keeps its
  column), with reset markers (solid = past, dashed = next). The sampler (`agents.update_quota`) reads only the new
  bytes of each `~/claude/headless-agents/*/transcript.jsonl` and takes the `rate_limit_event`
  (`rate_limit_info.unifiedWindows.{five_hour,seven_day}.{utilization,resetsAt}`) from the most recently
  written file. Utilization is a 0..1 fraction there; it is stored and shown as %. The series
  (`state/quota.json`, 7 days) only moves while some agent is running.
- **Headless agents**: one card per `headless-agents/<name>/`: running first, then agents finished in the
  last 24 h. Name (links to its log), state, model, auth (subscription / API key), start-end, cost so far
  (list price, estimate until the run ends), a cost sparkline (`state/agent_costs.json`, 48 h), the last assistant text
  (`last_text.txt`) and links to its goals on prove2.me (`https://prove2.me/theorems/<id>`) taken from
  `headless-agents/queue/registry.json` (batch `name` -> `modules` -> `groups[module].goals/ids`; no lookup file
  needed). **Phases**: a bar of ten stages (fetch, port, build, graph, plan, gen, measure, prose, check,
  publish; each covers the `carve_pipeline.py` steps listed in `agents.STAGES`), current one outlined, failed
  red, plus items live/total from `run_state.json`. Carve dirs are found at `~/.claude/jobs/<agent>/**/` (depth 3)
  and `~/claude/p2m-standalone/openai-ports/<agent>/`; a queue retry also shows the carves of the earlier batches on
  its modules (registry `batches`), labelled `<earlier>/<dir>` in italics, since it resumes them (`agents.earlier_batches`;
  q141-boltzmann-retry showed "setting up" for hours while resuming `oaiq-080/bz`); no state yet shows "setting up"
  (queue agents only).
- **Queue overview** at the top of the agents card: tiles for new groups waiting, retries waiting (with retry slots
  busy), batches running, groups that need a person (attempted-open with the retry spent, no notes, or on `no_retry`;
  amber when any) and groups proved, plus expandable lists. Read from `headless-agents/queue/overview.json`, which the
  queue supervisor (`claude-private/tools/oai-queue/queue.py`, `write_overview`) rewrites every tick; `/agents.json`
  passes it through as `queue`.
- **Carve sections** `carve-<hash>` (the hash of the driver's unit `carve-<hash>`): written by the carve driver itself
  (`prove2me/p2mlib/carvemonitor.py`, a daemon thread of `carve_pipeline.py`, every 60 s and at each step boundary;
  `split_run.py --go` keeps the counts current while a background publisher outlives its driver). Phases: Steps,
  Build (modules), a running step's LeanInfo modules, Measure (items of the plan), Publish (live of the plan);
  done or failed with the stopping reason at the end. Carves on a skill snapshot from before 2026-10-30 have none
  until resumed with `--upgrade`.
- **Log viewer** `/page/agent.html?name=<agent>`: transcript.jsonl as readable events (assistant text, tool calls
  with command/description, results cut to 4 lines with expand, clock times in CEST), newest at the bottom,
  polls every 3 s from the byte offset it has, filters All / Text / Tools / Errors plus a search box, "Load
  earlier events" for the head of long transcripts.

**Routes** (all in `monitor.py`; page files under `www/` are read per request, so page changes need no restart):
`/` and `/page/<name>.html` (= `www/<name>.html`), any other `www/` path with extension .js .css .html .svg .png
.ico (plain path segments only, nothing resolving outside `www/`), `/status.json` (now with `quota.series` rows
`[t, 5h %, 5h resetsAt, 7d %, 7d resetsAt]`), `/agents.json` (running / recent / hidden; cached 5 s) and
`/agent/<name>/<file>[?from=N&max=M]` where file is one of transcript.jsonl, state.json, usage.json, meta.json,
brief.md. The agent route is read-only: the name must be a plain directory name that is not a symlink, the file
must resolve inside that directory, responses are capped at 512 KiB. For transcripts `from` is a byte offset
(negative = from the end) and the reply holds whole lines only, with `X-Start`, `X-End`, `X-Size` headers: poll
again from `X-End`. Code: `agents.py` (summary, phases, safe paths, quota); tests `test_agents.py`,
`test_server.py`.

## Page layout (2026-11-05)

dbenbenn watches the load and quota but scrolled past the charts to reach the agents and "need a
person", so the page reads top-down by what wants attention (`www/glance.js`, `www/glance.css`):

1. **Glance tiles**: memory, CPU, load, swap, stalls, disk free, 7-day quota, each a number, one line
   and a 3-hour sparkline (7 days for quota), amber or red at the banner's thresholds (disk amber
   below 40 GiB free, where the OAI queue stops); each links to its detailed chart.
2. **Needs you**: one list of everything waiting for a person: missions waiting on him or ready to
   start, section alerts (with the section's state when not running), STALE sections, unreadable
   section files, the OAI queue's need-a-person groups, and the inboxes (which had their own box
   above the nav before). "Nothing needs you right now" when empty.
3. **Missions in flight** (below).
4. **Headless agents**: queue tiles (the need-a-person tile links to Needs you), the running agents;
   the finished ones fold into a `<details>` whose open state the browser remembers.
5. The work-in-progress sections, then the detailed **System resources**, **Disk** and **Quota** cards.

**Missions in flight.** `GET /missions.json` serves `MONITOR_HOME/missions.json`, written by the mission
tracker (`~/claude/claude-private/tools/mission-tracker`, user unit `mission-tracker.service`; its README
has the steps). Each mission is a row of five steps (Submit, publish, After Submit, review, After
approval) with who each waits on, and two buttons: **Check now** (the tracker asks prove2.me) and
**Start/Retry** a Claude step (a headless agent; the page asks for confirmation). Buttons `POST /request`
`{action: check|start, key}`; the monitor only writes the request to `MONITOR_HOME/requests/` and never
runs anything itself. It accepts a request only with the header `X-Monitor-Request: 1` and a JSON
content type (a cross-site form can send neither without a preflight this server never answers), a
body of at most 1 KiB, and an `Origin`, when present, naming this host (`post_request`, tested in
`test_server.py`). The page then polls `/missions.json` until the mission's `pending.rid` matches the
id the POST returned (a phone's clock may differ from the box's).

**Finished page** `/page/done.html` (2026-11-05, dbenbenn: "move completed tasks into a linked subpage"): the
headless agents that ended in the last 24 h, the done and failed sections (they expire after a day), and the
complete missions. The main page keeps only running agents, sections that are running, waiting or paused, and
missions in progress; the nav's "Finished (N)" and a line under the sections link there. Both pages are the same
script, `www/main.js` (it was inline in index.html) with `www/main.css`, switched by `<body data-view>`; each card
draws only when its element exists. Links between them go through `hrefFor`, and every fetch and asset path is
absolute, since done.html lives under /page/.

**Scroll position.** Every redraw (status every 30 s, agents every 15 s, missions every 30 s, a phase click, a
width change) runs inside `keepScroll`: it finds the element at the top of the viewport, the nearest ancestor with
an id (agent cards are `ag-<name>`, missions `m-<key>`, sections `sec-<id>`) and the child-index path down to it,
redraws, and scrolls by however far that element moved. Native scroll anchoring is off (`overflow-anchor: none`)
so the two never correct twice. Before this (2026-11-05), a card above the reader that changed height made the
page jump, and phones, which fire `resize` when the address bar hides, redrew every chart while scrolling;
resize now redraws only on a real width change.

**Retries and their carves** (2026-11-05, after q172 MUB confused dbenbenn: "two seemingly unrelated names"). A
retry batch resumes an earlier batch's carve, whose section the driver titles after the job dir's batch. So the
page: titles every `carve-*` section "Carve of <module>" and says which running agent works on it (the agent card
that lists that section id) and which batch started it, relabelling "worker log" as that batch's log (`carveView`
in main.js); on an agent card shows only the carve rows whose section is live, folding the rest (backups such as
`before_regen`, older carves of the module) into one grey "idle" line; counts items live from the section's
Publish phase (the whole plan; run_state.json lists only what was ever queued, so q172 read "154 / 157" at 623 of
6,338); greys a stage still recorded as running after the current one (a stop cut it off); and the items-live
sparkline's tooltip says "unchanged since …" when the count has stood still for half an hour. In the carve monitor
(prove2me `p2mlib/carvemonitor.py`; a running driver keeps its snapshot's version until it restarts): a running
`gen` gets a "Gen (files written)" phase (the .lean files under out/ written since the step started, of the plan's
items), Publish is `waiting` ("paused while <step> runs") when no publisher runs and the driver is not on a publish
step, and a measure step recorded as running but later than the current step is `waiting` ("interrupted").

**Stacked-chart legends** read `u._raw`, which `upsert` (and the disk chart) refresh along with the data:
a reused chart's legend otherwise kept the values of the page's first load (2026-11-05: a tab open
since the morning showed queue workers at 1.2 GiB beside an 18 GiB band).

## Changing the monitor

The code is `monitor.py` (sampling, sections, history, the HTTP server), `section.py` (producer
library and CLI) and `www/index.html` (the page, read fresh on every request, so page edits need no
restart). Charts use uPlot 1.6.30 (MIT), vendored in `www/vendor/` and served by the monitor itself so
the page needs no internet; range buttons, drag-to-zoom and a synced cursor are wired in the page.
To look at the page headless on NixOS use `google-chrome --headless=new --no-sandbox --disable-gpu --virtual-time-budget=6000 --screenshot=…` against a throwaway instance (`MONITOR_PORT=8799 MONITOR_HOME=/tmp/monhome python3 monitor.py`; kill it afterwards, never the system unit; a page that scrolls itself may screenshot blank, use `--dump-dom` or screenshot the dumped DOM). If Playwright is ever needed, ask
dbenbenn for a `playwright-driver.browsers` package. Tests: `python3 -m pytest -q ~/.claude/skills/monitor/tests`.
After changing `monitor.py` the service must restart: `sudo systemctl restart monitor`, which dbenbenn
runs (ask). Commit and push this skill (claude-skills-public) in the same turn.

## Chart categories and inboxes (2026-10-27)

The memory and CPU charts have four fixed categories (`monitor.CATS`; one per section gave about 100
"Headless agent" entries): **Lean** (lean, lake, anything in `lean.slice`), **queue workers** (in the
`oai-queue`, `headless-*` or `carve-*` user units), **Claude sessions** (processes under an interactive
`claude`, or its versioned binary `~/.local/share/claude/versions/X`), and grey **rest of the machine**
(the remainder of what is in use). Memory is per process (Pss_Anon). CPU of Lean and the queue comes from
their cgroups' `cpu.stat` (`cgroup_usage`), which counts processes that already exited: per-process
ticks see only processes alive at two samples, so short Lean compiles were missed (3.66 cores in
`lean.slice` charted as 1.01, the rest as "rest"). History rows from before are folded into the
categories (`fold_row`).

**Inboxes.** `MONITOR_HOME/inboxes.json` lists directories whose files wait for someone:
`[{"label", "dir", "ignore": ["README.md"]}]`. The page shows each one's count, oldest age and file names
under the title (amber when anything waits), each name a link to `/inbox/<n>/<file>` (read-only, plain
names inside that directory, no symlinks). The prove2me lessons inbox is the first.
