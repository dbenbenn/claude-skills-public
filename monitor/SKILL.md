---
name: monitor
description: The machine's monitoring page at http://<hostname>:8765/ (http://nixos:8765/ on dbenbenn's NixOS box) — system resources (memory, CPU, load, stall pressure, Lean processes) on top, then one section per piece of work in progress. Use whenever you start background or long-running work on the machine (a publisher, a batch of builds or provers, a watcher, anything expected to run more than about 15 minutes or past the end of your turn) so it publishes its progress in its own section; also when asked about the monitoring page, the machine's load or memory, or why the machine feels slow.
---

# The monitoring page

http://nixos:8765/ (the machine's hostname, port 8765; it was http://careyaibox:8765/ until the
move to the NixOS box on 2026-10-23) is dbenbenn's one place to see what the machine is doing. On top: the whole
machine's memory and CPU (split into Lean, each section's own processes, and the rest), load, kernel
stall pressure, every Lean/lake process with its working directory, and a red banner for machine trouble.
Below: **one section per piece of work**, written by whoever runs that work.

It is one process, `monitor.py`, run as a service that starts at boot and runs as dbenbenn. On the
NixOS box that is the system unit `monitor.service`, declared in `/etc/nixos/configuration.nix`
(`systemd.services.monitor`, `User = "dbenbenn"`); on a conventional distro, `monitor.service` in this
folder works as a systemd user unit with linger on. It samples every 30 s, keeps 48 h, and serves the
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
| `processes` | `[{label, match}]`: a Python regex searched in each process's command line. Matching processes count as this section in the memory and CPU charts and are listed under it. Lean and lake always count as Lean |
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
`{t, total, mem: {group: GiB}, cpu: {group: cores}, load1}`; `system.psi` rows `[t, cpu some, memory
some, memory full, io some, io full]` (avg10, %); `system.lean`; and `sections` with history, rates
and ETAs. The top banner is for machine trouble only (dbenbenn 2026-10-18): memory full > 5%, I/O full >
20%, CPU some > 50%, less than 4 GiB available, and Lean health flags from `lean-health.timer` (last
24 h). Project alerts and STALE badges stay in their sections; unreadable section files are listed
under the sections (`problems` in status.json).

## Changing the monitor

The code is `monitor.py` (sampling, sections, history, the HTTP server), `section.py` (producer
library and CLI) and `www/index.html` (the page, read fresh on every request, so page edits need no
restart). Charts use uPlot 1.6.30 (MIT), vendored in `www/vendor/` and served by the monitor itself so
the page needs no internet; range buttons, drag-to-zoom and a synced cursor are wired in the page.
To look at the page headless, use Playwright's Chromium; on careyaibox (Ubuntu) it needed four libraries
the machine lacked (libatk1.0-0t64, libatk-bridge2.0-0t64, libxdamage1, libatspi2.0-0t64), fetched with
`apt-get download`, unpacked with `dpkg-deb -x`, and found through `LD_LIBRARY_PATH`; on NixOS ask
dbenbenn for a `playwright-driver.browsers` package instead. Tests: `python3 -m pytest -q ~/.claude/skills/monitor/tests`.
After changing `monitor.py` the service must restart: on the NixOS box it is a system unit, so that is
`sudo systemctl restart monitor`, which dbenbenn runs (ask); with the user unit elsewhere it is
`systemctl --user restart monitor`. Commit and push this skill (claude-skills-public) in the same turn.
