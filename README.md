# Claude Code skills

[Claude Code](https://claude.com/claude-code) skills for formalizing mathematics and
publishing it on [prove2.me](https://prove2.me), shared as-is from one person's working setup. Each subdirectory
is one skill: a `SKILL.md` with frontmatter (`name`, `description`) that Claude
loads when a task matches the description, plus any reference files it points at.

| Skill | For |
| --- | --- |
| `formalizing-a-paper` | Formalizing a mathematics paper in Lean 4 / Mathlib, and auditing an existing formalization for fidelity to its source. Includes a reference file of recurring Lean/Mathlib pitfalls. |
| `prove2me` | Publishing Lean theorems to prove2.me, curating a mission's milestones, and keeping what is published faithful to its source. Includes a reference file on the upload pipeline and what silently breaks it. |

The two are paired: `formalizing-a-paper` is the artifact (a Lean development faithful to a
source), `prove2me` is the venue (what that platform freezes, publishes and reviews). Each
`SKILL.md` points at the other, since a mission that formalizes a paper needs both.

## Using these on a machine

Personal skills live in `~/.claude/skills/`, so either clone this repository
there:

```
git clone https://github.com/dbenbenn/claude-skills-public.git ~/.claude/skills
```

or clone it elsewhere and symlink the individual skills:

```
ln -s ~/src/claude-skills-public/formalizing-a-paper ~/.claude/skills/formalizing-a-paper
```

A skill scoped to one project goes in that project's `.claude/skills/` instead,
where it is versioned with the code and shared with anyone who clones it.

The `prove2me` skill's `scripts/` expect the prove2.me Lean workspace at
`~/claude/prove2me_workspace` or `~/prove2me_workspace`; set `P2M_WORKSPACE` otherwise.
They are written for the workflow described in the skill and carry no credentials — the
API helper reads the workspace's own `credentials.json`.
