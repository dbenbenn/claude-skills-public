# Claude Code skills

[Claude Code](https://claude.com/claude-code) skills for formalizing mathematics and
publishing it on [prove2.me](https://prove2.me), shared as-is from one person's working setup. Each subdirectory
is one skill: a `SKILL.md` with frontmatter (`name`, `description`) that Claude
loads when a task matches the description, plus any reference files it points at.

| Skill | For |
| --- | --- |
| `prove2me` | Running a formalization mission on prove2.me from a mathematics paper: the algorithm (twelve steps), the double-check list, an expansion per step, and the lessons behind them. Reference files: the upload pipeline and what silently breaks it, the measured audit evidence, and recurring Lean/Mathlib pitfalls. |

(`formalizing-a-paper`, the earlier general skill for a faithful Lean development, is folded
into `prove2me`; its fidelity, gap and bookkeeping rules live there now.)

## Using these on a machine

Personal skills live in `~/.claude/skills/`, so either clone this repository
there:

```
git clone https://github.com/dbenbenn/claude-skills-public.git ~/.claude/skills
```

or clone it elsewhere and symlink the individual skills:

```
ln -s ~/src/claude-skills-public/prove2me ~/.claude/skills/prove2me
```

A skill scoped to one project goes in that project's `.claude/skills/` instead,
where it is versioned with the code and shared with anyone who clones it.

The `prove2me` skill's `scripts/` expect the prove2.me Lean workspace at
`~/claude/prove2me_workspace` or `~/prove2me_workspace`; set `P2M_WORKSPACE` otherwise.
They are written for the workflow described in the skill and carry no credentials — the
API helper reads the workspace's own `credentials.json`.

## Lessons learned

Distilled from three prove2.me missions —
[Brin–Squier's PLF(ℝ)](https://prove2.me/missions/Brin%E2%80%93Squier%3A%20the%20group%20of%20piecewise-linear%20homeomorphisms%20of%20the%20line%20with%20finitely%20many%20breakpoints%20has%20no%20free%20subgroup%20of%20rank%20greater%20than%20one),
Thompson's group F after Cannon–Floyd–Parry
([§1 and §4](https://prove2.me/missions/Cannon%E2%80%93Floyd%E2%80%93Parry%3A%20Thompson%27s%20group%20F%20and%20the%20simplicity%20of%20its%20commutator%20subgroup),
[§2](https://prove2.me/missions/Cannon-Floyd-Parry%3A%20tree%20diagrams%20and%20the%20normal%20form%20for%20Thompson%27s%20group%20F)),
and a quadratic-forms mission — and one abandoned one. Each item is a
summary; the skill files hold the procedure and the measurements.

**1. Every description gets a blind read-back before it is published, and the read-back is
two artifacts, not one.** Hand an independent agent only the declaration, its preamble and
the definition files it imports — never the prose, the source, or your intent — and ask what
the code literally asserts. From that one blind reading, write two files: a *read-back*
(testimony, in plain mathematics, no verdicts, no Lean identifiers; it is published beside the
theorem for the field to compare against) and *captain's notes* (the conventions with
citations, the name check, the traps; for you, never published). Merging the two is the
recurring failure: the audit material is the interesting part and drifts back under the
read-back's name. Measured over 277 descriptions: 4% defective when written against a source
sentence, 32% for research code — and rereading your own prose did not help, because a
description and its author's understanding go wrong together. Never tell an auditor a
convention (composition order, what a bracket expands to): six of thirteen quoted the supplied
convention back verbatim and none cited a source. Let them read the libraries and require a
citation per convention instead. Details: `prove2me/SKILL.md` §"A description is not
publishable until someone blind-reads it" and §"The read-back is a published artifact";
the brief itself is `prove2me/scripts/readback-brief.md`.

**2. The audit spiral, and how to stop it.** More correctness auditing cannot fix what
correctness auditing causes: each round finds a real imprecision, the cheapest repair is an
added qualifying sentence, and after five rounds the passage is entirely true and unreadable.
The tell is corrective voice ("A caution about…", "Note that…") warning the reader off
mistakes only the author made. The one-number gate: **if the round grew the document, the
round failed**, however right each fix was. Make the response to a finding an explicit choice
among six — delete, correct, relocate, accept-as-imprecise, decline, restructure — and reach
for "accept" more than feels natural: precision has a home, usually downstream, and a
description may be looser than a milestone, which may be looser than the Lean. After three
rounds of patches on one passage, rewrite it whole. §"Accretion, and how to measure it" and
§"Responding to a finding".

**3. Repairs need their own audit, or the cascade never converges.** Four consecutive rounds
each found about twenty defects because the repair rate and the introduction rate cancelled.
Propose edits without applying them, verify each in full-field context (never a diff hunk),
re-audit every amendment as new text, gate mechanically on "the text audited is the text
applied", and terminate a patch only when a fresh auditor accepts it unchanged. §"Auditing a
fix is a separate job".

**4. Four audit axes, four separate passes.** Against the source, against a reader, against the
platform's rules, and against your own fixes. A pass briefed to do two of these does neither.
Ten source passes declared one mission clean; a single readability pass then returned 26
findings, and fixing them introduced two new false claims. §"Auditing".

**5. The variant trap.** The theorem a development proves is shaped by what its proof needs;
the theorem the source states is shaped by what reads well. They differ more often than not,
and the milestone gets linked to the wrong one. Read the cited proposition, not the source's
summarizing sentence, before publishing a statement — and audit titles as claims: a
substituted verb or a hyphenated adjective can turn a theorem vacuous. A name that needs a
caution is the wrong name, and names freeze at Submit. §"The variant trap" and §"Titles are
claims".

**6. Know exactly what is irreversible.** On the platform, `theorem_name`, `formal_statement`,
`preamble` and definition code freeze at publish; titles, prose, sources and explanations stay
editable forever. So get the *statement* right before publishing, not the proof, verify
mechanically that the published text equals the repo's, and never probe a write endpoint
against live prose. §"The one irreversible thing".

**7. Re-check the library during a long mission.** A draft that stays open for days can have
its goal proved by someone else meanwhile; one proposal lost its entire theorem that way while
its prose was being polished. One search at the start of every session, and again immediately
before Submit.

**8. Sweep date-dependent claims separately.** A source check cannot catch a sentence that has
gone stale since the paper was written: six audits against a 1985 source missed a claim false
since 2002. "Still open", "remains", "the standard test case", and every claim about what a
library lacks need a check against the present, not the paper.

**9. Version-control the mission record, and render it from the live API.** Read-backs of
milestones added after launch exist nowhere but your repo. The proposal snapshot freezes at
submit and drifts from the live mission, so a renderer fed the proposal shows stale prose.
Keep audit inputs as read-only evidence, never bulk-edit them, and do not write DOIs from
memory — five remembered DOI patterns were all wrong.

**10. A solution may import the mission's definitions and any platform theorem, never another
solution.** Imports that are all Proved give `ACCEPTED`; an import that is still Open gives
`SKETCH_ACCEPTED`, a reduction recorded in the decomposition tree whose target auto-resolves when
the leaves are proved. To ship a full proof of a milestone whose inputs are still Open, the
development lives as modules concatenated per submission (`prove2me/scripts/merge.py`). The
concatenation has failure modes that compile locally and fail on the verifier — a dropped
duplicate that swallows a file's closing `end`, a stray `theorem solution` in a module — and
the script now refuses both.

**11. Formalizing the paper, not just its theorems.** Reread the source before every numbered
result and before acting on any audit finding; recollection decays silently. Follow the paper's
proof and depart only when it has a gap, because proofs that mirror the paper certify the
paper, while proofs by other routes certify only the statements. Fidelity is about statements:
the paper's constants, generality and definitions, not a convenient stronger or weaker form.
When the paper has a gap, the new mathematics lives in its own file that the certification
must not depend on. `prove2me/SKILL.md`, *Expansion 3* and *Reading and bookkeeping habits*.

**12. Milestones are an attack path, not a coverage index.** An unlinked milestone says
"formalize this"; never use one to record something out of scope. Scope boundaries belong in
the description. When a milestone is too big, publish its steps as milestones of their own.
