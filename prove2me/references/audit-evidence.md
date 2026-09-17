# Audit evidence

Measured results behind the rules in `SKILL.md`. Read this when you want to know how much a
check is worth, or when you are tempted to skip one. The rules themselves are in SKILL.md;
nothing here is actionable on its own.

## Blind read-back: defect rates by how the description was written

One mission, four rounds, 277 descriptions.

| set | defect rate |
| --- | --- |
| paper-certifying, written against the source | 4% |
| paper-certifying, written earlier without a source check | 11% |
| research code, no source to anchor against | 29% |
| research code, written minutes after reading the statement | **32%** |

Writing the description immediately after reading the Lean did not help — it was the worst
set. Rereading cannot catch an error where your description and your understanding are wrong
together. Across the four rounds this found 32 real defects.

## Copying a sibling: the four failure shapes

The two in SKILL.md, plus:

- A hypothesis asserted to be "the same as" a sibling's when the sibling carries an extra
  global hypothesis this one does not.
- A definition described using a *neighbouring* definition's shape — `VisibleDense` written as
  though it were `LocallyDominated`.

And the first one in full: `lintegral_far_weight_le` vs `_prime` — the twin's display formula
carried over unchanged, differing in which coordinate carries the weight. No symmetry is
assumed, so they are different theorems, and the prose contradicted its own display.

## The six-pass fix cascade

One mission's prose, audited after every repair round. False claims found per pass:

| pass | target | false claims |
|---|---|---|
| 1 | original text | 7 |
| 2 | round-1 fixes | 2 |
| 3 | round-2 fixes | 1 |
| 4 | round-3 fixes | 1 |
| 5 | round-4 fixes | 1 |
| 6 | round-5 fixes | **0** |

11 false claims total, **4 introduced by the fixes themselves**. The loop does converge, but
only if each round gets smaller and the edits stay surgical. In an earlier mission where
rounds stayed the same size, four consecutive audits each found ~20 defects and never
converged: the repair rate and the introduction rate were cancelling.

## Structural de-accretion: what one pass recovered

Applying "one home per fact" across 20 fields of one proposal:

| | before | after |
|---|---|---|
| words in those fields | 3,356 | 2,404 |
| duplicated 10-word span pairs | 6 | 3 (all deliberate) |
| appeals to unnamed audits | 9 | 0 |
| worst milestone route | 330-word paragraph | 6 numbered steps |
| worst NL statement | 298 w, 49.7 w/sentence | 81 w |

Two sections had earlier been cut 199 → 73 and 702 → 401 words. In the 702-word one, ~35%
re-narrated a milestone's route (spans identical for 22 and 14 consecutive words) and ~38% was
corrective voice.

## Read-backs that were not read-backs

Thirteen items, briefed as blind audits and filed in the `readback` field: 11 carried a
TRUE/FALSE verdict, 4 said "Name fits", most sketched a proof, all 12 theorem ones ended with
a footnote about what the auditor had verified first, and one never stated its theorem at all.
Re-running them blind, given only the declaration, its preamble and `mission_auditor.md`,
produced testimony that met the spec — and surfaced three properties of the mission's own
definitions that no intent-aware pass had stated.

## Contaminating the read-back brief with a convention

One brief told auditors the composition convention `(f * g) x = f (g x)` and what the commutator
bracket expands to. Across thirteen testimonies:

| | count |
|---|---|
| quoted the supplied convention back verbatim | 6 of 13 |
| cited a source for it | **0 of 13** |

Both supplied conventions were in fact correct, verified afterwards at
`Mathlib/Algebra/Order/Group/End.lean:76,87` and `Algebra/Group/Commutator.lean:29`. That is the
point: the check was not a check, and had either been wrong, all thirteen would have agreed with
the captain and the audit would have certified the error.

Re-run with no conventions supplied, the libraries readable, and a citation required per
convention, the same thirteen cited 5–8 source files each, confirmed instances with `#synth`,
`pp.explicit` and `rfl` probes rather than trusting declarations, and left nothing material
unsettled. Facts the contaminated set had not produced:

- `List.prod` folds right, so the first list entry is the outermost map;
- one statement's right-hand side is a union of *open* supports, not of closures;
- "slope one at each end" says *agrees with a translation*, not *is the identity* — the
  trivializing misreading the mission's own description existed to rule out;
- a bare `commutator` could bind to `_root_.commutator` or to `Subgroup.commutator`, settled by
  `rfl`.

**The control.** A pre-launch statement whose read-back the platform holds immutably from the
contaminated era was read back again under the clean brief. It is the conjugation identity, where
composition order decides whether the answer is `f '' supp g` or `f⁻¹ '' supp g`. The two agree,
so the contaminated set was substantively sound and nothing published needed revisiting. Running
that control is what turned "probably fine" into "checked".

## Leaks through the brief and the prompt

Three leaks in one brief, found in this order:

1. **The rationale, inside the brief.** A blockquote at the top explained why never to supply a
   convention — and quoted the convention while doing it. Markdown blockquotes are not comments;
   thirteen auditors were launched against it before the owner asked whether those paragraphs
   were comments. Fix: doctrine in a sibling captain-only file, and the prompt names the exact
   files the auditor may open.
2. **Enumerating which conventions to check** (composition order, bracket, fold direction) steers
   attention to that development's particular traps. Fix: name kinds of Lean notation generally.
   The generic version immediately earned it — "or a same-named declaration from another
   namespace" is what surfaced the `commutator` resolution hazard above.
3. **An example citation carrying a real file and line.** The placeholder in the brief used `:76`,
   which is the actual line of the group instance.

**Absolute paths in the prompt reach the published testimony.** Auditors cite the paths they are
handed: 10 of 13 testimonies contained at least one, 15 in total, including a `lakefile.lean` and
a probe file inside the session's own job scratch directory. Cosmetic on a live mission, where
post-launch read-backs are local-only; permanent on a draft, where a submitted item's `readback`
is published for good and an absolute path is both a home-directory leak and a citation nobody
else can resolve. Fix: name one working directory, express everything relative to it, and require
library-relative citations plus the library revision, since line numbers drift.

**Auditors leave litter.** Several reported cleaning up their Lean probe files; thirteen were left
in the shared workspace scratch directory and had to be removed by hand. Name a probe directory
in the brief, require deletion, and check afterwards.

## Two discrepancies recorded rather than fixed

Both illustrate the same rule: a read-back is testimony, so the fix goes in the brief and the
discrepancy goes in the record.

- **Heading depth.** Nine of thirteen testimonies headed their sections `##`, four `###`, because
  the brief listed the section names beneath its own `## Write these four sections` heading. Not
  normalized: a cosmetic edit to testimony is indistinguishable downstream from a substantive one.
  Note the renderer embeds testimony verbatim, so the `##` files render as siblings of the
  read-back label rather than children — byte-fidelity was preferred to tidy rendering.
- **Absolute paths**, as above: 15 across 10 files, left in place for the same reason.

## Quotation misattachment, all three rounds

Three consecutive fix rounds, each attaching an exact quotation to the wrong noun: a remark about
a *result* hung on a *proof*; an author's "we follow…" reattributed to "his proof"; adjectives
describing one author's groups stretched over a later author's. The words were verbatim every
time — only the grammatical subject was wrong, which is why a quote-accuracy check passes it.

## Isolating an auditor: what it buys, measured

Container and namespace isolation were both unavailable (no `docker` group, no password-less
`sudo`, `unshare --map-root-user` refused writing `uid_map`), and a Claude Code subagent cannot
be containerized regardless — its file tools run outside any container, so isolation buys scratch
hygiene, not blindness. Staging each auditor in a directory holding only the brief, its task
files, a library symlink, a `probe` wrapper and an empty `scratch/` was the available substitute.

Same statement, same brief, sealed versus unsealed:

| | unsealed | sealed |
|---|---|---|
| absolute paths in the testimony | 2 | **0** |
| probe files left in the shared workspace | several | **0** |
| probe files left in its own scratch | — | 5, discarded at teardown |
| library source files cited | 5 | 5 |

Quality held; hygiene went to zero. Sealing also nearly shipped a regression — the staged
directory is not a lake project, so probes could not elaborate until a wrapper was added, and
elaborated probes are where the best testimony comes from.

The sealed auditor additionally reported that the definition file's doc comments assert side
claims it "neither used nor checked" — the unaudited surface noted in SKILL.md. Plausibly it read
those two files harder because they were the only two it had.

## A DOI you remembered is a DOI you invented

On the Cannon–Floyd–Parry description, five DOIs were written into the reference list from
remembered patterns — `10.1215/ijm/…` for Illinois J. Math., `10.1007/BF…` for a 1985
Inventiones paper, `10.4064/fm-13-1-73-116` for a 1929 Fundamenta paper. All five happened to
resolve to the right articles. That is the dangerous outcome: it trains the habit.

These identifiers are structured enough to guess and opaque enough that a wrong guess is
invisible. A fabricated DOI that resolves to *some* paper looks exactly like a correct one in
the rendered description, and the failure surfaces only when a reader clicks it.

Resolve before writing, not after:

```bash
curl -sL -H "Accept: application/vnd.citationstyles.csl+json" "https://doi.org/$DOI"
```

and check the returned author, title, container title, volume and year against the entry you
meant to write. For sources with no DOI (conference proceedings, older volumes), cite the
publisher's own archive and check it returns a 200 and the right content type — an inline link
to a bookstore page in the same description turned out to 403.

The related trap: page ranges. Secondary sources gave Olshanskii's ICM paper as pp. 415–423,
the source's own printed bibliography as 415–424. Where the two disagree and the source is in
hand, use the source and say in the audit that you did.
