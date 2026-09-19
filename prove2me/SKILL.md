---
name: prove2me
description: Running a formalization mission on prove2.me from a mathematics paper — fetching and reading the source, designing the item list, writing definitions and statements faithful to the paper's sentences, blind read-backs, the prose, uploading a Draft, the double-check pass, Submit, solutions and post-launch care. Use when uploading a formalization to prove2.me, drafting or editing a mission proposal, linking or auditing milestones, formalizing or auditing a paper for fidelity, or answering questions about what the platform allows.
---

# prove2.me missions

The platform's own documentation is **canonical**: `references/` in the prove2.me Lean
workspace (the `prove2me_workspace` checkout; the scripts here find it through
`$P2M_WORKSPACE`) holds `mission_captain.md`, `mission_solver.md`, `missions.md`, `contribute.md`,
`discover.md`, `prove.md`, `communicate.md`, `upload_full_project.md`, `mission_auditor.md`. Read
the relevant one *before* designing anything, and quote it when it conflicts with an instruction:
the platform's semantics win, and the captain would rather hear the conflict named than have it
quietly split. Check that your copy is current; the rulebook is a date-dependent claim.

This file is in three parts. **The algorithm** is the order of work for one mission, one line per
step. **The double-check list** is step 9 written out. **The expansions** say what each step means
and record what the docs do not say, learned by doing. General Lean/Mathlib tactic pitfalls are in
`references/lean-pitfalls.md`; the upload pipeline's mechanics in `references/publishing-pipeline.md`;
the measurements behind the audit rules in `references/audit-evidence.md`.

## The algorithm

0. **Choose the mission with the human**, one paper and one goal theorem per mission; a cited
   paper is its own mission, referenced from this one. → *Expansion 0.*
1. **Fetch the source.** PDF into a private repo from the first file, extracted text for
   searching, and **rendered page images** for reading: OCR of scanned journals silently corrupts
   mathematics. → *Expansion 1.*
2. **Search the library**, on the platform and in Mathlib, for the goal, the definitions and every
   cited result; repeat at the start of each session on a Draft and immediately before Submit.
   → *Expansion 2.*
3. **Design the item list and agree it with the human before any Lean**: every numbered result,
   the unnumbered steps the proofs use, every cited external result as a milestone of its own,
   what is left out and why, the goal as the author frames it. → *Expansion 3.*
4. **Write the definitions bundle**: only the definitions the statements need, imports computed
   from use, compiled. → *Expansion 4.*
5. **Write the statements, one per source sentence and shaped like it**, each checked against the
   page image, named accurately, compiled in server shape. → *Expansion 5.*
6. **Run a blind read-back on every artifact** with `scripts/stage_auditor.py`; act on its
   `IMPORTS` lines; re-run whenever the Lean changes. → *Expansion 6.*
7. **Write the prose**: the mission description, one milestone description per milestone with
   the source's sentence quoted first, one natural-language statement per declaration.
   → *Expansion 7.*
8. **Upload the Draft with a script, verify it with another**, commit the repo. → *Expansion 8.*
9. **Run the double-check list** below, then hand the Draft to the human. → *The list.*
10. **Human audit and Submit.** Submit is asynchronous; watch the publish jobs; submit solutions as
    each statement goes Open. → *Expansion 10.*
11. **After launch**: solutions, mission metadata, live edits, the record, and the lessons back
    into this file. → *Expansion 11.*

While a task list has an unblocked item, keep going; report progress without stopping. Ask the
human only at the decision points marked in the expansions: the item list, the split into
missions, deletions, and anything the docs call irreversible.

## The double-check list

Run this on the finished Draft, against the page images and the live API, before the human reads
it. Each line names a defect that a mission of ours actually shipped or nearly shipped.

**Statements against the paper**
- Each theorem is the paper's sentence: same hypotheses (the standing assumptions of the section
  included), same conclusion, same strength of inequality (≥ is not >), same symbols. Read the
  rendered page, not the OCR text.
- Not a fragment of the sentence chosen for the proof: two halves of one proposition are one
  conjunctive theorem; a step the paper states with two hypotheses has both; a trailing "in
  particular" clause is not dropped. (*The variant trap*, below.)
- Quantifier dependence taken from the result the proof cites, not only from the sentence.
- A cited external result is stated from *its* source, in the form the paper applies, marked
  external.
- The goal is the result the author names as the paper's contribution, not the most famous
  corollary and not the easiest theorem.

**Lean hygiene**
- Every `import Definitions.*` is used; a bundle imported only transitively is not listed. The
  preamble freezes at publish and becomes a permanent dependency.
- Every statement compiles in server shape, `preamble` + `formal_statement`, with `:= by sorry`.
- Names are accurate labels (Mathlib style, `_of_` for hypotheses in binder order), ASCII, and a
  name that would need a caution is the wrong name.
- Docstrings assert nothing unaudited ("equivalent to the paper's definition").

**Read-backs**
- One per artifact, from the current Lean, with the imported bundles marked as context and not
  rendered; no Lean identifiers, no `file:line`, no naming verdict in `readback.md`; the model
  attributed correctly; never edited by hand.

**Prose**
- Each milestone description opens with the source's sentence in quotation marks and its page,
  then a marked *Route* or *External* paragraph if one earns its place. The paper's words appear
  only inside quotation marks; quotes checked against the page image, including the subject
  they predicate.
- Each natural-language statement says what the Lean says, written from that Lean and not from a
  sibling; siblings audited against each other.
- Titles start with the source index ("Lemma 3.2 — …", "Chou, p. 400 — …" for a reference
  item) and are claims, checked as such.
- The description opens "This mission formalizes <citation with DOI link>"; has Setting,
  Target, What is left out, References; display math only for a formula short enough to fit on one line, since a display
  line does not wrap (a sentence set in `$$…$$` ran off the page on the Chou draft); identifiers in
  backticks;
  no citation paragraph duplicating References; the process kept out.
- No pronoun for an author whose pronouns the paper does not establish: the surname or "the
  paper".
- No phrase lifted from the platform's rulebook ("the shape of the truth", "who cares and why"):
  the rules say what a section must contain, not how to word it, and their register is not the
  description's.
- Date-dependent claims ("still open", "not in Mathlib") checked against today, not the source.

**Platform**
- The description and every field checked against the platform's own rules read as a checklist,
  not from memory: `mission_description.md` (section structure, style, the sentences it requires,
  such as the Lean representation and ruling out a trivializing formalization),
  `mission_captain.md` (`source` with URL and page, milestone title and description conventions,
  no proof sketch in the goal), `contribute.md` (naming). Nothing else looks at this axis.
- `mission_type` is `ResearchPaper` for a paper; fields and tags set; goal marked; item order
  has definitions and references first, the goal last; milestone list excludes the goal.
- The verify script reports every statement, definition, read-back, milestone, order and the
  description matching the repo (`BAD 0`).
- The library search re-run today.
- The repo committed and pushed with read-backs, statements, scripts and `proposal_state.json`.

## Expansion 0 — choosing the mission

A research paper is one mission with one goal theorem (`mission_captain.md`); a textbook is a
series. When the paper cites another paper for a theorem it uses, that theorem is a reference
milestone here and its own mission there, in whichever order publishes the dependency first: a
reference item needs the theorem to exist on the platform, Open is enough. Two authors' results
in one mission blur provenance in the names and the `source` fields, so split.

**Milestones are an attack path, not a coverage index.** Solvers look for a milestone whose
theorem is `null` or unproved, and the goal is never a milestone. So an unlinked milestone says
"formalize this" and must never record something out of scope; a milestone linked to an `Open`
theorem is the ideal live target; omission costs nothing, and coverage boundaries belong in the
description.

**External dependencies are milestones, not exclusions.** When a source result rests on a
theorem from elsewhere that Mathlib lacks, keep the result as a milestone and add the external
theorem as its own milestone (or a reference item if it is already published), stated faithfully
from *its* source in the form the paper applies, and say in the description that it is cited,
not proved. Scope the mission by the paper, not by Mathlib. Exclude only what cannot be *stated*
without a missing definition. (dbenbenn, 2026-09-17: a milestone naming a missing external
theorem "will just give more motivation for people to add those external theorems.")

Which result is the goal is the author's call before it is ours: read the introduction for the
sentence in which the paper says what it shows ("More precisely, we will show that…"). The most
cited corollary is often a later application; a headline consequence proved by importing another
mission's theorem is not a goal for this one.

## Expansion 1 — the source

Keep the PDF, a diffable text extraction, and the repository from day one: the human audits the
primary source and wants a copy that diffs. Project Euclid serves old journals at the article
path with `.pdf` in place of `.full`; its Download endpoint returns a bot page.

**Render the pages and read them.** `pdftotext` of a scanned 1960s–80s journal turns `≥` into
`>`, `α` into `a`, drops subscripts and splits displays. On one mission the goal was written
strictly, read back and uploaded before anyone looked at the page image, which shows `≥`.
No read-back can catch this: the auditor sees only the Lean. So for every quoted sentence and
every formalized formula, `pdftoppm -f N -l N -r 130 -png paper.pdf out` and read the image
before writing the Lean or the quote; use the OCR text for searching only.

Reading the LaTeX, when you have it, is not reading the paper either: macro names are not
notation (resolve the `\newcommand` chain and quote the rendered form); numbered environments
share counters and a commented-out one shifts everything after it; arXiv and proceedings versions
number differently, so cite one and record which; and "Let $X$ denote…" followed by "we find…" is
a claim, not a definition, so formalizing the displayed recursion as the definition silently
assumes the step.

**Cite the line, not the neighbourhood.** Every notation error in one audited project came from
reading around a result: an argument carried down from two items above, a symbol taken from a
macro, a number recalled from a remembered sequence. When you cite result $N$, open result $N$.

## Expansion 2 — the library search

`GET /theorems?q=…` and `?tags=…` on the platform, and `grep` in Mathlib, for the goal, each
definition and each cited result. Someone else can close your goal while a Draft sits for days:
on one mission the entire theorem, including its hard half, was published and proved by another
captain during a week of prose audits, unnoticed because the search was never re-run. One call
per session and one before Submit. When the goal is already proved elsewhere the mission dies
even if the decomposition is better; what survives is any public definition or reusable lemma
the other development kept private, published on its own merits.

The platform carries a large layer of auto-generated theorems with private definition bundles and
no source text (one account uploaded twelve percent of the catalogue in a week, one stub per
declaration of a machine-generated repository). Read a hit from such an account with that in mind.

## Expansion 3 — the design

List, from the paper: every numbered result; every unnumbered step a proof leans on (the
"clearly" sentences cost lemmas; a proof paragraph's difficulty is concentrated in what it does
not say); every result cited from elsewhere; the definitions needed to state all of it; and what
is left out, with the reason, for the description. Then agree the list with the human. Their
review is the scarce budget, so the shape is settled before the Lean and the read-backs are spent
on it.

Design questions that recur, with the answers we have settled on:

- **One statement per source sentence.** A proposition with two clauses is one conjunctive
  theorem; splitting it into two milestones is not a decomposition when one induction proves both.
  Anyone who needs a half takes `.1` or `.2`.
- **A step the paper states inside a proof** ("if $G$ is a non-locally finite periodic group then
  $G \in NF \setminus EG$") is a milestone with exactly that sentence's hypotheses and conclusion,
  not the fragment the argument used.
- **A cited theorem stated as a three-way equivalence** of which the paper applies one direction:
  state the direction applied and say so in the title, unless the other directions are cheap.
- **A lemma the paper uses in a special form** (extension of finitely presented by finite) is
  stated in that form; the general textbook form is a separate library contribution.
- **The structure a source builds with ordinals or Lie groups** is replaced by an inductive
  predicate or omitted; say so in "What is left out" and give the Lie-free route in the milestone.
- **Fidelity is about statements, not just truth**: match the paper's constants (`π²/(2θ²) + …`,
  not a convenient weaker bound), generality (the three-variable definition, with the
  specialisation derived), and naming (every numbered result gets a Lean theorem named for it).
- **When the paper has a gap**, closing it is research, not transcription: new mathematics lives
  in its own file and nothing the paper's build needs may depend on it; no result is marked done
  on the strength of mathematics the paper does not contain; a proof that a method is capped is a
  first-class result; state the residue sharply ("the gap reduces to *this* inequality").

**When a milestone is too big, publish its steps.** Read the source's own proof of the result and
publish the ingredients as theorems, linked as milestones ordered immediately before the hard one.
Steps that are not about the source at all ("an increasing homeomorphism of the line has no
non-fixed periodic point") are better published as standalone general theorems. Weakening a
conclusion to what the goal consumes can collapse the apparatus: check whether the proof can be
cut the same way before formalizing the source's version.

## Expansion 4 — the definitions bundle

A bundle holds only the definitions the mission's statements use, sourced to the pages that
define them; a paper that defers its definitions to another paper gets a bundle sourced to that
paper. Reuse published bundles (`Chou.wordBall` served three missions). Compute each file's
imports from the identifiers it uses, never from a template: the preamble is frozen at publish,
so an unused `import Definitions.X` is a dependency every citing development inherits forever. A
bundle beside the bundle that imports it changes no dependency and is not worth a click.

**Doc comments inside a published definition are an unaudited surface.** A read-back audits the
statement; a natural-language statement is audited against the Lean; a doc comment is neither,
and it is published and read on trust. Either prove what it claims somewhere in the mission and
say where, or do not assert it. The module docstring is equally frozen: no pronouns for authors,
no claims about equivalence to the paper.

When Lean needs a structure the paper takes for granted (a quotient known abelian, a rank),
build it so the instance exists by construction and say in the docstring that the object is
isomorphic to the paper's; the read-back will render the construction and the description
explains it.

## Expansion 5 — the statements

**Shape each statement like the source's sentence.** The theorem a development proves is chosen
for what the proof needs; the theorem the source states is chosen for what reads well; they
differ more often than not, and the milestone will be linked to the wrong one. This is the most
common defect by far; see *The variant trap* below for how it hides.

Include the section's standing assumptions as the paper states them ("we will always assume that
$A$ is abelian and that $B$ is finitely generated"), even where a proof does not use one; the
general form, if wanted, is a separate theorem. Take quantifier dependence from the result the
proof cites, not only from the sentence: English statements under-specify it, and the intended
strength lives in the cited lemma or in a remark after the statement.

**Names** are accurate labels: conclusion, then `_of_` hypotheses in binder order, ASCII, no
subscript abbreviations binders could capture. A name that needs a caution is the wrong name
(`no_free_subgroup` carried a 52-word paragraph; `no_free_subgroup_of_rank_two` deleted it).
An auditor's name check is a style opinion, not a fact: read the argument, do not count the
auditors. Namespaces by author (`Milnor.`, `Wolf.`) keep provenance visible when papers share a
bundle.

**Compile in server shape** — the file the server sees is `preamble` + `formal_statement` — and
rebuild every item that way before Submit; a UI edit is not type-checked and one failing draft
fails the whole submit. A published statement cannot grow: if the paper's result is a
conjunction and you publish two of three clauses, the third goes under a new name.

## Expansion 6 — blind read-backs

**A description is not publishable until someone blind-reads the Lean**, including milestones
added to a live mission where no Submit gate exists. Hand an independent agent the declaration,
its preamble and the definition files it imports, and not the prose, the source or your intent,
and ask what the code literally asserts; compare; publish only what survives. Measured across
277 descriptions: 4% defective when written against a source sentence, 32% for research code
written minutes after reading the statement. Rereading cannot catch an error where your
description and your understanding are wrong together.

**Use the tooling, do not rewrite it.** `scripts/readback-brief.md` is the text the auditors get;
`scripts/stage_auditor.py stage <slug> <artifact.lean> [imported-def.lean …]` seals one auditor in
a directory holding only the brief, the artifact, the imported bundles marked as context to expand
inline and not to render, the library roots, a probe wrapper and `scratch/`; `collect` pulls out
the two files, runs the hygiene checks on the publishable one, and prints any `IMPORTS` line the
auditor wrote about an unused import; `teardown` removes the directory. Strip docstrings from the
staged Lean first. The prompt's reply asks for five lines: conventions settled and whether source
settled them, anything unsettled, the name check, unused imported files.

**Two files from one blind reading.** `readback.md` is testimony, published beside the statement
on a draft item: what the declaration literally asserts, in mathematics, no judgment, no Lean
identifiers, no citations. `audit.md` is captain-side: conventions with `file:line`, what the
statement does not say, the name check, the imports. Write the read-back first. Never edit a
read-back; re-run it. Re-run whenever the Lean changes, including an import change that a
read-back described. Only draft proposal items carry testimony on the platform (`PATCH
/theorems/:id` rejects `readback`; `POST /submit-problem` drops it silently), so the repo's
`readbacks/` directory is the only record for anything published directly.

**The brief is the N-way artifact.** A defect in it corrupts every read-back. Never hand an
auditor a convention (the multiplication order, what a bracket expands to): let them read the
libraries, require a citation per convention and both readings for anything unsettled, say the
body is deliberately `sorry`, name one working directory with relative paths. Keep the rationale
out of the brief, in the private sibling file; enumerate kinds of notation, never your
development's own traps. Batching several declarations into one auditor is fine but each
read-back must be self-contained; a bundle's read-back is one numbered document. Cold-audit
findings are hypotheses: two of thirty-eight were wrong. The measurements are in
`references/audit-evidence.md`.

## Expansion 7 — the prose

**The description.** Write it against `mission_description.md` in the platform's references, which
fixes the section structure and the sentences it requires. First sentence: "This mission formalizes <author, *title*, journal, year,
pages (DOI link)>", with a companion paper in the same sentence. Then the motivation, built from
the papers' own sentences about their context: quote "we will show that…", "raise the question
of whether…"; never paraphrase a cited problem or credit an answer from memory. Then **Setting**
(each definition with its Lean name in backticks and the reading chosen for any ambiguous term,
"normal series" say), **Target** (the goal quoted with page, how it is stated, the milestone
plan), **What is left out** (with reasons), **References**. Display math renders but does not wrap, so use `$$…$$` only for a formula that fits on one
line; a whole sentence set as display math ran off the page on the Chou draft and reads fine as a
quoted sentence with inline math. The References never repeated as a paragraph; nothing about the process ("an
independent audit verified…"). Keep every statement about what the mission does and does not
prove: that honesty is what makes the rest credible.

**Milestone descriptions are the source's statement.** `mission_captain.md` defines the field as
"the lemma's statement in prose — the shared target agents formalize against", "usually verbatim
from the source paper", and says not to paste the natural-language statement. So: the source's
sentence in quotation marks with its page, first; then, if it earns its paragraph, *Route.* or
*External.* For an unnumbered step the paper does not state, paraphrase and quote only what it
does say. The paper's words never appear outside quotation marks. Keep descriptions in one file
and PATCH them through the milestones endpoint with an echo check.

**Natural-language statements say what the Lean says**, written from the declaration in front of
you and not from a sibling: what it asserts, where it is stronger or weaker than the source,
which hypotheses the source does not state. Describe; never assert a hypothesis is necessary
without a witness. **One home per fact**: the statement's fine print in the NL, the role and the
route in the milestone; a milestone may name its conclusion in one orienting clause. Milestones
are read standalone, so "the previous milestone" is broken for the actual reader.

**Titles are claims.** A substituted verb ("vanish" for "is the identity") and a conjunction
folded into a hyphenated adjective ("slope-one piecewise-linear" for two conditions) both change
the claim; take the verb from the source and grep the proposal for the word you replaced. A
milestone title indexes the source's lemma and may name a result stronger than what is
formalized; the NL and the read-back describe this declaration. Judge each by its yardstick.

**Pronouns.** Use the surname or "the paper". A frozen docstring on one published bundle still
carries a pronoun nobody could justify.

## Expansion 8 — upload and verify

Two scripts per mission, both idempotent: an uploader that creates the proposal once, POSTs
definitions with their read-backs, reference items, draft theorems (`preamble` split from the
body by the import lines), sets `main_item_id` and `item_order`, and POSTs the milestones; and a
verifier that fetches the Draft and compares every field to the repo, normalising whitespace,
and prints `BAD 0`. Every field means the prose fields too: title, natural-language statement
and source of each item, not only statements and read-backs. On the Milnor draft a pronoun fixed
in the repo's item file stayed on the server all afternoon because only milestone prose and the
description had upload scripts of their own; an item's prose changes only when the item is
PATCHed or re-POSTed, and a verifier that skips those fields cannot see the gap. Keep ids in `proposal_state.json`. Order: definition references, definition
bundles, the lemmas, the reference milestones, the goal last; milestones in that order too, since
the milestones endpoint's own order is what the human sees numbered.

The endpoints and their edges: an item's `PATCH /mission-proposals/:id/items/:item_id` takes
`theorem_name`, `theorem_title`, `formal_statement`, `natural_language_statement`, `preamble`,
`source`, `tags`, `readback`, `readback_model` and rejects milestone fields; milestone prose goes
to `PATCH /mission-proposals/:id/milestones/:item_id`, which accepts `milestone_title` and returns
`title`; the proposal's `PATCH` takes `description`, `mission_type`, `item_order`,
`main_item_id`. **Never probe a write endpoint with a dummy payload against live prose**;
snapshot first, probe with the real value. `mission_type` is `ResearchPaper` for a paper
(`Textbook`, `OpenProblem` otherwise); a wrong value is fixable on the live mission.

**Swapping a draft item** (a statement that has to change shape): POST the new item with its
fresh read-back, DELETE the old item and its milestone, restore the position in `item_order`,
POST the milestone. The generic tool pattern is `swap_item_server.py NEW OLD…` in a mission's
`tools/`. Editing a draft item clears the human's confirmation of it; PATCHing milestone prose
does not.

## Expansion 10 — the human audit and Submit

The human confirms each draft item on the platform and clicks Submit. **Submit is asynchronous**:
one publish job per item, compiled one at a time in `item_order` (about two minutes per theorem
on a busy queue, under a minute on a quiet one). Until the last job finishes the proposal still
reads `status: Draft` with `submitted_at: null`; items gain `theorem_id` one by one, definitions
first (which then show as `reference` items). `GET /publish-jobs?limit=200` is the only place a
failure appears (`FAILED` with `error_message`); a Draft status a quarter of an hour after the
click is not one, a second click does not duplicate jobs, and a run that goes quiet with items
still lacking ids resumes on another click. When the last item publishes the status becomes `In
review`; approval makes it a live mission.

**A statement is Open the moment its job publishes**, before review and before the last item.
Submit ready solutions as each one comes up; nothing waits for approval.

## Expansion 11 — after launch

**Solutions.** Keep the development as small modules that import each other; to submit a full proof, build
the submission by concatenating with `scripts/merge.py OUT MODULE…` (dedups by bare declaration name,
refuses unbalanced namespaces or a second `theorem solution`) and finishing with `theorem
solution` stated verbatim; re-elaborate the published statement locally and discharge it with
`solution <binders>` before submitting, which is the type check the server runs. A solution may
import any platform theorem as `Theorems.Thm_<Namespace>_<name>`, the mission's definitions and
Mathlib; never another solution or its own target. Importing only Proved theorems gives
`ACCEPTED` and the target shows Proved; importing an Open theorem gives `SKETCH_ACCEPTED`, a
reduction: the imported theorems become the target's decomposition children, the target sits in
the mission's tree and auto-resolves when every leaf is proved (`prove.md`, `missions.md`). A
reduction is the right submission when the decomposition is what you have and the leaves are
worth publishing for others to attack; a full proof by concatenation is the right one when you
have the whole argument and want the milestone Proved now. Fetch each imported statement into
`Theorems/Thm_….lean` locally to compile-check. Submit with `scripts/submit_verify.py TID FILE EXPL.md`; poll
`GET /verify?submission_id=…` (the documented `GET /submission/{id}` 404s). The first verify that
imports a freshly published bundle can time out at 300 s while the server builds it: resubmit
unchanged. Explanations are patchable; attach the route in prose and say the file is
self-contained.

**Metadata and edits on the live mission.** `PATCH /missions/:id` takes `name`, `description`,
`mission_type`, `field_ids`, `main_statement`. After a live edit the proposal snapshot lies:
read the live copy from `GET /missions?limit=…`, not from the proposal. `GET
/missions/:id/milestones` truncates silently at 20; pass `?limit=100`. A defect found after
launch is fixed by publishing a corrected statement and relinking with `PATCH /milestones/:id`
and a `reason`, never by softening the description. `DELETE` on a milestone cascades its history
with no undo: archive first, confirm with the human. Mission pages are addressed by URL-encoded
name; the id form renders "doesn't exist" while answering 200.

**Milestones added post-launch** go through `POST /submit-problem`, immediate and with no
read-back field, so the blind read-back runs before the POST and the repo keeps it.

**The record.** The repo holds the sources, statements, read-backs with their audits, the
scripts, `proposal_state.json`, `published_ids.json`, solutions and explanations, and the tools
the session wrote (copy them out of the job scratch directory before it disappears). Keep audit
inputs as evidence, never bulk-edited (`chmod` both the files and the directory: `sed -i` needs
the directory writable, a redirect needs the file). Render prose fields to markdown so edits diff.

**Lessons go here, not into memory.** Process rules belong in this file, in the public skills
repo, committed and pushed in the same turn; memories hold the human's preferences and the state
of live work. When a mission teaches something, edit the algorithm, the list or an expansion.

---

# Lessons behind the steps

## The irreversible surface

**`formal_statement`, `theorem_name`, `preamble` and definition code freeze at publish.**
`theorem_title`, `natural_language_statement`, `source`, `tags` and a solution's `explanation`
stay patchable forever, definitions included (`contribute.md`'s table omits `theorem_title` and
is wrong; verified against the API). Two paths reach publish: `POST /submit-problem` and
`/submit-definition` publish at the POST; a mission proposal publishes at Submit, and until then
every draft field is editable, statements included. Do not carry over the belief that a drafted
statement is committed. Get the statement right before publishing, not the proof; verify
mechanically that the published statement matches the repo's.

## The variant trap

In one paper it recurred five times: Corollary 3.6, Theorem 5.15, Proposition 5.14, Lemma A.1
and equation (15) were each milestoned to the variant the development used, found only by reading
the source sentence against the linked Lean. How they hide: a quantifier hoisted (the sentence
puts $C$ after $\Gamma$, the cited proposition says $C = C(d, \vartheta)$); a spurious hypothesis
the source never states; an invented object built to repair a gap, so the variants are
incomparable; a trailing clause dropped ("in particular, if $\Omega$ is a ball…" is a second
assertion); a step reformulated because the proof needed half of it; a fragment of a proof
sentence with a hypothesis removed because the fragment holds without it. The remedy is always
cheap: publish the source's own statement, derive it from the variant, link that, name the
variant in the description.

## Publish the statement before the proof

Publishing a statement with no solution leaves it `Open`; milestone it, and someone may close it.
The duty that comes with it: type-check, work the proof far enough to be confident (close the
constant arithmetic), and write the route into the milestone. A prose argument for a side claim
in a description can be retired into a citation by publishing the claim as its own `Open`
statement; pin its objects by pointwise hypotheses rather than a new definition, and keep
`source` honest about what the source supplies.

## Auditing

Four axes, and no one sees another's defects: **against the source**, **against a reader**,
**against the platform's rules** (read `mission_captain.md`, `contribute.md`,
`mission_description.md` as a checklist, field by field: one proposal that survived a dozen
audits had every `source` missing its URL and page, a proof sketch in the goal, no Lean
representation stated), and **against your own fixes**. Separate passes, separate briefs.

**Audit before publish.** Human review is the scarce budget; never trade an agent pass for
uncertainty handed to the human, and never reason "this field is patchable, so publish now and
audit later". Blindness is not the safeguard, the adversarial pass is: descriptions composed from
blind read-backs still carried a 12% error rate, because the composition step introduces its own
errors (a shift by $x$ written into a set-builder; a quantifier inverted). The recipe that worked:
definition bodies as mandatory input, a ban on unverifiable counterfactuals ("this hypothesis is
essential", every one false), a structural lint that every field of a structure-valued hypothesis
is accounted for, a second error-only pass, then publish.

**Accretion.** Each correctness round finds an imprecision, the cheapest repair is a qualifying
sentence, and after five rounds the passage is true and unreadable; the tell is corrective voice
warning the reader off mistakes the author made. If a round grew the document, the round failed.
Respond to a finding by choosing among delete, correct, relocate, accept, decline, restructure;
"accept" is the one you will never reach for and is often right, since precision has a home
downstream. Grep the whole proposal before restoring a "lost" fact; when a gap is exposed, ask
whether the passage needs the claim at all.

**Date-dependent claims** need a current check, not a source check: "still open", "not in
Mathlib", "the first". **Readability** is its own pass: dangling referents, symbols used before
introduced, one object under three names; its fixes introduced two fresh false claims, so they
get a correctness pass of their own. **Quote the subject the source predicates it of**; three fix
rounds each hung an exact quotation on the wrong noun. **Grep the mission's vocabulary** before
ruling on a term; the project's usage is the authority. **Once a passage has three rounds of
patches, rewrite it whole.**

**Auditing a fix is a separate job.** Propose, do not apply; verify the after-text in full field
context, never a hunk; re-audit every amendment (five of seven rewrites were still defective);
gate mechanically by hashing audited text; a patch is done when a fresh auditor accepts it
unchanged. A compiled probe settles the mathematics, not the sentence about it; state every claim
under the hypothesis your own document defines; an over-correction drops the other half.

## Reading and bookkeeping habits from formalizing papers

Reread the paper continuously: before each numbered result, when a proof fights back (you are
usually proving the wrong statement), before acting on any audit finding. Follow the paper's
proof and depart only when necessary, recording each departure: a formalization whose proofs
mirror the paper's certifies the paper; one that reaches the same statements by other routes
certifies only the statements. Give every numbered result a named theorem; when the paper gives
two descriptions of one object, prove their agreement, which is where a mis-transcribed
definition surfaces. Keep a status table with a row per numbered result, updated in the same
commit as the proof; `sorry` is a loan that must be zero at every commit called finished;
`#print axioms` on everything cited, generated as a batch; `#guard` numeric spot checks on
definitions before proving anything; build clean before reporting and say what was run. Findings
are hypotheses: verify each against the source before fixing it.

## Pipeline pitfalls

For the full-project upload pipeline (`references/publishing-pipeline.md`): every source
position Lean reports is a **UTF-8 byte offset**, so slice as `bytes`, never mix with `str`
indices, deduplicate overlapping edit ranges and drop edits nested inside a replaced range. The
job scratch directory is per-session, not per-project: namespace every artifact by project and
verify counts against the plan. `merge.py`'s two refusals encode a verifier rejection that once
took six diagnostic submissions.

## Contributing outside a mission

Almost every existing mission milestone is proved; the productive seams are milestones whose
linked theorem is `Disproved` through an encoding accident (`ConvexCone` need not contain `0`,
`AffineSubspace` may be empty), repaired by publishing the corrected statement and asking the
captain in the mission discussion to relink, which takes about a week; and infrastructure that is
published but entangled in a heavy bundle. A scan of every proved mission's solutions found 5,794
helper lemmas inside solution files, almost no cross-mission duplication, and one real gap
(Farey), so the pattern to look for is entangled infrastructure, not missing infrastructure.
