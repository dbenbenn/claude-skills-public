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

**Sync the rulebook to head at the start of every session**, before reading it:
`git -C "$P2M_WORKSPACE" fetch -q origin && git -C "$P2M_WORKSPACE" log --oneline HEAD..origin/main`,
then read the incoming diff of `references/` and `SKILL.md` and fast-forward
(`git -C "$P2M_WORKSPACE" merge --ff-only origin/main`). On 2026-09-23 the local copy was seven
releases behind, and those releases had rewritten the captain's faithfulness principles and
added the moderation loop, all unread while a proposal was being drafted against the old text.

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
   `IMPORTS` lines; re-run whenever the Lean changes. **Then a source-side audit on every
   statement** with `scripts/source_audit.py`: it lists what the source sentence claims before it
   sees the read-back, and a verdict that is not `faithful` blocks the hand-over until each gap
   has a written disposition. → *Expansion 6.*
7. **Write the prose**: the mission description, one milestone description per milestone with
   the source's sentence quoted first, one natural-language statement per declaration.
   → *Expansion 7.*
8. **Upload the Draft and verify it with `scripts/draft.py`**, commit the repo. → *Expansion 8.*
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
- The sentence does not *outrun* what it cites: when the paper says "by X and Y we conclude",
  read X and Y and check they reach the conclusion under the hypotheses actually stated.
  (*When the sentence outruns its citation*, below.)
- Every author is *they*, in prose and in Lean docstrings alike, unless the source itself
  states otherwise. A name is not evidence of anyone's pronouns, and a wrong guess about a
  real person is the one wording error a reader will always notice.
- Every reference that has a DOI carries it as a link. Look each one up (the Crossref API takes a
  bibliographic query and returns the DOI, the page range and the year, so it confirms you have
  the right item and not its sequel), then check the link resolves. Where an identifier covers a
  container rather than the item — a problems section holding one problem — say so in the entry
  rather than letting it read as the item's own. Where there genuinely is none, a book, say that
  too: an entry with no link should be visibly deliberate rather than an oversight.
- A cited external result is stated from *its* source, in the form the paper applies, marked
  external.
- The goal is the result the author names as the paper's contribution, not the most famous
  corollary and not the easiest theorem.

**Lean hygiene**
- Every `import Definitions.*` is used; a bundle imported only transitively is not listed. The
  preamble freezes at publish and becomes a permanent dependency.
- A solution carries no declaration unreachable from `solution`: run
  `scripts/prune_solution.py FILE --check` before submitting. Assembled-by-concatenation files
  routinely carry two thirds dead code, and a dead copy of a published theorem is the thing that
  later gets "reconnected" into a dependency that never existed.
- Every statement compiles in server shape, `preamble` + `formal_statement`, with `:= by sorry`.
- Names are accurate labels (Mathlib style, `_of_` for hypotheses in binder order), ASCII, and a
  name that would need a caution is the wrong name.
- **A published statement carries no docstring.** It is the only prose on the platform that both
  freezes and is never audited: `formal_statement` is immutable, and the read-back staging strips
  comments before the auditor sees the artifact, so nothing independent ever reads it. The
  platform does not want it either — `upload_full_project.md` tells uploaders to strip it, warning
  that a leading `/-- -/` can make the platform silently drop the declaration. Put the source
  quotation and the encoding notes (a commutator written longhand, a chain condition spelled out
  elementwise, a symbol renamed because Lean reserves it) in `natural_language_statement`, where
  the reader meets them beside the claim and a correction costs one PATCH.
- **A definition bundle keeps docstrings, but only for what cannot rot.** Its code freezes too:
  `PATCH /theorems/:id` answers `Unknown field(s): definition. Allowed: natural_language_statement,
  theorem_title, source, tags, deprecated, reason`, and the read-back staging strips the bundle's
  comments as well, so they are as unauditable and unfixable as a statement's were. They earn
  their place anyway for one reason a statement cannot claim: a bundle holds many declarations
  and has a single description for the lot, so a per-declaration docstring is the only
  per-declaration documentation a reader of the code gets. Keep them to what the object *is* and
  where in the source it comes from. Every sentence that asserts a *relationship* to the paper —
  that this agrees with the author's notation, that it is equivalent to their definition, why a
  formalization choice was made — belongs in `natural_language_statement`, which is patchable and
  is what the blind auditor's testimony is compared against. Two of ours show the stakes: the
  Milnor bundle claimed Wolf's words "are exactly" the published ball and was softened to "taken
  here as" hours before publish, and the Chou growth bundle carries a correct but frozen sentence
  about when its ball agrees with Chou's $F^n$.
- A docstring in a development module, which is never published, asserts nothing unaudited
  ("equivalent to the paper's definition").

**Read-backs**
- One per artifact, from the current Lean, with the imported bundles marked as context and not
  rendered; no Lean identifiers, no `file:line`, no naming verdict in `readback.md`; the model
  attributed correctly; never edited by hand. The auditor's five-line reply is kept as
  `<name>.reply.md` beside it.
- A source-side audit per statement, verdict `faithful`, or every WEAKER / MISSING claim decided in
  `<name>.dispositions.md`: **fixed** (the statement now says it), **carried** (another milestone
  states it, named), or **dismissed** (with the reason, e.g. true by definition). A real gap --
  one with a genuine near-miss -- leads the report to the human, not a list of routine results.
  The read-back cannot do this job: it is blind to the source by design, and its own "What it
  does not say" is a Lean-side list where the one real omission looks like boilerplate (Garrido
  III, M3: "Not that a u a ∈ St(1)" sat second of five bullets and nobody read it).

**Prose**
- Each milestone description opens with the source's sentence in quotation marks and its page,
  then a marked *Route* or *External* paragraph if one earns its place. The paper's words appear
  only inside quotation marks; quotes checked against the page image, including the subject
  they predicate.
- **Recheck all the quotes, as the platform holds them.** Every quotation in every field — milestone
  descriptions, natural-language statements, `source`, the mission description — read from the
  live Draft and compared word for word, punctuation included, with the rendered page. Do it
  last, after every upload, and preferably by an agent that did not write them: a check of your
  own transcription does not see what a script did to it afterwards (three Garrido quotes shipped
  as "Tarskis" and "Carathéodorys").
- Each natural-language statement says what the Lean says, written from that Lean and not from a
  sibling; siblings audited against each other. **In particular it may restate the source in the
  source's own notation ("that is, $aua = (u_1, u_0)$") only if the Lean proves everything that
  notation asserts.** That "that is" carried the unproved half of M3 past three separate reviews:
  the prose, the Draft hand-over and the proof report all repeated it.
- Titles start with the source index ("Lemma 3.2 — …", "Chou, p. 400 — …" for a reference
  item) and are claims, checked against the Lean and against the quotation in their own
  description — never written to be parallel with a neighbour. A title copied for shape carries
  over the part that should have changed, exactly as a copied description does. Watch the
  direction words: for a theorem with several conjuncts, one clause may run the other way, and a
  title that reads smoothly can assert the wrong direction for it. Wolf's Theorem 3.11 concludes
  that a finite-index subgroup *is* finitely generated, inherited downward, and separately that
  its polynomial growth passes *upward*; the milestone title said both passed up, contradicting
  the quotation printed under it.
- The milestone title and the theorem title are different fields on different endpoints. Editing
  one does not touch the other, so check both and check that they agree; a rename is when they
  drift apart.
- **Titles against the platform's rule, then ours.** The platform's rule (`mission_captain.md`,
  milestone `title`): "Strict rule: start with the index in the source (e.g. `Lemma 3.2`),
  followed by a short label of the lemma"; `theorem_title` is a free display label, and may be a
  name ("Sensitivity conjecture"). Our house rule on top: **a result with a canonical name gets the
  name** ("Tarski's theorem", "the Invariant Extension Theorem" — the source often gives it in
  parentheses, "Theorem 1.11 (Tarski)"); only a result without one gets a spelled-out claim, and
  then the label states the claim, the *whole* conclusion (every conjunct), not a topic
  ("subgroups of amenable groups") and not half of it;
  the simplest way to keep the pair agreeing is one title for both fields. Keep it short:
  a claim that needs 120 characters is straining the platform's "short label". On the Garrido
  draft Proposition 1.14's two titles each named a different conjunct, one in a word Garrido never
  uses ("unparadoxical"); Corollary 2.5's theorem title claimed the non-existence of a paradox,
  which the Lean does not assert.
- The description opens "This mission formalizes <citation with DOI link>"; has Setting,
  Target, What is left out, References. **Run `scripts/check_description.py` on it** — the
  opening sentence, the required sections, display-line length, author pronouns, rulebook
  phrases, first person and word count are all mechanical, and I have shipped a description
  that never named its source while this very rule sat here unread; display math only for a formula short enough to fit on one line, since a display
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

**Search the neighbouring Lean projects too** (dbenbenn, 2026-09-24), which none of the above
covers: **Lean Pool**, canonical repository `Vilin97/lean-pool` (other copies are forks — check
`fork`/`parent` with `gh api repos/<r>`), both its admitted projects (`LeanPool/projects.yml`) and
its intake list (`candidates/decisions.jsonl`, `candidates/README.md`); and **Tau Ceti**,
`TauCetiProject/TauCeti` and its roadmaps `TauCetiProject/TauCetiRoadmap`. Also **Palomar**
(palomar-registry.org, Tao et al.), a registry of machine-checked results: search its feed
`https://data.palomar-registry.org/recent.json` (entries carry abstract, MSC codes and theorem
names) for the goal and the named results. Registrations are frozen snapshots, not importable. Clone shallowly and
grep: GitHub code search rate-limits after a few queries. A hit is prior art to credit in the
description, and sometimes a reason not to run the mission; an arbitrary GitHub repository found
along the way is less salient. Garrido II was designed without this step, and the Banach–Tarski
paradox turned out to be formalized already in a Lean Pool candidate.

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

**A sentence that introduces notation gets a bundle definition whose type carries the sentence's
assumptions, and the statements use it wherever the source does.** Notation packs claims: Garrido
writes "any element $u \in St(1)$ as $u = (u_0, u_1)$", so the later "$aua = (u_1, u_0)$" asserts
$aua \in St(1)$ as well as the two components. Garrido III first absorbed that sentence into a
general section map defined on every automorphism, so the restriction was written down nowhere,
and M3 was stated with the two components only -- a statement $u \cdot a$ also satisfies. As
`stOnePair : St(1) → Aut(T) × Aut(T)` the notation cannot be applied to $aua$ without a proof that
$aua \in St(1)$, so no statement can drop it. Type the notation with what the defining sentence
assumes, not with what a later result proves: the Remark *shows* the components lie in $\Gamma$,
which is why the codomain is $\mathrm{Aut}(T)^2$ and not $\Gamma^2$. When a gap is found in a
statement whose source uses no such notation, the default fix is simply the missing conjunct.

A bundle holds only the definitions the mission's statements use, sourced to the pages that
define them; a paper that defers its definitions to another paper gets a bundle sourced to that
paper. Reuse published bundles (`Chou.wordBall` served three missions). Compute each file's
imports from the identifiers it uses, never from a template: the preamble is frozen at publish,
so an unused `import Definitions.X` is a dependency every citing development inherits forever. A
bundle beside the bundle that imports it changes no dependency and is not worth a click.

**Name every concept a statement uses more than once.** A clause written out in several
statements ("finitely additive", "`G`-invariant") is a definition the reader cannot cite and the
source's word never maps onto; define it once in the bundle and use the name. Mathlib's own
theorems often write such clauses inline (`IsFoelner.amenable` does), which is how the Garrido
draft ended up with seven copies of one additivity clause; copying Mathlib's shape is not a
reason to keep them. Say in the prose when the source uses a term it never defines, and what
standard meaning the definition takes.

**A universe-quantified definition must reach the object it will be applied to.** A property
that quantifies over `X : Type v` with `v` independent of the ambient `G : Type u` is stated at
every pair of levels, and a theorem using it can be false at some: Garrido's invariant extension
property, so quantified, made a four-way equivalence false at `u = 1`, `v = 0` (a large simple
group with a free subgroup acts trivially on every smaller set). `Type 0` is too small and an
independent `v` is too loose; `Type (max u v)` keeps "every `X`" and always contains
`ULift G`. And **re-run every local check file whenever a definition changes**: the universe
check written for exactly this had been failing silently since the edit that broke it.

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

**A published statement that turns out to be *false* is not the same case**, and must not be
quietly superseded: the platform takes disproofs. `POST /verify` with `proof_type=disprove` and a
`solution` proving the negation of the *whole quantified* statement — wrap the binders into one
`∀` and negate that, not the conclusion. A disproof may import `Definitions.Def_*` and Mathlib
but **not** `Theorems.Thm_*`, so lemmas it needs must be concatenated into the file. Accepted, it
flips the theorem to `Disproved`, which is what a reader who lands on it deserves to see;
deprecation says only that someone lost interest. `scripts/submit_verify.py --disprove` sends it.
**Fix the universe.** The verifier elaborates `solution @target`, so if the statement quantifies
over `Type*` and `solution` does too, nothing pins the universe and the verdict is `WA` with
"contains universe level metavariables". State the negation over `Type` and give the
counterexample there: refuting one instance refutes the polymorphic statement, and the check then
instantiates the target at universe 0. Check locally with `theorem _check : False := solution
@Target` beside a sorried copy of the target. dbenbenn pre-approves disproofs of Open false
statements; submit without asking.

**The hypothesis that admits too much.** The defect that produces a false statement is usually a
hypothesis that is weaker than the source's, not a wrong conclusion, and a blind read-back will
not catch it: the auditor is describing the Lean, and the Lean does say what they say. Wolf's
"minimal generating set" was read as *no proper subset generates*; that is equivalent to "basis"
for vector spaces and not for `ℤ`-modules, where `{2, 3}` is inclusion-minimal in `ℤ`. **Test a
hypothesis by instantiating the statement at its smallest case and asking what the hypothesis
still admits** — here `n = 1`, where it should have admitted only `{±1}`. Do it for any
hypothesis phrased as a minimality, maximality or independence condition.

**The conclusion that asks for too much.** The mirror case: an *existence* conclusion about
generating families of a finitely generated abelian group ("an independent generating set", "a
basis", "a subfamily that…") holds for free abelian groups and can fail with torsion — the
generating family `{(1,0), (0,2), (0,3)}` of `ℤ²` has no independent generating subfamily. Wolf's
Lemma 3.7 asks for commutators whose images are an independent generating set of each
lower-central factor; it was published, read back and sketched against twice before a class-2
group with `Γ₁ ≅ ℤ⁵ ⊕ ℤ/2` disproved it, because the earlier search tried only torsion-free and
cyclic factors. **Test such a conclusion on a non-cyclic factor with torsion before publishing**,
and when a proof says "choose any … subset", check one exists. The repair is usually the form the
source's own later proof uses (here p. 429: a subfamily generating a free abelian subgroup of
finite index), which is what the dependants needed anyway.

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
auditor wrote about an unused import; `teardown` removes the directory. For a whole mission use `stage_auditor.py stage-all MISSION_DIR [NAME…]` and `collect-all
MISSION_DIR [NAME…] [--teardown]`: driven by the same `mission.py` as `draft.py`, they stage each
theorem as its exact publish payload with the bundles it imports, save each prompt to a file, and
file the testimony under the names `draft.py` reads -- a pair that is missing a file or fails a
check goes to `readbacks/_failed/` and never replaces a good read-back. `stage` strips every
comment from what it stages, so pass the real files; it did not until 2026-09-24, when a bundle
auditor was found quoting a docstring, and the Garrido II and III bundle read-backs were re-run.
The prompt's reply asks for five lines: conventions settled and whether source
settled them, anything unsettled, the name check, unused imported files.

**Two files from one blind reading.** `readback.md` is testimony, published beside the statement
on a draft item: what the declaration literally asserts, in mathematics, no judgment, no Lean
identifiers, no citations. `audit.md` is captain-side: conventions with `file:line`, what the
statement does not say, the name check, the imports. Write the read-back first. Never edit a
read-back; re-run it. Re-run whenever the Lean changes, including an import change that a
read-back described. Only draft proposal items carry testimony on the platform (`PATCH
/theorems/:id` rejects `readback`; `POST /submit-problem` drops it silently), so the repo's
`readbacks/` directory is the only record for anything published directly.

**The text you stage and the library the probe uses can disagree.** An auditor reads the
`.lean` text staged into its directory, but `./probe` elaborates against the workspace's
*compiled* libraries. Edit a definition, stage the new text, and the probe still sees the old
`.olean`: the auditor reasons about one artifact and tests another, and nothing in the sealed
directory shows it. On the Garrido re-audit an auditor noticed the disagreement itself and said
so — luck, not a check. `stage_auditor.py stage` now runs `lake build` on every project module
the artifact reads before sealing anything, and refuses to stage if that build fails. Let
**lake** decide what is out of date: it tracks content, not timestamps, and a first version of
this gate compared mtimes and refused after a `touch` that changed nothing. The same trap
catches the captain: a checker that elaborates `preamble + formal_statement` proves nothing
about an edit whose module has not been rebuilt.

**The brief is the N-way artifact.** A defect in it corrupts every read-back. Never hand an
auditor a convention (the multiplication order, what a bracket expands to): let them read the
libraries, require a citation per convention and both readings for anything unsettled, say the
body is deliberately `sorry`, name one working directory with relative paths. Keep the rationale
out of the brief, in the private sibling file; enumerate kinds of notation, never your
development's own traps. Batching several declarations into one auditor is fine but each
read-back must be self-contained; a bundle's read-back is one numbered document. Cold-audit
findings are hypotheses: two of thirty-eight were wrong. The measurements are in
`references/audit-evidence.md`.


**The source-side audit (`scripts/source_audit.py`).** The read-back says what the Lean says; it
never sees the source, so it cannot notice that the Lean says less than the source. A second
agent works from the other side, in two phases the tool enforces:

1. `source_audit.py stage MISSION_DIR NAME`: the agent gets the quoted sentence (the “…” of the
   milestone description -- never the Route prose or the natural-language statement) and the page
   images, context pages included since notation is set there (`SOURCE_PDF`, `CONTEXT_PAGES` in
   `mission.py`). It writes `claims.md`: every atomic claim, notation-carried ones marked, and
   the sentence's hypotheses, ending with the line `END OF CLAIMS`.
2. `source_audit.py reveal MISSION_DIR NAME`, which refuses until that line is there, copies in
   the blind read-back; continue the same agent (SendMessage) and it writes `coverage.md`: each
   claim COVERED / WEAKER / MISSING, a **near-miss** object for every gap -- something the Lean
   accepts that the source excludes -- and a VERDICT line.

**The goal is a milestone for every purpose but the platform's list**: it keeps a
`milestone_title` and a `milestone_description` with its quoted sentence in the mission data,
`draft.py` leaves it off the milestone list as the platform requires, and every audit covers it
like the rest. An item may name `context_pages` where the notions its sentence uses are defined
(Garrido's Theorem 4.1 needs Definition 1.13 on p. 4 and the class EG on p. 7).

`collect` files both beside the read-back and exits 1 unless the verdict is `faithful`. Then write
the dispositions (the double-check list says how), fix, and re-run only what changed: a fresh
read-back of the changed statement, and phase 2 against it -- the claims do not change while the
source does not. Measured on Garrido III: M3's missing $aua \in St(1)$ was listed in phase 1 from
the source alone and given the near-miss $u \cdot a$; two faithful controls came back faithful.
About 46k tokens and 100 s per item, roughly the cost of the read-back itself.

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

**Check the quote after the script writes it, not before.** Checking a transcription against the
page image certifies what you typed, not what the file holds. On the Garrido draft three quotes
lost their apostrophes ("Tarskis theorem") because the script wrote `'Tarski''s'` in a Python
single-quoted string, which is two adjacent literals, not an escaped quote; the echo check passed,
since the server held exactly the damaged text, and dbenbenn found it reading M6. After generating
prose, re-read the written field against the page, and grep it for words that end in `s` where the
source has `'s`.

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

`scripts/draft.py MISSION_DIR upload [--go]` and `draft.py MISSION_DIR verify`; the mission
supplies only data, in `MISSION_DIR/mission.py` (the docstring lists what it defines, and
`extract_payloads()` builds each preamble from the bundles its statement uses). Every mission
through Garrido III copied its own uploader and verifier instead, and most of those verifiers
only checked that a read-back was non-empty. The upload creates the proposal once, posts
definitions with their read-backs, reference items, draft theorems, `main_item_id`,
`item_order` and the milestones -- and on every later run re-posts only what differs from the
live Draft, so an unchanged item never loses a confirmation. The verifier compares every field
to the repo, normalising whitespace, flags live items and milestones the repo lacks, and prints
`BAD 0`. Every field means the prose fields too: title, natural-language statement
and source of each item, not only statements and read-backs. On the Milnor draft a pronoun fixed
in the repo's item file stayed on the server all afternoon because only milestone prose and the
description had upload scripts of their own; an item's prose changes only when the item is
PATCHed or re-POSTed, and a verifier that skips those fields cannot see the gap. Ids live in `proposal.json`. Order: definition references, definition
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

**Check the target before spending a proof.** Another contributor can close an Open statement while
your prover runs: on the Chou mission `hall_finite_subgroups_of_index` was closed by another user
seven minutes before our proof landed, and the whole proof was wasted. `scripts/watch_targets.py
check <theorem_id>…` is the launch-time guard, one API call, run in the same breath as dispatching
the proof; `watch_targets.py watch …` under a Monitor turns a status flip during a long proof into
an event, and you decide whether to stop the prover. Do not automate the kill: the event is rare
and a half-written proof of a now-closed statement is still evidence of an approach.

**Published statements in the workspace.** After Submit, `scripts/fetch_theorems.py MISSION…`
writes every published theorem and bundle of the missions into `Theorems/` and `Definitions/` in
server shape and builds them, so solutions import exactly what the verifier compiles against; it
asks the platform for the list, where the per-mission fetchers read a hand-kept id file.

**A script that has had a bug is tracked and reused.** Every per-mission copy of a job carried its
own defects -- collectors that dropped `FAIL` lines, deprecate scripts that kept a deprecated
proof, forks without later fixes -- and each fix stayed stranded in one repo. When a one-off
script needs a fix, or the same job is about to be written a second time, it moves into
`scripts/` here.

**Graph hygiene: rewire, submit, audit.** A proof's graph edges are exactly its `import
Theorems.*` lines, so they are wrong in two ways: an import only dead code used (a false edge;
`prune_solution.py` now drops it) and a published theorem re-derived inline instead of imported
(a missing edge). `scripts/rewire.py FILE --target NAME -o OUT` turns each inline copy into a call
to the published theorem, adds the import, prunes and compiles; `scripts/submit_solution.py THEOREM
FILE --replaces OLD_SID…` submits, requires the new sketch's edges to equal the file's imports, and
retires the old proof through `deprecate.py`; `scripts/edge_audit.py MISSION…` checks every live
proof of a mission against its local file and reports INCORRECT, MISSING and UNMATCHED. Run the
audit after a mission's solutions land. The 2026-09-24 audit found 36 false edges on 19 theorems,
missing edges on 11, and two false edges on sketches submitted from test files.

**Solutions.** Keep the development as small modules that import each other; to submit a full proof, build
the submission by concatenating with `scripts/merge.py OUT MODULE…` (drops a declaration repeated
verbatim, refuses one whose name repeats with different text, unbalanced blocks, or a `theorem
solution`) and finishing with `theorem
solution` stated verbatim; **then prune what the proof does not use**, with
`scripts/prune_solution.py FILE --check`. Concatenation pulls in whole modules, so an assembled
file carries lemmas its target never touches — one Chou submission was 684 lines of which 205
were reachable. That is not only untidy: an unused copy of a *published* theorem reads as a
missing graph edge, and importing it to "fix" that asserts a dependency the proof does not have.
The script keeps what is reachable from `solution`, treats every attributed declaration and every
`instance` as a root — `@[simp]` and typeclass resolution use a declaration without naming it, so
unused-by-name is not unused — and `--check` re-elaborates the result, which is not optional; re-elaborate the published statement locally and discharge it with
`solution <binders>` before submitting, which is the type check the server runs. A solution may
import any platform theorem as `Theorems.Thm_<Namespace>_<name>`, the mission's definitions and
Mathlib; never another solution or its own target. Importing only Proved theorems gives
`ACCEPTED` and the target shows Proved; importing an Open theorem gives `SKETCH_ACCEPTED`, a
reduction: the imported theorems become the target's decomposition children, the target sits in
the mission's tree and auto-resolves when every leaf is proved (`prove.md`, `missions.md`). A
reduction is the right submission when the decomposition is what you have and the leaves are
worth publishing for others to attack; a full proof by concatenation is the right one when you
have the whole argument and want the milestone Proved now. After Submit, post every
solution as soon as its own statement is published: a wired solution whose imports are still Open
is accepted as a reduction and resolves to Proved when they are, so submitting in dependency
layers and waiting for each layer's verdicts only adds delay (dbenbenn, 2026-09-24). Fetch each imported statement into
`Theorems/Thm_….lean` locally to compile-check. Submit with `scripts/submit_verify.py TID FILE EXPL.md`; poll
`GET /verify?submission_id=…` (the documented `GET /submission/{id}` 404s). **The verifier runs with `autoImplicit` off, and `lake env lean` does not**: it ignores the
lakefile's `leanOptions`, so a `universe u` declared inside a `namespace … end` block that has
closed passes locally (the stray `u` is auto-bound) and fails on the server — as `unknown universe
level` or, worse, as SORRY on a declaration above it. Hoist every `universe` line to the top of an
assembled file; `prune_solution.py --check` now elaborates with `-DautoImplicit=false`. Four of
the 23 Garrido solutions failed this way. The first verify that
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
**A statement's Lean docstring is part of `formal_statement`**, since everything but the
`import` lines goes into that field — so the prose inside `/-- … -/` freezes too, while every
other piece of prose on the platform stays patchable. Give a docstring the scrutiny you give
the statement, not the scrutiny you give a description you can fix later. Cheaper still:
keep docstrings short and put the discussion in `natural_language_statement`, where a
correction costs one PATCH instead of a burned name.
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

## When the sentence outruns its citation

The variant trap is the development drifting from the source. This is the mirror image: the
*source's own sentence* claims more than the results it cites deliver, and formalizing the
sentence faithfully produces a statement nobody can prove.

Chou (1980), p. 400: "Now $C$ is finitely presented … By applying Lemmas 1 and 2 of Milnor we
conclude that $A$ is finitely generated." We published exactly that, twice. But Milnor's Lemma 2
concludes only that $A$ is *normally* generated by finitely many elements; the passage to finite
generation is his Lemma 3, stated for a **polycyclic** quotient, whose proof spends polycyclicity
on the normal form that makes the induction finite. Chou's own use is sound, because his quotient
is almost nilpotent; the sentence, read literally, is not supported. The statement turned out to be
true unless a finitely presented group of intermediate growth exists — an open problem — so as a
milestone it was a trap that could absorb unbounded solver effort.

What makes this one hard to see: the sentence is *true in context*, the author is not wrong, and
the hypotheses the author actually has are stronger than the ones the sentence names. A read-back
cannot catch it, because the Lean says exactly what the prose says. Only reading the cited lemmas
catches it.

So, whenever a statement's justification is a citation rather than a proof on the page:

- Read the cited results yourself, in their own source, before publishing.
- Check the hypotheses the author *has* at that point against the hypotheses the sentence *names*.
  Where they differ, the narrower ones are usually the honest statement.
- Prefer the hypothesis the cited proof actually uses. Here, "the quotient is virtually polycyclic"
  is both what Milnor proves and what every use in the paper supplies, and the corrected statement
  needs no finite presentation at all.
- If it is already published: the statement is frozen, so publish the corrected one, relink the
  milestones with a `reason`, and patch the old statement's prose to say what its cited argument
  does and does not give. Do not leave an unprovable statement carrying a milestone.

## Publish the statement before the proof

Publishing a statement with no solution leaves it `Open`; milestone it, and someone may close it.
The duty that comes with it: type-check, work the proof far enough to be confident (close the
constant arithmetic), and write the route into the milestone. A prose argument for a side claim
in a description can be retired into a citation by publishing the claim as its own `Open`
statement; pin its objects by pointwise hypotheses rather than a new definition, and keep
`source` honest about what the source supplies.

### A solution must not redeclare the target's name with a different signature

A `/verify` submission is compiled in an environment that already declares the target theorem.
If your solution file declares that **same full name** with a signature that is not identical,
the verdict is `WA` with

    expected token
    Unknown identifier `<your target's full name>`
    Unknown constant `_check`

— a parse-style error, **with no location**, that looks nothing like a name collision and
survives every local check: the merged file builds clean and the server-shape recheck (re-elaborate
the published `formal_statement`, discharge it with `solution`) passes, because locally nothing
else declares that name.

This bites when a development proves the target under its own name and the solution is assembled
by concatenating modules. An *identical* signature is harmless — one mission had a solution
redeclaring its target's exact name and signature and it was ACCEPTED — so the trap only springs
when the signatures differ, e.g. the module says `{G : Type u}` (a file with `universe u`) while
the published statement says `{G : Type*}`.

**Fix:** give the development's theorem a different name and let `solution` be the only
declaration matching the target. Do not "fix" it by editing the signature to match — the name is
the hazard, and a later edit can reintroduce the mismatch.

**Diagnosing a locationless `WA` generally.** Do not guess at syntax. Bisect with submissions
against targets where a `WA` costs nothing — an already-`Proved` theorem, or one that already has
an accepted sketch — changing exactly one thing at a time:

- same file, *different tail* proving some other theorem → isolates content from target;
- a known-good small solution *plus the suspect import* → isolates the import.

Two such submissions localised the above in minutes after two blind fixes had failed. Rule out
size first from the record: a 102KB solution had been accepted, so a 70KB one is not too big.

### Find an inlined sibling by its statement, never by its name

An edge in the mission graph exists only when a *solution* carries `import Theorems.Thm_<name>`.
A solution that re-proves a published sibling inline creates no edge, so a mission whose files
each re-derive their prerequisites renders as disconnected nodes hanging off its definition
bundles — which is how a human notices, by looking at the graph.

Finding the inlined copies is the whole job, and **a name-keyed scan is the wrong tool**, twice
over. It misses copies the development renamed: `isSDP_marks` for the published
`isStandardDyadicPartition_marks`, `exponents_getLast_eq_zero` for `getLast_exponents_eq_zero`.
And matching `<name>\b` against a *primed* copy silently succeeds, because `\b` sits between a
letter and `'` — so the extracted signature starts one character early, carries the apostrophe,
and an identical statement reports as a variant differing by exactly one character. On CFP §2
that pair of defects hid 12 of 25 copies and mislabelled 6 more as variants needing mathematical
work they did not need.

**So key the scan on the normalised statement and ignore names entirely**: parse every top-level
declaration, normalise whitespace from the binders to `:= by`, and look each one up in a map from
published statement to published name. Then excise the block, import the published theorem, and
rename the remaining references. A renamed copy costs one extra rewrite of its call sites and
nothing else.

**Rewrite the call sites to the fully-qualified name, never the bare one.** When the excised
copy had a different local name, its uses must be renamed — and `Foo.bar`, not `bar`. A short
name only resolves when the published theorem's namespace is the file's own or is `open`ed, so a
solution in `namespace MilnorWolf` importing a `GroupFiniteness` theorem breaks; on our Chou
pass exactly one of eight files was cross-namespace and exactly that one failed to compile. It
failed with `rcases failed: x✝ : ?m.161 is not an inductive datatype` rather than "unknown
identifier", because the bare name bound to *something else* in scope. That is the real hazard:
here the wrong binding errored, but a bare name that happens to typecheck against a different
theorem of the same short name changes what the proof proves, silently. Qualify, and compile.

Where the local statement genuinely differs, the variant trap's remedy applies unchanged: publish
the general form as its own node, keep the milestone on the source's own statement, derive one
from the other, and relink with a `reason`. Establish that a variant *is* one before paying for
it — twice now the difference has been in my comparison tool rather than in the mathematics.

### Import only what the proof uses — the rest is dead code, not a dependency

A solution assembled by concatenating modules carries lemmas its target never uses. Replacing
one of those with an import does not add a missing edge, it asserts **a dependency that does not
exist**, and the file still compiles, so nothing catches it. Measured across our missions: of
163 copies of published theorems sitting in submitted solutions, only **37** are reachable from
`solution`. Chou: 0 of 57. CFP §3: 0 of 21. Wolf: 0 of 21.

So classify before rewiring. Build the file's internal call graph and mark what is reachable
from `solution`: reachable copies get the import, unreachable ones are simply deleted. Counting
*references* is not enough — a copy referenced only by another dead copy is still dead, and that
weaker test called 9 of our §2 removals live when they were not. I shipped those 9 as false
edges before running the stronger one.

A false edge is worse than a missing one: a missing edge understates the structure, a false edge
misstates it, and the graph is the thing a reader trusts.

**The dependency API exists** — `GET /theorems/:id/graph` (nodes plus edges, from `root_id`)
and `GET /theorems/:id/decompositions`, both documented in `missions.md` and `prove.md`. Probing
for `/dependencies` and `/dependents`, getting 404, and concluding there was no such endpoint
was my error; read the docs for the route name rather than guessing it.

**Deprecating a superseded reduction is safe when the new one is a superset, and the way to
know is the frontier.** `GET /theorems/:id/open-leaves` returns the open leaves under a theorem:
record it before submitting, re-read it after deprecating, and compare. On the Chou reduction
`isVirtuallyNilpotent_or_hasExponentialGrowth_of_elementaryAmenable` the new sketch added one
*Proved* child to the existing five, so the target kept its single Open child and the frontier
was the same three Wolf leaves before and after. Do that check rather than reasoning that it
must be fine: a reduction is the mission's decomposition, and getting it wrong moves the
frontier other people are working from.

**Every accepted submission adds its own sketch node.** Edges run
`child -> sketch-<submission_id> -> parent`, so a theorem with three accepted solutions shows
three sketch nodes, each with its own children, and `has_hidden_deprecated_sketches` reports
whether any are suppressed. Resubmitting a cleaner proof therefore **adds** a decomposition
beside the old one rather than replacing it, and an edge from a superseded submission — false
or merely redundant — stays visible until that submission is deprecated. Decide deprecation
with the human *before* resubmitting a rewired proof, and tell them this is how the graph
behaves: the choice looks free until you know it duplicates every node.
Then deprecate with `scripts/deprecate.py --keep NEW_SID OLD_SID… [--go]`: you name the proof
that stays, each id is checked against the detail endpoint, and a deprecation that leaves the
theorem un-Proved is undone. The mission scripts it replaces guessed the keeper as the newest
list row, which can be a proof deprecated long ago.

**Look a known theorem up by `theorem_name`, not by `q=`.** The keyword search is for
discovery; asked for a name you already know it is both noisy (`caret` matches "Treshchev") and,
under load, unreliable — in one batch it returned nothing for five theorems that exist and had
been submitted against an hour earlier, and the script skipped them as "not found". The exact
filter `GET /theorems?theorem_name=<Namespace>.<name>` is documented in `mission_solver.md`.
Retry any lookup whose failure would silently drop work.

`GET /submissions` is unusual in four ways at once: it **ignores `theorem_id`**, it **ignores
`offset`**, it returns your entire history whatever `limit` says (762 rows for `limit=5`), and
it **never reports `deprecated_at`** — only `GET /submissions/:id` does. So one call is the
whole list and the pagination loop you would write by habit never terminates, re-reading the
same page forever; and a script that filters the list on `deprecated_at` treats
already-deprecated submissions as live. Confirm deprecation state per row against the detail
endpoint. It carries no solution code, and its `status` is `ACCEPTED` in capitals.

A verify can come back `ERROR` with `Module compilation timed out after 300s` when the server
has to build a module the submission imports. That is the transient `prove.md` describes:
resubmit unchanged.

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
