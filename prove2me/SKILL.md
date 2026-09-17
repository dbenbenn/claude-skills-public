---
name: prove2me
description: Working with the prove2.me platform — publishing Lean theorems and definitions, curating a mission's milestones, and keeping what is published faithful to the source it certifies. Use when uploading a formalization to prove2.me, drafting or editing a mission proposal, linking or auditing milestones, or answering questions about what the platform allows.
---

# prove2.me

The platform's own documentation is **canonical**: `references/` in the prove2.me Lean
workspace (the `prove2me_workspace` checkout; the scripts here find it through
`$P2M_WORKSPACE`) holds `mission_captain.md`, `mission_solver.md`, `missions.md`, `contribute.md`,
`discover.md`, `prove.md`, `communicate.md`, `upload_full_project.md`. Read the
relevant one *before* designing anything, and quote it when it conflicts with an
instruction — the platform's semantics should win, and the captain would rather hear
the conflict named than have it quietly split.

**Paired skill.** `formalizing-a-paper` covers the other half of this work — producing a Lean
development faithful to a written source, and auditing one for drift. This file is the *venue*
(what the platform freezes, publishes and reviews); that one is the *artifact*. When a mission
formalizes a paper, both apply; general Lean/Mathlib pitfalls belong in its
`references/lean-pitfalls.md`, not here.

This file records what the docs do not say, learned by doing.

## The one irreversible thing

**`formal_statement`, `theorem_name`, and definition code are frozen at publish.**
Everything else — `theorem_title`, `natural_language_statement`, `source`, `tags`,
and a solution's `explanation` — stays patchable forever, definitions included.
(`PATCH /theorems/:id` takes `theorem_title`, `natural_language_statement`, `source` and
`tags`. **`contribute.md`'s "Update Your Theorem" table omits `theorem_title`, and the table
is wrong** — verified patchable against the API on a 227-theorem upload
(`prove2me_workspace` commit `e40e88b`, which fixes `upload_full_project.md` but not
`contribute.md`). `preamble` is *not* patchable, so it freezes with the statement.)

So the irreversible surface at a direct `POST /submit-problem` is exactly four things:
`theorem_name`, `formal_statement`, `preamble`, and a definition's code. Titles and all
prose are recoverable. Budget your pre-publish scrutiny accordingly — and note the
canonical docs can be incomplete, so when a field's mutability decides how much care
something needs, check the API or ask, rather than trusting the table.

**Publish is not the same moment as the POST.** Two paths reach it:

- `POST /submit-problem` / `/submit-definition` publishes immediately — there the
  POST *is* the freeze point.
- A **mission proposal** does not. Every draft item stays fully editable — statement,
  definition code, preamble, title, prose — until your human clicks **Submit
  Proposal**, and since a recent platform change they can now edit statements
  themselves on the confirmation page. So while the proposal is a `Draft`, *nothing
  is irreversible*: re-`PATCH` the item and re-upload the definition body as often as
  a correction requires. Do not carry over the belief that a drafted statement is
  already committed — that was true earlier and is not any more.

**Milestone prose lives on a different endpoint from the theorem.** A draft item's
`PATCH /mission-proposals/:id/items/:item_id` accepts only `theorem_name`,
`theorem_title`, `formal_statement`, `natural_language_statement`, `preamble`,
`source`, `tags`, `readback`, `readback_model` — it rejects `milestone_title` and
`milestone_description` outright, even though a GET of the proposal returns them on
the item. Those two go to `PATCH /mission-proposals/:id/milestones/:item_id`
(keyed by the *item* id, not a separate milestone id).

**Never probe a write endpoint against live prose.** Guessing a URL with a dummy
payload is how you find the route, and a PATCH that succeeds has already destroyed
the field. Snapshot the whole proposal to a local file first and probe with the real
replacement value, so the worst case is a no-op rather than a silent overwrite of
text nobody has a copy of.

Two habits follow from the second path. A statement edited in the UI is **not
type-checked** there, and `mission_captain.md:205` fails the *whole* submit if any one
draft fails to compile — so re-fetch and rebuild every item in server shape
(`preamble + formal_statement`) before Submit. And an edited statement leaves its
read-back testifying about the old artifact; re-run the auditor.

Consequences, all of which cost real work when discovered late:

- **A published statement cannot grow.** If the paper's result is a conjunction and
  you publish two of its three clauses, you cannot add the third under that name.
  Publish under a new name, keep the old one (it is still true), and patch the old
  one's description to point at the new. A burned name is survivable; a name behind
  a *different* statement is the drift the whole project exists to prevent.
- **Get the statement right before publishing, not the proof.** Type-check it, and
  close whatever arithmetic could turn out wrong, before it is *published* — the
  POST for a direct submission, the Submit for a proposal.
- **Verify mechanically that the published statement matches the repo's**, by
  normalising whitespace and comparing strings. Do not trust that you wrote the same
  thing twice.

## Re-check the library *during* a long mission, not just before it

`mission_captain.md:14` says to search the library before drafting. That is not sufficient for
a mission that stays in Draft for days: someone else can close your goal while you are polishing
it. On one mission I ran seven audit passes over the prose of a van Kampen proposal; the entire
theorem — including the hard kernel half — was published and proved by another captain on day
one of that stretch, and I did not notice because I never re-ran the search.

One call is enough: `GET /theorems?tags=<your tag>` or `GET /theorems?q=...`. Run it at the start
of every working session on a Draft proposal, and always immediately before Submit. Cheap, and
the failure mode it prevents is total: a mission whose milestones point at solved problems is
worse than no mission, because `mission_captain.md` warns that curating targets that waste
solvers' effort is the one thing a captain must not do.

Corollary for the salvage decision: when your goal is already proved elsewhere, the mission dies
even if your decomposition is better. Milestones are an attack path, not a record. What can
survive is any *public definition* or *reusable lemma* the other development kept private inside
its proof — publish those on their own merits, not as milestones.

## Milestones are an attack path, not a coverage index

`missions.md` tells solvers to look for a milestone whose theorem is `null` or
unproved, and `mission_captain.md` says the goal theorem is never a milestone. So:

- **An unlinked milestone says "formalize this."** Never use one to record something
  out of scope — it reads as an endorsed target and will waste someone's time.
- **A milestone linked to an `Open` theorem is the ideal live target**: the solver
  gets a known-good statement instead of a blank.
- **Omission costs nothing** — "a milestone's absence doesn't mean not needed."
  Coverage boundaries belong in the mission description, not in the milestone list.
- One `theorem_id` per milestone; there is no array form. When the source's statement
  really is a conjunction, the fix is a Lean theorem shaped like the source's
  sentence, not a second link.
- `sort_order` is settable and is *not* logged to history, so reordering is free.
  Title must start with the source index ("Lemma 3.2 — …").
- **Milestone numbers come from the milestones endpoint's own order, not `item_order`.**
  That list excludes definitions, references and the goal, and can start anywhere in the
  source's numbering, so your count off the item list will not match the number your human
  reads on screen. Fetch the list before acting on "milestone 12".
- **`GET /missions/:id/milestones` truncates silently at 20.** It returns a `pagination` key
  and no warning, so a list that "still shows 20" after your POSTs looks like a failed write.
  Always pass `?limit=100`, and trust the write's `201` over a short read.
- **After a live edit, the proposal snapshot lies.** `PATCH /missions/:id` updates the mission's
  description, but `GET /mission-proposals/:id` keeps the frozen text from submission — so a
  read-back there will show your edit missing and tempt you to re-apply it. There is no
  `GET /missions/:id` (405); read the live copy out of `GET /missions?limit=…`.
- **A published statement is not final**: `PATCH /milestones/:id` with a new `theorem_id`
  and a `reason` relinks the milestone, so a defect found after launch is fixed by publishing
  a corrected statement and swapping the link — not by softening the description to match.
- `DELETE` cascades the milestone's edit history with no undo. Archive the
  description first; confirm with the user.

## The variant trap — the most common defect by far

**The theorem a development proves is chosen for what the proof needs. The theorem
the source states is chosen for what reads well. They differ more often than not,
and the milestone will be linked to the wrong one.**

In one paper this recurred five times: Corollary 3.6, Theorem 5.15, Proposition 5.14,
Lemma A.1, and equation (15) were each milestoned to the variant the development
used, not to the source's own statement. Each was found only by reading the source
sentence against the linked Lean.

How they hide:

- **A quantifier hoisted.** The source's sentence introduces a constant after the
  data, but a later sentence — or the proposition its proof cites — pins the constant
  to fewer parameters. *Read the result the proof cites, not just the statement.*
  In BKS, Corollary 3.6's `C` looks `Γ`-dependent until Proposition 3.5 says
  `C = C(d, ϑ)`, "no further dependence on `Γ`".
- **A spurious hypothesis.** The development adds a cap the source never states
  (`ϑ ≤ π/2`), harmless downstream but not the source's statement.
- **An invented object.** The development builds a structure to repair a gap — a
  "choice graph" for a non-unique majority cone — and proves connectivity there.
  The source's proposition is about a different graph. Note that such variants are
  often *incomparable*, not stronger: ours also assumed `ℓ ≥ 1`.
- **A trailing clause dropped.** "In particular, if Ω is a ball, the constant can be
  chosen independently of Ω" is a second assertion, not a corollary of the first.
- **A step reformulated.** The source converts both sides of an inequality; the
  development converts one, because that is all the limit argument needs.

The remedy is always the same and always cheap: publish the source's own statement,
derive it from the variant in a few lines, link *that* to the milestone with a
`reason` on the swap saying the old link is not a rejected path, and name the variant
in the description. Both stay published; both are true.

## Publish the statement before the proof

The platform's collaborative point. Publishing a statement with no solution leaves it
`Open`, milestone it, and someone else may close it. Worth doing whenever the proof is
more than an afternoon.

The duty that comes with it: `mission_captain.md` warns that curating a false or
unaudited milestone wastes solvers' effort. So before it goes public — type-check the
statement, work the proof far enough to be confident (skeleton with `sorry` at the
routine steps, but *close the constant arithmetic*), and write the route to a proof
into the description so an attacker is not starting cold.

**A second use: retire a prose argument into a citation.** `submit-problem` *requires* the
statement end in `:= by sorry`, so publishing an unproved statement is the platform's normal
order of operations, not a loophole. When a description is carrying a paragraph of hand
argument for a side claim, publish that claim as its own `Open` statement and cite it instead.
Two things make this cheap: the statement needs no definition bundle if its objects are pinned
by pointwise hypotheses — `(M : ℝ ≃o ℝ) (hM : ∀ y, M y = 2 * y)` rather than a published `def`
— and `natural_language_statement`, `source` and `tags` stay patchable afterwards; only
`formal_statement` is immutable. Two cautions. An `Open` link carries no proof, so a reader who
does not click gets nothing: keep one clause of the reason in the prose and let the link carry
the precision. And `source` must stay honest — where the source supplies the objects but not
the conclusion (a witness the paper never draws), say exactly that in the field rather than
citing it for both.

Closing one later is the ordinary `/verify` flow, with two things the docs get wrong or leave
open. The `202` from `POST /verify` tells you to poll `GET /submission/{id}` — that **404s**;
the working forms are `GET /verify?submission_id=…` (as `prove.md` documents) and
`GET /submissions/{id}`. **The first `/verify` that imports a freshly published definition can fail
with "Verification timed out after 300s"** while the verifier builds the new bundle on
demand — a 6,000-line file that compiles locally in 27 s did, and the identical resubmission
a few minutes later was ACCEPTED. Resubmit before touching the file. And a *solution* file may carry its own helper `def`s and lemmas: the
"never local `def`s" rule governs a statement's `preamble`, not a proof. Put helpers in their
own namespace and leave `solution` at top level. Before submitting, pull the published
`formal_statement` back from the API, re-elaborate it locally as a fresh declaration, and
discharge it with `solution <binders>` — that is the type check the server runs, so it turns a
WA verdict into a local compile error instead of a queue round-trip.

## A description is not publishable until someone blind-reads it

**Treat blind read-back as a required step of publishing, not an optional audit** — including
milestones added to a mission that is already live, where there is no Submit gate to stop you.
Before a `natural_language_statement` or `milestone_description` goes up, hand an
independent agent the declaration, its preamble and the definition files it imports —
and *not* the prose, *not* the source, *not* your intent — and ask what the code
literally asserts. Then compare. Only publish what survives.

Measured across 277 descriptions on one mission: **4%** defective when written against the
source, rising to **32%** for research code written minutes after reading the statement.
Writing the description immediately after reading the Lean did **not** help — rereading cannot
catch an error where your description and your understanding are wrong together; only a reader
who was never told the intended meaning can. Full table in `references/audit-evidence.md`.

**The single biggest source is copying a sibling.** Near-identical statements — a lemma
and its primed twin, seven instances of one template — get their descriptions copied,
and *copying preserves exactly the parts that should have changed*:

- A twin's **display formula** carried over unchanged while a trailing sentence noted the
  difference. The prose then contradicted its own display — and a reader takes the display as
  the claim.
- One ambiguous boilerplate sentence replicated across seven descriptions, each copy locally
  plausible, all seven wrong the same way.
- A reused **formalization note** — a *rationale*, not a claim — silently licensed dropping a
  conjunct from four conclusions. It read "since the generators commute the order is immaterial,
  and no commutativity hypothesis is needed to state it", true of the ordered-product *encoding*
  and false as a reason to omit commutativity from what is *proved*; four statements went up
  asserting independence where the prose promised a free abelian basis. A carried-over rationale
  is the most dangerous thing to copy, because it reads as already-audited reasoning: **re-derive
  what a reused note licenses, against the new conclusion.**

Two further cases, with the declarations named, are in `references/audit-evidence.md`.

So: **audit siblings against each other, not only each against its own Lean**, and never
repair a copied display with an appended sentence — rewrite the display.

This check tests prose against Lean. It cannot catch the *variant trap* above, where the
Lean is described faithfully but is the wrong theorem for the source. Both checks are
required, and they are independent.

## The read-back is a published artifact, not your audit notes

`readback` is testimony, not your notes on what an auditor told you. `mission_auditor.md`
specifies it: what the declaration *literally asserts* — no judgment, no advocacy, mathematics
rather than Lean syntax, one self-contained paragraph. It is recorded permanently beside the
published theorem, moderators read it at review, and your human compares each statement against
it at Submit. A read-back that does not state the claim defeats the step it exists for; I got
that wrong across a whole mission by filing audit reports there (`references/audit-evidence.md`).

So run **two passes and keep them apart** — and expect the merge to recur, because the audit
material is the interesting part and it drifts back under the read-back's name. Mine did, months
after I wrote this rule: a four-section testimony with a *Name check*, 233 Lean identifiers and
zero KaTeX spans, against a spec that asks for one self-contained account in plain mathematical
English with no judgment. **Re-read `mission_auditor.md` against your brief periodically**, and
mechanise its checks on the publishable file: no Lean identifiers, no `file:line`, no naming
verdict, math spans present. Easy requirements to lose that way — every implicit argument and
typeclass assumption, non-standard definitions expanded inline, and vacuous or degenerate
hypotheses, which the platform calls the classic faithfulness trap.

The shape that works is **two files from one blind reading**: a publishable read-back, and
captain-side notes holding the conventions-with-citations, the absences and the name check.
Splitting them across two blind agents buys nothing — same inputs, no mutual check — and costs
the correspondence between the citations and the testimony actually published. Write the
read-back first: a verdict reached first is one the rendering can be written to fit.

The *audit* gives you truth, vacuity, traps, name-fit
— for you, and it belongs in your prose or nowhere. The *read-back* gives the artifact's
testimony, for the field; its author gets only the declaration, its preamble and the spec, never
the informal statement, the source, or your intent. Re-run it whenever the Lean changes: a
regenerated artifact re-enters the audit queue, it does not inherit the clean bill of what it
replaced.

**The tuned brief and the staging tool are in `scripts/`, next to this file.** Use them, do
not rewrite them from this doctrine: `scripts/readback-brief.md` is the text the auditors
actually get (its captain-only rationale is kept out of this public repo, in the private
`claude-private` repo beside the memories, and must never be staged with it), and `scripts/stage_auditor.py stage|collect|teardown` seals one auditor in a
directory holding only the brief, its task files, a probe wrapper and an empty `scratch/`. Both
were tuned across two missions (the leaks and litter in `references/audit-evidence.md` are what
they fix). Strip comments and docstrings from the staged Lean first — a docstring is prose.

#### The brief is the N-way artifact

Every other artifact fails one at a time; the brief is an input to *every* read-back, so a defect
in it corrupts all of them at once. Commit it **before the first auditor runs** and have your
human review it alongside the statements.

**Never hand an auditor a convention.** Explaining the multiplication order, or what a bracket
expands to, plants your reading of exactly the points where a formalization goes wrong while
still compiling — and the testimony comes back echoing you, uncited. Withholding alone fails too:
auditors then guess or hedge. The distinction is that **letting them read the libraries is
legitimate — that is the language the statement is written in — while telling them a convention is
contamination.** So:

- Let them grep Mathlib and Lean core freely, and elaborate probes against them.
- Require a **citation per convention** — file, line, declaration — so the reading is re-checkable.
- Require an explicit flag with **both readings** for anything unsettled, so ambiguity surfaces as
  a finding instead of resolving in your favour.
- Say the body is deliberately `:= by sorry`, or they report the missing proof as a defect.
- Name **one working directory** and express task files, libraries and a probe directory relative
  to it; require library-relative citations plus the library revision, since line numbers drift.
  Auditors cite the paths you hand them, and on a draft mission a submitted `readback` is
  published for good. Check afterwards for probe files they left in the workspace.

**Keep the rationale out of the brief.** Doctrine, history and measurements go in a sibling file
marked captain-only, and the prompt names the exact files the auditor may open. My own fix failed
first time because I put its reasoning — which quoted the convention — in a blockquote atop the
brief, and blockquotes are not comments. Two subtler leaks: *enumerating which* conventions to
check steers attention to your own development's traps, so name kinds of Lean notation generally;
and an example citation containing a real file and line hands over the answer.

**Stage each auditor in its own directory, and make teardown your job.** Give it only the brief,
its task files, a symlink to the shared libraries, an empty per-auditor `scratch/`, and a wrapper
that elaborates a probe with the lake project as cwd. The auditor then never visits the repo, so
the captain-only doctrine file is unreachable *in practice* rather than merely forbidden, every
path is relative (which is what keeps absolute paths out of the citations), concurrent auditors
cannot collide, and cleanup stops depending on auditors who do not do it. Be honest that this is
not enforcement: a Claude Code subagent cannot be containerized — its file tools run outside any
container — so isolation buys scratch hygiene, not blindness. What staging buys is that a lapse
is no longer invited by the layout. **Check that sealing did not cost probe elaboration**: an
auditor that can only grep takes an instance declaration on trust.

Measurements for all of this — echo rates, what the clean brief surfaced, path leakage, sealed
versus unsealed — are in `references/audit-evidence.md`.

#### Never edit a read-back. Re-run it.

Its value is provenance: it certifies what an independent blind reader said the Lean asserts. Edit
it and it certifies what the captain was willing to publish, and no downstream reader can tell a
cosmetic edit from a substantive one — so there is no small fix here. The only changes are
re-running the auditor with a corrected brief, or changing the Lean and re-running; archive
superseded testimony with a note on why.

I broke this on a two-word deletion, stripping a leading "Again " — content-neutral, which is why
it felt safe and why the rule is absolute. Note what did not save me: the rendered record labels
that field "auditor testimony — do not edit", my own label, and I edited through it. **A warning
in your own tooling is not a control.** The control is having no procedure that ends in you typing
there. When something genuinely cosmetic is wrong — heading depth, a leaked path — fix the *brief*
and **record the discrepancy**, and do not let a renderer quietly normalize it either.

#### Doc comments on a published definition are an unaudited surface

A read-back audits the *statement*; a `natural_language_statement` is audited against the Lean; a
doc comment inside a published definition body is neither — and it is published, and read on
trust. One asserted that a definition was *equivalent* to the source's phrasing, which is exactly
where a definition could stop matching its source with no audit noticing. Either prove such a
claim somewhere in the mission and say where, or do not assert it in the comment. A sealed
auditor found this; it had only two files to read and so read them harder.

#### Batching is fine; self-containment is not optional

Fanning one auditor across several declarations is fine, and siblings then describe the same
ambient type in the same words. The cost is that the batch leaks into the prose: read-backs came
back opening "Again …" and "As above, …" — back-references to a sibling the reader never sees,
since each is published on its own theorem's page. `mission_auditor.md` asks for one
self-contained paragraph per declaration; put that sentence in the brief. One exception, worth
checking before you delete: a *definition bundle's* read-back is a single numbered document
covering several declarations, so "the previous one" inside it is correct.

## Audit the draft against the platform's own rules

Checking prose against its source, and checking it against a reader, will both pass a draft
that breaks the platform's documented requirements — those are a third axis and nothing else
looks at them. Read `references/mission_captain.md`, `contribute.md` and
`mission_description.md` *as a checklist* and go field by field. On one proposal that had
already survived a dozen audits this found four blocking defects: every `source` lacked the
required URL and page number, the goal item's statement carried a proof sketch the rules
forbid, the description stated no Lean representation at all, and the required
rule-out-a-trivializing-formalization sentence was missing. None was findable by any other
kind of audit.

**And check that your copy of the rules is current.** Mine was four commits stale; the rules I
had relied on were unchanged, but one that had changed governed name uniqueness at submit. The
rulebook is a date-dependent claim like any other.

## Auditing

Four axes, and no one of them sees another's defects. **Against the source** — does the prose
claim what the paper claims. **Against a reader** — comprehensible, non-redundant, ordered.
**Against the platform's rules** — the section above. **Against your own fixes** — below,
because repairing a finding is where new false claims enter. Separate passes, separate briefs; a
pass told to do two of these does neither. Measured results for all of it are in
`references/audit-evidence.md`.

### Accretion, and how to measure it

Correctness auditing has a failure mode that more correctness auditing cannot fix: each round
finds a real imprecision, the cheapest repair is an added qualifying sentence, and after five
rounds the passage is entirely true and unreadable. The tell is *corrective voice* — "the
temptation is to attribute each to the wrong place", "A caution about that minimum" — where every
warning exists because an audit caught the **author** erring. The reader is being talked out of
mistakes they were never going to make.

Do not wait to be told, because it is measurable: words per field and per sentence (an outlier at
twice its neighbours is the signal); shared 10-word n-grams between every pair of fields, which
finds duplication no reader would report politely; counts of corrective markers ("Note that",
"caution", "do not", "it is not"); counts of process provenance. One number catches the spiral
live — **if the round grew the document, the round failed**, however right each fix was. The
exception is mandated growth, a round adding what a spec demands.

Then cut, and treat the cut as its own audit, because the risk reverses: a fact removed from
field A on the assumption it lives in B. Beware **sequential** trims especially — a fact cut from
a section as "belonging in the milestone", then cut from the milestone as "duplicating the
section", ends with no home at all.

### Responding to a finding: six options, not one

The spiral runs on a default: "X is imprecise" invites a qualifying sentence, which is locally
free and globally ruinous. Make the response an explicit choice.

1. **Delete** — the claim was false; remove it rather than explain it. Explanatory rewrites add
   claims and each new claim needs its own verification, so the cheapest correct patch is usually
   the smallest.
2. **Correct** — wrong words for right ones, same length.
3. **Relocate** — true, but belongs in another field. This is what one-home-per-fact buys you.
4. **Accept** — the finding is right and the precision still is not worth the words *here*.
5. **Decline** — the finding is wrong.
6. **Restructure** — three patches on one passage means rewrite it whole.

**4 is the one you will never reach for, and it is often correct.** That a sentence is imprecise
does not establish that it must be made precise. Precision has a home, usually downstream: a
description may be looser than a milestone, which may be looser than the Lean. Ask which layer
owes the reader this.

**"Lost from a field" is not "lost from the proposal."** An auditor comparing drafts sees deletion
where you relocated: one reported five losses, four of which sat exactly where the rule puts them.
Grep the whole proposal before restoring anything, and brief auditors on where facts may live.

**When a gap is exposed, ask whether the passage needs the claim at all.** Shown that a paragraph's
evidence did not establish its claim, I completed the argument in forty-six words — in a section
whose job is to say who cares. The right fix was the opposite: cite the counterexamples and stop.
Half-explaining creates an obligation to be complete; citing does not, and the passage ended
shorter than before the question was asked.

### Sweep date-dependent claims as their own pass

A source paper cannot report what happened after it was written, so a source check cannot see a
claim that has since gone stale: six audits against one mission's 1985 source all missed a
sentence false since 2002, and the owner caught it on a first read. Anything of the form "still
open", "remains", "no X
yet", "the first", "the standard test case" needs a *current* check, not a source check; so does
every claim about what a library lacks. Do it even when the mathematics is old and settled — the
mathematics does not age, the commentary around it does. Watch the follow-on trap: my repair
advanced the clock to 2002 and stopped there, reproducing the same error one decade later.

### Correctness and readability are different audits

Ten passes against the sources passed one mission fit to publish; the owner then found, on an
ordinary read, a paragraph opening "A caution about that minimum" in a section that had never used
the word. Neither that nor a clause asserting nothing checkable is a *claim* defect, so no
claim-checking auditor was looking. Run a pass whose only brief is the reader: dangling and
distant referents, symbols used before they are introduced
(a `g` in a one-variable statement; `M` and `T` defined nowhere), definite articles with no
referent, one object under three names, forward references, signposting that reads as assertion. It
returned 26 findings against text already declared clean — and the fixes introduced two fresh false
claims, so readability fixes need a correctness pass of their own. Milestones are read standalone
on the platform: one that leans on "the previous one" is broken for its actual reader.

### Quote the subject the source predicates it of

Three consecutive fix rounds each attached a verbatim quotation to the wrong noun — a remark about
a *result* hung on a *proof* being the clearest. The words were exact every time; the attachment
was not. Check what the quoted sentence's grammatical subject is, and mark bracketed substitutions
and ellipses. And **once a passage has three rounds of patches, rewrite it whole**:
patch-on-patch left a section opening with a premise its own later paragraph withdrew, a
contradiction no single hunk contained and so invisible to every per-hunk check.

### Titles are claims, and every compression is one

Titles sit outside every audit surface — statements are read against the source, read-backs are
written blind, and the one line most readers see is written once and never revisited. A title's job
is to compress, so audit it as a claim.

- **A substituted verb.** "Commutators *vanish* near a common fixed point", where Lean and source
  both say *is the identity* — and "vanish" further suggests the maps commute outright, stronger
  than the neighbourhood claim. Take the verb from the source, then grep the proposal for the word
  you replaced; it is rarely in one field.
- **A conjunction folded into a hyphenated adjective** stops meaning the conjunction. "Slope-one
  piecewise-linear maps" stood for *finitely many breakpoints, and slope one at each of the two
  ends*, but reads as slope one everywhere — a translation, hence commuting, so the non-abelian
  hypothesis becomes unsatisfiable and the theorem reads vacuous.
- **Notation is the cure, not the disease**: the source's own `PLF'(ℝ)` took one title from 139
  characters to 55. A title is neither a statement (check it does not duplicate the milestone
  description) nor aspirational — solvers find open work from a milestone's unproved *state*.
  Where sibling titles spell a condition out, the one that abbreviates is the suspect.

The same test applies to `theorem_name`, with a deadline: **a name that needs a caution is the
wrong name, and the name freezes at Submit.** A goal called `no_free_subgroup` carried a 52-word
paragraph explaining that the group does contain rank-one free subgroups; renaming it
`no_free_subgroup_of_rank_two` deleted the paragraph instead of the doubt. Prefer the word to a
subscripted abbreviation where binders can capture it: `no_f2_subgroup` reads as "the second `f`"
in a statement whose binders are `f` and `g`.

But **an auditor's name-check is a style opinion, not a fact.** Three blind auditors independently
flagged `image` in `pairwise_disjoint_zpow_image`, because no `Set.image` occurs and Mathlib names
track syntax — yet the sets genuinely *are* the images, and `Ioo` is Lean jargon where a milestone
is read as mathematics. Agreement among auditors working from one brief is strong evidence about
what a statement *says* and weak evidence about what it should be *called*; the brief asks for a
name check, which invites nits. Read the argument; do not count the auditors.

### The yardstick depends on the field

A `milestone_title` indexes the **source's** lemma — `mission_captain.md`: "start with the index in
the source … followed by a short label of the lemma" — so judge it against the paper, and let it
name a result stronger than what the mission formalizes. `milestone_description` states that lemma
in prose. `natural_language_statement` and the read-back describe **this declaration**, so judge
those against the Lean. Applying the Lean's yardstick to prose about the paper yields confident
wrong corrections: in one session it condemned a `PLF'(ℝ)` hypothesis that was faithful and a
"dichotomy" label that correctly named the source's theorem.

### Grep the mission's vocabulary before ruling on a term

A title qualifier, a section heading, a word like "bridge" or "vacuous" becomes load-bearing
taxonomy, and the project's own usage is the authority, not your sense of the English. I declined a
finding because "bridge" seemed wrong for a milestone that another item's description already called
a bridge step — two seconds of grep, and the title freezes at Submit. The same check catches
drift: one word carrying two senses in one
document is a defect even when both uses are individually defensible, and the fix is to change the
*loose* occurrence and leave the technically standard one alone.

### Auditing a *fix* is a separate job from auditing the text

Blind read-back catches defects in what is already published. It does not catch the ones you
introduce while repairing them, and those rates can be comparable — which is how four consecutive
audit rounds each find ~20 defects and never converge, the repair rate and the introduction rate
cancelling. The cascade does converge if each round gets smaller; the tables are in
`references/audit-evidence.md`.

So when the fix is prose, run a pipeline and commit nothing until it clears:

1. **Propose, don't apply.** Stage each edit with its exact anchor and the *full field as it would
   read afterwards*.
2. **Verify the after-text in full field context, never a diff hunk.** Every defect worth catching
   was invisible in the hunk. Where several edits land in one field the verifier must see them all
   applied, or nobody ever reads the field as it will actually end up.
3. **Re-audit every amendment.** An amendment is new text; the agent that wrote it cannot audit it
   and neither can you. In one round **five of seven rewrites were still defective** after their
   first audit — referent, mood, register, true-claim-wrong-reason.
4. **Gate it mechanically.** Hash each patch's current text against the text that was actually
   audited, and refuse to apply while anything is STALE or never audited. The first run of such a
   gate caught a patch I had verified and forgotten to record.
5. **Terminate.** A patch is done when a fresh auditor accepts it **unchanged**. If it will not
   settle, drop it — *unless the text it replaces is actually false*, in which case it has to be
   made to work.

Four things that will mislead you inside the loop:

- **A compiled probe settles the mathematics, not the sentence written about it.** One verifier
  compiled a proof that two statements were interderivable, then called one "logically weaker".
- **Cold-audit findings are not authoritative.** Two of ~38 were wrong, one propagating into three
  drafts. Verify a finding against the source yourself before editing off the back of it —
  including citations an auditor hands you: one supplied a DOI that resolved to a different article.
- **State every claim under the hypothesis your own document defines, not the standard one.** A
  mission whose Setting defined "piecewise linear" with a *discrete* breakpoint set then asserted a
  lemma for "piecewise-linear `f,g` of slope 1 at both ends" — under its own definition that lemma
  is **false**; it needed the *finite*-breakpoint subgroup. Read every claim back with the
  document's own definitions substituted in, and tell auditors to do the same.
- **An over-correction drops the other half.** Told that a lemma's second input was misattributed, I
  replaced the wrong citation with one right one — where the source cites two. Repairing "A, not B"
  to "C" is still wrong when the truth is "C and D".

Tell verifiers plainly that rejecting a proposal is a useful result, and that every amendment costs
another full round; otherwise they amend for style and the cascade never ends.

## When a milestone is too big, publish its steps

A milestone nobody can close is a dead end for solvers, and "it's the hard one" is not a plan.
The captain's move is to **read the source's own proof of that result and publish the steps**.
On one mission the last open milestone was a page-long argument; reading it yielded four
ingredients, three of them provable that day. Each went up as a theorem, was proved, and was
linked as a milestone ordered immediately before the hard one — so the list became an attack
path instead of a cliff. The fourth then went through, because every input existed.

Two things make this pay off beyond the one mission. Steps that are not about your source at
all — "an increasing homeomorphism of the line has no non-fixed periodic point", "a set covered
by finitely many connected subsets has finitely many components" — are better published as
standalone general theorems; they get reused, and the mission's own milestone list stays about
the paper. And the *unstated* steps are the ones worth hunting: the sentence "clearly, `z`
preserves each component" cost a lemma, and the half-sentence "a free group of rank greater
than 1 is neither metabelian nor …" cost another. A proof paragraph's difficulty is concentrated
in what it does not say.

**Weakening the conclusion can collapse the apparatus.** Where the source built infinitely many
conjugates and invoked its own independence lemma to get a free abelian group of infinite rank,
the rank-two form needed exactly two conjugates and two point evaluations — the whole
restriction-to-an-interval machinery went away. If a mission has already cut a conclusion down
to what the goal consumes, check whether the *proof* can be cut the same way before formalizing
the source's version.

## Keep the mission record under version control

**Tooling that travels with this skill (`scripts/`):** `p2m.py` (`call(method, path, body)`;
the api key is exchanged for a short-lived token, never sent directly), `submit_verify.py TID
FILE [EXPLANATION.md]` (multipart `POST /verify` with polling), and `merge.py OUT MODULE...`,
which concatenates shared solution modules into one self-contained submission — a solution may
import only the mission's definitions. `merge.py` dedups by *bare* declaration name and refuses
an unbalanced `namespace`/`end` count or a second `theorem solution`; both refusals encode a
verifier rejection that once took four submissions to diagnose, so run it rather than writing a
one-off `cat`. All three locate the Lean workspace through `$P2M_WORKSPACE` or the known paths.

**Version-track the mission record from the first file, and keep auditor inputs as evidence.**
For part of the record the repo is not a convenience copy but the *only* copy: `readback` is a
**draft proposal item** field, and reference items take none at all, so a milestone added after
launch — published through `POST /submit-problem` — has no way to receive testimony afterwards:
`PATCH /theorems/:id` rejects it outright ("Unknown field(s): readback. Allowed:
natural_language_statement, theorem_title, source, tags, deprecated, reason", checked
2026-09-17). The published theorem object does carry a `readback` key (null), so
`POST /submit-problem` may accept one at creation; that is untested — try it on the next
statement you publish directly, and never on a throwaway. On one mission that was 13 of 25 declarations. So keep
read-backs in their own directory, render them into the record next to the platform's own with
each one's provenance labelled, and **print an explicit marker for any declaration with no
read-back at all** — an audit gap you can see in `git diff` is one you will close.

**Render the record from the live mission, never from the proposal.** After launch the
proposal's `description` is a frozen snapshot, so a renderer fed `proposal.json` silently shows
pre-launch prose and omits every milestone added since. Fetch the live mission and milestones,
keep the proposal alongside it for the pre-launch audit trail only, and have one generator own
every copy of a field so two copies cannot drift.

A mission accumulates the live description, the statements, every audit input, and the patch
scripts. Put it under local git at the start — no remote while the proposal is a Draft, since
its content should not be published before the owner submits. The payoff is exact recovery: a
spelling normalisation swept thirteen files in one `sed`, including archived audit inputs that
recorded what auditors were actually shown, and without history it could not be cleanly undone
(some of those files legitimately contained both spellings). Keep the audit inputs in their own
directory and treat them as evidence — never bulk-edit them; if one must change, record the
discrepancy instead.

Belt and braces on that directory, and note that the obvious half does not work:

| write method | file `chmod u-w` only | dir `chmod a-w` only | both |
|---|---|---|---|
| `sed -i` | **succeeds silently** | blocked | blocked |
| shell redirect `>` | blocked | **succeeds** | blocked |
| `open(...,'w')` | blocked | succeeds | blocked |
| create / delete | n/a | blocked | blocked |

They miss opposite things: `sed -i` renames a temp file, so it needs the *directory* writable
and ignores the file's mode; a redirect truncates the existing inode, so it needs the *file*
writable and ignores the directory. Set both. Permissions are the tripwire, git is the
recovery — rehearse `git checkout --` rather than trusting the design, which is how the gap
above was found.

Track a rendered copy too. The record's source of truth is JSON, whose changed lines run to
thousands of characters with escaped newlines, so a prose edit does not diff. Export each prose
field to its own markdown file and commit that alongside. Render it from the **live API, never
from your local draft**: the two drift, and a defect read off a stale record buys a fix round
for a bug that does not exist. One stray blank line in a reference list was chased that way —
it was in the draft, not in what had landed.

## Writing the prose

`natural_language_statement` and `milestone_description` are the only parts a reader
sees. Write them as a mathematician would, in KaTeX, from the statement in front of you rather
than from a sibling's text, and make them say what the formal statement *actually* says — including where it is stronger or weaker than the
source, which hypotheses the source does not state, and which of its claims are not
formalized. Every `QFS.foo` you cite should resolve on the platform; check that
mechanically before publishing, and inline or publish the ones that don't.

For the mechanics of the upload pipeline — skeleton subtraction, definition bundles,
embedded theorems, and the traps that silently corrupt output — see
`references/publishing-pipeline.md`. For the measured results behind the audit rules above —
defect rates, the six-pass cascade, what one de-accretion pass recovered — see
`references/audit-evidence.md`; read it when you are tempted to skip a check.

### One home per fact

An item has two prose fields and they are not interchangeable:

- `natural_language_statement` — **what the Lean says**, plus fine print about the claim: what
  it does not assert, where it is weaker or stronger than the source.
- `milestone_description` — **why the milestone is in the mission and how you would prove it**:
  role, route, Lean hazards.

For every sentence ask: is this about the *statement*, the *proof*, or the *mission*? First to
the NL, the other two to the milestone. A milestone may name its conclusion in one orienting
clause; it may not re-derive it or repeat the statement's fine print.

Without the rule the fields converge. On one mission six of eleven milestone descriptions
shared ten-word spans with their own item's NL, one pair had its two jobs exactly swapped, and
applying the rule cut 952 words across twenty fields without losing a fact. Milestones display
standalone, so one that leans on "the previous milestone" or on a symbol bound only in its NL
is broken for its actual reader.

### Keep your process out of the published prose

"An independent audit verified that implication in Lean", "Two audits probed this statement
without producing a proof", "checked in Lean" — nine had accumulated in one mission. Delete
them. A published claim should be checkable from the prose, the source, or the Lean; an
unnamed audit is checkable only by trusting a process the reader cannot see. Worse, attaching
one to a one-line fact *implies the fact was in doubt*, so the reader stops to re-check
something they would otherwise have accepted.

Keep every statement about what the mission does and does not prove — "the infinite-rank form
is not formalized here", "no `Subgroup` object is constructed by these milestones". Those are
checkable against the mission itself, and they are the honesty that makes the rest credible.
