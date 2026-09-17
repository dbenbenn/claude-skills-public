---
name: formalizing-a-paper
description: Workflow for formalizing a mathematics paper (or any written source with numbered results) in Lean 4 / Mathlib. Use when the task is to formalize, certify, verify, or check a paper, preprint, or book chapter — and whenever auditing an existing formalization for fidelity to its source. Covers keeping the Lean proofs close to the paper's proofs, tracking coverage, separating any new mathematics a gap in the source forces you into, and the recurring Lean/Mathlib pitfalls.
---

# Formalizing a paper in Lean

The failure mode of this work is not unsoundness — Lean prevents that. It is
**drift**: a repository full of true, sorry-free theorems that no longer
correspond to the paper anyone asked you to certify. Everything below exists to
prevent drift.

**Paired skill.** `prove2me` covers publishing a development to that platform — what freezes at
submit, how milestones and read-backs work, and the prose conventions it reviews against. This
file is the *artifact*, that one is the *venue*; when the task is formalizing a paper *for*
prove2.me, read both. Its "variant trap" section is the milestone-linking case of the fidelity
rules below.

## The two rules

**1. Reread the paper. Continuously.**

Not once at the start. Before formalizing each numbered result, open the source
and read *that result and its proof* again — the actual LaTeX, at the actual
line range. Your recollection of a proof decays fast and silently, and a
paraphrase you formed twenty theorems ago is not evidence. Keep the source
where you can `sed -n 'A,Bp'` it, and re-read on every one of:

- starting a new lemma;
- a proof that is fighting back (usually you are proving the wrong statement);
- writing or updating a status-table row;
- *any* audit finding, before acting on it.

**2. Follow the paper's proof. Depart only when necessary.**

Necessary means: the paper has a gap, or an error, or the step is genuinely
unformalizable as written. "I know a slicker argument" is not necessary. A
formalization whose proofs mirror the paper's is a certificate *of the paper*;
one that reaches the same statements by other routes certifies only the
statements. When you must depart, record it — see *Bookkeeping* below.

## Reading the LaTeX is not reading the paper

Rule 1 sends you to the source, and that is right: the source is the only place
the numbering and the exact hypotheses are unambiguous. But what you read there
is not what the paper's readers see, and three things leak across that gap.

**Macro names are not notation.** A paper writing
`\CostOf{\Size,\Shift,\Buffer}` may render as $m(n,k,b)$ — resolve the
`\newcommand` chain before quoting any symbol. In one case `\Cost` expanded to
`m_{#1}`, so the string "Cost" appeared nowhere in the PDF while appearing
throughout the formalization's docstrings, status table and published metadata;
its siblings `\SimpleCost`, `\EssentialCost`, `\RelCost` were $\mu$, $\psi$,
$f$ and had been quoted correctly, precisely because those also appear in prose.
Quote the rendered form, and say so if you must mention the macro.

**Numbers must be reconstructed, not recalled.** Numbered environments usually
share one counter (`\newtheorem{cor}[lemma]{Corollary}`), so kinds interleave:
Remark 1, Obs. 2, …, Thm 14. Extract them in order from the source *with comments
stripped* — one commented-out environment shifts everything after it. Two further
traps: numbering differs between an arXiv full version and a proceedings version
of the same paper, so cite one and record in the README which; and a paper may
write the same function with its arguments in different orders in different
places, so fix a convention and say that too.

**A statement's own sentence may understate what the paper proves.** English
statements routinely under-specify quantifier dependence, and the intended strength
lives in the result the proof *cites*, or in a remark just after. One corollary read
"Let $k$ … for a $\vartheta$-admissible configuration $\Gamma$. Then there are
$\vartheta' > 0$ and $C > 0$ …", which alone puts $C$ after $\Gamma$; its proof
invoked a proposition declaring $C = C(d,\vartheta)$ and adding "There is no further
dependence on $\Gamma$". Read the cited result before deciding which of two Lean
forms is the faithful one — otherwise you will publish the weaker as "the paper's"
and the stronger as "our improvement", exactly backwards.

**Cite the line, not the neighbourhood.** Every notation error in one audited
project came from reading around a result rather than reading it: a buffer
argument carried down from the two items above the one being cited (the
corollary switched from a relative $\beta$ to an absolute $b$ at its third
item), a symbol taken from a macro name instead of its expansion, a numbering
recalled from a remembered sequence. The Lean was right in every case; only the
prose describing it was wrong. When you cite result $N$, open result $N$.

**"Let $X$ denote …", followed by "we find", is a claim — not a definition.**
When a paper introduces a quantity operationally — *the number of moves the
method needs* — and then states a recursion it satisfies, formalizing that
recursion as the **definition** silently assumes the step. Everything downstream
then proves things about a recursion that nothing connects to the object of
interest. Whenever a definition in your development is a recursion the paper
displays as a numbered equation, check which way round the paper has it, and if
you have assumed the equation, put that in *Deviations* and name the equation.

## Fidelity is about statements, not just truth

Proving something true and stronger, or true and weaker-but-sufficient, is
still drift. Match the paper on all of:

- **Constants.** If the paper states `π²/(2θ²) + (T−1)π/(2|θ|)`, prove that, not
  a convenient `(T−1)π/|θ|` — even if the weaker form suffices downstream.
- **Generality.** If the paper defines a three-variable `μ(N, l, β)`, define
  that and derive the specialization you actually use, rather than only ever
  formalizing the specialization.
- **Naming.** Give each numbered result a Lean theorem named for it, even when
  it is a two-line corollary of something you already have. An unnamed
  intermediate result cannot be pointed at in a status table, so it silently
  reads as "not done".
- **Definitional consistency.** When the paper gives two descriptions of the
  same object (a recursion and a closed form; an algorithm's cost and an
  arithmetic formula), formalize *and prove* their agreement. That theorem is
  where a mis-transcribed definition surfaces.

## When the paper has a gap

Sooner or later the paper will ask you to believe a step it does not establish,
and closing it is research, not transcription. The two roles must not blur, or
the certificate stops meaning anything.

- **New mathematics lives in its own file**, excluded from the status tables and
  named as new in its own header. Nothing the paper's build needs may depend on
  it: the test is that deleting the file leaves the certification intact, and it
  is worth *running* that test, because a helper lemma written for the new work
  drifts into a paper file almost by itself.
- **No row is marked ✅ on the strength of mathematics the paper does not
  contain.** Cross-references from a row to the new file are useful and honest,
  but the row must say that is what they are.
- **Record what you proved cannot work.** A proof that a method is capped — that
  a hypothesis collapses to something already assumed, that an averaging set
  cannot exist — is a first-class result and belongs in the tables. It is what
  stops the next reader, or you in a month, from re-treading the same ground.
- State the residue as sharply as you can. "The gap" is not a deliverable; "the
  gap reduces to *this* inequality, and here is what a counterexample would have
  to look like" is.

## Bookkeeping

Maintain a status table in the README, one row per numbered result:

| Result | Paper | Lean | State |
| --- | --- | --- | --- |
| Fibonacci worst case `3n − 5` | Obs. 6 | `moveCount_fib` | ✅ proved |

This table is the audit instrument, not documentation garnish. Rules:

- Every numbered statement in scope gets a row, including ones you skipped.
- Update the row **in the same commit** as the proof. A stale 🚧 next to a
  proved theorem is the exact drift this is meant to catch.
- Keep prose sections for **Deviations** (each departure, with why) and **Not
  attempted** (each omission, with why — "empirical benchmarks", "the paper
  obtains this numerically, not by proof"). Honest omissions recorded in the
  README are a finished deliverable; silent ones are a bug report waiting.
- Periodically check the table's Lean names still resolve: a rename leaves a
  dangling row that reads as coverage you do not have.
- **Prose drifts faster than tables.** Every time a result moves the frontier,
  grep for the sentences that *state* the frontier — "open in dimension three",
  "what remains is" — and fix all of them in that commit. Left alone they
  accumulate into a document that contradicts itself section by section, which
  is worse than one that is merely out of date.
- **Docstrings are part of the audit surface**, not decoration. "No hypothesis
  at all" above a signature carrying four hypotheses is exactly the drift the
  tables exist to catch, and nothing checks it but you.
- **Keep the tables renderable.** A `|` in a cell ends the cell, backticks or
  not; `|f|²` and `{x | P x}` silently split a row into extra columns. An audit
  instrument nobody can read is not one.
- **If you report findings to the authors, cite the witness.** Every defect you
  claim should come with the Lean name that establishes it, so the claim can be
  checked — or contradicted — without taking your word for it. That is the whole
  point of having done it in Lean.

## Working rhythm

- **One result, one commit** while transcribing; one *idea* with its supporting
  lemmas once you are past the paper and doing research. Commit messages that
  name the paper's result ("Audit item 3: the Fibonacci worst-case family
  (Observation 6)") make the history itself a coverage record. Push often.
- **`sorry` is a loan, not a lie.** It is fine mid-proof; it must be zero at
  every commit you call finished. Check with `grep -rn 'sorry' --include='*.lean'`.
- **`#print axioms` on everything the README cites**, not just the headline
  theorems — an axiom creeps in through a dependency, and the cheap check is the
  whole set. Generate the batch rather than curating it: extract every `Foo.bar`
  name from the README, emit a file of `#check @Foo.bar` and `#print axioms
  Foo.bar` lines, run it, and grep the output for `sorryAx` and for any name
  outside `[propext, Classical.choice, Quot.sound]`. The `#check` half doubles as
  the dangling-name check.
- **`#guard` numeric spot checks** on definitions before proving anything about
  them. A definition that computes the wrong number on `n = 21, k = 8` will
  otherwise cost you a day of failed proofs. Note that `decide` cannot reduce
  well-founded recursion — spot-check by unfolding the recursion lemma instead.
- **Build clean before reporting.** `lake build`, plus the sorry grep, plus the
  axiom batch. Say which of these you ran.

## Auditing an existing formalization

Run a dedicated fidelity pass, separate from writing new proofs. Read the Lean
proof *next to* the paper's proof of the same result and ask: same statement,
same constants, same generality, same argument?

Two things to expect:

- **Findings are hypotheses.** Verify each against the source before fixing it.
  In practice a finding like "the Lean proof carries a spurious log factor the
  paper's proof does not" inverted on re-reading: the paper's own bound carried
  the log, and the Lean proof was already faithful. Re-read first; a fix
  applied to a misremembered paper is pure damage.
- **Check the definitions, not only the statements.** A statement is only as
  faithful as the definitions it names, and the content often sits in a custom
  index set or constant that the statement merely mentions. The highest-yield
  audit is a *blind read-back*: hand an independent agent only the declaration,
  its preamble, and the definition files it imports, and ask what the code
  literally asserts — no paper, no docstrings, no statement of intent. Then
  compare that against your own description. Rereading cannot catch an error
  where your description and your understanding are wrong together; an auditor
  who has never been told the intended meaning can.
- **Gaps and departures are the same problem.** A departure from the paper's
  argument is very often *where* a gap hides — the proof was rerouted because
  the paper's route was hard. Fixing fidelity tends to close gaps for free.

Collect findings into an ordered list first, fix in order, report at the end.

## Lean/Mathlib pitfalls

See `references/lean-pitfalls.md` for the recurring tactic-level failures
(cast unification for `linarith`, `omega` and nonlinear atoms, `gcongr`,
`decide` vs well-founded recursion, Fibonacci index conventions, and others).
Consult it when a proof fails for reasons that look mechanical rather than
mathematical.
