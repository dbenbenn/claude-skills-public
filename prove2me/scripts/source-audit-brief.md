# Source-side audit brief

You are checking a formalization against its mathematical source, from the source's side. You
work in two phases, and in the first you do not see the formalization at all.

## Phase 1: what the source sentence claims

Your directory holds `source.md` (the sentence under audit, quoted, with its page and label) and
the rendered page images `page-*.png` it comes from, including the pages that introduce the
notation it uses. Read the sentence **on the page image**, not only in `source.md`: the quotation
can lose a symbol, and the surrounding text is where notation and standing assumptions are set.

Write `claims.md`: every atomic claim the sentence makes, numbered.

- **C1, C2, …: claims.** One mathematical assertion each, in plain mathematical English with
  KaTeX. After each, quote the words that carry it.
- **H1, H2, …: hypotheses.** What the sentence assumes: its own "for every x ∈ S", "if …", and
  any standing assumption of the section or paragraph that it silently relies on.
- **Claims carried by notation count as claims.** Mark them *(notation)*. This is the category
  that gets lost. Examples of the kind of thing to look for:
  - writing an object in a notation that is only defined on some set asserts the object lies in
    that set (if $u = (u_0, u_1)$ is notation for elements of $S$, then "$x = (y, z)$" asserts
    $x \in S$ as well as the two components);
  - "$f : A \to B$" asserts $f$ is defined on all of $A$ and takes values in $B$;
  - "is a monomorphism", "is an isomorphism", "acts as …", "is a Klein 4 group" each unpack into
    several claims (well defined, a homomorphism, injective, …) -- list each one;
  - an equation between named objects asserts both sides exist and are defined;
  - "similarly", "in particular", "hence" introduce claims of their own.
- Claims about the sentence only: not its proof, not later results.
- Be exhaustive about the sentence, and brief about each claim.

When the list is complete, end `claims.md` with the line `END OF CLAIMS` -- write it last, and
only then: phase 2 starts from that line, so a list still being written must not carry it. Then
stop and reply in at most five lines: the number of claims and hypotheses, and which claims are
(notation). **Do not look for any formalization; there is none in your directory yet.**

## Phase 2: coverage (only when you are told to continue)

A file `readback.md` will then be added: a blind, plain-mathematics rendering of the formal
statement, written by someone who never saw the source. Compare it with `claims.md` and write
`coverage.md`:

- For each claim Cᵢ: **COVERED** (quote the part of the read-back that says it), **WEAKER** (it
  says something strictly weaker; say how), or **MISSING**.
- For each hypothesis Hᵢ: whether the read-back assumes it, and any hypothesis the read-back
  assumes that the source does not (**EXTRA** -- an extra hypothesis makes the statement weaker).
- **For every WEAKER or MISSING claim, give a near-miss:** a concrete object that satisfies the
  read-back's statement but violates the source's claim. If you cannot build one, say so -- the
  claim may be implied after all, and say by what.
- End with a verdict line: `VERDICT: faithful` or `VERDICT: gaps: C2, C5` (the claims missing
  or weaker).

Reply in at most five lines: the verdict and one line per gap.

## Rules

Work only inside your directory; read nothing outside it. Do not edit `source.md`, the images or
`readback.md`. Quote the source exactly.
