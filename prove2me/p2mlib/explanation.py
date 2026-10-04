"""Checks on a proof's `explanation` before it is sent to the platform.

prove.md asks every accepted proof to carry an explanation written like a section of a paper:
it opens with the statement in a display-math block, gives the idea, then the steps; no
commentary about the author or the platform, no "elegant" / "clever trick". 2026-10-04: 480 of
our 1053 accepted submissions had none, because submit_all never passed one.
"""
import re

PRON = re.compile(r'(?<![\w-])(he|him|his|she|her|hers)(?![\w-])', re.I)
CODE = re.compile(r'`[^`]*`|\$\$.*?\$\$|\$[^$\n]*\$', re.S)
BANNED = ('elegant', 'clever trick', 'beautiful')
MIN_CHARS = 200


def prose_only(text):
    """The text with code spans and math blanked out, so `hE` or $h$ is never read as prose."""
    return CODE.sub(lambda m: ' ' * len(m.group(0)), text)


def problems(text):
    """A list of reasons the explanation does not meet the platform's rules; empty when it does."""
    out = []
    t = (text or '').strip()
    if len(t) < MIN_CHARS:
        out.append('too short (%d characters; the platform wants a paper-style account)' % len(t))
    if '$$' not in t:
        out.append('no display math: open with the statement in a $$...$$ display')
    prose = prose_only(t)
    for m in PRON.finditer(prose):
        out.append('gendered pronoun %r (use the surname, "the paper" or "they")' % m.group(0))
    low = prose.lower()
    for w in BANNED:
        if w in low:
            out.append('%r: the platform rules out such adjectives' % w)
    return out
