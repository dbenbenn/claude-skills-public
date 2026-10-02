"""Lean names: short and full forms, primes, and comment-aware mentions -- in one place.

The recurring prime bug: `\\b` treats `'` as a word boundary, so `foo\\b` matches inside `foo'`
(build_solutions built `theorem solution'` from the dev lemma `isMarginal_EBad'`, 2026-10-02).
Every name match here uses IDENT_END instead."""
import re

from .leantext import strip

# characters that continue a Lean identifier (letters, digits, `_`, `'`, `!`, `?`, subscripts)
IDENT_CHAR = r"[\w'!?₀-ₜ]"
IDENT_END = r"(?!%s)" % IDENT_CHAR
IDENT_START = r"(?<![\w'!?₀-ₜ.])"


def short(name):
    """`A.B.foo'` -> `foo'`."""
    return name.rsplit('.', 1)[-1]


def base(name):
    """The short name without trailing primes: the published theorem a dev copy `foo''` copies."""
    return short(name).rstrip("'")


def qualify(namespace, name):
    """`name` declared inside `namespace` (`_root_.x` escapes it)."""
    if name.startswith('_root_.'):
        return name[len('_root_.'):]
    return '%s.%s' % (namespace, name) if namespace else name


def name_re(name):
    """A regex matching `name` as a whole identifier, optionally namespace-qualified, never as the
    prefix of a longer (e.g. primed) identifier."""
    return re.compile(IDENT_START + r"(?:[^\W\d][\w'!?₀-ₜ]*\.)*%s" % re.escape(short(name)) + IDENT_END)


def mentions(text, name):
    """Does Lean source `text` name `name` outside comments?"""
    return bool(name_re(name).search(strip(text)))
