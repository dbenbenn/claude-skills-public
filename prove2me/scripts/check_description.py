"""Run the prove2me skill's description checklist mechanically.

Written because the skill already carried the "opens with 'This mission formalizes …'" note and
I still shipped a description that never named its source. A rule I have to remember is a rule
I will drop, so the checkable parts are checked here.

usage: check_description.py PATH
"""
import os
import re
import sys

if len(sys.argv) != 2:
    sys.exit(__doc__)
p = sys.argv[1]
s = open(p, encoding='utf-8').read()
fail, warn = [], []

# 1. opens by naming what is formalized, with a resolvable link
first = s.strip().split('\n')[0]
if not first.startswith('This mission formalizes'):
    fail.append('does not open "This mission formalizes …" (opens: %r)' % first[:60])
elif not re.search(r'\]\(https?://', first + s.split('\n\n')[0]):
    fail.append('the opening citation carries no resolvable link')

# 2. required sections: the seven of the platform's mission_description.md, in its order. This
# checker once demanded a 'What is left out' section the rulebook does not have, and a description
# was renamed away from the rulebook's 'Formalization scope' to satisfy it (F-amenability,
# 2026-09-30); the rulebook wins, and what is left out belongs inside Formalization scope.
SECTIONS = [('Motivation', r'motivation'), ('Setting', r'setting'), ('Target', r'target|goal'),
            ('Significance', r'significance'), ('Difficulty', r'difficulty'),
            ('Formalization scope', r'formalization scope'), ('Selected references', r'references')]
heads = [h.strip() for h in re.findall(r'^##\s+(.+)$', s, re.M)]
pos = []
for label, rx in SECTIONS:
    i = next((k for k, h in enumerate(heads) if re.search(rx, h, re.I)), None)
    if i is None:
        fail.append('no section matching %r (mission_description.md)' % label)
    else:
        pos.append(i)
if pos != sorted(pos):
    warn.append('sections out of the rulebook order: ' + ', '.join(heads))
if any(re.search(r'what is left out', h, re.I) for h in heads):
    fail.append("'What is left out' is not a rulebook section: put it inside Formalization scope")

# 3. a display line does not wrap
for m in re.finditer(r'\$\$(.+?)\$\$', s, re.S):
    t = ' '.join(m.group(1).split())
    if len(t) > 90:
        fail.append('display math %d chars, will not wrap: %s…' % (len(t), t[:60]))

# 4. no pronoun for an author whose pronouns the source does not establish
for m in re.finditer(r'(?<![\w-])(he|she|her|hers|his|him)(?![\w-])', s, re.I):
    a, b = max(0, m.start() - 40), m.end() + 40
    fail.append('pronoun %r near: …%s…' % (m.group(0), ' '.join(s[a:b].split())))

# 5. no phrase lifted from the platform's rulebook
# paraphrases count too: 'it fixes no constant ...' was the Target rule's rationale
# about hard-coded constants, recited where the goal is a biconditional and it says
# nothing. A checker cannot catch paraphrase in general, only known instances.
for phrase in ('shape of the truth', 'who cares and why', 'wasted day',
               'solvers will not guess', 'weakest stable statement',
               'invalidated by the next improvement', 'fixes no constant'):
    if phrase in s.lower():
        fail.append('rulebook phrase present: %r' % phrase)

# 6. no first person, no meta-commentary about the process
# `I` followed by a period and a capital is an initial in a citation, not a pronoun; a
# checker that cries wolf stops being read
for m in re.finditer(r'(?<![\w-])(we|our|I|my)(?![\w-])', s):
    if m.group(0) == 'I' and re.match(r'\.\s*[A-Z]', s[m.end():m.end() + 3]):
        continue
    a, b = max(0, m.start() - 40), m.end() + 40
    warn.append('first person %r near: …%s…' % (m.group(0), ' '.join(s[a:b].split())))

# 6b. every "**Name** (year)" attribution in the body has a Selected-references entry.
# This is the defect dbenbenn caught by eye: "Ol'shanskii (1980)" was attributed with no
# entry. Bold-name-then-parenthesised-year is this genre's attribution idiom, so it is
# precise enough to check without firing on theorem names like Banach-Tarski.
_split = re.split(r'^##\s+.*references', s, flags=re.M | re.I)
if len(_split) > 1:
    _body, _refs = _split[0], _split[1]
    for m in re.finditer(r'\*\*([^*]{2,40}?)\*\*\s*\((?:1[6-9]\d\d|20\d\d)\)', _body):
        surname = m.group(1).strip().split()[-1].strip('.,;:')
        if surname and surname not in _refs:
            fail.append('attributed in the body but absent from the references: %r' % surname)

# 6c. date-dependent status claims: each must be checked against the platform today, not the
# source. QFS shipped "To date none of these results has a machine-checked proof" while six of its
# own milestones were Proved (2026-09-27); the checklist line on date-dependent claims did not
# catch it, so every such phrase is surfaced here for a look.
for m in re.finditer(r'(?i)\b(to date|as of|not yet|still open|remains? open|no (?:machine-checked|formal)|'
                     r'machine-checked|not in mathlib|has not been (?:formali[sz]ed|proved))\b', s):
    a, b = max(0, m.start() - 50), m.end() + 50
    warn.append('status claim, check it against the platform today: …%s…' % ' '.join(s[a:b].split()))

# 7. length
words = len(re.sub(r'\$[^$]*\$', ' X ', s).split())
if not 800 <= words <= 1500:
    warn.append('%d words, outside the 800-1500 guideline' % words)

print('%s: %d words, %d sections' % (os.path.basename(p), words,
                                     len(re.findall(r'^##\s', s, re.M))))
for w in warn:
    print('  warn  ' + w[:150])
for f in fail:
    print('  FAIL  ' + f[:150])
print('\n%s' % ('FAILURES: %d' % len(fail) if fail else 'no failures'))
sys.exit(1 if fail else 0)
