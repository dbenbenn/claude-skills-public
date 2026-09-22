"""Run the prove2me skill's description checklist mechanically.

Written because the skill already carried the "opens with 'This mission formalizes …'" note and
I still shipped a description that never named its source. A rule I have to remember is a rule
I will drop, so the checkable parts are checked here.

usage: check_description.py [path]   (default: description.md beside this file)
"""
import os
import re
import sys

p = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), 'description.md')
s = open(p, encoding='utf-8').read()
fail, warn = [], []

# 1. opens by naming what is formalized, with a resolvable link
first = s.strip().split('\n')[0]
if not first.startswith('This mission formalizes'):
    fail.append('does not open "This mission formalizes …" (opens: %r)' % first[:60])
elif not re.search(r'\]\(https?://', first + s.split('\n\n')[0]):
    fail.append('the opening citation carries no resolvable link')

# 2. required sections
for want in ('Setting', 'What is left out', 'references'):
    if not re.search(r'^##\s+.*' + want, s, re.M | re.I):
        fail.append('no section matching %r' % want)
if not re.search(r'^##\s+.*(target|goal)', s, re.M | re.I):
    fail.append('no Target/Goal section')

# 3. a display line does not wrap
for m in re.finditer(r'\$\$(.+?)\$\$', s, re.S):
    t = ' '.join(m.group(1).split())
    if len(t) > 90:
        fail.append('display math %d chars, will not wrap: %s…' % (len(t), t[:60]))

# 4. no pronoun for an author whose pronouns the source does not establish
for m in re.finditer(r'(?<![\w-])(she|her|hers|his|him)(?![\w-])', s, re.I):
    a, b = max(0, m.start() - 40), m.end() + 40
    fail.append('pronoun %r near: …%s…' % (m.group(0), ' '.join(s[a:b].split())))

# 5. no phrase lifted from the platform's rulebook
for phrase in ('shape of the truth', 'who cares and why', 'wasted day', 'solvers will not guess'):
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
