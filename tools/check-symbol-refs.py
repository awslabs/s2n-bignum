#!/usr/bin/env python3
#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

"""Check that S2N_BN_SYMBOL-defined symbols are also referenced through it.

S2N_BN_SYMBOL(name) expands to "_name" on Mach-O and to "name" elsewhere
(see include/_internal_s2n_bignum.h). So a symbol that is *defined* as

    S2N_BN_SYMBOL(foo_constant):

but *referenced* as a bare name

    lea     r10, [rip+foo_constant]

resolves fine on ELF, where both spellings collapse to "foo_constant", yet
leaves "foo_constant" undefined on Mach-O, where the definition is really
"_foo_constant". The ELF-only CI builds cannot see this, so it is checked
statically here instead.

Usage: check-symbol-refs.py [PATH ...]   (defaults to the current directory)

Exits non-zero, listing every offending line, if any mismatch is found.
"""

import os
import re
import sys

# A definition of the form "S2N_BN_SYMBOL(name):" at the start of a line.
DEF_RE = re.compile(r'^\s*S2N_BN_SYMBOL\(([A-Za-z_][A-Za-z0-9_]*)\)\s*:')

# Macros that deliberately take a *bare* name and apply S2N_BN_SYMBOL
# internally; a bare name on these lines is correct, not a finding.
MACRO_TAKES_BARE_NAME = re.compile(
    r'S2N_BN_(SYM_VISIBILITY_DIRECTIVE|SYM_PRIVACY_DIRECTIVE'
    r'|FUNCTION_TYPE_DIRECTIVE|SIZE_DIRECTIVE)\s*\('
)

# A correctly wrapped reference, blanked out before looking for bare ones.
WRAPPED_RE = re.compile(r'S2N_BN_SYMBOL\s*\(\s*[A-Za-z_][A-Za-z0-9_]*\s*\)')

SKIP_DIRS = {'.git', 'third_party'}


def bare_uses(path):
    """Yield (line_no, symbol, text) for bare uses of wrapped-only symbols."""
    with open(path, 'r', errors='replace') as fh:
        lines = fh.readlines()

    defined = {m.group(1) for m in (DEF_RE.match(ln) for ln in lines) if m}
    if not defined:
        return

    for lineno, raw in enumerate(lines, 1):
        code = raw.split('//')[0]
        stripped_code = code.strip()
        # Skip blank lines and preprocessor directives (the latter legitimately
        # mention bare names, e.g. in #define or #if defined(...)).
        if not stripped_code or stripped_code.startswith('#'):
            continue
        # Skip the symbol's own definition line.
        if DEF_RE.match(code):
            continue
        if MACRO_TAKES_BARE_NAME.search(code):
            continue

        residue = WRAPPED_RE.sub('@@', code)
        for sym in sorted(defined):
            pattern = r'(?<![A-Za-z0-9_])' + re.escape(sym) + r'(?![A-Za-z0-9_])'
            if re.search(pattern, residue):
                yield lineno, sym, raw.rstrip()


def main():
    roots = sys.argv[1:] or ['.']
    findings = []
    scanned = 0

    for root in roots:
        if not os.path.exists(root):
            print('ERROR: no such path: %s' % root)
            return 2
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            for name in sorted(filenames):
                if not name.endswith('.S'):
                    continue
                path = os.path.join(dirpath, name)
                scanned += 1
                for lineno, sym, text in bare_uses(path):
                    findings.append((path, lineno, sym, text))

    print('Checked %d .S file(s) under: %s' % (scanned, ', '.join(roots)))

    if not findings:
        print('OK: every S2N_BN_SYMBOL-defined symbol is referenced through it.')
        return 0

    print('')
    print('ERROR: %d bare reference(s) to S2N_BN_SYMBOL-defined symbol(s).' % len(findings))
    print('These link on ELF but leave the symbol undefined on Mach-O.')
    print('')
    for path, lineno, sym, text in findings:
        print('  %s:%d' % (path, lineno))
        print('      symbol: %s (defined as S2N_BN_SYMBOL(%s))' % (sym, sym))
        print('      source: %s' % text.strip())
        print('      fix   : reference it as S2N_BN_SYMBOL(%s)' % sym)
        print('')
    return 1


if __name__ == '__main__':
    sys.exit(main())
