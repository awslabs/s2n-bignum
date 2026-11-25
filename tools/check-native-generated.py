#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Check that the generated files of the builds of mlkem-native and
# mldsa-native are what their generators write now: for each build
# <arch>/<family>/<build> with a proofs.mk, that tools/native_proofs_mk.py
# writes that proofs.mk and tools/native_link.py writes
# <arch>/proofs/<family>/<build>/link.ml. After a change to the proofs of
# a build (the files they load, a new proof file) or to the generators,
# both files must be regenerated, as the generators' headers say, link.ml
# first, as proofs.mk has the files that link.ml loads; this catches the
# cases where that was forgotten.
#
# usage: python3 tools/check-native-generated.py [ARCH...]
#        (in s2n-bignum's root directory; ARCH is arm or x86, default both)
#
# Exits with status 1, after showing the first lines of each difference,
# if a file differs from what its generator writes.

import difflib, os, subprocess, sys

def generated(arch, tool, family, build):
    r = subprocess.run([sys.executable, os.path.join('..', 'tools', tool),
                        family, build], cwd=arch, capture_output=True,
                       text=True)
    if r.returncode != 0:
        return None, r.stderr.strip()
    return r.stdout, None

def main():
    arches = sys.argv[1:] or ['arm', 'x86']
    bad = checked = 0
    for arch in arches:
        for family in ('mlkem_native', 'mldsa_native'):
            fdir = os.path.join(arch, family)
            if not os.path.isdir(fdir):
                continue
            for build in sorted(os.listdir(fdir)):
                if not os.path.isfile(os.path.join(fdir, build, 'proofs.mk')):
                    continue
                for tool, path in (
                        ('native_link.py',
                         os.path.join('proofs', family, build, 'link.ml')),
                        ('native_proofs_mk.py',
                         os.path.join(family, build, 'proofs.mk'))):
                    full = os.path.join(arch, path)
                    if not os.path.isfile(full):
                        continue
                    checked += 1
                    out, err = generated(arch, tool, family, build)
                    if out is None:
                        print('%s: %s failed: %s' % (full, tool, err))
                        bad += 1
                        continue
                    old = open(full).read()
                    if out != old:
                        bad += 1
                        print('%s differs from what tools/%s writes;'
                              ' regenerate it in %s with' % (full, tool, arch))
                        print('  python3 ../tools/%s %s %s > %s'
                              % (tool, family, build, path))
                        diff = list(difflib.unified_diff(
                            old.splitlines(), out.splitlines(),
                            'committed', 'generated', lineterm='', n=1))
                        for line in diff[:20]:
                            print('    ' + line)
                        if len(diff) > 20:
                            print('    ... (%d more lines)' % (len(diff) - 20))
    print('%d generated files checked, %d differ' % (checked, bad))
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
