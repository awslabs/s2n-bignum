# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Convert NIST ACVP ML-KEM test vectors (JSON files from the ACVP-Server
# repository, gen-val/json-files/ML-KEM-keyGen-FIPS203 and
# ML-KEM-encapDecap-FIPS203) into HOL term files for mlkem_kat.ml.
#
# Usage: python3 make_vectors.py ACVPDIR OUTDIR
#
# where ACVPDIR contains keygen_prompt.json, keygen_expected.json,
# encdec_prompt.json and encdec_expected.json. For each parameter set this
# takes the first keyGen and the first encapsulation test case, and the
# first valid and the first rejected decapsulation test case (classified
# using the Python mirror ref_mlkem.py).

import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_mlkem as R

# Explicit byte lists, at most 79 columns with the indentation used below
# and room for the closing ]:byte list`]; on the last line.

def hol_bytes(h):
    words = ['word %d' % x for x in bytes.fromhex(h)]
    lines, cur = [], ''
    for i, w in enumerate(words):
        last = i == len(words) - 1
        piece = w + ('' if last else ';')
        limit = 73 - 6 - (16 if last else 0)
        if cur and len(cur) + len(piece) > limit:
            lines.append(cur.rstrip())
            cur = ''
        cur += piece + ' '
    lines.append(cur.rstrip())
    return '`[' + '\n      '.join(lines) + ']:byte list`'

def write(outdir, name, comment, fields):
    with open(os.path.join(outdir, name + '.ml'), 'w') as f:
        f.write('(*\n * Copyright Amazon.com, Inc. or its affiliates. '
                'All Rights Reserved.\n'
                ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n'
                ' *)\n\n')
        f.write('(* %s *)\n\n' % comment)
        f.write('mlkem_kat_vector "%s"\n [' % name)
        f.write(';\n  '.join('"%s",\n    %s' % (k, hol_bytes(v))
                            for k, v in fields))
        f.write('];;\n')

def main(acvp, outdir):
    load = lambda n: json.load(open(os.path.join(acvp, n + '.json')))
    def expected(E):
        return {(g['tgId'], t['tcId']): t
                for g in E['testGroups'] for t in g['tests']}
    KP, KE = load('keygen_prompt'), expected(load('keygen_expected'))
    EP, EE = load('encdec_prompt'), expected(load('encdec_expected'))
    for g in KP['testGroups']:
        ps = g['parameterSet']; n = ps.split('-')[-1]
        t = g['tests'][0]; e = KE[(g['tgId'], t['tcId'])]
        write(outdir, 'keygen' + n,
              'ACVP keyGen, %s, tgId %d tcId %d' % (ps, g['tgId'], t['tcId']),
              [('d', t['d']), ('z', t['z']), ('ek', e['ek']), ('dk', e['dk'])])
    for g in EP['testGroups']:
        ps = g['parameterSet']; n = ps.split('-')[-1]
        if g['function'] == 'encapsulation':
            t = g['tests'][0]; e = EE[(g['tgId'], t['tcId'])]
            write(outdir, 'encaps' + n,
                  'ACVP encapDecap, %s encapsulation, tgId %d tcId %d'
                  % (ps, g['tgId'], t['tcId']),
                  [('ek', t['ek']), ('m', t['m']),
                   ('k', e['k']), ('c', e['c'])])
        elif g['function'] == 'decapsulation':
            p = R.PARAMS[ps]; k = p[0]
            done = set()
            for t in g['tests']:
                dk = bytes.fromhex(t['dk']); c = bytes.fromhex(t['c'])
                m1 = R.kpke_decrypt(p, dk[:384 * k], c)
                kk1, r1 = R.G(m1 + dk[768 * k + 32:768 * k + 64])
                ok = R.kpke_encrypt(p, dk[384 * k:768 * k + 32], m1, r1) == c
                kind = 'valid' if ok else 'reject'
                if kind in done: continue
                done.add(kind)
                e = EE[(g['tgId'], t['tcId'])]
                write(outdir, 'decaps%s_%s' % (n, kind),
                      'ACVP encapDecap, %s decapsulation, tgId %d tcId %d '
                      '(%s)' % (ps, g['tgId'], t['tcId'], kind),
                      [('dk', t['dk']), ('c', t['c']), ('k', e['k'])])

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
