# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Convert NIST ACVP ML-DSA test vectors (JSON files from the ACVP-Server
# repository, gen-val/json-files/ML-DSA-{keyGen,sigGen,sigVer}-FIPS204)
# into HOL term files for mldsa_kat.ml.
#
# Usage: python3 make_vectors.py ACVPDIR OUTDIR
#
# where ACVPDIR has the directories ML-DSA-keyGen-FIPS204,
# ML-DSA-sigGen-FIPS204 and ML-DSA-sigVer-FIPS204, each with prompt.json
# and expectedResults.json. For each parameter set this takes the first
# keyGen test case; the deterministic sigGen test case of the internal
# interface (with a message, not an external mu) listed in SIGGEN below;
# and the accepted and rejected sigVer test cases of the internal
# interface listed in SIGVER below. The signing cases were chosen with the
# Python transcription ref_mldsa.py so that some attempts are rejected,
# for each of the two reasons that occur (the norm of z and the low bits),
# and the number of attempts is recorded in the file.

import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_mldsa as R

# tcId of the sigGen and sigVer test cases used, by parameter set.

SIGGEN = {'ML-DSA-44': 113, 'ML-DSA-65': 143, 'ML-DSA-87': 169}
SIGVER = {'ML-DSA-44': (116, 120), 'ML-DSA-65': (146, 137),
          'ML-DSA-87': (168, 171)}

# Explicit byte lists, at most 79 columns with the indentation used below
# and room for the closing ]:byte list`]; on the last line.

def hol_bytes(h):
    words = ['word %d' % x for x in bytes.fromhex(h)]
    if not words:
        return '`[]:byte list`'
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

def write(outdir, name, comments, fields):
    with open(os.path.join(outdir, name + '.ml'), 'w') as f:
        f.write('(*\n * Copyright Amazon.com, Inc. or its affiliates. '
                'All Rights Reserved.\n'
                ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n'
                ' *)\n\n')
        for c in comments:
            f.write('(* %s *)\n' % c.ljust(73))
        f.write('\nmldsa_kat_vector "%s"\n [' % name)
        f.write(';\n  '.join('"%s",\n    %s' % (k, v) for k, v in fields))
        f.write('];;\n')

def attempts(P, sk, mu, rnd):
    # The number of signing attempts, from the Python transcription.
    k, l, eta, tau, lam, g1, g2, omega = P
    c = R.bitlen(2 * eta)
    rho, key = sk[0:32], sk[32:64]
    s1b = R.slice_(128, 32 * c * l, sk)
    s2b = R.slice_(128 + 32 * c * l, 32 * c * k, sk)
    t0b = R.slice_(128 + 32 * c * (l + k), 416 * k, sk)
    s1 = [R.poly(lambda j, i=i: eta - R.field(c, s1b, 256 * i + j))
          for i in range(l)]
    s2 = [R.poly(lambda j, i=i: eta - R.field(c, s2b, 256 * i + j))
          for i in range(k)]
    t0 = [R.poly(lambda j, i=i: 4096 - R.field(13, t0b, 256 * i + j))
          for i in range(k)]
    rhopp = R.H(bytes(key) + bytes(rnd) + bytes(mu), 64)
    A = [[R.expand_a(rho, i, j) for j in range(l)] for i in range(k)]
    n = 0
    while R.sign_attempt(P, A, s1, s2, t0, mu, rhopp, l * n) is None:
        n += 1
    return n + 1

def main(acvp, outdir):
    def load(name):
        d = os.path.join(acvp, name)
        p = json.load(open(os.path.join(d, 'prompt.json')))
        e = json.load(open(os.path.join(d, 'expectedResults.json')))
        res = {(g['tgId'], t['tcId']): t
               for g in e['testGroups'] for t in g['tests']}
        return p, res
    n = lambda ps: ps.split('-')[-1]
    p, res = load('ML-DSA-keyGen-FIPS204')
    for g in p['testGroups']:
        ps = g['parameterSet']
        t = g['tests'][0]; e = res[(g['tgId'], t['tcId'])]
        write(outdir, 'keygen' + n(ps),
              ['ACVP keyGen, %s, tgId %d tcId %d' % (ps, g['tgId'], t['tcId'])],
              [('xi', hol_bytes(t['seed'])), ('pk', hol_bytes(e['pk'])),
               ('sk', hol_bytes(e['sk']))])
    p, res = load('ML-DSA-sigGen-FIPS204')
    for g in p['testGroups']:
        ps = g['parameterSet']
        if not (g['deterministic'] and g['signatureInterface'] == 'internal'
                and not g.get('externalMu')):
            continue
        for t in g['tests']:
            if t['tcId'] != SIGGEN[ps]:
                continue
            e = res[(g['tgId'], t['tcId'])]
            P = R.PARAMS[ps]
            sk, m = bytes.fromhex(t['sk']), bytes.fromhex(t['message'])
            rnd = bytes(32)
            sg = R.sign_internal(P, sk, m, rnd)
            assert sg == bytes.fromhex(e['signature'])
            mu = R.H(R.slice_(64, 64, sk) + m, 64)
            write(outdir, 'sign' + n(ps),
                  ['ACVP sigGen, %s, internal interface, deterministic,'
                   % ps, 'tgId %d tcId %d, %d signing attempts'
                   % (g['tgId'], t['tcId'], attempts(P, sk, mu, rnd))],
                  [('sk', hol_bytes(t['sk'])), ('m', hol_bytes(t['message'])),
                   ('rnd', hol_bytes(rnd.hex())),
                   ('sg', hol_bytes(e['signature']))])
    p, res = load('ML-DSA-sigVer-FIPS204')
    for g in p['testGroups']:
        ps = g['parameterSet']
        if not (g['signatureInterface'] == 'internal'
                and not g.get('externalMu')):
            continue
        for t in g['tests']:
            if t['tcId'] not in SIGVER[ps]:
                continue
            e = res[(g['tgId'], t['tcId'])]
            P = R.PARAMS[ps]
            ok = R.verify_internal(P, bytes.fromhex(t['pk']),
                                   bytes.fromhex(t['message']),
                                   bytes.fromhex(t['signature']))
            assert ok == e['testPassed']
            kind = 'valid' if ok else 'reject'
            write(outdir, 'verify%s_%s' % (n(ps), kind),
                  ['ACVP sigVer, %s, internal interface, tgId %d tcId %d'
                   % (ps, g['tgId'], t['tcId']),
                   'expected result: %s' % ('accepted' if ok else 'rejected')],
                  [('pk', hol_bytes(t['pk'])), ('m', hol_bytes(t['message'])),
                   ('sg', hol_bytes(t['signature'])),
                   ('ok', '`T`' if ok else '`F`')])

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
