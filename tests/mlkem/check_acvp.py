# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Check ref_mlkem.py against NIST ACVP JSON files (paths given as arguments).
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_mlkem as R

def hx(s): return bytes.fromhex(s)

def check_keygen(prompt, expected, limit):
    P, E = json.load(open(prompt)), json.load(open(expected))
    exp = {(g['tgId'], t['tcId']): t
           for g in E['testGroups'] for t in g['tests']}
    ok = bad = 0
    for g in P['testGroups']:
        p = R.PARAMS[g['parameterSet']]
        for t in g['tests'][:limit]:
            ek, dk = R.keygen_internal(p, hx(t['d']), hx(t['z']))
            e = exp[(g['tgId'], t['tcId'])]
            if ek == hx(e['ek']) and dk == hx(e['dk']): ok += 1
            else: bad += 1; print('keygen FAIL', g['parameterSet'], t['tcId'])
    print('keygen ok', ok, 'bad', bad)

def check_encdec(prompt, expected, limit):
    P, E = json.load(open(prompt)), json.load(open(expected))
    exp = {(g['tgId'], t['tcId']): t
           for g in E['testGroups'] for t in g['tests']}
    ok = bad = 0
    for g in P['testGroups']:
        p = R.PARAMS[g['parameterSet']]
        for t in g['tests'][:limit]:
            e = exp[(g['tgId'], t['tcId'])]
            if g['function'] == 'encapsulation':
                kk, c = R.encaps_internal(p, hx(t['ek']), hx(t['m']))
                good = kk == hx(e['k']) and c == hx(e['c'])
            elif g['function'] == 'decapsulation':
                kk = R.decaps_internal(p, hx(t['dk']), hx(t['c']))
                good = kk == hx(e['k'])
            else:
                continue
            if good: ok += 1
            else:
                bad += 1
                print('FAIL', g['function'], g['parameterSet'], t['tcId'])
    print('encdec ok', ok, 'bad', bad)

if __name__ == '__main__':
    d, limit = sys.argv[1], int(sys.argv[2])
    check_keygen(d + '/keygen_prompt.json', d + '/keygen_expected.json', limit)
    check_encdec(d + '/encdec_prompt.json', d + '/encdec_expected.json', limit)
