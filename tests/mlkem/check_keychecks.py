# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_mlkem as R
d = sys.argv[1]
P = json.load(open(d + '/encdec_prompt.json'))
E = json.load(open(d + '/encdec_expected.json'))
exp = {(g['tgId'], t['tcId']): t for g in E['testGroups'] for t in g['tests']}
ok = bad = 0
for g in P['testGroups']:
    p = R.PARAMS[g['parameterSet']]
    for t in g['tests']:
        e = exp[(g['tgId'], t['tcId'])]
        if g['function'] == 'encapsulationKeyCheck':
            got = R.ek_check(p, bytes.fromhex(t['ek']))
        elif g['function'] == 'decapsulationKeyCheck':
            got = R.dk_check(p, bytes.fromhex(t['dk']))
        else:
            continue
        if got == e['testPassed']: ok += 1
        else:
            bad += 1
            print('FAIL', g['function'], g['parameterSet'], t['tcId'])
print('keychecks ok', ok, 'bad', bad)
