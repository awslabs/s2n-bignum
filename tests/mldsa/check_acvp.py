# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Check the Python transcription ref_mldsa.py of common/fips204.ml against
# the NIST ACVP ML-DSA vectors (keyGen, sigGen and sigVer, FIPS204).
# usage: python3 -B check_acvp.py ACVPDIR [MAXPERGROUP]
# where ACVPDIR has the directories ML-DSA-keyGen-FIPS204,
# ML-DSA-sigGen-FIPS204 and ML-DSA-sigVer-FIPS204 of
# gen-val/json-files in https://github.com/usnistgov/ACVP-Server, each
# with prompt.json and expectedResults.json.
import hashlib, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_mldsa as R

D = sys.argv[1]
MAXN = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9

# The pre-hash functions of the ACVP vectors: (OID number, digest function)
PREHASH = {
 'SHA2-256': (1, lambda m: hashlib.sha256(m).digest()),
 'SHA2-384': (2, lambda m: hashlib.sha384(m).digest()),
 'SHA2-512': (3, lambda m: hashlib.sha512(m).digest()),
 'SHA2-224': (4, lambda m: hashlib.sha224(m).digest()),
 'SHA2-512/224': (5, lambda m: hashlib.new('sha512_224', m).digest()),
 'SHA2-512/256': (6, lambda m: hashlib.new('sha512_256', m).digest()),
 'SHA3-224': (7, lambda m: hashlib.sha3_224(m).digest()),
 'SHA3-256': (8, lambda m: hashlib.sha3_256(m).digest()),
 'SHA3-384': (9, lambda m: hashlib.sha3_384(m).digest()),
 'SHA3-512': (10, lambda m: hashlib.sha3_512(m).digest()),
 'SHAKE-128': (11, lambda m: hashlib.shake_128(m).digest(32)),
 'SHAKE-256': (12, lambda m: hashlib.shake_256(m).digest(64)),
}

def load(name):
    p = json.load(open(os.path.join(D, name, 'prompt.json')))
    e = json.load(open(os.path.join(D, name, 'expectedResults.json')))
    res = {(g['tgId'], t['tcId']): t
           for g in e['testGroups'] for t in g['tests']}
    return p, res

def h(s): return bytes.fromhex(s) if s is not None else b''

ok = bad = 0
def report(what, good):
    global ok, bad
    if good: ok += 1
    else:
        bad += 1; print('FAIL', what, flush=True)

p, res = load('ML-DSA-keyGen-FIPS204')
for g in p['testGroups']:
    P = R.PARAMS[g['parameterSet']]
    for t in g['tests'][:MAXN]:
        e = res[(g['tgId'], t['tcId'])]
        pk, sk = R.keygen(P, h(t['seed']))
        report(('keyGen', g['tgId'], t['tcId']),
               pk == h(e['pk']) and sk == h(e['sk']))
print('keyGen: %d ok, %d bad' % (ok, bad), flush=True)

p, res = load('ML-DSA-sigGen-FIPS204')
for g in p['testGroups']:
    P = R.PARAMS[g['parameterSet']]
    for t in g['tests'][:MAXN]:
        e = res[(g['tgId'], t['tcId'])]
        sk = h(t['sk'])
        rnd = bytes(32) if g['deterministic'] else h(t['rnd'])
        if g['signatureInterface'] == 'internal':
            if g.get('externalMu'):
                sg = R.sign_mu(P, sk, h(t['mu']), rnd)
            else:
                sg = R.sign_internal(P, sk, h(t['message']), rnd)
        elif g['preHash'] == 'pure':
            sg = R.sign(P, sk, h(t['message']), h(t['context']), rnd)
        else:
            n, f = PREHASH[t['hashAlg']]
            sg = R.hash_sign(P, sk, R.oid(n), f(h(t['message'])),
                             h(t['context']), rnd)
        report(('sigGen', g['tgId'], t['tcId']), sg == h(e['signature']))
print('sigGen: %d ok, %d bad' % (ok, bad), flush=True)

p, res = load('ML-DSA-sigVer-FIPS204')
for g in p['testGroups']:
    P = R.PARAMS[g['parameterSet']]
    for t in g['tests'][:MAXN]:
        e = res[(g['tgId'], t['tcId'])]
        pk, sg = h(t['pk']), h(t['signature'])
        if g['signatureInterface'] == 'internal':
            if g.get('externalMu'):
                v = R.verify_mu(P, pk, h(t['mu']), sg)
            else:
                v = R.verify_internal(P, pk, h(t['message']), sg)
        elif g['preHash'] == 'pure':
            v = R.verify(P, pk, h(t['message']), sg, h(t['context']))
        else:
            n, f = PREHASH[t['hashAlg']]
            v = R.hash_verify(P, pk, R.oid(n), f(h(t['message'])), sg,
                              h(t['context']))
        report(('sigVer', g['tgId'], t['tcId']), v == e['testPassed'])
print('total: %d ok, %d bad' % (ok, bad), flush=True)
