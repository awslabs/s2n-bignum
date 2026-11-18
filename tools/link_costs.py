#!/usr/bin/env python3

# Write the link_costs.tsv of a build of mlkem-native or mldsa-native (see
# native_link.py): the time of each proof file X_proof.ml, from the
# "Running time" line of X_proof.correct of an earlier run (make). Given
# the output of a run of the link file, it takes the times of its jobs
# ("par: job X: T s") instead. Jobs without a time keep the cost they have
# in link_costs.tsv, if any; the link file estimates the others from the
# size of their files.
#
# Usage, in s2n-bignum's arm or x86 directory:
#
#   python3 ../tools/link_costs.py mldsa_native gcc12_O2_reduced_ram [LOG]
#
# which reads mldsa_native/gcc12_O2_reduced_ram/*.correct (or LOG) and
# writes proofs/mldsa_native/gcc12_O2_reduced_ram/link_costs.tsv.

import os, re, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from native_link import read_costs

RUNNING = re.compile(rb'Running time: ([0-9.]+) sec')
JOB = re.compile(rb'^par: job ([A-Za-z0-9_]+): ([0-9.]+) s', re.M)

def running_time(path):
    try:
        data = open(path, 'rb').read()
    except OSError:
        return None
    m = RUNNING.findall(data)
    return float(m[-1]) if m else None

def main():
    if len(sys.argv) not in (3, 4):
        sys.exit('usage: link_costs.py FAMILY BUILD [LOG]')
    family, build = sys.argv[1:3]
    logs = '%s/%s' % (family, build)
    prf = 'proofs/%s/%s' % (family, build)
    path = '%s/link_costs.tsv' % prf
    costs = read_costs(prf)
    if len(sys.argv) == 4:
        for x, t in JOB.findall(open(sys.argv[3], 'rb').read()):
            costs[x.decode()] = float(t)
    else:
        for f in sorted(os.listdir(prf)):
            if f.endswith('_proof.ml'):
                t = running_time('%s/%s.correct' % (logs, f[:-3]))
                if t is not None:
                    costs[f[:-9]] = t
    rows = sorted(costs.items())
    with open(path, 'w') as out:
        out.write('# Seconds per job of link.ml (tools/native_link.py), from the\n'
                  '# proof times of an earlier run (tools/link_costs.py); used to\n'
                  '# run the costliest jobs first.\n')
        for x, t in rows:
            out.write('%s\t%.0f\n' % (x, t))
    print('%s: %d jobs with costs' % (prf, len(rows)))

if __name__ == '__main__':
    main()
