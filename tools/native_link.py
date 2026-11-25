#!/usr/bin/env python3

# Generate the link file of a build of a family of compiled code (mlkem-native, mldsa-native, ...),
# which
# proves all the theorems of the build in one session and then turns the
# theorems of the top-level functions into theorems without assumptions
# (see common/relative.ml). It serves both instruction sets: run it in
# s2n-bignum's arm or x86 directory.
#
# Each proof file X_proof.ml proves the theorems of its spec file X_spec.ml
# relative to the contracts of its callees, so the proof files do not
# depend on each other. The link file makes each of them the body of a
# functor Par_job_X, placed after the files that X_proof.ml loads, so that
# its names mean what they would mean there. The spec files come callees
# first, each after the spec files that it loads, in the order of the
# needs. par_run_jobs (common/par.ml) runs the jobs, costliest first: one
# after the other by default, at the same time on S2N_PAR_DOMAINS domains
# when built with HOL_PAR=1.
#
# The top-level functions are the API functions of the family that the
# build has proofs for; if it has none, the functions whose files no other
# file loads. For a family whose API is not given, every function
# is top-level, so the theorems of every proof file are closed. The theorems of their proof files that the jobs return are
# closed. The files of the tail of the family, fips203.ml for mlkem-native
# and fips204.ml and fips204_*.ml for mldsa-native, are loaded after the
# jobs, fips20N.ml first, and their theorems X_SUBROUTINE_FIPS20N and
# X_SUBROUTINE_SAFE_FIPS20N are closed too. Those files derive theorems of
# the API functions from their CORRECT and SAFE theorems: for mlkem-native
# without the hypothesis that SampleNTT terminates, for mldsa-native
# stated with the FIPS 204 specification common/fips204/fips204.ml. They
# are not jobs, so that what they load (such as Library/ringtheory.ml)
# does not exist while the proof files run.
#
# The cost of a job is its time in seconds from the file link_costs.tsv of
# the build directory (lines "X<tab>seconds", see link_costs.py), if it
# lists X, and otherwise estimated from the size of the proof file.
#
# Usage, in s2n-bignum's arm or x86 directory:
#
#   python3 ../tools/native_link.py mldsa_native gcc12_O2 \
#     > proofs/mldsa_native/gcc12_O2/link.ml
#
# A spec file without a proof file is an error, unless it is listed with
# --open SPEC,... (the names X of X_spec.ml): its contracts (the X_STMT of
# the spec file) then stay open, the link closes the theorems relative to
# them, prints the remaining assumptions of each theorem and fails if any
# other contract is not proved.

import os, re, sys

FAMILIES = {
    'mlkem_native': {
        'api': r'(keypair_derand|keypair|enc_derand|enc|dec|check_pk|check_sk)_k[234]$',
        'tail': 'fips203'},
    'mldsa_native': {
        'api': r'(keypair_internal|keypair|signature_internal|signature|signature_extmu|'
               r'signature_pre_hash_internal|signature_pre_hash_shake256|verify_internal|'
               r'verify|verify_extmu|verify_pre_hash_internal|verify_pre_hash_shake256|'
               r'prepare_domain_separation_prefix|pk_from_sk)_(44|65|87)$',
        'tail': 'fips204'},
}

# A family whose API is not given ('api': None) closes the theorems of every
# function; 'tail': None means no tail files; 'relative' names the wrapper
# of common/relative.ml that its spec files load, e.g.
#   FAMILIES['mylib'] = {'api': None, 'tail': None,
#                        'relative': '%s/proofs/mylib/relative.ml'}

# The wrapper of common/relative.ml for the instruction set, which the spec
# files of a family load, unless the family gives its own.
RELATIVE = '%s/proofs/mlkem_native/relative.ml'

NEEDS = re.compile(r'\s*needs\s+"([^"]+)"\s*;;')
THM = re.compile(r'^let\s+([A-Z0-9_]+_SUBROUTINE_(CORRECT|SAFE|FULL))\s*=', re.M)

def file_needs(path):
    """The files that path loads with needs, in order."""
    return [m.group(1) for l in open(path) for m in [NEEDS.match(l)] if m]

def read_costs(prf):
    """The costs of the jobs from link_costs.tsv of prf, if it exists."""
    costs = {}
    path = os.path.join(prf, 'link_costs.tsv')
    if os.path.exists(path):
        for l in open(path):
            f = l.split()
            if len(f) >= 2 and not l.startswith('#'):
                costs[f[0]] = float(f[1])
    return costs

def main():
    args = sys.argv[1:]
    allowed_open = []
    if len(args) == 4 and args[2] == '--open':
        allowed_open = [x for x in args[3].split(',') if x]
        args = args[:2]
    if len(args) != 2:
        sys.exit('usage: native_link.py FAMILY BUILD [--open SPEC,...] (FAMILY '
                 'one of %s, or any family with proofs/FAMILY/BUILD)'
                 % '|'.join(sorted(FAMILIES)))
    family, build = args[0], args[1]
    isa = os.path.basename(os.getcwd())
    if isa not in ('arm', 'x86'):
        sys.exit('native_link.py: run it in the arm or x86 directory')
    # A family not in FAMILIES has no API pattern (every function is closed)
    # and no tail; its spec files load proofs/FAMILY/relative.ml if there is
    # one, the instruction set's wrapper otherwise.
    own = 'proofs/%s/relative.ml' % family
    conf = FAMILIES.get(family, {'api': None, 'tail': None,
                                 'relative': ('%s/' + own) if os.path.isfile(own)
                                             else RELATIVE})
    api = conf['api']
    api = re.compile(api) if api is not None else None
    tail = conf['tail']
    relative = conf.get('relative', RELATIVE)
    prf = 'proofs/%s/%s' % (family, build)
    here = '%s/%s/' % (isa, prf)

    # The proof files, callees first
    files = sorted(f[:-9] for f in os.listdir(prf) if f.endswith('_proof.ml'))
    deps = dict((x, [l[len(here):-8] for l in file_needs('%s/%s_spec.ml' % (prf, x))
                     if l.startswith(here) and l.endswith('_spec.ml')])
                for x in files)
    # The callees whose spec file has no proof file yet: their contracts
    # stay open, and the theorems are closed relative to them.
    open_specs = set(y for x in files for y in deps[x] if y not in deps)
    # and, transitively, the callees of open spec files that have no proof
    # file either (their contracts are assumptions of the open ones)
    todo = list(open_specs)
    while todo:
        y = todo.pop()
        for l in file_needs('%s/%s_spec.ml' % (prf, y)):
            if l.startswith(here) and l.endswith('_spec.ml'):
                z = l[len(here):-8]
                if z not in deps and z not in open_specs:
                    open_specs.add(z); todo.append(z)
    # Specs named with --open that no proof loads, directly or through an
    # open spec, are open too (if their spec file exists).
    for y in allowed_open:
        if y not in deps and y not in open_specs:
            if not os.path.isfile('%s/%s_spec.ml' % (prf, y)):
                sys.exit('native_link.py: --open %s: no %s_spec.ml' % (y, y))
            open_specs.add(y)
    open_specs = sorted(open_specs)
    # A spec file that states no contract (no ..._STMT, e.g. one with shared
    # definitions only) has nothing to leave open.
    STMT0 = re.compile(r'^let\s+([A-Z0-9_]+_STMT)\s*=', re.M)
    open_specs = [y for y in open_specs
                  if STMT0.search(open('%s/%s_spec.ml' % (prf, y)).read())]
    for y in open_specs:
        if y not in allowed_open:
            sys.exit('native_link.py: %s_spec.ml has no proof file '
                     '(allow it with --open %s)' % (y, y))
    deps = dict((x, [y for y in deps[x] if y in deps]) for x in files)
    STMT = re.compile(r'^let\s+([A-Z0-9_]+_STMT)\s*=', re.M)
    open_stmts = [t for y in open_specs
                  for t in STMT.findall(open('%s/%s_spec.ml' % (prf, y)).read())]
    allowed_tm = '[%s]' % '; '.join(open_stmts)
    order = []; seen = set()
    def visit(x, path):
        if x in seen: return
        if x in path: sys.exit('native_link.py: circular needs at ' + x)
        for y in deps[x]: visit(y, path + [x])
        seen.add(x); order.append(x)
    for x in files: visit(x, [])

    # The theorems to close: those of the top-level functions and the tail
    top = [x for x in files if api is None or api.match(x)]
    if not top:
        needed = set(y for x in files for y in deps[x])
        top = [x for x in files if x not in needed]
    top_thms = dict((x, [m.group(1) for m in
                         THM.finditer(open('%s/%s_proof.ml' % (prf, x)).read())])
                    for x in top)
    tail_files, tail_thms = [], []
    if tail:
        tail_files = sorted(f for f in os.listdir(prf)
                            if re.match(r'%s(_[a-z0-9]+)?\.ml$' % tail, f))
        tail_files.sort(key=lambda f: f != tail + '.ml')
        tre = re.compile(r'^let\s+([A-Z0-9_]+_SUBROUTINE_(?:SAFE_)?%s)\s*='
                         % tail.upper(), re.M)
        for f in tail_files:
            tail_thms += tre.findall(open('%s/%s' % (prf, f)).read())
    job_thms = [t for x in order for t in top_thms.get(x, [])]
    thms = job_thms + tail_thms
    if len(set(thms)) != len(thms):
        sys.exit('native_link.py: a theorem name is in two files')

    out = ['(*',
           ' * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.',
           ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0',
           ' *)', '',
           '(* Generated by tools/native_link.py %s %s. Do not edit. *)' % (family, build), '',
           '(* ========================================================================= *)',
           '(* All the proofs of the build in one session. Each proof file proves the    *)',
           '(* theorems of its spec file relative to the contracts of its callees (see   *)',
           '(* common/relative.ml), so the proof files are independent jobs:             *)',
           '(* par_run_jobs runs them one after the other, or at the same time on        *)',
           '(* several domains with the parallel backend of common/par.ml (HOL_PAR=1,    *)',
           '(* S2N_PAR_DOMAINS). At the end, the theorems of the top-level functions are *)',
           '(* closed: each assumption is discharged by the theorem proved for it, so    *)',
           '(* the theorems below have no assumptions.                                   *)',
           '(* ========================================================================= *)',
           '', 'needs "%s";;' % (relative % isa), '',
           '(* Each proof file as a functor, after the files that it loads *)', '']

    # Module names in lower case after the prefix: pa_j does not read some
    # names with capitals, such as Par_job_H_44.
    modules = {}
    def module(x):
        m = 'Par_job_' + x.lower()
        if modules.setdefault(m, x) != x:
            sys.exit('native_link.py: two jobs named %s' % m)
        return m
    costs = read_costs(prf)
    for x in order:
        out += ['needs "%s";;' % l for l in file_needs('%s/%s_proof.ml' % (prf, x))]
        out += ['module %s (Par_unit : sig end) = struct' % module(x),
                'needs "%s%s_proof.ml";;' % (here, x), 'end;;', '']

    out += ['(* The jobs, and the theorems of the top-level functions *)', '',
            'let par_link_results = par_run_jobs [']
    for x in order:
        c = costs.get(x, os.path.getsize('%s/%s_proof.ml' % (prf, x)) / 100.0)
        ts = top_thms.get(x, [])
        out += ['  "%s", %.1f,' % (x, c),
                '  (fun () -> let module Par_this = %s (struct end) in' % module(x)]
        if not ts:
            out[-1] += ' []);'
        for k, t in enumerate(ts):
            out.append('     %s"%s", Par_this.%s%s'
                       % ('[' if k == 0 else ' ', t, t,
                          ']);' if k == len(ts) - 1 else ';'))
    out += ['];;', '',
            'let par_link_thm name = assoc name (flat par_link_results);;', '']
    if tail_files:
        out += ['(* The theorems stated with %s, at the top level *)'
                % re.sub(r'([A-Z]+)([0-9]+)', r'\1 \2', tail.upper()), '']
        out += ['needs "%s%s";;' % (here, f) for f in tail_files]
        out.append('')
    if open_specs:
        out += ['(* The contracts stated and proved, and the open ones, of the spec files',
                '   without a proof file: %s *)' % ', '.join(open_specs), '',
                'let relative_allowed_open = %s;;' % allowed_tm, '',
                'relative_report_open relative_allowed_open;;', '']
        for t in job_thms:
            out += ['let %s =' % t, '  relative_close_open relative_allowed_open (par_link_thm "%s");;' % t,
                    'relative_print_open "%s" %s;;' % (t, t), '']
        for t in tail_thms:
            out += ['let %s =' % t, '  relative_close_open relative_allowed_open %s;;' % t,
                    'relative_print_open "%s" %s;;' % (t, t), '']
    else:
        out += ['(* The contracts stated and proved, and those not proved, if any *)', '',
                'relative_report ();;', '']
        for t in job_thms:
            out += ['let %s =' % t, '  relative_close (par_link_thm "%s");;' % t, '']
        for t in tail_thms:
            out += ['let %s =' % t, '  relative_close %s;;' % t, '']

    full = [t for t in thms if t.endswith('_FULL') or
            (tail and t.endswith('_' + tail.upper()))]
    if full:
        out += ['(* The theorems that the build does not print itself *)', '']
        for t in full:
            out += ['Printf.printf "val %s : thm = %%s\\n" (string_of_thm %s);;' % (t, t)]
        out.append('')
    sys.stdout.write('\n'.join(out))

if __name__ == '__main__':
    main()
