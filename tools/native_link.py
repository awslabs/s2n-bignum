#!/usr/bin/env python3

# Generate the link file of a build of mlkem-native or mldsa-native, which
# proves all the theorems of the build in one session and then turns the
# theorems of the top-level functions into theorems without assumptions
# (see common/relative.ml). It serves both instruction sets: run it in
# s2n-bignum's arm or x86 directory.
#
# Each proof file X_proof.ml proves the theorems of its spec file X_spec.ml
# relative to the contracts of its callees, so the proof files do not
# depend on each other. The link file makes each of them the body of a
# functor Par_job_X, placed after the files that X_proof.ml loads (but see
# "Files loaded in a job" below), so that its names mean what they would
# mean there. The spec files come callees
# first, each after the spec files that it loads, in the order of the
# needs. par_run_jobs (common/par.ml) runs the jobs, costliest first: one
# after the other by default, at the same time on S2N_PAR_DOMAINS domains
# when built with HOL_PAR=1.
#
# The top-level functions are the API functions of the family that the
# build has proofs for; if it has none, the functions whose files no other
# file loads. The theorems of their proof files that the jobs return are
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
# A proof file can load a standalone proof with `loadt "path";;` (on a line of
# its own) instead of needs, to run it inside its job: a build of the ML-KEM
# API in assembly proves the contracts of its kernels from the standalone
# proofs of the library, which should not run before the jobs, one after the
# other, nor be run by each caller. What the loaded file loads with needs is
# loaded before the jobs, as the files that the proof file loads itself
# (other than those that only its job loads, see below).
#
# Files loaded in a job. The files that the proof files load are loaded one
# after the other before par_run_jobs, so the lemmas that they prove do not
# run at the same time. In the builds of IN_JOB_BUILDS, a file that only one
# job loads (directly or not, and that no spec file, no file of the tail and
# no other job loads) is loaded in that job instead, after the files before
# the jobs, if it is safe to:
# it uses no goal stack; it does not change the parser, the lexer or the
# interface; it makes no definition (new_definition, new_type, ...); it
# changes no global state other than refs that it defines itself (these
# belong to the module of the job); it defines no name at the top level
# that another file of the link defines differently, other than the
# contract of a spec file, which the proof of the contract proves under
# its name; and every file of the job sees, for each name it uses, the
# definition that it sees when the proof file runs on its own (the files
# loaded in the job come after the others, which may change the order).
# Otherwise the file, and what it loads, stays before the jobs. The checks
# read the text of the files (without comments and strings) and err on the
# side of keeping a file before the jobs. native_link.py writes to stderr
# the files that it loads in each job and why the others stay. The link
# files of the other builds load all these files before the jobs: loading
# a file in a job changes the order of the loads, so a build joins
# IN_JOB_BUILDS only together with a run of its new link file.
#
# The cost of a job is its time in seconds from the file link_costs.tsv of
# the build directory (lines "X<tab>seconds", see link_costs.py), if it
# lists X, and otherwise estimated from the size of the proof file.
#
# Usage, in s2n-bignum's arm or x86 directory:
#
#   python3 ../tools/native_link.py mldsa_native gcc12_O2 \
#     > proofs/mldsa_native/gcc12_O2/link.ml

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
        'tail': 'fips204'}}

# The builds whose link files load in a job the files that only that job
# loads (see "Files loaded in a job" above), as <isa>/<family>/<build>
IN_JOB_BUILDS = set([
    'arm/mldsa_native/clang23_O3_mono_reduced_ram',
    'x86/mldsa_native/clang23_O3_mono_reduced_ram'])

# The wrapper of common/relative.ml for the instruction set, which the spec
# files of both families load.
RELATIVE = '%s/proofs/mlkem_native/relative.ml'

NEEDS = re.compile(r'\s*needs\s+"([^"]+)"\s*;;')
LOADT = re.compile(r'\s*loadt\s+"([^"]+)"\s*;;')
THM = re.compile(r'^let\s+([A-Z0-9_]+_SUBROUTINE_(CORRECT|SAFE|FULL))\s*=', re.M)

def file_needs(path):
    """The files that path loads with needs, in order."""
    return [m.group(1) for l in open(path) for m in [NEEDS.match(l)] if m]

LOADS = {}

def file_loads(path):
    """The files that path loads with needs or loadt, in order, as pairs
    (kind, file)."""
    if path not in LOADS:
        LOADS[path] = [(k, m.group(1)) for l in open(path)
                       for k, r in (('needs', NEEDS), ('loadt', LOADT))
                       for m in [r.match(l)] if m]
    return LOADS[path]

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

# ---------------------------------------------------------------------------
# The files that only one job loads (see "Files loaded in a job" above). The
# paths are relative to the root of the repository, as in needs; a path that
# is not in it is a file of HOL Light (such as Library/words.ml).
# ---------------------------------------------------------------------------

def in_repo(f):
    return os.path.exists('../' + f)

def load_order(f, seen, parts=None):
    """The files whose bodies loading f with needs runs, in order, f last:
    each file loaded with needs once (seen holds those loaded before), each
    file loaded with loadt each time, added to parts."""
    out = []
    def load(p, kind):
        if kind == 'needs':
            if p in seen: return
            seen.add(p)
        elif parts is not None:
            parts.add(p)
        if in_repo(p):
            for k, q in file_loads('../' + p): load(q, k)
        out.append(p)
    load(f, 'needs')
    return out

ML_CODE = re.compile(r'\(\*|"(?:[^"\\]|\\.)*"|\'"\'|`')
ML_COMMENT = re.compile(r'\(\*|\*\)|"(?:[^"\\]|\\.)*"')

def ml_code(path, quotations):
    """The text of an OCaml file without its comments and strings, and
    without the HOL quotations `...` if quotations is false; the lines are
    kept."""
    s = open(path, errors='replace').read()
    out = []; i = 0; n = len(s)
    while i < n:
        m = ML_CODE.search(s, i)
        if not m:
            out.append(s[i:]); break
        out.append(s[i:m.start()])
        t = m.group(0)
        if t == '(*':
            depth = 1; j = m.end()
            while depth and j < n:
                c = ML_COMMENT.search(s, j)
                if not c:
                    j = n; break
                depth += {'(*': 1, '*)': -1}.get(c.group(0), 0)
                j = c.end()
            out.append('\n' * s.count('\n', m.start(), j)); i = j
        elif t == '`':
            j = s.find('`', m.end())
            j = n if j < 0 else j + 1
            out.append(s[m.start():j] if quotations else
                       ' ' + '\n' * s.count('\n', m.start(), j))
            i = j
        else:
            out.append('""' + '\n' * t.count('\n')); i = m.end()
    return ''.join(out)

DEF = re.compile(r'^(?:let|and)\s+(?:rec\s+)?([A-Za-z_][\w\']*)', re.M)
NAME = re.compile(r'[A-Za-z_][\w\']*')

class MlFile:
    """What a file defines at the top level (each name with the text of its
    definition, up to ;;) and the names that it uses."""
    def __init__(self, f):
        self.full = code = ml_code('../' + f, True) if in_repo(f) else ''
        self.defs = {}
        ms = list(DEF.finditer(code))
        for k, m in enumerate(ms):
            end = ms[k + 1].start() if k + 1 < len(ms) else len(code)
            e = code.find(';;', m.start(), end)
            self.defs[m.group(1)] = ' '.join(code[m.start():e if e >= 0 else end].split())
        self.code = ml_code('../' + f, False) if in_repo(f) else ''
        self.uses = set(NAME.findall(self.code)) - set(self.defs)

# What makes a file unsafe to load in a job, which runs on a domain of its own
# with the other jobs (see common/par.ml): the goal stack, changes of the
# parser, the lexer or the interface, definitions, and changes of state that
# the file does not make itself.
UNSAFE = [
    (re.compile(r'^(?:g|e|b|r|p)\s*[(`]|\b(?:set_goal|top_thm|top_goal|'
                r'current_goalstack|flush_goalstack)\b', re.M),
     'uses the goal stack'),
    (re.compile(r'\b(?:parse_as_\w+|unparse_as_\w+|override_interface|'
                r'overload_interface|make_overloadable|reduce_interface|'
                r'remove_interface|prioritize_\w+|reserve_words|'
                r'unreserve_words|new_type_abbrev|remove_type_abbrev|'
                r'set_jrh_lexer|install_parser|delete_parser|'
                r'install_user_printer|delete_user_printer)\b|'
                r'^let\s+(?:rec\s+)?(?:parse_term|parse_type|parse_preterm|'
                r'parse_pretype|lex|quotexpander)\b', re.M),
     'changes the parser, the lexer or the interface'),
    (re.compile(r'\b(?:new_\w*definition|new_specification|new_constant|'
                r'new_type|new_type_definition|new_basic_type_definition|'
                r'new_axiom|new_inductive_\w+|define|define_\w+)\b'),
     'makes a definition'),
    (re.compile(r'\b(?:install_layout|extend_basic_\w+|set_basic_\w+|'
                r'Hashtbl\.(?:add|replace|remove|clear|reset))\b'),
     'changes global state')]
ASSIGN = re.compile(r'(?<![\w.\'])([A-Za-z_][\w\']*)\s*(?::=|<-)|'
                    r'\b(?:incr|decr)\s+([A-Za-z_][\w\']*)')

def par_unsafe(m):
    """Why the file of MlFile m is not safe to load in a job, or None."""
    for k, (r, why) in enumerate(UNSAFE):
        if r.search(m.full if k == 0 else m.code):
            return why
    for a in ASSIGN.finditer(m.code):
        v = a.group(1) or a.group(2)
        if not re.match(r'let\s+(?:rec\s+)?%s\s*=\s*ref\b' % re.escape(v),
                        m.defs.get(v, '')):
            return 'changes %s, which it does not define' % v
    return None

def place_files(isa, jobs, top_files, in_jobs):
    """For the jobs (name -> path of the proof file), the files that only
    that job loads and that are safe to load in it; the other files that
    only it loads, with the reason they stay before the jobs. top_files are
    loaded at the top level in any case (relative.ml, the spec files and the
    tail) and so are the files that they load. If in_jobs is false (a build
    not in IN_JOB_BUILDS), all files but those loaded with loadt are."""
    parts = set()
    alone = dict((x, load_order(p, set(), parts)) for x, p in jobs.items())
    users = {}
    for x, seq in alone.items():
        for f in seq:
            if f != jobs[x]:
                users.setdefault(f, set()).add(x)
    top = set()
    def add_top(f):
        for g in load_order(f, set()):
            top.add(g)
    for f in top_files:
        add_top(f)
    for f, us in users.items():
        if f not in parts and (len(us) > 1 or not in_repo(f) or not in_jobs):
            add_top(f)
    ml = {}
    def get(f):
        if f not in ml: ml[f] = MlFile(f)
        return ml[f]
    # The definitions of every file of the link that is not a proof file
    defs = {}
    for f in set(f for seq in alone.values() for f in seq) | top:
        if f not in jobs.values():
            for d, t in get(f).defs.items():
                defs.setdefault(d, {})[f] = t
    stay = {}
    def keep(f, why):
        if f not in top and f not in parts and f not in stay:
            stay[f] = why
            add_top(f)
    for f, us in sorted(users.items()):
        if f in top or f in parts:
            continue
        m = get(f)
        why = par_unsafe(m)
        if why is None:
            for d, t in sorted(m.defs.items()):
                # The contract that a spec file states with assume_spec is
                # what the proof of its job proves, under the same name.
                other = [g for g, u in defs[d].items() if g != f and u != t and
                         not u.startswith('let %s = assume_spec ' % d)]
                if other:
                    why = 'defines %s differently from %s' % (d, other[0])
                    break
        if why:
            keep(f, why)
    # Each file of a job must see, for the names it uses, the definitions it
    # sees when the proof file is run on its own; otherwise the file that
    # makes the difference stays before the jobs.
    definers = {}
    for f in set(f for seq in alone.values() for f in seq):
        for d in get(f).defs:
            definers.setdefault(d, []).append(f)
    def last(fs, pos, limit):
        """The file of fs that comes last before limit in the order pos."""
        best = None
        for f in fs:
            p = pos.get(f)
            if p is not None and p < limit and (best is None or p > pos[best]):
                best = f
        return best
    changed = True
    while changed:
        changed = False
        seen = set(); toppos = {}
        def load_top(f):
            for g in load_order(f, seen):
                toppos.setdefault(g, len(toppos))
        load_top(RELATIVE % isa)
        for x in jobs:
            injob = set(f for f in alone[x] if f not in top or f in parts)
            for f in job_prelude(jobs[x], injob, set()):
                load_top(f)
            if all(f in parts or f == jobs[x] for f in injob):
                continue
            seq = alone[x]; apos = {}; jpos = {}
            for k, g in enumerate(seq):
                apos.setdefault(g, k)
                if g in injob:
                    jpos.setdefault(g, len(jpos))
            limit = len(toppos)
            for g in jpos:
                for u in get(g).uses:
                    fs = definers.get(u)
                    if not fs:
                        continue
                    a = last(fs, apos, apos[g])
                    b = last(fs, jpos, jpos[g]) or last(fs, toppos, limit)
                    if a and b and a != b and get(a).defs[u] != get(b).defs[u]:
                        for h in (g, a, b):
                            if h in injob and h != jobs[x] and h not in parts:
                                keep(h, 'the link would change the %s that %s sees'
                                     % (u, g))
                                changed = True
            if changed:
                break
    inner = dict((x, [f for f in alone[x] if f not in top and f != jobs[x] and
                      f not in parts]) for x in jobs)
    return inner, top, stay, parts

def job_prelude(path, injob, seen):
    """The files that the link file loads with needs before the job of the
    proof file path, given the files injob that are loaded in it (path, what
    it loads with loadt, and the files that only it loads): those that the
    files of the job load with needs and that are not in the job themselves,
    in the order of their needs. Without files that only it loads, these are
    the files that path loads with needs and that the files it loads with
    loadt load with needs."""
    out = []
    for kind, f in file_loads('../' + path):
        if f in injob and in_repo(f):
            if f not in seen:
                seen.add(f)
                out += job_prelude(f, injob, seen)
        elif kind == 'needs':
            out.append(f)
    return out

def main():
    if len(sys.argv) != 3 or sys.argv[1] not in FAMILIES:
        sys.exit('usage: native_link.py (%s) BUILD' % '|'.join(sorted(FAMILIES)))
    family, build = sys.argv[1], sys.argv[2]
    isa = os.path.basename(os.getcwd())
    if isa not in ('arm', 'x86'):
        sys.exit('native_link.py: run it in the arm or x86 directory')
    api = re.compile(FAMILIES[family]['api'])
    tail = FAMILIES[family]['tail']
    prf = 'proofs/%s/%s' % (family, build)
    here = '%s/%s/' % (isa, prf)

    # The proof files, callees first
    files = sorted(f[:-9] for f in os.listdir(prf) if f.endswith('_proof.ml'))
    deps = dict((x, [l[len(here):-8] for l in file_needs('%s/%s_spec.ml' % (prf, x))
                     if l.startswith(here) and l.endswith('_spec.ml')])
                for x in files)
    order = []; seen = set()
    def visit(x, path):
        if x in seen: return
        if x in path: sys.exit('native_link.py: circular needs at ' + x)
        for y in deps[x]: visit(y, path + [x])
        seen.add(x); order.append(x)
    for x in files: visit(x, [])

    # The theorems to close: those of the top-level functions and the tail
    top = [x for x in files if api.match(x)]
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
           '', 'needs "%s";;' % (RELATIVE % isa), '',
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
    jobs = dict((x, '%s%s_proof.ml' % (here, x)) for x in order)
    specs = ['%s%s' % (here, f) for f in sorted(os.listdir(prf))
             if f.endswith('_spec.ml')]
    inner, ontop, stay, parts = place_files(
        isa, jobs,
        [RELATIVE % isa] + specs + [here + f for f in tail_files],
        '%s/%s/%s' % (isa, family, build) in IN_JOB_BUILDS)
    for x in order:
        if inner[x]:
            sys.stderr.write('native_link.py: in the job %s: %s\n'
                             % (x, ' '.join(inner[x])))
    for f, why in sorted(stay.items()):
        sys.stderr.write('native_link.py: before the jobs: %s: %s\n' % (f, why))
    for x in order:
        injob = set(f for f in load_order(jobs[x], set())
                    if f not in ontop or f in parts)
        out += ['needs "%s";;' % l
                for l in job_prelude(jobs[x], injob, set())]
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
