#!/usr/bin/env python3

# Generate the layout file of an AArch64 libmlkem.so from mlkem-native, the
# HOL Light file that gives names to the addresses and sizes in the binary
# for common/layout.ml (see mlkem_native/README.md).
#
# Usage: gen_layout.py [--objdump OBJDUMP] [--nm NM] [--readelf READELF]
#                      BINARY > LAYOUT.ml
#
# For example, in s2n-bignum's arm directory:
#
#   python3 mlkem_native/gen_layout.py \
#     <mlkem-native>/binaries/multilevel/gcc12/O2/libmlkem.so \
#     > proofs/mlkem_native/gcc12_O2/layout.ml
#
# Everything comes from the ELF file: the symbol table, the section
# headers, the dynamic relocations and the disassembly of the code (by
# objdump), from which the labels inside the functions are found by an
# analysis of the control flow. No debug information is needed. The tools
# default to objdump, nm and readelf, or the environment variables
# OBJDUMP, NM and READELF; on a host that is not AArch64 use those of a
# cross toolchain, e.g. --objdump aarch64-linux-gnu-objdump.

import argparse, collections, hashlib, os, re, subprocess, sys, textwrap

BRANCH = re.compile(r'^(b|b\.\w+|cbz|cbnz|tbz|tbnz)$')
CLONE = re.compile(r'\.(constprop|isra|part|cold)\.\d+$')

def run(cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout

# ---------------------------------------------------------------------------
# Reading the binary
# ---------------------------------------------------------------------------

def disassemble(objdump, path):
    """The code at each symbol objdump shows, as (symbol, [(address,
    mnemonic, operands), ...]) by the address of the symbol."""
    funcs = collections.OrderedDict(); cur = None
    for l in run([objdump, '-d', '--no-show-raw-insn', path]).splitlines():
        m = re.match(r'^([0-9a-f]+) <(.*)>:', l)
        if m:
            cur = int(m.group(1), 16); funcs[cur] = (m.group(2), []); continue
        m = re.match(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$', l)
        if m and cur is not None:
            funcs[cur][1].append((int(m.group(1), 16), m.group(2), m.group(3)))
    return funcs

def symbols(nm, path):
    out = []
    for l in run([nm, '-S', '--defined-only', path]).splitlines():
        p = l.split()
        if len(p) == 4:
            out.append((int(p[0], 16), int(p[1], 16), p[2], p[3]))
    return out

def sections(readelf, path):
    sec = {}
    for l in run([readelf, '-SW', path]).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)', l)
        if m:
            sec[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16))
    return sec

def got_slots(readelf, path):
    got = {}
    for l in run([readelf, '-rW', path]).splitlines():
        p = l.split()
        if len(p) >= 5 and p[2] in ('R_AARCH64_JUMP_SLOT', 'R_AARCH64_GLOB_DAT'):
            got[p[4]] = int(p[0], 16)
    return got

def target(operands):
    m = re.search(r'\b([0-9a-f]+) <', operands)
    return int(m.group(1), 16) if m else None

# ---------------------------------------------------------------------------
# Labels inside a function, from its control flow graph
# ---------------------------------------------------------------------------

def control_flow(code):
    lo = code[0][0]; hi = code[-1][0] + 4
    op = {x: (o, a) for x, o, a in code}
    leaders = {lo}
    for x, o, a in code:
        if BRANCH.match(o) or o in ('ret', 'br'):
            if x + 4 < hi:
                leaders.add(x + 4)
            t = target(a)
            if BRANCH.match(o) and t is not None and lo <= t < hi:
                leaders.add(t)
    leaders = sorted(leaders); blocks = {}
    for i, s in enumerate(leaders):
        e = leaders[i + 1] if i + 1 < len(leaders) else hi
        blocks[s] = [x for x, _, _ in code if s <= x < e]
    succ = {}
    for s, ins in blocks.items():
        last = ins[-1]; o, a = op[last]; t = target(a); out = []
        if o in ('ret', 'br'):
            pass
        elif o == 'b':
            if t is not None and lo <= t < hi:
                out.append(t)
        else:
            if BRANCH.match(o) and t is not None and lo <= t < hi:
                out.append(t)
            if last + 4 < hi:
                out.append(last + 4)
        succ[s] = out
    pred = collections.defaultdict(list)
    for u, vs in succ.items():
        for v in vs:
            pred[v].append(u)
    return blocks, succ, pred, op

def dominators(blocks, pred, entry):
    nodes = sorted(blocks)
    dom = {n: set(nodes) for n in nodes}; dom[entry] = {entry}
    changed = True
    while changed:
        changed = False
        for n in nodes:
            if n == entry:
                continue
            ps = [dom[p] for p in pred[n]]
            new = {n} | (set.intersection(*ps) if ps else set())
            if new != dom[n]:
                dom[n] = new; changed = True
    return dom

def natural_loops(blocks, succ, pred, entry):
    """(header, sorted blocks of the loop) for each header, by address."""
    dom = dominators(blocks, pred, entry)
    loops = collections.defaultdict(set)
    for u, vs in succ.items():
        for h in vs:
            if h in dom[u]:                 # a back edge u -> h
                body = {h}; stack = []
                if u != h:
                    body.add(u); stack.append(u)
                while stack:
                    x = stack.pop()
                    for p in pred[x]:
                        if p not in body:
                            body.add(p); stack.append(p)
                loops[h] |= body
    return [(h, sorted(loops[h])) for h in sorted(loops)]

def labels(code, callee_name):
    """The labels of a function, as offsets from its start (see LABELS)."""
    lo = code[0][0]; hi = code[-1][0] + 4; L = collections.OrderedDict()
    blocks, succ, pred, op = control_flow(code)
    loops = natural_loops(blocks, succ, pred, lo)
    for k, (h, body) in enumerate(loops, 1):
        p = 'loop%d' % k; L[p] = h; inside = set(body)
        exits = []                          # (branch, target or None)
        for b in body:
            last = blocks[b][-1]
            for t in succ[b]:
                if t not in inside:
                    exits.append((last, t))
            o, a = op[last]
            if o == 'ret' or (o == 'b' and target(a) is not None and not lo <= target(a) < hi):
                exits.append((last, None))
        exits.sort()
        targets = sorted(set(t for _, t in exits if t is not None))
        for j, t in enumerate(targets, 1):
            L[p + '_exit' + ('' if len(targets) == 1 else str(j))] = t
        for j, (x, t) in enumerate(exits, 1):
            sfx = '' if len(exits) == 1 else str(j)
            o, a = op[x]
            if BRANCH.match(o) and o != 'b':
                L[p + '_test' + sfx] = x - 4
                if x + 4 in inside:
                    L[p + '_next' + sfx] = x + 4
        latches = [blocks[b][-1] for b in body if h in succ[b]]
        if len(latches) == 1:
            L[p + '_back'] = latches[0]
    headers = set(h for h, _ in loops); j = 0
    npred = collections.Counter(t for b in blocks for t in succ[b])
    for b in sorted(blocks):
        if b != lo and b not in headers and npred[b] >= 2:
            j += 1; L['join%d' % j] = b
    rets = [x for x, o, _ in code if o == 'ret']
    for k, x in enumerate(rets, 1):
        L['ret' if len(rets) == 1 else 'ret%d' % k] = x
    calls = [(x, callee_name(re.search(r'<([^>+]+)', a).group(1), target(a)))
             for x, o, a in code if o == 'bl']
    count = collections.Counter(c for _, c in calls); seen = collections.Counter()
    for x, c in calls:
        seen[c] += 1
        L['after_' + c + ('' if count[c] == 1 else '_%d' % seen[c])] = x + 4
    for k, x in enumerate([x for x, o, _ in code if o == 'adrp'], 1):
        L['adrp%d' % k] = x
    return collections.OrderedDict((n, v - lo) for n, v in L.items())

# ---------------------------------------------------------------------------
# The layout
# ---------------------------------------------------------------------------

class Layout:
    def __init__(self, path, objdump, nm, readelf):
        self.path = path
        code = disassemble(objdump, path)
        syms = symbols(nm, path)
        sec = sections(readelf, path)
        self.image_size = sum(sec['.rodata'])
        self.rodata = sec['.rodata']
        fsyms = sorted(s for s in syms if s[2] in 'tT')
        # Names: without a clone suffix if that is unambiguous, and numbered
        # by address if several functions have the same name (e.g. static
        # functions of the same name in different source files)
        base = collections.Counter(CLONE.sub('', s[3]) for s in set(fsyms))
        def plain(sym):
            b = CLONE.sub('', sym)
            return (b if base[b] == 1 or b == sym else sym).replace('.', '_')
        count = collections.Counter(plain(n) for a, sz, t, n in fsyms)
        seen = collections.Counter(); self.names = {}
        for a, sz, t, n in fsyms:
            p = plain(n); seen[p] += 1
            self.names[a, n] = p if count[p] == 1 else '%s_%d' % (p, seen[p])
        by_sym = collections.defaultdict(list)
        for a, sz, t, n in fsyms:
            by_sym[n].append(a)
        def fname(sym, addr=None):
            """The name of a symbol, or of the callee of a call to it."""
            if sym.endswith('@plt'):
                return sym[:-4].lstrip('_')
            if (addr, sym) not in self.names:
                addr = by_sym[sym][0] if len(by_sym[sym]) == 1 else None
            return self.names[addr, sym] if addr is not None else plain(sym)
        self.functions = collections.OrderedDict()
        for a, sz, t, n in fsyms:
            self.functions[self.names[a, n]] = (a, sz)
        # objdump shows the code under only one of several symbols at the
        # same address (e.g. after GCC's identical code folding), so the
        # code of a function is found by its address
        self.labels = {self.names[a, n]: labels(code[a][1], fname) for a, sz, t, n in fsyms}
        self.data = collections.OrderedDict(
            ('rodata_' + n, (a, sz)) for a, sz, t, n in sorted(syms) if t in 'rR')
        self.plt = collections.OrderedDict(
            (m.group(1).lstrip('_'), a) for a, (s, _) in code.items()
            for m in [re.match(r'(.*)@plt$', s)] if m)
        self.got = collections.OrderedDict(
            (s.lstrip('_'), a) for s, a in sorted(got_slots(readelf, path).items(), key=lambda x: x[1]))
        # Vectors of constants without symbols, loaded with ADRP and LDR
        # (of a Q, D or S register) by each function
        named = [(a, a + sz) for a, sz in self.data.values()]
        self.consts = collections.OrderedDict()
        width = {'q': 16, 'd': 8, 's': 4}
        for a, sz, t, n in fsyms:
            page = {}; used = {}
            for x, o, args in code[a][1]:
                m = re.match(r'(x\d+), ([0-9a-f]+) <', args)
                if o == 'adrp' and m:
                    page[m.group(1)] = int(m.group(2), 16); continue
                m = re.match(r'([qds])\d+, \[(x\d+), #(\d+)\]', args)
                if o == 'ldr' and m and m.group(2) in page:
                    v = page[m.group(2)] + int(m.group(3))
                    if self.rodata[0] <= v < self.image_size and \
                       not any(lo <= v < hi for lo, hi in named):
                        used[v] = max(used.get(v, 0), width[m.group(1)])
            if used:
                self.consts[self.names[a, n]] = sorted(used.items())

    def objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.functions.items()]
        return sorted(rows, key=lambda r: r[1])

    def data_objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.data.items()]
        for f, vs in self.consts.items():
            rows.append((f + '_consts', vs[0][0], vs[-1][0] + vs[-1][1] - vs[0][0]))
            if len(vs) > 1:
                for k, (v, w) in enumerate(vs, 1):
                    rows.append((f + '_const%d' % k, v, w))
        return sorted(rows, key=lambda r: (r[1], -r[2], r[0]))

    def check_names(self):
        names = collections.Counter(['libmlkem_size'])
        for n, a, sz in self.objects() + self.data_objects():
            names[n] += 1; names[n + '_size'] += 1
        for f, ls in self.labels.items():
            for l in ls:
                names[f + '_' + l] += 1
        for s in self.plt:
            names['plt_' + s] += 1; names['plt_' + s + '_size'] += 1
        for s in self.got:
            names['got_' + s] += 1
        dup = [n for n, c in names.items() if c > 1]
        if dup:
            sys.exit('gen_layout.py: names defined twice: ' + ' '.join(sorted(dup)))
        return len(names)

# ---------------------------------------------------------------------------
# Writing the HOL Light file
# ---------------------------------------------------------------------------

LABELS = '''\
Functions are named after their symbols, without a suffix such as
".constprop.0" that GCC adds to a specialized copy (unless that would
make two names the same), and with any other dots replaced by
underscores. A function f has the names f for its address and f_size for
its size, and a label l inside it has the name f_l for its address. The
labels are found from the control flow graph of the function:

 - loopK is the header of the K-th natural loop of the function (found
   from the dominators of the control flow graph), counting by the
   address of the header;
 - loopK_test is the instruction before a conditional branch out of the
   loop (usually the comparison that sets the flags for it), loopK_next
   is the instruction after such a branch if it is inside the loop, and
   loopK_back is the branch back to the header; these have a further
   number if the loop has several such branches;
 - loopK_exit is the target of the branches out of the loop, numbered if
   there are several;
 - joinK is the K-th instruction outside the loops with more than one
   predecessor in the control flow graph;
 - after_g is the instruction after the call of g, numbered if there are
   several calls of g;
 - ret is the return instruction, numbered if there are several, and
   adrpK is the K-th ADRP instruction.

The read-only data are the tables with symbols, named after the symbol
with "rodata_" in front (e.g. rodata_mlk_zetas, since mlk_zetas is the
HOL constant for its contents), and the vectors of constants without
symbols that the functions load with ADRP and LDR: for a function f,
f_consts is the block of all of them and, if there are several,
f_constK is the K-th one. The linker merges equal constants, so some
have several names. plt_g and got_g are the entry of the procedure
linkage table and the slot of the global offset table (GOT, which is not
part of the image) for an external symbol g, and libmlkem_size is the
size of the image, from address 0 to the end of the read-only data.'''

def box(text):
    out = []
    for para in text.split('\n\n'):
        if para.startswith(' - '):
            for it in para[3:].split('\n - '):
                out += textwrap.wrap(' '.join(it.split()), 73,
                                     initial_indent=' - ', subsequent_indent='   ')
        else:
            out += textwrap.wrap(' '.join(para.split()), 73)
        out.append('')
    return '\n'.join(('(* %-73s *)' % l).rstrip() if not l else '(* %-73s *)' % l
                     for l in out[:-1])

def table(rows):
    w = max(len(r[0]) for r in rows) + 3
    return '\n'.join('  %-*s 0x%04x, 0x%03x%s' % (w, '"%s",' % n, a, sz,
                     ';' if i + 1 < len(rows) else '') for i, (n, a, sz) in enumerate(rows))

def label_table(lay):
    out = []
    fs = [f for f, _ in sorted(lay.functions.items(), key=lambda x: x[1][0]) if lay.labels[f]]
    for i, f in enumerate(fs):
        items = ['"%s",0x%x' % (l, o) for l, o in
                 sorted(lay.labels[f].items(), key=lambda x: (x[1], x[0]))]
        lines = []; cur = '   ['
        for j, it in enumerate(items):
            piece = it + ('; ' if j + 1 < len(items) else ']')
            if len(cur) + len(piece) > 74:
                lines.append(cur.rstrip()); cur = '    '
            cur += piece
        lines.append(cur + (';' if i + 1 < len(fs) else ''))
        out.append('  "%s",\n%s' % (f, '\n'.join(lines)))
    return '\n'.join(out)

def rule(title):
    return '(* %s *)\n(* %-73s *)\n(* %s *)' % ('-' * 73, title, '-' * 73)

def write(lay, name, out):
    digest = hashlib.sha256(open(lay.path, 'rb').read()).hexdigest()
    intro = ('The layout of the binary %s of mlkem-native (see mlkem_native/README.md): '
             'names for the addresses in it, as offsets from the start of the image, and '
             'the sizes of its functions and data, for common/layout.ml. The proofs use '
             'these names, not the addresses themselves.\n\n'
             'This file is generated by mlkem_native/gen_layout.py from the binary with '
             'SHA-256 %s. Do not edit it by hand.\n\n' % (name, digest)) + LABELS
    out.write('(*\n * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.\n'
              ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n *)\n\n')
    out.write('(* %s *)\n%s\n(* %s *)\n\n' % ('=' * 73, box(intro), '=' * 73))
    out.write('needs "common/layout.ml";;\n\n')
    out.write('%s\n\ninstall_layout ["libmlkem_size",0x%x];;\n\n' %
              (rule('The size of the image.'), lay.image_size))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The functions, as (name, address, size).'), table(lay.objects())))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The read-only data, as (name, address, size).'), table(lay.data_objects())))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The entries of the procedure linkage table.'),
               table([('plt_' + s, a, 16) for s, a in sorted(lay.plt.items(), key=lambda x: x[1])])))
    out.write('%s\n\ninstall_layout [\n%s];;\n\n' %
              (rule('The slots of the global offset table.'),
               ';\n'.join('  "got_%s",0x%x' % (s, a) for s, a in lay.got.items())))
    out.write('%s\n\ninstall_layout (layout_labels [\n%s]);;\n' %
              (rule('The labels in the functions, as offsets from their start.'), label_table(lay)))

def main():
    ap = argparse.ArgumentParser(description='Generate the layout file of a libmlkem.so')
    ap.add_argument('binary')
    ap.add_argument('--name', help='name of the build in the header, e.g. "gcc 12 -O2"')
    ap.add_argument('--objdump', default=os.environ.get('OBJDUMP', 'objdump'))
    ap.add_argument('--nm', default=os.environ.get('NM', 'nm'))
    ap.add_argument('--readelf', default=os.environ.get('READELF', 'readelf'))
    args = ap.parse_args()
    lay = Layout(args.binary, args.objdump, args.nm, args.readelf)
    lay.check_names()
    write(lay, args.name or os.path.basename(args.binary), sys.stdout)

if __name__ == '__main__':
    main()
