#!/usr/bin/env python3

# Generate the layout file of an x86-64 libmldsa.so from mldsa-native, the
# HOL Light file that gives names to the addresses and sizes in the binary
# for common/layout.ml (see mldsa_native/README.md).
#
# Usage: gen_layout.py [--objdump OBJDUMP] [--nm NM] [--readelf READELF]
#                      [--name NAME] BINARY > LAYOUT.ml
#
# For example, in s2n-bignum's x86 directory:
#
#   python3 mldsa_native/gen_layout.py --name multilevel/gcc12/O2/libmldsa.so \
#     <build>/multilevel/gcc12/O2/libmldsa.so \
#     > proofs/mldsa_native/gcc12_O2/layout.ml
#
# Everything comes from the ELF file: the symbol table, the section
# headers, the dynamic relocations, the disassembly of the code (by
# objdump, in Intel syntax) and the jump tables in the read-only data,
# from which the labels inside the functions are found by an analysis of
# the control flow. This is the x86-64 version of the script of the same
# name for AArch64, and gives the same names wherever the code has the
# same shape.

import argparse, collections, hashlib, os, re, struct, subprocess, sys
import textwrap

CLONE = re.compile(r'\.(constprop|isra|part|cold)\.\d+$')
PREFIXES = ('rep', 'repz', 'repnz', 'repe', 'repne', 'lock', 'data16', 'cs',
            'ds', 'es', 'ss', 'notrack', 'bnd')
WIDTH = {'BYTE': 1, 'WORD': 2, 'DWORD': 4, 'QWORD': 8, 'XMMWORD': 16,
         'YMMWORD': 32}

def run(cmd):
    return subprocess.run(cmd, check=True, capture_output=True,
                          text=True).stdout

def op_of(o):
    """The operation of a mnemonic without its prefixes, e.g. ret for
    "repz ret" and stos for "rep stos"."""
    return o.split()[-1]

def is_jcc(o):
    o = op_of(o)
    return o.startswith('j') and o != 'jmp'

def is_jmp(o):
    return op_of(o) == 'jmp'

def is_branch(o):
    return is_jcc(o) or is_jmp(o)

def is_ret(o):
    return op_of(o) == 'ret'

def is_call(o):
    return op_of(o) == 'call'

# ---------------------------------------------------------------------------
# Reading the binary
# ---------------------------------------------------------------------------

def disassemble(objdump, path):
    """The code at each symbol objdump shows, as (symbol, [(address,
    mnemonic, operands), ...]) by the address of the symbol. A mnemonic
    includes its prefixes, e.g. "rep stos", and the operands include
    objdump's comment with the address of a RIP-relative operand."""
    funcs = collections.OrderedDict(); cur = None
    for l in run([objdump, '-d', '--no-show-raw-insn', '-M', 'intel', '-w',
                  path]).splitlines():
        m = re.match(r'^([0-9a-f]+) <(.*)>:', l)
        if m:
            cur = int(m.group(1), 16); funcs[cur] = (m.group(2), []); continue
        m = re.match(r'^\s+([0-9a-f]+):\s+((?:(?:%s)\s+)*)(\S+)\s*(.*)$'
                     % '|'.join(PREFIXES), l)
        if m and cur is not None:
            o = ' '.join(m.group(2).split() + [m.group(3)])
            funcs[cur][1].append((int(m.group(1), 16), o,
                                  m.group(4).strip()))
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
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+'
                     r'[0-9a-f]+\s+([0-9a-f]+)', l)
        if m:
            sec[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16))
    return sec

def got_slots(readelf, path):
    got = {}
    for l in run([readelf, '-rW', path]).splitlines():
        p = l.split()
        if len(p) >= 5 and p[2] in ('R_X86_64_JUMP_SLOT',
                                    'R_X86_64_GLOB_DAT'):
            got[p[4]] = int(p[0], 16)
    return got

def target(operands):
    """The target of a direct branch or call."""
    m = re.match(r'([0-9a-f]+) <', operands)
    return int(m.group(1), 16) if m else None

def rip_target(operands):
    """The address of a RIP-relative operand, from objdump's comment."""
    m = re.search(r'\[rip\+0x[0-9a-f]+\]\s*#\s*([0-9a-f]+)', operands)
    return int(m.group(1), 16) if m else None

def rip_width(o, operands):
    """The size of a RIP-relative memory operand (0 for LEA)."""
    if op_of(o) == 'lea':
        return 0
    m = re.search(r'\b([A-Z]+) PTR \[rip', operands)
    return WIDTH.get(m.group(1), 0) if m else 0

# ---------------------------------------------------------------------------
# Jump tables: an indirect JMP of a register computed as
#
#      cmp   r9d, 0xc            the bound n - 1 of the index
#      ja    <default>
#      ...
#      lea   rdx, [rip+table]
#      movsxd rax, DWORD PTR [rdx+rax*4]
#      add   rax, rdx
#      jmp   rax
#
# whose targets are the table plus each of its n signed 32-bit entries.
# ---------------------------------------------------------------------------

def jump_table(code, k, data):
    """For the indirect JMP code[k], (table, entries, [targets])."""
    x, o, a = code[k]
    reg = a.strip()
    base = None; idx_bound = None
    for j in range(k - 1, max(-1, k - 12), -1):
        _, oj, aj = code[j]
        m = re.match(r'(\w+),\[rip\+0x[0-9a-f]+\]', aj)
        if op_of(oj) == 'lea' and m and base is None:
            base = rip_target(aj)
        m = re.match(r'(\w+),0x([0-9a-f]+)$', aj)
        if op_of(oj) == 'cmp' and m and idx_bound is None and \
           j + 1 < len(code) and op_of(code[j + 1][1]) == 'ja':
            idx_bound = int(m.group(2), 16)
    if base is None or idx_bound is None:
        sys.exit('gen_layout.py: unrecognized indirect jump at 0x%x' % x)
    n = idx_bound + 1
    targets = [(base + struct.unpack_from('<i', data, base + 4 * i)[0])
               & 0xffffffffffffffff for i in range(n)]
    return base, n, targets

# ---------------------------------------------------------------------------
# Labels inside a function, from its control flow graph
# ---------------------------------------------------------------------------

def control_flow(code, lo, hi, tables):
    op = {x: (o, a) for x, o, a in code}
    nxt = {code[i][0]: (code[i + 1][0] if i + 1 < len(code) else hi)
           for i in range(len(code))}
    leaders = {lo}
    for x, o, a in code:
        if is_branch(o) or is_ret(o):
            if nxt[x] < hi:
                leaders.add(nxt[x])
            t = target(a)
            if is_branch(o) and t is not None and lo <= t < hi:
                leaders.add(t)
            for t in tables.get(x, (None, 0, []))[2]:
                leaders.add(t)
    leaders = sorted(leaders); blocks = {}
    for i, s in enumerate(leaders):
        e = leaders[i + 1] if i + 1 < len(leaders) else hi
        blocks[s] = [x for x, _, _ in code if s <= x < e]
    succ = {}
    for s, ins in blocks.items():
        last = ins[-1]; o, a = op[last]; t = target(a); out = []
        if is_ret(o):
            pass
        elif is_jmp(o):
            if last in tables:
                out += sorted(set(tables[last][2]))
            elif t is not None and lo <= t < hi:
                out.append(t)
        else:
            if is_jcc(o) and t is not None and lo <= t < hi:
                out.append(t)
            if nxt[last] < hi:
                out.append(nxt[last])
        succ[s] = out
    pred = collections.defaultdict(list)
    for u, vs in succ.items():
        for v in vs:
            pred[v].append(u)
    return blocks, succ, pred, op, nxt

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

def labels(code, lo, hi, tables, callee_name):
    """The labels of a function, as offsets from its start (see LABELS)."""
    L = collections.OrderedDict()
    blocks, succ, pred, op, nxt = control_flow(code, lo, hi, tables)
    prev = {code[i + 1][0]: code[i][0] for i in range(len(code) - 1)}
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
            if is_ret(o) or (is_jmp(o) and last not in tables and
                             not (target(a) is not None and
                                  lo <= target(a) < hi)):
                exits.append((last, None))
        exits.sort()
        targets = sorted(set(t for _, t in exits if t is not None))
        for j, t in enumerate(targets, 1):
            L[p + '_exit' + ('' if len(targets) == 1 else str(j))] = t
        for j, (x, t) in enumerate(exits, 1):
            sfx = '' if len(exits) == 1 else str(j)
            o, a = op[x]
            if is_jcc(o):
                L[p + '_test' + sfx] = prev[x]
                if nxt[x] in inside:
                    L[p + '_next' + sfx] = nxt[x]
        latches = [blocks[b][-1] for b in body if h in succ[b]]
        if len(latches) == 1:
            L[p + '_back'] = latches[0]
    headers = set(h for h, _ in loops); j = 0
    npred = collections.Counter(t for b in blocks for t in succ[b])
    for b in sorted(blocks):
        if b != lo and b not in headers and npred[b] >= 2:
            j += 1; L['join%d' % j] = b
    rets = [x for x, o, _ in code if is_ret(o)]
    for k, x in enumerate(rets, 1):
        L['ret' if len(rets) == 1 else 'ret%d' % k] = x
    calls = [(x, callee_name(re.search(r'<([^>+]+)', a).group(1), target(a)))
             for x, o, a in code if is_call(o)]
    count = collections.Counter(c for _, c in calls)
    seen = collections.Counter()
    for x, c in calls:
        seen[c] += 1
        L['after_' + c + ('' if count[c] == 1 else '_%d' % seen[c])] = nxt[x]
    for k, x in enumerate(sorted(tables), 1):
        L['switch%d' % k] = x
        for i, t in enumerate(tables[x][2]):
            L['switch%d_case%d' % (k, i)] = t
    return collections.OrderedDict((n, v - lo) for n, v in L.items())

# ---------------------------------------------------------------------------
# The layout
# ---------------------------------------------------------------------------

class Layout:
    def __init__(self, path, objdump, nm, readelf):
        self.path = path
        data = open(path, 'rb').read()
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
        # The code of a function is found by its address, and is only the
        # instructions inside its size, not the padding after it
        self.code = {}; self.tables = {}
        for a, sz, t, n in fsyms:
            f = self.names[a, n]
            self.code[f] = [c for c in code[a][1] if c[0] < a + sz]
            tabs = {}
            for k, (x, o, args) in enumerate(self.code[f]):
                if is_jmp(o) and target(args) is None and \
                   re.match(r'\w+$', args.strip()):
                    tabs[x] = jump_table(self.code[f], k, data)
            self.tables[f] = tabs
        self.labels = {f: labels(self.code[f], self.functions[f][0],
                                 sum(self.functions[f]), self.tables[f],
                                 fname)
                       for f in self.functions}
        self.fname = fname
        # The tables with symbols, numbered by address if several have the
        # same name (e.g. static tables in the code for each parameter set)
        dsyms = sorted((a, sz, n) for a, sz, t, n in syms if t in 'rR')
        dcount = collections.Counter(n for _, _, n in dsyms)
        dseen = collections.Counter()
        self.data = collections.OrderedDict()
        for a, sz, n in dsyms:
            dseen[n] += 1
            nm_ = 'rodata_' + n.replace('.', '_')
            if dcount[n] > 1:
                nm_ += '_%d' % dseen[n]
            self.data[nm_] = (a, sz)
        self.plt = collections.OrderedDict(
            (m.group(1).lstrip('_'), a) for a, (s, _) in code.items()
            for m in [re.match(r'(.*)@plt$', s)] if m)
        self.got = collections.OrderedDict(
            (s.lstrip('_'), a) for s, a in
            sorted(got_slots(readelf, path).items(), key=lambda x: x[1]))
        # Data without symbols that the functions refer to RIP-relative:
        # vectors of constants that they load, of the size of the load,
        # and jump tables, of four bytes per entry
        named = [(a, a + sz) for a, sz in self.data.values()]
        self.consts = collections.OrderedDict()
        self.jtabs = collections.OrderedDict()
        for f in self.functions:
            used = {}
            for x, o, args in self.code[f]:
                v = rip_target(args)
                if v is None or not self.rodata[0] <= v < self.image_size:
                    continue
                if any(lo <= v < hi for lo, hi in named):
                    continue
                if any(v == tb for tb, _, _ in self.tables[f].values()):
                    continue
                w = rip_width(o, args)
                if w:
                    used[v] = max(used.get(v, 0), w)
            if used:
                self.consts[f] = sorted(used.items())
            for k, x in enumerate(sorted(self.tables[f]), 1):
                tb, n, _ = self.tables[f][x]
                self.jtabs['%s_switch%d_table' % (f, k)] = (tb, 4 * n)

    def objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.functions.items()]
        return sorted(rows, key=lambda r: r[1])

    def data_objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.data.items()]
        for f, vs in self.consts.items():
            rows.append((f + '_consts', vs[0][0],
                         vs[-1][0] + vs[-1][1] - vs[0][0]))
            if len(vs) > 1:
                for k, (v, w) in enumerate(vs, 1):
                    rows.append((f + '_const%d' % k, v, w))
        rows += [(n, a, sz) for n, (a, sz) in self.jtabs.items()]
        return sorted(rows, key=lambda r: (r[1], -r[2], r[0]))

    def check_names(self):
        names = collections.Counter(['libmldsa_size'])
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
            sys.exit('gen_layout.py: names defined twice: ' +
                     ' '.join(sorted(dup)))
        return len(names)

# ---------------------------------------------------------------------------
# Writing the HOL Light file
# ---------------------------------------------------------------------------

LABELS = '''\
Every value comes from the ELF file, read with nm, readelf and objdump:

  libmldsa.so
    |
    +-- symbol table ........ functions f and f_size,
    |                         tables rodata_<symbol>
    +-- section headers ..... libmldsa_size
    +-- dynamic relocations . got_g
    +-- disassembly ......... plt_g, f_consts and f_constK,
    |                         labels f_<label> inside the functions
    +-- read-only data ...... jump tables f_switchK_table

The image is the start of the binary, from address 0 up to the end of the
read-only data, which is the first two loadable segments and the start of
the third. The global offset table (GOT) is in another segment and is not
part of the image:

  0                                    libmldsa_size
  | ELF headers | .plt | .text | .rodata |  ...  |  .got  |
  +-------------- the image --------------+       got_g

Functions are named after their symbols, without a suffix such as
".constprop.0" that GCC adds to a specialized copy (unless that would
make two names the same), with any other dots replaced by underscores,
and numbered if several functions have the same name (e.g. static
functions of different source files). A function f has the names f for
its address and f_size for its size, and a label l inside it has the name
f_l for its address.

The labels come from the control flow graph of each function. Its code,
as objdump disassembles it, is cut into basic blocks, which start at the
entry of the function, at the target of each branch inside it, and after
each branch and return. There is an edge from a block to the target of
its last instruction if that is a branch inside the function, to each
target of an indirect jump through a jump table (see below), and to the
next block unless that instruction is an unconditional jump or a return.
A call is an ordinary instruction inside a block, and a jump out of the
function (a tail call) ends it like a return.

A block D dominates a block B if every path from the entry to B passes
through D. An edge B -> H to a block H that dominates B is a back edge,
and its natural loop is H, the header, with all the blocks that can reach
B without passing through H. Loops with the same header are one loop. For
example, with the entry E:

        E
        |
        v
   +--> H ----> X       H dominates A and B, so B -> H is a back
   |    |               edge, and the loop is H, A and B; the edge
   |    v               H -> X leaves the loop
   |    A
   |    |
   +--- B

Unlike counting the branches to lower addresses, this also finds the
loops that the compiler enters by a jump into their middle.

The loops of a function are numbered by the address of their headers,
and the labels of the K-th loop are named after its branches:

  loopK:       ...           <-------+     the header
               ...                   |
  loopK_test:  cmp   eax, 0xff       |     before a conditional branch
               ja    out  ------+    |     out of the loop
  loopK_next:  ...              |    |     back in the loop
  loopK_back:  jmp   loopK  ----|----+     the back edge
  loopK_exit:  ...       <------+          the target out of the loop

In a loop that is tested at the bottom, the back edge is also the branch
out of the loop, and the exit is the instruction after it:

  loopK:       ...           <-------+
               ...                   |
  loopK_test:  cmp   rax, 0x400      |
  loopK_back:  jne   loopK  ---------+
  loopK_exit:  ...

The test, next and exit labels are numbered (loopK_test1, loopK_test2,
...) if the loop has several branches or targets out of it, and
loopK_back is only defined if the loop has one back edge. The other
labels are these:

               je    joinK  ---+
               ...             |
  joinK:       ...      <------+   a block with two predecessors
               call  g
  after_g:     ...                 the return from a call of g
  switchK:     jmp   rax           an indirect jump through a table
  ret:         ret

joinK is the K-th start of a block, other than the entry and the loop
headers, that has more than one predecessor. after_g is numbered if g is
called several times, and ret if there are several returns.

The K-th indirect jump of a function, switchK, is through a jump table of
GCC's position-independent kind, which has one signed 32-bit offset per
case, from the start of the table, of the code for that case:

               cmp   r9d, 0xc            the cases are 0 to 12
               ja    <default>
               lea   rdx, [rip+table]    f_switchK_table
               movsxd rax, DWORD PTR [rdx+rax*4]
               add   rax, rdx
  switchK:     jmp   rax

The label switchK_caseN is the target of case N, so several cases can
have the same address, and the table is in the read-only data.

The read-only data are the tables with symbols, named after the symbol
with "rodata_" in front and any dots replaced by underscores (e.g.
rodata_mld_zetas, since mld_zetas is the HOL constant for its contents),
and numbered if several have the same name (such as a static table that
is compiled once for each parameter set), the jump tables, and the
vectors of constants without symbols that the functions load
RIP-relative: for a function f, f_consts is the block of all of them and,
if there are several, f_constK is the K-th one, of the size of the load.
The linker merges equal constants, so some have several names. For an
external symbol g, plt_g is its entry in the procedure linkage table, and
got_g its slot in the GOT, from the dynamic relocations:

  plt_g:       jmp   QWORD PTR [rip+got_g]    jumps to the address of g
               push  <index>                  that the dynamic loader
               jmp   <.plt>                   has put in got_g

At the end of this file, the code of each function is listed as objdump
disassembles it, with each instruction at its offset from the start of
the function, the labels at an instruction on the line before it, the
name of the address of a RIP-relative operand on the line after its
instruction, and the branches inside the function as arrows on the
right, from each branch to its target (marked with <). The operand of a
branch is the first label at its target, or its offset. Where there are
too many branches at once to draw them all, only the operand shows the
target. For example:

  loop1:
    +0x8   movdqa  xmm0, XMMWORD PTR [rdi+rax*1]    <+
    +0xd   paddd   xmm0, XMMWORD PTR [rsi+rax*1]     |
    +0x12  movaps  XMMWORD PTR [rdi+rax*1], xmm0     |
    +0x16  add     rax, 0x10                         |
  loop1_test:                                        |
    +0x1a  cmp     rax, 0x400                        |
  loop1_back:                                        |
    +0x20  jne     loop1                            -+'''

def box(text):
    # Paragraphs whose lines all start with two spaces are diagrams, kept
    # as they are; lists start with " - "; the rest is filled.
    out = []
    for para in text.split('\n\n'):
        lines = para.split('\n')
        if all(l.startswith('  ') for l in lines):
            for l in lines:
                assert len(l.rstrip()) <= 73 and '*)' not in l and \
                    '(*' not in l, l
                out.append(l.rstrip())
        elif para.startswith(' - '):
            for it in para[3:].split('\n - '):
                out += textwrap.wrap(' '.join(it.split()), 73,
                                     break_on_hyphens=False,
                                     initial_indent=' - ',
                                     subsequent_indent='   ')
        else:
            out += textwrap.wrap(' '.join(para.split()), 73,
                                 break_on_hyphens=False)
        out.append('')
    return '\n'.join('(* %-73s *)' % l for l in out[:-1])

def table(rows):
    w = max(len(r[0]) for r in rows) + 3
    return '\n'.join('  %-*s 0x%04x, 0x%03x%s' % (w, '"%s",' % n, a, sz,
                     ';' if i + 1 < len(rows) else '')
                     for i, (n, a, sz) in enumerate(rows))

def label_table(lay):
    out = []
    fs = [f for f, _ in sorted(lay.functions.items(), key=lambda x: x[1][0])
          if lay.labels[f]]
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
    intro = ('The layout of the binary %s of mldsa-native for x86-64 (see '
             'mldsa_native/README.md): names for the addresses in it, as '
             'offsets from the start of the image, and the sizes of its '
             'functions and data, for common/layout.ml. The proofs use '
             'these names, not the addresses themselves.\n\n'
             'This file is generated by mldsa_native/gen_layout.py from the '
             'binary with SHA-256 %s. Do not edit it by hand.\n\n'
             % (name, digest)) + LABELS
    out.write('(*\n * Copyright Amazon.com, Inc. or its affiliates. '
              'All Rights Reserved.\n'
              ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n'
              ' *)\n\n')
    out.write('(* %s *)\n%s\n(* %s *)\n\n' % ('=' * 73, box(intro), '=' * 73))
    out.write('needs "common/layout.ml";;\n\n')
    out.write('%s\n\ninstall_layout ["libmldsa_size",0x%x];;\n\n' %
              (rule('The size of the image.'), lay.image_size))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The functions, as (name, address, size).'),
               table(lay.objects())))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The read-only data, as (name, address, size).'),
               table(lay.data_objects())))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The entries of the procedure linkage table.'),
               table([('plt_' + s, a, 16) for s, a in
                      sorted(lay.plt.items(), key=lambda x: x[1])])))
    out.write('%s\n\ninstall_layout [\n%s];;\n\n' %
              (rule('The slots of the global offset table.'),
               ';\n'.join('  "got_%s",0x%x' % (s, a)
                          for s, a in lay.got.items())))
    out.write('%s\n\ninstall_layout (layout_labels [\n%s]);;\n' %
              (rule('The labels in the functions, as offsets from their '
                    'start.'), label_table(lay)))
    out.write('\n%s\n\n%s' %
              (rule('The code of the functions, with the labels and the '
                    'branches.'), listings(lay)))

# ---------------------------------------------------------------------------
# Listings of the code, with the labels and arrows for the branches
# ---------------------------------------------------------------------------

LABEL_ORDER = ['loop', 'join', 'exit', 'test', 'next', 'back', 'after',
               'switch', 'case', 'ret']

def label_key(l):
    m = re.match(r'(loop\d+|switch\d+)(_([a-z]+))?', l)
    kind = (m.group(3) or re.match(r'[a-z]+', m.group(1)).group(0)) if m \
        else re.match(r'[a-z]+', l).group(0)
    return (LABEL_ORDER.index(kind) if kind in LABEL_ORDER else 99, l)

def listing(lay, f):
    """The code of f as lines: a line "name:" for the labels at each
    instruction, and each instruction at its offset from the start, with
    the branches inside f drawn as arrows on the right."""
    a0, size = lay.functions[f]
    code = lay.code[f]
    at = collections.defaultdict(list)
    for l, o in lay.labels[f].items():
        at[o].append(l)
    for o in at:
        at[o].sort(key=label_key)
    data = {}
    for n, (a, sz) in lay.data.items():
        data.setdefault(a, n)
    for fn, vs in lay.consts.items():
        for k, (v, w) in enumerate(vs, 1):
            data.setdefault(v, fn + ('_consts' if len(vs) == 1
                                     else '_const%d' % k))
    for n, (a, sz) in lay.jtabs.items():
        data.setdefault(a, n)
    for g, a in lay.got.items():
        data.setdefault(a, 'got_' + g)
    rows = []                   # (text, offset of the instruction or None)
    for x, o, args in code:
        off = x - a0
        if at[off]:
            line = ''
            for l in at[off]:
                if line and len(line) + len(l) + 2 > 44:
                    rows.append((line, None)); line = ''
                line += (' ' if line else '') + l + ':'
            rows.append((line, None))
        t = target(args)
        note = ''
        v = rip_target(args)
        if v is not None:
            note = data.get(v, '')
            if not note:
                below = [(a, n) for a, n in data.items() if a < v]
                if below:
                    a, n = max(below)
                    note = '%s + 0x%x' % (n, v - a)
            args = re.sub(r'\s*#.*$', '', args)
        elif t is not None:
            if (is_branch(o) or is_call(o)) and a0 <= t < a0 + size:
                ls = at.get(t - a0)
                args = re.sub(r'[0-9a-f]+ <[^>]*>',
                              ls[0] if ls else '+0x%x' % (t - a0), args)
            else:
                m = re.search(r'<([^>+]+)(\+0x[0-9a-f]+)?>', args)
                callee = lay.fname(m.group(1), t) if m else '?'
                args = re.sub(r'[0-9a-f]+ <[^>]*>',
                              callee + (m.group(2) or ''), args)
        args = re.sub(r'\s*#.*$', '', args)
        args = re.sub(r',(?=\S)', ', ', args)
        rows.append(('%7s  %-7s %s' % ('+0x%x' % off, o, args), off))
        if note:
            rows.append((' ' * 17 + '// ' + note, None))
    # Arcs for the branches inside f, from the row of the branch to the row
    # of its target, each in a column, the shortest ones nearest the code
    row_of = {off: i for i, (_, off) in enumerate(rows) if off is not None}
    arcs = []
    for x, o, args in code:
        t = target(args)
        if is_branch(o) and t is not None and a0 <= t < a0 + size and \
           t - a0 in row_of:
            arcs.append((row_of[x - a0], row_of[t - a0]))
    width = max(len(t) for t, _ in rows) + 2
    ncols = max(0, min(12, (78 - width - 2) // 2))
    cols = [[] for _ in range(ncols)]
    placed = []
    for src, dst in sorted(arcs, key=lambda a: (abs(a[0] - a[1]), a)):
        lo, hi = min(src, dst), max(src, dst)
        for c in range(ncols):
            if all(hi < l or lo > h for l, h in cols[c]):
                cols[c].append((lo, hi))
                placed.append((src, dst, lo, hi, c)); break
    grid = [[' '] * (2 * ncols + 2) for _ in rows]
    for src, dst, lo, hi, c in placed:
        for r in range(lo + 1, hi):
            if grid[r][2 * c + 1] == ' ':
                grid[r][2 * c + 1] = '|'
    for src, dst, lo, hi, c in placed:
        for r in (src, dst):
            for k in range(2 * c + 1):
                if grid[r][k] not in '+<':
                    grid[r][k] = '-'
            grid[r][2 * c + 1] = '+'
        grid[dst][0] = '<'
    out = []
    for (t, _), g in zip(rows, grid):
        line = ('  ' + t.ljust(width) + ''.join(g)).rstrip() if placed \
            else ('  ' + t).rstrip()
        out.append(line)
    return out

def listings(lay):
    out = []
    for f, (a, sz) in sorted(lay.functions.items(), key=lambda x: x[1][0]):
        out.append('(*** %s: 0x%x, 0x%x bytes\n' % (f, a, sz))
        out += listing(lay, f)
        out.append(' ***)\n')
    return '\n'.join(out)

def main():
    ap = argparse.ArgumentParser(
        description='Generate the layout file of an x86-64 libmldsa.so')
    ap.add_argument('binary')
    ap.add_argument('--name', help='name of the binary in the header, '
                    'e.g. multilevel/gcc12/O2/libmldsa.so')
    ap.add_argument('--objdump', default=os.environ.get('OBJDUMP', 'objdump'))
    ap.add_argument('--nm', default=os.environ.get('NM', 'nm'))
    ap.add_argument('--readelf', default=os.environ.get('READELF',
                                                        'readelf'))
    args = ap.parse_args()
    lay = Layout(args.binary, args.objdump, args.nm, args.readelf)
    lay.check_names()
    write(lay, args.name or os.path.basename(args.binary), sys.stdout)

if __name__ == '__main__':
    main()
