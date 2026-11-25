#!/usr/bin/env python3

# Generate the layout file of an ELF shared object, the HOL Light file that
# gives names to the addresses and sizes in the binary for
# common/layout.ml: the functions and the labels inside them, the data,
# the entries of the PLT and the slots of the GOT, the vtables, and the
# extent of the image and of the writable segment.
#
# Usage: elf_layout.py [options] BINARY > LAYOUT.ml
#
#   --lib LIB          the prefix of the names of the image, e.g. libsnappy
#                      for libsnappy_size (default: the file name without
#                      its extension)
#   --name NAME        the build, for the header, e.g. "gcc 12 -O2"
#   --project TEXT     what the binary is, for the header, e.g.
#                      "snappy 1.3.1 (see arm/snappy/README.md)"
#   --generator TEXT   how the file was made, for the header (default: the
#                      command line)
#   --strip-namespace NS  namespaces to drop from C++ names (repeatable)
#   --c-prefix PFX     a prefix for the names of the functions with C (not
#                      mangled) names, e.g. c_, so that they cannot be the
#                      same as the HOL constants of a specification
#   --image-end SECTION   the last section of the image (default .rodata)
#   --isa ISA          the instruction set of the binary (aarch64)
#   --objdump, --nm, --readelf, --cxxfilt   the tools (default objdump, nm,
#                      readelf and c++filt, or the variables OBJDUMP, NM,
#                      READELF and CXXFILT; on a host that is not AArch64
#                      use those of a cross toolchain)
#
# For example, in s2n-bignum's arm directory:
#
#   python3 ../tools/elf_layout.py --lib libsnappy --name "gcc 12 -O2" \
#     --project "snappy 1.3.1 (see snappy/README.md)" \
#     --strip-namespace snappy::internal --strip-namespace snappy \
#     --c-prefix c_ <snappy-build>/gcc12_O2/libsnappy.so \
#     > proofs/snappy/gcc12_O2/layout.ml
#
# Everything comes from the ELF file: the symbol table, the section and
# program headers, the dynamic relocations and the disassembly of the code
# (by objdump), from which the labels inside the functions are found by an
# analysis of the control flow. No debug information is needed. The names
# of C++ symbols are made by elf_names.py, whose header explains them.
#
# This generalizes arm/mlkem_native/gen_layout.py of the mlkem-native
# proofs: it adds the names of C++ symbols, the vtables, the GOT slots of
# every relocation in the GOT, the writable segment, and labels after the
# indirect calls, and leaves out the labels for inlined calls (--dwarf).

import argparse, collections, hashlib, os, re, shlex, subprocess, sys, textwrap

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import elf_names

BRANCH = re.compile(r'^(b|b\.\w+|cbz|cbnz|tbz|tbnz)$')
CLONE = elf_names.CLONE

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
    """The defined symbols with a size, as (address, size, type, name)."""
    out = []
    for l in run([nm, '-S', '--defined-only', path]).splitlines():
        p = l.split()
        if len(p) == 4:
            out.append((int(p[0], 16), int(p[1], 16), p[2], p[3]))
    return out

def sections(readelf, path):
    """name -> (address, size, flags)"""
    sec = collections.OrderedDict()
    for l in run([readelf, '-SW', path]).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)'
                     r'\s+[0-9a-f]+\s+([A-Za-z]*)\s', l)
        if m:
            sec[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16), m.group(4))
    return sec

def segments(readelf, path):
    """The program headers, as (type, vaddr, filesz, memsz, flags)."""
    out = []
    for l in run([readelf, '-lW', path]).splitlines():
        m = re.match(r'\s+(\S+)\s+0x[0-9a-f]+\s+0x([0-9a-f]+)\s+0x[0-9a-f]+\s+'
                     r'0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+([RWE ]+?)\s+0x', l)
        if m:
            out.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16),
                        int(m.group(4), 16), m.group(5).replace(' ', '')))
    return out

RELOC_TYPES = {
    183: {1027: 'R_AARCH64_RELATIVE', 1025: 'R_AARCH64_GLOB_DAT',
          1026: 'R_AARCH64_JUMP_SLOT', 257: 'R_AARCH64_ABS64',
          1032: 'R_AARCH64_IRELATIVE', 1024: 'R_AARCH64_COPY'},
    62: {8: 'R_X86_64_RELATIVE', 6: 'R_X86_64_GLOB_DAT', 7: 'R_X86_64_JUMP_SLOT',
         1: 'R_X86_64_64', 37: 'R_X86_64_IRELATIVE', 5: 'R_X86_64_COPY'}}

def dynamic_relocations(readelf, path):
    """The dynamic relocations (those of the SHT_RELA sections whose symbols
    are in the dynamic symbol table), as (offset, type, symbol or None,
    addend), read from the ELF file itself."""
    import struct
    data = open(path, 'rb').read()
    if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 1:
        sys.exit(path + ': not a 64-bit little-endian ELF file')
    machine, = struct.unpack_from('<H', data, 0x12)
    shoff, = struct.unpack_from('<Q', data, 0x28)
    shentsize, shnum = struct.unpack_from('<HH', data, 0x3a)
    secs = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize)
            for i in range(shnum)]
    out = []
    for sh in secs:
        if sh[1] != 4 or secs[sh[6]][1] != 11:     # SHT_RELA with SHT_DYNSYM
            continue
        symtab = secs[sh[6]]; strtab = secs[symtab[6]]
        for off in range(sh[4], sh[4] + sh[5], 24):
            r_offset, r_info, r_addend = struct.unpack_from('<QQq', data, off)
            typ, isym = r_info & 0xffffffff, r_info >> 32
            name = RELOC_TYPES.get(machine, {}).get(typ, 'R_%d_%d' % (machine, typ))
            sym = None
            if isym:
                st_name, = struct.unpack_from('<I', data, symtab[4] + 24 * isym)
                a = strtab[4] + st_name
                sym = data[a:data.index(b'\0', a)].decode()
            out.append((r_offset, name, sym, r_addend))
    return out

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
             for x, o, a in code if o == 'bl' and re.search(r'<([^>+]+)', a)]
    count = collections.Counter(c for _, c in calls); seen = collections.Counter()
    for x, c in calls:
        seen[c] += 1
        L['after_' + c + ('' if count[c] == 1 else '_%d' % seen[c])] = x + 4
    blrs = [x for x, o, _ in code if o == 'blr']
    for k, x in enumerate(blrs, 1):
        L['after_blr' if len(blrs) == 1 else 'after_blr%d' % k] = x + 4
    for k, x in enumerate([x for x, o, _ in code if o == 'adrp'], 1):
        L['adrp%d' % k] = x
    return collections.OrderedDict((n, v - lo) for n, v in L.items())

# ---------------------------------------------------------------------------
# The layout
# ---------------------------------------------------------------------------

ISAS = {'aarch64': {'jump_slot': 'R_AARCH64_JUMP_SLOT', 'glob_dat': 'R_AARCH64_GLOB_DAT',
                    'abs64': 'R_AARCH64_ABS64', 'relative': 'R_AARCH64_RELATIVE'}}

class Layout:
    def __init__(self, path, args):
        self.path = path; self.lib = args.lib
        if args.isa not in ISAS:
            sys.exit('elf_layout.py: the instruction set %s is not supported '
                     '(the labels need its branches)' % args.isa)
        rk = ISAS[args.isa]
        code = disassemble(args.objdump, path)
        syms = symbols(args.nm, path)
        sec = sections(args.readelf, path)
        segs = segments(args.readelf, path)
        relocs = dynamic_relocations(args.readelf, path)
        if args.image_end not in sec:
            sys.exit('elf_layout.py: no section ' + args.image_end)
        self.image_size = sec[args.image_end][0] + sec[args.image_end][1]
        load = [s for s in segs if s[0] == 'LOAD']
        if not load or load[0][1] != 0 or self.image_size > load[0][2]:
            sys.exit('elf_layout.py: the image is not at the start of the first segment')
        rw = [s for s in load if 'W' in s[4]]
        self.rw = (rw[0][1], rw[0][3]) if rw else None
        relro = [s for s in segs if s[0] == 'GNU_RELRO']
        self.relro = (relro[0][1], relro[0][2]) if relro else None
        self.rodata = sec.get('.rodata', (self.image_size, 0, ''))[:2]
        code_secs = [(a, a + sz) for n, (a, sz, fl) in sec.items()
                     if 'X' in fl and a + sz <= self.image_size]
        # The executable sections and .rodata of the image, by name
        self.sections = [(elf_names.c_name(n.lstrip('.')), a, sz) for n, (a, sz, fl) in sec.items()
                         if sz > 0 and a + sz <= self.image_size and
                         ('X' in fl or n == '.rodata')]
        in_code = lambda a: any(lo <= a < hi for lo, hi in code_secs)
        fsyms = sorted(s for s in syms if s[2] in 'tTwW' and s[1] > 0 and in_code(s[0]))
        names = elf_names.hol_names([(a, n) for a, sz, t, n in fsyms],
                                    args.strip_namespace, args.c_prefix, args.cxxfilt)
        dem = elf_names.demangle_all(sorted(set(CLONE.sub('', n) for _, _, _, n in fsyms)),
                                     args.cxxfilt)
        # One entry per name; the first name of an address (by the address,
        # then the name) is the one under which its code is listed
        self.functions = collections.OrderedDict(); self.aliases = {}
        self.demangled = {}; primary = {}
        for a, sz, t, n in sorted(fsyms, key=lambda s: (s[0], names[s[0], s[3]])):
            hn = names[a, n]
            if hn in self.functions:
                if self.functions[hn] != (a, sz):
                    sys.exit('elf_layout.py: two functions named ' + hn)
                continue
            self.functions[hn] = (a, sz)
            d = dem.get(CLONE.sub('', n), n)
            m = CLONE.search(n)
            self.demangled[hn] = d + (' [clone %s]' % m.group(1) if m else '')
            if a in primary:
                self.aliases.setdefault(primary[a], []).append(hn)
            else:
                primary[a] = hn
        by_addr = {a: hn for hn, (a, sz) in self.functions.items() if primary[a] == hn}
        sym_names = collections.defaultdict(set)
        for a, sz, t, n in fsyms:
            sym_names[n].add(a)
        self.imports = {}                   # import symbol -> HOL name
        imp_syms = sorted(set([m.group(1) for _, (s, _) in code.items()
                               for m in [re.match(r'(.*)@plt$', s)] if m] +
                              [s for _, _, s, _ in relocs if s]))
        imp_names = elf_names.hol_names([(0, s) for s in imp_syms],
                                        args.strip_namespace, '', args.cxxfilt)
        # Imports are distinct symbols, so equal names are numbered
        cnt = collections.Counter(imp_names.values()); seen = collections.Counter()
        for s in imp_syms:
            v = imp_names[0, s]
            if cnt[v] > 1:
                seen[v] += 1; v = '%s_%d' % (v, seen[v])
            self.imports[s] = v
        def fname(sym, addr=None):
            """The name of a symbol, or of the callee of a call to it."""
            if sym.endswith('@plt'):
                return self.imports.get(sym[:-4], elf_names.c_name(sym[:-4]))
            if addr is not None and addr in by_addr:
                return by_addr[addr]
            if len(sym_names[sym]) == 1:
                return by_addr.get(next(iter(sym_names[sym])), elf_names.c_name(sym))
            return elf_names.c_name(sym)
        self.fname = fname
        # objdump shows the code under only one of several symbols at the
        # same address, so the code of a function is found by its address
        self.labels = {}; self.code = {}
        for hn, (a, sz) in self.functions.items():
            self.labels[hn] = collections.OrderedDict()
            if by_addr.get(a) == hn:
                self.code[hn] = code[a][1]
                self.labels[hn] = labels(code[a][1], fname)
        # Data in the image and in the writable segment
        dsyms = [s for s in syms if s[2] in 'rRdDbBvVgGsS' and s[1] > 0]
        dnames = elf_names.hol_names([(a, n) for a, sz, t, n in dsyms],
                                     args.strip_namespace, '', args.cxxfilt)
        self.data = collections.OrderedDict()
        self.rwdata = collections.OrderedDict(); self.vtables = collections.OrderedDict()
        for a, sz, t, n in sorted(dsyms):
            hn = dnames[a, n]
            if a + sz <= self.image_size:
                self.data['rodata_' + hn] = (a, sz)
            else:
                nm_ = hn if hn.startswith('zt') else 'data_' + hn
                self.rwdata[nm_] = (a, sz)
                if hn.startswith('ztv_'):
                    self.vtables['vtable_' + hn[4:]] = a + 16
        objs = dict((a, n) for n, (a, sz) in list(self.rwdata.items()) + list(self.data.items()))
        objs.update(by_addr)
        # The PLT: each entry loads its GOT slot with ADRP and LDR
        self.plt = collections.OrderedDict(); plt_slot = {}
        for a, (s, ins) in code.items():
            m = re.match(r'(.*)@plt$', s)
            if not m:
                continue
            page = None; slot = None
            for x, o, ar in ins[:4]:
                mm = re.match(r'x16, ([0-9a-f]+) <', ar)
                if o == 'adrp' and mm:
                    page = int(mm.group(1), 16)
                mm = re.match(r'x17, \[x16, #(\d+)\]', ar)
                if o == 'ldr' and mm and page is not None:
                    slot = page + int(mm.group(1))
            self.plt[self.imports[m.group(1)]] = a
            plt_slot[m.group(1)] = slot
        # The GOT: every relocated slot in it
        gotsec = [sec[n][:2] for n in ('.got', '.got.plt') if n in sec]
        in_got = lambda a: any(lo <= a < lo + sz for lo, sz in gotsec)
        self.got = collections.OrderedDict(); self.got_kind = {}
        for off, typ, sym, add in sorted(relocs, key=lambda r: (r[1] != rk['jump_slot'], r[0])):
            if not in_got(off):
                continue
            if typ == rk['jump_slot'] and plt_slot.get(sym) not in (None, off):
                sys.exit('elf_layout.py: the PLT entry of %s does not read its slot' % sym)
            if sym is not None:
                n = self.imports[sym] + ('' if add == 0 else '_plus_%x' % add)
            elif typ == rk['relative']:
                n = objs.get(add, 'rel_%x' % add)
            else:
                n = '%s_%x' % (typ.lower(), off)
            if n in self.got:
                n += '_globdat' if typ == rk['glob_dat'] else '_%x' % off
            self.got[n] = off; self.got_kind[n] = typ
        self.got = collections.OrderedDict(sorted(self.got.items(), key=lambda x: x[1]))
        # Vectors of constants without symbols, loaded with ADRP and LDR
        # (of a Q, D or S register) by each function
        named = [(a, a + sz) for a, sz in self.data.values()]
        self.consts = collections.OrderedDict()
        width = {'q': 16, 'd': 8, 's': 4}
        for hn, ins in self.code.items():
            page = {}; used = {}
            for x, o, ar in ins:
                m = re.match(r'(x\d+), ([0-9a-f]+) <', ar)
                if o == 'adrp' and m:
                    page[m.group(1)] = int(m.group(2), 16); continue
                m = re.match(r'([qds])\d+, \[(x\d+), #(\d+)\]', ar)
                if o == 'ldr' and m and m.group(2) in page:
                    v = page[m.group(2)] + int(m.group(3))
                    if self.rodata[0] <= v < self.image_size and \
                       not any(lo <= v < hi for lo, hi in named):
                        used[v] = max(used.get(v, 0), width[m.group(1)])
            if used:
                self.consts[hn] = sorted(used.items())

    def objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.functions.items()]
        return sorted(rows, key=lambda r: (r[1], r[0]))

    def data_objects(self):
        rows = [(n, a, sz) for n, (a, sz) in self.data.items()]
        for f, vs in self.consts.items():
            rows.append((f + '_consts', vs[0][0], vs[-1][0] + vs[-1][1] - vs[0][0]))
            if len(vs) > 1:
                for k, (v, w) in enumerate(vs, 1):
                    rows.append((f + '_const%d' % k, v, w))
        return sorted(rows, key=lambda r: (r[1], -r[2], r[0]))

    def rw_objects(self):
        return sorted([(n, a, sz) for n, (a, sz) in self.rwdata.items()],
                      key=lambda r: (r[1], r[0]))

    def segment_names(self):
        out = [(self.lib + '_size', self.image_size)]
        for n, a, sz in self.sections:
            out += [(self.lib + '_' + n, a), (self.lib + '_' + n + '_size', sz)]
        if self.rw:
            out += [(self.lib + '_rw', self.rw[0]), (self.lib + '_rw_size', self.rw[1])]
        if self.relro:
            out += [(self.lib + '_relro', self.relro[0]),
                    (self.lib + '_relro_size', self.relro[1])]
        return out

    def check_names(self):
        names = collections.Counter(n for n, _ in self.segment_names())
        for n, a, sz in self.objects() + self.data_objects() + self.rw_objects():
            names[n] += 1; names[n + '_size'] += 1
        for n in self.vtables:
            names[n] += 1
        for f, ls in self.labels.items():
            for l in ls:
                names[f + '_' + l] += 1
        for s in self.plt:
            names['plt_' + s] += 1; names['plt_' + s + '_size'] += 1
        for s in self.got:
            names['got_' + s] += 1
        dup = [n for n, c in names.items() if c > 1]
        if dup:
            sys.exit('elf_layout.py: names defined twice: ' + ' '.join(sorted(dup)))
        bad = [n for n in names if not re.match(r'^[A-Za-z][A-Za-z0-9_]*$', n)]
        if bad:
            sys.exit('elf_layout.py: not identifiers: ' + ' '.join(sorted(bad)))
        return len(names)

def box(text):
    # Paragraphs whose lines all start with two spaces are diagrams, kept
    # as they are; lists start with " - "; the rest is filled.
    out = []
    for para in text.split('\n\n'):
        lines = para.split('\n')
        if all(l.startswith('  ') for l in lines):
            for l in lines:
                assert len(l.rstrip()) <= 73 and '*)' not in l and '(*' not in l, l
                out.append(l.rstrip())
        elif para.startswith(' - '):
            for it in para[3:].split('\n - '):
                out += textwrap.wrap(' '.join(it.split()), 73,
                                     break_on_hyphens=False,
                                     initial_indent=' - ', subsequent_indent='   ')
        else:
            out += textwrap.wrap(' '.join(para.split()), 73,
                                 break_on_hyphens=False)
        out.append('')
    return '\n'.join('(* %-73s *)' % l for l in out[:-1])

def table(rows):
    w = min(max(len(r[0]) for r in rows), 40) + 3
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

# ---------------------------------------------------------------------------
# Writing the HOL Light file
# ---------------------------------------------------------------------------

LABELS = '''\
Every value comes from the ELF file, read with nm, readelf and objdump:

  LIB.so
    |
    +-- symbol table ........ functions f and f_size, data rodata_<d>,
    |                         objects in the writable segment, vtable_<C>
    +-- headers ............. LIB_size,
    |                         LIB_<sec> and LIB_<sec>_size,
    |                         LIB_rw and LIB_rw_size,
    |                         LIB_relro and LIB_relro_size
    +-- dynamic relocations . got_<g>
    +-- disassembly ......... plt_<g>, f_consts and f_constK,
                              labels f_<label> inside the functions

The image is the start of the first loadable segment of the binary, up to
the end of the read-only data, LIB_size. Its executable sections and the
read-only data are at LIB_<sec>, of LIB_<sec>_size bytes, for <sec> the
name of the section without the dot, e.g. LIB_text. The second, writable,
segment,
from LIB_rw (LIB_rw_size bytes as loaded), holds the data that the
dynamic loader relocates: the vtables, the global offset table (GOT) and
the writable data, of which the part from LIB_relro (LIB_relro_size
bytes) is made read-only after the relocation. Both are loaded at the
same base, so these are all offsets from it:

  0                                  LIB_size
  | ELF headers | .plt | .text | .rodata |
  +------------ the image ---------------+

  LIB_rw
  | vtables | .got | .data |
  +--- writable segment ---+

The names of the functions and data come from their symbols, made into
identifiers as described in tools/elf_names.py: a C function keeps its
name (with the --c-prefix, if any), and a C++ function is named after
its demangled name, without its namespace, its parameters and return
type, unless it has overloads, whose names end in "__" and the types of
their parameters. Symbols at the same address that get the same name
(e.g. the complete and base-object constructors) are one function, and
the listing of each function gives its C++ name. A function f has the
names f for its address and f_size for its size, and a label l inside it
has the name f_l for its address.

The labels come from the control flow graph of each function. Its code,
as objdump disassembles it, is cut into basic blocks, which start at the
entry of the function, at the target of each branch inside it, and after
each branch and return. There is an edge from a block to the target of
its last instruction if that is a branch inside the function, and to the
next block unless that instruction is an unconditional branch or a
return. A call (BL or BLR) is an ordinary instruction inside a block,
and a branch out of the function (a tail call) ends it like a return.

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
  loopK_test:  cmp   w6, #0xff       |     before a conditional branch
               b.hi  out  ------+    |     out of the loop
  loopK_next:  ...              |    |     back in the loop
  loopK_back:  b     loopK  ----|----+     the back edge
  loopK_exit:  ...       <------+          the target out of the loop

In a loop that is tested at the bottom, the back edge is also the branch
out of the loop, and the exit is the instruction after it:

  loopK:       ...           <-------+
               ...                   |
  loopK_test:  cmp   x3, #0x20       |
  loopK_back:  b.ne  loopK  ---------+
  loopK_exit:  ...

The test, next and exit labels are numbered (loopK_test1, loopK_test2,
...) if the loop has several branches or targets out of it, and
loopK_back is only defined if the loop has one back edge. The other
labels are these:

               cbz   x0, joinK  ---+
               ...                 |
  joinK:       ...      <----------+   a block with two predecessors
               bl    g
  after_g:     ...                     the return from a call of g
               blr   x2
  after_blrK:  ...                     the return from an indirect call
  adrpK:       adrp  x0, <page>
               ldr   q0, [x0, #16]     loads the vector f_constK
  ret:         ret

joinK is the K-th start of a block, other than the entry and the loop
headers, that has more than one predecessor. after_g is numbered if g is
called several times, after_blr if there are several indirect calls, and
ret if there are several returns. adrpK is the K-th ADRP instruction.
ADRP computes the 4096-byte page of its target relative to its own page,
so the address that it computes with the LDR or ADD after it is the same
wherever the image is loaded, as long as that is at a multiple of 4096.

The read-only data are the objects with symbols in the image, named
after the symbol with "rodata_" in front, and the vectors of constants
without symbols that the functions load with ADRP and LDR of a Q, D or S
register: for a function f, f_consts is the block of all of them and, if
there are several, f_constK is the K-th one.

The objects with symbols in the writable segment are named after the
symbol, with "data_" in front unless they are made by the compiler for a
class (ztv_C for the vtable of class C, see tools/elf_names.py). For a
vtable ztv_C, vtable_C is ztv_C + 16, the address that the vptr of an
object of class C holds: the first virtual function is at vtable_C, the
next at vtable_C + 8, and so on.

For an imported symbol g, plt_g is its entry in the procedure linkage
table, which loads the address of g from its slot got_g in the GOT and
jumps there:

  plt_g:       adrp  x16, <page>        loads the address of g from
               ldr   x17, [x16, #off]   its slot got_g in the GOT and
               add   x16, x16, #off     jumps there
               br    x17

Every slot of the GOT that the dynamic loader relocates has a name:
got_g for an imported symbol g (with "_globdat" appended for a second
slot of the same symbol), and for a slot that holds an address in the
binary (a RELATIVE relocation), got_ and the name of what is at that
address, e.g. got_ztv_C for the vtable of C, which the code loads and
adds 16 to. What the slots hold once loaded is given by the list of
relocations, in the file generated by tools/elf_relocs.py.

At the end of this file, the code of each function is listed as objdump
disassembles it, with each instruction at its offset from the start of
the function, the labels at an instruction on the line before it, the
name of the address that an ADRP with an LDR or ADD computes on the line
after the LDR or ADD, and the branches inside the function as arrows on
the right, from each branch to its target (marked with <). The operand of
a branch is the first label at its target, or its offset. Where there
are too many branches at once to draw them all, only the operand shows
the target. For example:

  loop2:
    +0x20  lsl     w0, w8, w1            <+
    +0x24  ldrb    w2, [x5, x3]           |
           ...                            |
  loop2_test:                             |
    +0x44  cmp     w1, #0x8               |
  loop2_back:                             |
    +0x48  b.ne    loop2                 -+'''

def write(lay, args, out):
    digest = hashlib.sha256(open(lay.path, 'rb').read()).hexdigest()
    gen = args.generator or 'tools/elf_layout.py ' + ' '.join(
        shlex.quote(a) for a in sys.argv[1:-1]) + ' BINARY'
    intro = ('The layout of the binary %s%s%s: names for the addresses in it, as '
             'offsets from the base at which it is loaded, and the sizes of its '
             'functions and data, for common/layout.ml. The proofs use these names, '
             'not the addresses themselves.\n\n'
             'This file is generated by %s from the binary with SHA-256 %s. Do not '
             'edit it by hand.\n\n' % (
                 os.path.basename(lay.path),
                 ' of ' + args.project if args.project else '',
                 ', ' + args.name if args.name else '', gen, digest)) + \
            LABELS.replace('LIB', lay.lib)
    out.write('(*\n * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.\n'
              ' * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n *)\n\n')
    out.write('(* %s *)\n%s\n(* %s *)\n\n' % ('=' * 73, box(intro), '=' * 73))
    out.write('needs "common/layout.ml";;\n\n')
    out.write('%s\n\ninstall_layout [\n%s];;\n\n' %
              (rule('The image, its sections and the writable segment.'),
               ';\n'.join('  "%s",0x%x' % nv for nv in lay.segment_names())))
    out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
              (rule('The functions, as (name, address, size).'), table(lay.objects())))
    if lay.data_objects():
        out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
                  (rule('The read-only data, as (name, address, size).'),
                   table(lay.data_objects())))
    if lay.rw_objects():
        out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
                  (rule('The objects in the writable segment, as (name, address, size).'),
                   table(lay.rw_objects())))
    if lay.vtables:
        out.write('%s\n\ninstall_layout [\n%s];;\n\n' %
                  (rule('The vtables, as the addresses that the vptrs hold.'),
                   ';\n'.join('  "%s",0x%x' % (n, a) for n, a in lay.vtables.items())))
    if lay.plt:
        out.write('%s\n\ninstall_layout (layout_objects [\n%s]);;\n\n' %
                  (rule('The entries of the procedure linkage table.'),
                   table([('plt_' + s, a, 16) for s, a in
                          sorted(lay.plt.items(), key=lambda x: x[1])])))
    if lay.got:
        w = max(len(s) for s in lay.got) + 8
        out.write('%s\n\ninstall_layout [\n%s];;\n\n' %
                  (rule('The relocated slots of the global offset table.'),
                   ';\n'.join('  %-*s 0x%x' % (w, '"got_%s",' % s, a)
                              for s, a in lay.got.items())))
    out.write('%s\n\ninstall_layout (layout_labels [\n%s]);;\n' %
              (rule('The labels in the functions, as offsets from their start.'),
               label_table(lay)))
    out.write('\n%s\n\n%s' %
              (rule('The code of the functions, with the labels and the branches.'),
               listings(lay)))

# ---------------------------------------------------------------------------
# Listings of the code, with the labels and arrows for the branches
# ---------------------------------------------------------------------------

LABEL_ORDER = ['loop', 'join', 'exit', 'test', 'next', 'back', 'after', 'adrp', 'ret']

def label_key(l):
    m = re.match(r'(loop\d+)(_([a-z]+))?', l)
    kind = (m.group(3) or 'loop') if m else re.match(r'[a-z]+', l).group(0)
    return (LABEL_ORDER.index(kind) if kind in LABEL_ORDER else 99, l)

def listing(lay, f):
    """The code of f as lines: a line "name:" for the labels at each
    instruction, and each instruction at its offset from the start, with
    the branches inside f drawn as arrows on the right."""
    a0, size = lay.functions[f]
    code = [c for c in lay.code[f] if c[0] < a0 + size]    # not the padding
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
            data.setdefault(v, fn + ('_consts' if len(vs) == 1 else '_const%d' % k))
    for g, a in lay.got.items():
        data.setdefault(a, 'got_' + g)
    for n, (a, sz) in lay.rwdata.items():
        data.setdefault(a, n)
    rows = []                   # (text, offset of the instruction or None)
    page = {}
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
        if o == 'adrp':
            m = re.match(r'(x\d+), ([0-9a-f]+) <', args)
            if m:
                page[m.group(1)] = int(m.group(2), 16)
            args = re.sub(r'[0-9a-f]+ <[^>]*>', '<page>', args)
        else:
            m = re.match(r'(?:[xwqdsbh]\d+), \[(x\d+)(?:, #(\d+))?\]', args) if o.startswith('ld') or o.startswith('st') else \
                re.match(r'(?:x\d+), (x\d+), #0x([0-9a-f]+)$', args) if o == 'add' else None
            if m and m.group(1) in page:
                v = page[m.group(1)] + (int(m.group(2), 16) if o == 'add' else int(m.group(2) or 0))
                if v in data:
                    note = '  // ' + data[v]
            if t is not None:
                if a0 <= t < a0 + 4 * len(code) and (BRANCH.match(o)):
                    ls = at.get(t - a0)
                    args = re.sub(r'[0-9a-f]+ <[^>]*>', ls[0] if ls else '+0x%x' % (t - a0), args)
                else:
                    m = re.search(r'<([^>+]+)(\+0x[0-9a-f]+)?>', args)
                    callee = lay.fname(m.group(1), t) if m else '?'
                    args = re.sub(r'[0-9a-f]+ <[^>]*>', callee + (m.group(2) or ''), args)
            args = re.sub(r'\s*//.*$', '', args)
            # drop objdump's own comments, e.g. the decimal value of an immediate
        if o in ('b', 'bl') or BRANCH.match(o) or o == 'adrp':
            args = re.sub(r'\s*//.*$', '', args)
        rows.append(('%7s  %-7s %s' % ('+0x%x' % off, o, args), off))
        if note:
            rows.append((' ' * 17 + note.strip(), None))
    # Arcs for the branches inside f, from the row of the branch to the row
    # of its target, each in a column, the shortest ones nearest the code
    row_of = {off: i for i, (_, off) in enumerate(rows) if off is not None}
    arcs = []
    for x, o, args in code:
        t = target(args)
        if BRANCH.match(o) and t is not None and a0 <= t < a0 + 4 * len(code) and t - a0 in row_of:
            arcs.append((row_of[x - a0], row_of[t - a0]))
    width = max(len(t) for t, _ in rows) + 2
    ncols = max(0, min(12, (78 - width - 2) // 2))
    cols = [[] for _ in range(ncols)]
    placed = []
    for src, dst in sorted(arcs, key=lambda a: (abs(a[0] - a[1]), a)):
        lo, hi = min(src, dst), max(src, dst)
        for c in range(ncols):
            if all(hi < l or lo > h for l, h in cols[c]):
                cols[c].append((lo, hi)); placed.append((src, dst, lo, hi, c)); break
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
        line = ('  ' + t.ljust(width) + ''.join(g)).rstrip() if placed else '  ' + t
        out.append(line)
    return out

def listings(lay):
    out = []
    for f, (a, sz) in sorted(lay.functions.items(), key=lambda x: x[1][0]):
        if f not in lay.code:
            continue                        # another name of a function
        out.append('(*** %s: 0x%x, 0x%x bytes' % (f, a, sz))
        # Inside an OCaml comment, "(*" and "*)" would nest or end it (as
        # in the C++ type void (*)(void*)) and a double quote would start a
        # string, so they are spaced out or replaced
        body = ['     %s' % lay.demangled[f]] + \
               ['     also %s' % g for g in lay.aliases.get(f, [])] + [''] + \
               listing(lay, f)
        out += [l.replace('(*', '( *').replace('*)', '* )').replace('"', "'")
                for l in body]
        out.append(' ***)\n')
    return '\n'.join(out)

def main():
    ap = argparse.ArgumentParser(description='Generate the layout file of an ELF shared object')
    ap.add_argument('binary')
    ap.add_argument('--lib')
    ap.add_argument('--name', help='the build, e.g. "gcc 12 -O2"')
    ap.add_argument('--project', help='what the binary is, e.g. "snappy 1.3.1"')
    ap.add_argument('--generator', help='how the file was made, for the header')
    ap.add_argument('--strip-namespace', action='append', default=[])
    ap.add_argument('--c-prefix', default='')
    ap.add_argument('--image-end', default='.rodata')
    ap.add_argument('--isa', default='aarch64')
    ap.add_argument('--objdump', default=os.environ.get('OBJDUMP', 'objdump'))
    ap.add_argument('--nm', default=os.environ.get('NM', 'nm'))
    ap.add_argument('--readelf', default=os.environ.get('READELF', 'readelf'))
    ap.add_argument('--cxxfilt', default=os.environ.get('CXXFILT', 'c++filt'))
    args = ap.parse_args()
    if args.lib is None:
        args.lib = re.sub(r'\..*$', '', os.path.basename(args.binary))
    lay = Layout(args.binary, args)
    lay.check_names()
    write(lay, args, sys.stdout)

if __name__ == '__main__':
    main()
