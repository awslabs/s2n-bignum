#!/usr/bin/env python3

# The calls that the compiler has inlined into the functions of a
# libmlkem.so from mlkem-native, from its split debug information, for
# gen_layout.py --dwarf (see mlkem_native/README.md).
#
# Usage: dwarf_inline.py BINARY [DWP]     (DWP defaults to BINARY.dwp)
#
# prints, for each function with code, the tree of the calls of mlkem-native
# functions inlined into it, with their address ranges.
#
# The binaries are built with -gdwarf-4 -gsplit-dwarf, so the debug
# information is in two parts:
#
#   BINARY      the skeleton: the line table, .debug_addr (the addresses
#               that DIEs refer to by index, DW_FORM_GNU_addr_index) and
#               .debug_ranges (the address ranges of DIEs with DW_AT_ranges,
#               relative to the low_pc of the skeleton compile unit)
#   BINARY.dwp  the tree of DIEs: functions, inlined calls, their names
#
# llvm-symbolizer --dwp attributes the instructions of such binaries to the
# wrong inlined calls (e.g. code of mlk_poly_compress_d5_c in
# mlkem1024_indcpa_enc to "mlkem512_keypair_derand"), although the line
# numbers it gives are right. So this script reads the DIE tree with
# llvm-dwarfdump and resolves its addresses and ranges from the skeleton
# itself. The result is checked against the symbol table: the low_pc of
# every function with code must be that of a symbol of the same name.

import collections, re, subprocess, sys

def run(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout

def skeleton(dwarfdump, binary):
    info = run(dwarfdump, '--debug-info', binary)
    base = int(re.search(r'DW_AT_low_pc\s+\((0x[0-9a-f]+)\)', info).group(1), 16)
    addr = [int(x, 16) for x in re.findall(r'^0x[0-9a-f]+$',
                                           run(dwarfdump, '--debug-addr', binary), re.M)]
    ranges = collections.defaultdict(list)
    for l in run(dwarfdump, '--debug-ranges', binary).splitlines():
        m = re.match(r'([0-9a-f]{8}) ([0-9a-f]{16}) ([0-9a-f]{16})$', l)
        if m:
            lo, hi = int(m.group(2), 16), int(m.group(3), 16)
            if lo < hi:
                ranges[int(m.group(1), 16)].append((base + lo, base + hi))
    return addr, ranges

class Die:
    def __init__(self, off, tag):
        self.off, self.tag = off, tag
        self.attrs = {}; self.children = []

def die_tree(dwarfdump, dwp):
    root = None; stack = []; cur = None
    # llvm-dwarfdump reports the ranges it cannot resolve without the skeleton
    out = subprocess.run([dwarfdump, '--debug-info', dwp], capture_output=True, text=True).stdout
    for l in out.splitlines():
        m = re.match(r'(0x[0-9a-f]{8}):( +)(DW_TAG_\w+|NULL)', l)
        if m:
            depth = (len(m.group(2)) - 1) // 2
            stack = stack[:depth]
            if m.group(3) == 'NULL':
                cur = None; continue
            d = Die(int(m.group(1), 16), m.group(3))
            if stack:
                stack[-1].children.append(d)
            else:
                root = d
            stack.append(d); cur = d; continue
        m = re.match(r'\s+(DW_AT_\w+)\t\((.*)\)$', l)
        if m and cur is not None:
            cur.attrs[m.group(1)] = m.group(2)
    return root

def walk(d):
    yield d
    for c in d.children:
        yield from walk(c)

def inline_tree(binary, dwp=None, dwarfdump='llvm-dwarfdump'):
    """[(function, [(lo, hi)], [(chain, [(lo, hi)])])] for every function
    with code: its name, its address ranges, and the calls inlined into it,
    each with the chain of names of the inlined functions from the outermost
    to the callee itself, and the address ranges of its code."""
    addr, ranges = skeleton(dwarfdump, binary)
    root = die_tree(dwarfdump, dwp or binary + '.dwp')
    by_off = {d.off: d for d in walk(root)}
    def name(d):
        if 'DW_AT_name' in d.attrs:
            return d.attrs['DW_AT_name'].strip('"')
        o = d.attrs.get('DW_AT_abstract_origin') or d.attrs.get('DW_AT_specification')
        return name(by_off[int(o.split()[0], 16)]) if o else None
    def extent(d):
        if 'DW_AT_ranges' in d.attrs:
            return ranges[int(d.attrs['DW_AT_ranges'], 16)]
        lo = d.attrs.get('DW_AT_low_pc')
        if lo is None:
            return []
        m = re.match(r'indexed \(([0-9a-f]+)\)', lo)
        a = addr[int(m.group(1), 16)] if m else int(lo, 16)
        n = int(d.attrs.get('DW_AT_high_pc', '0x0'), 16)
        return [(a, a + n)] if n else []
    out = []
    for d in walk(root):
        if d.tag == 'DW_TAG_subprogram' and extent(d):
            calls = []
            def visit(x, chain):
                for c in x.children:
                    if c.tag == 'DW_TAG_inlined_subroutine':
                        calls.append((chain + [name(c)], extent(c)))
                        visit(c, chain + [name(c)])
                    else:
                        visit(c, chain)
            visit(d, [])
            out.append((name(d), extent(d), calls))
    return out

def main():
    binary = sys.argv[1]
    dwp = sys.argv[2] if len(sys.argv) > 2 else None
    for f, ext, calls in sorted(inline_tree(binary, dwp), key=lambda x: x[1][0][0]):
        print('%s 0x%x-0x%x' % (f, ext[0][0], ext[-1][1]))
        for chain, rs in calls:
            if chain[-1].startswith('mlkem') and rs:
                print('  %s%s  %s' % ('  ' * (len(chain) - 1), chain[-1],
                                      ' '.join('0x%x-0x%x' % r for r in rs)))

if __name__ == '__main__':
    main()
