#!/usr/bin/env python3
#
# Generate the transcription of the whole image of a libmldsa.so from
# mldsa-native, from address 0 to the end of .rodata, in the style of
# arm/mldsa_native/gcc12_O2/libmldsa.S.
#
# Usage: gen_libmldsa_s.py BINARY SYMBOL TITLE BINPATH INCLUDE_DIR > libmldsa.S
#
# For example, in s2n-bignum's arm directory:
#
#   python3 mldsa_native/gen_libmldsa_s.py \
#     <mldsa-native>/binaries/multilevel/gcc12/O3/libmldsa.so \
#     mldsa_native_libmldsa_gcc12_O3 "gcc 12, -O3" \
#     binaries/multilevel/gcc12/O3/libmldsa.so $PWD/../include \
#     > mldsa_native/gcc12_O3/libmldsa.S
#
#   SYMBOL   the symbol at the start, e.g. mldsa_native_libmldsa_clang17_O3
#   TITLE    e.g. "clang 17, -O3"
#   BINPATH  e.g. binaries/multilevel/clang17/O3/libmldsa.so
#   INCLUDE_DIR  s2n-bignum's include directory, for assembling the result
#
# Every instruction is first written as objdump shows it, with branch
# targets in the code replaced by labels, then the file is assembled and
# any instruction that does not assemble to the same word is written as
# .inst with the disassembly as a comment. ADRP and branches to addresses
# outside the code are always written as .inst.

import collections, os, re, struct, subprocess, sys, tempfile

def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True,
                          **kw).stdout

def sections(path):
    sec = collections.OrderedDict()
    for l in run(['readelf', '-SW', path]).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)'
                     r'\s+([0-9a-f]+)', l)
        if m:
            sec[m.group(1)] = (int(m.group(2), 16), int(m.group(4), 16))
    return sec

def segment0(data):
    phoff, = struct.unpack_from('<Q', data, 0x20)
    p_type, _, p_offset, p_vaddr, _, p_filesz = \
        struct.unpack_from('<IIQQQQ', data, phoff)
    assert p_type == 1 and p_offset == 0 and p_vaddr == 0
    return data[:p_filesz]

def disassemble(path):
    """[(address, word, mnemonic, operands)] and {address: symbol}"""
    ins = []; syms = {}; sect = None
    for l in run(['objdump', '-d', path]).splitlines():
        m = re.match(r'^Disassembly of section (\S+):', l)
        if m:
            sect = m.group(1); continue
        m = re.match(r'^([0-9a-f]+) <(.*)>:', l)
        if m:
            syms[int(m.group(1), 16)] = m.group(2); continue
        m = re.match(r'^\s+([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S+)\s*(.*)$', l)
        if m:
            ins.append((int(m.group(1), 16), int(m.group(2), 16),
                        m.group(3), m.group(4).strip()))
    return ins, syms

BRANCH = re.compile(r'^(b|bl|b\.\w+|cbz|cbnz|tbz|tbnz)$')
TARGET = re.compile(r'\b([0-9a-f]+) <[^>]*>')

def quads(data, lo, hi, out):
    assert lo % 8 == 0 and hi % 8 == 0
    for a in range(lo, hi, 8):
        out.append('        .quad   0x%016x' % struct.unpack_from('<Q', data, a))

def words(data, lo, hi, out):
    assert lo % 4 == 0 and hi % 4 == 0
    for a in range(lo, hi, 4):
        out.append('        .long   0x%08x' % struct.unpack_from('<I', data, a))

def generate(path, symbol, title, binpath, force_inst):
    data = open(path, 'rb').read()
    image = segment0(data)
    sec = sections(path)
    plt_lo = sec['.plt'][0]
    text_lo, text_sz = sec['.text']; text_hi = text_lo + text_sz
    ro_lo, ro_sz = sec['.rodata']; ro_hi = ro_lo + ro_sz
    assert sec['.plt'][0] + sec['.plt'][1] == text_lo
    ins, syms = disassemble(path)
    ins = [i for i in ins if plt_lo <= i[0] < text_hi]
    # Every word of the code is an instruction, in order
    assert [i[0] for i in ins] == list(range(plt_lo, text_hi, 4))
    for a, w, o, args in ins:
        assert struct.unpack_from('<I', image, a)[0] == w
    # Labels: branch targets in the code and the start of each function
    targets = set()
    for a, w, o, args in ins:
        if BRANCH.match(o):
            m = TARGET.search(args)
            if m:
                t = int(m.group(1), 16)
                if plt_lo <= t < text_hi:
                    targets.add(t)
    fsyms = {}
    for l in run(['nm', '-S', '--defined-only', path]).splitlines():
        p = l.split()
        if len(p) == 4 and p[2] in 'tT':
            fsyms.setdefault(int(p[0], 16), []).append((p[3], int(p[1], 16)))
    dsyms = {}
    for l in run(['nm', '-S', '--defined-only', path]).splitlines():
        p = l.split()
        if len(p) == 4 and p[2] in 'rR':
            dsyms[int(p[0], 16)] = (p[3], int(p[1], 16))
    labels = targets | set(a for a in fsyms if a >= text_lo)
    global OUTSIDE
    outside = [a for a, w, o, args in ins if BRANCH.match(o) and TARGET.search(args)
               and int(TARGET.search(args).group(1), 16) not in labels]
    OUTSIDE = ', as are the branches to addresses outside the code' if outside else ''
    lab = lambda t: 'L%04x' % t

    out = []
    out.append('// Copyright (c) The mldsa-native project authors')
    out.append('// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.')
    out.append('// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT')
    out.append('')
    out.append('// ' + '-' * 76)
    out.append("// The code and read-only data of mldsa-native's libmldsa.so (%s)" % title)
    out.append('//')
    hdr = ('This is a transcription of the binary %s from the binary branch of '
           'mldsa-native (see README.md), as loaded at an address that is a '
           'multiple of 4096: the start of its first segment, from address 0 up '
           'to the end of the read-only data. The ELF header and dynamic linking '
           'information at the start are given as data, as are the padding and '
           'the read-only data at the end, while the procedure linkage table and '
           'the code are given as instructions. The ADRP instructions, which '
           'compute addresses of pages relative to that of the instruction, are '
           'given as words%s. The labels are named after the addresses in the binary.' % (binpath, OUTSIDE))
    import textwrap
    for l in textwrap.wrap(hdr, 73, break_on_hyphens=False):
        out.append('// ' + l)
    out.append('// ' + '-' * 76)
    out.append('')
    out.append('#include "_internal_s2n_bignum_arm.h"')
    out.append('')
    out.append('        S2N_BN_SYM_VISIBILITY_DIRECTIVE(%s)' % symbol)
    out.append('        S2N_BN_SYM_PRIVACY_DIRECTIVE(%s)' % symbol)
    out.append('        .text')
    out.append('        .balign 4')
    out.append('')
    out.append('S2N_BN_SYMBOL(%s):' % symbol)
    out.append('')
    out.append('// ELF header and dynamic linking information (0x0 to 0x%x)' % plt_lo)
    out.append('')
    quads(image, 0, plt_lo, out)
    out.append('')
    out.append('// The procedure linkage table and the code (0x%x to 0x%x)' %
               (plt_lo, text_hi))
    out.append('// .plt')
    lines = {}            # address -> index in out of its instruction
    texts = {}            # address -> (assembler text, .inst text)
    for a, w, o, args in ins:
        if a >= text_lo and a in fsyms:
            for n, sz in fsyms[a]:
                out.append('')
                out.append('// %s (0x%x bytes)' % (n, sz))
        if a in labels:
            out.append(lab(a) + ':')
        args = args.split('//')[0].strip()
        dis = ('%-8s%s' % (o, args)).rstrip()
        if o == 'adrp':
            r, t = [x.strip() for x in args.split(',')]
            dis = 'adrp %s, 0x%x' % (r, int(t.split()[0], 16))
        inst = '        .inst   0x%08x  // %s' % (w, dis)
        asm = None
        if o != 'adrp' and o != 'adr' and a not in force_inst:
            m = TARGET.search(args)
            if m:
                t = int(m.group(1), 16)
                if BRANCH.match(o) and t in labels:
                    asm = '        ' + ('%-8s%s' % (o, TARGET.sub(lab(t), args))).rstrip()
            else:
                asm = '        ' + dis
        lines[a] = len(out)
        out.append(asm if asm is not None else inst)
        texts[a] = (asm, inst)
    out.append('')
    out.append('// Padding (0x%x to 0x%x)' % (text_hi, ro_lo))
    out.append('')
    if text_hi % 8 == 0 and ro_lo % 8 == 0:
        quads(image, text_hi, ro_lo, out)
    else:
        words(image, text_hi, ro_lo, out)
    out.append('')
    out.append('// The read-only data (0x%x to 0x%x)' % (ro_lo, ro_hi))
    out.append('')
    a = ro_lo
    for d in sorted(dsyms):
        n, sz = dsyms[d]
        quads(image, a, d, out)
        out.append('// %s (0x%x bytes)' % (n, sz))
        a = d
    quads(image, a, ro_hi, out)
    out.append('')
    out.append('#if defined(__linux__) && defined(__ELF__)')
    out.append('.section .note.GNU-stack, "", %progbits')
    out.append('#endif')
    return out, lines, texts, image[:ro_hi]

def assemble(lines, workdir):
    s = os.path.join(workdir, 'x.S'); o = os.path.join(workdir, 'x.o')
    open(s, 'w').write('\n'.join(lines) + '\n')
    cmd = ('cat %s | gcc -E -I%s -xassembler-with-cpp - | tr ";" "\\n" | '
           'as -march=armv8.2-a+sha3 -march=armv8-a+crypto -o %s -' %
           (s, INCLUDE, o))
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    # .text contents
    data = open(o, 'rb').read()
    shoff, = struct.unpack_from('<Q', data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from('<HHH', data, 0x3a)
    secs = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize)
            for i in range(shnum)]
    st = secs[shstrndx]
    for sh in secs:
        name = data[st[4] + sh[0]:data.index(b'\0', st[4] + sh[0])]
        if name == b'.text':
            return data[sh[4]:sh[4] + sh[5]], r.stderr
    return None, 'no .text'

INCLUDE = None
OUTSIDE = ''

def main():
    global INCLUDE
    path, symbol, title, binpath, INCLUDE = sys.argv[1:6]
    force = set()
    work = tempfile.mkdtemp(dir=os.environ.get('TMPDIR'))
    for it in range(5):
        out, lines, texts, image = generate(path, symbol, title, binpath, force)
        text, err = assemble(out, work)
        if text is None:
            sys.exit('assembly failed:\n' + err[:4000])
        if len(text) != len(image):
            sys.exit('size %d versus %d' % (len(text), len(image)))
        diffs = [a for a in lines if text[a:a+4] != image[a:a+4]]
        sys.stderr.write('iteration %d: %d differing instructions\n' % (it, len(diffs)))
        if not diffs:
            break
        for a in diffs:
            sys.stderr.write('  0x%x: %s\n' % (a, texts[a][1]))
        force |= set(diffs)
    assert text == image
    ninst = sum(1 for a in lines if out[lines[a]].lstrip().startswith('.inst'))
    sys.stderr.write('%d instructions as .inst\n' % ninst)
    sys.stdout.write('\n'.join(out) + '\n')

if __name__ == '__main__':
    main()
