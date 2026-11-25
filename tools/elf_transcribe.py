#!/usr/bin/env python3
#
# Generate the transcription of the whole image of an AArch64 ELF shared
# object, from address 0 to the end of a section (by default .rodata), as an
# assembler file that assembles to exactly the bytes of the binary there.
#
# Usage: elf_transcribe.py [options] BINARY SYMBOL INCLUDE_DIR > IMAGE.S
#
#   SYMBOL       the symbol at the start, e.g. snappy_libsnappy_gcc12_O2
#   INCLUDE_DIR  s2n-bignum's include directory, for assembling the result
#   --title TEXT     what the image is, e.g. "snappy 1.3.1, gcc 12 -O2"
#   --source TEXT    where the binary comes from, for the header, e.g.
#                    "libsnappy.so built by arm/snappy/build.sh"
#   --copyright TEXT a copyright line for the header (repeatable; the
#                    Amazon line is always added after these)
#   --license TEXT   the SPDX license expression (default: Apache-2.0 OR
#                    ISC OR MIT-0)
#   --image-end SECTION   the last section of the image (default .rodata)
#   --isa ISA        the instruction set (only aarch64)
#   --objdump, --nm, --readelf, --cc, --as   the tools
#
# For example, in s2n-bignum's arm directory:
#
#   python3 ../tools/elf_transcribe.py \
#     --title "snappy 1.3.1, gcc 12 -O2" \
#     --source "libsnappy.so built by snappy/build.sh" \
#     --copyright "Copyright 2011 Google Inc. All Rights Reserved." \
#     --license "BSD-3-Clause AND (Apache-2.0 OR ISC OR MIT-0)" \
#     <snappy-build>/gcc12_O2/libsnappy.so snappy_libsnappy_gcc12_O2 \
#     $PWD/../include > snappy/gcc12_O2/libsnappy.S
#
# The image is the start of the first loadable segment. The executable
# sections in it (.init, .plt, .text, .fini, ...) are written as
# instructions, as objdump shows them, with the targets of the branches
# into them as labels named after their addresses (L<hex>); everything else
# (the ELF header, the dynamic linking information, the padding and the
# read-only data) is written as data, in .quad, .long or .byte directives.
# The file is assembled, and every instruction that does not assemble to
# the same word is written as .inst with the disassembly as a comment, as
# are always ADR, ADRP, the branches to addresses outside the code and the
# words that objdump does not decode. The script fails unless the
# assembled text is identical to the image. It generalizes
# arm/mlkem_native/gen_libmlkem_s.py of the mlkem-native proofs.

import argparse, collections, os, re, struct, subprocess, sys, tempfile, textwrap

def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True,
                          **kw).stdout

def sections(readelf, path):
    """name -> (address, size, flags), in the order of the headers"""
    sec = collections.OrderedDict()
    for l in run([readelf, '-SW', path]).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)'
                     r'\s+[0-9a-f]+\s+([A-Za-z]*)\s', l)
        if m:
            sec[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16), m.group(4))
    return sec

def segment0(data):
    phoff, = struct.unpack_from('<Q', data, 0x20)
    p_type, _, p_offset, p_vaddr, _, p_filesz = \
        struct.unpack_from('<IIQQQQ', data, phoff)
    assert p_type == 1 and p_offset == 0 and p_vaddr == 0
    return data[:p_filesz]

def disassemble(objdump, path):
    """[(address, word, mnemonic, operands)] of the executable sections"""
    ins = []
    for l in run([objdump, '-d', path]).splitlines():
        m = re.match(r'^\s+([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S+)\s*(.*)$', l)
        if m:
            ins.append((int(m.group(1), 16), int(m.group(2), 16),
                        m.group(3), m.group(4).strip()))
    return ins

BRANCH = re.compile(r'^(b|bl|b\.\w+|cbz|cbnz|tbz|tbnz)$')
TARGET = re.compile(r'\b([0-9a-f]+) <[^>]*>')

def data_lines(image, lo, hi, out):
    """The bytes [lo,hi) as .quad where 8-aligned, else .long or .byte."""
    a = lo
    while a < hi:
        if a % 8 == 0 and a + 8 <= hi:
            out.append('        .quad   0x%016x' % struct.unpack_from('<Q', image, a)); a += 8
        elif a % 4 == 0 and a + 4 <= hi:
            out.append('        .long   0x%08x' % struct.unpack_from('<I', image, a)); a += 4
        else:
            out.append('        .byte   0x%02x' % image[a]); a += 1

def generate(args, force_inst):
    path = args.binary
    data = open(path, 'rb').read()
    image = segment0(data)
    sec = sections(args.readelf, path)
    if args.image_end not in sec:
        sys.exit('elf_transcribe.py: no section ' + args.image_end)
    end = sec[args.image_end][0] + sec[args.image_end][1]
    if end > len(image):
        sys.exit('elf_transcribe.py: %s is not in the first segment' % args.image_end)
    code = [(n, a, a + sz) for n, (a, sz, fl) in sec.items()
            if 'X' in fl and sz > 0 and a + sz <= end]
    code.sort(key=lambda c: c[1])
    in_code = lambda t: any(lo <= t < hi for _, lo, hi in code)
    ins = [i for i in disassemble(args.objdump, path) if in_code(i[0])]
    # Every word of the code is an instruction, in order
    want = [a for _, lo, hi in code for a in range(lo, hi, 4)]
    if [i[0] for i in ins] != want:
        sys.exit('elf_transcribe.py: objdump does not show every word of the code')
    for a, w, o, ar in ins:
        assert struct.unpack_from('<I', image, a)[0] == w
    # Labels: branch targets in the code and the start of each function
    targets = set()
    for a, w, o, ar in ins:
        if BRANCH.match(o):
            m = TARGET.search(ar)
            if m and in_code(int(m.group(1), 16)):
                targets.add(int(m.group(1), 16))
    fsyms = collections.defaultdict(list); dsyms = collections.defaultdict(list)
    for l in run([args.nm, '-S', '--defined-only', path]).splitlines():
        p = l.split()
        if len(p) == 4 and p[2] in 'tTwW':
            fsyms[int(p[0], 16)].append((p[3], int(p[1], 16)))
        elif len(p) == 4 and p[2] in 'rR':
            dsyms[int(p[0], 16)].append((p[3], int(p[1], 16)))
    labels = targets | set(a for a in fsyms if in_code(a))
    lab = lambda t: 'L%04x' % t
    outside = [a for a, w, o, ar in ins if BRANCH.match(o) and TARGET.search(ar)
               and int(TARGET.search(ar).group(1), 16) not in labels]

    out = []
    for c in args.copyright:
        out.append('// ' + c)
    out.append('// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.')
    out.append('// SPDX-License-Identifier: ' + args.license)
    out.append('')
    out.append('// ' + '-' * 76)
    out.append('// The image of %s' % (args.title or os.path.basename(path)))
    out.append('//')
    hdr = ('This is a transcription of %s, as loaded at an address that is a '
           'multiple of 4096: the start of its first segment, from address 0 up '
           'to the end of %s (0x%x). It is generated by tools/elf_transcribe.py. '
           'The ELF header and dynamic linking information at the start are given '
           'as data, as are the padding and the read-only data, while the '
           'executable sections (%s) are given as instructions. The ADR and ADRP '
           'instructions, which compute addresses relative to that of the '
           'instruction, are given as words%s, with the disassembly as a comment. '
           'The labels are named after the addresses in the binary.' %
           (args.source or os.path.basename(path), args.image_end, end,
            ', '.join(n for n, _, _ in code),
            ', as are the branches to addresses outside the code' if outside else ''))
    for l in textwrap.wrap(hdr, 73, break_on_hyphens=False):
        out.append('// ' + l)
    out.append('// ' + '-' * 76)
    out.append('')
    out.append('#include "_internal_s2n_bignum_arm.h"')
    out.append('')
    out.append('        S2N_BN_SYM_VISIBILITY_DIRECTIVE(%s)' % args.symbol)
    out.append('        S2N_BN_SYM_PRIVACY_DIRECTIVE(%s)' % args.symbol)
    out.append('        .text')
    out.append('        .balign 4')
    out.append('')
    out.append('S2N_BN_SYMBOL(%s):' % args.symbol)
    lines = {}            # address -> index in out of its instruction
    texts = {}            # address -> (assembler text, .inst text)
    pos = 0
    by_addr = {a: (a, w, o, ar) for a, w, o, ar in ins}
    def data_part(lo, hi, what):
        if lo >= hi:
            return
        out.append('')
        out.append('// %s (0x%x to 0x%x)' % (what, lo, hi))
        out.append('')
        a = lo
        for d in sorted(x for x in dsyms if lo <= x < hi):
            data_lines(image, a, d, out)
            for n, sz in dsyms[d]:
                out.append('// %s (0x%x bytes)' % (n, sz))
            a = d
        data_lines(image, a, hi, out)
    for k, (n, lo, hi) in enumerate(code):
        data_part(pos, lo, 'ELF header and dynamic linking information' if pos == 0
                  else 'Data and padding')
        out.append('')
        out.append('// %s (0x%x to 0x%x)' % (n, lo, hi))
        for a in range(lo, hi, 4):
            _, w, o, ar = by_addr[a]
            if a in fsyms:
                for fn, sz in fsyms[a]:
                    out.append('')
                    out.append('// %s (0x%x bytes)' % (fn, sz))
            if a in labels:
                out.append(lab(a) + ':')
            ar = ar.split('//')[0].strip()
            dis = ('%-8s%s' % (o, ar)).rstrip()
            if o in ('adrp', 'adr'):
                r, t = [x.strip() for x in ar.split(',', 1)]
                dis = '%s %s, 0x%x' % (o, r, int(t.split()[0], 16))
            inst = '        .inst   0x%08x  // %s' % (w, dis)
            asm = None
            if o not in ('adrp', 'adr') and not o.startswith('.') and \
               o != 'udf' and a not in force_inst:
                m = TARGET.search(ar)
                if m:
                    t = int(m.group(1), 16)
                    if BRANCH.match(o) and t in labels:
                        asm = '        ' + ('%-8s%s' % (o, TARGET.sub(lab(t), ar))).rstrip()
                else:
                    asm = '        ' + dis
            lines[a] = len(out)
            out.append(asm if asm is not None else inst)
            texts[a] = (asm, inst)
        pos = hi
    data_part(pos, end, 'Data and padding, then the read-only data')
    out.append('')
    out.append('#if defined(__linux__) && defined(__ELF__)')
    out.append('.section .note.GNU-stack, "", %progbits')
    out.append('#endif')
    return out, lines, texts, image[:end]

def assemble(args, lines, workdir):
    s = os.path.join(workdir, 'x.S'); o = os.path.join(workdir, 'x.o')
    open(s, 'w').write('\n'.join(lines) + '\n')
    cmd = ('cat %s | %s -E -I%s -xassembler-with-cpp - | tr ";" "\\n" | '
           '%s -march=armv8.2-a+sha3 -march=armv8-a+crypto -o %s -' %
           (s, args.cc, args.include, args.asm, o))
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
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

def main():
    ap = argparse.ArgumentParser(description='Transcribe the image of an ELF shared object')
    ap.add_argument('binary'); ap.add_argument('symbol'); ap.add_argument('include')
    ap.add_argument('--title'); ap.add_argument('--source')
    ap.add_argument('--copyright', action='append', default=[])
    ap.add_argument('--license', default='Apache-2.0 OR ISC OR MIT-0')
    ap.add_argument('--image-end', default='.rodata')
    ap.add_argument('--isa', default='aarch64')
    ap.add_argument('--objdump', default=os.environ.get('OBJDUMP', 'objdump'))
    ap.add_argument('--nm', default=os.environ.get('NM', 'nm'))
    ap.add_argument('--readelf', default=os.environ.get('READELF', 'readelf'))
    ap.add_argument('--cc', default=os.environ.get('CC', 'gcc'))
    ap.add_argument('--as', dest='asm', default=os.environ.get('AS', 'as'))
    args = ap.parse_args()
    if args.isa != 'aarch64':
        sys.exit('elf_transcribe.py: only aarch64 is supported')
    force = set()
    work = tempfile.mkdtemp(dir=os.environ.get('TMPDIR'))
    for it in range(5):
        out, lines, texts, image = generate(args, force)
        text, err = assemble(args, out, work)
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
    if text != image:
        sys.exit('elf_transcribe.py: the assembled text is not the image')
    ninst = sum(1 for a in lines if out[lines[a]].lstrip().startswith('.inst'))
    sys.stderr.write('%d instructions as .inst\n' % ninst)
    sys.stdout.write('\n'.join(out) + '\n')

if __name__ == '__main__':
    main()
