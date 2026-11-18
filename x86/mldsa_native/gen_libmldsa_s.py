#!/usr/bin/env python3
#
# Generate the transcription of the whole image of an x86-64 libmldsa.so
# from mldsa-native, from address 0 to the end of .rodata, in the style of
# x86/mldsa_native/gcc12_O2/libmldsa.S.
#
# Usage: gen_libmldsa_s.py BINARY SYMBOL TITLE BINPATH INCLUDE_DIR > libmldsa.S
#
# For example, in s2n-bignum's x86 directory:
#
#   python3 mldsa_native/gen_libmldsa_s.py \
#     <build>/multilevel/gcc12/O2/libmldsa.so \
#     mldsa_native_libmldsa_gcc12_O2 "gcc 12, -O2" \
#     multilevel/gcc12/O2/libmldsa.so $PWD/../include \
#     > mldsa_native/gcc12_O2/libmldsa.S
#
#   SYMBOL   the symbol at the start, e.g. mldsa_native_libmldsa_gcc12_O2
#   TITLE    e.g. "gcc 12, -O2"
#   BINPATH  e.g. multilevel/gcc12/O2/libmldsa.so
#   INCLUDE_DIR  s2n-bignum's include directory, for assembling the result
#
# Every instruction is first written as objdump shows it in Intel syntax,
# with the targets of branches and calls inside the image and the
# RIP-relative references to code or read-only data in it replaced by
# labels L<address>. The file is then assembled as the Makefile does, and
# any instruction that does not assemble to the same bytes is tried with
# the pseudo-prefixes {disp8}, {disp32}, {load} and {store} in turn, and
# otherwise written as .byte with the disassembly as a comment. The NOPs
# and the instructions that refer to addresses outside the image, i.e. to
# the global offset table, are always written as .byte. This is an adapted
# version of the generator used for the x86-64 code of mlkem-native.

import os, re, subprocess, sys, tempfile

def run(cmd):
    return subprocess.run(cmd, check=True, capture_output=True,
                          text=True).stdout

def main():
    path, symbol, title, binpath, include = sys.argv[1:6]
    data = open(path, 'rb').read()

    secs = {}
    for m in re.finditer(r'\]\s+(\S+)\s+\S+\s+([0-9a-f]{16})\s+([0-9a-f]+)'
                         r'\s+([0-9a-f]+)', run(['readelf', '-SW', path])):
        secs[m.group(1)] = tuple(int(m.group(i), 16) for i in (2, 3, 4))
    for s in ('.plt', '.text', '.rodata'):
        va, off, sz = secs[s]
        assert va == off, 'address and offset differ for ' + s
    plt_start, _, plt_size = secs['.plt']
    text_start, _, text_size = secs['.text']
    ro_start, _, ro_size = secs['.rodata']
    end = ro_start + ro_size
    code_end = text_start + text_size
    assert plt_start + plt_size == text_start

    funcs = {}
    for m in re.finditer(r'^([0-9a-f]+) ([0-9a-f]+) [tT] (\S+)$',
                         run(['nm', '-S', path]), re.M):
        funcs[int(m.group(1), 16)] = m.group(3)
    dsyms = {}
    for m in re.finditer(r'^([0-9a-f]+) ([0-9a-f]+) [rR] (\S+)$',
                         run(['nm', '-S', path]), re.M):
        a = int(m.group(1), 16)
        if ro_start <= a < end:
            dsyms[a] = (m.group(3), int(m.group(2), 16))

    dis = run(['objdump', '-d', '-M', 'intel', '-w',
               '--start-address=%d' % plt_start,
               '--stop-address=%d' % code_end, path])
    insns = []
    for line in dis.split('\n'):
        mm = re.match(r'^\s*([0-9a-f]+):\t([0-9a-f ]+?)\s*\t(.*)$', line)
        if mm:
            a = int(mm.group(1), 16)
            raw = bytes(int(x, 16) for x in mm.group(2).split())
            insns.append([a, raw, mm.group(3).strip()])
    pos = plt_start
    for a, raw, asm in insns:
        assert a == pos, 'gap in the disassembly at 0x%x' % pos
        pos += len(raw)
    assert pos == code_end, 'disassembly ends at 0x%x' % pos
    assert all(data[a:a + len(r)] == r for a, r, _ in insns)

    def lab(a):
        return 'L%x' % a

    code_targets, data_targets = set(), set()
    texts = []
    for a, raw, asm in insns:
        nasm = re.sub(r'\s+#.*$', '', asm) if 'rip' not in asm else asm
        if (nasm.startswith('nop') or nasm.startswith('data16') or
                nasm.startswith('cs nop') or nasm == 'xchg   ax,ax'):
            texts.append(None)
            continue
        mb = re.match(r'^(j[a-z]+|call|jmp)\s+([0-9a-f]+) <.*>$', nasm)
        if mb:
            t = int(mb.group(2), 16)
            if plt_start <= t < code_end:
                code_targets.add(t)
                texts.append('%s %s' % (mb.group(1), lab(t)))
            else:
                texts.append(None)
            continue
        mr = re.search(r'\[rip\+0x([0-9a-f]+)\]\s+#\s+([0-9a-f]+)', nasm)
        if mr:
            t = int(mr.group(2), 16)
            if ro_start <= t < end:
                data_targets.add(t)
            elif plt_start <= t < code_end:
                code_targets.add(t)
            else:
                texts.append(None)
                continue
            nasm = re.sub(r'\[rip\+0x[0-9a-f]+\]\s+#.*$',
                          '[rip+%s]' % lab(t), nasm)
        elif 'rip' in nasm:
            texts.append(None)
            continue
        texts.append(re.sub(r'\s+', ' ', nasm))

    def fmt(txt):
        parts = txt.split(' ', 1)
        if len(parts) == 1:
            return txt
        mn, ops = parts
        if mn in ('rep', 'repz', 'repnz', 'lock'):
            mn2, _, ops = ops.partition(' ')
            mn = mn + ' ' + mn2
        ops = re.sub(r',(?=\S)', ', ', ops.strip())
        return '%-7s %s' % (mn, ops)

    def data_lines(lo, hi, labels, names={}):
        res, a = [], lo
        while a < hi:
            if a in names:
                res.append('// %s (0x%x bytes)' % names[a])
            if a in labels:
                res.append('%s:' % lab(a))
            nxt = min([t for t in labels | set(names) if t > a] + [hi])
            if all(b == 0 for b in data[a:nxt]) and nxt - a >= 16:
                res.append('        .zero   %d' % (nxt - a))
                a = nxt
                continue
            if a % 8 == 0 and a + 8 <= nxt:
                res.append('        .quad   0x%016x' %
                           int.from_bytes(data[a:a + 8], 'little'))
                a += 8
            else:
                res.append('        .byte   0x%02x' % data[a])
                a += 1
        return res

    def render(choices):
        body = ['// ELF header and dynamic linking information, and padding',
                '// (0x0 to 0x%x)' % plt_start, '']
        body += data_lines(0, plt_start, set())
        body += ['', '// The procedure linkage table (0x%x to 0x%x)' %
                 (plt_start, text_start), '']
        for (a, raw, asm), txt, ch in zip(insns, texts, choices):
            if a == text_start:
                body += ['', '// The code (0x%x to 0x%x)' %
                         (text_start, code_end)]
            if a in funcs and a >= text_start:
                body += ['', '// %s (0x%x)' % (funcs[a], a), '']
            if a in code_targets or a in funcs:
                body.append('%s:' % lab(a))
            if txt is None or ch == 'byte':
                c = re.sub(r'\s+', ' ', re.sub(r'\s+#.*$', '', asm))
                c = re.sub(r'\s+<[^>]*>$', '', c)
                body.append('        // ' + fmt(c))
                body.append('        .byte   ' +
                            ','.join('0x%02x' % b for b in raw))
            else:
                body.append('        ' + (ch + ' ' if ch else '') + fmt(txt))
        body += ['', '// Padding (0x%x to 0x%x)' % (code_end, ro_start), '']
        body += data_lines(code_end, ro_start, set())
        body += ['', '// The read-only data (0x%x to 0x%x)' % (ro_start, end),
                 '']
        body += data_lines(ro_start, end, data_targets, dsyms)
        return body

    def full(body):
        hdr = [
            '// Copyright (c) The mldsa-native project authors',
            '// Copyright Amazon.com, Inc. or its affiliates. '
            'All Rights Reserved.',
            '// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT', '',
            '// ' + '-' * 76,
            "// The code and read-only data of mldsa-native's libmldsa.so "
            '(%s)' % title,
            '//']
        text = (
            'This is a transcription of the binary %s for x86-64 (see '
            'README.md), as loaded at an address that is a multiple of '
            '4096: its bytes from address 0 up to the end of the read-only '
            'data, which are its first two loadable segments and the start '
            'of the third, with the padding between them. The ELF header '
            'and dynamic linking information at the start, the padding and '
            'the read-only data are given as data, while the procedure '
            'linkage table and the code are given as instructions. The '
            'instructions that refer to the global offset table, which is '
            'outside the image, are given as bytes, as are the NOPs and '
            'any instruction that the assembler would encode differently. '
            'The labels are named after the addresses in the binary.'
            % binpath)
        words, line = text.split(), '//'
        for w in words:
            if len(line) + 1 + len(w) > 79:
                hdr.append(line)
                line = '//'
            line += ' ' + w
        hdr.append(line)
        hdr += ['// ' + '-' * 76, '',
                '#include "_internal_s2n_bignum_x86.h"', '',
                '        .intel_syntax noprefix',
                '        S2N_BN_SYM_VISIBILITY_DIRECTIVE(%s)' % symbol,
                '        S2N_BN_SYM_PRIVACY_DIRECTIVE(%s)' % symbol,
                '        .text',
                '        .balign 16', '',
                'S2N_BN_SYMBOL(%s):' % symbol, '']
        return hdr + body + [
            '', '#if defined(__linux__) && defined(__ELF__)',
            '.section .note.GNU-stack, "", %progbits', '#endif']

    def assemble(lines):
        with tempfile.TemporaryDirectory() as d:
            sp, op = os.path.join(d, 'x.S'), os.path.join(d, 'x.o')
            open(sp, 'w').write('\n'.join(lines) + '\n')
            cmd = ("cat %s | sed -e 's/\\/\\/.*//' | gcc -E -I%s "
                   "-DWINDOWS_ABI=0 -xassembler-with-cpp - | tr ';' '\\n' | "
                   "as -o %s -" % (sp, include, op))
            r = subprocess.run(cmd, shell=True, capture_output=True,
                               text=True)
            if r.returncode:
                return None, r.stderr
            rel = run(['objdump', '-r', op])
            if 'R_X86_64' in rel:
                sys.exit('relocations in the image:\n' + rel[:2000])
            subprocess.run(['objcopy', '-O', 'binary', '--only-section=.text',
                            op, os.path.join(d, 'x.bin')], check=True)
            return open(os.path.join(d, 'x.bin'), 'rb').read(), ''

    choices = [''] * len(insns)
    order = ['', '{disp8}', '{disp32}', '{load}', '{store}', 'byte']
    for attempt in range(8 * len(insns) + 8):
        lines = full(render(choices))
        code, err = assemble(lines)
        if code is None:
            bad = set(int(x) for x in re.findall(r':(\d+): Error', err))
            fixed = False
            for k, (a, raw, asm) in enumerate(insns):
                if texts[k] is not None and choices[k] != 'byte':
                    line = '        ' + \
                        (choices[k] + ' ' if choices[k] else '') + \
                        fmt(texts[k])
                    for b in bad:
                        if 0 < b <= len(lines) and lines[b - 1] == line:
                            choices[k] = 'byte'
                            fixed = True
            if not fixed:
                sys.exit(err[:3000])
            continue
        if code == data[:end]:
            break
        for k, (a, raw, asm) in enumerate(insns):
            if code[a:a + len(raw)] != raw:
                if choices[k] == 'byte':
                    sys.exit('mismatch in a .byte instruction at 0x%x' % a)
                choices[k] = order[order.index(choices[k]) + 1]
                break
        else:
            sys.exit('data mismatch')
    else:
        sys.exit('could not match the bytes')

    for l in lines:
        if len(l) > 79:
            sys.stderr.write('long line: %s\n' % l)
    sys.stdout.write('\n'.join(lines) + '\n')
    sys.stderr.write(
        '%d instructions, %d as bytes, %d with pseudo-prefixes\n' %
        (len(insns),
         sum(1 for t, c in zip(texts, choices) if t is None or c == 'byte'),
         sum(1 for c in choices if c not in ('', 'byte'))))

if __name__ == '__main__':
    main()
