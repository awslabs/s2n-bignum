#!/usr/bin/env python3

# Check that a function in an assembled transcription (an ELF object file)
# has exactly the same code as a function in a binary (e.g. one of the
# libmlkem.so files in mlkem-native's binary branch).
#
# Usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL
#                               [DATA_SYMBOL BINARY_DATA_SYMBOL ...]
#
# For example, in s2n-bignum's arm directory, after "make" has built the
# object file:
#
#   python3 mlkem_native/check_transcription.py \
#     mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o \
#     mlkem_native_poly_reduce_gcc12_O2 \
#     <mlkem-native>/binaries/multilevel/gcc12/O2/libmlkem.so \
#     mlkem_poly_reduce
#
# If the code refers to read-only data using ADRP and ADD with relocations,
# the pairs of data symbols given are checked to have identical contents,
# and the relocated instructions are checked to compute the address of the
# corresponding data symbol in the binary (allowing for an addend).

import struct
import sys

class Elf:
  def __init__(self, path):
    self.path = path
    data = self.data = open(path, 'rb').read()
    if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 1:
      sys.exit(path + ': not a 64-bit little-endian ELF file')
    shoff, = struct.unpack_from('<Q', data, 0x28)
    shentsize, shnum = struct.unpack_from('<HH', data, 0x3a)
    self.sections = [struct.unpack_from('<IIQQQQIIQQ', data,
                                        shoff + i * shentsize)
                     for i in range(shnum)]
    self.symbols = []
    for sh in self.sections:
      if sh[1] != 2:             # SHT_SYMTAB
        continue
      strtab = self.sections[sh[6]]
      for off in range(sh[4], sh[4] + sh[5], 24):
        st_name, st_info, st_other, st_shndx, st_value, st_size = \
          struct.unpack_from('<IBBHQQ', data, off)
        start = strtab[4] + st_name
        name = data[start:data.index(b'\0', start)].decode()
        self.symbols.append((name, st_info & 0xf, st_shndx, st_value, st_size))

  def symbol(self, name):
    for sym in self.symbols:
      if sym[0] == name and sym[1] in (1, 2):      # STT_OBJECT, STT_FUNC
        return sym
    sys.exit(self.path + ': no symbol ' + name)

  def contents(self, sym):
    sec = self.sections[sym[2]]
    pos = sec[4] + sym[3] - sec[3]
    return self.data[pos:pos + sym[4]]

  def relocations(self, shndx):
    # Map from offsets in section shndx to (type, symbol, addend)
    relocs = {}
    for sh in self.sections:
      if sh[1] != 4 or sh[7] != shndx:              # SHT_RELA for it
        continue
      for off in range(sh[4], sh[4] + sh[5], 24):
        r_offset, r_info, r_addend = struct.unpack_from('<QQq', self.data, off)
        relocs[r_offset] = (r_info & 0xffffffff, r_info >> 32, r_addend)
    return relocs

def word(b, i):
  return struct.unpack_from('<I', b, i)[0]

if len(sys.argv) < 5 or len(sys.argv) % 2 == 0:
  sys.exit('usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL'
           ' [DATA_SYMBOL BINARY_DATA_SYMBOL ...]')

obj, binary = Elf(sys.argv[1]), Elf(sys.argv[3])
fsym, bsym = obj.symbol(sys.argv[2]), binary.symbol(sys.argv[4])
mine, theirs = obj.contents(fsym), binary.contents(bsym)
ok = True
if len(mine) != len(theirs):
  print('DIFFERENT: %d bytes versus %d bytes' % (len(mine), len(theirs)))
  ok = False

# Data symbols, mapping symbols in the object to addresses in the binary

datamap = {}
for i in range(5, len(sys.argv), 2):
  dsym, bdsym = obj.symbol(sys.argv[i]), binary.symbol(sys.argv[i + 1])
  if obj.contents(dsym) != binary.contents(bdsym):
    print('DIFFERENT: data %s and %s' % (sys.argv[i], sys.argv[i + 1]))
    ok = False
  datamap[(dsym[2], dsym[3])] = bdsym[3]

relocs = obj.relocations(fsym[2])
for i in range(0, min(len(mine), len(theirs)), 4):
  w0, w1 = word(mine, i), word(theirs, i)
  r = relocs.get(fsym[3] + i)
  if r is None:
    if w0 != w1:
      print('DIFFERENT: instruction at offset 0x%x' % i)
      ok = False
    continue
  rtype, rsym, addend = r
  name, _, shndx, value, _ = obj.symbols[rsym]
  target = datamap.get((shndx, value))
  if target is None:
    # A section symbol, so the addend is relative to the section
    for (dshndx, dvalue), btarget in datamap.items():
      if dshndx == shndx:
        target = btarget - dvalue
  if target is None:
    print('DIFFERENT: unknown relocation target at offset 0x%x' % i)
    ok = False
    continue
  target += addend
  pc = bsym[3] + i
  if rtype == 275:               # R_AARCH64_ADR_PREL_PG_HI21
    imm = ((w1 >> 29) & 3) | (((w1 >> 5) & 0x7ffff) << 2)
    if imm & 0x100000:
      imm -= 0x200000
    good = (w0 & 0x9f00001f) == (w1 & 0x9f00001f) and \
           (pc & ~0xfff) + (imm << 12) == target & ~0xfff
  elif rtype == 277:             # R_AARCH64_ADD_ABS_LO12_NC
    good = (w0 & 0xffc003ff) == (w1 & 0xffc003ff) and \
           (w1 >> 10) & 0xfff == target & 0xfff
  else:
    good = False
  if not good:
    print('DIFFERENT: relocated instruction at offset 0x%x' % i)
    ok = False

if ok:
  print('OK: %s and %s are identical (%d bytes)' %
        (sys.argv[2], sys.argv[4], len(mine)))
sys.exit(0 if ok else 1)
