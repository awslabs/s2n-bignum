#!/usr/bin/env python3

# Check that a function in an assembled transcription (an ELF object file)
# has exactly the same code as a function in a binary (e.g. libmlkem.so
# built for x86-64 by the recipe of mlkem-native's binary branch).
#
# Usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL
#                               [DATA_SYMBOL BINARY_DATA_SYMBOL ...]
#
# For example, in s2n-bignum's x86 directory, after "make" has built the
# object file:
#
#   python3 mlkem_native/check_transcription.py \
#     mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o \
#     mlkem_native_poly_reduce_gcc12_O2 \
#     <build>/multilevel/gcc12/O2/libmlkem.so \
#     mlkem_poly_reduce
#
# If the code refers to read-only data with RIP-relative addressing, the
# displacements are R_X86_64_PC32 relocations in the object file. The pairs
# of data symbols given are checked to have identical contents, and the
# relocated displacements in the binary are checked to give the address of
# the corresponding data there (allowing for the addend). For data without a
# symbol in the binary, its address can be given in hexadecimal instead.
#
# Alternatively, with SYMBOL given as "-" and BINARY_SYMBOL as an address in
# hexadecimal, the whole .text section of FILE.o is checked to be identical,
# without any relocations, to the contents of the loaded segments of BINARY
# starting at that address. This is for the transcription of a whole image.

import struct
import sys

class Elf:
  def __init__(self, path):
    self.path = path
    data = self.data = open(path, 'rb').read()
    if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 1:
      sys.exit(path + ': not a 64-bit little-endian ELF file')
    machine, = struct.unpack_from('<H', data, 0x12)
    if machine != 62:                               # EM_X86_64
      sys.exit(path + ': not an x86-64 ELF file')
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

  def bytes_at(self, addr, size):
    # Contents of the section with the given virtual address range
    for sec in self.sections:
      if sec[1] == 1 and sec[3] <= addr and addr + size <= sec[3] + sec[5]:
        pos = sec[4] + addr - sec[3]
        return self.data[pos:pos + size]
    sys.exit(self.path + ': no data at address 0x%x' % addr)

  def segment_bytes(self, addr, size):
    # Contents of memory from the given virtual address when the binary is
    # loaded. Each loadable segment maps whole pages (of its alignment) of
    # the file, so the bytes up to the end of the page containing the end of
    # its data are those of the file, except that any part beyond the data
    # in the file but within the segment in memory (as for .bss) is zero.
    phoff, = struct.unpack_from('<Q', self.data, 0x20)
    phentsize, phnum = struct.unpack_from('<HH', self.data, 0x36)
    segs = []
    for i in range(phnum):
      p_type, _, p_offset, p_vaddr, _, p_filesz, p_memsz, p_align = \
        struct.unpack_from('<IIQQQQQQ', self.data, phoff + i * phentsize)
      if p_type == 1:
        page = max(p_align, 1)
        start = p_vaddr - p_vaddr % page
        end = -(-(p_vaddr + max(p_filesz, p_memsz)) // page) * page
        segs.append((start, end, p_offset - (p_vaddr - start),
                     p_vaddr + p_filesz, p_memsz > p_filesz))
    out = bytearray()
    while len(out) < size:
      a = addr + len(out)
      for start, end, off, fend, bss in segs:
        if start <= a < end:
          n = min(size - len(out), end - a)
          for k in range(a, a + n):
            out.append(0 if bss and k >= fend else self.data[off + k - start])
          break
      else:
        sys.exit(self.path + ': no segment with data at address 0x%x' % a)
    return bytes(out)

  def section_index(self, name):
    shstrndx, = struct.unpack_from('<H', self.data, 0x3e)
    strtab = self.sections[shstrndx]
    for i, sh in enumerate(self.sections):
      start = strtab[4] + sh[0]
      if self.data[start:self.data.index(b'\0', start)].decode() == name:
        return i
    sys.exit(self.path + ': no section ' + name)

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

if len(sys.argv) < 5 or len(sys.argv) % 2 == 0:
  sys.exit('usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL'
           ' [DATA_SYMBOL BINARY_DATA_SYMBOL ...]')

obj, binary = Elf(sys.argv[1]), Elf(sys.argv[3])

if sys.argv[2] == '-':
  if len(sys.argv) != 5 or not sys.argv[4].startswith('0x'):
    sys.exit('usage: check_transcription.py FILE.o - BINARY ADDRESS')
  text = obj.section_index('.text')
  sec = obj.sections[text]
  mine = obj.data[sec[4]:sec[4] + sec[5]]
  theirs = binary.segment_bytes(int(sys.argv[4], 16), len(mine))
  if obj.relocations(text):
    print('DIFFERENT: the .text section has relocations')
  elif mine != theirs:
    diffs = [i for i in range(len(mine)) if mine[i] != theirs[i]]
    print('DIFFERENT: %d bytes, the first at offset 0x%x' %
          (len(diffs), diffs[0]))
  else:
    print('OK: the .text section and the segments from %s are identical '
          '(%d bytes)' % (sys.argv[4], len(mine)))
    sys.exit(0)
  sys.exit(1)

fsym, bsym = obj.symbol(sys.argv[2]), binary.symbol(sys.argv[4])
mine, theirs = obj.contents(fsym), binary.contents(bsym)
ok = True
if len(mine) != len(theirs):
  print('DIFFERENT: %d bytes versus %d bytes' % (len(mine), len(theirs)))
  ok = False

# Data symbols, mapping symbols in the object to addresses in the binary

datamap = {}
for i in range(5, len(sys.argv), 2):
  dsym = obj.symbol(sys.argv[i])
  if sys.argv[i + 1].startswith('0x'):
    baddr = int(sys.argv[i + 1], 16)
    bdata = binary.bytes_at(baddr, dsym[4])
  else:
    bdsym = binary.symbol(sys.argv[i + 1])
    baddr, bdata = bdsym[3], binary.contents(bdsym)
  if obj.contents(dsym) != bdata:
    print('DIFFERENT: data %s and %s' % (sys.argv[i], sys.argv[i + 1]))
    ok = False
  datamap[(dsym[2], dsym[3])] = baddr

# The relocated displacements, each 4 bytes, which are compared separately

relocs = obj.relocations(fsym[2])
fields = {}
for off, r in relocs.items():
  if fsym[3] <= off < fsym[3] + fsym[4]:
    fields[off - fsym[3]] = r

i = 0
n = min(len(mine), len(theirs))
while i < n:
  r = fields.get(i)
  if r is None:
    if mine[i] != theirs[i]:
      print('DIFFERENT: byte at offset 0x%x' % i)
      ok = False
    i += 1
    continue
  rtype, rsym, addend = r
  name, stype, shndx, value, _ = obj.symbols[rsym]
  disp, = struct.unpack_from('<i', theirs, i)
  good = False
  if rtype == 2:                                  # R_X86_64_PC32
    target = datamap.get((shndx, value)) if stype != 3 else None
    if target is not None:
      good = (bsym[3] + i + disp - (target + addend)) % 2**64 == 0
    else:
      # A section symbol: the data referred to is at value + addend + 4 + k
      # in the section, with k the number of bytes of the instruction after
      # the displacement (an immediate), so find a data symbol containing it
      for k in (0, 1, 2, 4):
        t = value + addend + 4 + k
        for (dshndx, dvalue), btarget in datamap.items():
          size = [sy[4] for sy in obj.symbols
                  if sy[2] == dshndx and sy[3] == dvalue and sy[1] == 1]
          if dshndx == shndx and size and dvalue <= t <= dvalue + size[0]:
            bt = btarget + t - dvalue
            if (bsym[3] + i + 4 + k + disp - bt) % 2**64 == 0:
              good = True
  if not good:
    print('DIFFERENT: relocated displacement at offset 0x%x' % i)
    ok = False
  i += 4

if ok:
  print('OK: %s and %s are identical (%d bytes)' %
        (sys.argv[2], sys.argv[4], len(mine)))
sys.exit(0 if ok else 1)
