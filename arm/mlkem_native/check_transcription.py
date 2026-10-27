#!/usr/bin/env python3

# Check that a function in an assembled transcription (an ELF object file)
# has exactly the same code bytes as a function in a binary (e.g. one of
# the libmlkem.so files in mlkem-native's binary branch).
#
# Usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL
#
# For example, in s2n-bignum's arm directory, after "make" has built the
# object file:
#
#   python3 mlkem_native/check_transcription.py \
#     mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o \
#     mlkem_native_poly_reduce_gcc12_O2 \
#     <mlkem-native>/binaries/multilevel/gcc12/O2/libmlkem.so \
#     mlkem_poly_reduce

import struct
import sys

def symbol_bytes(path, name):
  data = open(path, 'rb').read()
  if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 1:
    sys.exit(path + ': not a 64-bit little-endian ELF file')
  shoff, = struct.unpack_from('<Q', data, 0x28)
  shentsize, shnum = struct.unpack_from('<HH', data, 0x3a)
  sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize)
              for i in range(shnum)]
  for sh in sections:
    if sh[1] != 2:               # SHT_SYMTAB
      continue
    strtab = sections[sh[6]]
    for off in range(sh[4], sh[4] + sh[5], 24):
      st_name, st_info, st_other, st_shndx, st_value, st_size = \
        struct.unpack_from('<IBBHQQ', data, off)
      start = strtab[4] + st_name
      sym = data[start:data.index(b'\0', start)].decode()
      if sym == name and (st_info & 0xf) == 2:     # STT_FUNC
        sec = sections[st_shndx]
        pos = sec[4] + st_value - sec[3]
        return data[pos:pos + st_size]
  sys.exit(path + ': no function symbol ' + name)

if len(sys.argv) != 5:
  sys.exit('usage: check_transcription.py FILE.o SYMBOL BINARY BINARY_SYMBOL')

mine = symbol_bytes(sys.argv[1], sys.argv[2])
theirs = symbol_bytes(sys.argv[3], sys.argv[4])
if mine == theirs:
  print('OK: %s and %s are identical (%d bytes)' %
        (sys.argv[2], sys.argv[4], len(mine)))
  sys.exit(0)
if len(mine) != len(theirs):
  print('DIFFERENT: %d bytes versus %d bytes' % (len(mine), len(theirs)))
for i in range(0, min(len(mine), len(theirs)), 4):
  if mine[i:i+4] != theirs[i:i+4]:
    print('DIFFERENT: first difference at offset 0x%x' % i)
    break
sys.exit(1)
