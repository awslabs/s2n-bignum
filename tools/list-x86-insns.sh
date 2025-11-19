#!/bin/bash
# This script must be run from the "x86/" directory
# Choose output file based on input argument (no default)

if [ "$#" -ne 1 ]; then
  echo "list-x86-insns.sh <output.ml>"
fi

outfile=$1

# Choose slightly different parameters on clang-based Mac OS / ARM setup

OSTYPE_RESULT=`uname`

if [ "$OSTYPE_RESULT" = "Darwin" ]; then
  ASSEMBLE="as -arch x86_64"
  OBJDUMP="objdump"
else
  ASSEMBLE="as"
  OBJDUMP="objdump --insn-width=16"
fi

# Concatenate the code from all s2n-bignum assembler source files.
# (The pattern is more involved than */*.S to avoid "proofs/template.S".)
# Scrub any data declarations and then assemble, using the Windows
# ABI versions since in principle they may use strictly more instructions.

for i in [a-oq-z]*/*.S p[235]*/*.S
do
  egrep -v '\.quad|\.word' $i | gcc -E -I ../include  -xassembler-with-cpp -DWINDOWS_ABI=1 - >/tmp/source_nodata.S
  $ASSEMBLE -c /tmp/source_nodata.S -o /tmp/objcode_nodata.o
  $OBJDUMP -M intel --no-addresses --no-show-raw-insn -d /tmp/objcode_nodata.o
done  >/tmp/all_disassembly

# Extract the object files and split into register and memory operations
# Replace memory cell in all memory ops with a fixed [rsp+32]
# Thus collect 2 lists of instructions we want to handle

grep '^\s' /tmp/all_disassembly | sed -E -e 's/^( |\t)*//' | sed -e 's/\#.*$//' | sort | uniq >/tmp/all_instructions
grep '\[' /tmp/all_instructions | grep -vi '^lea'  >/tmp/fullmemory_instructions
(grep -v '\[' /tmp/all_instructions ; grep -i '^lea' /tmp/all_instructions) >/tmp/other_instructions
echo '.intel_syntax noprefix' >/tmp/register_instructions
egrep -vi '^(j|call|ret|push|pop)' /tmp/other_instructions | grep -vwi rsp | grep -vwi rip | sort | uniq  >>/tmp/register_instructions
echo '.intel_syntax noprefix' >/tmp/memory_instructions
sed -e 's/\[.*\]/MEMORY_CELL/' /tmp/fullmemory_instructions | grep -vwi rsp | grep -vwi rip | sort | uniq | sed -e 's/MEMORY_CELL/[rsp+32]/' >>/tmp/memory_instructions

# Now turn them into the syntax for the simulator OCaml input

echo 'let iclasses_regreg = [' > "$outfile"
$ASSEMBLE -c /tmp/register_instructions -o /tmp/register.o
$OBJDUMP -M intel --no-addresses -d /tmp/register.o | grep '^\s' | sed -E -e 's/^( |\t)*/ /' | sed -E -e 's/( |\t)( |\t).*//' >/tmp/register_codings
sed -E -e 's/([0-9a-f][0-9a-f])/0x\1;/g' /tmp/register_codings | sed -e 's/^ /\[/' | sed -e 's/;$/];/' >/tmp/register_paste1
grep -v '.intel_syntax'  /tmp/register_instructions | sed -E -e 's/(^.*$)/\(\* \1 \*\)/' >/tmp/register_paste2
paste -d ' ' /tmp/register_paste1 /tmp/register_paste2 >> "$outfile"
echo '];;' >> "$outfile"
echo '' >> "$outfile"

echo 'let iclasses_simplemem = [' >> "$outfile"
$ASSEMBLE -c /tmp/memory_instructions -o /tmp/memory.o
$OBJDUMP -M intel --no-addresses -d /tmp/memory.o | grep '^\s' | sed -E -e 's/^( |\t)*/ /' | sed -E -e 's/( |\t)( |\t).*//' >/tmp/memory_codings
sed -E -e 's/([0-9a-f][0-9a-f])/0x\1;/g' /tmp/memory_codings | sed -e 's/^ /\[/' | sed -e 's/;$/];/' >/tmp/memory_paste1
grep -v '.intel_syntax'  /tmp/memory_instructions | sed -E -e 's/(^.*$)/\(\* \1 \*\)/' >/tmp/memory_paste2
paste -d ' ' /tmp/memory_paste1 /tmp/memory_paste2 >> "$outfile"
echo '];;' >> "$outfile"
