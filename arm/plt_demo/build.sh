#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Builds the test library libplt_demo.so from src/plt_demo.S as a shared
# object with the link options of the snappy build (-Bsymbolic, -z now,
# -z relro), so that its imports memcpy and memmove are called through the
# PLT and its data has RELATIVE, ABS64, GLOB_DAT and JUMP_SLOT relocations,
# and writes, with the tools of the snappy image, the transcription
# plt_demo.S of its image and the relocations ../proofs/plt_demo_relocs.ml.
# Run in this directory with an AArch64 gcc and binutils (e.g. those of the
# nix environment of the proofs); the offsets in ../proofs/plt_demo.ml are
# those of the build with GNU ld 2.46. Without --write it checks the
# committed files.

set -e
CC=${CC:-gcc}
TMP=$(mktemp -d)
$CC -c src/plt_demo.S -o $TMP/plt_demo.o
$CC -shared -nostdlib -Wl,-Bsymbolic -Wl,-z,now -Wl,-z,relro \
    -Wl,--build-id=none -Wl,-soname,libplt_demo.so \
    $TMP/plt_demo.o -o $TMP/libplt_demo.so
python3 ../../tools/elf_transcribe.py \
    --title "the test library libplt_demo.so" \
    --source "libplt_demo.so built by plt_demo/build.sh" \
    --image-end .text $TMP/libplt_demo.so plt_demo $PWD/../../include \
    > $TMP/plt_demo.S
python3 ../../tools/elf_relocs.py --title "the test library libplt_demo.so" \
    $TMP/libplt_demo.so plt_demo > $TMP/plt_demo_relocs.ml
if [ "$1" = "--write" ]; then
  cp $TMP/plt_demo.S plt_demo.S
  cp $TMP/plt_demo_relocs.ml ../proofs/plt_demo_relocs.ml
else
  cmp $TMP/plt_demo.S plt_demo.S
  cmp $TMP/plt_demo_relocs.ml ../proofs/plt_demo_relocs.ml
  echo "plt_demo.S and plt_demo_relocs.ml are those of libplt_demo.so"
fi
rm -r $TMP
