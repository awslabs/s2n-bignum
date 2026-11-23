/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * The linker script for the image of the AVX-512 version of the x86
 * mlkem_native2 functions used in their proofs, built by the rule for
 * mlkem_native/asm_avx512/mlkem_native2_avx512_image.elf in proofs.mk: the
 * code of the objects in the order given there, linked at address 0,
 * followed by the constants block, all in the one section .text.
 */

SECTIONS
{
  .text 0 :
  {
    *(.text)
    . = ALIGN(64);
    *(.rodata)
  }
  /DISCARD/ : { *(*) }
}
