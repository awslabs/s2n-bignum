/*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* Linker script for the Sail-backed RV32IM cosimulation template. The
   `.cosim` address is shared with riscv/proofs/sail-cosim-runner. */

OUTPUT_ARCH("riscv")
ENTRY(_start)

SECTIONS
{
  . = 0x80000000;
  .text.init : { *(.text.init) }
  . = 0x80001000;
  .cosim : { *(.cosim) }
  . = 0x80002000;
  .tohost : { *(.tohost) }
}
