/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *
 * Assembler macros of the x86 mlkem_native2 functions.
 *
 * leadisp dst, base, disp is lea dst, [base+(disp)] for an offset disp
 * that is 0 in some instances of the code, and mov dst, base in those,
 * which is how GNU as with -O2 assembles such an lea anyway: the code is
 * then the same whatever the options of the assembler.
 */
#ifndef MLKEM_NATIVE2_MACROS_H
#define MLKEM_NATIVE2_MACROS_H

        .macro  leadisp dst, base, disp
        .if     (\disp) == 0
        mov     \dst, \base
        .else
        lea     \dst, [\base+(\disp)]
        .endif
        .endm

#endif
