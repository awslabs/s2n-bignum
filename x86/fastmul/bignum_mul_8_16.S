/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[8], y[8]; output z[16]
//
//    extern void bignum_mul_8_16
//     (uint64_t z[static 16], uint64_t x[static 8], uint64_t y[static 8]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------

// These are actually right

#define z rdi
#define x rsi

// Copied in or set up

#define y rcx

// A zero register

#define zero rbp

// Hm, it's so painful not being able to numerically index registers
// Add in x[i] * rdx to the (i,i+1) position with the register window
// Would be nice to have conditional expressions reg[i], reg[i+1] ...

.macro mulpadd arg1,arg2
        mulx    rbx, rax, [x+8*\arg2]
.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm


// Add in the whole j'th row

.macro addrow arg1
        mov     rdx, [y+8*\arg1]
        xor     zero, zero

        mulpadd \arg1, 0

.if (\arg1 % 8 == 0)
        mov     [z+8*\arg1],r8
.elseif (\arg1 % 8 == 1)
        mov     [z+8*\arg1],r9
.elseif (\arg1 % 8 == 2)
        mov     [z+8*\arg1],r10
.elseif (\arg1 % 8 == 3)
        mov     [z+8*\arg1],r11
.elseif (\arg1 % 8 == 4)
        mov     [z+8*\arg1],r12
.elseif (\arg1 % 8 == 5)
        mov     [z+8*\arg1],r13
.elseif (\arg1 % 8 == 6)
        mov     [z+8*\arg1],r14
.elseif (\arg1 % 8 == 7)
        mov     [z+8*\arg1],r15
.endif

        mulpadd \arg1, 1
        mulpadd \arg1, 2
        mulpadd \arg1, 3
        mulpadd \arg1, 4
        mulpadd \arg1, 5
        mulpadd \arg1, 6

.if (\arg1 % 8 == 0)
        mulx    r8, rax, [x+8*7]
        adcx    r15, rax
        adox    r8, zero
        adcx    r8, zero
.elseif (\arg1 % 8 == 1)
        mulx    r9, rax, [x+8*7]
        adcx    r8, rax
        adox    r9, zero
        adcx    r9, zero
.elseif (\arg1 % 8 == 2)
        mulx    r10, rax, [x+8*7]
        adcx    r9, rax
        adox    r10, zero
        adcx    r10, zero
.elseif (\arg1 % 8 == 3)
        mulx    r11, rax, [x+8*7]
        adcx    r10, rax
        adox    r11, zero
        adcx    r11, zero
.elseif (\arg1 % 8 == 4)
        mulx    r12, rax, [x+8*7]
        adcx    r11, rax
        adox    r12, zero
        adcx    r12, zero
.elseif (\arg1 % 8 == 5)
        mulx    r13, rax, [x+8*7]
        adcx    r12, rax
        adox    r13, zero
        adcx    r13, zero
.elseif (\arg1 % 8 == 6)
        mulx    r14, rax, [x+8*7]
        adcx    r13, rax
        adox    r14, zero
        adcx    r14, zero
.elseif (\arg1 % 8 == 7)
        mulx    r15, rax, [x+8*7]
        adcx    r14, rax
        adox    r15, zero
        adcx    r15, zero
.endif

.endm



.intel_syntax noprefix

                .globl  bignum_mul_8_16
                .text

bignum_mul_8_16:

// Save more registers to play with

        push    rbp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

// Copy y into a safe register to start with

        mov     y, rdx

// Zero a register, which also makes sure we don't get a fake carry-in

        xor     zero, zero

// Do the zeroth row, which is a bit different
// Write back the zero-zero product and then accumulate
// r8,r15,r14,r13,r12,r11,r10,r9 as y[0] * x from 1..8

        mov     rdx, [y+8*0]

        mulx    r9, r8, [x+8*0]
        mov     [z+8*0], r8

        mulx    r10, rbx, [x+8*1]
        adcx    r9, rbx

        mulx    r11, rbx, [x+8*2]
        adcx    r10, rbx

        mulx    r12, rbx, [x+8*3]
        adcx    r11, rbx

        mulx    r13, rbx, [x+8*4]
        adcx    r12, rbx

        mulx    r14, rbx, [x+8*5]
        adcx    r13, rbx

        mulx    r15, rbx, [x+8*6]
        adcx    r14, rbx

        mulx    r8, rbx, [x+8*7]
        adcx    r15, rbx
        adcx    r8, zero

// Now all the other rows in a uniform pattern

        addrow  1
        addrow  2
        addrow  3
        addrow  4
        addrow  5
        addrow  6
        addrow  7

// Now write back the additional columns

        mov     [z+8*8], r8
        mov     [z+8*9], r9
        mov     [z+8*10], r10
        mov     [z+8*11], r11
        mov     [z+8*12], r12
        mov     [z+8*13], r13
        mov     [z+8*14], r14
        mov     [z+8*15], r15

// Real epilog



        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

        ret