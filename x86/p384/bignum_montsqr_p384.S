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
// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_montsqr_p384
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is
// guaranteed in particular if x < p_384 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v r10
#define w r11

// A zero register, very often

#define zero rbp

// Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of the
// rotating register window r15,...,r8 maintaining consistent
// double-carrying using ADCX and ADOX and using rbx/rax as temps

.macro mulpadd arg1,arg2
        mulx    rbx, rax, \arg2
.if (\arg1 % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif (\arg1 % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif (\arg1 % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif (\arg1 % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif (\arg1 % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif (\arg1 % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif (\arg1 % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif (\arg1 % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing [d5;d4;d3;d2;d1] and re-using d0 as a
// temporary internally, as well as rax, rbx and rdx.
// It is OK for d6 and d0 to be the same register (they often are)
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64
//
//       montreds d6,d5,d4,d3,d2,d1,d0

.macro montreds d6,d5,d4,d3,d2,d1,d0
// Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64
                mov     rdx, \d0
                shl     rdx, 32
                add     rdx, \d0
// Construct [rbx;d0;rax;-] = (2^384 - p_384) * w
// We know the lowest word will cancel so we can re-use d0 as a temp, and rbx
                mov     rax, 0xffffffff00000001
                mulx    rax, \d0, rax
                mov     ebx, 0x00000000ffffffff
                mulx    \d0, rbx, rbx
                add     rax, rbx
                adc     \d0, rdx
                mov     ebx, 0
                adc     rbx, rbx
// Now subtract that and add 2^384 * w
                sub     \d1, rax
                sbb     \d2, \d0
                sbb     \d3, rbx
                sbb     \d4, 0
                sbb     \d5, 0
                mov     \d6, rdx
                sbb     \d6, 0
.endm

.intel_syntax noprefix

                .globl  bignum_montsqr_p384

bignum_montsqr_p384:

// Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Set up an initial window [rcx;r15;...r9] = [34;05;03;01]
// Note that we are using rcx as the first step past the rotating window

        mov     rdx, [x]
        mulx    r10, r9, [x+8*1]
        mulx    r12, r11, [x+8*3]
        mulx    r14, r13, [x+8*5]
        mov     rdx, [x+8*3]
        mulx    rcx, r15, [x+8*4]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zero, zero

// Chain in the addition of 02 + 12 + 13 + 14 + 15 to that window
// (no carry-out possible)

        mov     rdx, [x+8*2]
        mulpadd 2,[x]
        mulpadd 3, [x+8*1]
        mov     rdx, [x+8*1]
        mulpadd 4, [x+8*3]
        mulpadd 5, [x+8*4]
        mulpadd 6, [x+8*5]
        adcx    r15, zero
        adox    rcx, zero
        adcx    rcx, zero

// Again zero out the flags. Actually they are already cleared but it may
// help decouple these in the OOO engine not to wait for the chain above

        xor     zero, zero

// Now chain in the 04 + 23 + 24 + 25 + 35 + 45 terms
// We are running out of registers in our rotating window, so we start
// using rbx (and hence need care with using mulpadd after this). Thus
// our result so far is in [rbp;rbx;rcx;r15;...r9]

        mov     rdx, [x+8*4]
        mulpadd 4, [x]
        mov     rdx, [x+8*2]
        mulpadd 5, [x+8*3]
        mulpadd 6, [x+8*4]
        mulx    rdx, rax, [x+8*5]
        adcx    r15, rax
        adox    rcx, rdx

// First set up the last couple of spots in our window, [rbp;rbx] = 45
// then add the last other term 35

        mov     rdx, [x+8*5]
        mulx    rbp, rbx, [x+8*4]
        mulx    rdx, rax, [x+8*3]
        adcx    rcx, rax
        adox    rbx, rdx
        mov     eax, 0
        adcx    rbx, rax
        adox    rbp, rax
        adcx    rbp, rax

// Just for a clear fresh start for the flags; we don't use the zero

        xor     rax, rax

// Double and add to the 00 + 11 + 22 + 33 + 44 + 55 terms
// For one glorious moment the entire squaring result is all in the
// register file as [rsi;rbp;rbx;rcx;r15;...;r8]
// (since we've now finished with x we can re-use rsi)

        mov     rdx, [x]
        mulx    rax, r8, [x]
        adcx    r9, r9
        adox    r9, rax
        mov     rdx, [x+8*1]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [x+8*2]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [x+8*3]
        mulx    rdx, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, r15
        adox    r15, rdx
        mov     rdx, [x+8*4]
        mulx    rdx, rax, rdx
        adcx    rcx, rcx
        adox    rcx, rax
        adcx    rbx, rbx
        adox    rbx, rdx
        mov     rdx, [x+8*5]
        mulx    rsi, rax, rdx
        adcx    rbp, rbp
        adox    rbp, rax
        mov     eax, 0
        adcx    rsi, rax
        adox    rsi, rax

// We need just *one* more register as a temp for the Montgomery steps.
// Since we are writing to the z buffer anyway, make use of that to stash rbx.

        mov     [z], rbx

// Montgomery reduce the r13,...,r8 window 6 times

        montreds r8,r13,r12,r11,r10,r9,r8
        montreds r9,r8,r13,r12,r11,r10,r9
        montreds r10,r9,r8,r13,r12,r11,r10
        montreds r11,r10,r9,r8,r13,r12,r11
        montreds r12,r11,r10,r9,r8,r13,r12
        montreds r13,r12,r11,r10,r9,r8,r13

// Now we can safely restore rbx before accumulating

        mov     rbx, [z]

        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0
        adc     r8, 0

// We now have a pre-reduced 7-word form z = [r8; rsi;rbp;rbx;rcx;r15;r14]
// Next, accumulate in different registers z - p_384, or more precisely
//
//   [r8; r13;r12;r11;r10;r9;rax] = z + (2^384 - p_384)

        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        mov     rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0x00000000ffffffff
        adc     r9, r15
        mov     r10d, 0x0000000000000001
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0

// ~ZF <=> r12 >= 1 <=> z + (2^384 - p_384) >= 2^384 <=> z >= p_384, which
// determines whether to use the further reduced argument or the original z.

        cmovnz  r14, rax
        cmovnz  r15, r9
        cmovnz  rcx, r10
        cmovnz  rbx, r11
        cmovnz  rbp, r12
        cmovnz  rsi, r13

// Write back the result

        mov     [z], r14
        mov     [z+8*1], r15
        mov     [z+8*2], rcx
        mov     [z+8*3], rbx
        mov     [z+8*4], rbp
        mov     [z+8*5], rsi

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret