// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo m, z := x mod m, where m is k digits and x is n digits
// Inputs x[n], m[k]; output z[k]
//
//    extern void bignum_mod
//     (uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x,
//      const uint64_t *m);
//
// Reduces the n-digit input x modulo the k-digit modulus m, producing the
// k-digit result z. There are no restrictions on the relative sizes of n
// and k; in particular n may be smaller or larger than k. The modulus m
// is assumed to be nonzero.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x, X4 = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod)
        .text
        .balign 4

#define movbig(nn,n3,n2,n1,n0)                                          \
        movz    nn, n0 __LF                                             \
        movk    nn, n1, lsl #16 __LF                                    \
        movk    nn, n2, lsl #32 __LF                                    \
        movk    nn, n3, lsl #48

// We get BLOCKSIZE bits per iteration

#define BLOCKSIZE 61

// The input arguments, which don't move from their initial placement

#define k x0
#define z x1
#define n x2
#define x x3
#define m x4

// Short-term variables

#define hh x5
#define ll x6
#define tt x7
#define ii x8
#define mm x9
#define ss x10
#define dd x11
#define pcode x12
#define lf x13
#define hf x14

// Longer-term variables

#define q x15
#define h x15

#define i x16
#define j x17
#define l x19
#define p x20
#define w x21
#define c x22

// Shadow of the top accumulator word (formerly spilled to z[k])

#define zt x23

// Aliases for other settings

#define t0 hh
#define t1 ll
#define t2 mm
#define t3 dd
#define t4 w

S2N_BN_SYMBOL(bignum_mod):
        CFI_START

// We make use of registers beyond the modifiable

        CFI_PUSH2(x19,x20)
        CFI_PUSH2(x21,x22)
        CFI_PUSH2(x23,x24)

// Zero the k result words z[0..k-1]; the (k+1)'th accumulator word that the
// original spilled to z[k] is now kept in the register zt. (As before, the
// degenerate k = 0 case still writes z[0]; for a nonzero modulus, which is a
// precondition, this writes exactly z[0..k-1].)

        mov     zt, xzr
        mov     ii, xzr
Lbignum_mod_initloop:
        str     xzr, [z, ii, lsl #3]
        add     ii, ii, #1
        cmp     k, ii
        bhi     Lbignum_mod_initloop

// If n = 0 do nothing

        cmp     n, xzr
        beq     Lbignum_mod_end

// p = bignum_bitsize(k,m);
// t = (p < 64) ? m[0] << (64-p) : bignum_bitfield(k,m,p-64,64);

        mov     hh, xzr         // High of selected pair
        mov     ll, xzr         // Low of selected pair
        mov     dd, xzr         // Selected index
        mov     ss, xzr         // Previous word

        mov     ii, xzr
        cbz     k, Lbignum_mod_findertail
Lbignum_mod_finderloop:
        ldr     tt, [m, ii, lsl #3]
        cmp     tt, xzr
        csel    hh, tt, hh, ne
        csel    ll, ss, ll, ne
        csel    dd, ii, dd, ne
        mov     ss, tt

        add     ii, ii, #1
        cmp     ii, k
        bcc     Lbignum_mod_finderloop
Lbignum_mod_findertail:
        clz     tt, hh
        lsl     p, dd, #6
        add     p, p, #64
        sub     p, p, tt

        lsl     hh, hh, tt
        neg     tt, tt
        lsr     ll, ll, tt
        orr     ll, hh, ll

        cmp     tt, xzr
        csel    t0, hh, ll, eq

// w = word_recip((t + 1 == 0) ? t : t + 1);
// Crudely inlined version of word_recip; may get away with weaker though

        adds    t0, t0, #1
        cinv    t0, t0, eq

        lsr     t2, t0, #16
        eor     t1, t2, #0x1ffffffffffff
        add     t2, t2, #0x1
        lsr     t1, t1, #32
        mneg    t4, t2, t1
        lsr     t3, t4, #49
        mul     t3, t3, t3
        lsr     t4, t4, #34
        add     t4, t3, t4
        orr     t3, t3, #0x40000000
        mul     t3, t4, t3
        lsr     t3, t3, #30
        lsl     t4, t1, #30
        madd    t1, t1, t3, t4
        lsr     t1, t1, #30
        mneg    t4, t2, t1
        lsr     t4, t4, #24
        mul     t4, t4, t1
        lsl     t1, t1, #16
        lsr     t4, t4, #24
        add     t1, t1, t4
        mneg    t4, t2, t1
        lsr     t4, t4, #32
        mul     t4, t4, t1
        lsl     t1, t1, #31
        lsr     t4, t4, #17
        add     t1, t1, t4
        mul     t3, t0, t1
        umulh   t4, t0, t1
        extr    t3, t4, t3, #60
        lsr     t4, t1, #33
        mvn     t3, t3
        mul     t3, t4, t3
        lsl     t1, t1, #1
        lsr     t3, t3, #33
        add     t1, t1, t3
        adds    t3, t1, #0x1
        cinv    t3, t3, eq
        umulh   t4, t0, t3
        adds    t4, t4, t0
        csel    w, t1, t3, cs

// i = BLOCKSIZE * ((64 * n + BLOCKSIZE - 1) / BLOCKSIZE - 1);
// j = BLOCKSIZE;
//
// Avoid udiv using reciprocal multiplication on n directly
//
// ARITH_RULE
//  `n < 2 EXP 60
//   ==> (64 * n) DIV 61 =
//       (0xc9714fbcda3ac11 * n) DIV 2 EXP 64 + n`;;

        movbig(t0, 0xc97, 0x14fb, 0xcda3, 0xac11)
        umulh   t0, t0, n
        add     t0, t0, n               // t0 = (64 * n) / 61
        mov     t1, #BLOCKSIZE
        mul     t0, t0, t1              // t0 = 61 * (64 * n) / 61
        sub     t1, t0, #61             // t1 = 61 * (64 * n) / 61 - 61

        ands    xzr, t0, #0x3F
        csel    i, t0, t1, ne

        mov     j, #BLOCKSIZE

// l = word_min(k+1,(j+63)/64);

        add     t0, k, #1
        add     t1, j, #63
        lsr     t1, t1, #6
        cmp     t0, t1
        csel    l, t0, t1, cc

// c = bignum_bitfield(n,x,i,BLOCKSIZE);
// By choice of i this is within the top word of x, so just use low part of i

        sub     tt, n, #1
        ldr     c, [x, tt, lsl #3]
        lsr     c, c, i

// z[0] = c

        str     c, [z]

// h = (p < 64) ? (c>>p) : 0;

        lsr     h, c, p
        cmp     p, #64
        csel    h, h, xzr, cc

// *** BEGINNING OF MAIN LOOP

        lsr     pcode, p, #6
        add     pcode, pcode, #1

Lbignum_mod_loop:

// i -= BLOCKSIZE;
// c = bitfield(n,x,i,BLOCKSIZE);
// We don't bother masking c since that happens anyway when it's used.
// The upper word index is clamped to n - 1 so as not to read past x;
// when that happens its bits are not part of the field anyway.

        sub     i, i, #BLOCKSIZE

        lsr     t2, i, #6
        ldr     t0, [x, t2, lsl #3]
        add     t3, t2, #1
        cmp     t3, n
        csel    t3, t3, t2, cc
        ldr     t1, [x, t3, lsl #3]

        and     t2, i, #63
        neg     t3, t2

        lsr     t0, t0, t2
        lsl     t1, t1, t3

        orr     t1, t1, t0
        cmp     t2, xzr
        csel    c, t0, t1, eq

// q = multop(w,h) + h;

        umulh   t0, w, h
        add     q, t0, h

// bignum_cmnegadd(l,z,q,k,m);
// *** COMBINED WITH
// bignum_shl_small(l,z,l,z,BLOCKSIZE);
// z[0] += c;
// *** AND ALSO noting data to reconstruct bitfield(z',p,64).
//
// The z := z - q * m is actually done by z + q * ~m + q. Note that
// after the n'th stage in this accumulation process the total is
// therefore <= (B^n - 1) + (B - 1) * (B^n - 1) + (B - 1) where B = 2^64.
// This is exactly B^{n+1} - 1 so the result just fits in n + 1 words
// and we just need the single top word "hh" to carry. In order to do
// the logging as we pass the p bit, it's useful not to require CF as
// part of the carry chain between stages.

        mov     hf, xzr

        lsl     c, c, #(64 - BLOCKSIZE)

        mov     hh, q
        mov     ii, xzr

        subs    dd, l, #1
        beq     Lbignum_mod_trivnegadd

Lbignum_mod_innerloop:
        ldr     tt, [m, ii, lsl #3]
        mvn     tt, tt

        mul     ll, q, tt
        umulh   mm, q, tt

        ldr     ss, [z, ii, lsl #3]
        adds    ss, ss, hh
        cset    tt, cs

        adds    ss, ss, ll
        adc     hh, tt, mm

        extr    c, ss, c, #(64 - BLOCKSIZE)
        str     c, [z, ii, lsl #3]

        cmp     ii, pcode
        csel    lf, c, lf, cc
        csel    hf, c, hf, eq

        mov     c, ss

        add     ii, ii, #1
        cmp     ii, dd
        bne     Lbignum_mod_innerloop

// Last iteration, where we may not load m digit and don't do high stuff

Lbignum_mod_trivnegadd:

        mov     tt, xzr
        cmp     ii, k
        beq     Lbignum_mod_offendm
        ldr     tt, [m, ii, lsl #3]
Lbignum_mod_offendm:
        mvn     tt, tt
        mul     ll, q, tt

// The top accumulator word (ii == k) is held in zt rather than z[k], so both
// its load and its store go to the register; only ii < k touches memory.

        cmp     ii, k
        bne     Lbignum_mod_trivmem
        add     ss, zt, hh
        add     ss, ss, ll
        extr    c, ss, c, #(64 - BLOCKSIZE)
        mov     zt, c
        b       Lbignum_mod_trivlogged
Lbignum_mod_trivmem:
        ldr     ss, [z, ii, lsl #3]
        add     ss, ss, hh
        add     ss, ss, ll
        extr    c, ss, c, #(64 - BLOCKSIZE)
        str     c, [z, ii, lsl #3]
Lbignum_mod_trivlogged:

        cmp     ii, pcode
        csel    lf, c, lf, cc
        csel    hf, c, hf, eq

        add     ii, ii, #1

// j += BLOCKSIZE;
// l' = word_min(k+1,(j+63)/64);

        add     j, j, #BLOCKSIZE

        add     t0, k, #1
        add     t1, j, #63
        lsr     t1, t1, #6
        cmp     t0, t1
        csel    l, t0, t1, cc

// Make it into bignum_shl_small(l',z,l,z,BLOCKSIZE);

        cmp     ii, l
        beq     Lbignum_mod_noel
        lsr     c, ss, #(64 - BLOCKSIZE)
        cmp     ii, k
        bne     Lbignum_mod_noelmem
        mov     zt, c
        b       Lbignum_mod_noellogged
Lbignum_mod_noelmem:
        str     c, [z, ii, lsl #3]
Lbignum_mod_noellogged:

        cmp     ii, pcode
        csel    lf, c, lf, cc
        csel    hf, c, hf, eq

        add     ii, ii, #1

Lbignum_mod_noel:

// Lower field lf is only meaningful if pcode <= i + 1
// If ii + 1 < pcode then override lf = 0
// If ii + 1 = pcode then override lf = z[ii]

        cmp     ii, pcode
        csel    lf, lf, xzr, cs
        csel    lf, c, lf, eq

// Final bitfield selection

        and     t0, p, #63
        neg     t1, t0

        lsr     lf, lf, t0
        lsl     hf, hf, t1

        orr     hf, hf, lf
        cmp     t0, #0
        csel    h, lf, hf, eq

        cbnz    i, Lbignum_mod_loop

// *** END OF MAIN LOOP

// q = multop(w,h) + h;

        umulh   t0, w, h
        add     q, t0, h

// bignum_cmnegadd(l,z,q,k,m);
// At this point l = k + 1 is guaranteed
//
// Fold in storing data for the following bitfield-finder, with
// a variant of pcode (1 less than before)
//
// Since this is the last usage we bump p up to p + BLOCKSIZE

        mov     hh, q
        mov     ii, xzr

        add     p, p, #(64 - BLOCKSIZE)
        lsr     pcode, p, #6
        mov     lf, xzr
        mov     hf, xzr

        cbz     k, Lbignum_mod_negaddtail1
Lbignum_mod_negaddloop1:
        ldr     tt, [m, ii, lsl #3]
        mvn     tt, tt
        mul     ll, q, tt
        umulh   mm, q, tt
        ldr     ss, [z, ii, lsl #3]
        adds    ss, ss, hh
        cset    tt, cs
        adds    ss, ss, ll
        adc     hh, tt, mm
        str     ss, [z, ii, lsl #3]

        cmp     ii, pcode
        csel    lf, ss, lf, cc
        csel    hf, ss, hf, eq

        add     ii, ii, #1
        cmp     ii, k
        bne     Lbignum_mod_negaddloop1
Lbignum_mod_negaddtail1:
        sub     hh, hh, q
        mov     ss, zt                  // top word (was z[k])
        add     ss, ss, hh
        mov     zt, ss                  // top word (was z[k])

        cmp     ii, pcode
        csel    lf, ss, lf, cc
        csel    hf, ss, hf, eq

// h = (p < BLOCKSIZE) ? z[0] << (BLOCKSIZE-p) :
//     bignum_bitfield(k+1,z,p-BLOCKSIZE,64);

        and     t0, p, #63
        neg     t1, t0

        lsr     lf, lf, t0
        lsl     hf, hf, t1

        orr     hf, hf, lf
        cmp     t0, #0
        csel    h, lf, hf, eq

//  q = multop(w,h) + h;

        umulh   t0, w, h
        add     q, t0, h

//  q = (q >> BLOCKSIZE) + 1;

        lsr     q, q, #BLOCKSIZE
        add     q, q, #1

// t = bignum_cmnegadd(k+1,z,q,k,m);
// We don't actually store the k+1 word but do the comparison to get t
// We use a more traditional carry-flag-using variant here

        mov     hh, q
        adds    ii, xzr, xzr
        cbz     k, Lbignum_mod_negaddtail2
Lbignum_mod_negaddloop2:
        ldr     tt, [m, ii, lsl #3]
        mvn     tt, tt
        mul     ll, q, tt
        umulh   mm, q, tt
        ldr     ss, [z, ii, lsl #3]
        adcs    ss, ss, hh
        adc     hh, mm, xzr
        adds    ss, ss, ll
        str     ss, [z, ii, lsl #3]
        add     ii, ii, #1
        sub     tt, ii, k
        cbnz    tt, Lbignum_mod_negaddloop2
Lbignum_mod_negaddtail2:
        mov     ss, zt                  // top word (was z[k])
        adc     ss, ss, hh
        cmp     ss, q

        csetm   mm, cc

//  bignum_optadd(k,z,z,t,m);

        cbz     k, Lbignum_mod_optaddtail
        adds    ii, xzr, xzr
Lbignum_mod_optaddloop:
        ldr     ss, [z, ii, lsl #3]
        ldr     tt, [m, ii, lsl #3]
        and     tt, tt, mm
        adcs    ss, ss, tt
        str     ss, [z, ii, lsl #3]
        add     ii, ii, #1
        sub     tt, ii, k
        cbnz    tt, Lbignum_mod_optaddloop
Lbignum_mod_optaddtail:

// Restore registers and return

Lbignum_mod_end:

        CFI_POP2(x23,x24)
        CFI_POP2(x21,x22)
        CFI_POP2(x19,x20)

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
