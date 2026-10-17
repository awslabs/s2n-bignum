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
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod)
        .text

// We get BLOCKSIZE bits per iteration

#define BLOCKSIZE 61

// x86 has far fewer registers than the ARM original, and "mul" ties up
// rdx:rax while variable shifts need cl, so bookkeeping state that is not
// on the hot path of the inner accumulation loop lives in stack slots.
// The two most-used pointers (z, m) are instead kept live in registers
// throughout; this is a leaf function so nothing else can clobber them.

#define STACKVARSIZE 72

#define kk      QWORD PTR [rsp]           // modulus size k
#define zt      QWORD PTR [rsp+8]         // shadow of the top word (was z[k])
#define nn      QWORD PTR [rsp+16]        // input size n
#define xx      QWORD PTR [rsp+24]        // input pointer x
#define mmm     QWORD PTR [rsp+32]        // modulus pointer m (also kept in r8)
#define ww      QWORD PTR [rsp+40]        // reciprocal w
#define pp      QWORD PTR [rsp+48]        // bitsize p of the modulus
#define jj      QWORD PTR [rsp+56]        // ascending bit counter j
#define hs      QWORD PTR [rsp+64]        // running high estimate h

// Live pointers held in registers throughout the body

#define z rsi
#define m r8

// Longer-term values in callee-saved registers, surviving the inner loop

#define i       rbx                        // descending bit index into x
#define l       r12                        // current word count l
#define pc      r13                        // "pcode" = (p >> 6) related index
#define lf      r14                        // low logged field word
#define hf      r15                        // high logged field word
#define q       rbp                        // quotient digit q

// Inner-loop scratch: rax, rdx (the multiply), rcx, r9 (hh), r10 (ii),
// r11 (c/funnel), and rdi as an extra counter/temporary.

S2N_BN_SYMBOL(bignum_mod):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(STACKVARSIZE)

// Stash arguments.  On entry (post-shim): rdi=k, rsi=z, rdx=n, rcx=x, r8=m.
// Keep z in rsi and m in r8 live; the rest go to slots.

        mov     kk, rdi
        mov     nn, rdx
        mov     xx, rcx
        mov     mmm, r8

// bignum_of_word(k,z,0ull);  zero the k result words z[0..k-1]. The (k+1)'th
// accumulator word that the original spilled to z[k] is now kept in "zt".

        xor     rax, rax
        mov     zt, rax                  // shadow top word starts at 0
        xor     rcx, rcx
        cmp     rcx, rdi
        je      Lbignum_mod_initdone     // k = 0: nothing to zero
Lbignum_mod_initloop:
        mov     [z+8*rcx], rax
        inc     rcx
        cmp     rcx, rdi
        jb      Lbignum_mod_initloop     // zero z[0..k-1] only, never z[k]
Lbignum_mod_initdone:

// If n = 0 do nothing

        test    rdx, rdx
        jz      Lbignum_mod_end

// p = bignum_bitsize(k,m); and the normalized top two-word window t0.
// Find top nonzero word m[dd]=hh and the word below it ll.
//   rax=hh, rdx=ll, r9=dd, r10=ss(prev), r11=ii, rcx=scratch

        xor     rax, rax                 // hh
        xor     rdx, rdx                 // ll
        xor     r9, r9                   // dd
        xor     r10, r10                 // ss
        xor     r11, r11                 // ii
        mov     rdi, kk
        test    rdi, rdi
        jz      Lbignum_mod_findertail
Lbignum_mod_finderloop:
        mov     rcx, [m+8*r11]
        test    rcx, rcx
        cmovnz  rax, rcx                  // hh = m[ii] if nonzero
        cmovnz  rdx, r10                  // ll = prev word if nonzero
        cmovnz  r9, r11                   // dd = ii if nonzero
        mov     r10, rcx                  // ss = m[ii]
        inc     r11
        cmp     r11, rdi
        jb      Lbignum_mod_finderloop
Lbignum_mod_findertail:

// tt = clz(hh) via bsr (hh nonzero since m nonzero); p = 64*dd + 64 - tt

        bsr     rcx, rax                 // rcx = index of top set bit of hh
        xor     rcx, 63                  // rcx = clz(hh) = tt
        mov     r11, r9
        shl     r11, 6                   // 64*dd
        add     r11, 64
        sub     r11, rcx                 // p = 64*dd + 64 - tt
        mov     pp, r11

// Normalize the window: hh <<= tt ; ll >>= (64-tt) ; combine; guard tt=0

        shl     rax, cl                  // hh << tt  (cl = tt)
        neg     rcx                      // 64 - tt (mod 64)
        shr     rdx, cl                  // ll >> (64-tt)
        or      rdx, rax
        neg     rcx                      // restore tt
        test    rcx, rcx
        cmovz   rdx, rax                 // if tt=0 use hh alone; rdx = t0

// w = word_recip((t0 + 1 == 0) ? t0 : t0 + 1);  inlined word_recip.
// Input word (top bit set) in rdx; adjusted value in r11 = a; result in r9.

        mov     rax, rdx
        add     rax, 1
        cmovc   rax, rdx
        mov     r11, rax                 // a

        mov     rbx, r11                 // b     (rbx = i not yet live)
        mov     r9, 0x1FFFFFFFFFFFF      // x
        shr     rbx, 16
        xor     r9, rbx
        inc     rbx
        shr     r9, 32
        mov     rdx, rbx
        imul    rdx, r9
        neg     rdx
        mov     rax, rdx
        shr     rax, 49
        imul    rax, rax
        shr     rdx, 34
        add     rdx, rax
        or      rax, 0x40000000
        imul    rax, rdx
        shr     rax, 30
        imul    rax, r9
        shl     r9, 30
        add     r9, rax
        shr     r9, 30
        mov     rdx, rbx
        imul    rdx, r9
        neg     rdx
        shr     rdx, 24
        imul    rdx, r9
        shl     r9, 16
        shr     rdx, 24
        add     r9, rdx
        mov     rdx, rbx
        imul    rdx, r9
        neg     rdx
        shr     rdx, 32
        imul    rdx, r9
        shl     r9, 31
        shr     rdx, 17
        add     r9, rdx
        mov     rax, r11
        mul     r9
        shrd    rax, rdx, 60
        mov     rdx, r9
        shr     rdx, 33
        not     rax
        imul    rax, rdx
        shl     r9, 1
        shr     rax, 33
        add     r9, rax
        add     r9, 1
        mov     rax, r11
        sbb     r9, 0
        mul     r9
        add     rdx, r11
        sbb     r9, 0                    // r9 = w
        mov     ww, r9

// i = BLOCKSIZE * ((64 * n + BLOCKSIZE - 1) / BLOCKSIZE - 1);
//  n < 2^60 ==> (64*n) DIV 61 = (0xc9714fbcda3ac11 * n) DIV 2^64 + n

        mov     rax, 0xc9714fbcda3ac11
        mov     r11, nn
        mul     r11
        add     rdx, r11                 // (64*n)/61
        imul    rdx, rdx, BLOCKSIZE      // 61 * ((64*n)/61)
        lea     rax, [rdx-BLOCKSIZE]     // that minus 61
        test    rdx, 63
        cmovnz  rax, rdx
        mov     i, rax                   // i

// j = BLOCKSIZE

        mov     jj, BLOCKSIZE

// l = word_min(k+1,(j+63)/64);

        mov     rdi, kk
        lea     rax, [rdi+1]             // k+1
        mov     rdx, BLOCKSIZE+63
        shr     rdx, 6                   // (j+63)/64
        cmp     rax, rdx
        cmovnc  rax, rdx
        mov     l, rax                   // l

// c = bignum_bitfield(n,x,i,BLOCKSIZE);  within top word x[n-1] by choice of i

        mov     rdi, xx
        mov     r11, nn
        dec     r11
        mov     r11, [rdi+8*r11]         // x[n-1]
        mov     rcx, i
        shr     r11, cl                  // c = x[n-1] >> i  (r11 = c)

// z[0] = c

        mov     [z], r11

// h = (p < 64) ? (c>>p) : 0;

        mov     rcx, pp
        mov     rax, r11                 // c
        xor     edx, edx                 // 0, for the p >= 64 case
        shr     rax, cl                  // c >> p
        cmp     rcx, 64
        cmovnc  rax, rdx                 // if p >= 64, h = 0
        mov     hs, rax                  // h

// pc = (p >> 6) + 1

        mov     pc, pp
        shr     pc, 6
        inc     pc

// *** BEGINNING OF MAIN LOOP ***

Lbignum_mod_loop:

// i -= BLOCKSIZE;  c = bitfield(n,x,i,BLOCKSIZE) via two-word funnel.
// The upper word index is clamped to n - 1 so as not to read past x;
// when that happens its bits are not part of the field anyway.

        sub     i, BLOCKSIZE

        mov     rdi, xx
        mov     rax, i
        shr     rax, 6                   // word offset
        mov     rcx, i
        and     rcx, 63                  // shift s = i & 63
        mov     r10, [rdi+8*rax]         // lo = x[off]
        lea     rdx, [rax+1]
        cmp     rdx, nn
        cmovnc  rdx, rax                 // min(off+1,n-1), as off < n
        mov     r11, [rdi+8*rdx]         // hi = x[min(off+1,n-1)]
        shrd    r10, r11, cl             // (lo>>s)|(hi<<(64-s)); s=0 -> lo
        mov     r11, r10                 // c = block (top garbage masked on use)

// q = multop(w,h) + h;  (multop = high 64 of w*h)

        mov     rax, ww
        mul     hs                       // rdx:rax = w * h
        mov     q, rdx
        add     q, hs                    // q = hi(w*h) + h

// z := (z << BLOCKSIZE) - q*m + c, done as z + q*(~m) + q + c, fused with the
// shl_small funnel (via shrd) and logging of the field around bit p.

        xor     hf, hf                   // hf = 0
        shl     r11, (64-BLOCKSIZE)      // c <<= (64-BLOCKSIZE)
        mov     r9, q                    // hh = q
        xor     r10, r10                 // ii = 0

        mov     rdi, l
        dec     rdi                      // dd = l - 1
        jz      Lbignum_mod_trivnegadd

Lbignum_mod_innerloop:
        mov     rax, [m+8*r10]
        not     rax                      // ~m[ii]
        mul     q                        // rdx:rax = q * ~m[ii]  (ll=rax, mm=rdx)
        mov     rcx, [z+8*r10]           // ss = z[ii]
        add     rcx, r9                  // ss += hh   (CF1)
        mov     r9, rdx                  // hh = mm
        adc     r9, 0                    // hh = mm + CF1
        add     rcx, rax                 // ss += ll   (CF2)
        adc     r9, 0                    // hh = mm + CF1 + CF2
        shrd    r11, rcx, (64-BLOCKSIZE) // c = extr(ss, c, 64-BLOCKSIZE)
        mov     [z+8*r10], r11           // z[ii] = c
        cmp     r10, pc
        cmovb   lf, r11                  // ii < pcode -> lf = c
        cmove   hf, r11                  // ii == pcode -> hf = c
        mov     r11, rcx                 // c = ss
        inc     r10
        cmp     r10, rdi
        jne     Lbignum_mod_innerloop

// Last iteration: may be at ii = k (don't load m), and no high propagation

Lbignum_mod_trivnegadd:
        xor     eax, eax                 // tt = 0
        lea     rdi, [z+8*r10]           // &z[ii]
        lea     rdx, zt                  // &zt (shadow top word)
        cmp     r10, kk
        cmove   rdi, rdx                 // ii == k ? &zt : &z[ii]
        je      Lbignum_mod_offendm      // ii == k: no m[k], tt stays 0
        mov     rax, [m+8*r10]           // tt = m[ii]
Lbignum_mod_offendm:
        not     rax
        mul     q                        // rax = lo(q * ~tt); rdx (=&zt) now dead
        mov     rcx, [rdi]               // ss = *(z[ii] or zt)
        add     rcx, r9                  // ss += hh
        add     rcx, rax                 // ss += ll
        shrd    r11, rcx, (64-BLOCKSIZE) // c = extr(ss, c, 64-BLOCKSIZE)
        mov     [rdi], r11               // store c to z[ii] or zt
        cmp     r10, pc
        cmovb   lf, r11
        cmove   hf, r11
        inc     r10

// j += BLOCKSIZE;  l' = word_min(k+1,(j+63)/64);

        mov     rax, jj
        add     rax, BLOCKSIZE
        mov     jj, rax                  // j += BLOCKSIZE
        mov     rdi, kk
        lea     rdi, [rdi+1]             // k+1
        add     rax, 63
        shr     rax, 6                   // (j+63)/64
        cmp     rdi, rax
        cmovnc  rdi, rax
        mov     l, rdi                   // l = min(k+1,(j+63)/64)

// Turn into bignum_shl_small(l',z,l,z,BLOCKSIZE): if ii != l store one more

        cmp     r10, l
        je      Lbignum_mod_noel
        mov     rax, rcx                 // ss
        shr     rax, (64-BLOCKSIZE)      // ss >> (64-BLOCKSIZE)
        mov     r11, rax                 // c = ss >> (64-BLOCKSIZE)
        lea     rax, [z+8*r10]           // &z[ii]
        lea     rdi, zt                  // &zt
        cmp     r10, kk
        cmove   rax, rdi                 // ii == k ? &zt : &z[ii]
        mov     [rax], r11
        cmp     r10, pc
        cmovb   lf, r11
        cmove   hf, r11
        inc     r10
Lbignum_mod_noel:

// Field selection tidy-up: lf meaningful only if pcode <= ii+1
//   ii < pcode -> lf = 0 ; ii == pcode -> lf = c ; ii > pcode -> lf unchanged

        xor     eax, eax
        cmp     r10, pc
        cmovb   lf, rax
        cmove   lf, r11

// h = combine(hf,lf) around bit p:  t0 = p & 63
//   lf >>= t0 ; hf <<= (64 - t0) ; h = (t0==0) ? lf : (hf | lf)

        mov     rcx, pp
        and     rcx, 63                  // t0
        mov     r11, rcx                 // keep t0 (neg below clobbers rcx)
        mov     rax, lf
        shr     rax, cl                  // lf >> t0
        mov     rdx, hf
        neg     rcx                      // 64 - t0
        shl     rdx, cl                  // hf << (64-t0)
        or      rdx, rax                 // hf | lf
        test    r11, r11
        cmovz   rdx, rax                 // if t0==0, h = lf
        mov     hs, rdx                  // h

        test    i, i
        jnz     Lbignum_mod_loop

// *** END OF MAIN LOOP ***

// q = multop(w,h) + h;

        mov     rax, ww
        mul     hs
        mov     q, rdx
        add     q, hs

// bignum_cmnegadd(l,z,q,k,m); l = k+1 here.  Fold logging with a variant
// pcode (1 less than before); since last usage, bump p to p + BLOCKSIZE.

        mov     r9, q                    // hh = q
        xor     r10, r10                 // ii = 0
        mov     r11, pp
        add     r11, (64-BLOCKSIZE)      // p += (64 - BLOCKSIZE)
        mov     pp, r11
        shr     r11, 6
        mov     pc, r11                  // pcode = p >> 6
        xor     lf, lf
        xor     hf, hf

        mov     rdi, kk
        test    rdi, rdi
        jz      Lbignum_mod_negaddtail1
Lbignum_mod_negaddloop1:
        mov     rax, [m+8*r10]
        not     rax
        mul     q                        // rdx:rax = q * ~m[ii]
        mov     rcx, [z+8*r10]           // ss = z[ii]
        add     rcx, r9                  // ss += hh (CF1)
        mov     r9, rdx
        adc     r9, 0                    // hh = mm + CF1
        add     rcx, rax                 // ss += ll (CF2)
        adc     r9, 0                    // hh = mm + CF1 + CF2
        mov     [z+8*r10], rcx           // z[ii] = ss
        cmp     r10, pc
        cmovb   lf, rcx
        cmove   hf, rcx
        inc     r10
        cmp     r10, kk
        jne     Lbignum_mod_negaddloop1
Lbignum_mod_negaddtail1:
        sub     r9, q                    // hh -= q
        mov     rcx, zt                  // top word (was z[k])
        add     rcx, r9
        mov     zt, rcx                  // top word (was z[k])
        cmp     r10, pc
        cmovb   lf, rcx
        cmove   hf, rcx

// h = combine(hf,lf) around bit p:  t0 = p & 63

        mov     rcx, pp
        and     rcx, 63
        mov     r11, rcx                 // keep t0 (neg below clobbers rcx)
        mov     rax, lf
        shr     rax, cl
        mov     rdx, hf
        neg     rcx
        shl     rdx, cl
        or      rdx, rax
        test    r11, r11
        cmovz   rdx, rax
        mov     hs, rdx                  // h

// q = multop(w,h) + h;  then q = (q >> BLOCKSIZE) + 1;

        mov     rax, ww
        mul     hs
        mov     q, rdx
        add     q, hs
        shr     q, BLOCKSIZE
        add     q, 1

// t = bignum_cmnegadd(k+1,z,q,k,m); carry-flag variant, computing t via the
// top comparison.  We don't store the (k+1)'th word but do compare.
//
// Two carries interleave here, exactly as in the ARM original: the running
// high word hh (held in r9), and the low-add carry that must pass between
// iterations.  Since x86 loop control (inc/cmp) clobbers CF, we hold that
// carry explicitly in a mask register cy = rdi (0 or -1) and re-inject it.

        mov     r9, q                    // hh = q
        xor     r10, r10                 // ii = 0
        xor     edi, edi                 // cy = 0 (low-add carry mask)
        mov     rax, kk
        test    rax, rax
        jz      Lbignum_mod_negaddtail2
Lbignum_mod_negaddloop2:
        mov     rax, [m+8*r10]
        not     rax
        mul     q                        // rdx:rax = q * ~m[ii]  (ll=rax, mm=rdx)
        neg     rdi                      // rdi = cy as 0/1 (CF = 0 after)
        mov     rcx, [z+8*r10]           // ss = z[ii]
        adc     rcx, r9                  // ss = z[ii] + hh + cy   (CF captured)
        mov     r9, rdx                  // hh = mm
        adc     r9, 0                    // hh = mm + carry_from(z+hh+cy)
        add     rcx, rax                 // ss += ll ; CF is the carry to keep
        sbb     rdi, rdi                 // cy = -CF (mask) for next iteration
        mov     [z+8*r10], rcx
        inc     r10
        cmp     r10, kk
        jne     Lbignum_mod_negaddloop2
Lbignum_mod_negaddtail2:
        neg     rdi                      // CF = cy bit
        mov     rcx, zt                  // top word (was z[k])
        adc     rcx, r9                  // ss = top + hh + cy
        cmp     rcx, q
        sbb     r9, r9                   // r9 = mask t = (top < q) ? -1 : 0

// bignum_optadd(k,z,z,t,m); if t (mask) set, add m back into z[0..k-1].
// Carry held explicitly in cy = rdi mask across the loop control.

        xor     r10, r10                 // ii = 0
        xor     edi, edi                 // cy = 0
        mov     rax, kk
        test    rax, rax
        jz      Lbignum_mod_optaddtail
Lbignum_mod_optaddloop:
        mov     rcx, [z+8*r10]
        mov     rax, [m+8*r10]
        and     rax, r9                  // m[ii] & mask  (also clears CF)
        neg     rdi                      // CF = cy (rdi was 0 or -1 mask)
        adc     rcx, rax                 // ss = z[ii] + (m&mask) + cy
        sbb     rdi, rdi                 // cy = -CF for next iteration
        mov     [z+8*r10], rcx
        inc     r10
        cmp     r10, kk
        jne     Lbignum_mod_optaddloop
Lbignum_mod_optaddtail:

Lbignum_mod_end:
        CFI_INC_RSP(STACKVARSIZE)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
