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

#include "_internal_s2n_bignum_x86_att.h"

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

#define kk      (%rsp)                  // modulus size k
#define zt      8(%rsp)                 // shadow of the top word (was z[k])
#define nn      16(%rsp)                // input size n
#define xx      24(%rsp)                // input pointer x
#define mmm     32(%rsp)                // modulus pointer m (also kept in r8)
#define ww      40(%rsp)                // reciprocal w
#define pp      48(%rsp)                // bitsize p of the modulus
#define jj      56(%rsp)                // ascending bit counter j
#define hs      64(%rsp)                // running high estimate h

// Live pointers held in registers throughout the body

#define z %rsi
#define m %r8

// Longer-term values in callee-saved registers, surviving the inner loop

#define i       %rbx                    // descending bit index into x
#define l       %r12                    // current word count l
#define pc      %r13                    // "pcode" = (p >> 6) related index
#define lf      %r14                    // low logged field word
#define hf      %r15                    // high logged field word
#define q       %rbp                    // quotient digit q

// Inner-loop scratch: rax, rdx (the multiply), rcx, r9 (hh), r10 (ii),
// r11 (c/funnel), and rdi as an extra counter/temporary.

S2N_BN_SYMBOL(bignum_mod):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(%rdi)
        CFI_PUSH(%rsi)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
        movq    56(%rsp), %r8
#endif

        CFI_PUSH(%rbx)
        CFI_PUSH(%rbp)
        CFI_PUSH(%r12)
        CFI_PUSH(%r13)
        CFI_PUSH(%r14)
        CFI_PUSH(%r15)
        CFI_DEC_RSP(STACKVARSIZE)

// Stash arguments.  On entry (post-shim): rdi=k, rsi=z, rdx=n, rcx=x, r8=m.
// Keep z in rsi and m in r8 live; the rest go to slots.

        movq    %rdi, kk
        movq    %rdx, nn
        movq    %rcx, xx
        movq    %r8, mmm

// bignum_of_word(k,z,0ull);  zero the k result words z[0..k-1]. The (k+1)'th
// accumulator word that the original spilled to z[k] is now kept in "zt".

        xorq    %rax, %rax
        movq    %rax, zt                // shadow top word starts at 0
        xorq    %rcx, %rcx
        cmpq    %rdi, %rcx
        je      Lbignum_mod_initdone    // k = 0: nothing to zero
Lbignum_mod_initloop:
        movq    %rax, (z,%rcx,8)
        incq    %rcx
        cmpq    %rdi, %rcx
        jb      Lbignum_mod_initloop    // zero z[0..k-1] only, never z[k]
Lbignum_mod_initdone:

// If n = 0 do nothing

        testq   %rdx, %rdx
        jz      Lbignum_mod_end

// p = bignum_bitsize(k,m); and the normalized top two-word window t0.
// Find top nonzero word m[dd]=hh and the word below it ll.
//   rax=hh, rdx=ll, r9=dd, r10=ss(prev), r11=ii, rcx=scratch

        xorq    %rax, %rax              // hh
        xorq    %rdx, %rdx              // ll
        xorq    %r9, %r9                // dd
        xorq    %r10, %r10              // ss
        xorq    %r11, %r11              // ii
        movq    kk, %rdi
        testq   %rdi, %rdi
        jz      Lbignum_mod_findertail
Lbignum_mod_finderloop:
        movq    (m,%r11,8), %rcx
        testq   %rcx, %rcx
        cmovnzq %rcx, %rax              // hh = m[ii] if nonzero
        cmovnzq %r10, %rdx              // ll = prev word if nonzero
        cmovnzq %r11, %r9               // dd = ii if nonzero
        movq    %rcx, %r10              // ss = m[ii]
        incq    %r11
        cmpq    %rdi, %r11
        jb      Lbignum_mod_finderloop
Lbignum_mod_findertail:

// tt = clz(hh) via bsr (hh nonzero since m nonzero); p = 64*dd + 64 - tt

        bsrq    %rax, %rcx              // rcx = index of top set bit of hh
        xorq    $63, %rcx               // rcx = clz(hh) = tt
        movq    %r9, %r11
        shlq    $6, %r11                // 64*dd
        addq    $64, %r11
        subq    %rcx, %r11              // p = 64*dd + 64 - tt
        movq    %r11, pp

// Normalize the window: hh <<= tt ; ll >>= (64-tt) ; combine; guard tt=0

        shlq    %cl, %rax               // hh << tt  (cl = tt)
        negq    %rcx                    // 64 - tt (mod 64)
        shrq    %cl, %rdx               // ll >> (64-tt)
        orq     %rax, %rdx
        negq    %rcx                    // restore tt
        testq   %rcx, %rcx
        cmovzq  %rax, %rdx              // if tt=0 use hh alone; rdx = t0

// w = word_recip((t0 + 1 == 0) ? t0 : t0 + 1);  inlined word_recip.
// Input word (top bit set) in rdx; adjusted value in r11 = a; result in r9.

        movq    %rdx, %rax
        addq    $1, %rax
        cmovcq  %rdx, %rax
        movq    %rax, %r11              // a

        movq    %r11, %rbx              // b     (rbx = i not yet live)
        movq    $0x1FFFFFFFFFFFF, %r9   // x
        shrq    $16, %rbx
        xorq    %rbx, %r9
        incq    %rbx
        shrq    $32, %r9
        movq    %rbx, %rdx
        imulq   %r9, %rdx
        negq    %rdx
        movq    %rdx, %rax
        shrq    $49, %rax
        imulq   %rax, %rax
        shrq    $34, %rdx
        addq    %rax, %rdx
        orq     $0x40000000, %rax
        imulq   %rdx, %rax
        shrq    $30, %rax
        imulq   %r9, %rax
        shlq    $30, %r9
        addq    %rax, %r9
        shrq    $30, %r9
        movq    %rbx, %rdx
        imulq   %r9, %rdx
        negq    %rdx
        shrq    $24, %rdx
        imulq   %r9, %rdx
        shlq    $16, %r9
        shrq    $24, %rdx
        addq    %rdx, %r9
        movq    %rbx, %rdx
        imulq   %r9, %rdx
        negq    %rdx
        shrq    $32, %rdx
        imulq   %r9, %rdx
        shlq    $31, %r9
        shrq    $17, %rdx
        addq    %rdx, %r9
        movq    %r11, %rax
        mulq    %r9
        shrdq   $60, %rdx, %rax
        movq    %r9, %rdx
        shrq    $33, %rdx
        notq    %rax
        imulq   %rdx, %rax
        shlq    $1, %r9
        shrq    $33, %rax
        addq    %rax, %r9
        addq    $1, %r9
        movq    %r11, %rax
        sbbq    $0, %r9
        mulq    %r9
        addq    %r11, %rdx
        sbbq    $0, %r9                 // r9 = w
        movq    %r9, ww

// i = BLOCKSIZE * ((64 * n + BLOCKSIZE - 1) / BLOCKSIZE - 1);
//  n < 2^60 ==> (64*n) DIV 61 = (0xc9714fbcda3ac11 * n) DIV 2^64 + n

        movq    $0xc9714fbcda3ac11, %rax
        movq    nn, %r11
        mulq    %r11
        addq    %r11, %rdx              // (64*n)/61
        imulq   $BLOCKSIZE, %rdx, %rdx  // 61 * ((64*n)/61)
        leaq    -(BLOCKSIZE)(%rdx), %rax // that minus 61
        testq   $63, %rdx
        cmovnzq %rdx, %rax
        movq    %rax, i                 // i

// j = BLOCKSIZE

        movq    $BLOCKSIZE, jj

// l = word_min(k+1,(j+63)/64);

        movq    kk, %rdi
        leaq    1(%rdi), %rax           // k+1
        movq    $BLOCKSIZE + 63, %rdx
        shrq    $6, %rdx                // (j+63)/64
        cmpq    %rdx, %rax
        cmovncq %rdx, %rax
        movq    %rax, l                 // l

// c = bignum_bitfield(n,x,i,BLOCKSIZE);  within top word x[n-1] by choice of i

        movq    xx, %rdi
        movq    nn, %r11
        decq    %r11
        movq    (%rdi,%r11,8), %r11     // x[n-1]
        movq    i, %rcx
        shrq    %cl, %r11               // c = x[n-1] >> i  (r11 = c)

// z[0] = c

        movq    %r11, (z)

// h = (p < 64) ? (c>>p) : 0;

        movq    pp, %rcx
        movq    %r11, %rax              // c
        xorl    %edx, %edx              // 0, for the p >= 64 case
        shrq    %cl, %rax               // c >> p
        cmpq    $64, %rcx
        cmovncq %rdx, %rax              // if p >= 64, h = 0
        movq    %rax, hs                // h

// pc = (p >> 6) + 1

        movq    pp, pc
        shrq    $6, pc
        incq    pc

// *** BEGINNING OF MAIN LOOP ***

Lbignum_mod_loop:

// i -= BLOCKSIZE;  c = bitfield(n,x,i,BLOCKSIZE) via two-word funnel.
// The upper word index is clamped to n - 1 so as not to read past x;
// when that happens its bits are not part of the field anyway.

        subq    $BLOCKSIZE, i

        movq    xx, %rdi
        movq    i, %rax
        shrq    $6, %rax                // word offset
        movq    i, %rcx
        andq    $63, %rcx               // shift s = i & 63
        movq    (%rdi,%rax,8), %r10     // lo = x[off]
        leaq    1(%rax), %rdx
        cmpq    nn, %rdx
        cmovncq %rax, %rdx              // min(off+1,n-1), as off < n
        movq    (%rdi,%rdx,8), %r11     // hi = x[min(off+1,n-1)]
        shrdq   %cl, %r11, %r10         // (lo>>s)|(hi<<(64-s)); s=0 -> lo
        movq    %r10, %r11              // c = block (top garbage masked on use)

// q = multop(w,h) + h;  (multop = high 64 of w*h)

        movq    ww, %rax
        mulq    hs                      // rdx:rax = w * h
        movq    %rdx, q
        addq    hs, q                   // q = hi(w*h) + h

// z := (z << BLOCKSIZE) - q*m + c, done as z + q*(~m) + q + c, fused with the
// shl_small funnel (via shrd) and logging of the field around bit p.

        xorq    hf, hf                  // hf = 0
        shlq    $(64 - BLOCKSIZE), %r11 // c <<= (64-BLOCKSIZE)
        movq    q, %r9                  // hh = q
        xorq    %r10, %r10              // ii = 0

        movq    l, %rdi
        decq    %rdi                    // dd = l - 1
        jz      Lbignum_mod_trivnegadd

Lbignum_mod_innerloop:
        movq    (m,%r10,8), %rax
        notq    %rax                    // ~m[ii]
        mulq    q                       // rdx:rax = q * ~m[ii]  (ll=rax, mm=rdx)
        movq    (z,%r10,8), %rcx        // ss = z[ii]
        addq    %r9, %rcx               // ss += hh   (CF1)
        movq    %rdx, %r9               // hh = mm
        adcq    $0, %r9                 // hh = mm + CF1
        addq    %rax, %rcx              // ss += ll   (CF2)
        adcq    $0, %r9                 // hh = mm + CF1 + CF2
        shrdq   $(64 - BLOCKSIZE), %rcx, %r11 // c = extr(ss, c, 64-BLOCKSIZE)
        movq    %r11, (z,%r10,8)        // z[ii] = c
        cmpq    pc, %r10
        cmovbq  %r11, lf                // ii < pcode -> lf = c
        cmoveq  %r11, hf                // ii == pcode -> hf = c
        movq    %rcx, %r11              // c = ss
        incq    %r10
        cmpq    %rdi, %r10
        jne     Lbignum_mod_innerloop

// Last iteration: may be at ii = k (don't load m), and no high propagation

Lbignum_mod_trivnegadd:
        xorl    %eax, %eax              // tt = 0
        leaq    (z,%r10,8), %rdi        // &z[ii]
        leaq    zt, %rdx                // &zt (shadow top word)
        cmpq    kk, %r10
        cmoveq  %rdx, %rdi              // ii == k ? &zt : &z[ii]
        je      Lbignum_mod_offendm     // ii == k: no m[k], tt stays 0
        movq    (m,%r10,8), %rax        // tt = m[ii]
Lbignum_mod_offendm:
        notq    %rax
        mulq    q                       // rax = lo(q * ~tt); rdx (=&zt) now dead
        movq    (%rdi), %rcx            // ss = *(z[ii] or zt)
        addq    %r9, %rcx               // ss += hh
        addq    %rax, %rcx              // ss += ll
        shrdq   $(64 - BLOCKSIZE), %rcx, %r11 // c = extr(ss, c, 64-BLOCKSIZE)
        movq    %r11, (%rdi)            // store c to z[ii] or zt
        cmpq    pc, %r10
        cmovbq  %r11, lf
        cmoveq  %r11, hf
        incq    %r10

// j += BLOCKSIZE;  l' = word_min(k+1,(j+63)/64);

        movq    jj, %rax
        addq    $BLOCKSIZE, %rax
        movq    %rax, jj                // j += BLOCKSIZE
        movq    kk, %rdi
        leaq    1(%rdi), %rdi           // k+1
        addq    $63, %rax
        shrq    $6, %rax                // (j+63)/64
        cmpq    %rax, %rdi
        cmovncq %rax, %rdi
        movq    %rdi, l                 // l = min(k+1,(j+63)/64)

// Turn into bignum_shl_small(l',z,l,z,BLOCKSIZE): if ii != l store one more

        cmpq    l, %r10
        je      Lbignum_mod_noel
        movq    %rcx, %rax              // ss
        shrq    $(64 - BLOCKSIZE), %rax // ss >> (64-BLOCKSIZE)
        movq    %rax, %r11              // c = ss >> (64-BLOCKSIZE)
        leaq    (z,%r10,8), %rax        // &z[ii]
        leaq    zt, %rdi                // &zt
        cmpq    kk, %r10
        cmoveq  %rdi, %rax              // ii == k ? &zt : &z[ii]
        movq    %r11, (%rax)
        cmpq    pc, %r10
        cmovbq  %r11, lf
        cmoveq  %r11, hf
        incq    %r10
Lbignum_mod_noel:

// Field selection tidy-up: lf meaningful only if pcode <= ii+1
//   ii < pcode -> lf = 0 ; ii == pcode -> lf = c ; ii > pcode -> lf unchanged

        xorl    %eax, %eax
        cmpq    pc, %r10
        cmovbq  %rax, lf
        cmoveq  %r11, lf

// h = combine(hf,lf) around bit p:  t0 = p & 63
//   lf >>= t0 ; hf <<= (64 - t0) ; h = (t0==0) ? lf : (hf | lf)

        movq    pp, %rcx
        andq    $63, %rcx               // t0
        movq    %rcx, %r11              // keep t0 (neg below clobbers rcx)
        movq    lf, %rax
        shrq    %cl, %rax               // lf >> t0
        movq    hf, %rdx
        negq    %rcx                    // 64 - t0
        shlq    %cl, %rdx               // hf << (64-t0)
        orq     %rax, %rdx              // hf | lf
        testq   %r11, %r11
        cmovzq  %rax, %rdx              // if t0==0, h = lf
        movq    %rdx, hs                // h

        testq   i, i
        jnz     Lbignum_mod_loop

// *** END OF MAIN LOOP ***

// q = multop(w,h) + h;

        movq    ww, %rax
        mulq    hs
        movq    %rdx, q
        addq    hs, q

// bignum_cmnegadd(l,z,q,k,m); l = k+1 here.  Fold logging with a variant
// pcode (1 less than before); since last usage, bump p to p + BLOCKSIZE.

        movq    q, %r9                  // hh = q
        xorq    %r10, %r10              // ii = 0
        movq    pp, %r11
        addq    $(64 - BLOCKSIZE), %r11 // p += (64 - BLOCKSIZE)
        movq    %r11, pp
        shrq    $6, %r11
        movq    %r11, pc                // pcode = p >> 6
        xorq    lf, lf
        xorq    hf, hf

        movq    kk, %rdi
        testq   %rdi, %rdi
        jz      Lbignum_mod_negaddtail1
Lbignum_mod_negaddloop1:
        movq    (m,%r10,8), %rax
        notq    %rax
        mulq    q                       // rdx:rax = q * ~m[ii]
        movq    (z,%r10,8), %rcx        // ss = z[ii]
        addq    %r9, %rcx               // ss += hh (CF1)
        movq    %rdx, %r9
        adcq    $0, %r9                 // hh = mm + CF1
        addq    %rax, %rcx              // ss += ll (CF2)
        adcq    $0, %r9                 // hh = mm + CF1 + CF2
        movq    %rcx, (z,%r10,8)        // z[ii] = ss
        cmpq    pc, %r10
        cmovbq  %rcx, lf
        cmoveq  %rcx, hf
        incq    %r10
        cmpq    kk, %r10
        jne     Lbignum_mod_negaddloop1
Lbignum_mod_negaddtail1:
        subq    q, %r9                  // hh -= q
        movq    zt, %rcx                // top word (was z[k])
        addq    %r9, %rcx
        movq    %rcx, zt                // top word (was z[k])
        cmpq    pc, %r10
        cmovbq  %rcx, lf
        cmoveq  %rcx, hf

// h = combine(hf,lf) around bit p:  t0 = p & 63

        movq    pp, %rcx
        andq    $63, %rcx
        movq    %rcx, %r11              // keep t0 (neg below clobbers rcx)
        movq    lf, %rax
        shrq    %cl, %rax
        movq    hf, %rdx
        negq    %rcx
        shlq    %cl, %rdx
        orq     %rax, %rdx
        testq   %r11, %r11
        cmovzq  %rax, %rdx
        movq    %rdx, hs                // h

// q = multop(w,h) + h;  then q = (q >> BLOCKSIZE) + 1;

        movq    ww, %rax
        mulq    hs
        movq    %rdx, q
        addq    hs, q
        shrq    $BLOCKSIZE, q
        addq    $1, q

// t = bignum_cmnegadd(k+1,z,q,k,m); carry-flag variant, computing t via the
// top comparison.  We don't store the (k+1)'th word but do compare.
//
// Two carries interleave here, exactly as in the ARM original: the running
// high word hh (held in r9), and the low-add carry that must pass between
// iterations.  Since x86 loop control (inc/cmp) clobbers CF, we hold that
// carry explicitly in a mask register cy = rdi (0 or -1) and re-inject it.

        movq    q, %r9                  // hh = q
        xorq    %r10, %r10              // ii = 0
        xorl    %edi, %edi              // cy = 0 (low-add carry mask)
        movq    kk, %rax
        testq   %rax, %rax
        jz      Lbignum_mod_negaddtail2
Lbignum_mod_negaddloop2:
        movq    (m,%r10,8), %rax
        notq    %rax
        mulq    q                       // rdx:rax = q * ~m[ii]  (ll=rax, mm=rdx)
        negq    %rdi                    // rdi = cy as 0/1 (CF = 0 after)
        movq    (z,%r10,8), %rcx        // ss = z[ii]
        adcq    %r9, %rcx               // ss = z[ii] + hh + cy   (CF captured)
        movq    %rdx, %r9               // hh = mm
        adcq    $0, %r9                 // hh = mm + carry_from(z+hh+cy)
        addq    %rax, %rcx              // ss += ll ; CF is the carry to keep
        sbbq    %rdi, %rdi              // cy = -CF (mask) for next iteration
        movq    %rcx, (z,%r10,8)
        incq    %r10
        cmpq    kk, %r10
        jne     Lbignum_mod_negaddloop2
Lbignum_mod_negaddtail2:
        negq    %rdi                    // CF = cy bit
        movq    zt, %rcx                // top word (was z[k])
        adcq    %r9, %rcx               // ss = top + hh + cy
        cmpq    q, %rcx
        sbbq    %r9, %r9                // r9 = mask t = (top < q) ? -1 : 0

// bignum_optadd(k,z,z,t,m); if t (mask) set, add m back into z[0..k-1].
// Carry held explicitly in cy = rdi mask across the loop control.

        xorq    %r10, %r10              // ii = 0
        xorl    %edi, %edi              // cy = 0
        movq    kk, %rax
        testq   %rax, %rax
        jz      Lbignum_mod_optaddtail
Lbignum_mod_optaddloop:
        movq    (z,%r10,8), %rcx
        movq    (m,%r10,8), %rax
        andq    %r9, %rax               // m[ii] & mask  (also clears CF)
        negq    %rdi                    // CF = cy (rdi was 0 or -1 mask)
        adcq    %rax, %rcx              // ss = z[ii] + (m&mask) + cy
        sbbq    %rdi, %rdi              // cy = -CF for next iteration
        movq    %rcx, (z,%r10,8)
        incq    %r10
        cmpq    kk, %r10
        jne     Lbignum_mod_optaddloop
Lbignum_mod_optaddtail:

Lbignum_mod_end:
        CFI_INC_RSP(STACKVARSIZE)
        CFI_POP(%r15)
        CFI_POP(%r14)
        CFI_POP(%r13)
        CFI_POP(%r12)
        CFI_POP(%rbp)
        CFI_POP(%rbx)
#if WINDOWS_ABI
        CFI_POP(%rsi)
        CFI_POP(%rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
