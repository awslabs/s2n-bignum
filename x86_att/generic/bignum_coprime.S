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
// Test bignums for coprimality, gcd(x,y) = 1
// Inputs x[m], y[n]; output function return; temporary buffer t[>=2*max(m,n)]
//
//    extern uint64_t bignum_coprime
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y, uint64_t *t);
//
// Test for whether two bignums are coprime (no common factor besides 1).
// This is equivalent to testing if their gcd is 1, but a bit faster than
// doing those two computations separately.
//
// Here bignum x is m digits long, y is n digits long and the temporary
// buffer t needs to be 2 * max(m,n) digits long. The return value is
// 1 if coprime(x,y) and 0 otherwise.
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, R8 = t, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_coprime
        .text

// We get CHUNKSIZE bits per outer iteration, 64 minus a bit for proxy errors

#define CHUNKSIZE 58

// These variables are so fundamental we keep them consistently in registers.
// m is in fact the temporary buffer argument w so use the same register

#define m %r8
#define n %r15
#define k %r14
#define l %r13

// These are kept on the stack since there aren't enough registers

#define mat_mm      (%rsp)
#define mat_mn      8(%rsp)
#define mat_nm      16(%rsp)
#define mat_nn      24(%rsp)
#define t           32(%rsp)
#define evenor      40(%rsp)

#define STACKVARSIZE 48

// These are shorthands for common temporary register

#define a %rax
#define b %rbx
#define c %rcx
#define d %rdx
#define i %r9

// Temporaries for the top proxy selection part

#define c1        %r10
#define c2        %r11
#define h1        %r12
#define h2        %rbp
#define l1        %rdi
#define l2        %rsi

// Re-use for the actual proxies; m_hi = h1 and n_hi = h2 are assumed

#define m_hi    %r12
#define n_hi    %rbp
#define m_lo    %rdi
#define n_lo    %rsi

// Re-use for the matrix entries in the inner loop, though they
// get spilled to the corresponding memory locations mat_...

#define m_m     %r10
#define m_n     %r11
#define n_m     %rcx
#define n_n     %rdx

#define ishort   %r9d
#define m_mshort %r10d
#define m_nshort %r11d
#define n_mshort %ecx
#define n_nshort %edx

// Because they are so unmemorable

#define arg1 %rdi
#define arg2 %rsi
#define arg3 %rdx
#define arg4 %rcx

bignum_coprime:

// Save all required registers and make room on stack for all the above vars

                pushq   %rbp
                pushq   %rbx
                pushq   %r12
                pushq   %r13
                pushq   %r14
                pushq   %r15
                subq    $STACKVARSIZE, %rsp

// Compute k = max(m,n), and if this is zero skip to the end. Note that
// in this case k is also in %rax so serves as the right answer of "false"

                movq    arg1, %rax
                cmpq    arg3, %rax
                cmovcq  arg3, %rax
                movq    %rax, k

                testq   %rax, %rax
                jz      end

// Set up inside w two size-k buffers m and n

                leaq    (m,k,8), n

// Copy the input x into the buffer m, padding with zeros as needed

                xorq    i, i
                testq   arg1, arg1
                jz      xpadloop
xloop:
                movq    (arg2,i,8), a
                movq    a, (m,i,8)
                incq    i
                cmpq    arg1, i
                jc      xloop
                cmpq    k, i
                jnc     xskip
xpadloop:
                movq    $0,  (m,i,8)
                incq    i
                cmpq    k, i
                jc      xpadloop
xskip:

// Copy the input y into the buffer n, padding with zeros as needed

                xorq    i, i
                testq   arg3, arg3
                jz      ypadloop
yloop:
                movq    (arg4,i,8), a
                movq    a, (n,i,8)
                incq    i
                cmpq    arg3, i
                jc      yloop
                cmpq    k, i
                jnc     yskip
ypadloop:
                movq    $0,  (n,i,8)
                incq    i
                cmpq    k, i
                jc      ypadloop
yskip:

// Set up the outer loop count of 64 * sum of input sizes.
// The invariant is that m * n < 2^t at all times.

                leaq    (arg1,arg3), a
                shlq    $6, a
                movq    a, t

// Record for the very end the OR of the lowest words.
// If the bottom bit is zero we know both are even so the answer is false.
// But since this is constant-time code we still execute all the main part.

                movq    (m), a
                movq    (n), b
                orq     b, a
                movq    a, evenor

// Now if n is even trigger a swap of m and n. This ensures that if
// one or other of m and n is odd then we make sure now that n is,
// as expected by our invariant later on.

                andq    $1, b
                subq    $1, b

                xorq    i, i
swaploop:
                movq    (m,i,8), a
                movq    (n,i,8), c
                movq    a, d
                xorq    c, d
                andq    b, d
                xorq    d, a
                xorq    d, c
                movq    a, (m,i,8)
                movq    c, (n,i,8)
                incq    i
                cmpq    k, i
                jnz     swaploop

// Start of the main outer loop iterated t times

outerloop:

// We need only bother with sharper l = min k (ceil(t/64)) digits
// Either both m and n fit in l digits, or m has become zero and so
// nothing happens in the loop anyway and this makes no difference.

                movq    t, l
                addq    $63, l
                shrq    $6, l
                cmpq    k, l
                cmovncq k, l

// Select upper and lower proxies for both m and n to drive the inner
// loop. The lower proxies are simply the lowest digits themselves,
// m_lo = m[0] and n_lo = n[0], while the upper proxies are bitfields
// of the two inputs selected so their top bit (63) aligns with the
// most significant bit of *either* of the two inputs.

                xorq    h1, h1 // Previous high and low for m
                xorq    l1, l1
                xorq    h2, h2 // Previous high and low for n
                xorq    l2, l2
                xorq    c2, c2 // Mask flag: previous word of one was nonzero
                                // and in this case h1 and h2 are those words

                xorq    i, i
toploop:
                movq    (m,i,8), b
                movq    (n,i,8), c
                movq    c2, c1
                andq    h1, c1
                andq    h2, c2
                movq    b, a
                orq     c, a
                negq    a
                cmovcq  c1, l1
                cmovcq  c2, l2
                cmovcq  b, h1
                cmovcq  c, h2
                sbbq    c2, c2
                incq    i
                cmpq    l, i
                jc      toploop

                movq    h1, a
                orq     h2, a
                bsrq    a, c
                xorq    $63, c
                shldq   %cl, l1, h1
                shldq   %cl, l2, h2

// m_lo = m[0], n_lo = n[0];

                movq    (m), %rax
                movq    %rax, m_lo

                movq    (n), %rax
                movq    %rax, n_lo

// Now the inner loop, with i as loop counter from CHUNKSIZE down.
// This records a matrix of updates to apply to the initial
// values of m and n with, at stage j:
//
//     sgn * m' = (m_m * m - m_n * n) / 2^j
//    -sgn * n' = (n_m * m - n_n * n) / 2^j
//
// where "sgn" is either +1 or -1, and we lose track of which except
// that both instance above are the same. This throwing away the sign
// costs nothing (since we have to correct in general anyway because
// of the proxied comparison) and makes things a bit simpler. But it
// is simply the parity of the number of times the first condition,
// used as the swapping criterion, fires in this loop.

                movl    $1, m_mshort
                movl    $0, m_nshort
                movl    $0, n_mshort
                movl    $1, n_nshort
                movl    $CHUNKSIZE, ishort

innerloop:

// Not quite the same: the value b is in the flags as a NZ condition
//
// b = (m_lo & 1ull) & (m_hi < n_hi);

                movq    m_hi, %rax
                subq    n_hi, %rax
                sbbq    %rax, %rax
                andq    $1, %rax
                testq   m_lo, %rax

// if (b) { swap(m_hi,n_hi); swap(m_lo,n_lo); }

                movq    m_hi, %rax
                cmovnzq n_hi, m_hi
                cmovnzq %rax, n_hi

                movq    m_lo, %rax
                cmovnzq n_lo, m_lo
                cmovnzq %rax, n_lo

// if (b) { swap(m_m,n_m); swap(m_n,n_n); }

                movq    m_m, %rax
                cmovnzq n_m, m_m
                cmovnzq %rax, n_m

                movq    m_n, %rax
                cmovnzq n_n, m_n
                cmovnzq %rax, n_n

// This time actually put the condition in RBX as a mask
//
// b = (m_lo & 1ull);

                movq    m_lo, %rbx
                andq    $1, %rbx
                negq    %rbx

// if (b) { m_hi -= n_hi; m_lo -= n_lo; }

                movq    n_hi, %rax
                andq    %rbx, %rax
                subq    %rax, m_hi
                movq    n_lo, %rax
                andq    %rbx, %rax
                subq    %rax, m_lo

// if (b) { m_m += n_m; m_n += n_n; }

                movq    n_m, %rax
                andq    %rbx, %rax
                addq    %rax, m_m

                movq    n_n, %rax
                andq    %rbx, %rax
                addq    %rax, m_n

// m_hi >>= 1; m_lo >>= 1;

                shrq    $1, m_hi
                shrq    $1, m_lo

// n_m <<= 1; n_n <<= 1;

                leaq    (n_m,n_m), n_m
                leaq    (n_n,n_n), n_n

// End of the inner for-loop

                decq    i
                jnz     innerloop

// Put the matrix entries in memory since we're out of registers
// We pull them out repeatedly in the next loop

                movq    m_m, mat_mm
                movq    m_n, mat_mn
                movq    n_m, mat_nm
                movq    n_n, mat_nn

// Now actually compute the updates to m and n corresponding to that matrix,
// and correct the signs if they have gone negative. First we compute the
// (k+1)-sized updates with the following invariant (here h1 and h2 are in
// fact carry bitmasks, either 0 or -1):
//
//    h1::l1::m = m_m * m - m_n * n
//    h2::l2::n = n_m * m - n_n * n

                xorq    i, i
                xorq    h1, h1
                xorq    l1, l1
                xorq    h2, h2
                xorq    l2, l2
crossloop:

                movq    (m,i,8), c
                movq    mat_mm, a
                mulq    c
                addq    a, l1
                adcq    $0, d
                movq    d, c1 // Now c1::l1 is +ve part 1

                movq    mat_nm, a
                mulq    c
                addq    a, l2
                adcq    $0, d
                movq    d, c2 // Now c2::l2 is +ve part 2

                movq    (n,i,8), c
                movq    mat_mn, a
                mulq    c
                subq    h1, d // Now d::a is -ve part 1

                subq    a, l1
                sbbq    d, c1
                sbbq    h1, h1
                movq    l1, (m,i,8)
                movq    c1, l1

                movq    mat_nn, a
                mulq    c
                subq    h2, d // Now d::a is -ve part 2

                subq    a, l2
                sbbq    d, c2
                sbbq    h2, h2
                movq    l2, (n,i,8)
                movq    c2, l2

                incq    i
                cmpq    l, i
                jc      crossloop

// Now fix the signs of m and n if they have gone negative

                xorq    i, i
                movq    h1, c1 // carry-in coded up as well
                movq    h2, c2 // carry-in coded up as well
                xorq    h1, l1 // for the end digit
                xorq    h2, l2 // for the end digit
optnegloop:
                movq    (m,i,8), a
                xorq    h1, a
                negq    c1
                adcq    $0, a
                sbbq    c1, c1
                movq    a, (m,i,8)
                movq    (n,i,8), a
                xorq    h2, a
                negq    c2
                adcq    $0, a
                sbbq    c2, c2
                movq    a, (n,i,8)
                incq    i
                cmpq    l, i
                jc      optnegloop
                subq    c1, l1
                subq    c2, l2

// Now shift them right CHUNKSIZE bits

                movq    l, i
shiftloop:
                movq    -8(m,i,8), a
                movq    a, h1
                shrdq   $CHUNKSIZE, l1, a
                movq    a, -8(m,i,8)
                movq    h1, l1
                movq    -8(n,i,8), a
                movq    a, h2
                shrdq   $CHUNKSIZE, l2, a
                movq    a, -8(n,i,8)
                movq    h2, l2
                decq    i
                jnz     shiftloop

// End of main loop. We can stop if t' <= 0 since then m * n < 2^0, which
// since n is odd (in the main cases where we had one or other input odd)
// means that m = 0 and n is the final gcd. Moreover we do in fact need to
// maintain strictly t > 0 in the main loop, or the computation of the
// optimized digit bound l could collapse to 0.

                subq    $CHUNKSIZE, t
                jnbe    outerloop

// Now compare n with 1 (OR of the XORs in a)

                movq    (n), a
                xorq    $1, a
                cmpq    $1, k
                jz      finalcomb
                movl    $1, ishort
compareloop:
                orq     (n,i,8), a
                incq    i
                cmpq    k, i
                jc      compareloop

// Now combine that with original "evenor" oddness flag
// The final condition is lsb(evenor) = 1 AND a = 0

finalcomb:
                negq    a
                sbbq    a, a
                incq    a
                andq    evenor, a

// The end

end:
                addq    $STACKVARSIZE, %rsp
                popq    %r15
                popq    %r14
                popq    %r13
                popq    %r12
                popq    %rbx
                popq    %rbp

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif