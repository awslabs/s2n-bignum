// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform for ML-DSA
// Input a[256], zetas (all signed 32-bit words); output a[256] (signed 32-bit words)
//
// The transform is in-place with input and output a[256], with the output
// in bitreversed order. Computes the forward NTT of a polynomial in place,
// transforming from coefficient representation to NTT representation. The input
// polynomial a is a 256-element array of signed 32-bit integers representing
// coefficients in normal order, assumed to be coefficient-wise bound by MLDSA_Q
// (8380417) in absolute value. The zetas parameter points to precomputed twiddle
// factors (roots of unity and their Montgomery inverses) required for the NTT
// computation. The output polynomial is in bitreversed order and coefficient-wise
// bound by 42035261 (just over 5*Q) in absolute value. Output coefficients are
// congruent to the mathematical NTT result modulo Q but are not fully reduced.
//
// The implementation uses Montgomery arithmetic for efficient modular reduction
// modulo Q = 8380417, maintaining constant-time execution for side-channel
// resistance. The transform operates in the ring R_Q = Z_Q[x]/(x^256 + 1).
//
// extern void mldsa_ntt(int32_t a[static 256], const int32_t zetas[static 624]);
//
// Standard x86-64 ABI: RDI = a, RSI = zetas
// Microsoft x64 ABI:   RCX = a, RDX = zetas
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_ntt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_ntt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_ntt)
        .text

#define a %rdi
#define zetas %rsi

#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQ 0
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV 8
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV_QINV 16
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV 24
#define MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV 32
#define MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS 328

.macro shuffle8 r0,r1,r2,r3
vperm2i128	$0x20,%ymm\r1,%ymm\r0,%ymm\r2
vperm2i128	$0x31,%ymm\r1,%ymm\r0,%ymm\r3
.endm

.macro shuffle4 r0,r1,r2,r3
vpunpcklqdq	%ymm\r1,%ymm\r0,%ymm\r2
vpunpckhqdq	%ymm\r1,%ymm\r0,%ymm\r3
.endm

.macro shuffle2 r0,r1,r2,r3
vmovsldup	%ymm\r1,%ymm\r2
vpblendd	$0xAA,%ymm\r2,%ymm\r0,%ymm\r2
vpsrlq		$32,%ymm\r0,%ymm\r0
vpblendd	$0xAA,%ymm\r1,%ymm\r0,%ymm\r3
.endm

.macro butterfly l,h,zl0=1,zl1=1,zh0=2,zh1=2
vpmuldq		%ymm\zl0,%ymm\h,%ymm13
vmovshdup	%ymm\h,%ymm12
vpmuldq		%ymm\zl1,%ymm12,%ymm14

vpmuldq		%ymm\zh0,%ymm\h,%ymm\h
vpmuldq		%ymm\zh1,%ymm12,%ymm12

vpmuldq		%ymm0,%ymm13,%ymm13
vpmuldq		%ymm0,%ymm14,%ymm14

vmovshdup	%ymm\h,%ymm\h
vpblendd	$0xAA,%ymm12,%ymm\h,%ymm\h

vpsubd		%ymm\h,%ymm\l,%ymm12
vpaddd		%ymm\h,%ymm\l,%ymm\l

vmovshdup	%ymm13,%ymm13
vpblendd	$0xAA,%ymm14,%ymm13,%ymm13

vpaddd		%ymm13,%ymm12,%ymm\h
vpsubd		%ymm13,%ymm\l,%ymm\l
.endm

.macro levels0t1 off
/* level 0 */
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+1)*4(%rsi),%ymm1
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+1)*4(%rsi),%ymm2

vmovdqa		0+32*\off(%rdi),%ymm4
vmovdqa		128+32*\off(%rdi),%ymm5
vmovdqa		256+32*\off(%rdi),%ymm6
vmovdqa		384+32*\off(%rdi),%ymm7
vmovdqa		512+32*\off(%rdi),%ymm8
vmovdqa		640+32*\off(%rdi),%ymm9
vmovdqa		768+32*\off(%rdi),%ymm10
vmovdqa		896+32*\off(%rdi),%ymm11

butterfly       4,8
butterfly       5,9
butterfly       6,10
butterfly       7,11

/* level 1 */
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+2)*4(%rsi),%ymm1
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+2)*4(%rsi),%ymm2
butterfly       4,6
butterfly       5,7

vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+3)*4(%rsi),%ymm1
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+3)*4(%rsi),%ymm2
butterfly       8,10
butterfly       9,11

vmovdqa		%ymm4,0+32*\off(%rdi)
vmovdqa		%ymm5,128+32*\off(%rdi)
vmovdqa		%ymm6,256+32*\off(%rdi)
vmovdqa		%ymm7,384+32*\off(%rdi)
vmovdqa		%ymm8,512+32*\off(%rdi)
vmovdqa		%ymm9,640+32*\off(%rdi)
vmovdqa		%ymm10,768+32*\off(%rdi)
vmovdqa		%ymm11,896+32*\off(%rdi)
.endm

.macro levels2t7 off
/* level 2 */
vmovdqa		256*\off+0(%rdi),%ymm4
vmovdqa		256*\off+32(%rdi),%ymm5
vmovdqa		256*\off+64(%rdi),%ymm6
vmovdqa		256*\off+96(%rdi),%ymm7
vmovdqa		256*\off+128(%rdi),%ymm8
vmovdqa		256*\off+160(%rdi),%ymm9
vmovdqa		256*\off+192(%rdi),%ymm10
vmovdqa		256*\off+224(%rdi),%ymm11
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+4+\off)*4(%rsi),%ymm1
vpbroadcastd	(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+4+\off)*4(%rsi),%ymm2

butterfly       4,8
butterfly       5,9
butterfly       6,10
butterfly       7,11

shuffle8        4,8,3,8
shuffle8        5,9,4,9
shuffle8        6,10,5,10
shuffle8        7,11,6,11

/* level 3 */
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+8+8*\off)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+8+8*\off)*4(%rsi),%ymm2

butterfly       3,5
butterfly       8,10
butterfly       4,6
butterfly       9,11

shuffle4        3,5,7,5
shuffle4        8,10,3,10
shuffle4        4,6,8,6
shuffle4        9,11,4,11

/* level 4 */
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+40+8*\off)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+40+8*\off)*4(%rsi),%ymm2

butterfly       7,8
butterfly       5,6
butterfly       3,4
butterfly       10,11

shuffle2        7,8,9,8
shuffle2        5,6,7,6
shuffle2        3,4,5,4
shuffle2        10,11,3,11

/* level 5 */
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+72+8*\off)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+72+8*\off)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15

butterfly       9,5,1,10,2,15
butterfly       8,4,1,10,2,15
butterfly       7,3,1,10,2,15
butterfly       6,11,1,10,2,15

/* level 6 */
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       9,7,1,10,2,15
butterfly       8,6,1,10,2,15

vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off+32)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off+32)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       5,3,1,10,2,15
butterfly       4,11,1,10,2,15

/* level 7 */
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       9,8,1,10,2,15

vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+32)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+32)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       7,6,1,10,2,15

vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+64)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+64)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       5,4,1,10,2,15

vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+96)*4(%rsi),%ymm1
vmovdqa		(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+96)*4(%rsi),%ymm2
vpsrlq		$32,%ymm1,%ymm10
vmovshdup	%ymm2,%ymm15
butterfly       3,11,1,10,2,15

vmovdqa		%ymm9,256*\off+0(%rdi)
vmovdqa		%ymm8,256*\off+32(%rdi)
vmovdqa		%ymm7,256*\off+64(%rdi)
vmovdqa		%ymm6,256*\off+96(%rdi)
vmovdqa		%ymm5,256*\off+128(%rdi)
vmovdqa		%ymm4,256*\off+160(%rdi)
vmovdqa		%ymm3,256*\off+192(%rdi)
vmovdqa		%ymm11,256*\off+224(%rdi)
.endm

S2N_BN_SYMBOL(mldsa_ntt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(176)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVEU(%xmm9,48)
        CFI_STACKSAVEU(%xmm10,64)
        CFI_STACKSAVEU(%xmm11,80)
        CFI_STACKSAVEU(%xmm12,96)
        CFI_STACKSAVEU(%xmm13,112)
        CFI_STACKSAVEU(%xmm14,128)
        CFI_STACKSAVEU(%xmm15,144)
        CFI_STACKSAVE(%rdi,160)
        CFI_STACKSAVE(%rsi,168)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

        vmovdqa MLD_AVX2_BACKEND_DATA_OFFSET_8XQ*4(%rsi), %ymm0

        levels0t1 0
        levels0t1 1
        levels0t1 2
        levels0t1 3

        levels2t7 0
        levels2t7 1
        levels2t7 2
        levels2t7 3

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOADU(%xmm9,48)
        CFI_STACKLOADU(%xmm10,64)
        CFI_STACKLOADU(%xmm11,80)
        CFI_STACKLOADU(%xmm12,96)
        CFI_STACKLOADU(%xmm13,112)
        CFI_STACKLOADU(%xmm14,128)
        CFI_STACKLOADU(%xmm15,144)
        CFI_STACKLOAD(%rdi,160)
        CFI_STACKLOAD(%rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_ntt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
