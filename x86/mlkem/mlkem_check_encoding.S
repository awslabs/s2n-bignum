// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Check that bytes encode ML-KEM polynomials with reduced coefficients
// Input a[384*k] (bytes), k; output function return
//
// Returns 1 if each of the 256 * k 12-bit little-endian fields of the
// 384 * k bytes, two to each group of 3 bytes, is less than 3329, and
// 0 otherwise. Thus 1 means that ByteEncode_12(ByteDecode_12(a)) = a for
// each 384-byte polynomial, the modulus check of an encapsulation key in
// FIPS 203 (section 7.2), as done by mlkem-native's mlk_kem_check_pk. The
// time taken depends only on k.
//
// extern uint64_t mlkem_check_encoding(const uint8_t *a, uint64_t k);
//
// Standard x86-64 ABI: RDI = a, RSI = k
// Microsoft x64 ABI:   RCX = a, RDX = k
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_check_encoding)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_check_encoding):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(48)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVE(rdi,32)
        CFI_STACKSAVE(rsi,40)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// ymm0 = 3328 in each word, ymm5 = 0x0fff in each word,
// ymm6 = the byte pairs of the fields (lane 1 from 4 bytes in),
// ymm4 = the accumulator of fields > 3328

        mov     eax, 0xd000d00
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0xfff0fff
        vmovd   xmm5, eax
        vpbroadcastd ymm5, xmm5
        movabs  rax, 0x0504040302010100
        vmovq   xmm6, rax
        movabs  rax, 0x0b0a0a0908070706
        vpinsrq xmm6, xmm6, rax, 1
        movabs  rax, 0x0908080706050504
        vmovq   xmm7, rax
        movabs  rax, 0x0f0e0e0d0c0b0b0a
        vpinsrq xmm7, xmm7, rax, 1
        vinserti128 ymm6, ymm6, xmm7, 1
        vpxor   xmm4, xmm4, xmm4
        test    rsi, rsi
        jz      Lmlkem_check_encoding_done

Lmlkem_check_encoding_loop:
        vmovdqu xmm1, [rdi+0]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+8], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+24]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+32], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+48]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+56], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+72]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+80], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+96]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+104], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+120]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+128], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+144]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+152], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+168]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+176], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+192]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+200], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+216]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+224], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+240]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+248], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+264]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+272], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+288]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+296], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+312]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+320], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        vmovdqu xmm1, [rdi+336]
        vinserti128 ymm1, ymm1, XMMWORD PTR [rdi+344], 1
        vpshufb ymm1, ymm1, ymm6
        vpsrlw  ymm2, ymm1, 4
        vpand   ymm1, ymm1, ymm5
        vpblendw ymm1, ymm1, ymm2, 0xaa
        vpcmpgtw ymm1, ymm1, ymm0
        vpor    ymm4, ymm4, ymm1
        vmovdqu xmm3, [rdi+360]
        vinserti128 ymm3, ymm3, XMMWORD PTR [rdi+368], 1
        vpshufb ymm3, ymm3, ymm6
        vpsrlw  ymm7, ymm3, 4
        vpand   ymm3, ymm3, ymm5
        vpblendw ymm3, ymm3, ymm7, 0xaa
        vpcmpgtw ymm3, ymm3, ymm0
        vpor    ymm4, ymm4, ymm3
        add     rdi, 384
        dec     rsi
        jnz     Lmlkem_check_encoding_loop

Lmlkem_check_encoding_done:
        xor     eax, eax
        vptest  ymm4, ymm4
        setz    al

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOAD(rdi,32)
        CFI_STACKLOAD(rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_check_encoding)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
