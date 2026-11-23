// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 3 for ML-KEM
// Input buf[192] (bytes); output r[256] (signed 16-bit words)
//
// Each group of 3 input bytes, the 24-bit little-endian number t, gives
// four coefficients, each in the range -3..3: with t_k the bits of t,
//
//   r[4*i+j] = (t_6j + t_6j+1 + t_6j+2) - (t_6j+3 + t_6j+4 + t_6j+5)
//
// for group i = 0..63 and j = 0..3. This is SamplePolyCBD_3 of FIPS 203
// (Algorithm 8) on the 192 bytes, as in mlkem-native's mlk_poly_cbd3.
//
// extern void mlkem_cbd3(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 192]);
//
// Standard x86-64 ABI: RDI = r, RSI = buf
// Microsoft x64 ABI:   RCX = r, RDX = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd3)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd3)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd3)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_cbd3):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVE(rdi,80)
        CFI_STACKSAVE(rsi,88)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// ymm0 = the byte selection in each lane, ymm1 = the shifts 0, 4,
// ymm2 = 0x003f003f in each dword, ymm3 = 7 in each word,
// ymm8 = the popcounts of 0..7 in each lane, ymm9 = the byte
// selection for the last vector

        movabs  rax, 0x8080020180800100
        vmovq   xmm0, rax
        movabs  rax, 0x8080050480800403
        vpinsrq xmm0, xmm0, rax, 1
        vinserti128 ymm0, ymm0, xmm0, 1
        mov     eax, 0x4
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1
        vpsllq  ymm1, ymm1, 32
        mov     eax, 0x3f003f
        vmovd   xmm2, eax
        vpbroadcastd ymm2, xmm2
        mov     eax, 0x70007
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        movabs  rax, 0x0302020102010100
        vmovq   xmm8, rax
        movabs  rax, 0x0000000000000000
        vpinsrq xmm8, xmm8, rax, 1
        vinserti128 ymm8, ymm8, xmm8, 1
        movabs  rax, 0x8080060580800504
        vmovq   xmm9, rax
        movabs  rax, 0x8080090880800807
        vpinsrq xmm9, xmm9, rax, 1
        movabs  rax, 0x80800c0b80800b0a
        vmovq   xmm10, rax
        movabs  rax, 0x80800f0e80800e0d
        vpinsrq xmm10, xmm10, rax, 1
        vinserti128 ymm9, ymm9, xmm10, 1

// For each 12 bytes, 16 coefficients

        vmovdqu xmm4, [rsi+0]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+6], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+0], ymm4
        vmovdqu xmm6, [rsi+12]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+18], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+32], ymm6
        vmovdqu xmm4, [rsi+24]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+30], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+64], ymm4
        vmovdqu xmm6, [rsi+36]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+42], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+96], ymm6
        vmovdqu xmm4, [rsi+48]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+54], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+128], ymm4
        vmovdqu xmm6, [rsi+60]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+66], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+160], ymm6
        vmovdqu xmm4, [rsi+72]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+78], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+192], ymm4
        vmovdqu xmm6, [rsi+84]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+90], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+224], ymm6
        vmovdqu xmm4, [rsi+96]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+102], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+256], ymm4
        vmovdqu xmm6, [rsi+108]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+114], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+288], ymm6
        vmovdqu xmm4, [rsi+120]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+126], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+320], ymm4
        vmovdqu xmm6, [rsi+132]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+138], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+352], ymm6
        vmovdqu xmm4, [rsi+144]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+150], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+384], ymm4
        vmovdqu xmm6, [rsi+156]
        vinserti128 ymm6, ymm6, XMMWORD PTR [rsi+162], 1
        vpshufb ymm6, ymm6, ymm0
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+416], ymm6
        vmovdqu xmm4, [rsi+168]
        vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+174], 1
        vpshufb ymm4, ymm4, ymm0
        vpsrlvd ymm4, ymm4, ymm1
        vpslld  ymm5, ymm4, 10
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm2
        vpsrlw  ymm5, ymm4, 3
        vpand   ymm4, ymm4, ymm3
        vpshufb ymm4, ymm8, ymm4
        vpshufb ymm5, ymm8, ymm5
        vpsubw  ymm4, ymm4, ymm5
        vmovdqu [rdi+448], ymm4
        vmovdqu xmm6, [rsi+176]
        vinserti128 ymm6, ymm6, xmm6, 1
        vpshufb ymm6, ymm6, ymm9
        vpsrlvd ymm6, ymm6, ymm1
        vpslld  ymm7, ymm6, 10
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm2
        vpsrlw  ymm7, ymm6, 3
        vpand   ymm6, ymm6, ymm3
        vpshufb ymm6, ymm8, ymm6
        vpshufb ymm7, ymm8, ymm7
        vpsubw  ymm6, ymm6, ymm7
        vmovdqu [rdi+480], ymm6

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOAD(rdi,80)
        CFI_STACKLOAD(rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd3)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
