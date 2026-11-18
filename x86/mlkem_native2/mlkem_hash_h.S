// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The hash H of ML-KEM, SHA3-256, with the x1 Keccak permutation
// Inputs in[len], c; output out[32]
//
// Sets out to SHA3-256(in), as in FIPS 202: the sponge with rate 136 bytes
// over Keccak-f1600 of the message padded with the domain bits 01 (byte
// 0x06) and the final bit (0x80 in the last byte of the block). This is
// H of FIPS 203 (section 4.1), and mlkem-native's mlk_sha3_256. The time
// taken depends only on len, and the Keccak state is zeroed before
// returning.
//
// extern void mlkem_hash_h(uint8_t out[S2N_BIGNUM_STATIC 32],
//                          const uint8_t *in, uint64_t len,
//                          const mlkem_native2_consts *c);
//
// Standard x86-64 ABI: RDI = out, RSI = in, RDX = len, RCX = c
// (the constants block: rc is used)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"
#ifndef MLKEM_NATIVE2_CONSTS_H
#include "mlkem_native2_consts.h"
#endif
#ifndef MLKEM_NATIVE2_NAMES_H
#include "mlkem_native2_names.h"
#endif
#include "mlkem_native2_macros.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(N2(mlkem_hash_h))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(N2(mlkem_hash_h))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(N2(mlkem_hash_h))
        .text
        .balign 32

// The stack frame: the 200-byte Keccak state at rsp (16-byte aligned after
// the four pushes and the frame), out, in, len and c in rbx, rbp, r12
// and r13 across the calls

#define FRAME 216
#define RATE 136

S2N_BN_SYMBOL(N2(mlkem_hash_h)):
        CFI_START
        _CET_ENDBR
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_DEC_RSP(FRAME)
        mov     rbx, rdi
        mov     rbp, rsi
        mov     r12, rdx
        mov     r13, rcx
        vpxor   xmm0, xmm0, xmm0
        vmovdqu [rsp+0], ymm0
        vmovdqu [rsp+32], ymm0
        vmovdqu [rsp+64], ymm0
        vmovdqu [rsp+96], ymm0
        vmovdqu [rsp+128], ymm0
        vmovdqu [rsp+160], ymm0
        vmovq   [rsp+192], xmm0

// Absorb the full blocks: XOR in RATE bytes and permute

Lmlkem_hash_h_block:
        cmp     r12, RATE
        jb      Lmlkem_hash_h_last
        vmovdqu ymm0, [rbp+0]
        vpxor   ymm0, ymm0, [rsp+0]
        vmovdqu [rsp+0], ymm0
        vmovdqu ymm0, [rbp+32]
        vpxor   ymm0, ymm0, [rsp+32]
        vmovdqu [rsp+32], ymm0
        vmovdqu ymm0, [rbp+64]
        vpxor   ymm0, ymm0, [rsp+64]
        vmovdqu [rsp+64], ymm0
        vmovdqu ymm0, [rbp+96]
        vpxor   ymm0, ymm0, [rsp+96]
        vmovdqu [rsp+96], ymm0
        mov     rax, [rbp+128]
        xor     [rsp+128], rax
        mov     rdi, rsp
        leadisp rsi, r13, MLKEM_C_RC
        call    S2N_BN_SYMBOL(N2_KECCAK_X1)
        add     rbp, RATE
        sub     r12, RATE
        jmp     Lmlkem_hash_h_block

// The last block: XOR in the len < RATE remaining bytes, whole words and
// then single bytes, the domain byte 0x06 after them and 0x80 at the end,
// and permute

Lmlkem_hash_h_last:
        mov     rdi, rsp
        mov     rcx, r12
        shr     rcx, 3
        jz      Lmlkem_hash_h_lastbytes
Lmlkem_hash_h_lastwords:
        mov     rax, [rbp]
        xor     [rdi], rax
        add     rbp, 8
        add     rdi, 8
        dec     rcx
        jnz     Lmlkem_hash_h_lastwords
Lmlkem_hash_h_lastbytes:
        mov     rcx, r12
        and     ecx, 7
        jz      Lmlkem_hash_h_pad
Lmlkem_hash_h_lastbyte:
        movzx   eax, BYTE PTR [rbp]
        xor     [rdi], al
        inc     rbp
        inc     rdi
        dec     rcx
        jnz     Lmlkem_hash_h_lastbyte
Lmlkem_hash_h_pad:
        xor     BYTE PTR [rdi], 0x06
        xor     BYTE PTR [rsp+RATE-1], 0x80
        mov     rdi, rsp
        leadisp rsi, r13, MLKEM_C_RC
        call    S2N_BN_SYMBOL(N2_KECCAK_X1)

// The digest, then zero the state

        vmovdqu ymm0, [rsp+0]
        vmovdqu [rbx+0], ymm0
        vpxor   xmm0, xmm0, xmm0
        vmovdqu [rsp+0], ymm0
        vmovdqu [rsp+32], ymm0
        vmovdqu [rsp+64], ymm0
        vmovdqu [rsp+96], ymm0
        vmovdqu [rsp+128], ymm0
        vmovdqu [rsp+160], ymm0
        vmovq   [rsp+192], xmm0
        vzeroupper
        CFI_INC_RSP(FRAME)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(N2(mlkem_hash_h))

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
