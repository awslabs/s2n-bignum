// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Generate the ML-KEM matrix, hashing messages and sampling noise on the side
// Inputs rho[32], k, flags, jobs[2], noise, c; outputs a[256*k*k], the hash
// digests and the noise polynomials
//
// For 0 <= i, j < k, the polynomial a[i][j] = a[256 * (k * i + j) ...] is
// set to SampleNTT(rho || j || i) as in FIPS 203 (Algorithm 7), or if bit 0
// of flags is set (transposed) SampleNTT(rho || i || j): the rejection
// sampling of 12-bit fields < 3329 from the output of SHAKE128 of the
// 34-byte seed, with the coefficients then permuted into the custom NTT
// order of the x86 kernels (as by mlkem_unpack). This is mlkem-native's
// mlk_gen_matrix with its x86_64 backend. The parameter k is 2, 3 or 4,
// and a must be 32-byte aligned.
//
// If bit 1 of flags is set, each job in jobs[0..1] with a nonzero ds is a
// hash to compute at the same time: its 32-byte digest is the first 32
// bytes of the output of the sponge with rate 136 of the len bytes at msg
// with the domain byte ds, i.e. SHA3-256 for ds = 0x06 and SHAKE256 (to 32
// bytes) for ds = 0x1f, and is written to out. The length len must be a
// multiple of 8. The hashes run in lanes 2 and 3 of the x4 permutation
// while the matrix polynomials take the others.
//
// If bit 2 of flags is set, then also for 0 <= i < n the polynomial
// out[256 * i ...] of the noise job is set to
// SamplePolyCBD_2(PRF_2(sigma, nonce0 + i)), as by mlkem_getnoise (with
// nonce0 + n at most 256): these are sampled in lanes left idle by the
// matrix, and any left over at the end by calling mlkem_getnoise.
//
// The jobs and the noise job are read only when their bits are set, and no
// address is compared with NULL, so any addresses work.
//
// The time taken depends only on k, the jobs' lengths, the number of noise
// polynomials and the matrix (and so on rho), all public; the message
// bytes and the noise seed, which may be secret, only pass through XORs,
// the permutation and the CBD, and the Keccak state is zeroed before
// returning.
//
// typedef struct {const uint8_t *msg; uint64_t len, ds; uint8_t *out;}
//         mlkem_hash_job;
// typedef struct {const uint8_t *sigma; uint64_t nonce0, n; int16_t *out;}
//         mlkem_noise_job;
// extern void mlkem_gen_matrix(int16_t *a, const uint8_t rho[32],
//                              uint64_t k, uint64_t flags,
//                              const mlkem_hash_job jobs[2],
//                              const mlkem_noise_job *noise,
//                              const mlkem_native2_consts *c);
//
// Standard x86-64 ABI: RDI = a, RSI = rho, RDX = k, RCX = flags, R8 = jobs,
// R9 = noise, [RSP+8] = c (the constants block: rc, the rho8 and rho56
// tables of sha3_keccak4_f1600_alt and rej_uniform_table are used)
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
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(N2(mlkem_gen_matrix))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(N2(mlkem_gen_matrix))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(N2(mlkem_gen_matrix))
        .text
        .balign 32

// The stack frame, 16-byte aligned after the six pushes: the x4 Keccak
// state (four 200-byte lanes), the three-block output buffers of the four
// lanes, the working copies of the two hash jobs (p = next message byte,
// r = bytes left or -1 after the final block, ds or 0 when inactive, out)
// and of the noise job (sigma, nonce0, n, out and next, the number
// started), the noise polynomial of each lane (-1 if none), the flags
// argument (bit 0 is transposed), the flags of the current pass, the
// multiplier for division by k, the count of a polynomial in the rare
// case of more blocks, k, k * k, the number of matrix lanes of the pass
// and the number of lanes free of hash jobs. The constants block c is
// above the frame, as the seventh argument.

#define ST 0
#define BUF 800
#define JOBS 2816
#define NOISE 2880
#define NCUR 2928
#define TRANSP 2960
#define FLAGS 2968
#define KDIV 2976
#define RCNT 2984
#define KK 2992
#define K 3000
#define NM 3008
#define NMAT 3016
#define FRAME 3032
#define ARG7 (FRAME + 56)

#define LANEBYTES 200
#define BUFBYTES 504
#define SHAKE128_RATE 168
#define SHAKE256_RATE 136

// Registers held across calls

#define a rbx
#define rho rbp
#define idx r12
#define step r13
#define lane r14
#define idxd r12d
#define stepd r13d
#define laned r14d
#define c r15

// The domain bytes of SHAKE128 and SHAKE256 (with the final bit, 0x80 in
// the last byte of the block, this is the padding)

#define SHAKE128_DS 0x1f
#define SHAKE256_DS 0x1f

// ----------------------------------------------------------------------------
// Macros for the steps on single lanes. They use only rax, rcx, rdx, rsi,
// rdi, r8-r11 and ymm0-ymm1 (besides the calls in samplepoly).
// ----------------------------------------------------------------------------

// laneaddr dst, l: dst := the address of lane l (a register) of the state

        .macro laneaddr dst, l
        imul    \dst, \l, LANEBYTES
        lea     \dst, [rsp+ST+\dst]
        .endm

// zerolanes off, len: zero len bytes (a multiple of 16) of the state at
// off, 128 bytes at a time and then the rest

        .macro zerolanes off, len
        .if ((\len) % 16) != 0
        .error "zerolanes: len must be a multiple of 16"
        .endif
        vpxor   xmm0, xmm0, xmm0
        leadisp rdi, rsp, ST+(\off)
        .if ((\len) / 128) != 0
        mov     ecx, ((\len) / 128)
1:
        vmovdqu [rdi], ymm0
        vmovdqu [rdi+32], ymm0
        vmovdqu [rdi+64], ymm0
        vmovdqu [rdi+96], ymm0
        add     rdi, 128
        dec     ecx
        jnz     1b
        .endif
        .set    i, 0
        .rept   (((\len) % 128) / 32)
        vmovdqu [rdi+i], ymm0
        .set    i, i + 32
        .endr
        .if ((\len) % 32) != 0
        vmovdqu [rdi+i], xmm0
        .endif
        .endm

// initlane l, e: set lane l to the absorbed seed of matrix polynomial e
// (registers): rho, the two index bytes, the domain byte 0x1f, zeros and
// the final bit 0x80 in byte 167. The row e / k is (e * m) >> 5 with
// m = 16, 11, 8 for k = 2, 3, 4 (in the frame), exact for e < 16.

        .macro initlane l, e
        laneaddr rdi, \l
        mov     rax, \e
        imul    rax, [rsp+KDIV]
        shr     rax, 5
        mov     rdx, rax
        imul    rdx, [rsp+K]
        mov     rcx, \e
        sub     rcx, rdx
        test    QWORD PTR [rsp+TRANSP], 1
        mov     rdx, rcx
        cmovnz  rdx, rax
        cmovnz  rax, rcx
        shl     rax, 8
        or      rax, rdx
        or      rax, (SHAKE128_DS << 16)
        vmovdqu ymm1, [rho]
        vmovdqu [rdi], ymm1
        mov     [rdi+32], rax
        vpxor   xmm0, xmm0, xmm0
        vmovdqu [rdi+40], ymm0
        vmovdqu [rdi+72], ymm0
        vmovdqu [rdi+104], ymm0
        vmovdqu [rdi+136], ymm0
        vmovdqu [rdi+168], ymm0
        mov     BYTE PTR [rdi+167], 0x80
        .endm

// initnoise l, i: set lane l to the absorbed seed of noise polynomial i
// (registers): sigma || (nonce0 + i), the domain byte 0x1f, zeros and the
// final bit 0x80 in byte 135.

        .macro initnoise l, i
        laneaddr rdi, \l
        mov     rsi, [rsp+NOISE]
        mov     rax, [rsp+NOISE+8]
        add     rax, \i
        movzx   eax, al
        or      eax, (SHAKE256_DS << 8)
        vmovdqu ymm1, [rsi]
        vmovdqu [rdi], ymm1
        mov     [rdi+32], rax
        vpxor   xmm0, xmm0, xmm0
        vmovdqu [rdi+40], ymm0
        vmovdqu [rdi+72], ymm0
        vmovdqu [rdi+104], ymm0
        vmovdqu [rdi+136], ymm0
        vmovdqu [rdi+168], ymm0
        mov     BYTE PTR [rdi+135], 0x80
        .endm

// absorbjob j: absorb the next block of hash job j (0 or 1, a number) into
// its lane (2 or 3), if the job is active (ds is nonzero) and not finished:
// 136 message bytes, or the r < 136 that remain and the padding (the
// domain byte ds at r and 0x80 at 135), setting r = -1 to mark the final
// block.

        .macro absorbjob j
        lea     r9, [rsp+JOBS+32*\j]
        mov     r10, [r9]
        mov     r11, [r9+8]
        mov     r8, [r9+16]
        test    r8, r8
        jz      9f
        test    r11, r11
        js      9f
        lea     rdi, [rsp+ST+LANEBYTES*(2+\j)]
        mov     ecx, SHAKE256_RATE
        cmp     r11, rcx
        cmovb   rcx, r11
        mov     rdx, rdi
        test    rcx, rcx
        jz      2f
1:
        mov     rax, [r10]
        xor     [rdx], rax
        add     r10, 8
        add     rdx, 8
        sub     rcx, 8
        jnz     1b
2:
        cmp     r11, SHAKE256_RATE
        jae     3f
        xor     [rdi+r11], r8b
        xor     BYTE PTR [rdi+SHAKE256_RATE-1], 0x80
        mov     [r9], r10
        mov     QWORD PTR [r9+8], -1
        jmp     9f
3:
        sub     r11, SHAKE256_RATE
        mov     [r9], r10
        mov     [r9+8], r11
9:
        .endm

// finishjob j: if hash job j has absorbed its final block (and so just been
// permuted), copy the 32-byte digest from its lane and make it inactive
// (ds = 0).

        .macro finishjob j
        lea     r9, [rsp+JOBS+32*\j]
        cmp     QWORD PTR [r9+16], 0
        je      9f
        cmp     QWORD PTR [r9+8], 0
        jge     9f
        mov     rdi, [r9+24]
        vmovdqu ymm0, [rsp+ST+LANEBYTES*(2+\j)]
        vmovdqu [rdi], ymm0
        mov     QWORD PTR [r9+16], 0
9:
        .endm

// samplepoly: rejection sampling for matrix polynomial idx + lane from the
// three blocks in the buffer of that lane, then, while it has fewer than
// 256 coefficients (the rare case), another block squeezed from the lane
// with the x1 permutation and sampled from the lane directly, and the
// permutation into the custom NTT order. This calls functions: the lane
// and polynomial are recomputed from the callee-saved idx and lane.

        .macro samplepoly
        lea     rax, [idx+lane]
        shl     rax, 9
        lea     rdi, [a+rax]
        xor     esi, esi
        imul    rdx, lane, BUFBYTES
        lea     rdx, [rsp+BUF+rdx]
        mov     ecx, BUFBYTES
        lea     r8, [c+MLKEM_C_REJ_UNIFORM_TABLE]
        call    S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME)
1:
        cmp     rax, 256
        jae     2f
        mov     [rsp+RCNT], rax
        laneaddr rdi, lane
        leadisp rsi, c, MLKEM_C_RC
        call    S2N_BN_SYMBOL(N2_KECCAK_X1)
        lea     rax, [idx+lane]
        shl     rax, 9
        lea     rdi, [a+rax]
        mov     rsi, [rsp+RCNT]
        laneaddr rdx, lane
        mov     ecx, SHAKE128_RATE
        lea     r8, [c+MLKEM_C_REJ_UNIFORM_TABLE]
        call    S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME)
        jmp     1b
2:
        lea     rax, [idx+lane]
        shl     rax, 9
        lea     rdi, [a+rax]
        call    S2N_BN_SYMBOL(mlkem_unpack)
        .endm

// copyblock dst, src: copy the 168 bytes of a SHAKE128 block (registers)

        .macro copyblock dst, src
        vmovdqu ymm0, [\src]
        vmovdqu [\dst], ymm0
        vmovdqu ymm0, [\src+32]
        vmovdqu [\dst+32], ymm0
        vmovdqu ymm0, [\src+64]
        vmovdqu [\dst+64], ymm0
        vmovdqu ymm0, [\src+96]
        vmovdqu [\dst+96], ymm0
        vmovdqu ymm0, [\src+128]
        vmovdqu [\dst+128], ymm0
        mov     rax, [\src+160]
        mov     [\dst+160], rax
        .endm

// x4: the x4 permutation of the whole state

        .macro x4
        leadisp rdi, rsp, ST
        leadisp rsi, c, MLKEM_C_RC
        lea     rdx, [c+MLKEM_C_KECCAK_RHO8]
        lea     rcx, [c+MLKEM_C_KECCAK_RHO56]
        call    S2N_BN_SYMBOL(N2_KECCAK_X4)
        .endm

// ----------------------------------------------------------------------------
// The function
// ----------------------------------------------------------------------------

S2N_BN_SYMBOL(N2(mlkem_gen_matrix)):
        CFI_START
        _CET_ENDBR
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(FRAME)

        mov     a, rdi
        mov     rho, rsi
        mov     [rsp+K], rdx
        mov     [rsp+TRANSP], rcx
        mov     c, [rsp+ARG7]
        mov     eax, 16
        cmp     rdx, 3
        mov     r10d, 11
        cmove   rax, r10
        cmp     rdx, 4
        mov     r10d, 8
        cmove   rax, r10
        mov     [rsp+KDIV], rax
        mov     rax, rdx
        imul    rax, rdx
        mov     [rsp+KK], rax
        xor     idxd, idxd

// Copy the noise job (bit 2 of the flags), with next = 0, or make it empty
// (n = 0)

        xor     eax, eax
        mov     [rsp+NOISE+16], rax
        mov     [rsp+NOISE+24], rax
        mov     [rsp+NOISE+32], rax
        test    ecx, 4
        jz      Lmlkem_gen_matrix_nonoise
        vmovdqu ymm0, [r9]
        vmovdqu [rsp+NOISE], ymm0
Lmlkem_gen_matrix_nonoise:

// Copy the hash jobs (bit 1), or make them inactive (ds = 0), and zero
// their lanes 2 and 3

        test    ecx, 2
        jz      Lmlkem_gen_matrix_nojobs
        vmovdqu ymm0, [r8]
        vmovdqu [rsp+JOBS], ymm0
        vmovdqu ymm0, [r8+32]
        vmovdqu [rsp+JOBS+32], ymm0
        jmp     Lmlkem_gen_matrix_jobsdone
Lmlkem_gen_matrix_nojobs:
        mov     [rsp+JOBS+16], rax
        mov     [rsp+JOBS+48], rax
Lmlkem_gen_matrix_jobsdone:
        zerolanes (2*LANEBYTES), (2*LANEBYTES)

// The main loop: each pass samples nm polynomials in lanes 0..nm-1, where
// nm = min(nmat, the number left) and nmat is four if no hash job is
// active, three if only job 1 (lane 3) is, two if job 0 (lane 2) is. The
// lanes nm..nmat-1 are idle, and take noise polynomials, one block each, a
// new one at each step. When one polynomial remains, no hash job is active
// and there is no noise left, it is sampled with the x1 permutation
// instead, which is cheaper than an x4 one with lanes left idle.

Lmlkem_gen_matrix_outer:
        cmp     idx, [rsp+KK]
        jae     Lmlkem_gen_matrix_hashtail
        mov     eax, 4
        mov     r10d, 3
        cmp     QWORD PTR [rsp+JOBS+48], 0
        cmovne  rax, r10
        mov     r10d, 2
        cmp     QWORD PTR [rsp+JOBS+16], 0
        cmovne  rax, r10
        mov     [rsp+NMAT], rax
        mov     rdx, [rsp+KK]
        sub     rdx, idx
        cmp     rax, 4
        jne     Lmlkem_gen_matrix_pass
        cmp     rdx, 1
        ja      Lmlkem_gen_matrix_pass
        mov     rcx, [rsp+NOISE+32]
        cmp     rcx, [rsp+NOISE+16]
        jae     Lmlkem_gen_matrix_x1tail
Lmlkem_gen_matrix_pass:
        cmp     rax, rdx
        cmova   rax, rdx
        mov     [rsp+NM], rax

// Initialize the lanes of the polynomials idx .. idx+nm-1

        xor     laned, laned
Lmlkem_gen_matrix_initloop:
        lea     r11, [idx+lane]
        initlane lane, r11
        inc     lane
        cmp     lane, [rsp+NM]
        jb      Lmlkem_gen_matrix_initloop

// Three steps: give each idle lane the next noise polynomial if any,
// absorb a block of each active hash job, permute, copy a block of output
// of each matrix polynomial's lane to its buffer, and sample each noise
// polynomial from its lane. Whether there are hash jobs or noise to do
// is decided once for the pass, the flags being kept in the frame
// (bit 0: hash jobs active, bit 1: idle lanes and noise left).

        mov     rax, [rsp+JOBS+16]
        or      rax, [rsp+JOBS+48]
        setnz   al
        movzx   eax, al
        mov     rcx, [rsp+NOISE+32]
        cmp     rcx, [rsp+NOISE+16]
        jae     Lmlkem_gen_matrix_nonoiseflag
        mov     rcx, [rsp+NM]
        cmp     rcx, [rsp+NMAT]
        jae     Lmlkem_gen_matrix_nonoiseflag
        or      eax, 2
Lmlkem_gen_matrix_nonoiseflag:
        mov     [rsp+FLAGS], rax

        xor     stepd, stepd
Lmlkem_gen_matrix_steploop:
        test    QWORD PTR [rsp+FLAGS], 2
        jz      Lmlkem_gen_matrix_noiseinit_done
        mov     lane, [rsp+NM]
Lmlkem_gen_matrix_noiseinit:
        cmp     lane, [rsp+NMAT]
        jae     Lmlkem_gen_matrix_noiseinit_done
        mov     QWORD PTR [rsp+NCUR+8*lane], -1
        mov     r11, [rsp+NOISE+32]
        cmp     r11, [rsp+NOISE+16]
        jae     Lmlkem_gen_matrix_noiseinit_next
        mov     [rsp+NCUR+8*lane], r11
        lea     rax, [r11+1]
        mov     [rsp+NOISE+32], rax
        initnoise lane, r11
Lmlkem_gen_matrix_noiseinit_next:
        inc     lane
        jmp     Lmlkem_gen_matrix_noiseinit
Lmlkem_gen_matrix_noiseinit_done:
        test    QWORD PTR [rsp+FLAGS], 1
        jz      Lmlkem_gen_matrix_nohash1
        absorbjob 0
        absorbjob 1
Lmlkem_gen_matrix_nohash1:
        x4
        test    QWORD PTR [rsp+FLAGS], 1
        jz      Lmlkem_gen_matrix_nohash2
        finishjob 0
        finishjob 1
Lmlkem_gen_matrix_nohash2:

// Copy the block of each of the nm lanes 0..nm-1 to offset 168 * step of
// its buffer (the buffers 504 bytes apart, the lanes 200)

        imul    rdi, step, SHAKE128_RATE
        lea     rdi, [rsp+BUF+rdi]
        leadisp rsi, rsp, ST
        mov     rdx, [rsp+NM]
Lmlkem_gen_matrix_copyloop:
        copyblock rdi, rsi
        add     rdi, BUFBYTES
        add     rsi, LANEBYTES
        dec     rdx
        jnz     Lmlkem_gen_matrix_copyloop

        test    QWORD PTR [rsp+FLAGS], 2
        jz      Lmlkem_gen_matrix_noisecbd_done
        mov     lane, [rsp+NM]
Lmlkem_gen_matrix_noisecbd:
        cmp     lane, [rsp+NMAT]
        jae     Lmlkem_gen_matrix_noisecbd_done
        mov     rax, [rsp+NCUR+8*lane]
        test    rax, rax
        js      Lmlkem_gen_matrix_noisecbd_next
        shl     rax, 9
        mov     rdi, [rsp+NOISE+24]
        add     rdi, rax
        laneaddr rsi, lane
        call    S2N_BN_SYMBOL(mlkem_cbd2)
Lmlkem_gen_matrix_noisecbd_next:
        inc     lane
        jmp     Lmlkem_gen_matrix_noisecbd
Lmlkem_gen_matrix_noisecbd_done:
        inc     step
        cmp     step, 3
        jb      Lmlkem_gen_matrix_steploop

// Rejection sampling of the three blocks of each lane, and any more
// blocks needed

        xor     laned, laned
Lmlkem_gen_matrix_rejloop:
        samplepoly
        inc     lane
        cmp     lane, [rsp+NM]
        jb      Lmlkem_gen_matrix_rejloop
        add     idx, [rsp+NM]
        jmp     Lmlkem_gen_matrix_outer

// One polynomial left and no jobs or noise: in lane 0 with the x1
// permutation

Lmlkem_gen_matrix_x1tail:
        xor     laned, laned
        initlane lane, idx
        xor     stepd, stepd
Lmlkem_gen_matrix_x1loop:
        leadisp rdi, rsp, ST
        leadisp rsi, c, MLKEM_C_RC
        call    S2N_BN_SYMBOL(N2_KECCAK_X1)
        imul    rdi, step, SHAKE128_RATE
        lea     rdi, [rsp+BUF+rdi]
        leadisp rsi, rsp, ST
        copyblock rdi, rsi
        inc     step
        cmp     step, 3
        jb      Lmlkem_gen_matrix_x1loop
        samplepoly
        inc     idx
        cmp     idx, [rsp+KK]
        jb      Lmlkem_gen_matrix_x1tail

// Any blocks of the jobs left once the matrix is done (none in the uses
// by ML-KEM, where the jobs finish with the matrix)

Lmlkem_gen_matrix_hashtail:
        mov     rax, [rsp+JOBS+16]
        or      rax, [rsp+JOBS+48]
        jz      Lmlkem_gen_matrix_noisetail
        absorbjob 0
        absorbjob 1
        x4
        finishjob 0
        finishjob 1
        jmp     Lmlkem_gen_matrix_hashtail

// Any noise polynomials left, by mlkem_getnoise

Lmlkem_gen_matrix_noisetail:
        mov     rax, [rsp+NOISE+32]
        mov     rcx, [rsp+NOISE+16]
        cmp     rax, rcx
        jae     Lmlkem_gen_matrix_end
        mov     rdi, rax
        shl     rdi, 9
        add     rdi, [rsp+NOISE+24]
        mov     rsi, [rsp+NOISE]
        mov     rdx, [rsp+NOISE+8]
        add     rdx, rax
        sub     rcx, rax
        mov     r8, rcx
        mov     r9d, 2
        sub     rsp, 16
        mov     [rsp], c
        call    S2N_BN_SYMBOL(N2(mlkem_getnoise))
        add     rsp, 16

// Zero the Keccak state, which may hold secret hash and noise states, and
// return

Lmlkem_gen_matrix_end:
        zerolanes 0, (4*LANEBYTES)
        vzeroupper

        CFI_INC_RSP(FRAME)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(N2(mlkem_gen_matrix))

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
