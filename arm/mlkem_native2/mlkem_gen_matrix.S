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
// 34-byte seed. This is mlkem-native's mlk_gen_matrix (which matches the
// order of the coefficients in the native NTT). The parameter k is 2, 3 or
// 4.
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
// Standard ARM ABI: X0 = a, X1 = rho, X2 = k, X3 = flags, X4 = jobs,
// X5 = noise, X6 = c (the constants block: rc and rej_uniform_table are
// used)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_gen_matrix)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_gen_matrix)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_gen_matrix)
        .text
        .balign 4

// The stack frame: the saved registers, the x4 Keccak state (four
// 200-byte lanes), the three-block output buffers of the four lanes, the
// working copies of the two hash jobs (p = next message byte, r = bytes
// left or -1 after the final block, ds or 0 when inactive, out) and of the
// noise job (sigma, nonce0, n, out and next, the number started), the
// noise polynomial of each lane (-1 if none), the flags argument (bit 0 is
// transposed), the flags of the current pass, the multiplier for division
// by k and the count of a polynomial in the rare case of more blocks.

#define SAVE 0
#define ST 96
#define BUF 896
#define JOBS 2912
#define NOISE 2976
#define NCUR 3024
#define TRANSP 3056
#define FLAGS 3064
#define KDIV 3072
#define RCNT 3080
#define FRAME 3088

#define LANEBYTES 200
#define BUFBYTES 504
#define SHAKE128_RATE 168
#define SHAKE256_RATE 136

// Registers held across calls

#define a x19
#define rho x20
#define k x21
#define nm x22
#define c x23
#define idx x24
#define kk x25
#define nmat x26
#define step x27
#define lane x28

// The domain bytes of SHAKE128 and SHAKE256 (with the final bit, 0x80 in
// the last byte of the block, this is the padding)

#define SHAKE128_DS 0x1f
#define SHAKE256_DS 0x1f

// ----------------------------------------------------------------------------
// Macros for the steps on single lanes. They use only x0-x15 and v0-v18.
// ----------------------------------------------------------------------------

// laneaddr dst, l: dst := the address of lane l (a register) of the state

        .macro laneaddr dst, l
        mov     \dst, #LANEBYTES
        mul     \dst, \l, \dst
        add     \dst, \dst, #ST
        add     \dst, sp, \dst
        .endm

// zerolanes off, len: zero len bytes (a multiple of 16) of the state

        .macro zerolanes off, len
        add     x0, sp, #(ST+\off)
        mov     x1, #(\len)
1:
        stp     xzr, xzr, [x0], #16
        subs    x1, x1, #16
        bne     1b
        .endm

// initlane l, e: set lane l to the absorbed seed of matrix polynomial e
// (registers): rho, the two index bytes, the domain byte 0x1f, zeros and
// the final bit 0x80 in byte 167. The row e / k is (e * m) >> 5 with
// m = 16, 11, 8 for k = 2, 3, 4 (in the frame), exact for e < 16.

        .macro initlane l, e
        laneaddr x0, \l
        ldr     x3, [sp, #KDIV]
        mul     x3, \e, x3
        lsr     x3, x3, #5
        msub    x4, x3, k, \e
        ldr     x5, [sp, #TRANSP]
        tst     x5, #1
        csel    x5, x3, x4, ne
        csel    x6, x4, x3, ne
        orr     x5, x5, x6, lsl #8
        orr     x5, x5, #(SHAKE128_DS << 16)
        ldp     q0, q1, [rho]
        stp     q0, q1, [x0]
        stp     x5, xzr, [x0, #32]
        movi    v0.2d, #0
        stp     q0, q0, [x0, #48]
        stp     q0, q0, [x0, #80]
        stp     q0, q0, [x0, #112]
        str     q0, [x0, #144]
        mov     x5, #0x8000000000000000
        str     x5, [x0, #160]
        stp     xzr, xzr, [x0, #168]
        stp     xzr, xzr, [x0, #184]
        .endm

// initnoise l, i: set lane l to the absorbed seed of noise polynomial i
// (registers): sigma || (nonce0 + i), the domain byte 0x1f, zeros and the
// final bit 0x80 in byte 135.

        .macro initnoise l, i
        laneaddr x0, \l
        add     x2, sp, #NOISE
        ldp     x2, x3, [x2]
        add     x1, \i, x3
        and     x1, x1, #0xff
        orr     x1, x1, #(SHAKE256_DS << 8)
        ldp     q0, q1, [x2]
        stp     q0, q1, [x0]
        stp     x1, xzr, [x0, #32]
        movi    v0.2d, #0
        stp     q0, q0, [x0, #48]
        stp     q0, q0, [x0, #80]
        stp     xzr, xzr, [x0, #112]
        mov     x1, #0x8000000000000000
        stp     x1, xzr, [x0, #128]
        stp     q0, q0, [x0, #144]
        stp     xzr, xzr, [x0, #176]
        str     xzr, [x0, #192]
        .endm

// absorbjob j: absorb the next block of hash job j (0 or 1, a number) into
// its lane (2 or 3), if the job is active (ds is nonzero) and not finished:
// 136 message bytes, or the r < 136 that remain and the padding (the
// domain byte ds at r and 0x80 at 135), setting r = -1 to mark the final
// block.

        .macro absorbjob j
        add     x9, sp, #(JOBS+32*\j)
        ldp     x10, x11, [x9]
        ldr     x8, [x9, #16]
        cbz     x8, 9f
        tbnz    x11, #63, 9f
        add     x12, sp, #(ST+LANEBYTES*(2+\j))
        mov     x13, #SHAKE256_RATE
        cmp     x11, x13
        csel    x14, x11, x13, cc
        mov     x15, x12
        cbz     x14, 2f
1:
        ldr     x2, [x10], #8
        ldr     x3, [x15]
        eor     x3, x3, x2
        str     x3, [x15], #8
        subs    x14, x14, #8
        bne     1b
2:
        cmp     x11, x13
        bcs     3f
        ldrb    w3, [x12, x11]
        eor     w3, w3, w8
        strb    w3, [x12, x11]
        ldrb    w3, [x12, #(SHAKE256_RATE-1)]
        eor     w3, w3, #0x80
        strb    w3, [x12, #(SHAKE256_RATE-1)]
        mov     x11, #-1
        stp     x10, x11, [x9]
        b       9f
3:
        sub     x11, x11, x13
        stp     x10, x11, [x9]
9:
        .endm

// finishjob j: if hash job j has absorbed its final block (and so just been
// permuted), copy the 32-byte digest from its lane and make it inactive
// (ds = 0).

        .macro finishjob j
        add     x9, sp, #(JOBS+32*\j)
        ldp     x11, x10, [x9, #8]
        cbz     x10, 9f
        tbz     x11, #63, 9f
        ldr     x13, [x9, #24]
        add     x12, sp, #(ST+LANEBYTES*(2+\j))
        ldp     q0, q1, [x12]
        stp     q0, q1, [x13]
        str     xzr, [x9, #16]
9:
        .endm

// samplepoly l, e: rejection sampling for matrix polynomial e from the
// three blocks in the buffer of lane l (registers), then, while it has
// fewer than 256 coefficients (the rare case), another block squeezed
// from the lane with the x1 permutation and sampled from the lane
// directly. This calls functions: the lane and polynomial are recomputed
// from l and e, which must be callee-saved registers.

        .macro samplepoly l, e
        add     x0, a, \e, lsl #9
        mov     x2, #BUFBYTES
        mul     x2, \l, x2
        add     x2, x2, #BUF
        add     x2, sp, x2
        mov     x1, #0
        mov     x3, #BUFBYTES
        add     x4, c, #MLKEM_C_REJ_UNIFORM_TABLE
        bl      S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME)
1:
        cmp     x0, #256
        bcs     2f
        str     x0, [sp, #RCNT]
        laneaddr x0, \l
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak_f1600)
        add     x0, a, \e, lsl #9
        ldr     x1, [sp, #RCNT]
        laneaddr x2, \l
        mov     x3, #SHAKE128_RATE
        add     x4, c, #MLKEM_C_REJ_UNIFORM_TABLE
        bl      S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME)
        b       1b
2:
        .endm

// copyblock dst, src: copy the 168 bytes of a SHAKE128 block

        .macro copyblock dst, src
        ldp     q0, q1, [\src]
        ldp     q2, q3, [\src, #32]
        ldp     q4, q5, [\src, #64]
        ldp     q6, q7, [\src, #96]
        ldp     q16, q17, [\src, #128]
        ldr     d18, [\src, #160]
        stp     q0, q1, [\dst]
        stp     q2, q3, [\dst, #32]
        stp     q4, q5, [\dst, #64]
        stp     q6, q7, [\dst, #96]
        stp     q16, q17, [\dst, #128]
        str     d18, [\dst, #160]
        .endm

// ----------------------------------------------------------------------------
// The function
// ----------------------------------------------------------------------------

S2N_BN_SYMBOL(mlkem_gen_matrix):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_DEC_SP(FRAME)
        CFI_STACKSAVE2X(x19,x20,SAVE,SAVE+8)
        CFI_STACKSAVE2X(x21,x22,SAVE+16,SAVE+24)
        CFI_STACKSAVE2X(x23,x24,SAVE+32,SAVE+40)
        CFI_STACKSAVE2X(x25,x26,SAVE+48,SAVE+56)
        CFI_STACKSAVE2X(x27,x28,SAVE+64,SAVE+72)
        CFI_STACKSAVE2X(x29,x30,SAVE+80,SAVE+88)

        mov     a, x0
        mov     rho, x1
        mov     k, x2
        str     x3, [sp, #TRANSP]
        mov     x7, #16
        cmp     k, #3
        mov     x8, #11
        csel    x7, x8, x7, eq
        cmp     k, #4
        mov     x8, #8
        csel    x7, x8, x7, eq
        str     x7, [sp, #KDIV]
        mov     c, x6
        mul     kk, k, k
        mov     idx, #0

// Copy the noise job (bit 2 of the flags), with next = 0, or make it empty
// (n = 0)

        add     x6, sp, #NOISE
        stp     xzr, xzr, [x6, #16]
        str     xzr, [x6, #32]
        tbz     x3, #2, Lmlkem_gen_matrix_nonoise
        ldp     q0, q1, [x5]
        stp     q0, q1, [x6]
Lmlkem_gen_matrix_nonoise:

// Copy the hash jobs (bit 1), or make them inactive (ds = 0), and zero
// their lanes 2 and 3

        add     x6, sp, #JOBS
        tbz     x3, #1, Lmlkem_gen_matrix_nojobs
        ldp     q0, q1, [x4]
        ldp     q2, q3, [x4, #32]
        stp     q0, q1, [x6]
        stp     q2, q3, [x6, #32]
        b       Lmlkem_gen_matrix_jobsdone
Lmlkem_gen_matrix_nojobs:
        str     xzr, [x6, #16]
        str     xzr, [x6, #48]
Lmlkem_gen_matrix_jobsdone:
        zerolanes (2*LANEBYTES), (2*LANEBYTES)

// The main loop: each pass samples nm polynomials in lanes 0..nm-1, where
// nm = min(nmat, the number left) and nmat is four if no hash job is
// active, three if only job 1 (lane 3) is, two if job 0 (lane 2) is. The
// lanes nm..nmat-1 are idle, and take noise polynomials, one block each, a
// new one at each step. When at most two polynomials remain, no hash job
// is active and there is no noise left, they are sampled one at a time
// with the x1 permutation instead, which is cheaper than an x4 one with
// lanes left idle.

Lmlkem_gen_matrix_outer:
        cmp     idx, kk
        bcs     Lmlkem_gen_matrix_hashtail
        mov     nmat, #4
        ldr     x0, [sp, #(JOBS+48)]
        cmp     x0, #0
        mov     x1, #3
        csel    nmat, x1, nmat, ne
        ldr     x0, [sp, #(JOBS+16)]
        cmp     x0, #0
        mov     x1, #2
        csel    nmat, x1, nmat, ne
        sub     x2, kk, idx
        cmp     nmat, #4
        ccmp    x2, #2, #2, eq
        bhi     Lmlkem_gen_matrix_pass
        ldr     x3, [sp, #(NOISE+16)]
        ldr     x4, [sp, #(NOISE+32)]
        cmp     x4, x3
        bcs     Lmlkem_gen_matrix_x1tail
Lmlkem_gen_matrix_pass:
        cmp     nmat, x2
        csel    nm, x2, nmat, hi

// Initialize the lanes of the polynomials idx .. idx+nm-1

        mov     lane, #0
Lmlkem_gen_matrix_initloop:
        add     x1, idx, lane
        initlane lane, x1
        add     lane, lane, #1
        cmp     lane, nm
        bcc     Lmlkem_gen_matrix_initloop

// Three steps: give each idle lane the next noise polynomial if any,
// absorb a block of each active hash job, permute, copy a block of output
// of each matrix polynomial's lane to its buffer, and sample each noise
// polynomial from its lane. Whether there are hash jobs or noise to do
// is decided once for the pass, the flags being kept in the frame
// (bit 0: hash jobs active, bit 1: idle lanes and noise left).

        ldr     x0, [sp, #(JOBS+16)]
        ldr     x1, [sp, #(JOBS+48)]
        orr     x0, x0, x1
        cmp     x0, #0
        cset    x2, ne
        ldr     x3, [sp, #(NOISE+16)]
        ldr     x4, [sp, #(NOISE+32)]
        cmp     x4, x3
        ccmp    nm, nmat, #2, cc
        cset    x1, cc
        orr     x2, x2, x1, lsl #1
        str     x2, [sp, #FLAGS]

        mov     step, #0
Lmlkem_gen_matrix_steploop:
        ldr     x2, [sp, #FLAGS]
        tbz     x2, #1, Lmlkem_gen_matrix_noiseinit_done
        mov     lane, nm
Lmlkem_gen_matrix_noiseinit:
        cmp     lane, nmat
        bcs     Lmlkem_gen_matrix_noiseinit_done
        add     x9, sp, #NCUR
        mov     x0, #-1
        str     x0, [x9, lane, lsl #3]
        ldr     x3, [sp, #(NOISE+16)]
        ldr     x4, [sp, #(NOISE+32)]
        cmp     x4, x3
        bcs     Lmlkem_gen_matrix_noiseinit_next
        str     x4, [x9, lane, lsl #3]
        add     x5, x4, #1
        str     x5, [sp, #(NOISE+32)]
        initnoise lane, x4
Lmlkem_gen_matrix_noiseinit_next:
        add     lane, lane, #1
        b       Lmlkem_gen_matrix_noiseinit
Lmlkem_gen_matrix_noiseinit_done:
        ldr     x2, [sp, #FLAGS]
        tbz     x2, #0, Lmlkem_gen_matrix_nohash1
        absorbjob 0
        absorbjob 1
Lmlkem_gen_matrix_nohash1:
        add     x0, sp, #ST
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak4_f1600_alt2)
        ldr     x2, [sp, #FLAGS]
        tbz     x2, #0, Lmlkem_gen_matrix_nohash2
        finishjob 0
        finishjob 1
Lmlkem_gen_matrix_nohash2:

// Copy the block of each of the nm lanes 0..nm-1 to offset 168 * step of
// its buffer (the buffers 504 bytes apart, the lanes 200)

        mov     x4, #SHAKE128_RATE
        mul     x0, step, x4
        add     x0, x0, #BUF
        add     x0, sp, x0
        add     x1, sp, #ST
        mov     x2, nm
Lmlkem_gen_matrix_copyloop:
        copyblock x0, x1
        add     x0, x0, #BUFBYTES
        add     x1, x1, #LANEBYTES
        subs    x2, x2, #1
        bne     Lmlkem_gen_matrix_copyloop

        ldr     x2, [sp, #FLAGS]
        tbz     x2, #1, Lmlkem_gen_matrix_noisecbd_done
        mov     lane, nm
Lmlkem_gen_matrix_noisecbd:
        cmp     lane, nmat
        bcs     Lmlkem_gen_matrix_noisecbd_done
        add     x9, sp, #NCUR
        ldr     x0, [x9, lane, lsl #3]
        tbnz    x0, #63, Lmlkem_gen_matrix_noisecbd_next
        ldr     x1, [sp, #(NOISE+24)]
        add     x0, x1, x0, lsl #9
        laneaddr x1, lane
        bl      S2N_BN_SYMBOL(mlkem_cbd2)
Lmlkem_gen_matrix_noisecbd_next:
        add     lane, lane, #1
        b       Lmlkem_gen_matrix_noisecbd
Lmlkem_gen_matrix_noisecbd_done:
        add     step, step, #1
        cmp     step, #3
        bcc     Lmlkem_gen_matrix_steploop

// Rejection sampling of the three blocks of each lane, and any more
// blocks needed

        mov     lane, #0
Lmlkem_gen_matrix_rejloop:
        add     step, idx, lane
        samplepoly lane, step
        add     lane, lane, #1
        cmp     lane, nm
        bcc     Lmlkem_gen_matrix_rejloop
        add     idx, idx, nm
        b       Lmlkem_gen_matrix_outer

// One or two polynomials left and no jobs or noise: one at a time in lane 0
// with the x1 permutation

Lmlkem_gen_matrix_x1tail:
        mov     lane, #0
        initlane lane, idx
        mov     step, #0
Lmlkem_gen_matrix_x1loop:
        add     x0, sp, #ST
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak_f1600)
        mov     x4, #SHAKE128_RATE
        mul     x0, step, x4
        add     x0, x0, #BUF
        add     x0, sp, x0
        add     x1, sp, #ST
        copyblock x0, x1
        add     step, step, #1
        cmp     step, #3
        bcc     Lmlkem_gen_matrix_x1loop
        samplepoly lane, idx
        add     idx, idx, #1
        cmp     idx, kk
        bcc     Lmlkem_gen_matrix_x1tail

// Any blocks of the jobs left once the matrix is done (none in the uses
// by ML-KEM, where the jobs finish with the matrix)

Lmlkem_gen_matrix_hashtail:
        ldr     x0, [sp, #(JOBS+16)]
        ldr     x1, [sp, #(JOBS+48)]
        orr     x0, x0, x1
        cbz     x0, Lmlkem_gen_matrix_noisetail
        absorbjob 0
        absorbjob 1
        add     x0, sp, #ST
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak4_f1600_alt2)
        finishjob 0
        finishjob 1
        b       Lmlkem_gen_matrix_hashtail

// Any noise polynomials left, by mlkem_getnoise

Lmlkem_gen_matrix_noisetail:
        add     x9, sp, #NOISE
        ldp     x1, x2, [x9]
        ldp     x3, x4, [x9, #16]
        ldr     x5, [x9, #32]
        cmp     x5, x3
        bcs     Lmlkem_gen_matrix_end
        add     x0, x4, x5, lsl #9
        add     x2, x2, x5
        sub     x3, x3, x5
        mov     x4, x3
        mov     x5, #2
        mov     x6, c
        bl      S2N_BN_SYMBOL(mlkem_getnoise)

// Zero the Keccak state, which may hold secret hash and noise states, and
// return

Lmlkem_gen_matrix_end:
        zerolanes 0, (4*LANEBYTES)

        CFI_STACKLOAD2(x19,x20,SAVE)
        CFI_STACKLOAD2(x21,x22,SAVE+16)
        CFI_STACKLOAD2(x23,x24,SAVE+32)
        CFI_STACKLOAD2(x25,x26,SAVE+48)
        CFI_STACKLOAD2(x27,x28,SAVE+64)
        CFI_STACKLOAD2(x29,x30,SAVE+80)
        CFI_INC_SP(FRAME)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_gen_matrix)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
