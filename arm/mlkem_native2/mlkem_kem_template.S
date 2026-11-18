// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The ML-KEM key encapsulation mechanism of FIPS 203, one parameter set
//
// This template is included by mlkem512.S, mlkem768.S and mlkem1024.S
// with MLKEM_K = 2, 3 or 4 and MLKEM_L = 256 * MLKEM_K, and gives the
// functions of mlkem-native's API for that parameter set ML-KEM-L, with
// the same results:
//
//   int mlkemL_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins)
//   int mlkemL_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
//                         const uint8_t *coins)
//   int mlkemL_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
//   int mlkemL_check_pk(const uint8_t *pk)
//   int mlkemL_check_sk(const uint8_t *sk)
//
// with L = 256 * MLKEM_K: ML-KEM.KeyGen_internal (Algorithm 16) with
// coins = d || z, ML-KEM.Encaps_internal (Algorithm 17) with coins = m
// after the encapsulation key check, ML-KEM.Decaps_internal (Algorithm 18)
// after the decapsulation key (hash) check, and the two checks (section
// 7). They return 0, or -4 (MLK_ERR_INVALID_PK) or -5 (MLK_ERR_INVALID_SK)
// when a check fails, in which case nothing is written.
//
// Two internal functions are shared by enc_derand and dec:
//
//   void mlkemL_pke_encrypt(uint8_t *ct, const int16_t *at,
//                           const uint8_t *pk, const uint8_t m[32],
//                           int16_t *noise)
//   void mlkemL_pke_decrypt(uint8_t m[32], const uint8_t *ct,
//                           const uint8_t *sk)
//
// K-PKE.Encrypt (Algorithm 14) given the transposed matrix at sampled from
// the seed of pk and the noise sampled from r, and K-PKE.Decrypt
// (Algorithm 15).
//
// The structure differs from mlkem-native's in how the Keccak work is
// scheduled over the lanes of the x4 permutation: H(pk), and in
// decapsulation J(z || c), are computed in lanes beside the sampling of
// the matrix, and noise is sampled in lanes the matrix leaves idle (see
// mlkem_gen_matrix). Otherwise the steps are those of FIPS 203 as
// implemented by mlkem-native, with its native AArch64 kernels.
//
// All functions are constant-time in the secret data (and the checks'
// results are public); the stack buffers holding secrets are zeroed
// before returning.
// ----------------------------------------------------------------------------

// The including file has included _internal_s2n_bignum_arm.h and
// mlkem_native2_consts.h.

// Assembled on its own rather than included by mlkem512.S, mlkem768.S
// or mlkem1024.S (as by a build that takes every .S file), the
// template is empty.

#if defined(MLKEM_K)

// The parameters

#define N 256
#define POLYBYTES 384
#define K MLKEM_K
#define VECBYTES (POLYBYTES * K)
#define PKBYTES (VECBYTES + 32)
#define SKBYTES (2 * VECBYTES + 96)

#if MLKEM_K == 2
#define ETA1 3
#define DU 10
#define DV 4
#elif MLKEM_K == 3
#define ETA1 2
#define DU 10
#define DV 4
#elif MLKEM_K == 4
#define ETA1 2
#define DU 11
#define DV 5
#else
#error "MLKEM_K must be 2, 3 or 4"
#endif

#define CTBYTES (32 * (DU * K + DV))
#define DUBYTES (32 * DU)

#define ERR_INVALID_PK -4
#define ERR_INVALID_SK -5

// The flags of mlkem_gen_matrix: the matrix transposed, hash jobs given,
// and a noise job given (used when eta1 = 2)

#define GM_TRANSPOSED 1
#define GM_JOBS 2
#if ETA1 == 2
#define GM_NOISE 4
#else
#define GM_NOISE 0
#endif

// Names: FN(f) is mlkemL_f, and the kernels for this K and du, dv

#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)
#define FN(f) CAT(CAT(mlkem, MLKEM_L), CAT(_, f))
// LFN(f) for the labels inside the functions: FN(f) with an L prefix,
// which keeps the label local to the object on Mach-O
#define LFN(f) CAT(L, FN(f))
#define BASEMUL CAT(CAT(mlkem_basemul_k, MLKEM_K), _alt)
#define COMPRESS_DU CAT(mlkem_compress_d, DU)
#define COMPRESS_DV CAT(mlkem_compress_d, DV)
#define DECOMPRESS_DU CAT(mlkem_decompress_d, DU)
#define DECOMPRESS_DV CAT(mlkem_decompress_d, DV)

        .text
        .balign 4

// ----------------------------------------------------------------------------
// Assembler macros for the frames, which may exceed the 12-bit immediates
// ----------------------------------------------------------------------------

// fadd reg, off: reg := sp + off

        .macro fadd reg, off
        .if (\off) < 4096
        add     \reg, sp, #(\off)
        .else
        add     \reg, sp, #((\off) & 0xfff)
        add     \reg, \reg, #((\off) >> 12), lsl #12
        .endif
        .endm

// addoff dst, base, off: dst := base + off

        .macro addoff dst, base, off
        .if (\off) < 4096
        add     \dst, \base, #(\off)
        .else
        add     \dst, \base, #((\off) & 0xfff)
        add     \dst, \dst, #((\off) >> 12), lsl #12
        .endif
        .endm

// framealloc size / framefree size: adjust sp by a frame size

        .macro framealloc size
        .if (\size) < 4096
        sub     sp, sp, #(\size)
        .else
        sub     sp, sp, #((\size) & 0xfff)
        sub     sp, sp, #((\size) >> 12), lsl #12
        .endif
        .endm

        .macro framefree size
        .if (\size) < 4096
        add     sp, sp, #(\size)
        .else
        add     sp, sp, #((\size) & 0xfff)
        add     sp, sp, #((\size) >> 12), lsl #12
        .endif
        .endm

// saveregs / restoreregs: x19-x30 at the bottom of the frame

        .macro saveregs
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        stp     x29, x30, [sp, #80]
        .endm

        .macro restoreregs
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldp     x29, x30, [sp, #80]
        .endm

// consts reg: reg := the address of the constants block

        .macro consts reg
#if defined(__ELF__)
        adrp    \reg, S2N_BN_SYMBOL(mlkem_native2_constants)
        add     \reg, \reg, :lo12:S2N_BN_SYMBOL(mlkem_native2_constants)
#else
        adrp    \reg, S2N_BN_SYMBOL(mlkem_native2_constants)@PAGE
        add     \reg, \reg, S2N_BN_SYMBOL(mlkem_native2_constants)@PAGEOFF
#endif
        .endm

// declassify reg, len: in a build for constant-time testing under valgrind
// (MLKEM_CT_TESTING defined), mark the len bytes at reg as defined, i.e.
// public, with memcheck's client request (the special sequence of
// rotations by 3, 13, 51 and 61 and orr x10, x10, x10, with x4 pointing at
// the request and its arguments and x3 the default result); otherwise
// nothing. It clobbers x3, x4 and x9.

        .macro declassify reg, len
#if defined(MLKEM_CT_TESTING)
        sub     sp, sp, #48
        movz    x9, #0x0002
        movk    x9, #0x4d43, lsl #16
        stp     x9, \reg, [sp]
        mov     x9, #(\len)
        stp     x9, xzr, [sp, #16]
        stp     xzr, xzr, [sp, #32]
        mov     x3, #0
        mov     x4, sp
        ror     x12, x12, #3
        ror     x12, x12, #13
        ror     x12, x12, #51
        ror     x12, x12, #61
        orr     x10, x10, x10
        add     sp, sp, #48
#endif
        .endm

// zero off, len: zero len bytes (a multiple of 32) of the frame at off

        .macro zero off, len
        fadd    x0, \off
        mov     x1, #(\len)
        movi    v0.2d, #0
1:
        stp     q0, q0, [x0], #32
        subs    x1, x1, #32
        bne     1b
        .endm

// copy32 dst, src: copy 32 bytes (dst and src registers)

        .macro copy32 dst, src
        ldp     q0, q1, [\src]
        stp     q0, q1, [\dst]
        .endm

// ----------------------------------------------------------------------------
// The polynomial-vector steps of K-PKE, as sequences of kernel calls.
// The constants block is in x28 throughout.
// ----------------------------------------------------------------------------

// ntt off: the NTT of the K polynomials of the vector at off

        .macro ntt off
        .set i, 0
        .rept K
        fadd    x0, ((\off) + 512 * i)
        add     x1, x28, #MLKEM_C_NTT_ZETAS_12345
        add     x2, x28, #MLKEM_C_NTT_ZETAS_67
        bl      S2N_BN_SYMBOL(mlkem_ntt_alt)
        .set i, i + 1
        .endr
        .endm

// intt off, n: the inverse NTT of n polynomials at off

        .macro intt off, n
        .set i, 0
        .rept \n
        fadd    x0, ((\off) + 512 * i)
        add     x1, x28, #MLKEM_C_INTT_ZETAS_12345
        add     x2, x28, #MLKEM_C_INTT_ZETAS_67
        bl      S2N_BN_SYMBOL(mlkem_intt_alt)
        .set i, i + 1
        .endr
        .endm

// mulcache dst, src: the mulcaches of the K polynomials of the vector at
// src, 256 bytes each, at dst

        .macro mulcache dst, src
        .set i, 0
        .rept K
        fadd    x0, ((\dst) + 256 * i)
        fadd    x1, ((\src) + 512 * i)
        add     x2, x28, #MLKEM_C_MULCACHE_ZETAS
        add     x3, x28, #MLKEM_C_MULCACHE_ZETAS_TWISTED
        bl      S2N_BN_SYMBOL(mlkem_mulcache_compute)
        .set i, i + 1
        .endr
        .endm

// ----------------------------------------------------------------------------
// int FN(check_pk)(const uint8_t *pk): the modulus check of FIPS 203,
// that ByteEncode_12(ByteDecode_12(t)) = t for the polynomial vector t at
// the start of pk; 0 if it holds, else -4.
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(check_pk))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(check_pk))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(check_pk))

S2N_BN_SYMBOL(FN(check_pk)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_PUSH2(x29, x30)
        mov     x1, #K
        bl      S2N_BN_SYMBOL(mlkem_check_encoding)
        mov     w1, #ERR_INVALID_PK
        cmp     x0, #0
        csel    w0, w1, wzr, eq
        CFI_POP2(x29, x30)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(check_pk))

// ----------------------------------------------------------------------------
// int FN(check_sk)(const uint8_t *sk): the hash check of FIPS 203, that
// H(ek) = h for the encapsulation key ek and the hash h in sk; 0 if it
// holds, else -5.
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(check_sk))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(check_sk))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(check_sk))

#define CSK_H 32
#define CSK_FRAME 64

S2N_BN_SYMBOL(FN(check_sk)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_DEC_SP(CSK_FRAME)
        stp     x19, x30, [sp]
        mov     x19, x0
        add     x0, sp, #CSK_H
        add     x1, x19, #VECBYTES
        mov     x2, #PKBYTES
        consts  x3
        bl      S2N_BN_SYMBOL(mlkem_hash_h)
        add     x0, sp, #CSK_H
        add     x1, x19, #(SKBYTES - 64)
        ldp     x2, x3, [x0]
        ldp     x4, x5, [x0, #16]
        ldp     x6, x7, [x1]
        ldp     x8, x9, [x1, #16]
        eor     x2, x2, x6
        eor     x3, x3, x7
        eor     x4, x4, x8
        eor     x5, x5, x9
        orr     x2, x2, x3
        orr     x4, x4, x5
        orr     x2, x2, x4
        mov     w1, #ERR_INVALID_SK
        cmp     x2, #0
        csel    w0, wzr, w1, eq
        ldp     x19, x30, [sp]
        CFI_INC_SP(CSK_FRAME)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(check_sk))

// ----------------------------------------------------------------------------
// int FN(keypair_derand)(uint8_t *pk, uint8_t *sk, const uint8_t *coins)
//
// K-PKE.KeyGen(d) for d = coins[0..31]: (rho, sigma) = G(d || K), the
// matrix from rho, s and e from sigma with eta1, t = A s + e in the NTT
// domain; pk = ByteEncode_12(t) || rho and sk = ByteEncode_12(s) || pk ||
// H(pk) || z with z = coins[32..63].
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(keypair_derand))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(keypair_derand))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(keypair_derand))

// The frame: G's input d || K, its output rho || sigma, the noise job, the
// matrix, s and e (consecutive, as sampled together), the mulcache of s,
// and t.

#define KP_GIN 96
#define KP_G 160
#define KP_NJOB 224
#define KP_A 256
#define KP_S (KP_A + 512 * K * K)
#define KP_E (KP_S + 512 * K)
#define KP_SC (KP_E + 512 * K)
#define KP_T (KP_SC + 256 * K)
#define KP_FRAME (KP_T + 512 * K)

S2N_BN_SYMBOL(FN(keypair_derand)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        framealloc KP_FRAME
        saveregs
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        consts  x28

// (rho, sigma) = G(d || K)

        fadd    x0, KP_GIN
        copy32  x0, x21
        mov     w1, #K
        strb    w1, [x0, #32]
        fadd    x0, KP_G
        fadd    x1, KP_GIN
        mov     x2, #33
        mov     x3, x28
        bl      S2N_BN_SYMBOL(mlkem_hash_g)

// rho is public, although computed from the secret d

        fadd    x5, KP_G
        declassify x5, 32

// The matrix A and the noise s, e: for eta1 = 2 the noise is sampled in
// lanes left idle by the matrix, otherwise separately

#if ETA1 == 2
        fadd    x5, KP_NJOB
        fadd    x0, (KP_G + 32)
        mov     x1, #0
        stp     x0, x1, [x5]
        mov     x0, #(2 * K)
        fadd    x1, KP_S
        stp     x0, x1, [x5, #16]
#else
        mov     x5, #0
#endif
        fadd    x0, KP_A
        fadd    x1, KP_G
        mov     x2, #K
        mov     x3, #GM_NOISE
        mov     x4, #0
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_gen_matrix)
#if ETA1 != 2
        fadd    x0, KP_S
        fadd    x1, (KP_G + 32)
        mov     x2, #0
        mov     x3, #(2 * K)
        mov     x4, #(2 * K)
        mov     x5, #ETA1
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_getnoise)
#endif

// t = A s + e in the NTT domain, reduced

        ntt     KP_S
        ntt     KP_E
        mulcache KP_SC, KP_S
        .set j, 0
        .rept K
        fadd    x0, (KP_T + 512 * j)
        fadd    x1, (KP_A + 512 * K * j)
        fadd    x2, KP_S
        fadd    x3, KP_SC
        bl      S2N_BN_SYMBOL(BASEMUL)
        fadd    x0, (KP_T + 512 * j)
        bl      S2N_BN_SYMBOL(mlkem_tomont)
        fadd    x0, (KP_T + 512 * j)
        fadd    x1, (KP_E + 512 * j)
        bl      S2N_BN_SYMBOL(mlkem_add_reduce)
        fadd    x0, (KP_S + 512 * j)
        bl      S2N_BN_SYMBOL(mlkem_reduce)
        .set j, j + 1
        .endr

// pk = ByteEncode_12(t) || rho, sk = ByteEncode_12(s) || pk || H(pk) || z

        .set j, 0
        .rept K
        add     x0, x19, #(POLYBYTES * j)
        fadd    x1, (KP_T + 512 * j)
        bl      S2N_BN_SYMBOL(mlkem_tobytes_alt)
        add     x0, x20, #(POLYBYTES * j)
        fadd    x1, (KP_S + 512 * j)
        bl      S2N_BN_SYMBOL(mlkem_tobytes_alt)
        .set j, j + 1
        .endr
        add     x0, x19, #VECBYTES
        fadd    x1, KP_G
        copy32  x0, x1
        add     x0, x20, #VECBYTES
        mov     x1, x19
        mov     x2, #(PKBYTES / 32)
LFN(keypair_copypk):
        ldp     q0, q1, [x1], #32
        stp     q0, q1, [x0], #32
        subs    x2, x2, #1
        bne     LFN(keypair_copypk)
        add     x0, x20, #(SKBYTES - 64)
        mov     x1, x19
        mov     x2, #PKBYTES
        mov     x3, x28
        bl      S2N_BN_SYMBOL(mlkem_hash_h)
        add     x0, x20, #(SKBYTES - 32)
        add     x1, x21, #32
        copy32  x0, x1

// Zero the secrets: d, sigma, s, e and their mulcache (t is public)

        zero    KP_GIN, (KP_A - KP_GIN)
        zero    KP_S, (KP_T - KP_S)

        mov     w0, #0
        restoreregs
        framefree KP_FRAME
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(keypair_derand))

// ----------------------------------------------------------------------------
// void FN(pke_encrypt)(uint8_t *ct, const int16_t *at, const uint8_t *pk,
//                      const uint8_t m[32], int16_t *noise)
//
// K-PKE.Encrypt(pk, m, r) given the transposed matrix at sampled from the
// seed of pk and the noise noise = y || e1 || e2 (2 * K + 1 polynomials)
// sampled from r (with eta1, eta2 = 2): u = InvNTT(A^T NTT(y)) + e1 and
// v = InvNTT(t^T NTT(y)) + e2 + Decompress_1(m), and ct = Compress_du(u) ||
// Compress_dv(v). The noise y is replaced by NTT(y).
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(pke_encrypt))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(pke_encrypt))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(pke_encrypt))

// The frame: the mulcache of y, t from pk, u, v and the polynomial of m.
// The noise is in x23: y, e1, e2 at offsets 0, 512 * K, 1024 * K.

#define PE_YC 96
#define PE_T (PE_YC + 256 * K)
#define PE_U (PE_T + 512 * K)
#define PE_V (PE_U + 512 * K)
#define PE_M (PE_V + 512)
#define PE_FRAME (PE_M + 512)

S2N_BN_SYMBOL(FN(pke_encrypt)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        framealloc PE_FRAME
        saveregs
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        mov     x22, x3
        mov     x23, x4
        consts  x28

        .set j, 0
        .rept K
        fadd    x0, (PE_T + 512 * j)
        add     x1, x21, #(POLYBYTES * j)
        bl      S2N_BN_SYMBOL(mlkem_frombytes)
        .set j, j + 1
        .endr
        fadd    x0, PE_M
        mov     x1, x22
        bl      S2N_BN_SYMBOL(mlkem_frommsg)

// NTT(y) and its mulcache

        .set j, 0
        .rept K
        add     x0, x23, #(512 * j)
        add     x1, x28, #MLKEM_C_NTT_ZETAS_12345
        add     x2, x28, #MLKEM_C_NTT_ZETAS_67
        bl      S2N_BN_SYMBOL(mlkem_ntt_alt)
        fadd    x0, (PE_YC + 256 * j)
        add     x1, x23, #(512 * j)
        add     x2, x28, #MLKEM_C_MULCACHE_ZETAS
        add     x3, x28, #MLKEM_C_MULCACHE_ZETAS_TWISTED
        bl      S2N_BN_SYMBOL(mlkem_mulcache_compute)
        .set j, j + 1
        .endr

// u = InvNTT(A^T y) + e1, v = InvNTT(t^T y) + e2 + m, all reduced

        .set j, 0
        .rept K
        fadd    x0, (PE_U + 512 * j)
        addoff  x1, x20, (512 * K * j)
        mov     x2, x23
        fadd    x3, PE_YC
        bl      S2N_BN_SYMBOL(BASEMUL)
        .set j, j + 1
        .endr
        fadd    x0, PE_V
        fadd    x1, PE_T
        mov     x2, x23
        fadd    x3, PE_YC
        bl      S2N_BN_SYMBOL(BASEMUL)
        intt    PE_U, (K + 1)
        .set j, 0
        .rept K
        fadd    x0, (PE_U + 512 * j)
        addoff  x1, x23, (512 * (K + j))
        bl      S2N_BN_SYMBOL(mlkem_add_reduce)
        .set j, j + 1
        .endr
        fadd    x0, PE_V
        addoff  x1, x23, (1024 * K)
        bl      S2N_BN_SYMBOL(mlkem_add_reduce)
        fadd    x0, PE_V
        fadd    x1, PE_M
        bl      S2N_BN_SYMBOL(mlkem_add_reduce)

// ct = Compress_du(u) || Compress_dv(v)

        .set j, 0
        .rept K
        add     x0, x19, #(DUBYTES * j)
        fadd    x1, (PE_U + 512 * j)
        bl      S2N_BN_SYMBOL(COMPRESS_DU)
        .set j, j + 1
        .endr
        add     x0, x19, #(DUBYTES * K)
        fadd    x1, PE_V
        bl      S2N_BN_SYMBOL(COMPRESS_DV)

// Zero the secrets: everything but t (the noise is the caller's)

        zero    PE_YC, (PE_T - PE_YC)
        zero    PE_U, (PE_FRAME - PE_U)

        restoreregs
        framefree PE_FRAME
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(pke_encrypt))

// ----------------------------------------------------------------------------
// int FN(enc_derand)(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
//                    const uint8_t *coins)
//
// After the encapsulation key check: (K, r) = G(m || H(pk)) for
// m = coins[0..31], with H(pk) computed beside the sampling of the
// transposed matrix (except for K = 2, where it is separate), then the
// noise from r, ct = K-PKE.Encrypt(pk, m, r) and ss = K.
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(enc_derand))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(enc_derand))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(enc_derand))

// The frame: G's input m || H(pk), its output K || r, the hash job for
// H(pk), the noise y || e1 || e2 and the transposed matrix.

#define EN_GIN 96
#define EN_KR 160
#define EN_JOBS 224
#define EN_NOISE 288
#define EN_AT (EN_NOISE + 512 * (2 * K + 1))
#define EN_FRAME (EN_AT + 512 * K * K)

S2N_BN_SYMBOL(FN(enc_derand)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        framealloc EN_FRAME
        saveregs
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        mov     x22, x3
        consts  x28

        mov     x0, x21
        mov     x1, #K
        bl      S2N_BN_SYMBOL(mlkem_check_encoding)
        cbz     x0, LFN(enc_invalid)

        fadd    x0, EN_GIN
        copy32  x0, x22

// The transposed matrix, and H(pk) beside it as job 1 (lane 3), except
// for K = 2, where two x1 permutations on their own beat a third x4 pass

#if MLKEM_K == 2
        fadd    x0, (EN_GIN + 32)
        mov     x1, x21
        mov     x2, #PKBYTES
        mov     x3, x28
        bl      S2N_BN_SYMBOL(mlkem_hash_h)
        mov     x4, #0
#define EN_GM_FLAGS GM_TRANSPOSED
#else
        fadd    x4, EN_JOBS
        stp     xzr, xzr, [x4]
        stp     xzr, xzr, [x4, #16]
        mov     x0, #PKBYTES
        stp     x21, x0, [x4, #32]
        mov     x0, #0x06
        fadd    x1, (EN_GIN + 32)
        stp     x0, x1, [x4, #48]
#define EN_GM_FLAGS (GM_TRANSPOSED + GM_JOBS)
#endif
        fadd    x0, EN_AT
        add     x1, x21, #VECBYTES
        mov     x2, #K
        mov     x3, #EN_GM_FLAGS
        mov     x5, #0
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_gen_matrix)

// (K, r) = G(m || H(pk)), the noise from r, ct = K-PKE.Encrypt(pk, m, r),
// ss = K

        fadd    x0, EN_KR
        fadd    x1, EN_GIN
        mov     x2, #64
        mov     x3, x28
        bl      S2N_BN_SYMBOL(mlkem_hash_g)
        fadd    x0, EN_NOISE
        fadd    x1, (EN_KR + 32)
        mov     x2, #0
        mov     x3, #(2 * K + 1)
        mov     x4, #K
        mov     x5, #ETA1
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_getnoise)
        mov     x0, x19
        fadd    x1, EN_AT
        mov     x2, x21
        fadd    x3, EN_GIN
        fadd    x4, EN_NOISE
        bl      S2N_BN_SYMBOL(FN(pke_encrypt))
        fadd    x1, EN_KR
        copy32  x20, x1

        zero    EN_GIN, (EN_AT - EN_GIN)
        mov     w0, #0
        b       LFN(enc_return)
LFN(enc_invalid):
        mov     w0, #ERR_INVALID_PK
LFN(enc_return):
        restoreregs
        framefree EN_FRAME
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(enc_derand))

// ----------------------------------------------------------------------------
// void FN(pke_decrypt)(uint8_t m[32], const uint8_t *ct, const uint8_t *sk)
//
// K-PKE.Decrypt(sk, ct): u = Decompress_du of the first part of ct,
// v = Decompress_dv of the rest, s from sk, w = v - InvNTT(s^T NTT(u)),
// and m = ByteEncode_1(Compress_1(w)).
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(pke_decrypt))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(pke_decrypt))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(pke_decrypt))

// The frame: u, its mulcache, v, s and s^T u

#define PD_U 96
#define PD_UC (PD_U + 512 * K)
#define PD_V (PD_UC + 256 * K)
#define PD_S (PD_V + 512)
#define PD_W (PD_S + 512 * K)
#define PD_FRAME (PD_W + 512)

S2N_BN_SYMBOL(FN(pke_decrypt)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        framealloc PD_FRAME
        saveregs
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        consts  x28

        .set j, 0
        .rept K
        fadd    x0, (PD_U + 512 * j)
        add     x1, x20, #(DUBYTES * j)
        bl      S2N_BN_SYMBOL(DECOMPRESS_DU)
        fadd    x0, (PD_S + 512 * j)
        add     x1, x21, #(POLYBYTES * j)
        bl      S2N_BN_SYMBOL(mlkem_frombytes)
        .set j, j + 1
        .endr
        fadd    x0, PD_V
        add     x1, x20, #(DUBYTES * K)
        bl      S2N_BN_SYMBOL(DECOMPRESS_DV)

        ntt     PD_U
        mulcache PD_UC, PD_U
        fadd    x0, PD_W
        fadd    x1, PD_S
        fadd    x2, PD_U
        fadd    x3, PD_UC
        bl      S2N_BN_SYMBOL(BASEMUL)
        intt    PD_W, 1
        fadd    x0, PD_V
        fadd    x1, PD_W
        bl      S2N_BN_SYMBOL(mlkem_sub_reduce)
        mov     x0, x19
        fadd    x1, PD_V
        bl      S2N_BN_SYMBOL(mlkem_tomsg)

        zero    PD_U, (PD_FRAME - PD_U)
        restoreregs
        framefree PD_FRAME
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(pke_decrypt))

// ----------------------------------------------------------------------------
// int FN(dec)(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
//
// m' = K-PKE.Decrypt(dk, c) and (K', r') = G(m' || h) first; then the
// transposed matrix with H(ek) and J(z || c) computed beside it, and the
// noise from r' sampled in lanes it leaves idle (for eta1 = 2; otherwise
// separately); then the hash check H(ek) = h, c' = K-PKE.Encrypt(ek, m',
// r'), and ss = K' if c' = c, else J(z || c), selected in constant time.
// The work before the hash check is wasted when it fails, but that is the
// rare case and its result is public.
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(dec))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(dec))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(dec))

// The frame: G's input m' || h, its output K' || r', the digests H(ek) and
// J(z || c), the hash jobs and the noise job, z || c, the re-encryption
// c', the noise y || e1 || e2 and the transposed matrix.

#define DE_GIN 96
#define DE_KR 160
#define DE_HEK 224
#define DE_J 256
#define DE_JOBS 288
#define DE_NJOB 352
#define DE_ZC 384
#define DE_CT2 (DE_ZC + 32 + CTBYTES)
#define DE_NOISE (DE_CT2 + CTBYTES)
#define DE_AT (DE_NOISE + 512 * (2 * K + 1))
#define DE_FRAME (DE_AT + 512 * K * K)

S2N_BN_SYMBOL(FN(dec)):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        framealloc DE_FRAME
        saveregs
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        consts  x28

// m' = K-PKE.Decrypt(dk, c), (K', r') = G(m' || h)

        fadd    x0, DE_GIN
        mov     x1, x20
        mov     x2, x21
        bl      S2N_BN_SYMBOL(FN(pke_decrypt))
        fadd    x0, (DE_GIN + 32)
        add     x1, x21, #(SKBYTES - 64)
        copy32  x0, x1
        fadd    x0, DE_KR
        fadd    x1, DE_GIN
        mov     x2, #64
        mov     x3, x28
        bl      S2N_BN_SYMBOL(mlkem_hash_g)

// z || c, and the matrix with H(ek) (job 0, lane 2) and J(z || c) (job 1,
// lane 3) beside it, and the noise in idle lanes for eta1 = 2

        fadd    x0, DE_ZC
        add     x1, x21, #(SKBYTES - 32)
        copy32  x0, x1
        add     x0, x0, #32
        mov     x1, x20
        mov     x2, #(CTBYTES / 32)
LFN(dec_copyct):
        ldp     q0, q1, [x1], #32
        stp     q0, q1, [x0], #32
        subs    x2, x2, #1
        bne     LFN(dec_copyct)

        fadd    x4, DE_JOBS
        add     x0, x21, #VECBYTES
        mov     x1, #PKBYTES
        stp     x0, x1, [x4]
        mov     x0, #0x06
        fadd    x1, DE_HEK
        stp     x0, x1, [x4, #16]
        fadd    x0, DE_ZC
        mov     x1, #(32 + CTBYTES)
        stp     x0, x1, [x4, #32]
        mov     x0, #0x1f
        fadd    x1, DE_J
        stp     x0, x1, [x4, #48]
#if ETA1 == 2
        fadd    x5, DE_NJOB
        fadd    x0, (DE_KR + 32)
        mov     x1, #0
        stp     x0, x1, [x5]
        mov     x0, #(2 * K + 1)
        fadd    x1, DE_NOISE
        stp     x0, x1, [x5, #16]
#else
        mov     x5, #0
#endif
        fadd    x0, DE_AT
        add     x1, x21, #(2 * VECBYTES)
        mov     x2, #K
        mov     x3, #(GM_TRANSPOSED + GM_JOBS + GM_NOISE)
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_gen_matrix)
#if ETA1 != 2
        fadd    x0, DE_NOISE
        fadd    x1, (DE_KR + 32)
        mov     x2, #0
        mov     x3, #(2 * K + 1)
        mov     x4, #K
        mov     x5, #ETA1
        mov     x6, x28
        bl      S2N_BN_SYMBOL(mlkem_getnoise)
#endif

// The hash check (its result is public)

        fadd    x0, DE_HEK
        add     x1, x21, #(SKBYTES - 64)
        ldp     x2, x3, [x0]
        ldp     x4, x5, [x0, #16]
        ldp     x6, x7, [x1]
        ldp     x8, x9, [x1, #16]
        eor     x2, x2, x6
        eor     x3, x3, x7
        eor     x4, x4, x8
        eor     x5, x5, x9
        orr     x2, x2, x3
        orr     x4, x4, x5
        orr     x2, x2, x4
        cbnz    x2, LFN(dec_invalid)

// c' = K-PKE.Encrypt(ek, m', r')

        fadd    x0, DE_CT2
        fadd    x1, DE_AT
        add     x2, x21, #VECBYTES
        fadd    x3, DE_GIN
        fadd    x4, DE_NOISE
        bl      S2N_BN_SYMBOL(FN(pke_encrypt))

// ss = K' if c' = c, else J(z || c), in constant time: OR together the
// XORs of c and c', and select with the all-ones or all-zeros mask

        mov     x0, x20
        fadd    x1, DE_CT2
        mov     x2, #(CTBYTES / 16)
        movi    v2.2d, #0
LFN(dec_compare):
        ldr     q0, [x0], #16
        ldr     q1, [x1], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v2.16b, v2.16b, v0.16b
        subs    x2, x2, #1
        bne     LFN(dec_compare)
        umaxv   s2, v2.4s
        fmov    w0, s2
        cmp     w0, #0
        csetm   x0, eq
        dup     v3.2d, x0
        fadd    x1, DE_KR
        fadd    x2, DE_J
        ldp     q0, q1, [x1]
        ldp     q4, q5, [x2]
        bsl     v3.16b, v0.16b, v4.16b
        dup     v6.2d, x0
        bsl     v6.16b, v1.16b, v5.16b
        stp     q3, q6, [x19]

        zero    DE_GIN, (DE_AT - DE_GIN)
        mov     w0, #0
        b       LFN(dec_return)
LFN(dec_invalid):
        zero    DE_GIN, (DE_AT - DE_GIN)
        mov     w0, #ERR_INVALID_SK
LFN(dec_return):
        restoreregs
        framefree DE_FRAME
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(FN(dec))

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

#endif
