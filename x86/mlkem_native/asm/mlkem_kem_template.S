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
// the seed of pk (in the custom NTT order of the x86 kernels) and the
// noise sampled from r, and K-PKE.Decrypt (Algorithm 15). Their pointer
// arguments at and noise must be 32-byte aligned.
//
// The structure differs from mlkem-native's in how the Keccak work is
// scheduled over the lanes of the x4 permutation: H(pk), and in
// decapsulation J(z || c), are computed in lanes beside the sampling of
// the matrix, and noise is sampled in lanes the matrix leaves idle (see
// mlkem_gen_matrix). Otherwise the steps are those of FIPS 203 as
// implemented by mlkem-native, with its native x86_64 kernels (and the
// custom order of the NTT domain that they use).
//
// All functions are constant-time in the secret data (and the checks'
// results are public); the stack buffers holding secrets are zeroed
// before returning.
//
// The API functions follow the System V ABI, or with WINDOWS_ABI the
// Microsoft x64 ABI: then each is a wrapper that saves rdi, rsi and
// xmm6-xmm15, moves the arguments and calls the System V code. Everything
// they call is System V code in either case.
// ----------------------------------------------------------------------------

// The including file has included _internal_s2n_bignum_x86.h,
// mlkem_native2_consts.h and mlkem_native2_names.h (for the names of the
// AVX-512 version, which assembles this template with
// MLKEM_NATIVE2_AVX512 defined).

#include "mlkem_native2_macros.h"

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

// Names: FN(f) is mlkemL_f, and the kernels and their tables for this K
// and du, dv

#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)
#define FN(f) N2(CAT(CAT(mlkem, MLKEM_L), CAT(_, f)))
// LFN(f) for the labels inside the functions: FN(f) with an L prefix,
// which keeps the label local to the object on Mach-O
#define LFN(f) CAT(L, FN(f))
#define BASEMUL CAT(mlkem_basemul_k, MLKEM_K)
#define COMPRESS_DU CAT(CAT(mlkem_compress_d, DU), _x86)
#define COMPRESS_DV CAT(CAT(mlkem_compress_d, DV), _x86)
#define DECOMPRESS_DU CAT(CAT(mlkem_decompress_d, DU), _x86)
#define DECOMPRESS_DV CAT(CAT(mlkem_decompress_d, DV), _x86)
#define C_COMPRESS_DU CAT(CAT(MLKEM_C_COMPRESS_D, DU), _DATA)
#define C_COMPRESS_DV CAT(CAT(MLKEM_C_COMPRESS_D, DV), _DATA)
#define C_DECOMPRESS_DU CAT(CAT(MLKEM_C_DECOMPRESS_D, DU), _DATA)
#define C_DECOMPRESS_DV CAT(CAT(MLKEM_C_DECOMPRESS_D, DV), _DATA)

        .intel_syntax noprefix
        .text
        .balign 32

// ----------------------------------------------------------------------------
// Assembler macros for the frames and common steps
// ----------------------------------------------------------------------------

// enter size / leave_: a frame with rbp as the frame pointer, the
// callee-saved rbx and r12-r15 below it, and size bytes (a multiple of 32)
// at rsp, which is 32-byte aligned. The constants block is then in r15.
// The first 32 bytes of each frame that calls mlkem_gen_matrix or
// mlkem_getnoise hold their seventh argument.

        .macro  enter size
        .if ((\size) % 32) != 0
        .error  "enter: the frame size must be a multiple of 32"
        .endif
        push    rbp
        .cfi_adjust_cfa_offset 8
        .cfi_rel_offset rbp, 0
        mov     rbp, rsp
        .cfi_def_cfa_register rbp
        push    rbx
        .cfi_offset rbx, -24
        push    r12
        .cfi_offset r12, -32
        push    r13
        .cfi_offset r13, -40
        push    r14
        .cfi_offset r14, -48
        push    r15
        .cfi_offset r15, -56
        sub     rsp, (\size)
        and     rsp, -32
        lea     r15, [rip+S2N_BN_SYMBOL(mlkem_native2_constants)]
        .endm

        .macro  leave_
        lea     rsp, [rbp-40]
        pop     r15
        .cfi_restore r15
        pop     r14
        .cfi_restore r14
        pop     r13
        .cfi_restore r13
        pop     r12
        .cfi_restore r12
        pop     rbx
        .cfi_restore rbx
        pop     rbp
        .cfi_restore rbp
        .cfi_def_cfa rsp, 8
        ret
        .endm

// winentry body, nargs: with WINDOWS_ABI, the Microsoft x64 entry of an
// API function: save rdi, rsi and xmm6-xmm15, move the nargs (at most
// four) arguments to their System V registers, call the System V code at
// body and restore; nothing otherwise. The frame keeps rsp 16-byte
// aligned at the call.

        .macro  winentry body, nargs
#if WINDOWS_ABI
        sub     rsp, 184
        .cfi_adjust_cfa_offset 184
        vmovdqu [rsp], xmm6
        vmovdqu [rsp+16], xmm7
        vmovdqu [rsp+32], xmm8
        vmovdqu [rsp+48], xmm9
        vmovdqu [rsp+64], xmm10
        vmovdqu [rsp+80], xmm11
        vmovdqu [rsp+96], xmm12
        vmovdqu [rsp+112], xmm13
        vmovdqu [rsp+128], xmm14
        vmovdqu [rsp+144], xmm15
        mov     [rsp+160], rdi
        mov     [rsp+168], rsi
        mov     rdi, rcx
        .if (\nargs) >= 2
        mov     rsi, rdx
        .endif
        .if (\nargs) >= 3
        mov     rdx, r8
        .endif
        .if (\nargs) >= 4
        mov     rcx, r9
        .endif
        call    \body
        vmovdqu xmm6, [rsp]
        vmovdqu xmm7, [rsp+16]
        vmovdqu xmm8, [rsp+32]
        vmovdqu xmm9, [rsp+48]
        vmovdqu xmm10, [rsp+64]
        vmovdqu xmm11, [rsp+80]
        vmovdqu xmm12, [rsp+96]
        vmovdqu xmm13, [rsp+112]
        vmovdqu xmm14, [rsp+128]
        vmovdqu xmm15, [rsp+144]
        mov     rdi, [rsp+160]
        mov     rsi, [rsp+168]
        add     rsp, 184
        .cfi_adjust_cfa_offset -184
        ret
\body:
#endif
        .endm

// declassify off, len, area: in a build for constant-time testing under
// valgrind (MLKEM_CT_TESTING defined), mark the len bytes at rsp + off as
// defined, i.e. public, with memcheck's client request (the special
// sequence of rotations of rdi by 3, 13, 61 and 51 and xchg rbx, rbx, with
// rax pointing at the request and its arguments and rdx the default
// result), using the 48 bytes at rsp + area; otherwise nothing. It
// clobbers rax and rdx.

        .macro  declassify off, len, area
#if defined(MLKEM_CT_TESTING)
        mov     eax, 0x4d430002
        mov     [rsp+(\area)], rax
        leadisp rax, rsp, (\off)
        mov     [rsp+(\area)+8], rax
        mov     eax, (\len)
        mov     [rsp+(\area)+16], rax
        xor     eax, eax
        mov     [rsp+(\area)+24], rax
        mov     [rsp+(\area)+32], rax
        mov     [rsp+(\area)+40], rax
        xor     edx, edx
        leadisp rax, rsp, (\area)
        rol     rdi, 3
        rol     rdi, 13
        rol     rdi, 61
        rol     rdi, 51
        xchg    rbx, rbx
#endif
        .endm

// zero off, len: zero len bytes (a multiple of 32) of the frame at off,
// 128 bytes at a time and then the rest

        .macro  zero off, len
        .if ((\len) % 32) != 0
        .error  "zero: the length must be a multiple of 32"
        .endif
        vpxor   xmm0, xmm0, xmm0
        leadisp rdi, rsp, (\off)
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
        .endm

// copy dst, src, len: copy len bytes (a multiple of 32; the addresses
// registers or register+offset expressions without brackets)

        .macro  copy dst, src, len
        .if ((\len) % 32) != 0
        .error  "copy: the length must be a multiple of 32"
        .endif
        .set    i, 0
        .rept   ((\len) / 32)
        vmovdqu ymm0, [\src+i]
        vmovdqu [\dst+i], ymm0
        .set    i, i + 32
        .endr
        .endm

// ----------------------------------------------------------------------------
// The polynomial-vector steps of K-PKE, as sequences of kernel calls, with
// the constants block in r15.
// ----------------------------------------------------------------------------

// ntt off, base: the NTT of the K polynomials of the vector at base + off
// (base rsp or a callee-saved register)

        .macro  ntt off, base=rsp
        .set    i, 0
        .rept   K
        leadisp rdi, \base, (\off)+512*i
        lea     rsi, [r15+MLKEM_C_QDATA]
        call    S2N_BN_SYMBOL(mlkem_ntt_x86)
        .set    i, i + 1
        .endr
        .endm

// intt off, n: the inverse NTT of n polynomials at rsp + off

        .macro  intt off, n
        .set    i, 0
        .rept   (\n)
        leadisp rdi, rsp, (\off)+512*i
        lea     rsi, [r15+MLKEM_C_QDATA]
        call    S2N_BN_SYMBOL(mlkem_intt_x86)
        .set    i, i + 1
        .endr
        .endm

// mulcache dst, src, base: the mulcaches of the K polynomials of the
// vector at base + src, 256 bytes each, at rsp + dst

        .macro  mulcache dst, src, base=rsp
        .set    i, 0
        .rept   K
        leadisp rdi, rsp, (\dst)+256*i
        leadisp rsi, \base, (\src)+512*i
        lea     rdx, [r15+MLKEM_C_QDATA]
        call    S2N_BN_SYMBOL(mlkem_mulcache_compute_x86)
        .set    i, i + 1
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
        _CET_ENDBR
        winentry LFN(check_pk_standard), 1
        sub     rsp, 8
        .cfi_adjust_cfa_offset 8
        mov     esi, K
        call    S2N_BN_SYMBOL(mlkem_check_encoding)
        mov     edx, ERR_INVALID_PK
        xor     ecx, ecx
        test    rax, rax
        cmovz   ecx, edx
        mov     eax, ecx
        add     rsp, 8
        .cfi_adjust_cfa_offset -8
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

S2N_BN_SYMBOL(FN(check_sk)):
        CFI_START
        _CET_ENDBR
        winentry LFN(check_sk_standard), 1
        CFI_PUSH(rbx)
        CFI_DEC_RSP(48)
        mov     rbx, rdi
        mov     rdi, rsp
        lea     rsi, [rbx+VECBYTES]
        mov     edx, PKBYTES
        lea     rcx, [rip+S2N_BN_SYMBOL(mlkem_native2_constants)]
        call    S2N_BN_SYMBOL(N2(mlkem_hash_h))
        mov     rax, [rsp]
        xor     rax, [rbx+SKBYTES-64]
        mov     rcx, [rsp+8]
        xor     rcx, [rbx+SKBYTES-56]
        or      rax, rcx
        mov     rcx, [rsp+16]
        xor     rcx, [rbx+SKBYTES-48]
        or      rax, rcx
        mov     rcx, [rsp+24]
        xor     rcx, [rbx+SKBYTES-40]
        or      rax, rcx
        mov     edx, ERR_INVALID_SK
        xor     ecx, ecx
        test    rax, rax
        cmovnz  ecx, edx
        mov     eax, ecx
        CFI_INC_RSP(48)
        CFI_POP(rbx)
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

// The frame: the seventh argument of the calls, G's input d || K, its
// output rho || sigma, the noise job, the client request of declassify,
// the matrix, s and e (consecutive, as sampled together), the mulcache of
// s, and t.

#define KP_GIN 32
#define KP_G 96
#define KP_NJOB 160
#define KP_CTA 192
#define KP_A 256
#define KP_S (KP_A + 512 * K * K)
#define KP_E (KP_S + 512 * K)
#define KP_SC (KP_E + 512 * K)
#define KP_T (KP_SC + 256 * K)
#define KP_FRAME (KP_T + 512 * K)

S2N_BN_SYMBOL(FN(keypair_derand)):
        CFI_START
        _CET_ENDBR
        winentry LFN(keypair_derand_standard), 3
        enter   KP_FRAME
        mov     rbx, rdi
        mov     r12, rsi
        mov     r13, rdx

// (rho, sigma) = G(d || K)

        copy    rsp+KP_GIN, r13, 32
        mov     BYTE PTR [rsp+KP_GIN+32], K
        lea     rdi, [rsp+KP_G]
        lea     rsi, [rsp+KP_GIN]
        mov     edx, 33
        mov     rcx, r15
        call    S2N_BN_SYMBOL(N2(mlkem_hash_g))

// rho is public, although computed from the secret d

        declassify KP_G, 32, KP_CTA

// The matrix A and the noise s, e: for eta1 = 2 the noise is sampled in
// lanes left idle by the matrix, otherwise separately

#if ETA1 == 2
        lea     rax, [rsp+KP_G+32]
        mov     [rsp+KP_NJOB], rax
        mov     QWORD PTR [rsp+KP_NJOB+8], 0
        mov     QWORD PTR [rsp+KP_NJOB+16], (2 * K)
        lea     rax, [rsp+KP_S]
        mov     [rsp+KP_NJOB+24], rax
        lea     r9, [rsp+KP_NJOB]
#else
        xor     r9d, r9d
#endif
        lea     rdi, [rsp+KP_A]
        lea     rsi, [rsp+KP_G]
        mov     edx, K
        mov     ecx, GM_NOISE
        xor     r8d, r8d
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_gen_matrix))
#if ETA1 != 2
        lea     rdi, [rsp+KP_S]
        lea     rsi, [rsp+KP_G+32]
        xor     edx, edx
        mov     ecx, (2 * K)
        mov     r8d, (2 * K)
        mov     r9d, ETA1
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_getnoise))
#endif

// t = A s + e in the NTT domain, reduced

        ntt     KP_S
        ntt     KP_E
        mulcache KP_SC, KP_S
        .set    j, 0
        .rept   K
        lea     rdi, [rsp+KP_T+512*j]
        lea     rsi, [rsp+KP_A+512*K*j]
        lea     rdx, [rsp+KP_S]
        lea     rcx, [rsp+KP_SC]
        call    S2N_BN_SYMBOL(BASEMUL)
        lea     rdi, [rsp+KP_T+512*j]
        call    S2N_BN_SYMBOL(mlkem_tomont)
        lea     rdi, [rsp+KP_T+512*j]
        lea     rsi, [rsp+KP_E+512*j]
        call    S2N_BN_SYMBOL(mlkem_add_reduce)
        lea     rdi, [rsp+KP_S+512*j]
        call    S2N_BN_SYMBOL(mlkem_reduce)
        .set    j, j + 1
        .endr

// pk = ByteEncode_12(t) || rho, sk = ByteEncode_12(s) || pk || H(pk) || z

        .set    j, 0
        .rept   K
        leadisp rdi, rbx, POLYBYTES*j
        lea     rsi, [rsp+KP_T+512*j]
        call    S2N_BN_SYMBOL(mlkem_tobytes)
        leadisp rdi, r12, POLYBYTES*j
        lea     rsi, [rsp+KP_S+512*j]
        call    S2N_BN_SYMBOL(mlkem_tobytes)
        .set    j, j + 1
        .endr
        copy    rbx+VECBYTES, rsp+KP_G, 32
        copy    r12+VECBYTES, rbx, PKBYTES
        lea     rdi, [r12+SKBYTES-64]
        mov     rsi, rbx
        mov     edx, PKBYTES
        mov     rcx, r15
        call    S2N_BN_SYMBOL(N2(mlkem_hash_h))
        copy    r12+SKBYTES-32, r13+32, 32

// Zero the secrets: d, sigma, s, e and their mulcache (t is public)

        zero    KP_GIN, (KP_A - KP_GIN)
        zero    KP_S, (KP_T - KP_S)

        xor     eax, eax
        vzeroupper
        leave_
        .cfi_endproc

S2N_BN_SIZE_DIRECTIVE(FN(keypair_derand))

// ----------------------------------------------------------------------------
// void FN(pke_encrypt)(uint8_t *ct, const int16_t *at,
//                      const uint8_t *pk, const uint8_t m[32],
//                      int16_t *noise)
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
// The noise is in r14: y, e1, e2 at offsets 0, 512 * K, 1024 * K.

#define PE_YC 0
#define PE_T (PE_YC + 256 * K)
#define PE_U (PE_T + 512 * K)
#define PE_V (PE_U + 512 * K)
#define PE_M (PE_V + 512)
#define PE_FRAME (PE_M + 512)

S2N_BN_SYMBOL(FN(pke_encrypt)):
        CFI_START
        _CET_ENDBR
        enter   PE_FRAME
        mov     rbx, rdi
        mov     r12, rsi
        mov     r13, rdx
        mov     r14, r8

        lea     rdi, [rsp+PE_M]
        mov     rsi, rcx
        call    S2N_BN_SYMBOL(mlkem_frommsg)
        .set    j, 0
        .rept   K
        lea     rdi, [rsp+PE_T+512*j]
        leadisp rsi, r13, POLYBYTES*j
        call    S2N_BN_SYMBOL(mlkem_frombytes)
        .set    j, j + 1
        .endr

// NTT(y) and its mulcache

        ntt     0, r14
        mulcache PE_YC, 0, r14

// u = InvNTT(A^T y) + e1, v = InvNTT(t^T y) + e2 + m, all reduced

        .set    j, 0
        .rept   K
        lea     rdi, [rsp+PE_U+512*j]
        leadisp rsi, r12, 512*K*j
        mov     rdx, r14
        leadisp rcx, rsp, PE_YC
        call    S2N_BN_SYMBOL(BASEMUL)
        .set    j, j + 1
        .endr
        lea     rdi, [rsp+PE_V]
        lea     rsi, [rsp+PE_T]
        mov     rdx, r14
        leadisp rcx, rsp, PE_YC
        call    S2N_BN_SYMBOL(BASEMUL)
        intt    PE_U, (K + 1)
        .set    j, 0
        .rept   K
        lea     rdi, [rsp+PE_U+512*j]
        lea     rsi, [r14+512*(K+j)]
        call    S2N_BN_SYMBOL(mlkem_add_reduce)
        .set    j, j + 1
        .endr
        lea     rdi, [rsp+PE_V]
        lea     rsi, [r14+1024*K]
        call    S2N_BN_SYMBOL(mlkem_add_reduce)
        lea     rdi, [rsp+PE_V]
        lea     rsi, [rsp+PE_M]
        call    S2N_BN_SYMBOL(mlkem_add_reduce)

// ct = Compress_du(u) || Compress_dv(v)

        .set    j, 0
        .rept   K
        leadisp rdi, rbx, DUBYTES*j
        lea     rsi, [rsp+PE_U+512*j]
        lea     rdx, [r15+C_COMPRESS_DU]
        call    S2N_BN_SYMBOL(COMPRESS_DU)
        .set    j, j + 1
        .endr
        lea     rdi, [rbx+DUBYTES*K]
        lea     rsi, [rsp+PE_V]
        lea     rdx, [r15+C_COMPRESS_DV]
        call    S2N_BN_SYMBOL(COMPRESS_DV)

// Zero the secrets: everything but t (the noise is the caller's)

        zero    PE_YC, (PE_T - PE_YC)
        zero    PE_U, (PE_FRAME - PE_U)

        vzeroupper
        leave_
        .cfi_endproc

S2N_BN_SIZE_DIRECTIVE(FN(pke_encrypt))

// ----------------------------------------------------------------------------
// int FN(enc_derand)(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
//                    const uint8_t *coins)
//
// After the encapsulation key check: (K, r) = G(m || H(pk)) for
// m = coins[0..31], with H(pk) computed beside the sampling of the
// transposed matrix, then the noise from r, ct = K-PKE.Encrypt(pk, m, r)
// and ss = K.
// ----------------------------------------------------------------------------

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(FN(enc_derand))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(FN(enc_derand))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(FN(enc_derand))

// The frame: the seventh argument of the calls, G's input m || H(pk), its
// output K || r, the hash jobs (job 1 for H(pk)), the noise y || e1 || e2
// and the transposed matrix.

#define EN_GIN 32
#define EN_KR 96
#define EN_JOBS 160
#define EN_NOISE 224
#define EN_AT (EN_NOISE + 512 * (2 * K + 1))
#define EN_FRAME (EN_AT + 512 * K * K)

S2N_BN_SYMBOL(FN(enc_derand)):
        CFI_START
        _CET_ENDBR
        winentry LFN(enc_derand_standard), 4
        enter   EN_FRAME
        mov     rbx, rdi
        mov     r12, rsi
        mov     r13, rdx
        mov     r14, rcx

        mov     rdi, r13
        mov     esi, K
        call    S2N_BN_SYMBOL(mlkem_check_encoding)
        test    rax, rax
        jz      LFN(enc_invalid)

        copy    rsp+EN_GIN, r14, 32

// The transposed matrix, and H(pk) beside it as job 1 (lane 3)

        xor     eax, eax
        mov     [rsp+EN_JOBS], rax
        mov     [rsp+EN_JOBS+8], rax
        mov     [rsp+EN_JOBS+16], rax
        mov     [rsp+EN_JOBS+24], rax
        mov     [rsp+EN_JOBS+32], r13
        mov     QWORD PTR [rsp+EN_JOBS+40], PKBYTES
        mov     QWORD PTR [rsp+EN_JOBS+48], 0x06
        lea     rax, [rsp+EN_GIN+32]
        mov     [rsp+EN_JOBS+56], rax
        lea     rdi, [rsp+EN_AT]
        lea     rsi, [r13+VECBYTES]
        mov     edx, K
        mov     ecx, (GM_TRANSPOSED + GM_JOBS)
        lea     r8, [rsp+EN_JOBS]
        xor     r9d, r9d
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_gen_matrix))

// (K, r) = G(m || H(pk)), the noise from r, ct = K-PKE.Encrypt(pk, m, r),
// ss = K

        lea     rdi, [rsp+EN_KR]
        lea     rsi, [rsp+EN_GIN]
        mov     edx, 64
        mov     rcx, r15
        call    S2N_BN_SYMBOL(N2(mlkem_hash_g))
        lea     rdi, [rsp+EN_NOISE]
        lea     rsi, [rsp+EN_KR+32]
        xor     edx, edx
        mov     ecx, (2 * K + 1)
        mov     r8d, K
        mov     r9d, ETA1
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_getnoise))
        mov     rdi, rbx
        lea     rsi, [rsp+EN_AT]
        mov     rdx, r13
        lea     rcx, [rsp+EN_GIN]
        lea     r8, [rsp+EN_NOISE]
        call    S2N_BN_SYMBOL(FN(pke_encrypt))
        copy    r12, rsp+EN_KR, 32

        zero    EN_GIN, (EN_AT - EN_GIN)
        xor     eax, eax
        jmp     LFN(enc_return)
LFN(enc_invalid):
        mov     eax, ERR_INVALID_PK
LFN(enc_return):
        vzeroupper
        leave_
        .cfi_endproc

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

#define PD_U 0
#define PD_UC (PD_U + 512 * K)
#define PD_V (PD_UC + 256 * K)
#define PD_S (PD_V + 512)
#define PD_W (PD_S + 512 * K)
#define PD_FRAME (PD_W + 512)

S2N_BN_SYMBOL(FN(pke_decrypt)):
        CFI_START
        _CET_ENDBR
        enter   PD_FRAME
        mov     rbx, rdi
        mov     r12, rsi
        mov     r13, rdx

        .set    j, 0
        .rept   K
        leadisp rdi, rsp, PD_U+512*j
        leadisp rsi, r12, DUBYTES*j
        lea     rdx, [r15+C_DECOMPRESS_DU]
        call    S2N_BN_SYMBOL(DECOMPRESS_DU)
        lea     rdi, [rsp+PD_S+512*j]
        leadisp rsi, r13, POLYBYTES*j
        call    S2N_BN_SYMBOL(mlkem_frombytes)
        .set    j, j + 1
        .endr
        lea     rdi, [rsp+PD_V]
        lea     rsi, [r12+DUBYTES*K]
        lea     rdx, [r15+C_DECOMPRESS_DV]
        call    S2N_BN_SYMBOL(DECOMPRESS_DV)

        ntt     PD_U
        mulcache PD_UC, PD_U
        lea     rdi, [rsp+PD_W]
        lea     rsi, [rsp+PD_S]
        leadisp rdx, rsp, PD_U
        lea     rcx, [rsp+PD_UC]
        call    S2N_BN_SYMBOL(BASEMUL)
        intt    PD_W, 1
        lea     rdi, [rsp+PD_V]
        lea     rsi, [rsp+PD_W]
        call    S2N_BN_SYMBOL(mlkem_sub_reduce)
        mov     rdi, rbx
        lea     rsi, [rsp+PD_V]
        call    S2N_BN_SYMBOL(mlkem_tomsg)

        zero    PD_U, (PD_FRAME - PD_U)
        vzeroupper
        leave_
        .cfi_endproc

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

// The frame: the seventh argument of the calls, G's input m' || h, its
// output K' || r', the digests H(ek) and J(z || c), the hash jobs and the
// noise job, z || c, the re-encryption c', the noise y || e1 || e2 and the
// transposed matrix.

#define DE_GIN 32
#define DE_KR 96
#define DE_HEK 160
#define DE_J 192
#define DE_JOBS 224
#define DE_NJOB 288
#define DE_ZC 320
#define DE_CT2 (DE_ZC + 32 + CTBYTES)
#define DE_NOISE (DE_CT2 + CTBYTES)
#define DE_AT (DE_NOISE + 512 * (2 * K + 1))
#define DE_FRAME (DE_AT + 512 * K * K)

S2N_BN_SYMBOL(FN(dec)):
        CFI_START
        _CET_ENDBR
        winentry LFN(dec_standard), 3
        enter   DE_FRAME
        mov     rbx, rdi
        mov     r12, rsi
        mov     r13, rdx

// m' = K-PKE.Decrypt(dk, c), (K', r') = G(m' || h)

        lea     rdi, [rsp+DE_GIN]
        mov     rsi, r12
        mov     rdx, r13
        call    S2N_BN_SYMBOL(FN(pke_decrypt))
        copy    rsp+DE_GIN+32, r13+SKBYTES-64, 32
        lea     rdi, [rsp+DE_KR]
        lea     rsi, [rsp+DE_GIN]
        mov     edx, 64
        mov     rcx, r15
        call    S2N_BN_SYMBOL(N2(mlkem_hash_g))

// z || c, and the matrix with H(ek) (job 0, lane 2) and J(z || c) (job 1,
// lane 3) beside it, and the noise in idle lanes for eta1 = 2

        copy    rsp+DE_ZC, r13+SKBYTES-32, 32
        copy    rsp+DE_ZC+32, r12, CTBYTES

        lea     rax, [r13+VECBYTES]
        mov     [rsp+DE_JOBS], rax
        mov     QWORD PTR [rsp+DE_JOBS+8], PKBYTES
        mov     QWORD PTR [rsp+DE_JOBS+16], 0x06
        lea     rax, [rsp+DE_HEK]
        mov     [rsp+DE_JOBS+24], rax
        lea     rax, [rsp+DE_ZC]
        mov     [rsp+DE_JOBS+32], rax
        mov     QWORD PTR [rsp+DE_JOBS+40], (32 + CTBYTES)
        mov     QWORD PTR [rsp+DE_JOBS+48], 0x1f
        lea     rax, [rsp+DE_J]
        mov     [rsp+DE_JOBS+56], rax
#if ETA1 == 2
        lea     rax, [rsp+DE_KR+32]
        mov     [rsp+DE_NJOB], rax
        mov     QWORD PTR [rsp+DE_NJOB+8], 0
        mov     QWORD PTR [rsp+DE_NJOB+16], (2 * K + 1)
        lea     rax, [rsp+DE_NOISE]
        mov     [rsp+DE_NJOB+24], rax
        lea     r9, [rsp+DE_NJOB]
#else
        xor     r9d, r9d
#endif
        lea     rdi, [rsp+DE_AT]
        lea     rsi, [r13+2*VECBYTES]
        mov     edx, K
        mov     ecx, (GM_TRANSPOSED + GM_JOBS + GM_NOISE)
        lea     r8, [rsp+DE_JOBS]
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_gen_matrix))
#if ETA1 != 2
        lea     rdi, [rsp+DE_NOISE]
        lea     rsi, [rsp+DE_KR+32]
        xor     edx, edx
        mov     ecx, (2 * K + 1)
        mov     r8d, K
        mov     r9d, ETA1
        mov     [rsp], r15
        call    S2N_BN_SYMBOL(N2(mlkem_getnoise))
#endif

// The hash check (its result is public)

        mov     rax, [rsp+DE_HEK]
        xor     rax, [r13+SKBYTES-64]
        mov     rcx, [rsp+DE_HEK+8]
        xor     rcx, [r13+SKBYTES-56]
        or      rax, rcx
        mov     rcx, [rsp+DE_HEK+16]
        xor     rcx, [r13+SKBYTES-48]
        or      rax, rcx
        mov     rcx, [rsp+DE_HEK+24]
        xor     rcx, [r13+SKBYTES-40]
        or      rax, rcx
        jnz     LFN(dec_invalid)

// c' = K-PKE.Encrypt(ek, m', r')

        lea     rdi, [rsp+DE_CT2]
        lea     rsi, [rsp+DE_AT]
        lea     rdx, [r13+VECBYTES]
        lea     rcx, [rsp+DE_GIN]
        lea     r8, [rsp+DE_NOISE]
        call    S2N_BN_SYMBOL(FN(pke_encrypt))

// ss = K' if c' = c, else J(z || c), in constant time: OR together the
// XORs of c and c', and select with the all-ones or all-zeros mask

        vpxor   xmm2, xmm2, xmm2
        .set    i, 0
        .rept   (CTBYTES / 32)
        vmovdqu ymm0, [r12+i]
        vpxor   ymm0, ymm0, [rsp+DE_CT2+i]
        vpor    ymm2, ymm2, ymm0
        .set    i, i + 32
        .endr
        xor     eax, eax
        vptest  ymm2, ymm2
        setz    al
        neg     rax
        vmovq   xmm3, rax
        vpbroadcastq ymm3, xmm3
        vmovdqu ymm0, [rsp+DE_J]
        vmovdqu ymm1, [rsp+DE_KR]
        vpblendvb ymm0, ymm0, ymm1, ymm3
        vmovdqu [rbx], ymm0

        zero    DE_GIN, (DE_AT - DE_GIN)
        xor     eax, eax
        jmp     LFN(dec_return)
LFN(dec_invalid):
        zero    DE_GIN, (DE_AT - DE_GIN)
        mov     eax, ERR_INVALID_SK
LFN(dec_return):
        vzeroupper
        leave_
        .cfi_endproc

S2N_BN_SIZE_DIRECTIVE(FN(dec))

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

#endif
