// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Viewing table as `height` rows with 8 words width, copy the 8 words at
// table[idx - 1] into z.  If `idx` is zero or larger than `height`,
// `z` is set to zero (ie, the affine point at infinity).
//
// This is useful to select an affine p256 point from a table of
// precomputed points.
//
//    extern void bignum_aff_point_select_p256_avx2
//     (uint64_t z[static 8], const uint64_t *table, uint64_t height,
//      uint64_t idx);
//
// This uses avx2 instructions, it is the callers responsibility to ensure
// the CPU supports these.  If not, the caller should instead call
// `bignum_copy_row_from_table(z, table, height, 8, idx - 1)`
// and then use `bignum_mux_4` to select between that and the point at infinity
// for zero `idx`.
//
// Standard x86-64 ABI: RDI = z, RSI = table, RDX = height, RCX = idx
// Microsoft x64 ABI:   RCX = z, RDX = table, R8 = height, R9 = idx
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_aff_point_select_p256_avx2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_aff_point_select_p256_avx2)
        .text

#define z rdi
#define table rsi
#define height rdx
#define idx rcx

// loop counter
#define i r9

#define acc0  ymm0
#define acc1  ymm1
#define row0  ymm2
#define row1  ymm3
#define xi    xmm4
#define yi    ymm4
#define xidx  xmm5
#define yidx  ymm5
#define ymask ymm6
#define yones ymm7

S2N_BN_SYMBOL(bignum_aff_point_select_p256_avx2):

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif
        prefetcht0 [table]
        prefetcht0 [table+128]

        // zero accumulators
        vpxor   acc0, acc0, acc0
        vpxor   acc1, acc1, acc1

        // skip if height == 0
        test    height, height
        jz      bignum_aff_point_select_p256_avx2_end

        // nb, i and idx are 1-indexed
        mov     i, 1
        mov     rax, table

        // set up selection blocks (acc0 as a stand-in for zeros):
        vmovq   xidx, idx
        vpermd  yidx, acc0, yidx
        vmovq   xi, i
        vpermd  yi, acc0, yi
        vmovdqa yones, yi

bignum_aff_point_select_p256_avx2_rowloop:
        // read in candidate row
        vmovdqu row0, [rax]
        vmovdqu row1, [rax+32]

        // construct 256-bit mask selecting correct row
        vpcmpeqd ymask, yi, yidx
        vpaddq   yi, yi, yones

        // mix into accumulators based on mask
        vblendvpd    acc0, acc0, row0, ymask
        vblendvpd    acc1, acc1, row1, ymask

        // next row
        add     rax, 64
        inc     i
        cmp     i, height
        jle     bignum_aff_point_select_p256_avx2_rowloop

bignum_aff_point_select_p256_avx2_end:
        vmovdqu [z], acc0
        vmovdqu [z+32], acc1

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret


#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
