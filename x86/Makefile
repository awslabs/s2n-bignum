#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

OSTYPE_RESULT=$(shell uname -s)
ARCHTYPE_RESULT=$(shell uname -m)

# Assembler directives that mark symbols as .hidden
# or .private_extern can be enabled by passing
# in the S2N_BN_HIDE_SYMBOLS parameter as:
#
#    make S2N_BN_HIDE_SYMBOLS=1
#

ifeq ($(S2N_BN_HIDE_SYMBOLS),1)
SYMBOL_HIDING=-DS2N_BN_HIDE_SYMBOLS=1
else
SYMBOL_HIDING=
endif

# Add explicit language input parameter to cpp, otherwise the use of #n for
# numeric literals in ARM code is a problem when used inside #define macros
# since normally that means stringization.
#
# Some clang-based preprocessors seem to behave differently, and get confused
# by single-quote characters in comments, so we eliminate // comments first.

ifeq ($(OSTYPE_RESULT),Darwin)
PREPROCESS=sed -e 's/\/\/.*//' | $(CC) -E -I../include -DWINDOWS_ABI=0 $(SYMBOL_HIDING) -xassembler-with-cpp -
else
ifeq ($(OSTYPE_RESULT),CYGWIN_NT-10.0)
PREPROCESS=$(CC) -E -I../include -DWINDOWS_ABI=1 $(SYMBOL_HIDING) -xassembler-with-cpp -
else
PREPROCESS=$(CC) -E -I../include -DWINDOWS_ABI=0 $(SYMBOL_HIDING) -xassembler-with-cpp -
endif
endif

# Generally GNU-type assemblers are happy with multiple instructions on
# a line, but we split them up anyway just in case.

SPLIT=tr ';' '\n'

# If actually on an x86 machine, just use the assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). For the clang
# version on OS X we just add the "-arch x86_64" option. For the Linux/gcc
# toolchain we assume the presence of the special cross-assembler. This
# can be installed via something like:
#
#  sudo apt-get install binutils-x86-64-linux-gnu

ifeq ($(ARCHTYPE_RESULT),x86_64)
ASSEMBLE=as
LINK=ld
else
ifeq ($(OSTYPE_RESULT),Darwin)
ASSEMBLE=as -arch x86_64
LINK=ld
else
ASSEMBLE=x86_64-linux-gnu-as
LINK=x86_64-linux-gnu-ld
endif
endif

# Alternative preprocessing that forces WINDOWS_ABI=1
# This is used to generate additional .obj files purely
# for proof-checking, not used for actual code execution.

ifeq ($(OSTYPE_RESULT),Darwin)
WINPREPROCESS=sed -e 's/\/\/.*//' | $(CC) -E -I../include -DWINDOWS_ABI=1 -xassembler-with-cpp -
else
WINPREPROCESS=$(CC) -E -I../include -DWINDOWS_ABI=1 -xassembler-with-cpp -
endif

# List of object files for point operations and bignum operations

POINT_OBJ = curve25519/curve25519_ladderstep.o \
            curve25519/curve25519_ladderstep_alt.o \
            curve25519/curve25519_pxscalarmul.o \
            curve25519/curve25519_pxscalarmul_alt.o \
            curve25519/curve25519_x25519.o \
            curve25519/curve25519_x25519_alt.o \
            curve25519/curve25519_x25519base.o \
            curve25519/curve25519_x25519base_alt.o \
            curve25519/edwards25519_decode.o \
            curve25519/edwards25519_decode_alt.o \
            curve25519/edwards25519_encode.o \
            curve25519/edwards25519_epadd.o \
            curve25519/edwards25519_epadd_alt.o \
            curve25519/edwards25519_epdouble.o \
            curve25519/edwards25519_epdouble_alt.o \
            curve25519/edwards25519_pdouble.o \
            curve25519/edwards25519_pdouble_alt.o \
            curve25519/edwards25519_pepadd.o \
            curve25519/edwards25519_pepadd_alt.o \
            curve25519/edwards25519_scalarmulbase.o \
            curve25519/edwards25519_scalarmulbase_alt.o \
            curve25519/edwards25519_scalarmuldouble.o \
            curve25519/edwards25519_scalarmuldouble_alt.o \
            p256/p256_montjadd.o \
            p256/p256_montjadd_alt.o \
            p256/p256_montjdouble.o \
            p256/p256_montjdouble_alt.o \
            p256/p256_montjmixadd.o \
            p256/p256_montjmixadd_alt.o \
            p256/p256_montjscalarmul.o \
            p256/p256_montjscalarmul_alt.o \
            p256/p256_scalarmul.o \
            p256/p256_scalarmul_alt.o \
            p256/p256_scalarmulbase.o \
            p256/p256_scalarmulbase_alt.o \
            p384/p384_montjadd.o \
            p384/p384_montjadd_alt.o \
            p384/p384_montjdouble.o \
            p384/p384_montjdouble_alt.o \
            p384/p384_montjmixadd.o \
            p384/p384_montjmixadd_alt.o \
            p384/p384_montjscalarmul.o \
            p384/p384_montjscalarmul_alt.o \
            p521/p521_jadd.o \
            p521/p521_jadd_alt.o \
            p521/p521_jdouble.o \
            p521/p521_jdouble_alt.o \
            p521/p521_jmixadd.o \
            p521/p521_jmixadd_alt.o \
            p521/p521_jscalarmul.o \
            p521/p521_jscalarmul_alt.o \
            secp256k1/secp256k1_jadd.o \
            secp256k1/secp256k1_jadd_alt.o \
            secp256k1/secp256k1_jdouble.o \
            secp256k1/secp256k1_jdouble_alt.o \
            secp256k1/secp256k1_jmixadd.o \
            secp256k1/secp256k1_jmixadd_alt.o \
            sm2/sm2_montjadd.o \
            sm2/sm2_montjadd_alt.o \
            sm2/sm2_montjdouble.o \
            sm2/sm2_montjdouble_alt.o \
            sm2/sm2_montjmixadd.o \
            sm2/sm2_montjmixadd_alt.o \
            sm2/sm2_montjscalarmul.o \
            sm2/sm2_montjscalarmul_alt.o

BIGNUM_OBJ = curve25519/bignum_add_p25519.o \
             curve25519/bignum_cmul_p25519.o \
             curve25519/bignum_cmul_p25519_alt.o \
             curve25519/bignum_double_p25519.o \
             curve25519/bignum_inv_p25519.o \
             curve25519/bignum_invsqrt_p25519.o \
             curve25519/bignum_invsqrt_p25519_alt.o \
             curve25519/bignum_madd_n25519.o \
             curve25519/bignum_madd_n25519_alt.o \
             curve25519/bignum_mod_m25519.o \
             curve25519/bignum_mod_m25519_4.o \
             curve25519/bignum_mod_n25519.o \
             curve25519/bignum_mod_n25519_4.o \
             curve25519/bignum_mod_p25519_4.o \
             curve25519/bignum_mul_p25519.o \
             curve25519/bignum_mul_p25519_alt.o \
             curve25519/bignum_neg_p25519.o \
             curve25519/bignum_optneg_p25519.o \
             curve25519/bignum_sqr_p25519.o \
             curve25519/bignum_sqr_p25519_alt.o \
             curve25519/bignum_sqrt_p25519.o \
             curve25519/bignum_sqrt_p25519_alt.o \
             curve25519/bignum_sub_p25519.o \
             fastmul/bignum_emontredc_8n.o \
             fastmul/bignum_kmul_16_32.o \
             fastmul/bignum_kmul_32_64.o \
             fastmul/bignum_ksqr_16_32.o \
             fastmul/bignum_ksqr_32_64.o \
             fastmul/bignum_mul_4_8.o \
             fastmul/bignum_mul_4_8_alt.o \
             fastmul/bignum_mul_6_12.o \
             fastmul/bignum_mul_6_12_alt.o \
             fastmul/bignum_mul_8_16.o \
             fastmul/bignum_mul_8_16_alt.o \
             fastmul/bignum_sqr_4_8.o \
             fastmul/bignum_sqr_4_8_alt.o \
             fastmul/bignum_sqr_6_12.o \
             fastmul/bignum_sqr_6_12_alt.o \
             fastmul/bignum_sqr_8_16.o \
             fastmul/bignum_sqr_8_16_alt.o \
             generic/bignum_add.o \
             generic/bignum_amontifier.o \
             generic/bignum_amontmul.o \
             generic/bignum_amontredc.o \
             generic/bignum_amontsqr.o \
             generic/bignum_bitfield.o \
             generic/bignum_bitsize.o \
             generic/bignum_cdiv.o \
             generic/bignum_cdiv_exact.o \
             generic/bignum_cld.o \
             generic/bignum_clz.o \
             generic/bignum_cmadd.o \
             generic/bignum_cmnegadd.o \
             generic/bignum_cmod.o \
             generic/bignum_cmul.o \
             generic/bignum_coprime.o \
             generic/bignum_copy.o \
             generic/bignum_copy_row_from_table.o \
             generic/bignum_ctd.o \
             generic/bignum_ctz.o \
             generic/bignum_demont.o \
             generic/bignum_digit.o \
             generic/bignum_digitsize.o \
             generic/bignum_divmod10.o \
             generic/bignum_emontredc.o \
             generic/bignum_eq.o \
             generic/bignum_even.o \
             generic/bignum_ge.o \
             generic/bignum_gt.o \
             generic/bignum_iszero.o \
             generic/bignum_le.o \
             generic/bignum_lt.o \
             generic/bignum_madd.o \
             generic/bignum_modadd.o \
             generic/bignum_moddouble.o \
             generic/bignum_modexp.o \
             generic/bignum_modifier.o \
             generic/bignum_modinv.o \
             generic/bignum_modoptneg.o \
             generic/bignum_modsub.o \
             generic/bignum_montifier.o \
             generic/bignum_montmul.o \
             generic/bignum_montredc.o \
             generic/bignum_montsqr.o \
             generic/bignum_mul.o \
             generic/bignum_muladd10.o \
             generic/bignum_mux.o \
             generic/bignum_mux16.o \
             generic/bignum_negmodinv.o \
             generic/bignum_nonzero.o \
             generic/bignum_normalize.o \
             generic/bignum_odd.o \
             generic/bignum_of_word.o \
             generic/bignum_optadd.o \
             generic/bignum_optneg.o \
             generic/bignum_optsub.o \
             generic/bignum_optsubadd.o \
             generic/bignum_pow2.o \
             generic/bignum_shl_small.o \
             generic/bignum_shr_small.o \
             generic/bignum_sqr.o \
             generic/bignum_sub.o \
             generic/word_bytereverse.o \
             generic/word_clz.o \
             generic/word_ctz.o \
             generic/word_divstep59.o \
             generic/word_max.o \
             generic/word_min.o \
             generic/word_negmodinv.o \
             generic/word_popcount.o \
             generic/word_recip.o \
             mldsa/mldsa_caddq.o \
             mldsa/mldsa_chknorm.o \
             mldsa/mldsa_decompose_32.o \
             mldsa/mldsa_decompose_88.o \
             mldsa/mldsa_intt.o \
             mldsa/mldsa_ntt.o \
             mldsa/mldsa_nttunpack.o \
             mldsa/mldsa_pointwise.o \
             mldsa/mldsa_pointwise_acc_l4.o \
             mldsa/mldsa_pointwise_acc_l5.o \
             mldsa/mldsa_pointwise_acc_l7.o \
             mldsa/mldsa_poly_use_hint_32.o \
             mldsa/mldsa_poly_use_hint_88.o \
             mldsa/mldsa_polyz_unpack_17.o \
             mldsa/mldsa_polyz_unpack_19.o \
             mldsa/mldsa_reduce.o \
             mldsa/mldsa_rej_uniform_VARIABLE_TIME.o \
             mldsa/mldsa_rej_uniform_eta2_VARIABLE_TIME.o \
             mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.o \
             mlkem/mlkem_basemul_k2.o \
             mlkem/mlkem_basemul_k3.o \
             mlkem/mlkem_basemul_k4.o \
             mlkem/mlkem_frombytes.o \
             mlkem/mlkem_intt.o \
             mlkem/mlkem_mulcache_compute.o \
             mlkem/mlkem_ntt.o \
             mlkem/mlkem_reduce.o \
             mlkem/mlkem_rej_uniform_VARIABLE_TIME.o \
             mlkem/mlkem_tobytes.o \
             mlkem/mlkem_tomont.o \
             mlkem/mlkem_unpack.o \
             p256/bignum_add_p256.o \
             p256/bignum_bigendian_4.o \
             p256/bignum_cmul_p256.o \
             p256/bignum_cmul_p256_alt.o \
             p256/bignum_deamont_p256.o \
             p256/bignum_deamont_p256_alt.o \
             p256/bignum_demont_p256.o \
             p256/bignum_demont_p256_alt.o \
             p256/bignum_double_p256.o \
             p256/bignum_half_p256.o \
             p256/bignum_inv_p256.o \
             p256/bignum_littleendian_4.o \
             p256/bignum_mod_n256.o \
             p256/bignum_mod_n256_alt.o \
             p256/bignum_mod_n256_4.o \
             p256/bignum_mod_p256.o \
             p256/bignum_mod_p256_alt.o \
             p256/bignum_mod_p256_4.o \
             p256/bignum_montinv_p256.o \
             p256/bignum_montmul_p256.o \
             p256/bignum_montmul_p256_alt.o \
             p256/bignum_montsqr_p256.o \
             p256/bignum_montsqr_p256_alt.o \
             p256/bignum_mux_4.o \
             p256/bignum_neg_p256.o \
             p256/bignum_nonzero_4.o \
             p256/bignum_optneg_p256.o \
             p256/bignum_sub_p256.o \
             p256/bignum_tomont_p256.o \
             p256/bignum_tomont_p256_alt.o \
             p256/bignum_triple_p256.o \
             p256/bignum_triple_p256_alt.o \
             p384/bignum_add_p384.o \
             p384/bignum_bigendian_6.o \
             p384/bignum_cmul_p384.o \
             p384/bignum_cmul_p384_alt.o \
             p384/bignum_deamont_p384.o \
             p384/bignum_deamont_p384_alt.o \
             p384/bignum_demont_p384.o \
             p384/bignum_demont_p384_alt.o \
             p384/bignum_double_p384.o \
             p384/bignum_half_p384.o \
             p384/bignum_inv_p384.o \
             p384/bignum_littleendian_6.o \
             p384/bignum_mod_n384.o \
             p384/bignum_mod_n384_alt.o \
             p384/bignum_mod_n384_6.o \
             p384/bignum_mod_p384.o \
             p384/bignum_mod_p384_alt.o \
             p384/bignum_mod_p384_6.o \
             p384/bignum_montinv_p384.o \
             p384/bignum_montmul_p384.o \
             p384/bignum_montmul_p384_alt.o \
             p384/bignum_montsqr_p384.o \
             p384/bignum_montsqr_p384_alt.o \
             p384/bignum_mux_6.o \
             p384/bignum_neg_p384.o \
             p384/bignum_nonzero_6.o \
             p384/bignum_optneg_p384.o \
             p384/bignum_sub_p384.o \
             p384/bignum_tomont_p384.o \
             p384/bignum_tomont_p384_alt.o \
             p384/bignum_triple_p384.o \
             p384/bignum_triple_p384_alt.o \
             p521/bignum_add_p521.o \
             p521/bignum_cmul_p521.o \
             p521/bignum_cmul_p521_alt.o \
             p521/bignum_deamont_p521.o \
             p521/bignum_demont_p521.o \
             p521/bignum_double_p521.o \
             p521/bignum_fromlebytes_p521.o \
             p521/bignum_half_p521.o \
             p521/bignum_inv_p521.o \
             p521/bignum_mod_n521_9.o \
             p521/bignum_mod_n521_9_alt.o \
             p521/bignum_mod_p521_9.o \
             p521/bignum_montmul_p521.o \
             p521/bignum_montmul_p521_alt.o \
             p521/bignum_montsqr_p521.o \
             p521/bignum_montsqr_p521_alt.o \
             p521/bignum_mul_p521.o \
             p521/bignum_mul_p521_alt.o \
             p521/bignum_neg_p521.o \
             p521/bignum_optneg_p521.o \
             p521/bignum_sqr_p521.o \
             p521/bignum_sqr_p521_alt.o \
             p521/bignum_sub_p521.o \
             p521/bignum_tolebytes_p521.o \
             p521/bignum_tomont_p521.o \
             p521/bignum_triple_p521.o \
             p521/bignum_triple_p521_alt.o \
             secp256k1/bignum_add_p256k1.o \
             secp256k1/bignum_cmul_p256k1.o \
             secp256k1/bignum_cmul_p256k1_alt.o \
             secp256k1/bignum_deamont_p256k1.o \
             secp256k1/bignum_demont_p256k1.o \
             secp256k1/bignum_double_p256k1.o \
             secp256k1/bignum_half_p256k1.o \
             secp256k1/bignum_mod_n256k1.o \
             secp256k1/bignum_mod_n256k1_4.o \
             secp256k1/bignum_mod_p256k1.o \
             secp256k1/bignum_mod_p256k1_4.o \
             secp256k1/bignum_montmul_p256k1.o \
             secp256k1/bignum_montmul_p256k1_alt.o \
             secp256k1/bignum_montsqr_p256k1.o \
             secp256k1/bignum_montsqr_p256k1_alt.o \
             secp256k1/bignum_mul_p256k1.o \
             secp256k1/bignum_mul_p256k1_alt.o \
             secp256k1/bignum_neg_p256k1.o \
             secp256k1/bignum_optneg_p256k1.o \
             secp256k1/bignum_sqr_p256k1.o \
             secp256k1/bignum_sqr_p256k1_alt.o \
             secp256k1/bignum_sub_p256k1.o \
             secp256k1/bignum_tomont_p256k1.o \
             secp256k1/bignum_tomont_p256k1_alt.o \
             secp256k1/bignum_triple_p256k1.o \
             secp256k1/bignum_triple_p256k1_alt.o \
             sha3/sha3_keccak_f1600.o \
             sha3/sha3_keccak4_f1600.o \
             sha3/sha3_keccak4_f1600_alt.o \
             sm2/bignum_add_sm2.o \
             sm2/bignum_cmul_sm2.o \
             sm2/bignum_cmul_sm2_alt.o \
             sm2/bignum_deamont_sm2.o \
             sm2/bignum_demont_sm2.o \
             sm2/bignum_double_sm2.o \
             sm2/bignum_half_sm2.o \
             sm2/bignum_inv_sm2.o \
             sm2/bignum_mod_nsm2.o \
             sm2/bignum_mod_nsm2_alt.o \
             sm2/bignum_mod_nsm2_4.o \
             sm2/bignum_mod_sm2.o \
             sm2/bignum_mod_sm2_4.o \
             sm2/bignum_montinv_sm2.o \
             sm2/bignum_montmul_sm2.o \
             sm2/bignum_montmul_sm2_alt.o \
             sm2/bignum_montsqr_sm2.o \
             sm2/bignum_montsqr_sm2_alt.o \
             sm2/bignum_neg_sm2.o \
             sm2/bignum_optneg_sm2.o \
             sm2/bignum_sub_sm2.o \
             sm2/bignum_tomont_sm2.o \
             sm2/bignum_triple_sm2.o \
             sm2/bignum_triple_sm2_alt.o

OBJ = $(POINT_OBJ) $(BIGNUM_OBJ)

# The objects of the image of the mlkem_native2 functions, for their
# proofs, in the order of the image (see mlkem_native2/README.md). None of
# these is in OBJ yet.

MLKEM_NATIVE2_IMAGE_OBJ = mlkem_native2/mlkem512.o \
                          mlkem_native2/mlkem768.o \
                          mlkem_native2/mlkem1024.o \
                          mlkem_native2/mlkem_gen_matrix.o \
                          mlkem_native2/mlkem_getnoise.o \
                          mlkem_native2/mlkem_hash_g.o \
                          mlkem_native2/mlkem_hash_h.o \
                          mlkem/mlkem_add_reduce.o \
                          mlkem/mlkem_basemul_k2.o \
                          mlkem/mlkem_basemul_k3.o \
                          mlkem/mlkem_basemul_k4.o \
                          mlkem/mlkem_cbd2.o \
                          mlkem/mlkem_cbd3.o \
                          mlkem/mlkem_check_encoding.o \
                          mlkem/mlkem_compress_d10_x86.o \
                          mlkem/mlkem_compress_d11_x86.o \
                          mlkem/mlkem_compress_d4_x86.o \
                          mlkem/mlkem_compress_d5_x86.o \
                          mlkem/mlkem_decompress_d10_x86.o \
                          mlkem/mlkem_decompress_d11_x86.o \
                          mlkem/mlkem_decompress_d4_x86.o \
                          mlkem/mlkem_decompress_d5_x86.o \
                          mlkem/mlkem_frombytes.o \
                          mlkem/mlkem_frommsg.o \
                          mlkem/mlkem_intt.o \
                          mlkem/mlkem_mulcache_compute.o \
                          mlkem/mlkem_ntt.o \
                          mlkem/mlkem_reduce.o \
                          mlkem/mlkem_rej_uniform_alt_VARIABLE_TIME.o \
                          mlkem/mlkem_sub_reduce.o \
                          mlkem/mlkem_tobytes.o \
                          mlkem/mlkem_tomont.o \
                          mlkem/mlkem_tomsg.o \
                          mlkem/mlkem_unpack.o \
                          sha3/sha3_keccak_f1600_alt2.o \
                          sha3/sha3_keccak4_f1600_alt.o \
                          mlkem_native2/mlkem_native2_constants.o

# The same for the AVX-512 version: its API, middle layer and Keccak
# permutations, the same leaves and the same constants block

MLKEM_NATIVE2_AVX512_IMAGE_OBJ = \
        mlkem_native2_avx512/mlkem512_avx512.o \
        mlkem_native2_avx512/mlkem768_avx512.o \
        mlkem_native2_avx512/mlkem1024_avx512.o \
        mlkem_native2_avx512/mlkem_gen_matrix_avx512.o \
        mlkem_native2_avx512/mlkem_getnoise_avx512.o \
        mlkem_native2_avx512/mlkem_hash_g_avx512.o \
        mlkem_native2_avx512/mlkem_hash_h_avx512.o \
        $(filter mlkem/%,$(MLKEM_NATIVE2_IMAGE_OBJ)) \
        mlkem_native2_avx512/sha3_keccak_f1600_avx512.o \
        mlkem_native2_avx512/sha3_keccak4_f1600_avx512.o \
        mlkem_native2/mlkem_native2_constants.o

# Tutorial assembly files

TUTORIAL_PROOFS = $(wildcard tutorial/*.ml)

TUTORIAL_OBJ = $(filter-out tutorial/safety.o, $(TUTORIAL_PROOFS:.ml=.o)) \
    curve25519/bignum_mod_n25519.o p256/bignum_mux_4.o p256/bignum_mux_4.obj \
    tutorial/rel_simp2.o tutorial/rel_equivtac2.o tutorial/rel_reordertac2.o \
    tutorial/rodata_local.o

.PHONY: bmi clean clobber

# Actual object files for execution, with the "native" ABI

%.o : %.S ; cat $< | $(PREPROCESS) | $(SPLIT) | $(ASSEMBLE) -o $@ -

# Windows ABI variants used only for proof checking

WINOBJ  = $(OBJ:.o=.obj)

%.obj : %.S ; cat $< | $(WINPREPROCESS) | $(SPLIT) | $(ASSEMBLE) -o $@ -

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

# The image for the proofs of the mlkem_native2 functions, linked at 0
# with GNU ld (the linker script is not for the Darwin linker)

mlkem_native2/mlkem_native2_image.elf: $(MLKEM_NATIVE2_IMAGE_OBJ) \
                                       mlkem_native2/mlkem_native2_image.ld
	$(LINK) --no-relax -e 0 -T mlkem_native2/mlkem_native2_image.ld \
	  -o $@ $(MLKEM_NATIVE2_IMAGE_OBJ)

mlkem_native2_avx512/mlkem_native2_avx512_image.elf: \
        $(MLKEM_NATIVE2_AVX512_IMAGE_OBJ) \
        mlkem_native2_avx512/mlkem_native2_avx512_image.ld
	$(LINK) --no-relax -e 0 \
	  -T mlkem_native2_avx512/mlkem_native2_avx512_image.ld \
	  -o $@ $(MLKEM_NATIVE2_AVX512_IMAGE_OBJ)

# The code of the API is in the template that the files for the parameter
# sets include, and the AVX-512 version is assembled from the same
# sources, with the names of mlkem_native2_names.h

MLKEM_NATIVE2_N2_DEPS = mlkem_native2/mlkem_native2_consts.h \
                        mlkem_native2/mlkem_native2_names.h
mlkem_native2/mlkem512.o mlkem_native2/mlkem768.o \
mlkem_native2/mlkem1024.o: mlkem_native2/mlkem_kem_template.S \
                           $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2/mlkem_gen_matrix.o mlkem_native2/mlkem_getnoise.o \
mlkem_native2/mlkem_hash_g.o mlkem_native2/mlkem_hash_h.o: \
        $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2_avx512/mlkem512_avx512.o mlkem_native2_avx512/mlkem768_avx512.o \
mlkem_native2_avx512/mlkem1024_avx512.o: mlkem_native2/mlkem_kem_template.S \
                                         $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2_avx512/mlkem_gen_matrix_avx512.o: \
        mlkem_native2/mlkem_gen_matrix.S $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2_avx512/mlkem_getnoise_avx512.o: \
        mlkem_native2/mlkem_getnoise.S $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2_avx512/mlkem_hash_g_avx512.o: \
        mlkem_native2/mlkem_hash_g.S $(MLKEM_NATIVE2_N2_DEPS)
mlkem_native2_avx512/mlkem_hash_h_avx512.o: \
        mlkem_native2/mlkem_hash_h.S $(MLKEM_NATIVE2_N2_DEPS)

winobj: $(WINOBJ) ;

clean:; rm -f libs2nbignum.a */*.o */*.obj */*.correct */*.native \
              mlkem_native2/*.elf mlkem_native2_avx512/*.elf

# Dynamically regenerate or destroy the files recording which functions
# use BMI and/or ADX instructions in the x86 versions. These won't run
# on some older x86 machines

yesbmi_functions: $(OBJ) ; for i in */*.o; do objdump -d $$i | (egrep -qi '(mulx|adcx|adox)' && grep 'S2N_BN_SYMBOL' `echo $$i | sed -e 's/o$$/S/'`) ; done | sed -e 's/S2N_BN_SYMBOL(//; s/)://' | sort >yesbmi_functions
nonbmi_functions: $(OBJ) ; for i in */*.o; do objdump -d $$i | (egrep -qi '(mulx|adcx|adox)' || grep 'S2N_BN_SYMBOL' `echo $$i | sed -e 's/o$$/S/'`) ; done | sed -e 's/S2N_BN_SYMBOL(//; s/)://' | sort >nonbmi_functions

bmi: yesbmi_functions nonbmi_functions ; [ `cat ???bmi_functions | sort | uniq | wc -l` -eq `grep '^extern' ../include/s2n-bignum.h | grep -v _neon | wc -l` ]

clobber: clean ; rm -f yesbmi_functions nonbmi_functions

# Proof-related parts
#
# The proof files are all independent, though each one loads the
# same common infrastructure "base.ml". So you can potentially
# run the proofs in parallel for more speed, e.g.
#
#    nohup make -j 16 proofs &
#
# If you build hol-light yourself (see https://github.com/jrh13/hol-light)
# in your home directory, and do "make" inside the subdirectory hol-light,
# then the following HOLDIR setting should be right:

# TODO: exhaustively list all files. Do we need ocamldep-equivalent tool for HOL Light?
BASE_ML=proofs/base.ml \
        proofs/decode.ml \
        proofs/instruction.ml \
        proofs/subroutine_signatures.ml \
        proofs/x86.ml

HOLDIR?=$(HOME)/hol-light
HOLLIGHT:=$(HOLDIR)/hol.sh

PROOF_BINS = $(OBJ:.o=.native)
PROOF_LOGS = $(OBJ:.o=.correct)
TUTORIAL_PROOF_BINS = $(TUTORIAL_PROOFS:.ml=.native)
TUTORIAL_PROOF_LOGS = $(TUTORIAL_PROOFS:.ml=.correct)

# Build precompiled native binaries of HOL Light proofs

proofs/simulator.native: proofs/simulator.ml ../common/cosim.ml ../common/sematest.ml $(BASE_ML) x86-insns.ml proofs/simulator_forms.ml ; ../tools/build-proof.sh proofs/simulator.ml "$(HOLLIGHT)" "$@"

# For constant-time property and memory safety, collect input/output/temporary
# buffers from function signatures in s2n-bignum.h .

proofs/subroutine_signatures.ml: ../include/s2n-bignum.h ; cd .. && python3 tools/collect-signatures.py

.SECONDEXPANSION:
%.native: proofs/$$(*F).ml $(BASE_ML) %.o %.obj ; ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

# Run them and print the standard output+error at *.correct

%.correct: %.native ; ../tools/run-proof.sh "$<" "$@"

# Cases where a proof uses other proofs for lemmas and/or subroutines

curve25519/curve25519_x25519.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519_alt.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519_byte.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519_byte_alt.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519base.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519base_alt.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519base_byte.native: curve25519/bignum_inv_p25519.native
curve25519/curve25519_x25519base_byte_alt.native: curve25519/bignum_inv_p25519.native
curve25519/edwards25519_scalarmulbase.native: curve25519/bignum_inv_p25519.native
curve25519/edwards25519_scalarmulbase_alt.native: curve25519/bignum_inv_p25519.native
curve25519/edwards25519_scalarmuldouble.native: curve25519/bignum_inv_p25519.native
curve25519/edwards25519_scalarmuldouble_alt.native: curve25519/bignum_inv_p25519.native
generic/bignum_modexp.native: generic/bignum_amontifier.native generic/bignum_amontmul.native generic/bignum_demont.native generic/bignum_mux.native
p256/p256_montjadd.native: p256/bignum_montsqr_p256.native p256/bignum_montmul_p256.native p256/bignum_sub_p256.native
p256/p256_montjdouble.native: p256/bignum_montsqr_p256.native p256/bignum_montmul_p256.native p256/bignum_sub_p256.native p256/bignum_add_p256.native
p256/p256_montjscalarmul.native: p256/p256_montjadd.native p256/p256_montjdouble.native
p256/p256_montjscalarmul_alt.native: p256/p256_montjadd_alt.native p256/p256_montjdouble_alt.native
p256/p256_scalarmul.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/bignum_tomont_p256.native p256/p256_montjadd.native p256/p256_montjdouble.native p256/p256_montjmixadd.native
p256/p256_scalarmul_alt.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjadd_alt.native p256/p256_montjdouble_alt.native p256/p256_montjmixadd_alt.native
p256/p256_scalarmulbase.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjmixadd.native
p256/p256_scalarmulbase_alt.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjmixadd_alt.native
p384/p384_montjadd.native: p384/bignum_montsqr_p384.native p384/bignum_montmul_p384.native p384/bignum_sub_p384.native
p384/p384_montjdouble.native: p384/bignum_montsqr_p384.native p384/bignum_montmul_p384.native p384/bignum_sub_p384.native p384/bignum_add_p384.native
p384/p384_montjscalarmul.native: \
    p384/p384_montjadd.native p384/p384_montjdouble.native \
    p384/bignum_sub_p384.native p384/bignum_add_p384.native
p384/p384_montjscalarmul_alt.native: p384/p384_montjadd_alt.native p384/p384_montjdouble_alt.native
p521/p521_jadd.native: p521/bignum_mul_p521.native p521/bignum_sqr_p521.native
p521/p521_jdouble.native: p521/bignum_mul_p521.native p521/bignum_sqr_p521.native
p521/p521_jscalarmul.native: p521/bignum_mod_n521_9.native p521/p521_jadd.native p521/p521_jdouble.native
p521/p521_jscalarmul_alt.native: p521/bignum_mod_n521_9.native
sm2/sm2_montjscalarmul.native: sm2/sm2_montjadd.native sm2/sm2_montjdouble.native
sm2/sm2_montjscalarmul_alt.native: sm2/sm2_montjadd_alt.native sm2/sm2_montjdouble_alt.native

# The proofs of the mlkem_native2 functions are about the image of all the
# functions they call, and use the theorems for the code of those.
MLKEM_NATIVE2_IMAGE_PROOF = mlkem_native2/mlkem_native2_image.elf \
                            proofs/mlkem_native2_image.ml \
                            proofs/utils/mlkem_native2_tools.ml
MLKEM_NATIVE2_SPONGE_PROOF = $(MLKEM_NATIVE2_IMAGE_PROOF) \
                             proofs/utils/mlkem_native2_sponge.ml \
                             proofs/utils/keccak_fips202.ml \
                             proofs/utils/mlkem_bytes.ml \
                             proofs/utils/keccak_avx2.ml \
                             proofs/sha3_keccak_f1600_alt2.ml \
                             sha3/sha3_keccak_f1600_alt2.o
mlkem_native2/mlkem_hash_g.native: \
  proofs/mlkem_hash_g.ml $(BASE_ML) $(MLKEM_NATIVE2_SPONGE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem_hash_h.native: \
  proofs/mlkem_hash_h.ml $(BASE_ML) $(MLKEM_NATIVE2_SPONGE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_NOISE_PROOF = $(MLKEM_NATIVE2_SPONGE_PROOF) \
                            proofs/utils/mlkem_native2_noise.ml \
                            proofs/mlkem_cbd2.ml mlkem/mlkem_cbd2.o \
                            proofs/mlkem_cbd3.ml mlkem/mlkem_cbd3.o \
                            proofs/sha3_keccak4_f1600_alt.ml \
                            sha3/sha3_keccak4_f1600_alt.o \
                            sha3/sha3_keccak4_f1600_alt.obj
mlkem_native2/mlkem_getnoise.native: \
  proofs/mlkem_getnoise.ml $(BASE_ML) $(MLKEM_NATIVE2_NOISE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
# The proofs of mlkem_gen_matrix, for each k in their own files (each level
# of the API needs only those for its k)
MLKEM_NATIVE2_GM_PROOF = $(MLKEM_NATIVE2_NOISE_PROOF) \
                         proofs/mlkem_getnoise.ml \
                         proofs/utils/mlkem_native_fips203.ml \
                         proofs/utils/mlkem_native2_matrix.ml \
                         proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml \
                         mlkem/mlkem_rej_uniform_alt_VARIABLE_TIME.o \
                         proofs/mlkem_unpack.ml mlkem/mlkem_unpack.o \
                         mlkem/mlkem_unpack.obj proofs/mlkem_gen_matrix.ml
mlkem_native2/mlkem_gen_matrix_k2.native: \
  proofs/mlkem_gen_matrix_k2.ml $(BASE_ML) $(MLKEM_NATIVE2_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem_gen_matrix_k3.native: \
  proofs/mlkem_gen_matrix_k3.ml $(BASE_ML) $(MLKEM_NATIVE2_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem_gen_matrix_k4.native: \
  proofs/mlkem_gen_matrix_k4.ml $(BASE_ML) $(MLKEM_NATIVE2_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_GM_SAFE_PROOF = $(MLKEM_NATIVE2_GM_PROOF) \
                              proofs/utils/mlkem_native2_safety.ml \
                              proofs/utils/mlkem_native2_keccak_full.ml \
                              proofs/utils/mlkem_native2_rej_full.ml \
                              proofs/utils/mlkem_native2_gm_safe.ml
mlkem_native2/mlkem_gen_matrix_k2_safe.native: \
  proofs/mlkem_gen_matrix_k2_safe.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem_gen_matrix_k3_safe.native: \
  proofs/mlkem_gen_matrix_k3_safe.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem_gen_matrix_k4_safe.native: \
  proofs/mlkem_gen_matrix_k4_safe.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
# The proofs of the API functions, for each parameter set in its own file
MLKEM_NATIVE2_API_PROOF = $(MLKEM_NATIVE2_NOISE_PROOF) \
                          proofs/utils/mlkem_native2_safety.ml \
                          proofs/utils/mlkem_compress_consts.ml \
                          proofs/utils/mlkem_native2_api.ml \
                          proofs/mlkem_ntt.ml \
                          mlkem/mlkem_ntt.o mlkem/mlkem_ntt.obj \
                          proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml \
                          mlkem/mlkem_rej_uniform_alt_VARIABLE_TIME.o \
                          proofs/mlkem_hash_h.ml \
                          proofs/mlkem_check_encoding.ml \
                          mlkem/mlkem_check_encoding.o
MLKEM_NATIVE2_KEM_PROOF = $(MLKEM_NATIVE2_API_PROOF) \
                          $(MLKEM_NATIVE2_GM_PROOF) \
                          proofs/utils/mlkem_native2_kpke.ml \
                          proofs/utils/mlkem_native2_kem.ml \
                          proofs/mlkem_hash_g.ml \
                          proofs/mlkem_ntt.ml \
                          mlkem/mlkem_ntt.o mlkem/mlkem_ntt.obj \
                          proofs/mlkem_intt.ml \
                          mlkem/mlkem_intt.o mlkem/mlkem_intt.obj \
                          proofs/mlkem_mulcache_compute.ml \
                          mlkem/mlkem_mulcache_compute.o \
                          mlkem/mlkem_mulcache_compute.obj \
                          proofs/mlkem_basemul_k2.ml \
                          mlkem/mlkem_basemul_k2.o mlkem/mlkem_basemul_k2.obj \
                          proofs/mlkem_basemul_k3.ml \
                          mlkem/mlkem_basemul_k3.o mlkem/mlkem_basemul_k3.obj \
                          proofs/mlkem_basemul_k4.ml \
                          mlkem/mlkem_basemul_k4.o mlkem/mlkem_basemul_k4.obj \
                          proofs/mlkem_tomont.ml \
                          mlkem/mlkem_tomont.o mlkem/mlkem_tomont.obj \
                          proofs/mlkem_reduce.ml \
                          mlkem/mlkem_reduce.o mlkem/mlkem_reduce.obj \
                          proofs/mlkem_add_reduce.ml mlkem/mlkem_add_reduce.o \
                          proofs/mlkem_sub_reduce.ml mlkem/mlkem_sub_reduce.o \
                          proofs/mlkem_tobytes.ml \
                          mlkem/mlkem_tobytes.o mlkem/mlkem_tobytes.obj \
                          proofs/mlkem_frombytes.ml \
                          mlkem/mlkem_frombytes.o mlkem/mlkem_frombytes.obj \
                          proofs/mlkem_frommsg.ml mlkem/mlkem_frommsg.o \
                          proofs/mlkem_tomsg.ml mlkem/mlkem_tomsg.o \
                          proofs/mlkem_compress_d4_x86.ml \
                          mlkem/mlkem_compress_d4_x86.o \
                          proofs/mlkem_compress_d5_x86.ml \
                          mlkem/mlkem_compress_d5_x86.o \
                          proofs/mlkem_compress_d10_x86.ml \
                          mlkem/mlkem_compress_d10_x86.o \
                          proofs/mlkem_compress_d11_x86.ml \
                          mlkem/mlkem_compress_d11_x86.o \
                          proofs/mlkem_decompress_d4_x86.ml \
                          mlkem/mlkem_decompress_d4_x86.o \
                          proofs/mlkem_decompress_d5_x86.ml \
                          mlkem/mlkem_decompress_d5_x86.o \
                          proofs/mlkem_decompress_d10_x86.ml \
                          mlkem/mlkem_decompress_d10_x86.o \
                          proofs/mlkem_decompress_d11_x86.ml \
                          mlkem/mlkem_decompress_d11_x86.o
MLKEM_NATIVE2_KEM_SAFE_PROOF = $(MLKEM_NATIVE2_KEM_PROOF) \
                               $(MLKEM_NATIVE2_GM_SAFE_PROOF) \
                               proofs/utils/mlkem_native2_kem_safe.ml
mlkem_native2/mlkem512.native: \
  proofs/mlkem512.ml $(BASE_ML) $(MLKEM_NATIVE2_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k2.ml proofs/mlkem_gen_matrix_k2_safe.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem768.native: \
  proofs/mlkem768.ml $(BASE_ML) $(MLKEM_NATIVE2_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k3.ml proofs/mlkem_gen_matrix_k3_safe.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2/mlkem1024.native: \
  proofs/mlkem1024.ml $(BASE_ML) $(MLKEM_NATIVE2_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k4.ml proofs/mlkem_gen_matrix_k4_safe.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

# Tutorial

# safety tutorial does not have safety.o and uses existing ones
tutorial/safety.native: tutorial/safety.ml proofs/bignum_mux_4.ml \
                        curve25519/bignum_mod_n25519.o ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
# other tutorials have their .o files
.SECONDEXPANSION:
tutorial/%.native: tutorial/%.ml tutorial/%.o ; ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
# Additional dependencies on .o files
tutorial/rodata.native: tutorial/rodata_local.o
tutorial/rel_simp.native: tutorial/rel_simp2.o
tutorial/rel_equivtac.native: tutorial/rel_equivtac2.o tutorial/rel_equivtac_sse.o
tutorial/rel_reordertac.native: tutorial/rel_reordertac2.o


build_proofs: $(PROOF_BINS);
# Conservatively check that there is no redefinition of "check_axioms"
# '-I' excludes binary files (*.native).
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"
build_tutorial: $(TUTORIAL_OBJ) $(TUTORIAL_PROOF_BINS);
run_proofs: build_proofs $(PROOF_LOGS);

proofs: run_proofs ; ../tools/count-proofs.sh .
tutorial: build_tutorial $(TUTORIAL_PROOF_LOGS);

# The proofs of the mlkem_native2 functions, which are not in OBJ

MLKEM_NATIVE2_PROOF_LOGS = mlkem_native2/mlkem_gen_matrix_k2.correct \
                           mlkem_native2/mlkem_gen_matrix_k3.correct \
                           mlkem_native2/mlkem_gen_matrix_k4.correct \
                           mlkem_native2/mlkem_gen_matrix_k2_safe.correct \
                           mlkem_native2/mlkem_gen_matrix_k3_safe.correct \
                           mlkem_native2/mlkem_gen_matrix_k4_safe.correct \
                           mlkem_native2/mlkem_getnoise.correct \
                           mlkem_native2/mlkem_hash_g.correct \
                           mlkem_native2/mlkem_hash_h.correct \
                           mlkem_native2/mlkem512.correct \
                           mlkem_native2/mlkem768.correct \
                           mlkem_native2/mlkem1024.correct

mlkem_native2_proofs: $(MLKEM_NATIVE2_PROOF_LOGS);

# The proofs of the AVX-512 version of mlkem_native2: those of its two
# Keccak permutations, and of their correctness and safety in one for the
# callers in the image, and then those of the image, copies of those of the
# AVX2 version above with their own parts for the permutations

MLKEM_NATIVE2_AVX512_KECCAK_PROOF = proofs/utils/keccak_spec.ml \
                                    proofs/utils/keccak_avx2.ml \
                                    proofs/utils/keccak_avx512.ml
mlkem_native2_avx512/sha3_keccak_f1600_avx512.native: \
  proofs/sha3_keccak_f1600_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KECCAK_PROOF) \
  mlkem_native2_avx512/sha3_keccak_f1600_avx512.o ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/sha3_keccak4_f1600_avx512.native: \
  proofs/sha3_keccak4_f1600_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KECCAK_PROOF) \
  mlkem_native2_avx512/sha3_keccak4_f1600_avx512.o ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/keccak_avx512_full.native: \
  proofs/utils/keccak_avx512_full.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KECCAK_PROOF) \
  proofs/sha3_keccak_f1600_avx512.ml proofs/sha3_keccak4_f1600_avx512.ml \
  mlkem_native2_avx512/sha3_keccak_f1600_avx512.o \
  mlkem_native2_avx512/sha3_keccak4_f1600_avx512.o ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

MLKEM_NATIVE2_AVX512_IMAGE_PROOF = \
  mlkem_native2_avx512/mlkem_native2_avx512_image.elf \
  proofs/mlkem_native2_avx512_image.ml \
  proofs/utils/mlkem_native2_tools.ml
MLKEM_NATIVE2_AVX512_SPONGE_PROOF = $(MLKEM_NATIVE2_AVX512_IMAGE_PROOF) \
  proofs/utils/mlkem_native2_avx512_sponge.ml \
  proofs/utils/keccak_fips202.ml \
  proofs/utils/mlkem_bytes.ml \
  $(MLKEM_NATIVE2_AVX512_KECCAK_PROOF) \
  proofs/sha3_keccak_f1600_avx512.ml \
  mlkem_native2_avx512/sha3_keccak_f1600_avx512.o
mlkem_native2_avx512/mlkem_hash_g_avx512.native: \
  proofs/mlkem_hash_g_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_SPONGE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem_hash_h_avx512.native: \
  proofs/mlkem_hash_h_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_SPONGE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_AVX512_NOISE_PROOF = $(MLKEM_NATIVE2_AVX512_SPONGE_PROOF) \
  proofs/utils/mlkem_native2_avx512_noise.ml \
  proofs/mlkem_cbd2.ml mlkem/mlkem_cbd2.o \
  proofs/mlkem_cbd3.ml mlkem/mlkem_cbd3.o \
  proofs/sha3_keccak4_f1600_avx512.ml \
  mlkem_native2_avx512/sha3_keccak4_f1600_avx512.o
mlkem_native2_avx512/mlkem_getnoise_avx512.native: \
  proofs/mlkem_getnoise_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_NOISE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_AVX512_GM_PROOF = $(MLKEM_NATIVE2_AVX512_NOISE_PROOF) \
  proofs/mlkem_getnoise_avx512.ml \
  proofs/utils/mlkem_native_fips203.ml \
  proofs/utils/mlkem_native2_avx512_matrix.ml \
  proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml \
  mlkem/mlkem_rej_uniform_alt_VARIABLE_TIME.o \
  proofs/mlkem_unpack.ml mlkem/mlkem_unpack.o mlkem/mlkem_unpack.obj \
  proofs/mlkem_gen_matrix_avx512.ml
mlkem_native2_avx512/mlkem_gen_matrix_k2_avx512.native: \
  proofs/mlkem_gen_matrix_k2_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem_gen_matrix_k3_avx512.native: \
  proofs/mlkem_gen_matrix_k3_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem_gen_matrix_k4_avx512.native: \
  proofs/mlkem_gen_matrix_k4_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_AVX512_GM_SAFE_PROOF = $(MLKEM_NATIVE2_AVX512_GM_PROOF) \
  proofs/utils/mlkem_native2_avx512_safety.ml \
  proofs/utils/keccak_avx512_full.ml \
  proofs/utils/mlkem_native2_avx512_keccak_full.ml \
  proofs/utils/mlkem_native2_rej_full.ml \
  proofs/utils/mlkem_native2_avx512_gm_safe.ml
mlkem_native2_avx512/mlkem_gen_matrix_k2_safe_avx512.native: \
  proofs/mlkem_gen_matrix_k2_safe_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem_gen_matrix_k3_safe_avx512.native: \
  proofs/mlkem_gen_matrix_k3_safe_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem_gen_matrix_k4_safe_avx512.native: \
  proofs/mlkem_gen_matrix_k4_safe_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_GM_SAFE_PROOF) ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
MLKEM_NATIVE2_AVX512_API_PROOF = $(MLKEM_NATIVE2_AVX512_NOISE_PROOF) \
  proofs/utils/mlkem_native2_avx512_safety.ml \
  proofs/utils/mlkem_compress_consts.ml \
  proofs/utils/mlkem_native2_avx512_api.ml \
  proofs/mlkem_ntt.ml mlkem/mlkem_ntt.o mlkem/mlkem_ntt.obj \
  proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml \
  mlkem/mlkem_rej_uniform_alt_VARIABLE_TIME.o \
  proofs/mlkem_hash_h_avx512.ml \
  proofs/mlkem_check_encoding.ml mlkem/mlkem_check_encoding.o
MLKEM_NATIVE2_AVX512_KEM_PROOF = $(MLKEM_NATIVE2_AVX512_API_PROOF) \
  $(MLKEM_NATIVE2_AVX512_GM_PROOF) \
  proofs/utils/mlkem_native2_kpke.ml \
  proofs/utils/mlkem_native2_avx512_kem.ml \
  proofs/mlkem_hash_g_avx512.ml \
  proofs/mlkem_intt.ml mlkem/mlkem_intt.o mlkem/mlkem_intt.obj \
  proofs/mlkem_mulcache_compute.ml \
  mlkem/mlkem_mulcache_compute.o mlkem/mlkem_mulcache_compute.obj \
  proofs/mlkem_basemul_k2.ml mlkem/mlkem_basemul_k2.o mlkem/mlkem_basemul_k2.obj \
  proofs/mlkem_basemul_k3.ml mlkem/mlkem_basemul_k3.o mlkem/mlkem_basemul_k3.obj \
  proofs/mlkem_basemul_k4.ml mlkem/mlkem_basemul_k4.o mlkem/mlkem_basemul_k4.obj \
  proofs/mlkem_tomont.ml mlkem/mlkem_tomont.o mlkem/mlkem_tomont.obj \
  proofs/mlkem_reduce.ml mlkem/mlkem_reduce.o mlkem/mlkem_reduce.obj \
  proofs/mlkem_add_reduce.ml mlkem/mlkem_add_reduce.o \
  proofs/mlkem_sub_reduce.ml mlkem/mlkem_sub_reduce.o \
  proofs/mlkem_tobytes.ml mlkem/mlkem_tobytes.o mlkem/mlkem_tobytes.obj \
  proofs/mlkem_frombytes.ml mlkem/mlkem_frombytes.o mlkem/mlkem_frombytes.obj \
  proofs/mlkem_frommsg.ml mlkem/mlkem_frommsg.o \
  proofs/mlkem_tomsg.ml mlkem/mlkem_tomsg.o \
  proofs/mlkem_compress_d4_x86.ml mlkem/mlkem_compress_d4_x86.o \
  proofs/mlkem_compress_d5_x86.ml mlkem/mlkem_compress_d5_x86.o \
  proofs/mlkem_compress_d10_x86.ml mlkem/mlkem_compress_d10_x86.o \
  proofs/mlkem_compress_d11_x86.ml mlkem/mlkem_compress_d11_x86.o \
  proofs/mlkem_decompress_d4_x86.ml mlkem/mlkem_decompress_d4_x86.o \
  proofs/mlkem_decompress_d5_x86.ml mlkem/mlkem_decompress_d5_x86.o \
  proofs/mlkem_decompress_d10_x86.ml mlkem/mlkem_decompress_d10_x86.o \
  proofs/mlkem_decompress_d11_x86.ml mlkem/mlkem_decompress_d11_x86.o
MLKEM_NATIVE2_AVX512_KEM_SAFE_PROOF = $(MLKEM_NATIVE2_AVX512_KEM_PROOF) \
  $(MLKEM_NATIVE2_AVX512_GM_SAFE_PROOF) \
  proofs/utils/mlkem_native2_avx512_kem_safe.ml
mlkem_native2_avx512/mlkem512_avx512.native: \
  proofs/mlkem512_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k2_avx512.ml \
  proofs/mlkem_gen_matrix_k2_safe_avx512.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem768_avx512.native: \
  proofs/mlkem768_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k3_avx512.ml \
  proofs/mlkem_gen_matrix_k3_safe_avx512.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
mlkem_native2_avx512/mlkem1024_avx512.native: \
  proofs/mlkem1024_avx512.ml $(BASE_ML) \
  $(MLKEM_NATIVE2_AVX512_KEM_SAFE_PROOF) \
  proofs/mlkem_gen_matrix_k4_avx512.ml \
  proofs/mlkem_gen_matrix_k4_safe_avx512.ml ; \
  ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

MLKEM_NATIVE2_AVX512_PROOF_LOGS = \
  mlkem_native2_avx512/sha3_keccak_f1600_avx512.correct \
  mlkem_native2_avx512/sha3_keccak4_f1600_avx512.correct \
  mlkem_native2_avx512/keccak_avx512_full.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k2_avx512.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k3_avx512.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k4_avx512.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k2_safe_avx512.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k3_safe_avx512.correct \
  mlkem_native2_avx512/mlkem_gen_matrix_k4_safe_avx512.correct \
  mlkem_native2_avx512/mlkem_getnoise_avx512.correct \
  mlkem_native2_avx512/mlkem_hash_g_avx512.correct \
  mlkem_native2_avx512/mlkem_hash_h_avx512.correct \
  mlkem_native2_avx512/mlkem512_avx512.correct \
  mlkem_native2_avx512/mlkem768_avx512.correct \
  mlkem_native2_avx512/mlkem1024_avx512.correct

mlkem_native2_avx512_proofs: $(MLKEM_NATIVE2_AVX512_PROOF_LOGS);


x86-insns.ml: ; ../tools/list-x86-insns.sh x86-insns.ml
# Always run sematest regardless of dependency check
FORCE: ;
# Always use max. # of cores because in Makefile one cannot get the passed number of -j.
# A portable way of getting the number of max. cores:
# https://stackoverflow.com/a/23569003/1488216
NUM_CORES_FOR_SEMATEST = $(shell getconf _NPROCESSORS_ONLN)
sematest: FORCE proofs/simulator.native; cat x86-insns.ml; ../tools/run-sematest.sh x86 $(NUM_CORES_FOR_SEMATEST)
