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
PREPROCESS=sed -e 's/\/\/.*//' | $(CC) -E -I../include $(SYMBOL_HIDING) -xassembler-with-cpp -
else
PREPROCESS=$(CC) -E -I../include $(SYMBOL_HIDING) -xassembler-with-cpp -
endif

# Generally GNU-type assemblers are happy with multiple instructions on
# a line, but we split them up anyway just in case.

SPLIT=tr ';' '\n'

# If actually on an ARM8 machine, just use the assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). For the clang
# version on OS X we just add the "-arch arm64" option. For the Linux/gcc
# toolchain we assume the presence of the special cross-assembler. This
# can be installed via something like:
#
#  sudo apt-get install binutils-aarch64-linux-gnu

ifeq ($(ARCHTYPE_RESULT),aarch64)
ASSEMBLE=as -march=armv8.2-a+sha3
OBJDUMP=objdump -d
else
ifeq ($(ARCHTYPE_RESULT),arm64)
ASSEMBLE=as -march=armv8.2-a+sha3
OBJDUMP=objdump -d
else
ifeq ($(OSTYPE_RESULT),Darwin)
ASSEMBLE=as -arch arm64 -march=armv8.2-a+sha3
OBJDUMP=otool -tvV
else
ASSEMBLE=aarch64-linux-gnu-as -march=armv8.2-a+sha3
OBJDUMP=aarch64-linux-gnu-objdump -d
endif
endif
endif

# List of object files for point operations and bignum operations

POINT_OBJ = curve25519/curve25519_ladderstep.o \
            curve25519/curve25519_ladderstep_alt.o \
            curve25519/curve25519_pxscalarmul.o \
            curve25519/curve25519_pxscalarmul_alt.o \
            curve25519/curve25519_x25519.o \
            curve25519/curve25519_x25519_alt.o \
            curve25519/curve25519_x25519_byte.o \
            curve25519/curve25519_x25519_byte_alt.o \
            curve25519/curve25519_x25519base.o \
            curve25519/curve25519_x25519base_alt.o \
            curve25519/curve25519_x25519base_byte.o \
            curve25519/curve25519_x25519base_byte_alt.o \
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
             curve25519/bignum_double_p25519.o \
             curve25519/bignum_inv_p25519.o \
             curve25519/bignum_invsqrt_p25519.o \
             curve25519/bignum_invsqrt_p25519_alt.o \
             curve25519/bignum_madd_n25519.o \
             curve25519/bignum_madd_n25519_alt.o \
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
             fastmul/bignum_emontredc_8n_cdiff.o \
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
             generic/bignum_copy_row_from_table_8n.o \
             generic/bignum_copy_row_from_table_16.o \
             generic/bignum_copy_row_from_table_32.o \
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
             mlkem/mlkem_basemul_k2.o \
             mlkem/mlkem_basemul_k3.o \
             mlkem/mlkem_basemul_k4.o \
             mlkem/mlkem_intt.o \
             mlkem/mlkem_mulcache_compute.o \
             mlkem/mlkem_ntt.o \
             mlkem/mlkem_reduce.o \
             mlkem/mlkem_tobytes.o \
             mlkem/mlkem_tomont.o \
             mlkem/mlkem_rej_uniform_VARIABLE_TIME.o \
             p256/bignum_add_p256.o \
             p256/bignum_bigendian_4.o \
             p256/bignum_cmul_p256.o \
             p256/bignum_deamont_p256.o \
             p256/bignum_demont_p256.o \
             p256/bignum_double_p256.o \
             p256/bignum_half_p256.o \
             p256/bignum_inv_p256.o \
             p256/bignum_littleendian_4.o \
             p256/bignum_mod_n256.o \
             p256/bignum_mod_n256_4.o \
             p256/bignum_mod_p256.o \
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
             p256/bignum_triple_p256.o \
             p384/bignum_add_p384.o \
             p384/bignum_bigendian_6.o \
             p384/bignum_cmul_p384.o \
             p384/bignum_deamont_p384.o \
             p384/bignum_demont_p384.o \
             p384/bignum_double_p384.o \
             p384/bignum_half_p384.o \
             p384/bignum_inv_p384.o \
             p384/bignum_littleendian_6.o \
             p384/bignum_mod_n384.o \
             p384/bignum_mod_n384_6.o \
             p384/bignum_mod_p384.o \
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
             p384/bignum_triple_p384.o \
             p521/bignum_add_p521.o \
             p521/bignum_cmul_p521.o \
             p521/bignum_deamont_p521.o \
             p521/bignum_demont_p521.o \
             p521/bignum_double_p521.o \
             p521/bignum_fromlebytes_p521.o \
             p521/bignum_half_p521.o \
             p521/bignum_inv_p521.o \
             p521/bignum_mod_n521_9.o \
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
             secp256k1/bignum_add_p256k1.o \
             secp256k1/bignum_cmul_p256k1.o \
             secp256k1/bignum_deamont_p256k1.o \
             secp256k1/bignum_demont_p256k1.o \
             secp256k1/bignum_double_p256k1.o \
             secp256k1/bignum_half_p256k1.o \
             secp256k1/bignum_mod_n256k1_4.o \
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
             secp256k1/bignum_triple_p256k1.o \
             sha3/sha3_keccak_f1600.o \
             sha3/sha3_keccak_f1600_alt.o \
             sha3/sha3_keccak2_f1600.o \
             sha3/sha3_keccak2_f1600_alt.o \
             sha3/sha3_keccak4_f1600.o \
             sha3/sha3_keccak4_f1600_alt.o \
             sha3/sha3_keccak4_f1600_alt2.o \
             sm2/bignum_add_sm2.o \
             sm2/bignum_cmul_sm2.o \
             sm2/bignum_deamont_sm2.o \
             sm2/bignum_demont_sm2.o \
             sm2/bignum_double_sm2.o \
             sm2/bignum_half_sm2.o \
             sm2/bignum_inv_sm2.o \
             sm2/bignum_mod_nsm2.o \
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
             sm2/bignum_triple_sm2.o

UNOPT_OBJ = p256/unopt/bignum_montmul_p256_base.o \
            p256/unopt/bignum_montsqr_p256_base.o \
            p256/unopt/p256_montjadd.o \
            p256/unopt/p256_montjdouble.o \
            p384/unopt/bignum_montmul_p384_base.o \
            p384/unopt/bignum_montsqr_p384_base.o \
            p384/unopt/p384_montjadd.o \
            p384/unopt/p384_montjdouble.o \
            p521/unopt/bignum_montmul_p521_base.o \
            p521/unopt/bignum_montsqr_p521_base.o \
            p521/unopt/bignum_mul_p521_base.o \
            p521/unopt/bignum_sqr_p521_base.o \
            fastmul/unopt/bignum_emontredc_8n_base.o \
            fastmul/unopt/bignum_emontredc_8n_cdiff_base.o \
            fastmul/unopt/bignum_mul_8_16_base.o \
            fastmul/unopt/bignum_sqr_8_16_base.o

OBJ = $(POINT_OBJ) $(BIGNUM_OBJ)

# Tutorial assembly files

TUTORIAL_PROOFS = $(wildcard tutorial/*.ml)

TUTORIAL_OBJ = $(TUTORIAL_PROOFS:.ml=.o) tutorial/rel_loop2.o tutorial/rel_simp2.o tutorial/rel_veceq2.o tutorial/rel_equivtac2.o tutorial/rel_reordertac2.o

# According to
# https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms,
# x18 should not be used for Apple platforms. Check this using grep.

%.o : %.S
	cat $< | $(PREPROCESS) | $(SPLIT) | grep -v -E '^\s+\.(quad|hword)\s+(0x|-)?[0-9a-f]+$$' | $(ASSEMBLE) -o $@ -
	$(OBJDUMP) $@ | ( ( ! grep --ignore-case -E 'w18|[^0]x18' ) || ( rm $@ ; exit 1 ) )
	cat $< | $(PREPROCESS) | $(SPLIT) | $(ASSEMBLE) -o $@ -

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

clean:; rm -f libs2nbignum.a */*.o */*/*.o */*.correct */*.native

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

HOLDIR?=$(HOME)/hol-light
HOLLIGHT:=$(HOLDIR)/hol.sh

PROOF_BINS = $(OBJ:.o=.native)
PROOF_LOGS = $(OBJ:.o=.correct)
TUTORIAL_PROOF_BINS = $(TUTORIAL_PROOFS:.ml=.native)
TUTORIAL_PROOF_LOGS = $(TUTORIAL_PROOFS:.ml=.correct)

# Build precompiled native binaries of HOL Light proofs

proofs/simulator.native: proofs/simulator.ml ; ../tools/build-proof.sh proofs/simulator.ml "$(HOLLIGHT)" "$@"

.SECONDEXPANSION:
%.native: proofs/$$(*F).ml %.o ; ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

# Run them and print the standard output+error at *.correct

%.correct: %.native ; ../tools/run-proof.sh "$<" "$@"

# Cases where a proof uses other proofs for lemmas and/or subroutines

p256/bignum_montmul_p256.native: p256/unopt/bignum_montmul_p256_base.o
p384/bignum_montmul_p384.native: p384/unopt/bignum_montmul_p384_base.o
p521/bignum_montmul_p521.native: p521/unopt/bignum_montmul_p521_base.o
p256/bignum_montsqr_p256.native: p256/unopt/bignum_montsqr_p256_base.o
p384/bignum_montsqr_p384.native: p384/unopt/bignum_montsqr_p384_base.o
p521/bignum_montsqr_p521.native: p521/unopt/bignum_montsqr_p521_base.o
p521/bignum_mul_p521.native: p521/unopt/bignum_mul_p521_base.o
p521/bignum_sqr_p521.native: p521/unopt/bignum_sqr_p521_base.o
fastmul/bignum_emontredc_8n_cdiff.native: fastmul/unopt/bignum_emontredc_8n_base.o fastmul/unopt/bignum_emontredc_8n_cdiff_base.o
fastmul/bignum_mul_8_16.native: fastmul/unopt/bignum_mul_8_16_base.o
fastmul/bignum_sqr_8_16.native: fastmul/unopt/bignum_sqr_8_16_base.o
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
p256/p256_montjadd.native: p256/unopt/p256_montjadd.o p256/bignum_montsqr_p256.native p256/bignum_montmul_p256.native p256/bignum_sub_p256.native
p256/p256_montjdouble.native: p256/unopt/p256_montjdouble.o p256/bignum_montsqr_p256.native p256/bignum_montmul_p256.native p256/bignum_sub_p256.native p256/bignum_add_p256.native
p256/p256_montjscalarmul.native: p256/p256_montjadd.native p256/p256_montjdouble.native
p256/p256_montjscalarmul_alt.native: p256/p256_montjadd_alt.native p256/p256_montjdouble_alt.native
p256/p256_scalarmul.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/bignum_tomont_p256.native p256/p256_montjadd.native p256/p256_montjdouble.native p256/p256_montjmixadd.native
p256/p256_scalarmul_alt.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjadd_alt.native p256/p256_montjdouble_alt.native p256/p256_montjmixadd_alt.native
p256/p256_scalarmulbase.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjmixadd.native
p256/p256_scalarmulbase_alt.native: p256/bignum_demont_p256.native p256/bignum_inv_p256.native p256/p256_montjmixadd_alt.native
p384/p384_montjadd.native: p384/unopt/p384_montjadd.o p384/bignum_montsqr_p384.native p384/bignum_montmul_p384.native p384/bignum_sub_p384.native
p384/p384_montjdouble.native: p384/unopt/p384_montjdouble.o p384/bignum_montsqr_p384.native p384/bignum_montmul_p384.native p384/bignum_sub_p384.native p384/bignum_add_p384.native
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

# Tutorial

.SECONDEXPANSION:
tutorial/%.native: tutorial/%.ml tutorial/%.o ; ../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"
# Additional dependencies on .o files
tutorial/rel_loop.native: tutorial/rel_loop2.o
tutorial/rel_simp.native: tutorial/rel_simp2.o
tutorial/rel_veceq.native: tutorial/rel_veceq2.o
tutorial/rel_equivtac.native: tutorial/rel_equivtac2.o
tutorial/rel_reordertac.native: tutorial/rel_reordertac2.o


unopt: $(UNOPT_OBJ)

build_proofs: $(UNOPT_OBJ) $(PROOF_BINS)
# Conservatively check that there is no redefinition of "check_axioms"
# '-I' excludes binary files (*.native).
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"
build_tutorial: $(TUTORIAL_OBJ) $(TUTORIAL_PROOF_BINS);
run_proofs: build_proofs $(PROOF_LOGS);

proofs: run_proofs ; ../tools/count-proofs.sh .
tutorial: build_tutorial $(TUTORIAL_PROOF_LOGS);

# Always run sematest regardless of dependency check
FORCE: ;
# Always use max. # of cores because in Makefile one cannot get the passed number of -j.
# A portable way of getting the number of max. cores:
# https://stackoverflow.com/a/23569003/1488216
NUM_CORES_FOR_SEMATEST = $(shell getconf _NPROCESSORS_ONLN)
sematest: FORCE $(OBJ) proofs/simulator_iclasses.ml proofs/simulator.native
	../tools/run-sematest.sh arm $(NUM_CORES_FOR_SEMATEST)
