# The ML-KEM API in AVX-512 assembly for x86-64 (see README.md), the build
# asm_avx512 of mlkem_native: the part of its make rules that
# tools/native_proofs_mk.py does not generate (proofs.mk, generated, has the
# objects and the proofs). The proofs of this build are about the image of
# the functions linked by GNU ld (mlkem_native2_avx512_image.elf), so every
# proof reads it, and the standalone proofs of the kernels that the proof
# files load read their Windows objects (.obj) too.

# The objects of the image of the functions, for their proofs, in the
# order of the image

MLKEM_ASM_AVX512_IMAGE_OBJ = \
        mlkem_native/asm_avx512/mlkem512_avx512.o \
        mlkem_native/asm_avx512/mlkem768_avx512.o \
        mlkem_native/asm_avx512/mlkem1024_avx512.o \
        mlkem_native/asm_avx512/mlkem_gen_matrix_avx512.o \
        mlkem_native/asm_avx512/mlkem_getnoise_avx512.o \
        mlkem_native/asm_avx512/mlkem_hash_g_avx512.o \
        mlkem_native/asm_avx512/mlkem_hash_h_avx512.o \
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
        mlkem_native/asm_avx512/sha3_keccak_f1600_avx512.o \
        mlkem_native/asm_avx512/sha3_keccak4_f1600_avx512.o \
        mlkem_native/asm/mlkem_native2_constants.o

# The image, linked at 0 with GNU ld (the linker script is not for the
# Darwin linker)

mlkem_native/asm_avx512/mlkem_native2_avx512_image.elf: $(MLKEM_ASM_AVX512_IMAGE_OBJ) \
        mlkem_native/asm_avx512/mlkem_native2_avx512_image.ld
	$(LINK) --no-relax -e 0 -T mlkem_native/asm_avx512/mlkem_native2_avx512_image.ld \
	  -o $@ $(MLKEM_ASM_AVX512_IMAGE_OBJ)

# The AVX-512 version is assembled from the sources of ../asm, with the
# names of its mlkem_native2_names.h

MLKEM_ASM_AVX512_N2_DEPS = mlkem_native/asm/mlkem_native2_consts.h \
                           mlkem_native/asm/mlkem_native2_names.h
mlkem_native/asm_avx512/mlkem512_avx512.o mlkem_native/asm_avx512/mlkem768_avx512.o \
mlkem_native/asm_avx512/mlkem1024_avx512.o: mlkem_native/asm/mlkem_kem_template.S \
                                         $(MLKEM_ASM_AVX512_N2_DEPS)
mlkem_native/asm_avx512/mlkem_gen_matrix_avx512.o: \
        mlkem_native/asm/mlkem_gen_matrix.S $(MLKEM_ASM_AVX512_N2_DEPS)
mlkem_native/asm_avx512/mlkem_getnoise_avx512.o: \
        mlkem_native/asm/mlkem_getnoise.S $(MLKEM_ASM_AVX512_N2_DEPS)
mlkem_native/asm_avx512/mlkem_hash_g_avx512.o: \
        mlkem_native/asm/mlkem_hash_g.S $(MLKEM_ASM_AVX512_N2_DEPS)
mlkem_native/asm_avx512/mlkem_hash_h_avx512.o: \
        mlkem_native/asm/mlkem_hash_h.S $(MLKEM_ASM_AVX512_N2_DEPS)

MLKEM_ASM_AVX512_PROOF_TARGETS = $(filter mlkem_native/asm_avx512/%, \
                                   $(MLKEM_NATIVE_PROOFS:=.native))
$(MLKEM_ASM_AVX512_PROOF_TARGETS): \
  mlkem_native/asm_avx512/mlkem_native2_avx512_image.elf \
  $(filter-out mlkem_native/%, $(MLKEM_ASM_AVX512_IMAGE_OBJ:.o=.obj))
