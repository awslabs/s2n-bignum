# The ML-KEM API in AVX2 assembly for x86-64 (see README.md), the build asm
# of mlkem_native: the part of its make rules that tools/native_proofs_mk.py
# does not generate (proofs.mk, generated, has the objects and the proofs).
# The proofs of this build are about the image of the functions linked by
# GNU ld (mlkem_native2_image.elf), so every proof reads it, and the
# standalone proofs of the kernels that the proof files load read their
# Windows objects (.obj) too.

# The objects of the image of the functions, for their proofs, in the
# order of the image

MLKEM_ASM_IMAGE_OBJ = mlkem_native/asm/mlkem512.o \
                          mlkem_native/asm/mlkem768.o \
                          mlkem_native/asm/mlkem1024.o \
                          mlkem_native/asm/mlkem_gen_matrix.o \
                          mlkem_native/asm/mlkem_getnoise.o \
                          mlkem_native/asm/mlkem_hash_g.o \
                          mlkem_native/asm/mlkem_hash_h.o \
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
                          mlkem_native/asm/mlkem_native2_constants.o

# The image, linked at 0 with GNU ld (the linker script is not for the
# Darwin linker)

mlkem_native/asm/mlkem_native2_image.elf: $(MLKEM_ASM_IMAGE_OBJ) \
        mlkem_native/asm/mlkem_native2_image.ld
	$(LINK) --no-relax -e 0 -T mlkem_native/asm/mlkem_native2_image.ld \
	  -o $@ $(MLKEM_ASM_IMAGE_OBJ)

# The code of the API is in the template that the files for the parameter
# sets include, and the other files include the definitions of the layout
# of the constants and the names of the functions

MLKEM_ASM_N2_DEPS = mlkem_native/asm/mlkem_native2_consts.h \
                        mlkem_native/asm/mlkem_native2_names.h
mlkem_native/asm/mlkem512.o mlkem_native/asm/mlkem768.o \
mlkem_native/asm/mlkem1024.o: mlkem_native/asm/mlkem_kem_template.S \
                           $(MLKEM_ASM_N2_DEPS)
mlkem_native/asm/mlkem_gen_matrix.o mlkem_native/asm/mlkem_getnoise.o \
mlkem_native/asm/mlkem_hash_g.o mlkem_native/asm/mlkem_hash_h.o: \
        $(MLKEM_ASM_N2_DEPS)

MLKEM_ASM_PROOF_TARGETS = $(filter mlkem_native/asm/%, \
                            $(MLKEM_NATIVE_PROOFS:=.native))
$(MLKEM_ASM_PROOF_TARGETS): mlkem_native/asm/mlkem_native2_image.elf \
  $(filter-out mlkem_native/%, $(MLKEM_ASM_IMAGE_OBJ:.o=.obj))
