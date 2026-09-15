#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

CLANG ?= clang

HOLDIR ?= $(HOME)/hol-light
HOLLIGHT := $(HOLDIR)/hol.sh

RV32_FLAGS = -target riscv32 -march=rv32im -mabi=ilp32
MLDSA_CPPFLAGS = -I mldsa \
	-DMLD_CONFIG_PARAMETER_SET=44 \
	-DMLD_CONFIG_USE_NATIVE_BACKEND_ARITH \
	-DMLD_CONFIG_ARITH_BACKEND_FILE=\"native/rv32im/meta.h\"

MODEL_ML = \
	proofs/base.ml \
	proofs/decode.ml \
	proofs/instruction.ml \
	proofs/riscv.ml

TUTORIAL_PROOFS := $(wildcard tutorial/*.ml)
TUTORIAL_PROOF_BINS := $(TUTORIAL_PROOFS:.ml=.native)
TUTORIAL_PROOF_LOGS := $(TUTORIAL_PROOFS:.ml=.correct)

MODEL_CHECKS := proofs/consttime.ml
MODEL_CHECK_BINS := $(MODEL_CHECKS:.ml=.native)
MODEL_CHECK_LOGS := $(MODEL_CHECKS:.ml=.correct)

proofs/%.native: proofs/%.ml $(MODEL_ML)
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

MLDSA_SOURCE_DIR = mldsa/src/native/rv32im/src
MLDSA_CONFIG = mldsa/src/common.h mldsa/src/native/rv32im/meta.h

MLDSA_OBJ = \
	mldsa/mldsa_ntt.o \
	mldsa/mldsa_ntt_slowmul.o \
	mldsa/mldsa_intt.o \
	mldsa/mldsa_intt_slowmul.o \
	mldsa/mldsa_pointwise_montgomery.o

all: $(MLDSA_OBJ)

mldsa/mldsa_ntt.o: \
	$(MLDSA_SOURCE_DIR)/mldsa_ntt_rv32im_asm.S $(MLDSA_CONFIG)
	$(CLANG) $(RV32_FLAGS) $(MLDSA_CPPFLAGS) -c $< -o $@

mldsa/mldsa_ntt_slowmul.o: \
	$(MLDSA_SOURCE_DIR)/mldsa_ntt_rv32im_slowmul_asm.S $(MLDSA_CONFIG)
	$(CLANG) $(RV32_FLAGS) $(MLDSA_CPPFLAGS) \
		-DMLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER -c $< -o $@

mldsa/mldsa_intt.o: \
	$(MLDSA_SOURCE_DIR)/mldsa_intt_rv32im_asm.S $(MLDSA_CONFIG)
	$(CLANG) $(RV32_FLAGS) $(MLDSA_CPPFLAGS) -c $< -o $@

mldsa/mldsa_intt_slowmul.o: \
	$(MLDSA_SOURCE_DIR)/mldsa_intt_rv32im_slowmul_asm.S $(MLDSA_CONFIG)
	$(CLANG) $(RV32_FLAGS) $(MLDSA_CPPFLAGS) \
		-DMLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER -c $< -o $@

mldsa/mldsa_pointwise_montgomery.o: \
	$(MLDSA_SOURCE_DIR)/mldsa_poly_pointwise_montgomery_rv32im_asm.S \
	$(MLDSA_CONFIG)
	$(CLANG) $(RV32_FLAGS) $(MLDSA_CPPFLAGS) -c $< -o $@

tutorial/%.native: tutorial/%.ml $(MODEL_ML)
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

%.correct: %.native
	../tools/run-proof.sh "$<" "$@"

build_tutorial: $(MODEL_CHECK_BINS) $(TUTORIAL_PROOF_BINS)
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"

tutorial: build_tutorial $(MODEL_CHECK_LOGS) $(TUTORIAL_PROOF_LOGS)

clean:
	rm -f $(MLDSA_OBJ) $(MODEL_CHECK_BINS) $(MODEL_CHECK_LOGS) \
		$(TUTORIAL_PROOF_BINS) $(TUTORIAL_PROOF_LOGS)

.PHONY: all build_tutorial tutorial clean
