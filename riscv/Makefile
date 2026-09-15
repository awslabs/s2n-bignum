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

PROOF_SOURCES = \
	proofs/mldsa_ntt.ml \
	proofs/mldsa_ntt_slowmul.ml \
	proofs/mldsa_intt.ml \
	proofs/mldsa_intt_slowmul.ml \
	proofs/mldsa_pointwise_montgomery.ml

PROOF_SUPPORT := $(wildcard proofs/*.ml)
PROOF_BINS := $(patsubst proofs/%.ml,mldsa/%.native,$(PROOF_SOURCES))
PROOF_LOGS := $(PROOF_BINS:.native=.correct)

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

mldsa/%.native: proofs/%.ml $(PROOF_SUPPORT) mldsa/%.o
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

tutorial/%.native: tutorial/%.ml $(MODEL_ML)
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

%.correct: %.native
	../tools/run-proof.sh "$<" "$@"

build_proofs: $(MLDSA_OBJ) $(PROOF_BINS)
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"

run_proofs: build_proofs $(PROOF_LOGS)

proofs: run_proofs

build_tutorial: $(MODEL_CHECK_BINS) $(TUTORIAL_PROOF_BINS)
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"

tutorial: build_tutorial $(MODEL_CHECK_LOGS) $(TUTORIAL_PROOF_LOGS)

clean:
	rm -f $(MLDSA_OBJ) $(PROOF_BINS) $(PROOF_LOGS) \
		$(MODEL_CHECK_BINS) $(MODEL_CHECK_LOGS) \
		$(TUTORIAL_PROOF_BINS) $(TUTORIAL_PROOF_LOGS)

.PHONY: all build_proofs run_proofs proofs build_tutorial tutorial clean
