#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

HOLDIR ?= $(HOME)/hol-light
HOLLIGHT := $(HOLDIR)/hol.sh

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

tutorial/%.native: tutorial/%.ml $(MODEL_ML)
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

%.correct: %.native
	../tools/run-proof.sh "$<" "$@"

build_tutorial: $(MODEL_CHECK_BINS) $(TUTORIAL_PROOF_BINS)
	! grep -RI "check_axioms" . ../common/ --exclude="Makefile"

tutorial: build_tutorial $(MODEL_CHECK_LOGS) $(TUTORIAL_PROOF_LOGS)

clean:
	rm -f $(MODEL_CHECK_BINS) $(MODEL_CHECK_LOGS) \
		$(TUTORIAL_PROOF_BINS) $(TUTORIAL_PROOF_LOGS)

.PHONY: build_tutorial tutorial clean
