#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

HOLDIR ?= $(HOME)/hol-light
HOLLIGHT := $(HOLDIR)/hol.sh

TESTS := $(wildcard *_tests.ml)
TEST_BINS := $(TESTS:.ml=.native)
TEST_LOGS := $(TESTS:.ml=.correct)
SHARED_ML := $(filter-out $(TESTS),$(wildcard *.ml))

.PHONY: build_tests test test_tactics clean

build_tests: $(TEST_BINS)

test: build_tests $(TEST_LOGS)

test_tactics: tactics_tests.correct

%.native: %.ml $(SHARED_ML)
	../tools/build-proof.sh "$<" "$(HOLLIGHT)" "$@"

%.correct: %.native
	../tools/run-proof.sh "$<" "$@"

clean:
	rm -f $(TEST_BINS) $(TEST_LOGS)
