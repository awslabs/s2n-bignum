# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Run every tutorial step, or one with `make 03-plugins`.
# HOLDIR must name a HOL Light checkout built with HOLLIGHT_USE_MODULE=1.
STEPS := $(sort $(patsubst %/run.sh,%,$(wildcard */run.sh)))
.PHONY: all $(STEPS)
all: $(STEPS)
$(STEPS):
	@echo "=== tutorial $@"
	@bash $@/run.sh
