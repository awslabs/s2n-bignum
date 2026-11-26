# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Stress hol-d's lifecycle and concurrency. Needs Linux, and HOLDIR naming a
# HOL Light checkout built with HOLLIGHT_USE_MODULE=1, with its OCaml
# switch active.
HOLDIR ?= $(HOME)/hol-light
.PHONY: all
all:
	@$(MAKE) -s -C .. HOLDIR="$(HOLDIR)"
	@HOLDIR="$(abspath $(HOLDIR))" python3 stress.py
