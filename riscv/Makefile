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

# Cosimulation (`make sematest`) checks the RV32IM model against a concrete
# executor: it builds a small freestanding monitor with a bare-metal RISC-V
# toolchain and runs it under a system-mode QEMU. None of this is needed for
# the ordinary model/tutorial build or for proof checking; it is used only by
# the cosim targets below. On Ubuntu the tools can be installed via something
# like:
#
#   sudo apt-get install qemu-system-misc \
#       gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf
#
# The packaged bare-metal toolchain is named riscv64-unknown-elf-* and builds
# the 32-bit runner through its rv32im/ilp32 multilib; the RISC-V system
# emulator (qemu-system-riscv32) comes from qemu-system-misc. Override
# RISCV_PREFIX (or QEMU_RISCV32, read by proofs/cosim-runner) to use a
# different toolchain or emulator.
RISCV_PREFIX ?= riscv64-unknown-elf-
RISCV_CC ?= $(RISCV_PREFIX)gcc
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_MARCH ?= rv32im_zicsr_zifencei

COSIM_CFLAGS ?= -Os -Wall -Wextra -ffreestanding -fno-builtin \
	-fno-pic -fno-pie -fno-stack-protector
COSIM_LDFLAGS ?= -static -nostdlib -nostartfiles -Wl,--no-relax \
	-Wl,--build-id=none

.PHONY: build_tutorial tutorial sematest clean FORCE

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

proofs/cosim-runner.elf: proofs/cosim_runner.c proofs/cosim_start.S \
		proofs/cosim.ld
	$(RISCV_CC) -march=$(RISCV_MARCH) -mabi=ilp32 -mcmodel=medany \
		$(COSIM_CFLAGS) $(COSIM_LDFLAGS) -Wl,-T,proofs/cosim.ld \
		-o $@ proofs/cosim_runner.c proofs/cosim_start.S

proofs/cosim-runner.bin: proofs/cosim-runner.elf
	$(RISCV_OBJCOPY) -O binary $< $@

proofs/simulator.native: proofs/simulator.ml ../common/cosim.ml \
		../common/sematest.ml $(MODEL_ML) proofs/cosim-runner \
		proofs/cosim-runner.bin
	../tools/build-proof.sh proofs/simulator.ml "$(HOLLIGHT)" "$@"

FORCE:

NUM_CORES_FOR_SEMATEST ?= 1

sematest: FORCE proofs/simulator.native
	../tools/run-sematest.sh riscv $(NUM_CORES_FOR_SEMATEST)

clean:
	rm -f $(MODEL_CHECK_BINS) $(MODEL_CHECK_LOGS) \
		$(TUTORIAL_PROOF_BINS) $(TUTORIAL_PROOF_LOGS) \
		proofs/simulator.native \
		proofs/cosim-runner.elf proofs/cosim-runner.bin
