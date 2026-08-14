# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# KAT gate for the AES-256-GCM whole-blocks DECRYPT kernel.
# Host must be aarch64 (the .o objects run natively).
#
#   make            build + run the PRIMARY differential gate (no aws-lc dep)
#   make run        alias for the default
#   make absolute   build + run the ABSOLUTE enc->dec round-trip (needs aws-lc)
#   make all        run both
#   make clean      remove build artifacts
#
# The objects under test live one directory up (build them there first):
#   aesv8_gcm_8x_dec_256_wb.o   (target)
#   aesv8_gcm_8x_dec_256.o      (trusted differential reference)
#   aesv8_gcm_8x_enc_256.o      (trusted encrypt kernel, for the round-trip)
#
# The ABSOLUTE test additionally assembles two READ-ONLY aws-lc aarch64 asm
# files (never modified) for aes_hw_set_encrypt_key / aes_hw_encrypt /
# gcm_init_v8.  Override AWS_LC_DIR if aws-lc lives elsewhere.

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11
AESDIR   = ..

WB_OBJ   = $(AESDIR)/aesv8_gcm_8x_dec_256_wb.o
SIB_OBJ  = $(AESDIR)/aesv8_gcm_8x_dec_256.o
ENC_OBJ  = $(AESDIR)/aesv8_gcm_8x_enc_256.o

AWS_LC_DIR ?= $(HOME)/workplace/git-code/aws-lc
AWS_LC_GEN  = $(AWS_LC_DIR)/generated-src/linux-aarch64/crypto/fipsmodule
AWS_LC_ASM  = $(AWS_LC_GEN)/aesv8-armx.S $(AWS_LC_GEN)/ghashv8-armx.S

.PHONY: all run absolute clean
all: run absolute

kat_wb_dec: kat_wb_dec.c $(WB_OBJ) $(SIB_OBJ)
	$(CC) $(CFLAGS) -o $@ kat_wb_dec.c $(WB_OBJ) $(SIB_OBJ)

run: kat_wb_dec
	./kat_wb_dec

kat_wb_dec_absolute: kat_wb_dec_absolute.c $(WB_OBJ) $(ENC_OBJ) $(AWS_LC_ASM)
	$(CC) $(CFLAGS) -I $(AWS_LC_DIR)/include -o $@ kat_wb_dec_absolute.c \
		$(WB_OBJ) $(ENC_OBJ) $(AWS_LC_ASM)

absolute: kat_wb_dec_absolute
	./kat_wb_dec_absolute

clean:
	rm -f kat_wb_dec kat_wb_dec_absolute
