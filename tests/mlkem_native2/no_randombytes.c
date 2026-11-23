/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* randombytes for test drivers that use only the deterministic API but
   link a library that also has the randomized one. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  (void)out, (void)outlen;
  abort();
}
