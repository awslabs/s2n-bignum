// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// -------------------------------------------------------------------------
// Print the optional CPU features with which x86simulate runs instructions.
//
// x86simulate --features builds and runs this program the same way as the
// per-case harness, so the result describes the CPU that executes the
// cases: the host, a virtual machine, or an emulator such as qemu-x86_64
// with its -cpu model. The output is one line of space-separated names,
// using the names of Linux's /proc/cpuinfo flags, from:
//
//   pclmulqdq ssse3 sse4_1 popcnt aes avx abm bmi1 avx2 bmi2 adx vpclmulqdq
//
// Names are omitted if the feature is absent. avx, avx2 and vpclmulqdq,
// whose VEX forms use the YMM state, also require the operating system to
// enable that state (CPUID.1:ECX.OSXSAVE and XCR0 bits 1 and 2).
// -------------------------------------------------------------------------

#include <stdint.h>
#include <stdio.h>

static void cpuid(uint32_t leaf, uint32_t subleaf, uint32_t r[4])
{
  __asm__ __volatile__("cpuid"
                       : "=a"(r[0]), "=b"(r[1]), "=c"(r[2]), "=d"(r[3])
                       : "a"(leaf), "c"(subleaf));
}

static int bit(uint32_t word, int n) { return (word >> n) & 1; }

static void feature(int present, const char *name, int *first)
{
  if (!present) return;
  printf("%s%s", *first ? "" : " ", name);
  *first = 0;
}

int main(void)
{
  uint32_t r[4], max_leaf, max_extended, ecx1, ebx7 = 0, ecx7 = 0, ecx81 = 0;
  int ymm = 0, avx, first = 1;

  cpuid(0, 0, r);
  max_leaf = r[0];
  cpuid(1, 0, r);
  ecx1 = r[2];

  // XGETBV raises #UD unless CPUID.1:ECX.OSXSAVE is set
  if (bit(ecx1, 27))
  {
    uint32_t xcr0, xcr0_hi;
    __asm__ __volatile__("xgetbv" : "=a"(xcr0), "=d"(xcr0_hi) : "c"(0));
    ymm = (xcr0 & 6) == 6;
  }

  // Leaves above the maximum return the data of another leaf
  if (max_leaf >= 7)
  {
    cpuid(7, 0, r);
    ebx7 = r[1];
    ecx7 = r[2];
  }
  cpuid(0x80000000u, 0, r);
  max_extended = r[0];
  if (max_extended >= 0x80000001u)
  {
    cpuid(0x80000001u, 0, r);
    ecx81 = r[2];
  }

  avx = ymm && bit(ecx1, 28);

  feature(bit(ecx1, 1), "pclmulqdq", &first);
  feature(bit(ecx1, 9), "ssse3", &first);
  feature(bit(ecx1, 19), "sse4_1", &first);
  feature(bit(ecx1, 23), "popcnt", &first);
  feature(bit(ecx1, 25), "aes", &first);
  feature(avx, "avx", &first);
  feature(bit(ecx81, 5), "abm", &first);
  feature(bit(ebx7, 3), "bmi1", &first);
  feature(avx && bit(ebx7, 5), "avx2", &first);
  feature(bit(ebx7, 8), "bmi2", &first);
  feature(bit(ebx7, 19), "adx", &first);
  feature(avx && bit(ecx7, 10), "vpclmulqdq", &first);
  printf("\n");
  return 0;
}
