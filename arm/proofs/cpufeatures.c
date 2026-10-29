// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// -------------------------------------------------------------------------
// Print the optional CPU features with which armsimulate runs instructions.
//
// armsimulate --features builds and runs this program the same way as the
// per-case harness, so the result describes the CPU that executes the
// cases: the host, a virtual machine, or an emulator such as qemu-aarch64
// with its -cpu model. The output is one line of space-separated names,
// using the names of Linux's /proc/cpuinfo Features, from:
//
//   aes pmull sha2 sha3 sha512
//
// Names are omitted if the feature is absent. The features come from
// AT_HWCAP on Linux and from the hw.optional sysctls on macOS. On other
// systems the program prints nothing and fails, so that the features are
// reported as unknown rather than absent.
// -------------------------------------------------------------------------

#include <stdio.h>

static void feature(int present, const char *name, int *first)
{
  if (!present) return;
  printf("%s%s", *first ? "" : " ", name);
  *first = 0;
}

#if defined(__linux__)

#include <sys/auxv.h>

// Bit positions of AT_HWCAP, as in the kernel's asm/hwcap.h
#define CAP_AES (1ul << 3)
#define CAP_PMULL (1ul << 4)
#define CAP_SHA2 (1ul << 6)
#define CAP_SHA3 (1ul << 17)
#define CAP_SHA512 (1ul << 21)

int main(void)
{
  unsigned long hwcap = getauxval(AT_HWCAP);
  int first = 1;
  feature((hwcap & CAP_AES) != 0, "aes", &first);
  feature((hwcap & CAP_PMULL) != 0, "pmull", &first);
  feature((hwcap & CAP_SHA2) != 0, "sha2", &first);
  feature((hwcap & CAP_SHA3) != 0, "sha3", &first);
  feature((hwcap & CAP_SHA512) != 0, "sha512", &first);
  printf("\n");
  return 0;
}

#elif defined(__APPLE__)

#include <stddef.h>
#include <sys/sysctl.h>

// Read a sysctl flag, trying the older name if the first does not exist
static int sysctl_flag(const char *name, const char *older)
{
  int value = 0;
  size_t size = sizeof(value);
  if (sysctlbyname(name, &value, &size, NULL, 0) == 0) return value != 0;
  size = sizeof(value);
  if (older != NULL && sysctlbyname(older, &value, &size, NULL, 0) == 0)
    return value != 0;
  return 0;
}

int main(void)
{
  int first = 1;
  feature(sysctl_flag("hw.optional.arm.FEAT_AES", NULL), "aes", &first);
  feature(sysctl_flag("hw.optional.arm.FEAT_PMULL", NULL), "pmull", &first);
  feature(sysctl_flag("hw.optional.arm.FEAT_SHA256", NULL), "sha2", &first);
  feature(sysctl_flag("hw.optional.arm.FEAT_SHA3", "hw.optional.armv8_2_sha3"),
          "sha3", &first);
  feature(sysctl_flag("hw.optional.arm.FEAT_SHA512",
                      "hw.optional.armv8_2_sha512"),
          "sha512", &first);
  printf("\n");
  return 0;
}

#else

int main(void)
{
  fprintf(stderr, "cpufeatures: no feature detection for this system\n");
  return 1;
}

#endif
