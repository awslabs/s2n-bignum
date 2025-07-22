// On x86 machines, restrict the set of tested functions appropriately
// if the machine does not seem to support the BMI2 and ADX extensions.

enum arch_name { ARCH_X86_64, ARCH_AARCH64 };

#ifdef __x86_64__

int cpuid_extendedfeatures(void)
{ int a = 7, b = 0, c = 0, d = 0;
  asm ("cpuid\n\t"
    : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
    : "0" (a), "2" (c));
  return b;
}

int supports_bmi2_and_adx(void)
{ int c = cpuid_extendedfeatures();
  return (c & (1ul<<8)) && (c & (1ul<<19));
}

enum arch_name get_arch_name()
{ return ARCH_X86_64;
}

int supports_arm_sha3(void)
{ // Not an ARM machine at all
  return 0;
}

#else

int supports_bmi2_and_adx(void)
{ // AArch64 does not support BMI2 or ADX extension.
  return 0;
}

#if __linux__
  #include <sys/auxv.h>
  #include <asm/hwcap.h>
  int supports_arm_sha3(void)
  {
    long hwcaps = getauxval(AT_HWCAP);
    return (hwcaps & HWCAP_SHA3) != 0;
  }

#else

  int supports_arm_sha3(void)
  {
  #if __ARM_FEATURE_SHA3
    return 1;
  #else
    return 0;
  #endif
  }
#endif

enum arch_name get_arch_name()
{ return ARCH_AARCH64;
}

#endif
