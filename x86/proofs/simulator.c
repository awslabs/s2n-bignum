#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>

#define DEBUG 0

// regs[0..STATESIZE-1]: integer registers, flags, vector registers, opmask
// registers and a small buffer in the stack. Built with ZMM_STATE (for an
// executor with AVX-512, by template_zmm.S), the vector registers are
// ZMM0-31 and the opmasks K0-7 follow; otherwise they are YMM0-15, by
// template.S, and there are no opmasks:
//
//      RAX = regfile[0]
//      RCX = regfile[1]
//      RDX = regfile[2]
//      RBX = regfile[3]
//      OF:DF:xx:xx:SF:ZF:xx:AF:xx:PF:xx:CF = regfile[4] & 0xFF
//      RBP = regfile[5]
//      RSI = regfile[6]
//      RDI = regfile[7]
//       R8 = regfile[8]
//       R9 = regfile[9]
//      R10 = regfile[10]
//      R11 = regfile[11]
//      R12 = regfile[12]
//      R13 = regfile[13]
//      R14 = regfile[14]
//      R15 = regfile[15]
//      VEC0.d[0] = regfile[16]
//      ...
//      VEC0.d[VECWORDS-1] = regfile[16+VECWORDS-1]
//      VEC1.d[0] = regfile[16+VECWORDS]
//      ...
//      K0 ... K7 = regfile[MASKBASE ... MASKBASE+7] (ZMM_STATE only)
//      [SP,...,SP+255] = regfile[STACKBASE ... STACKBASE+31]
//
// so STATESIZE is 312 with ZMM_STATE (ZMM0 at 16..23, K0 at 272, the stack
// buffer at 280..311) and 112 without (YMM0 at 16..19, the stack buffer at
// 80..111).

#ifdef ZMM_STATE
#define VECREGS 32
#define VECWORDS 8
#define MASKREGS 8
#else
#define VECREGS 16
#define VECWORDS 4
#define MASKREGS 0
#endif

#define MASKBASE (16 + VECREGS * VECWORDS)
#define STACKBASE (MASKBASE + MASKREGS)
#define STATESIZE (STACKBASE + 32)
static uint64_t regs[STATESIZE];

extern uint64_t harness(uint64_t *regfile);

void print_regs()
{ printf("   RAX = 0x%016"PRIx64"\n",regs[0]);
  printf("   RCX = 0x%016"PRIx64"\n",regs[1]);
  printf("   RDX = 0x%016"PRIx64"\n",regs[2]);
  printf("   RBX = 0x%016"PRIx64"\n",regs[3]);
  printf("   RBP = 0x%016"PRIx64"\n",regs[5]);
  printf("   RSI = 0x%016"PRIx64"\n",regs[6]);
  printf("   RDI = 0x%016"PRIx64"\n",regs[7]);
  printf("    R8 = 0x%016"PRIx64"\n",regs[8]);
  printf("    R9 = 0x%016"PRIx64"\n",regs[9]);
  printf("   R10 = 0x%016"PRIx64"\n",regs[10]);
  printf("   R11 = 0x%016"PRIx64"\n",regs[11]);
  printf("   R12 = 0x%016"PRIx64"\n",regs[12]);
  printf("   R13 = 0x%016"PRIx64"\n",regs[13]);
  printf("   R14 = 0x%016"PRIx64"\n",regs[14]);
  printf("   R15 = 0x%016"PRIx64"\n",regs[15]);
  printf("    OF = %d\n",(regs[4] & (1<<11)) != 0);
  printf("    DF = %d\n",(regs[4] & (1<<10)) != 0);
  printf("    SF = %d\n",(regs[4] & (1<<7)) != 0);
  printf("    ZF = %d\n",(regs[4] & (1<<6)) != 0);
  printf("    AF = %d\n",(regs[4] & (1<<4)) != 0);
  printf("    PF = %d\n",(regs[4] & (1<<2)) != 0);
  printf("    CF = %d\n",(regs[4] & (1<<0)) != 0);
  { int r, w;
    for (r = 0; r < VECREGS; ++r)
     { printf(" %cMM%-2d = 0x", VECWORDS == 8 ? 'Z' : 'Y', r);
       for (w = VECWORDS - 1; w >= 0; --w)
         printf("%016"PRIx64"%s", regs[16 + r * VECWORDS + w], w ? ":" : "\n");
     }
    for (r = 0; r < MASKREGS; ++r)
      printf("    K%d = 0x%016"PRIx64"\n", r, regs[MASKBASE + r]);
    for (r = 0; r < 8; ++r)
      printf("   SP%d = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",
             r, regs[STACKBASE + 4 * r], regs[STACKBASE + 4 * r + 1],
             regs[STACKBASE + 4 * r + 2], regs[STACKBASE + 4 * r + 3]);
  }
}

// The cosim campaign deliberately runs undefined encodings and faulting
// instructions. Exit at once on those signals rather than dumping core:
// the executor treats empty output as a trap either way, and a core dump
// only adds delay. The handler runs on its own stack because the
// instruction under test may leave the stack pointer unusable.

static void trap_exit(int sig)
{ _exit(128 + sig);
}

static void install_trap_handlers()
{ static char altstack[256 * 1024];
  static const int sigs[] = { SIGILL, SIGSEGV, SIGBUS, SIGFPE, SIGTRAP };
  stack_t ss = { 0 };
  struct sigaction sa = { 0 };
  size_t i;

  ss.ss_sp = altstack;
  ss.ss_size = sizeof(altstack);
  sigaltstack(&ss, NULL);

  sa.sa_handler = trap_exit;
  sa.sa_flags = SA_ONSTACK;
  sigemptyset(&sa.sa_mask);
  for (i = 0; i < sizeof(sigs) / sizeof(sigs[0]); ++i)
    sigaction(sigs[i], &sa, NULL);
}

int main(int argc, char *argv[])
{ uint64_t retval, i;

  for (i = 1; i < argc && i <= STATESIZE; ++i)
    regs[i-1] = strtoul(argv[i],NULL,0);

  if (DEBUG)
   { printf("About to call harness with these arguments\n");
     print_regs();
   }

  install_trap_handlers();
  retval = harness(regs);

  if (DEBUG)
   { printf("Called it and got %"PRIu64"\n",retval);
     print_regs();
   }
  else
   { for (i = 0; i < STATESIZE; ++i) printf("%"PRIu64" ",regs[i]);
     printf("\n");
   }

  return retval;
}
