#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>

#define DEBUG 0

// regs[0 ~ 31]:  X registers
// regs[32 + 2*i]: Qi.d[0]
// regs[32 + 2*i+1]: Qi.d[1]
// regs[96..127]: [SP,...SP+255]

#define STATESIZE 128
static uint64_t regs[STATESIZE];

extern uint64_t harness(uint64_t *regfile);

void print_regs()
{ uint64_t i;
  for (i = 0; i < 32; ++i)
    printf("   %sX%"PRId64" = 0x%016"PRIx64"\n",((i<10)?" ":""),i,regs[i]);
  for (i = 0; i < 32; ++i)
    printf("   %sQ%"PRId64".{d[0], d[1]} = { 0x%016"PRIx64", 0x%016"PRIx64" }\n",((i<10)?" ":""),i,regs[32+i*2],regs[32+i*2+1]);
  for (i = 0; i < 32; ++i)
    printf("SP[%"PRId64"] = 0x%016"PRIx64"\n",i,regs[96+i]);
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
