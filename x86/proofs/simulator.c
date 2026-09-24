#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#define DEBUG 0

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
//      ...

#define STATESIZE 312
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
  { uint64_t r;
    for (r = 0; r < 32; ++r)
     { uint64_t b = 16 + r * 8;
       printf(" ZMM%-2"PRIu64" = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64
              ":%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",
              r,regs[b+7],regs[b+6],regs[b+5],regs[b+4],
                regs[b+3],regs[b+2],regs[b+1],regs[b+0]);
     }
    for (r = 0; r < 8; ++r)
      printf("    K%"PRIu64" = 0x%016"PRIx64"\n",r,regs[272+r]);
    for (r = 0; r < 8; ++r)
     { uint64_t b = 280 + r * 4;
       printf("  SP%"PRIu64" = 0x%016"PRIx64":%016"PRIx64":%016"PRIx64":%016"PRIx64"\n",
              r,regs[b+0],regs[b+1],regs[b+2],regs[b+3]);
     }
  }
}

int main(int argc, char *argv[])
{ uint64_t retval, i;

  for (i = 1; i < argc && i <= STATESIZE; ++i)
    regs[i-1] = strtoul(argv[i],NULL,0);

  if (DEBUG)
   { printf("About to call harness with these arguments\n");
     print_regs();
   }

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
