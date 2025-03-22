
#ifdef __APPLE__
#   define S2N_BN_SYMBOL(NAME) _##NAME
#else
#   define S2N_BN_SYMBOL(name) name
#endif

#define S2N_BN_SYM_VISIBILITY_DIRECTIVE(name) .globl S2N_BN_SYMBOL(name)
#ifdef S2N_BN_HIDE_SYMBOLS
#   ifdef __APPLE__
#      define S2N_BN_SYM_PRIVACY_DIRECTIVE(name) .private_extern S2N_BN_SYMBOL(name)
#   else
#      define S2N_BN_SYM_PRIVACY_DIRECTIVE(name) .hidden S2N_BN_SYMBOL(name)
#   endif
#else
#   define S2N_BN_SYM_PRIVACY_DIRECTIVE(name)  /* NO-OP: S2N_BN_SYM_PRIVACY_DIRECTIVE */
#endif

// Enable indirect branch tracking support unless explicitly disabled
// with -DNO_IBT. If the platform supports CET, simply inherit this from
// the usual header. Otherwise manually define _CET_ENDBR, used at each
// x86 entry point, to be the ENDBR64 instruction, with an explicit byte
// sequence for compilers/assemblers that don't know about it. Note that
// it is safe to use ENDBR64 on all platforms, since the encoding is by
// design interpreted as a NOP on all pre-CET x86_64 processors. The only
// downside is a small increase in code size and potentially a modest
// slowdown from executing one more instruction.

#if NO_IBT
#define _CET_ENDBR
#elif defined(__CET__)
#include <cet.h>
#else
#define _CET_ENDBR .byte 0xf3,0x0f,0x1e,0xfa
#endif

// Variants of standard instructions with CFI (call frame information)
// annotations included. Two are common to x86 and ARM:

#define CFI_START
#define CFI_RET ret

// These are ARM-specific

#define CFI_BL(target) bl target

#define CFI_PUSH2(lo,hi) stp     lo, hi, [sp, #-16]!
#define CFI_POP2(lo,hi) ldp     lo, hi, [sp], #16

#define CFI_INC_SP(offset) add     sp, sp, #(offset)
#define CFI_DEC_SP(offset) sub     sp, sp, #(offset)

// These are x86-specific

#define CFI_CALL(target) call    target

#define CFI_PUSH(reg) push    reg
#define CFI_POP(reg) pop     reg

#define CFI_INC_RSP(offset) add     rsp, offset
#define CFI_DEC_RSP(offset) sub     rsp, offset
