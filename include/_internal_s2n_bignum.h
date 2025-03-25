
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

#define CFI_START .cfi_startproc
#define CFI_RET ret ; .cfi_endproc

// These are ARM-specific

#define CFI_BL(target) bl target

#define CFI_PUSH2(lo,hi) stp     lo, hi, [sp, #-16]! ; .cfi_adjust_cfa_offset 16
#define CFI_PUSH1Z(reg) stp     reg, xzr, [sp, #-16]! ; .cfi_adjust_cfa_offset 16

#define CFI_POP2(lo,hi) ldp     lo, hi, [sp], #16 ; .cfi_adjust_cfa_offset (-16)
#define CFI_POP1Z(reg) ldp     reg, xzr, [sp], #16 ; .cfi_adjust_cfa_offset (-16)

#define CFI_STACKSAVE2(lo,hi,offset) stp     lo, hi, [sp, #(offset)]
#define CFI_STACKSAVE1Z(reg,offset) stp     reg, xzr, [sp, #(offset)]

#define CFI_STACKLOAD2(lo,hi,offset) ldp     lo, hi, [sp, #(offset)]
#define CFI_STACKLOAD1Z(reg,offset) ldp     reg, xzr, [sp, #(offset)]

#define CFI_INC_SP(offset) add     sp, sp, #(offset) ; .cfi_adjust_cfa_offset (-(offset))
#define CFI_DEC_SP(offset) sub     sp, sp, #(offset) ; .cfi_adjust_cfa_offset (offset)

// These are x86-specific

#define CFI_CALL(target) call    target

#define CFI_PUSH(reg) push    reg ; .cfi_adjust_cfa_offset 8
#define CFI_POP(reg) pop     reg ; .cfi_adjust_cfa_offset (-8)

#define CFI_INC_RSP(offset) add     rsp, offset ; .cfi_adjust_cfa_offset (-(offset))
#define CFI_DEC_RSP(offset) sub     rsp, offset ; .cfi_adjust_cfa_offset (offset)
