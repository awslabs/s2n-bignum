#ifdef __APPLE__
#   define S2N_BN_SYMBOL(NAME) _##NAME
#   if defined(__AARCH64EL__) || defined(__ARMEL__)
#     define __LF %%
#   else
#     define __LF ;
#   endif
#else
#   define S2N_BN_SYMBOL(name) name
#   define __LF ;
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

#ifdef __APPLE__
#   define S2N_BN_FUNCTION_TYPE_DIRECTIVE(name) /* Not used in Mach-O */
#else
#   define S2N_BN_FUNCTION_TYPE_DIRECTIVE(name) .type name, %function
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

// Variants of instructions including CFI (call frame information) annotations

#define CFI_START .cfi_startproc
#define CFI_RET ret ; .cfi_endproc

#define CFI_CALL(target) call    target

#define CFI_PUSH(reg) push    reg ; .cfi_adjust_cfa_offset 8 ; .cfi_rel_offset reg, 0
#define CFI_POP(reg) pop     reg ; .cfi_adjust_cfa_offset (-8) ; .cfi_restore reg

#define CFI_INC_RSP(offset) add     rsp, offset ; .cfi_adjust_cfa_offset (-(offset))
#define CFI_DEC_RSP(offset) sub     rsp, offset ; .cfi_adjust_cfa_offset (offset)
