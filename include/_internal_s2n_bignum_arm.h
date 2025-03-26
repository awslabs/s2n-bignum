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

// Variants of instructions including CFI (call frame information) annotations

#define CFI_START .cfi_startproc
#define CFI_RET ret ; .cfi_endproc

#define CFI_BL(target) bl target

#define CFI_PUSH2(lo,hi) stp     lo, hi, [sp, #-16]! ; .cfi_adjust_cfa_offset 16 ; .cfi_rel_offset lo, 0 ; .cfi_rel_offset hi, 8
#define CFI_PUSH1Z(reg) stp     reg, xzr, [sp, #-16]! ; .cfi_adjust_cfa_offset 16 ; .cfi_rel_offset reg, 0

#define CFI_POP2(lo,hi) ldp     lo, hi, [sp], #16 ; .cfi_adjust_cfa_offset (-16) ; .cfi_restore lo ; .cfi_restore hi
#define CFI_POP1Z(reg) ldp     reg, xzr, [sp], #16 ; .cfi_adjust_cfa_offset (-16) ; .cfi_restore reg

#define CFI_STACKSAVE2(lo,hi,offset) stp     lo, hi, [sp, #(offset)] ; .cfi_rel_offset lo, offset ; .cfi_rel_offset hi, offset+8
#define CFI_STACKSAVE1Z(reg,offset) stp     reg, xzr, [sp, #(offset)] ; .cfi_rel_offset reg, offset

#define CFI_STACKLOAD2(lo,hi,offset) ldp     lo, hi, [sp, #(offset)] ; .cfi_restore lo ; .cfi_restore hi
#define CFI_STACKLOAD1Z(reg,offset) ldp     reg, xzr, [sp, #(offset)] ; .cfi_restore reg

#define CFI_INC_SP(offset) add     sp, sp, #(offset) ; .cfi_adjust_cfa_offset (-(offset))
#define CFI_DEC_SP(offset) sub     sp, sp, #(offset) ; .cfi_adjust_cfa_offset (offset)
