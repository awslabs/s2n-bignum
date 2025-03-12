
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

// The standard approach to enabling CET based on platform would be:
//
//  #ifdef __CET__
//  #include <cet.h>
//  #else
//  #define _CET_ENDBR
//  #endif
//
// We instead enable it by default unless disabled with -DNO_IBT
// We also give ENDBR64 as an explicit byte sequence so the code
// still builds on old assemblers/compilers that don't support it.

#if NO_IBT
#define _CET_ENDBR
#else
#define _CET_ENDBR .byte 0xf3,0x0f,0x1e,0xfa
#endif
