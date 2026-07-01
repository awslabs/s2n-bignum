// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
//
// Emitted by Ragamuffin transpiler.

// ----------------------------------------------------------------------------
// MD5 block compression
//
// extern void md5_compress(uint32_t state[static 4],
//                          const uint8_t *data,
//                          size_t num_blocks);
//
// SysV: RDI = state, RSI = data, RDX = num_blocks. Win64 shim copies RCX,RDX,R8.
// ----------------------------------------------------------------------------


#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(md5_compress)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(md5_compress)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(md5_compress)
        .text

S2N_BN_SYMBOL(md5_compress):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        CFI_PUSH(rbp)
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

Lmd5_compress_prologue:
        mov     rbp, rdi
        shl     rdx, 6
        lea     rdi, [rsi+rdx*1]
        mov     eax, [rbp]
        mov     ebx, [rbp+4]
        mov     ecx, [rbp+8]
        mov     edx, [rbp+12]
        cmp     rsi, rdi
        je      Lmd5_compress_end

Lmd5_compress_loop:
        mov     r8d, eax
        mov     r9d, ebx
        mov     r14d, ecx
        mov     r15d, edx
        mov     r10d, [rsi]
        mov     r11d, edx
        xor     r11d, ecx
        lea     eax, [rax+r10*1-680876936]
        and     r11d, ebx
        xor     r11d, edx
        mov     r10d, [rsi+4]
        add     eax, r11d
        rol     eax, 7
        mov     r11d, ecx
        add     eax, ebx
        xor     r11d, ebx
        lea     edx, [rdx+r10*1-389564586]
        and     r11d, eax
        xor     r11d, ecx
        mov     r10d, [rsi+8]
        add     edx, r11d
        rol     edx, 12
        mov     r11d, ebx
        add     edx, eax
        xor     r11d, eax
        lea     ecx, [rcx+r10*1+606105819]
        and     r11d, edx
        xor     r11d, ebx
        mov     r10d, [rsi+12]
        add     ecx, r11d
        rol     ecx, 17
        mov     r11d, eax
        add     ecx, edx
        xor     r11d, edx
        lea     ebx, [rbx+r10*1-1044525330]
        and     r11d, ecx
        xor     r11d, eax
        mov     r10d, [rsi+16]
        add     ebx, r11d
        rol     ebx, 22
        mov     r11d, edx
        add     ebx, ecx
        xor     r11d, ecx
        lea     eax, [rax+r10*1-176418897]
        and     r11d, ebx
        xor     r11d, edx
        mov     r10d, [rsi+20]
        add     eax, r11d
        rol     eax, 7
        mov     r11d, ecx
        add     eax, ebx
        xor     r11d, ebx
        lea     edx, [rdx+r10*1+1200080426]
        and     r11d, eax
        xor     r11d, ecx
        mov     r10d, [rsi+24]
        add     edx, r11d
        rol     edx, 12
        mov     r11d, ebx
        add     edx, eax
        xor     r11d, eax
        lea     ecx, [rcx+r10*1-1473231341]
        and     r11d, edx
        xor     r11d, ebx
        mov     r10d, [rsi+28]
        add     ecx, r11d
        rol     ecx, 17
        mov     r11d, eax
        add     ecx, edx
        xor     r11d, edx
        lea     ebx, [rbx+r10*1-45705983]
        and     r11d, ecx
        xor     r11d, eax
        mov     r10d, [rsi+32]
        add     ebx, r11d
        rol     ebx, 22
        mov     r11d, edx
        add     ebx, ecx
        xor     r11d, ecx
        lea     eax, [rax+r10*1+1770035416]
        and     r11d, ebx
        xor     r11d, edx
        mov     r10d, [rsi+36]
        add     eax, r11d
        rol     eax, 7
        mov     r11d, ecx
        add     eax, ebx
        xor     r11d, ebx
        lea     edx, [rdx+r10*1-1958414417]
        and     r11d, eax
        xor     r11d, ecx
        mov     r10d, [rsi+40]
        add     edx, r11d
        rol     edx, 12
        mov     r11d, ebx
        add     edx, eax
        xor     r11d, eax
        lea     ecx, [rcx+r10*1-42063]
        and     r11d, edx
        xor     r11d, ebx
        mov     r10d, [rsi+44]
        add     ecx, r11d
        rol     ecx, 17
        mov     r11d, eax
        add     ecx, edx
        xor     r11d, edx
        lea     ebx, [rbx+r10*1-1990404162]
        and     r11d, ecx
        xor     r11d, eax
        mov     r10d, [rsi+48]
        add     ebx, r11d
        rol     ebx, 22
        mov     r11d, edx
        add     ebx, ecx
        xor     r11d, ecx
        lea     eax, [rax+r10*1+1804603682]
        and     r11d, ebx
        xor     r11d, edx
        mov     r10d, [rsi+52]
        add     eax, r11d
        rol     eax, 7
        mov     r11d, ecx
        add     eax, ebx
        xor     r11d, ebx
        lea     edx, [rdx+r10*1-40341101]
        and     r11d, eax
        xor     r11d, ecx
        mov     r10d, [rsi+56]
        add     edx, r11d
        rol     edx, 12
        mov     r11d, ebx
        add     edx, eax
        xor     r11d, eax
        lea     ecx, [rcx+r10*1-1502002290]
        and     r11d, edx
        xor     r11d, ebx
        mov     r10d, [rsi+60]
        add     ecx, r11d
        rol     ecx, 17
        mov     r11d, eax
        add     ecx, edx
        xor     r11d, edx
        lea     ebx, [rbx+r10*1+1236535329]
        and     r11d, ecx
        xor     r11d, eax
        mov     r10d, [rsi]
        add     ebx, r11d
        rol     ebx, 22
        mov     r11d, edx
        add     ebx, ecx
        mov     r10d, [rsi+4]
        mov     r11d, edx
        mov     r12d, edx
        not     r11d
        lea     eax, [rax+r10*1-165796510]
        and     r12d, ebx
        and     r11d, ecx
        mov     r10d, [rsi+24]
        add     eax, r11d
        mov     r11d, ecx
        add     eax, r12d
        mov     r12d, ecx
        rol     eax, 5
        add     eax, ebx
        not     r11d
        lea     edx, [rdx+r10*1-1069501632]
        and     r12d, eax
        and     r11d, ebx
        mov     r10d, [rsi+44]
        add     edx, r11d
        mov     r11d, ebx
        add     edx, r12d
        mov     r12d, ebx
        rol     edx, 9
        add     edx, eax
        not     r11d
        lea     ecx, [rcx+r10*1+643717713]
        and     r12d, edx
        and     r11d, eax
        mov     r10d, [rsi]
        add     ecx, r11d
        mov     r11d, eax
        add     ecx, r12d
        mov     r12d, eax
        rol     ecx, 14
        add     ecx, edx
        not     r11d
        lea     ebx, [rbx+r10*1-373897302]
        and     r12d, ecx
        and     r11d, edx
        mov     r10d, [rsi+20]
        add     ebx, r11d
        mov     r11d, edx
        add     ebx, r12d
        mov     r12d, edx
        rol     ebx, 20
        add     ebx, ecx
        not     r11d
        lea     eax, [rax+r10*1-701558691]
        and     r12d, ebx
        and     r11d, ecx
        mov     r10d, [rsi+40]
        add     eax, r11d
        mov     r11d, ecx
        add     eax, r12d
        mov     r12d, ecx
        rol     eax, 5
        add     eax, ebx
        not     r11d
        lea     edx, [rdx+r10*1+38016083]
        and     r12d, eax
        and     r11d, ebx
        mov     r10d, [rsi+60]
        add     edx, r11d
        mov     r11d, ebx
        add     edx, r12d
        mov     r12d, ebx
        rol     edx, 9
        add     edx, eax
        not     r11d
        lea     ecx, [rcx+r10*1-660478335]
        and     r12d, edx
        and     r11d, eax
        mov     r10d, [rsi+16]
        add     ecx, r11d
        mov     r11d, eax
        add     ecx, r12d
        mov     r12d, eax
        rol     ecx, 14
        add     ecx, edx
        not     r11d
        lea     ebx, [rbx+r10*1-405537848]
        and     r12d, ecx
        and     r11d, edx
        mov     r10d, [rsi+36]
        add     ebx, r11d
        mov     r11d, edx
        add     ebx, r12d
        mov     r12d, edx
        rol     ebx, 20
        add     ebx, ecx
        not     r11d
        lea     eax, [rax+r10*1+568446438]
        and     r12d, ebx
        and     r11d, ecx
        mov     r10d, [rsi+56]
        add     eax, r11d
        mov     r11d, ecx
        add     eax, r12d
        mov     r12d, ecx
        rol     eax, 5
        add     eax, ebx
        not     r11d
        lea     edx, [rdx+r10*1-1019803690]
        and     r12d, eax
        and     r11d, ebx
        mov     r10d, [rsi+12]
        add     edx, r11d
        mov     r11d, ebx
        add     edx, r12d
        mov     r12d, ebx
        rol     edx, 9
        add     edx, eax
        not     r11d
        lea     ecx, [rcx+r10*1-187363961]
        and     r12d, edx
        and     r11d, eax
        mov     r10d, [rsi+32]
        add     ecx, r11d
        mov     r11d, eax
        add     ecx, r12d
        mov     r12d, eax
        rol     ecx, 14
        add     ecx, edx
        not     r11d
        lea     ebx, [rbx+r10*1+1163531501]
        and     r12d, ecx
        and     r11d, edx
        mov     r10d, [rsi+52]
        add     ebx, r11d
        mov     r11d, edx
        add     ebx, r12d
        mov     r12d, edx
        rol     ebx, 20
        add     ebx, ecx
        not     r11d
        lea     eax, [rax+r10*1-1444681467]
        and     r12d, ebx
        and     r11d, ecx
        mov     r10d, [rsi+8]
        add     eax, r11d
        mov     r11d, ecx
        add     eax, r12d
        mov     r12d, ecx
        rol     eax, 5
        add     eax, ebx
        not     r11d
        lea     edx, [rdx+r10*1-51403784]
        and     r12d, eax
        and     r11d, ebx
        mov     r10d, [rsi+28]
        add     edx, r11d
        mov     r11d, ebx
        add     edx, r12d
        mov     r12d, ebx
        rol     edx, 9
        add     edx, eax
        not     r11d
        lea     ecx, [rcx+r10*1+1735328473]
        and     r12d, edx
        and     r11d, eax
        mov     r10d, [rsi+48]
        add     ecx, r11d
        mov     r11d, eax
        add     ecx, r12d
        mov     r12d, eax
        rol     ecx, 14
        add     ecx, edx
        not     r11d
        lea     ebx, [rbx+r10*1-1926607734]
        and     r12d, ecx
        and     r11d, edx
        mov     r10d, [rsi]
        add     ebx, r11d
        mov     r11d, edx
        add     ebx, r12d
        mov     r12d, edx
        rol     ebx, 20
        add     ebx, ecx
        mov     r10d, [rsi+20]
        mov     r11d, ecx
        lea     eax, [rax+r10*1-378558]
        mov     r10d, [rsi+32]
        xor     r11d, edx
        xor     r11d, ebx
        add     eax, r11d
        rol     eax, 4
        mov     r11d, ebx
        add     eax, ebx
        lea     edx, [rdx+r10*1-2022574463]
        mov     r10d, [rsi+44]
        xor     r11d, ecx
        xor     r11d, eax
        add     edx, r11d
        rol     edx, 11
        mov     r11d, eax
        add     edx, eax
        lea     ecx, [rcx+r10*1+1839030562]
        mov     r10d, [rsi+56]
        xor     r11d, ebx
        xor     r11d, edx
        add     ecx, r11d
        rol     ecx, 16
        mov     r11d, edx
        add     ecx, edx
        lea     ebx, [rbx+r10*1-35309556]
        mov     r10d, [rsi+4]
        xor     r11d, eax
        xor     r11d, ecx
        add     ebx, r11d
        rol     ebx, 23
        mov     r11d, ecx
        add     ebx, ecx
        lea     eax, [rax+r10*1-1530992060]
        mov     r10d, [rsi+16]
        xor     r11d, edx
        xor     r11d, ebx
        add     eax, r11d
        rol     eax, 4
        mov     r11d, ebx
        add     eax, ebx
        lea     edx, [rdx+r10*1+1272893353]
        mov     r10d, [rsi+28]
        xor     r11d, ecx
        xor     r11d, eax
        add     edx, r11d
        rol     edx, 11
        mov     r11d, eax
        add     edx, eax
        lea     ecx, [rcx+r10*1-155497632]
        mov     r10d, [rsi+40]
        xor     r11d, ebx
        xor     r11d, edx
        add     ecx, r11d
        rol     ecx, 16
        mov     r11d, edx
        add     ecx, edx
        lea     ebx, [rbx+r10*1-1094730640]
        mov     r10d, [rsi+52]
        xor     r11d, eax
        xor     r11d, ecx
        add     ebx, r11d
        rol     ebx, 23
        mov     r11d, ecx
        add     ebx, ecx
        lea     eax, [rax+r10*1+681279174]
        mov     r10d, [rsi]
        xor     r11d, edx
        xor     r11d, ebx
        add     eax, r11d
        rol     eax, 4
        mov     r11d, ebx
        add     eax, ebx
        lea     edx, [rdx+r10*1-358537222]
        mov     r10d, [rsi+12]
        xor     r11d, ecx
        xor     r11d, eax
        add     edx, r11d
        rol     edx, 11
        mov     r11d, eax
        add     edx, eax
        lea     ecx, [rcx+r10*1-722521979]
        mov     r10d, [rsi+24]
        xor     r11d, ebx
        xor     r11d, edx
        add     ecx, r11d
        rol     ecx, 16
        mov     r11d, edx
        add     ecx, edx
        lea     ebx, [rbx+r10*1+76029189]
        mov     r10d, [rsi+36]
        xor     r11d, eax
        xor     r11d, ecx
        add     ebx, r11d
        rol     ebx, 23
        mov     r11d, ecx
        add     ebx, ecx
        lea     eax, [rax+r10*1-640364487]
        mov     r10d, [rsi+48]
        xor     r11d, edx
        xor     r11d, ebx
        add     eax, r11d
        rol     eax, 4
        mov     r11d, ebx
        add     eax, ebx
        lea     edx, [rdx+r10*1-421815835]
        mov     r10d, [rsi+60]
        xor     r11d, ecx
        xor     r11d, eax
        add     edx, r11d
        rol     edx, 11
        mov     r11d, eax
        add     edx, eax
        lea     ecx, [rcx+r10*1+530742520]
        mov     r10d, [rsi+8]
        xor     r11d, ebx
        xor     r11d, edx
        add     ecx, r11d
        rol     ecx, 16
        mov     r11d, edx
        add     ecx, edx
        lea     ebx, [rbx+r10*1-995338651]
        mov     r10d, [rsi]
        xor     r11d, eax
        xor     r11d, ecx
        add     ebx, r11d
        rol     ebx, 23
        mov     r11d, ecx
        add     ebx, ecx
        mov     r10d, [rsi]
        mov     r11d, 4294967295
        xor     r11d, edx
        lea     eax, [rax+r10*1-198630844]
        or      r11d, ebx
        xor     r11d, ecx
        add     eax, r11d
        mov     r10d, [rsi+28]
        mov     r11d, 4294967295
        rol     eax, 6
        xor     r11d, ecx
        add     eax, ebx
        lea     edx, [rdx+r10*1+1126891415]
        or      r11d, eax
        xor     r11d, ebx
        add     edx, r11d
        mov     r10d, [rsi+56]
        mov     r11d, 4294967295
        rol     edx, 10
        xor     r11d, ebx
        add     edx, eax
        lea     ecx, [rcx+r10*1-1416354905]
        or      r11d, edx
        xor     r11d, eax
        add     ecx, r11d
        mov     r10d, [rsi+20]
        mov     r11d, 4294967295
        rol     ecx, 15
        xor     r11d, eax
        add     ecx, edx
        lea     ebx, [rbx+r10*1-57434055]
        or      r11d, ecx
        xor     r11d, edx
        add     ebx, r11d
        mov     r10d, [rsi+48]
        mov     r11d, 4294967295
        rol     ebx, 21
        xor     r11d, edx
        add     ebx, ecx
        lea     eax, [rax+r10*1+1700485571]
        or      r11d, ebx
        xor     r11d, ecx
        add     eax, r11d
        mov     r10d, [rsi+12]
        mov     r11d, 4294967295
        rol     eax, 6
        xor     r11d, ecx
        add     eax, ebx
        lea     edx, [rdx+r10*1-1894986606]
        or      r11d, eax
        xor     r11d, ebx
        add     edx, r11d
        mov     r10d, [rsi+40]
        mov     r11d, 4294967295
        rol     edx, 10
        xor     r11d, ebx
        add     edx, eax
        lea     ecx, [rcx+r10*1-1051523]
        or      r11d, edx
        xor     r11d, eax
        add     ecx, r11d
        mov     r10d, [rsi+4]
        mov     r11d, 4294967295
        rol     ecx, 15
        xor     r11d, eax
        add     ecx, edx
        lea     ebx, [rbx+r10*1-2054922799]
        or      r11d, ecx
        xor     r11d, edx
        add     ebx, r11d
        mov     r10d, [rsi+32]
        mov     r11d, 4294967295
        rol     ebx, 21
        xor     r11d, edx
        add     ebx, ecx
        lea     eax, [rax+r10*1+1873313359]
        or      r11d, ebx
        xor     r11d, ecx
        add     eax, r11d
        mov     r10d, [rsi+60]
        mov     r11d, 4294967295
        rol     eax, 6
        xor     r11d, ecx
        add     eax, ebx
        lea     edx, [rdx+r10*1-30611744]
        or      r11d, eax
        xor     r11d, ebx
        add     edx, r11d
        mov     r10d, [rsi+24]
        mov     r11d, 4294967295
        rol     edx, 10
        xor     r11d, ebx
        add     edx, eax
        lea     ecx, [rcx+r10*1-1560198380]
        or      r11d, edx
        xor     r11d, eax
        add     ecx, r11d
        mov     r10d, [rsi+52]
        mov     r11d, 4294967295
        rol     ecx, 15
        xor     r11d, eax
        add     ecx, edx
        lea     ebx, [rbx+r10*1+1309151649]
        or      r11d, ecx
        xor     r11d, edx
        add     ebx, r11d
        mov     r10d, [rsi+16]
        mov     r11d, 4294967295
        rol     ebx, 21
        xor     r11d, edx
        add     ebx, ecx
        lea     eax, [rax+r10*1-145523070]
        or      r11d, ebx
        xor     r11d, ecx
        add     eax, r11d
        mov     r10d, [rsi+44]
        mov     r11d, 4294967295
        rol     eax, 6
        xor     r11d, ecx
        add     eax, ebx
        lea     edx, [rdx+r10*1-1120210379]
        or      r11d, eax
        xor     r11d, ebx
        add     edx, r11d
        mov     r10d, [rsi+8]
        mov     r11d, 4294967295
        rol     edx, 10
        xor     r11d, ebx
        add     edx, eax
        lea     ecx, [rcx+r10*1+718787259]
        or      r11d, edx
        xor     r11d, eax
        add     ecx, r11d
        mov     r10d, [rsi+36]
        mov     r11d, 4294967295
        rol     ecx, 15
        xor     r11d, eax
        add     ecx, edx
        lea     ebx, [rbx+r10*1-343485551]
        or      r11d, ecx
        xor     r11d, edx
        add     ebx, r11d
        mov     r10d, [rsi]
        mov     r11d, 4294967295
        rol     ebx, 21
        xor     r11d, edx
        add     ebx, ecx
        add     eax, r8d
        add     ebx, r9d
        add     ecx, r14d
        add     edx, r15d
        add     rsi, 64
        cmp     rsi, rdi
        jb      Lmd5_compress_loop

Lmd5_compress_end:
        mov     [rbp], eax
        mov     [rbp+4], ebx
        mov     [rbp+8], ecx
        mov     [rbp+12], edx
        CFI_STACKLOAD(r15, 0)
        CFI_STACKLOAD(r14, 8)
        CFI_STACKLOAD(r12, 16)
        CFI_STACKLOAD(rbx, 24)
        CFI_STACKLOAD(rbp, 32)
        CFI_INC_RSP(40)

Lmd5_compress_epilogue:

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET


S2N_BN_SIZE_DIRECTIVE(md5_compress)


#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
