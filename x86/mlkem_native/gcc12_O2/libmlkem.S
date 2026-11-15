// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (gcc 12, -O2)
//
// This is a transcription of the binary multilevel/gcc12/O2/libmlkem.so for
// x86-64 (see README.md): its bytes from address 0 up to the end of the
// read-only data, as they are when it is loaded, which are its first two
// loadable segments and the start of the third, with the padding between them.
// The ELF header and dynamic linking information at the start, the padding and
// the read-only data are given as data, while the procedure linkage table and
// the code are given as instructions. The instructions that refer to the
// global offset table, which is outside the image, are given as bytes, as are
// the NOPs and an instruction that the assembler would encode differently. The
// labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

.intel_syntax noprefix
        .text

// ELF header and dynamic linking information, and padding
// (0x0 to 0x1000)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x00000001003e0003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000020830
        .quad   0x0038004000000000
        .quad   0x0019001a00400009
        .quad   0x0000000400000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000798
        .quad   0x0000000000000798
        .quad   0x0000000000001000
        .quad   0x0000000500000001
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x0000000000006904
        .quad   0x0000000000006904
        .quad   0x0000000000001000
        .quad   0x0000000400000001
        .quad   0x0000000000008000
        .quad   0x0000000000008000
        .quad   0x0000000000008000
        .quad   0x0000000000001700
        .quad   0x0000000000001700
        .quad   0x0000000000001000
        .quad   0x0000000600000001
        .quad   0x0000000000009e90
        .quad   0x000000000000ae90
        .quad   0x000000000000ae90
        .quad   0x0000000000000170
        .quad   0x0000000000000170
        .quad   0x0000000000001000
        .quad   0x0000000600000002
        .quad   0x0000000000009e90
        .quad   0x000000000000ae90
        .quad   0x000000000000ae90
        .quad   0x0000000000000150
        .quad   0x0000000000000150
        .quad   0x0000000000000008
        .quad   0x0000000400000004
        .quad   0x00000000000096d0
        .quad   0x00000000000096d0
        .quad   0x00000000000096d0
        .quad   0x0000000000000030
        .quad   0x0000000000000030
        .quad   0x0000000000000008
        .quad   0x000000046474e553
        .quad   0x00000000000096d0
        .quad   0x00000000000096d0
        .quad   0x00000000000096d0
        .quad   0x0000000000000030
        .quad   0x0000000000000030
        .quad   0x0000000000000008
        .quad   0x000000066474e551
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000010
        .quad   0x000000046474e552
        .quad   0x0000000000009e90
        .quad   0x000000000000ae90
        .quad   0x000000000000ae90
        .quad   0x0000000000000170
        .quad   0x0000000000000170
        .quad   0x0000000000000001
        .quad   0x0000001700000011
        .quad   0x0000000800000011
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000130000000f
        .quad   0x000000050000000c
        .quad   0x0000000a00000000
        .quad   0x0000001600000000
        .quad   0x0000001000000002
        .quad   0x0000000000000003
        .quad   0x0000000000000014
        .quad   0x000000000000000e
        .quad   0x0000000000000009
        .quad   0x0000001200000000
        .quad   0x0000000400000015
        .quad   0x0000000000000000
        .quad   0x0000000700000000
        .quad   0x0000000600000001
        .quad   0x000000000000000d
        .quad   0x000000000000000b
        .quad   0x0000000000000000
        .quad   0x0000000200000011
        .quad   0x0000000700000002
        .quad   0x10e2681100ba0008
        .quad   0x4e41e1a21018344c
        .quad   0x0000000000000002
        .quad   0x0000000500000003
        .quad   0x0000000600000000
        .quad   0x0000000a00000009
        .quad   0x0000000d0000000b
        .quad   0x0000000000000010
        .quad   0x0000001300000012
        .quad   0x0000001500000014
        .quad   0x16c2d2ff00000000
        .quad   0xb06297357ef0d7dc
        .quad   0xe75d09fabccdaaab
        .quad   0x7ef0d7792fce7b36
        .quad   0x7fad8555ee0ec8b7
        .quad   0x884de195e75d0996
        .quad   0x835a16e0a53138a4
        .quad   0xd2675e2c16c2d869
        .quad   0xbccdb015d9726a43
        .quad   0xee0ec34dd2675dcb
        .quad   0x94bd4643ae74fb66
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000052
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00070012000000fd
        .quad   0x00000000000052f0
        .quad   0x00000000000002a9
        .quad   0x0007001200000014
        .quad   0x00000000000018b0
        .quad   0x00000000000000ec
        .quad   0x00070012000000dc
        .quad   0x0000000000005190
        .quad   0x00000000000000e1
        .quad   0x0007001200000178
        .quad   0x00000000000071c0
        .quad   0x00000000000002a9
        .quad   0x000700120000011c
        .quad   0x0000000000006de0
        .quad   0x00000000000000ec
        .quad   0x0007001200000040
        .quad   0x0000000000001ac0
        .quad   0x0000000000000067
        .quad   0x0007001200000001
        .quad   0x0000000000001790
        .quad   0x000000000000011f
        .quad   0x0007001200000073
        .quad   0x0000000000001c20
        .quad   0x0000000000000067
        .quad   0x00070012000000b3
        .quad   0x0000000000005000
        .quad   0x0000000000000111
        .quad   0x000700120000010a
        .quad   0x0000000000006cc0
        .quad   0x000000000000011f
        .quad   0x0007001200000146
        .quad   0x0000000000006ff0
        .quad   0x0000000000000067
        .quad   0x000700120000005e
        .quad   0x0000000000001b30
        .quad   0x00000000000000e1
        .quad   0x000700120000012e
        .quad   0x0000000000006ed0
        .quad   0x0000000000000111
        .quad   0x00070012000000f0
        .quad   0x0000000000005280
        .quad   0x0000000000000067
        .quad   0x00070012000000a1
        .quad   0x0000000000004f10
        .quad   0x00000000000000ec
        .quad   0x0007001200000157
        .quad   0x0000000000007060
        .quad   0x00000000000000e1
        .quad   0x000700120000016b
        .quad   0x0000000000007150
        .quad   0x0000000000000067
        .quad   0x000700120000008f
        .quad   0x0000000000004df0
        .quad   0x000000000000011f
        .quad   0x0007001200000081
        .quad   0x0000000000001c90
        .quad   0x00000000000002a9
        .quad   0x00070012000000cb
        .quad   0x0000000000005120
        .quad   0x0000000000000067
        .quad   0x0007001200000027
        .quad   0x00000000000019a0
        .quad   0x0000000000000111
        .quad   0x30316d656b6c6d00
        .quad   0x6b636568635f3432
        .quad   0x656b6c6d006b705f
        .quad   0x68635f343230316d
        .quad   0x6d006b735f6b6365
        .quad   0x343230316d656b6c
        .quad   0x7269617079656b5f
        .quad   0x00646e617265645f
        .quad   0x3230316d656b6c6d
        .quad   0x69617079656b5f34
        .quad   0x6d6f646e61720072
        .quad   0x6c6d007365747962
        .quad   0x5f343230316d656b
        .quad   0x617265645f636e65
        .quad   0x6d656b6c6d00646e
        .quad   0x636e655f34323031
        .quad   0x30316d656b6c6d00
        .quad   0x6d006365645f3432
        .quad   0x5f3231356d656b6c
        .quad   0x6b705f6b63656863
        .quad   0x31356d656b6c6d00
        .quad   0x5f6b636568635f32
        .quad   0x6d656b6c6d006b73
        .quad   0x7079656b5f323135
        .quad   0x617265645f726961
        .quad   0x6d656b6c6d00646e
        .quad   0x7079656b5f323135
        .quad   0x656b6c6d00726961
        .quad   0x636e655f3231356d
        .quad   0x00646e617265645f
        .quad   0x3231356d656b6c6d
        .quad   0x6b6c6d00636e655f
        .quad   0x65645f3231356d65
        .quad   0x376d656b6c6d0063
        .quad   0x6b636568635f3836
        .quad   0x656b6c6d006b705f
        .quad   0x6568635f3836376d
        .quad   0x6c6d006b735f6b63
        .quad   0x6b5f3836376d656b
        .quad   0x645f726961707965
        .quad   0x6c6d00646e617265
        .quad   0x6b5f3836376d656b
        .quad   0x6d00726961707965
        .quad   0x5f3836376d656b6c
        .quad   0x617265645f636e65
        .quad   0x6d656b6c6d00646e
        .quad   0x00636e655f383637
        .quad   0x3836376d656b6c6d
        .quad   0x62696c006365645f
        .quad   0x6f732e6d656b6c6d
        .quad   0x632f656d6f682f00
        .quad   0x6c6d2f656475616c
        .quad   0x623638782f6d656b
        .quad   0x74756f2f646c6975
        .quad   0x74756f2f73747570
        .quad   0x0000000062696c2f
        .quad   0x000000000000aff8
        .quad   0x0000000100000007
        .zero   2160

// The procedure linkage table (0x1000 to 0x1020)

L1000:
        // push    QWORD PTR [rip+0x9fe2]
        .byte   0xff,0x35,0xe2,0x9f,0x00,0x00
        // jmp     QWORD PTR [rip+0x9fe4]
        .byte   0xff,0x25,0xe4,0x9f,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L1010:
        // jmp     QWORD PTR [rip+0x9fe2]
        .byte   0xff,0x25,0xe2,0x9f,0x00,0x00
        // push    0x0
        .byte   0x68,0x00,0x00,0x00,0x00
        {disp32} jmp     L1000

// The code (0x1020 to 0x7904)

// mlkem1024_gen_matrix (0x1020)

L1020:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14d, edx
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     r15, rsp
        lea     r12, [rsp+0x100]
        mov     rax, r15
L1055:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     rax, r12
        jne     L1055
        xor     ebx, ebx
L1067:
        mov     rax, r15
        mov     esi, ebx
L106c:
        mov     edx, esi
        mov     ecx, esi
        and     edx, 0x3
        shr     ecx, 0x2
        test    r14d, r14d
        mov     edi, edx
        cmovne  edx, ecx
        cmovne  ecx, edi
        add     rax, 0x40
        add     esi, 0x1
        mov     BYTE PTR [rax-0x20], dl
        mov     BYTE PTR [rax-0x1f], cl
        cmp     rax, r12
        jne     L106c
        lea     eax, [rbx+0x3]
        mov     edi, ebx
        mov     r8, r15
        shr     eax, 0x2
        shr     edi, 0x2
        shl     rax, 0xb
        shl     rdi, 0xb
        lea     rcx, [r13+rax*1+0x600]
        lea     eax, [rbx+0x2]
        add     rdi, r13
        shr     eax, 0x2
        shl     rax, 0xb
        lea     rdx, [r13+rax*1+0x400]
        lea     eax, [rbx+0x1]
        add     ebx, 0x4
        shr     eax, 0x2
        shl     rax, 0xb
        lea     rsi, [r13+rax*1+0x200]
        call    L60e0
        cmp     ebx, 0x10
        jne     L1067
        xor     eax, eax
        mov     rdi, r15
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_indcpa_keypair_derand (0x1110)

L1110:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r14, [rbp-0x2030]
        push    r13
        lea     r13, [rbp-0x3c30]
        push    r12
        lea     r12, [rbp-0x3c50]
        push    r10
        push    rbx
        lea     rbx, [rbp-0x3c70]
        sub     rsp, 0x3cc0
        movdqu  xmm1, XMMWORD PTR [rdx]
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     QWORD PTR [rbp-0x3cc8], rdi
        mov     QWORD PTR [rbp-0x3cd0], rsi
        mov     rdi, rbx
        lea     rsi, [rbp-0x3cb0]
        mov     edx, 0x21
        movaps  XMMWORD PTR [rbp-0x3cb0], xmm1
        movaps  XMMWORD PTR [rbp-0x3ca0], xmm2
        mov     QWORD PTR [rbp-0x3ce0], rsi
        mov     QWORD PTR [rbp-0x3cd8], rbx
        mov     BYTE PTR [rbp-0x3c90], 0x4
        call    L3570
        mov     rsi, rbx
        xor     edx, edx
        mov     rdi, r14
        mov     QWORD PTR [rbp-0x3cc0], r14
        lea     rbx, [rbp-0x2830]
        call    L1020
        sub     rsp, 0x8
        mov     r8, r12
        xor     r9d, r9d
        push    0x3
        lea     rcx, [rbp-0x2230]
        mov     rdi, rbx
        lea     rdx, [rbp-0x2430]
        push    0x2
        lea     rsi, [rbp-0x2630]
        push    0x1
        call    L2260
        lea     rax, [rbp-0x3830]
        add     rsp, 0x18
        mov     r8, r12
        mov     QWORD PTR [rbp-0x3cb8], rax
        mov     rdi, rax
        lea     rcx, [rbp-0x3230]
        lea     rdx, [rbp-0x3430]
        push    0x7
        lea     rsi, [rbp-0x3630]
        mov     r9d, 0x4
        mov     r15, rax
        push    0x6
        lea     r12, [rbp-0x3030]
        push    0x5
        call    L2260
        add     rsp, 0x20
        mov     rdi, rbx
        call    L2040
        mov     rdi, r15
        mov     r15, r12
        call    L2040
        mov     rsi, rbx
        mov     rdi, r13
        call    L2190
L124f:
        mov     rsi, r14
        mov     rdi, r15
        mov     rcx, r13
        mov     rdx, rbx
        add     r15, 0x200
        add     r14, 0x800
        call    L20a0
        cmp     r15, rbx
        jne     L124f
        mov     rdi, r12
        call    L2230
        mov     r14, QWORD PTR [rbp-0x3cb8]
        mov     rdi, r12
        mov     rsi, r14
        call    L2200
        mov     rdi, r12
        call    L21d0
        mov     rdi, r15
        call    L21d0
        mov     rdi, QWORD PTR [rbp-0x3cd0]
        mov     rsi, r15
        call    L1fc0
        mov     rbx, QWORD PTR [rbp-0x3cc8]
        mov     rsi, r12
        mov     rdi, rbx
        call    L1fc0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x80
        movdqa  xmm3, XMMWORD PTR [rbp-0x3c70]
        movdqa  xmm4, XMMWORD PTR [rbp-0x3c60]
        rep stos QWORD PTR es:[rdi], rax
        movups  XMMWORD PTR [rbx+0x600], xmm3
        movups  XMMWORD PTR [rbx+0x610], xmm4
        mov     ecx, 0x100
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, r14
        mov     QWORD PTR [rbp-0x3cb8], r14
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3cc0]
        mov     ecx, 0x400
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3cc0]
        pxor    xmm0, xmm0
        mov     BYTE PTR [rbp-0x3c90], 0x0
        mov     rax, QWORD PTR [rbp-0x3ce0]
        movaps  XMMWORD PTR [rbp-0x3cb0], xmm0
        movaps  XMMWORD PTR [rbp-0x3ca0], xmm0
        mov     rax, QWORD PTR [rbp-0x3cd8]
        movaps  XMMWORD PTR [rbp-0x3c70], xmm0
        movaps  XMMWORD PTR [rbp-0x3c60], xmm0
        movaps  XMMWORD PTR [rbp-0x3c50], xmm0
        movaps  XMMWORD PTR [rbp-0x3c40], xmm0
        lea     rsp, [rbp-0x30]
        xor     eax, eax
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_indcpa_enc (0x1390)

L1390:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0x3830]
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, rdx
        push    r10
        push    rbx
        mov     rbx, rsi
        mov     rsi, rdx
        sub     rsp, 0x4a60
        mov     QWORD PTR [rbp-0x4a80], rdi
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x4a58], rax
        call    L2000
        lea     rax, [rbp-0x4830]
        mov     rsi, rbx
        movdqu  xmm1, XMMWORD PTR [r12+0x600]
        movdqu  xmm2, XMMWORD PTR [r12+0x610]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x4a70], rax
        lea     r12, [rbp-0x2030]
        movaps  XMMWORD PTR [rbp-0x4a50], xmm1
        lea     rbx, [rbp-0x4030]
        mov     r14, r12
        movaps  XMMWORD PTR [rbp-0x4a40], xmm2
        call    L3210
        lea     rax, [rbp-0x4a50]
        mov     edx, 0x1
        mov     rdi, r12
        mov     rsi, rax
        mov     QWORD PTR [rbp-0x4a88], rax
        call    L1020
        sub     rsp, 0x8
        mov     r8, r13
        xor     r9d, r9d
        push    0x3
        lea     rcx, [rbp-0x3a30]
        mov     rdi, rbx
        lea     rdx, [rbp-0x3c30]
        push    0x2
        lea     rsi, [rbp-0x3e30]
        push    0x1
        call    L2260
        add     rsp, 0x18
        mov     r8, r13
        lea     rax, [rbp-0x3030]
        mov     QWORD PTR [rbp-0x4a60], rax
        lea     rcx, [rbp-0x2a30]
        mov     r9d, 0x4
        mov     rdi, rax
        push    0x7
        lea     rdx, [rbp-0x2c30]
        lea     rsi, [rbp-0x2e30]
        push    0x6
        push    0x5
        call    L2260
        lea     rax, [rbp-0x4630]
        mov     rsi, r13
        add     rsp, 0x20
        mov     rdi, rax
        mov     edx, 0x8
        mov     QWORD PTR [rbp-0x4a78], rax
        lea     r13, [rbp-0x4430]
        call    L23e0
        mov     rdi, rbx
        call    L2040
        mov     rsi, rbx
        mov     rdi, r13
        call    L2190
        lea     rax, [rbp-0x2830]
        mov     QWORD PTR [rbp-0x4a68], rax
        mov     r15, rax
L14fe:
        mov     rsi, r14
        mov     rdi, r15
        mov     rcx, r13
        mov     rdx, rbx
        add     r15, 0x200
        add     r14, 0x800
        call    L20a0
        cmp     r15, r12
        jne     L14fe
        lea     r12, [rbp-0x4a30]
        mov     rsi, QWORD PTR [rbp-0x4a58]
        mov     rcx, r13
        mov     rdx, rbx
        mov     rdi, r12
        call    L20a0
        mov     r14, QWORD PTR [rbp-0x4a68]
        mov     rdi, r14
        call    L2070
        mov     rdi, r12
        call    L5860
        mov     rsi, QWORD PTR [rbp-0x4a60]
        mov     rdi, r14
        call    L2200
        mov     rsi, QWORD PTR [rbp-0x4a78]
        mov     rdi, r12
        call    L56b0
        mov     rsi, QWORD PTR [rbp-0x4a70]
        mov     rdi, r12
        call    L56b0
        mov     rdi, r14
        call    L21d0
        mov     rdi, r12
        call    L5660
        mov     rdi, QWORD PTR [rbp-0x4a80]
        mov     rsi, r14
        call    L1f40
        mov     rax, QWORD PTR [rbp-0x4a80]
        mov     rsi, r12
        add     rax, 0x580
        mov     rdi, rax
        call    L28c0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x4a78]
        mov     ecx, 0x40
        mov     rdx, QWORD PTR [rbp-0x4a78]
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x4a70]
        mov     ecx, 0x40
        mov     rdx, QWORD PTR [rbp-0x4a70]
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, r14
        mov     QWORD PTR [rbp-0x4a68], r14
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x4a60]
        mov     ecx, 0x100
        mov     rdx, QWORD PTR [rbp-0x4a60]
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x4a58]
        mov     ecx, 0x100
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x4a58]
        mov     ecx, 0x100
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x400
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rbp-0x4a88]
        movaps  XMMWORD PTR [rbp-0x4a50], xmm0
        movaps  XMMWORD PTR [rbp-0x4a40], xmm0
        lea     rsp, [rbp-0x30]
        xor     eax, eax
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_indcpa_dec (0x1690)

L1690:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x1820
        lea     rbx, [rsp+0x820]
        mov     QWORD PTR [rsp+0x18], rdi
        lea     r15, [rsp+0x1020]
        mov     rdi, rbx
        lea     r14, [rsp+0x420]
        call    L1f80
        lea     rsi, [r12+0x580]
        lea     r12, [rsp+0x20]
        mov     rdi, r12
        call    L2de0
        mov     rsi, r13
        mov     rdi, r15
        lea     r13, [rsp+0x220]
        call    L2000
        mov     rdi, rbx
        call    L2040
        mov     rsi, rbx
        mov     rdi, r14
        call    L2190
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, r15
        mov     rdi, r13
        call    L20a0
        mov     rdi, r13
        call    L5860
        mov     rsi, r13
        mov     rdi, r12
        call    L56e0
        mov     rdi, r12
        call    L5660
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     rsi, r12
        call    L3260
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem1024_check_pk (0x1790)

L1790:
        push    rbp
        mov     rsi, rdi
        mov     rbp, rsp
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xe00
        lea     rbx, [rsp+0x600]
        mov     r12, rsp
        mov     rdi, rbx
        call    L2000
        mov     rdi, rbx
        call    L21d0
        mov     rsi, rbx
        mov     rdi, r12
        call    L1fc0
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L17e0:
        movdqu  xmm1, XMMWORD PTR [r13+rax*1+0x0]
        pxor    xmm1, XMMWORD PTR [r12+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x600
        jne     L17e0
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x8
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        mov     rdi, r12
        mov     ecx, 0xc0
        sete    dl
        xor     eax, eax
        rep stos QWORD PTR es:[rdi], rax
        movzx   edx, dl
        lea     edx, [rdx*4-0x4]
        mov     ecx, 0x100
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x18]
        mov     eax, edx
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem1024_check_sk (0x18b0)

L18b0:
        push    rbp
        lea     rsi, [rdi+0x600]
        mov     edx, 0x620
        mov     rbp, rsp
        push    r12
        push    rbx
        mov     rbx, rdi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     r12, rsp
        mov     rdi, r12
        call    L3510
        movdqu  xmm1, XMMWORD PTR [rbx+0xc20]
        movdqu  xmm2, XMMWORD PTR [rbx+0xc30]
        pxor    xmm1, XMMWORD PTR [rsp]
        pxor    xmm2, XMMWORD PTR [rsp+0x10]
        movdqa  xmm0, xmm1
        pxor    xmm1, xmm2
        por     xmm0, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        pxor    xmm0, xmm0
        sete    al
        movaps  XMMWORD PTR [rsp], xmm0
        movzx   eax, al
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     eax, [rax+rax*4-0x5]
        lea     rsp, [rbp-0x10]
        pop     rbx
        pop     r12
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_keypair_derand (0x19a0)

L19a0:
        push    r13
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsp, 0x8
        call    L1110
        mov     r13d, eax
        test    eax, eax
        jne     L1a48
        mov     rax, QWORD PTR [rbp+0x0]
        lea     rdi, [rbx+0x608]
        lea     rcx, [rbx+0x600]
        mov     rsi, rbp
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rbx+0x600], rax
        sub     rcx, rdi
        mov     rdx, QWORD PTR [rbp+0x618]
        lea     rax, [rbx+0xc20]
        sub     rsi, rcx
        add     ecx, 0x620
        mov     QWORD PTR [rbx+0xc18], rdx
        shr     ecx, 0x3
        mov     edx, 0x620
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbp
        mov     rdi, rax
        call    L3510
        movdqu  xmm0, XMMWORD PTR [r12+0x20]
        mov     eax, r13d
        movups  XMMWORD PTR [rbx+0xc40], xmm0
        movdqu  xmm1, XMMWORD PTR [r12+0x30]
        movups  XMMWORD PTR [rbx+0xc50], xmm1
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L1a48:
        lea     rdi, [rbp+0x8]
        mov     rcx, rbp
        xor     eax, eax
        mov     QWORD PTR [rbp+0x0], 0x0
        mov     QWORD PTR [rbp+0x618], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x620
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0xc58], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xc60
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0x8
        mov     eax, r13d
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_keypair (0x1ac0)

L1ac0:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x40
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x40
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L1b20
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L19a0
L1af9:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L1b20:
        mov     eax, 0xfffffffd
        jmp     L1af9
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem1024_enc_derand (0x1b30)

L1b30:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        push    r13
        mov     r13, rsi
        push    r12
        mov     r12, rdi
        mov     rdi, rdx
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        add     rsp, 0xffffffffffffff80
        call    L1790
        mov     r14, rsp
        test    eax, eax
        je      L1ba0
        lea     r15, [rsp+0x40]
L1b65:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90
L1ba0:
        movdqu  xmm1, XMMWORD PTR [r15]
        movdqu  xmm2, XMMWORD PTR [r15+0x10]
        lea     rdi, [rsp+0x20]
        mov     rsi, rbx
        mov     edx, 0x620
        lea     r15, [rsp+0x40]
        movaps  XMMWORD PTR [rsp], xmm1
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        call    L3510
        mov     edx, 0x40
        mov     rsi, r14
        mov     rdi, r15
        call    L3570
        lea     rcx, [rsp+0x60]
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r12
        call    L1390
        test    eax, eax
        jne     L1b65
        movdqa  xmm3, XMMWORD PTR [rsp+0x40]
        movdqa  xmm4, XMMWORD PTR [rsp+0x50]
        movups  XMMWORD PTR [r13+0x0], xmm3
        movups  XMMWORD PTR [r13+0x10], xmm4
        jmp     L1b65
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem1024_enc (0x1c20)

L1c20:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L1c80
        mov     rcx, rbx
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, r12
        call    L1b30
L1c61:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L1c80:
        mov     eax, 0xfffffffd
        jmp     L1c61
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem1024_dec (0x1c90)

L1c90:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        push    r14
        mov     r14, rdi
        mov     rdi, rdx
        push    r13
        mov     r13, rdx
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x6e0
        call    L18b0
        test    eax, eax
        je      L1d28
        mov     ebx, eax
        lea     r10, [rsp+0x20]
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
L1cd1:
        xor     eax, eax
        mov     rdi, r8
        mov     ecx, 0xc8
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, ebx
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L1d28:
        lea     r10, [rsp+0x20]
        mov     rdx, r13
        mov     rsi, r15
        mov     rdi, r10
        mov     QWORD PTR [rsp+0x18], r10
        call    L1690
        mov     r10, QWORD PTR [rsp+0x18]
        test    eax, eax
        mov     ebx, eax
        je      L1d60
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
        jmp     L1cd1
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L1d60:
        lea     r9, [rsp+0x60]
        mov     rsi, r10
        mov     edx, 0x40
        mov     QWORD PTR [rsp+0x18], r10
        movdqu  xmm3, XMMWORD PTR [r13+0xc20]
        mov     rdi, r9
        mov     QWORD PTR [rsp+0x8], r9
        movdqu  xmm4, XMMWORD PTR [r13+0xc30]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        call    L3570
        mov     r10, QWORD PTR [rsp+0x18]
        lea     r8, [rsp+0xa0]
        lea     rcx, [rsp+0x80]
        mov     rdi, r8
        lea     rdx, [r13+0x600]
        mov     QWORD PTR [rsp+0x18], r8
        mov     rsi, r10
        mov     QWORD PTR [rsp+0x10], r10
        call    L1390
        mov     r8, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp+0x10]
        test    eax, eax
        mov     r9, QWORD PTR [rsp+0x8]
        mov     ebx, eax
        jne     L1cd1
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop
        .byte   0x90
L1df0:
        movdqu  xmm1, XMMWORD PTR [r15+rax*1]
        pxor    xmm1, XMMWORD PTR [r8+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x620
        jne     L1df0
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x8], r9
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x10], r10
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    eax, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    r12d, xmm0
        movzx   r12d, r12b
        neg     r12d
        sar     r12d, 0x10
        xor     r12d, eax
        xor     r12d, eax
        mov     rdx, r8
        mov     ecx, 0xc4
        mov     rsi, r15
        movdqu  xmm6, XMMWORD PTR [r13+0xc50]
        mov     QWORD PTR [rsp+0x18], r8
        movzx   r12d, r12b
        lea     rax, [rsp+0xc0]
        movdqu  xmm5, XMMWORD PTR [r13+0xc40]
        mov     rdi, rax
        neg     r12d
        movaps  XMMWORD PTR [rsp+0xb0], xmm6
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     ecx, 0x640
        mov     esi, 0x20
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0xa0], xmm5
        call    L3480
        mov     r9, QWORD PTR [rsp+0x8]
        mov     r10, QWORD PTR [rsp+0x10]
        xor     eax, eax
        mov     r8, QWORD PTR [rsp+0x18]
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L1f10:
        movzx   esi, BYTE PTR [r9+rax*1]
        mov     ecx, r12d
        movzx   edx, BYTE PTR [r14+rax*1]
        sar     ecx, 0x10
        xor     edx, esi
        and     edx, ecx
        xor     edx, esi
        mov     BYTE PTR [r14+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x20
        jne     L1f10
        jmp     L1cd1
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem1024_polyvec_compress_du (0x1f40)

L1f40:
        push    r12
        lea     r12, [rdi+0x580]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
L1f51:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x160
        add     rbp, 0x200
        call    L2af0
        cmp     rbx, r12
        jne     L1f51
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_polyvec_decompress_du (0x1f80)

L1f80:
        push    r12
        lea     r12, [rsi+0x580]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L1f91:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x160
        add     rbp, 0x200
        call    L2fe0
        cmp     rbx, r12
        jne     L1f91
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_polyvec_tobytes (0x1fc0)

L1fc0:
        push    r12
        lea     r12, [rdi+0x600]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
L1fd1:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x180
        add     rbp, 0x200
        call    L3180
        cmp     rbx, r12
        jne     L1fd1
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_polyvec_frombytes (0x2000)

L2000:
        push    r12
        lea     r12, [rsi+0x600]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L2011:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x180
        add     rbp, 0x200
        call    L31c0
        cmp     rbx, r12
        jne     L2011
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_polyvec_ntt (0x2040)

L2040:
        push    rbx
        mov     rbx, rdi
        call    L5780
        lea     rdi, [rbx+0x200]
        call    L5780
        lea     rdi, [rbx+0x400]
        call    L5780
        lea     rdi, [rbx+0x600]
        pop     rbx
        jmp     L5780
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem1024_polyvec_invntt_tomont (0x2070)

L2070:
        push    rbx
        mov     rbx, rdi
        call    L5860
        lea     rdi, [rbx+0x200]
        call    L5860
        lea     rdi, [rbx+0x400]
        call    L5860
        lea     rdi, [rbx+0x600]
        pop     rbx
        jmp     L5860
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0x20a0)

L20a0:
        push    r15
        mov     r9, rdi
        mov     rax, rcx
        lea     rdi, [rdx+0x2]
        push    r14
        mov     r8, rsi
        lea     rdx, [r9+0x2]
        lea     r14, [rcx+0x100]
        push    r13
        push    r12
        push    rbp
        push    rbx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L20c8:
        mov     r10, rax
        xor     r9d, r9d
        xor     esi, esi
        xor     ecx, ecx
        lea     rbx, [r8+0x2]
        lea     r11, [rdi-0x2]
L20da:
        movsx   r15d, WORD PTR [rbx+r9*1]
        movsx   ebp, WORD PTR [r10]
        add     r10, 0x100
        movsx   r13d, WORD PTR [r8+r9*1]
        mov     DWORD PTR [rsp-0x4], r15d
        mov     r12d, DWORD PTR [rsp-0x4]
        movsx   r15d, WORD PTR [r11+r9*1]
        imul    ebp, r12d
        mov     r12d, ebp
        mov     ebp, r13d
        imul    ebp, r15d
        add     r12d, ebp
        movsx   ebp, WORD PTR [rdi+r9*1]
        add     r9, 0x200
        add     ecx, r12d
        mov     r12d, DWORD PTR [rsp-0x4]
        imul    ebp, r13d
        imul    r12d, r15d
        add     ebp, r12d
        add     esi, ebp
        cmp     r9, 0x800
        jne     L20da
        add     rax, 0x2
        add     r8, 0x4
        add     rdi, 0x4
        add     rdx, 0x4
        imul    r9w, cx, 0xf301
        movsx   r9d, r9w
        imul    r9d, r9d, 0xfffff2ff
        add     ecx, r9d
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x6], cx
        imul    cx, si, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, esi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x4], cx
        cmp     r14, rax
        jne     L20c8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop
        .byte   0x90

// mlkem1024_polyvec_mulcache_compute (0x2190)

L2190:
        push    r12
        lea     r12, [rdi+0x400]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
L21a1:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x100
        add     rbp, 0x200
        call    L5710
        cmp     rbx, r12
        jne     L21a1
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_polyvec_reduce (0x21d0)

L21d0:
        push    rbx
        mov     rbx, rdi
        call    L5660
        lea     rdi, [rbx+0x200]
        call    L5660
        lea     rdi, [rbx+0x400]
        call    L5660
        lea     rdi, [rbx+0x600]
        pop     rbx
        jmp     L5660
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem1024_polyvec_add (0x2200)

L2200:
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, rsi
        push    rbx
        xor     ebx, ebx
L220c:
        lea     rsi, [rbp+rbx*1+0x0]
        lea     rdi, [r12+rbx*1]
        add     rbx, 0x200
        call    L56b0
        cmp     rbx, 0x800
        jne     L220c
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop
        .byte   0x90

// mlkem1024_polyvec_tomont (0x2230)

L2230:
        push    rbx
        mov     rbx, rdi
        call    L55a0
        lea     rdi, [rbx+0x200]
        call    L55a0
        lea     rdi, [rbx+0x400]
        call    L55a0
        lea     rdi, [rbx+0x600]
        pop     rbx
        jmp     L55a0
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem1024_poly_getnoise_eta1_4x (0x2260)

L2260:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x330]
        lea     r14, [rbp-0x130]
        push    r13
        lea     r13, [rbp-0xb0]
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        lea     rbx, [rbp-0x230]
        sub     rsp, 0x320
        mov     r11d, DWORD PTR [r10]
        mov     ecx, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x348], rdx
        movdqu  xmm1, XMMWORD PTR [r8]
        mov     edx, DWORD PTR [r10+0x10]
        mov     QWORD PTR [rbp-0x338], rdi
        lea     rdi, [rbp-0x2b0]
        movdqu  xmm0, XMMWORD PTR [r8+0x10]
        mov     QWORD PTR [rbp-0x340], rsi
        lea     r8, [rbp-0x270]
        lea     rsi, [rbp-0x2f0]
        mov     BYTE PTR [rbp-0x2d0], r11b
        lea     r10, [rbp-0x1b0]
        movaps  XMMWORD PTR [rbp-0x330], xmm1
        movaps  XMMWORD PTR [rbp-0x320], xmm0
        movaps  XMMWORD PTR [rbp-0x2f0], xmm1
        movaps  XMMWORD PTR [rbp-0x2e0], xmm0
        movaps  XMMWORD PTR [rbp-0x2b0], xmm1
        movaps  XMMWORD PTR [rbp-0x2a0], xmm0
        movaps  XMMWORD PTR [rbp-0x270], xmm1
        movaps  XMMWORD PTR [rbp-0x260], xmm0
        mov     BYTE PTR [rbp-0x310], r9b
        mov     r9, r15
        mov     BYTE PTR [rbp-0x290], cl
        mov     rcx, r13
        mov     BYTE PTR [rbp-0x250], dl
        mov     rdx, r14
        push    0x21
        push    r8
        mov     r8d, 0x80
        push    rdi
        mov     rdi, rbx
        push    rsi
        mov     rsi, r10
        mov     QWORD PTR [rbp-0x350], r10
        call    L3870
        mov     rdi, QWORD PTR [rbp-0x338]
        add     rsp, 0x20
        mov     rsi, rbx
        call    L63b0
        mov     rsi, QWORD PTR [rbp-0x350]
        mov     rdi, QWORD PTR [rbp-0x340]
        call    L63b0
        mov     rdi, QWORD PTR [rbp-0x348]
        mov     rsi, r14
        call    L63b0
        test    r12, r12
        je      L23a7
        mov     rsi, r13
        mov     rdi, r12
        call    L63b0
L23a7:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x40
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x20
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem1024_poly_getnoise_eta2 (0x23e0)

L23e0:
        push    rbp
        mov     ecx, 0x21
        mov     rbp, rsp
        push    r13
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xc0
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm2, XMMWORD PTR [rsi+0x10]
        mov     esi, 0x80
        lea     rbx, [rsp+0x40]
        mov     r13, rsp
        mov     BYTE PTR [rsp+0x20], dl
        mov     rdi, rbx
        mov     rdx, r13
        movaps  XMMWORD PTR [rsp], xmm1
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        call    L3480
        mov     rdi, r12
        mov     rsi, rbx
        call    L63b0
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x10
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        mov     BYTE PTR [rsp+0x20], 0x0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem_poly_compress_d4 (0x2460)

L2460:
        movq    xmm3, QWORD PTR [rip+L8000]
        mov     rdx, rsi
        mov     rcx, rdi
        lea     rsi, [rsi+0x200]
        movq    xmm5, QWORD PTR [rip+L8008]
        pxor    xmm4, xmm4
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2488:
        movq    xmm1, QWORD PTR [rdx]
        movdqa  xmm6, xmm4
        movq    xmm0, QWORD PTR [rdx+0x8]
        movdqa  xmm8, xmm4
        add     rdx, 0x10
        add     rcx, 0x4
        pcmpgtw xmm6, xmm1
        pcmpgtw xmm8, xmm0
        movdqa  xmm7, xmm1
        punpcklwd xmm1, xmm6
        punpcklwd xmm7, xmm6
        movdqa  xmm6, xmm0
        pshufd  xmm1, xmm1, 0x4e
        punpcklwd xmm6, xmm8
        movdqa  xmm2, xmm1
        movdqa  xmm1, xmm0
        movdqa  xmm0, xmm7
        pslld   xmm0, 0x6
        punpcklwd xmm1, xmm8
        psubd   xmm0, xmm7
        pshufd  xmm1, xmm1, 0x4e
        pslld   xmm0, 0x8
        psubd   xmm0, xmm7
        movdqa  xmm7, xmm2
        pslld   xmm7, 0x6
        psubd   xmm7, xmm2
        pslld   xmm7, 0x8
        psubd   xmm7, xmm2
        movdqa  xmm2, xmm6
        pslld   xmm2, 0x6
        psubd   xmm2, xmm6
        pslld   xmm2, 0x8
        psubd   xmm2, xmm6
        movdqa  xmm6, xmm1
        pslld   xmm6, 0x6
        psubd   xmm6, xmm1
        pslld   xmm6, 0x8
        psubd   xmm6, xmm1
        movdqa  xmm1, xmm0
        pslld   xmm1, 0x2
        paddd   xmm1, xmm0
        movdqa  xmm0, xmm7
        pslld   xmm0, 0x2
        paddd   xmm0, xmm7
        pslld   xmm1, 0x4
        paddd   xmm1, xmm3
        pslld   xmm0, 0x4
        paddd   xmm0, xmm3
        psrld   xmm1, 0x1c
        movdqa  xmm7, xmm1
        psrld   xmm0, 0x1c
        punpcklwd xmm7, xmm0
        punpcklwd xmm1, xmm0
        movdqa  xmm0, xmm2
        pslld   xmm0, 0x2
        pshufd  xmm7, xmm7, 0x4e
        paddd   xmm0, xmm2
        movdqa  xmm2, xmm6
        punpcklwd xmm1, xmm7
        pslld   xmm2, 0x2
        pand    xmm1, xmm5
        paddd   xmm2, xmm6
        movdqa  xmm7, xmm1
        pslld   xmm0, 0x4
        paddd   xmm0, xmm3
        pslld   xmm2, 0x4
        paddd   xmm2, xmm3
        psrld   xmm0, 0x1c
        movdqa  xmm6, xmm0
        psrld   xmm2, 0x1c
        punpcklwd xmm6, xmm2
        punpcklwd xmm0, xmm2
        pshufd  xmm6, xmm6, 0x4e
        punpcklwd xmm0, xmm6
        pand    xmm0, xmm5
        packuswb xmm7, xmm0
        pshufd  xmm7, xmm7, 0x8
        movq    rax, xmm7
        mov     r8, rax
        mov     r9, rax
        mov     r10, rax
        mov     r11, rax
        shr     r8, 0x18
        shr     r9, 0x10
        movzx   edi, ah
        shl     r8d, 0x4
        shr     r10, 0x20
        shr     r11, 0x38
        or      r8d, r9d
        mov     r9, rax
        shl     edi, 0x4
        shr     r9, 0x28
        or      edi, eax
        shr     rax, 0x30
        movzx   r8d, r8b
        shl     r9d, 0x4
        movzx   edi, dil
        or      r9d, r10d
        mov     r10, r11
        shl     r10d, 0x4
        movzx   r9d, r9b
        or      eax, r10d
        movzx   eax, al
        shl     eax, 0x8
        or      eax, r9d
        shl     eax, 0x8
        or      eax, r8d
        shl     eax, 0x8
        or      eax, edi
        mov     DWORD PTR [rcx-0x4], eax
        cmp     rsi, rdx
        jne     L2488
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_poly_compress_d10 (0x2660)

L2660:
        push    r13
        lea     rdx, [rdi+0x4]
        xor     ecx, ecx
        mov     r8d, 0x9d7dbc00
        movabs  rdi, 0x100000000
        push    r12
        push    rbp
        push    rbx
        lea     r10, [rsp-0x8]
        mov     r9, rsp
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L2688:
        mov     r11, r10
        mov     ebx, ecx
L268d:
        mov     eax, ebx
        add     r11, 0x2
        add     ebx, 0x1
        movsx   rax, WORD PTR [rsi+rax*2]
        imul    rax, r8
        add     rax, rdi
        shr     rax, 0x21
        and     ax, 0x3ff
        mov     WORD PTR [r11-0x2], ax
        cmp     r9, r11
        jne     L268d
        movzx   ebx, WORD PTR [rsp-0x8]
        movzx   r12d, WORD PTR [rsp-0x6]
        add     ecx, 0x4
        add     rdx, 0x5
        movzx   eax, WORD PTR [rsp-0x4]
        movzx   r11d, WORD PTR [rsp-0x2]
        mov     r13d, ebx
        lea     ebp, [r12*4+0x0]
        shr     r12w, 0x6
        movzx   ebx, bl
        shr     r13w, 0x8
        or      ebp, r13d
        mov     r13d, eax
        shr     ax, 0x4
        shl     r13d, 0x4
        movzx   ebp, bpl
        or      r12d, r13d
        mov     r13d, eax
        mov     eax, r11d
        shr     r11w, 0x2
        shl     eax, 0x6
        movzx   r12d, r12b
        mov     BYTE PTR [rdx-0x5], r11b
        or      eax, r13d
        movzx   eax, al
        shl     eax, 0x8
        or      eax, r12d
        shl     eax, 0x8
        or      eax, ebp
        shl     eax, 0x8
        or      eax, ebx
        mov     DWORD PTR [rdx-0x9], eax
        cmp     ecx, 0x100
        jne     L2688
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret

// mlkem_poly_decompress_d4 (0x2740)

L2740:
        xor     edx, edx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2748:
        movzx   eax, BYTE PTR [rsi+rdx*1]
        and     eax, 0xf
        imul    eax, eax, 0xd01
        add     eax, 0x8
        shr     eax, 0x4
        mov     WORD PTR [rdi+rdx*4], ax
        movzx   eax, BYTE PTR [rsi+rdx*1]
        shr     al, 0x4
        movzx   eax, al
        imul    eax, eax, 0xd01
        add     eax, 0x8
        shr     eax, 0x4
        mov     WORD PTR [rdi+rdx*4+0x2], ax
        add     rdx, 0x1
        cmp     rdx, 0x80
        jne     L2748
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_poly_decompress_d10 (0x2790)

L2790:
        movq    xmm4, QWORD PTR [rip+L8010]
        mov     rdx, rsi
        mov     rcx, rdi
        pxor    xmm3, xmm3
        lea     rsi, [rsi+0x140]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L27b0:
        movzx   r9d, BYTE PTR [rdx+0x1]
        movzx   edi, WORD PTR [rdx]
        add     rdx, 0x5
        add     rcx, 0x8
        movzx   r10d, BYTE PTR [rdx-0x3]
        movzx   eax, BYTE PTR [rdx-0x2]
        shr     r9b, 0x2
        and     edi, 0x3ff
        mov     r8d, r10d
        movzx   r9d, r9b
        shl     r10d, 0x6
        or      r9d, r10d
        shr     r8b, 0x4
        movzx   r10d, al
        shl     r10d, 0x4
        movzx   r8d, r8b
        shr     al, 0x6
        and     r9d, 0x3ff
        or      r8d, r10d
        movzx   r10d, BYTE PTR [rdx-0x1]
        movzx   eax, al
        and     r8d, 0x3ff
        shl     r10d, 0x2
        or      eax, r10d
        movzx   eax, ax
        shl     rax, 0x10
        or      rax, r8
        shl     rax, 0x10
        or      rax, r9
        shl     rax, 0x10
        or      rax, rdi
        movq    xmm0, rax
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm3
        punpcklwd xmm2, xmm3
        pshufd  xmm0, xmm0, 0x4e
        movdqa  xmm1, xmm2
        pslld   xmm1, 0x1
        paddd   xmm1, xmm2
        pslld   xmm1, 0x2
        paddd   xmm1, xmm2
        paddd   xmm2, xmm4
        pslld   xmm1, 0x8
        paddd   xmm1, xmm2
        movdqa  xmm2, xmm0
        pslld   xmm2, 0x1
        paddd   xmm2, xmm0
        psrld   xmm1, 0xa
        movdqa  xmm5, xmm1
        pslld   xmm2, 0x2
        paddd   xmm2, xmm0
        paddd   xmm0, xmm4
        pslld   xmm2, 0x8
        paddd   xmm2, xmm0
        psrld   xmm2, 0xa
        punpcklwd xmm5, xmm2
        punpcklwd xmm1, xmm2
        pshufd  xmm5, xmm5, 0x4e
        punpcklwd xmm1, xmm5
        movq    QWORD PTR [rcx-0x8], xmm1
        cmp     rdx, rsi
        jne     L27b0
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_poly_compress_d5 (0x28c0)

L28c0:
        push    rbp
        mov     rcx, rsi
        mov     rdx, rdi
        lea     rsi, [rdi+0xa0]
        movq    xmm2, QWORD PTR [rip+L8018]
        push    rbx
        pxor    xmm3, xmm3
        movq    xmm4, QWORD PTR [rip+L8008]
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L28e8:
        movq    xmm0, QWORD PTR [rcx]
        movdqa  xmm1, xmm3
        add     rdx, 0x5
        add     rcx, 0x10
        movq    xmm6, QWORD PTR [rcx-0x8]
        pcmpgtw xmm1, xmm0
        movdqa  xmm9, xmm0
        movdqa  xmm8, xmm6
        punpcklwd xmm0, xmm1
        punpcklwd xmm9, xmm1
        pshufd  xmm0, xmm0, 0x4e
        movdqa  xmm10, xmm0
        movdqa  xmm0, xmm3
        pcmpgtw xmm0, xmm6
        movdqa  xmm5, xmm10
        pslld   xmm5, 0x2
        paddd   xmm5, xmm10
        punpcklwd xmm8, xmm0
        punpcklwd xmm6, xmm0
        movdqa  xmm0, xmm9
        pslld   xmm0, 0x2
        pshufd  xmm6, xmm6, 0x4e
        movdqa  xmm11, xmm8
        paddd   xmm0, xmm9
        pslld   xmm11, 0x2
        movdqa  xmm7, xmm6
        paddd   xmm11, xmm8
        pslld   xmm7, 0x2
        paddd   xmm7, xmm6
        movdqa  xmm1, xmm0
        pslld   xmm1, 0x6
        psubd   xmm1, xmm0
        movdqa  xmm0, xmm5
        pslld   xmm0, 0x6
        psubd   xmm0, xmm5
        pslld   xmm1, 0x6
        psubd   xmm1, xmm9
        pslld   xmm0, 0x6
        psubd   xmm0, xmm10
        pslld   xmm1, 0x6
        paddd   xmm1, xmm2
        pslld   xmm0, 0x6
        paddd   xmm0, xmm2
        psrld   xmm1, 0x1b
        movdqa  xmm5, xmm1
        psrld   xmm0, 0x1b
        punpcklwd xmm5, xmm0
        punpcklwd xmm1, xmm0
        movdqa  xmm0, xmm11
        pshufd  xmm5, xmm5, 0x4e
        pslld   xmm0, 0x6
        punpcklwd xmm1, xmm5
        movdqa  xmm5, xmm7
        psubd   xmm0, xmm11
        pslld   xmm5, 0x6
        pand    xmm1, xmm4
        psubd   xmm5, xmm7
        movdqa  xmm7, xmm1
        pslld   xmm0, 0x6
        psubd   xmm0, xmm8
        pslld   xmm5, 0x6
        psubd   xmm5, xmm6
        pslld   xmm0, 0x6
        paddd   xmm0, xmm2
        pslld   xmm5, 0x6
        paddd   xmm5, xmm2
        psrld   xmm0, 0x1b
        movdqa  xmm6, xmm0
        psrld   xmm5, 0x1b
        punpcklwd xmm6, xmm5
        punpcklwd xmm0, xmm5
        pshufd  xmm6, xmm6, 0x4e
        punpcklwd xmm0, xmm6
        pand    xmm0, xmm4
        packuswb xmm7, xmm0
        pshufd  xmm7, xmm7, 0x8
        movq    rax, xmm7
        mov     rdi, rax
        mov     rbp, rax
        movzx   ebx, ah
        mov     r8, rax
        shr     rdi, 0x18
        shr     rbp, 0x10
        mov     r11, rbx
        mov     rbx, rax
        shl     ebp, 0x2
        mov     r10d, edi
        shr     rbx, 0x20
        mov     r9, r11
        shl     r10d, 0x7
        shr     r11b, 0x3
        shr     r8, 0x30
        or      r10d, ebp
        shr     dil, 1
        mov     rbp, rax
        shr     rbp, 0x28
        or      r10d, r11d
        mov     r11d, ebx
        shr     bl, 0x4
        shl     r11d, 0x4
        add     ebp, ebp
        shl     r9d, 0x5
        movzx   r10d, r10b
        or      r11d, edi
        mov     edi, r8d
        or      r9d, eax
        shr     rax, 0x38
        shl     edi, 0x6
        movzx   r11d, r11b
        movzx   r9d, r9b
        shr     r8b, 0x2
        or      edi, ebp
        shl     eax, 0x3
        or      edi, ebx
        or      r8d, eax
        movzx   edi, dil
        mov     BYTE PTR [rdx-0x1], r8b
        shl     edi, 0x8
        or      edi, r11d
        shl     edi, 0x8
        or      edi, r10d
        shl     edi, 0x8
        or      edi, r9d
        mov     DWORD PTR [rdx-0x5], edi
        cmp     rdx, rsi
        jne     L28e8
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_poly_compress_d11 (0x2af0)

L2af0:
        push    r12
        mov     rcx, rdi
        pxor    xmm5, xmm5
        lea     rdi, [rdi+0x160]
        push    rbp
        movdqa  xmm3, XMMWORD PTR [rip+L8030]
        pxor    xmm4, xmm4
        push    rbx
        movdqa  xmm6, XMMWORD PTR [rip+L8040]
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2b20:
        movdqa  xmm2, XMMWORD PTR [rsi]
        movdqa  xmm0, xmm5
        movdqa  xmm7, xmm4
        pcmpgtw xmm0, xmm2
        movdqa  xmm1, xmm2
        punpcklwd xmm1, xmm0
        punpckhwd xmm2, xmm0
        pcmpgtd xmm7, xmm1
        movdqa  xmm8, xmm1
        punpckldq xmm8, xmm7
        movdqa  xmm9, xmm8
        psllq   xmm9, 0x2
        paddq   xmm9, xmm8
        movdqa  xmm0, xmm9
        psllq   xmm0, 0x6
        psubq   xmm0, xmm9
        psllq   xmm0, 0x6
        psubq   xmm0, xmm8
        psllq   xmm0, 0x3
        psubq   xmm0, xmm8
        psllq   xmm0, 0x4
        psubq   xmm0, xmm8
        movdqa  xmm8, xmm1
        punpckhdq xmm8, xmm7
        psllq   xmm0, 0xb
        movdqa  xmm7, xmm8
        paddq   xmm0, xmm3
        psllq   xmm7, 0x2
        psrlq   xmm0, 0x21
        paddq   xmm7, xmm8
        movdqa  xmm1, xmm7
        psllq   xmm1, 0x6
        psubq   xmm1, xmm7
        movdqa  xmm7, xmm4
        psllq   xmm1, 0x6
        pcmpgtd xmm7, xmm2
        psubq   xmm1, xmm8
        psllq   xmm1, 0x3
        psubq   xmm1, xmm8
        psllq   xmm1, 0x4
        psubq   xmm1, xmm8
        movdqa  xmm8, xmm2
        punpckldq xmm8, xmm7
        psllq   xmm1, 0xb
        movdqa  xmm9, xmm8
        paddq   xmm1, xmm3
        psllq   xmm9, 0x2
        psrlq   xmm1, 0x21
        paddq   xmm9, xmm8
        shufps  xmm0, xmm1, 0x88
        movdqa  xmm1, xmm9
        psllq   xmm1, 0x6
        psubq   xmm1, xmm9
        psllq   xmm1, 0x6
        psubq   xmm1, xmm8
        psllq   xmm1, 0x3
        psubq   xmm1, xmm8
        psllq   xmm1, 0x4
        psubq   xmm1, xmm8
        movdqa  xmm8, xmm2
        punpckhdq xmm8, xmm7
        psllq   xmm1, 0xb
        movdqa  xmm7, xmm8
        paddq   xmm1, xmm3
        psllq   xmm7, 0x2
        psrlq   xmm1, 0x21
        paddq   xmm7, xmm8
        movdqa  xmm2, xmm7
        psllq   xmm2, 0x6
        psubq   xmm2, xmm7
        psllq   xmm2, 0x6
        psubq   xmm2, xmm8
        psllq   xmm2, 0x3
        psubq   xmm2, xmm8
        psllq   xmm2, 0x4
        psubq   xmm2, xmm8
        psllq   xmm2, 0xb
        paddq   xmm2, xmm3
        psrlq   xmm2, 0x21
        shufps  xmm1, xmm2, 0x88
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        pand    xmm0, xmm6
        pextrw  r8d, xmm0, 0x0
        pextrw  r10d, xmm0, 0x1
        pextrw  ebx, xmm0, 0x2
        mov     r9d, r8d
        pextrw  ebp, xmm0, 0x3
        pextrw  eax, xmm0, 0x4
        movzx   r8d, r8b
        shr     r9w, 0x8
        lea     r12d, [rbp+rbp*1+0x0]
        pextrw  edx, xmm0, 0x5
        shr     bp, 0x7
        lea     r11d, [r10*8+0x0]
        shr     r10w, 0x5
        or      r9d, r11d
        mov     r11d, ebx
        shl     r11d, 0x6
        movzx   r9d, r9b
        or      r10d, r11d
        mov     r11d, ebx
        shr     bx, 0xa
        or      ebx, r12d
        mov     r12d, eax
        shr     r11w, 0x2
        movzx   r10d, r10b
        shl     r12d, 0x4
        movzx   ebx, bl
        movzx   r11d, r11b
        or      ebp, r12d
        mov     r12d, eax
        mov     eax, edx
        shl     eax, 0x7
        shr     r12w, 0x4
        movzx   ebp, bpl
        or      r12d, eax
        mov     eax, edx
        shr     dx, 0x9
        shr     ax, 1
        movzx   r12d, r12b
        movzx   eax, al
        shl     rax, 0x8
        or      rax, r12
        shl     rax, 0x8
        or      rax, rbp
        shl     rax, 0x8
        or      rax, rbx
        shl     rax, 0x8
        or      rax, r11
        shl     rax, 0x8
        or      rax, r10
        shl     rax, 0x8
        or      rax, r9
        shl     rax, 0x8
        or      rax, r8
        mov     QWORD PTR [rcx], rax
        pextrw  eax, xmm0, 0x6
        lea     r8d, [rax*4+0x0]
        shr     ax, 0x6
        or      edx, r8d
        mov     BYTE PTR [rcx+0x8], dl
        pextrw  edx, xmm0, 0x7
        mov     r8d, edx
        shl     r8d, 0x5
        shr     dx, 0x3
        add     rcx, 0xb
        add     rsi, 0x10
        or      eax, r8d
        mov     BYTE PTR [rcx-0x1], dl
        mov     BYTE PTR [rcx-0x2], al
        cmp     rdi, rcx
        jne     L2b20
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_poly_decompress_d5 (0x2de0)

L2de0:
        push    r12
        mov     rdx, rsi
        mov     rcx, rdi
        lea     rsi, [rsi+0xa0]
        push    rbp
        pxor    xmm4, xmm4
        pxor    xmm2, xmm2
        movq    xmm3, QWORD PTR [rip+L8020]
        push    rbx
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2e08:
        movzx   edi, BYTE PTR [rdx]
        movzx   r10d, BYTE PTR [rdx+0x1]
        movzx   r11d, BYTE PTR [rdx+0x2]
        movzx   ebx, BYTE PTR [rdx+0x3]
        mov     r9d, edi
        lea     r8d, [r10*8+0x0]
        movzx   eax, BYTE PTR [rdx+0x4]
        and     edi, 0x1f
        shr     r9b, 0x5
        lea     ebp, [r11+r11*1]
        shr     r11b, 0x4
        or      r8d, r9d
        mov     r9d, r10d
        shr     r10b, 0x7
        lea     r12d, [rax*4+0x0]
        shr     al, 0x3
        or      r10d, ebp
        mov     ebp, ebx
        shr     r9b, 0x2
        shl     ebp, 0x4
        movzx   eax, al
        and     r10d, 0x1f
        and     r9d, 0x1f
        or      r11d, ebp
        mov     ebp, ebx
        shr     bl, 0x6
        and     r8d, 0x1f
        shl     rax, 0x8
        or      ebx, r12d
        shr     bpl, 1
        and     r11d, 0x1f
        and     ebx, 0x1f
        and     ebp, 0x1f
        or      rax, rbx
        shl     rax, 0x8
        or      rax, rbp
        shl     rax, 0x8
        or      rax, r11
        shl     rax, 0x8
        or      rax, r10
        shl     rax, 0x8
        or      rax, r9
        shl     rax, 0x8
        or      rax, r8
        shl     rax, 0x8
        or      rax, rdi
        add     rdx, 0x5
        add     rcx, 0x10
        movq    xmm0, rax
        movdqa  xmm6, xmm0
        punpcklbw xmm0, xmm4
        punpcklbw xmm6, xmm4
        pshufd  xmm0, xmm0, 0x4e
        movdqa  xmm5, xmm6
        punpcklwd xmm6, xmm2
        movdqa  xmm7, xmm0
        punpcklwd xmm5, xmm2
        pshufd  xmm6, xmm6, 0x4e
        punpcklwd xmm7, xmm2
        movdqa  xmm1, xmm5
        punpcklwd xmm0, xmm2
        pslld   xmm1, 0x1
        pshufd  xmm0, xmm0, 0x4e
        paddd   xmm1, xmm5
        pslld   xmm1, 0x2
        paddd   xmm1, xmm5
        paddd   xmm5, xmm3
        pslld   xmm1, 0x8
        paddd   xmm1, xmm5
        movdqa  xmm5, xmm6
        pslld   xmm5, 0x1
        paddd   xmm5, xmm6
        psrld   xmm1, 0x5
        pslld   xmm5, 0x2
        paddd   xmm5, xmm6
        paddd   xmm6, xmm3
        pslld   xmm5, 0x8
        paddd   xmm5, xmm6
        movdqa  xmm6, xmm1
        psrld   xmm5, 0x5
        punpcklwd xmm6, xmm5
        punpcklwd xmm1, xmm5
        movdqa  xmm5, xmm0
        pshufd  xmm6, xmm6, 0x4e
        pslld   xmm5, 0x1
        punpcklwd xmm1, xmm6
        paddd   xmm5, xmm0
        movq    QWORD PTR [rcx-0x10], xmm1
        movdqa  xmm1, xmm7
        pslld   xmm1, 0x1
        paddd   xmm1, xmm7
        pslld   xmm5, 0x2
        paddd   xmm5, xmm0
        paddd   xmm0, xmm3
        pslld   xmm1, 0x2
        paddd   xmm1, xmm7
        paddd   xmm7, xmm3
        pslld   xmm5, 0x8
        paddd   xmm0, xmm5
        pslld   xmm1, 0x8
        paddd   xmm1, xmm7
        psrld   xmm0, 0x5
        psrld   xmm1, 0x5
        movdqa  xmm5, xmm1
        punpcklwd xmm1, xmm0
        punpcklwd xmm5, xmm0
        pshufd  xmm5, xmm5, 0x4e
        punpcklwd xmm1, xmm5
        movq    QWORD PTR [rcx-0x8], xmm1
        cmp     rdx, rsi
        jne     L2e08
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_poly_decompress_d11 (0x2fe0)

L2fe0:
        movdqa  xmm4, XMMWORD PTR [rip+L8050]
        movdqa  xmm3, XMMWORD PTR [rip+L8060]
        push    r13
        push    r12
        push    rbp
        lea     rbp, [rsi+0x160]
        push    rbx
        mov     rbx, rdi
        mov     rdi, rsi
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3008:
        movzx   r10d, BYTE PTR [rdi+0x1]
        movzx   r8d, BYTE PTR [rdi+0x2]
        movzx   r9d, BYTE PTR [rdi+0x4]
        movzx   r13d, BYTE PTR [rdi+0x3]
        shr     r10b, 0x3
        mov     r11d, r8d
        shl     r8d, 0x5
        movzx   eax, BYTE PTR [rdi+0x5]
        movzx   r10d, r10b
        shl     r13d, 0x2
        movzx   r12d, BYTE PTR [rdi+0x6]
        movzx   ecx, WORD PTR [rdi]
        or      r10d, r8d
        mov     r8d, r9d
        shr     r11b, 0x6
        movzx   edx, BYTE PTR [rdi+0x8]
        shl     r8d, 0xa
        movzx   r11d, r11b
        shr     r9b, 1
        movzx   esi, BYTE PTR [rdi+0x9]
        or      r8d, r13d
        movzx   r9d, r9b
        movzx   r13d, BYTE PTR [rdi+0x7]
        and     cx, 0x7ff
        or      r8d, r11d
        movzx   r11d, al
        shr     al, 0x4
        and     r10w, 0x7ff
        shl     r11d, 0x7
        movzx   eax, al
        add     r13d, r13d
        and     r8w, 0x7ff
        or      r9d, r11d
        movd    xmm1, ecx
        movd    xmm5, r8d
        movzx   r11d, r12b
        shl     r11d, 0x4
        shr     r12b, 0x7
        and     r9w, 0x7ff
        pinsrw  xmm1, r10d, 0x1
        or      eax, r11d
        mov     r11d, edx
        movzx   r12d, r12b
        shr     dl, 0x2
        shl     r11d, 0x9
        movzx   edx, dl
        and     ax, 0x7ff
        or      r11d, r13d
        movd    xmm0, eax
        pinsrw  xmm5, r9d, 0x1
        or      r11d, r12d
        movzx   r12d, sil
        shr     sil, 0x5
        punpckldq xmm1, xmm5
        shl     r12d, 0x6
        movzx   esi, sil
        and     r11w, 0x7ff
        or      edx, r12d
        movzx   r12d, BYTE PTR [rdi+0xa]
        pinsrw  xmm0, r11d, 0x1
        and     dx, 0x7ff
        shl     r12d, 0x3
        movd    xmm2, edx
        or      esi, r12d
        add     rdi, 0xb
        add     rbx, 0x10
        pinsrw  xmm2, esi, 0x1
        punpckldq xmm0, xmm2
        movdqa  xmm2, xmm4
        punpcklqdq xmm1, xmm0
        pmullw  xmm2, xmm1
        pmulhuw xmm1, xmm4
        movdqa  xmm0, xmm2
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm1
        movdqa  xmm1, xmm2
        paddd   xmm0, xmm3
        paddd   xmm1, xmm3
        psrld   xmm1, 0xb
        psrld   xmm0, 0xb
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        movaps  XMMWORD PTR [rbx-0x10], xmm0
        cmp     rbp, rdi
        jne     L3008
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret

// mlkem_poly_tobytes (0x3180)

L3180:
        lea     r8, [rdi+0x180]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3190:
        movzx   eax, WORD PTR [rsi+0x2]
        movzx   edx, WORD PTR [rsi]
        add     rdi, 0x3
        add     rsi, 0x4
        mov     ecx, eax
        mov     BYTE PTR [rdi-0x3], dl
        shr     dx, 0x8
        shl     ecx, 0x4
        shr     ax, 0x4
        or      edx, ecx
        mov     BYTE PTR [rdi-0x1], al
        mov     BYTE PTR [rdi-0x2], dl
        cmp     r8, rdi
        jne     L3190
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_poly_frombytes (0x31c0)

L31c0:
        lea     r9, [rsi+0x180]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L31d0:
        movzx   eax, BYTE PTR [rsi+0x1]
        movzx   edx, BYTE PTR [rsi+0x2]
        add     rsi, 0x3
        add     rdi, 0x4
        movzx   r8d, BYTE PTR [rsi-0x3]
        mov     ecx, eax
        shr     al, 0x4
        shl     ecx, 0x8
        movzx   eax, al
        shl     edx, 0x4
        and     cx, 0xf00
        or      eax, edx
        or      ecx, r8d
        mov     WORD PTR [rdi-0x2], ax
        mov     WORD PTR [rdi-0x4], cx
        cmp     r9, rsi
        jne     L31d0
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlkem_poly_frommsg (0x3210)

L3210:
        mov     r8, rdi
        mov     r9d, 0x1
        xor     edi, edi
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3220:
        xor     ecx, ecx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L3228:
        mov     eax, r9d
        shl     eax, cl
        and     al, BYTE PTR [rsi]
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        lea     edx, [rcx+rdi*1]
        add     ecx, 0x1
        and     ax, 0x681
        mov     WORD PTR [r8+rdx*2], ax
        cmp     ecx, 0x8
        jne     L3228
        add     edi, 0x8
        add     rsi, 0x1
        cmp     edi, 0x100
        jne     L3220
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlkem_poly_tomsg (0x3260)

L3260:
        xor     r8d, r8d
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3268:
        mov     BYTE PTR [rdi], 0x0
        xor     edx, edx
        xor     ecx, ecx
        // nop
        .byte   0x90
L3270:
        lea     eax, [rcx+r8*1]
        movsx   eax, WORD PTR [rsi+rax*2]
        imul    eax, eax, 0x13afb8
        add     eax, 0x40000000
        shr     eax, 0x1f
        shl     eax, cl
        add     ecx, 0x1
        or      edx, eax
        mov     BYTE PTR [rdi], dl
        cmp     ecx, 0x8
        jne     L3270
        add     r8d, 0x8
        add     rdi, 0x1
        cmp     r8d, 0x100
        jne     L3268
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlk_keccak_absorb_once (0x32b0)

L32b0:
        push    r14
        xor     eax, eax
        push    r13
        mov     r13, rdi
        add     rdi, 0x8
        push    r12
        mov     r12d, esi
        push    rbp
        mov     r14, r12
        mov     rbp, rdx
        push    rbx
        mov     rbx, rcx
        mov     rcx, r13
        sub     rsp, 0x10
        mov     BYTE PTR [rsp+0xc], r8b
        mov     QWORD PTR [rdi-0x8], 0x0
        mov     QWORD PTR [rdi+0xb8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xc8
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        cmp     rbx, r12
        jb      L332b
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L3308:
        mov     rsi, rbp
        mov     ecx, r14d
        xor     edx, edx
        mov     rdi, r13
        call    L3d40
        sub     rbx, r12
        mov     rdi, r13
        add     rbp, r12
        call    L3e70
        cmp     rbx, r12
        jae     L3308
L332b:
        sub     r14d, 0x1
        mov     r12d, ebx
        test    rbx, rbx
        jne     L3378
L3337:
        lea     rbx, [rsp+0xc]
        mov     edx, r12d
        mov     rdi, r13
        mov     ecx, 0x1
        mov     rsi, rbx
        call    L3d40
        mov     edx, r14d
        mov     rsi, rbx
        mov     rdi, r13
        mov     ecx, 0x1
        mov     BYTE PTR [rsp+0xc], 0x80
        call    L3d40
        add     rsp, 0x10
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L3378:
        mov     ecx, ebx
        xor     edx, edx
        mov     rsi, rbp
        mov     rdi, r13
        call    L3d40
        mov     eax, r14d
        cmp     rax, rbx
        jne     L3337
        lea     rsi, [rsp+0xc]
        mov     edx, ebx
        mov     rdi, r13
        mov     ecx, 0x1
        or      BYTE PTR [rsp+0xc], 0x80
        call    L3d40
        add     rsp, 0x10
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_shake128_absorb_once (0x33c0)

L33c0:
        mov     rcx, rdx
        mov     r8d, 0x1f
        mov     rdx, rsi
        mov     esi, 0xa8
        jmp     L32b0
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_shake128_squeezeblocks (0x33e0)

L33e0:
        test    rsi, rsi
        je      L3428
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L33f8:
        mov     rdi, r12
        call    L3e70
        mov     rsi, rbp
        mov     ecx, 0xa8
        xor     edx, edx
        mov     rdi, r12
        add     rbp, 0xa8
        call    L3d10
        sub     rbx, 0x1
        jne     L33f8
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L3428:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_shake128_init (0x3430)

L3430:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem_shake128_release (0x3440)

L3440:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0xd0], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xe0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_shake256 (0x3480)

L3480:
        push    rbp
        mov     r8d, 0x1f
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        mov     esi, 0x88
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xe0
        mov     r14, rsp
        mov     rdi, r14
        call    L32b0
        test    r12, r12
        je      L34eb
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L34c0:
        mov     rdi, r14
        mov     ebx, 0x88
        call    L3e70
        cmp     r12, rbx
        mov     rsi, r13
        mov     rdi, r14
        cmovbe  rbx, r12
        xor     edx, edx
        mov     ecx, ebx
        add     r13, rbx
        call    L3d10
        sub     r12, rbx
        jne     L34c0
L34eb:
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x1c
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_sha3_256 (0x3510)

L3510:
        push    rbp
        mov     rcx, rdx
        mov     r8d, 0x6
        mov     rdx, rsi
        push    rbx
        mov     rbp, rdi
        mov     esi, 0x88
        sub     rsp, 0xd8
        mov     rbx, rsp
        mov     rdi, rbx
        call    L32b0
        mov     rdi, rbx
        call    L3e70
        mov     rdi, rbx
        mov     ecx, 0x20
        xor     edx, edx
        mov     rsi, rbp
        call    L3d10
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x19
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0xd8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_sha3_512 (0x3570)

L3570:
        push    rbp
        mov     rcx, rdx
        mov     r8d, 0x6
        mov     rdx, rsi
        push    rbx
        mov     rbp, rdi
        mov     esi, 0x48
        sub     rsp, 0xd8
        mov     rbx, rsp
        mov     rdi, rbx
        call    L32b0
        mov     rdi, rbx
        call    L3e70
        mov     rdi, rbx
        mov     ecx, 0x40
        xor     edx, edx
        mov     rsi, rbp
        call    L3d10
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x19
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0xd8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlk_keccak_absorb_once_x4.constprop.0 (0x35d0)

L35d0:
        push    r15
        mov     r15, r8
        mov     r8, r9
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, rdx
        push    rbp
        push    rbx
        mov     ebx, esi
        sub     rsp, 0x28
        mov     rbp, QWORD PTR [rsp+0x60]
        mov     DWORD PTR [rsp+0xc], esi
        mov     BYTE PTR [rsp+0x1f], 0x1f
        cmp     rbp, rbx
        jb      L364f
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L3608:
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     rcx, r15
        mov     rdx, r13
        mov     eax, DWORD PTR [rsp+0x14]
        mov     rsi, r12
        mov     rdi, r14
        sub     rbp, rbx
        add     r12, rbx
        add     r13, rbx
        add     r15, rbx
        push    rax
        mov     QWORD PTR [rsp+0x10], r8
        call    L3df0
        mov     rdi, r14
        call    L4740
        mov     r8, QWORD PTR [rsp+0x10]
        pop     r9
        pop     r10
        add     r8, rbx
        cmp     rbp, rbx
        jae     L3608
L364f:
        mov     eax, DWORD PTR [rsp+0xc]
        mov     ebx, ebp
        sub     eax, 0x1
        mov     DWORD PTR [rsp], eax
        test    rbp, rbp
        jne     L36c0
L3660:
        lea     rbp, [rsp+0x1f]
        sub     rsp, 0x8
        mov     r9d, ebx
        mov     rdi, r14
        push    0x1
        mov     r8, rbp
        mov     rcx, rbp
        mov     rdx, rbp
        mov     rsi, rbp
        call    L3df0
        mov     r9d, DWORD PTR [rsp+0x10]
        mov     rdx, rbp
        mov     r8, rbp
        mov     rcx, rbp
        mov     rsi, rbp
        mov     rdi, r14
        mov     BYTE PTR [rsp+0x2f], 0x80
        mov     DWORD PTR [rsp], 0x1
        call    L3df0
        pop     rax
        pop     rdx
        add     rsp, 0x28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L36c0:
        sub     rsp, 0x8
        mov     rdi, r14
        xor     r9d, r9d
        mov     rcx, r15
        push    rbp
        mov     rdx, r13
        mov     rsi, r12
        call    L3df0
        mov     eax, DWORD PTR [rsp+0x10]
        pop     rdi
        pop     r8
        cmp     rax, rbp
        jne     L3660
        lea     rsi, [rsp+0x1f]
        or      BYTE PTR [rsp+0x1f], 0x80
        mov     r9d, ebp
        mov     rdi, r14
        sub     rsp, 0x8
        mov     rcx, rsi
        mov     r8, rsi
        mov     rdx, rsi
        push    0x1
        call    L3df0
        pop     rcx
        pop     rsi
        add     rsp, 0x28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_shake128x4_absorb_once (0x3720)

L3720:
        sub     rsp, 0x10
        mov     r10, rdi
        mov     QWORD PTR [rdi], 0x0
        xor     eax, eax
        mov     QWORD PTR [rdi+0x318], 0x0
        lea     rdi, [rdi+0x8]
        mov     r11, rcx
        mov     rcx, r10
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        push    r9
        mov     rcx, rdx
        mov     r9, r8
        mov     rdx, rsi
        mov     r8, r11
        mov     esi, 0xa8
        mov     rdi, r10
        call    L35d0
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_shake128x4_squeezeblocks (0x3780)

L3780:
        test    r8, r8
        je      L3810
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rcx
        sub     rsp, 0x8
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L37b0:
        mov     rdi, r15
        call    L4740
        sub     rsp, 0x8
        mov     rdx, r12
        mov     r8, rbx
        push    0xa8
        mov     rcx, rbp
        mov     rsi, r13
        xor     r9d, r9d
        mov     rdi, r15
        add     r13, 0xa8
        add     r12, 0xa8
        add     rbp, 0xa8
        add     rbx, 0xa8
        call    L3d70
        pop     rax
        pop     rdx
        sub     r14, 0x1
        jne     L37b0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3810:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem_shake128x4_init (0x3820)

L3820:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem_shake128x4_release (0x3830)

L3830:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0x310], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_shake256x4 (0x3870)

L3870:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        mov     r11, r8
        push    QWORD PTR [r10-0x8]
        mov     rax, r11
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rdi
        push    r14
        mov     r14, rsi
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        sub     rsp, 0x5a8
        mov     QWORD PTR [rbp-0x5c0], rdx
        movabs  rdx, 0xf0f0f0f0f0f0f0f1
        mov     rbx, QWORD PTR [r10]
        mul     rdx
        mov     QWORD PTR [rbp-0x5a8], r11
        lea     r11, [rbp-0x350]
        mov     r8, QWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x5b0], rdi
        mov     rdi, r11
        mov     QWORD PTR [rbp-0x5c8], rcx
        mov     ecx, 0x64
        mov     rax, rdx
        mov     QWORD PTR [rbp-0x5b8], rsi
        mov     rsi, r9
        mov     r9, QWORD PTR [r10+0x10]
        shr     rax, 0x7
        mov     QWORD PTR [rbp-0x598], r11
        mov     rdx, rsi
        mov     esi, 0x88
        mov     QWORD PTR [rbp-0x5a0], rax
        xor     eax, eax
        rep stos QWORD PTR es:[rdi], rax
        push    QWORD PTR [r10+0x18]
        mov     rdi, r11
        mov     rcx, rbx
        call    L35d0
        mov     r11, QWORD PTR [rbp-0x5a8]
        pop     rdi
        pop     r8
        cmp     r11, 0x87
        jbe     L399b
        mov     rbx, QWORD PTR [rbp-0x5a0]
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L3940:
        mov     rdi, QWORD PTR [rbp-0x598]
        call    L4740
        sub     rsp, 0x8
        mov     rcx, r13
        mov     rsi, r15
        push    0x88
        mov     r8, r12
        mov     rdx, r14
        xor     r9d, r9d
        mov     rdi, QWORD PTR [rbp-0x598]
        add     r15, 0x88
        add     r14, 0x88
        add     r13, 0x88
        add     r12, 0x88
        call    L3d70
        pop     rcx
        pop     rsi
        sub     rbx, 0x1
        jne     L3940
        mov     r11, QWORD PTR [rbp-0x5a8]
L399b:
        movabs  rax, 0xf0f0f0f0f0f0f0f1
        mul     r11
        mov     rbx, rdx
        shr     rbx, 0x7
        mov     rax, rbx
        shl     rax, 0x4
        add     rax, rbx
        mov     rbx, r11
        shl     rax, 0x3
        sub     rbx, rax
        jne     L3a40
        lea     r12, [rbp-0x3e0]
        lea     r13, [rbp-0x470]
        lea     r14, [rbp-0x500]
        lea     r15, [rbp-0x590]
L39e1:
        mov     rdi, QWORD PTR [rbp-0x598]
        xor     eax, eax
        mov     ecx, 0x64
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x598]
        mov     ecx, 0x11
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x11
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x11
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x11
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L3a40:
        mov     rsi, QWORD PTR [rbp-0x5a0]
        mov     rdi, QWORD PTR [rbp-0x598]
        lea     r12, [rbp-0x3e0]
        lea     r13, [rbp-0x470]
        lea     r14, [rbp-0x500]
        lea     r15, [rbp-0x590]
        mov     rax, rsi
        shl     rax, 0x4
        add     rax, rsi
        shl     rax, 0x3
        mov     QWORD PTR [rbp-0x5a0], rax
        call    L4740
        sub     rsp, 0x8
        mov     rcx, r13
        mov     rdx, r14
        push    0x88
        xor     r9d, r9d
        mov     r8, r12
        mov     rsi, r15
        mov     rdi, QWORD PTR [rbp-0x598]
        call    L3d70
        mov     rdx, QWORD PTR [rbp-0x5b0]
        mov     rax, QWORD PTR [rbp-0x5a0]
        mov     ecx, ebx
        add     rdx, rax
        cmp     ebx, 0x8
        jae     L3b90
        test    bl, 0x4
        jne     L3cc3
        test    ecx, ecx
        je      L3ae4
        movzx   esi, BYTE PTR [rbp-0x590]
        mov     BYTE PTR [rdx], sil
        test    cl, 0x2
        jne     L3cd9
L3ae4:
        mov     rdx, QWORD PTR [rbp-0x5b8]
        mov     ecx, ebx
        add     rdx, rax
        cmp     ebx, 0x8
        jae     L3c38
        test    bl, 0x4
        jne     L3cad
        test    ecx, ecx
        je      L3b19
        movzx   esi, BYTE PTR [rbp-0x500]
        mov     BYTE PTR [rdx], sil
        test    cl, 0x2
        jne     L3cf9
L3b19:
        mov     rdx, QWORD PTR [rbp-0x5c0]
        mov     ecx, ebx
        add     rdx, rax
        cmp     ebx, 0x8
        jae     L3c00
        test    bl, 0x4
        jne     L3c97
        test    ecx, ecx
        je      L3b4e
        movzx   esi, BYTE PTR [rbp-0x470]
        mov     BYTE PTR [rdx], sil
        test    cl, 0x2
        jne     L3ce9
L3b4e:
        mov     rsi, QWORD PTR [rbp-0x5c8]
        mov     ecx, ebx
        add     rsi, rax
        mov     rax, rsi
        cmp     ebx, 0x8
        jae     L3bc8
        and     ebx, 0x4
        jne     L3c7f
        test    ecx, ecx
        je      L3b81
        movzx   edx, BYTE PTR [rbp-0x3e0]
        mov     BYTE PTR [rsi], dl
        test    cl, 0x2
        jne     L3c6d
L3b81:
        pop     rax
        pop     rdx
        jmp     L39e1
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3b90:
        mov     rcx, QWORD PTR [rbp-0x590]
        lea     rdi, [rdx+0x8]
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rdx], rcx
        mov     ecx, ebx
        mov     rsi, QWORD PTR [r15+rcx*1-0x8]
        mov     QWORD PTR [rdx+rcx*1-0x8], rsi
        sub     rdx, rdi
        mov     rsi, r15
        lea     ecx, [rbx+rdx*1]
        sub     rsi, rdx
        shr     ecx, 0x3
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        jmp     L3ae4
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L3bc8:
        mov     rdx, QWORD PTR [rbp-0x3e0]
        lea     rdi, [rsi+0x8]
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rsi], rdx
        mov     edx, ebx
        sub     rax, rdi
        mov     rcx, QWORD PTR [r12+rdx*1-0x8]
        mov     QWORD PTR [rsi+rdx*1-0x8], rcx
        lea     ecx, [rbx+rax*1]
        mov     rsi, r12
        sub     rsi, rax
        shr     ecx, 0x3
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        pop     rax
        pop     rdx
        jmp     L39e1
        // nop
        .byte   0x90
L3c00:
        mov     rcx, QWORD PTR [rbp-0x470]
        lea     rdi, [rdx+0x8]
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rdx], rcx
        mov     ecx, ebx
        mov     rsi, QWORD PTR [r13+rcx*1-0x8]
        mov     QWORD PTR [rdx+rcx*1-0x8], rsi
        sub     rdx, rdi
        mov     rsi, r13
        lea     ecx, [rbx+rdx*1]
        sub     rsi, rdx
        shr     ecx, 0x3
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        jmp     L3b4e
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L3c38:
        mov     rcx, QWORD PTR [rbp-0x500]
        lea     rdi, [rdx+0x8]
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rdx], rcx
        mov     ecx, ebx
        mov     rsi, QWORD PTR [r14+rcx*1-0x8]
        mov     QWORD PTR [rdx+rcx*1-0x8], rsi
        sub     rdx, rdi
        mov     rsi, r14
        lea     ecx, [rbx+rdx*1]
        sub     rsi, rdx
        shr     ecx, 0x3
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        jmp     L3b19
L3c6d:
        movzx   edx, WORD PTR [r12+rcx*1-0x2]
        mov     WORD PTR [rsi+rcx*1-0x2], dx
        pop     rax
        pop     rdx
        jmp     L39e1
L3c7f:
        mov     edx, DWORD PTR [rbp-0x3e0]
        mov     DWORD PTR [rsi], edx
        mov     edx, DWORD PTR [r12+rcx*1-0x4]
        mov     DWORD PTR [rsi+rcx*1-0x4], edx
        pop     rax
        pop     rdx
        jmp     L39e1
L3c97:
        mov     esi, DWORD PTR [rbp-0x470]
        mov     DWORD PTR [rdx], esi
        mov     esi, DWORD PTR [r13+rcx*1-0x4]
        mov     DWORD PTR [rdx+rcx*1-0x4], esi
        jmp     L3b4e
L3cad:
        mov     esi, DWORD PTR [rbp-0x500]
        mov     DWORD PTR [rdx], esi
        mov     esi, DWORD PTR [r14+rcx*1-0x4]
        mov     DWORD PTR [rdx+rcx*1-0x4], esi
        jmp     L3b19
L3cc3:
        mov     esi, DWORD PTR [rbp-0x590]
        mov     DWORD PTR [rdx], esi
        mov     esi, DWORD PTR [r15+rcx*1-0x4]
        mov     DWORD PTR [rdx+rcx*1-0x4], esi
        jmp     L3ae4
L3cd9:
        movzx   esi, WORD PTR [r15+rcx*1-0x2]
        mov     WORD PTR [rdx+rcx*1-0x2], si
        jmp     L3ae4
L3ce9:
        movzx   esi, WORD PTR [r13+rcx*1-0x2]
        mov     WORD PTR [rdx+rcx*1-0x2], si
        jmp     L3b4e
L3cf9:
        movzx   esi, WORD PTR [r14+rcx*1-0x2]
        mov     WORD PTR [rdx+rcx*1-0x2], si
        jmp     L3b19
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_keccakf1600_extract_bytes (0x3d10)

L3d10:
        mov     edx, edx
        test    ecx, ecx
        je      L3d30
        mov     ecx, ecx
        xor     eax, eax
        add     rdi, rdx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L3d20:
        movzx   edx, BYTE PTR [rdi+rax*1]
        mov     BYTE PTR [rsi+rax*1], dl
        add     rax, 0x1
        cmp     rcx, rax
        jne     L3d20
L3d30:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem_keccakf1600_xor_bytes (0x3d40)

L3d40:
        mov     edx, edx
        test    ecx, ecx
        je      L3d62
        mov     ecx, ecx
        add     rdi, rdx
        lea     rdx, [rsi+rcx*1]
        // nop
        .byte   0x90
L3d50:
        movzx   eax, BYTE PTR [rsi]
        add     rsi, 0x1
        xor     BYTE PTR [rdi], al
        add     rdi, 0x1
        cmp     rsi, rdx
        jne     L3d50
L3d62:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_keccakf1600x4_extract_bytes (0x3d70)

L3d70:
        push    r15
        mov     r15, rdx
        mov     edx, r9d
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, r8
        push    r12
        push    rbp
        mov     ebp, r9d
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rsp+0x40]
        mov     ecx, r12d
        call    L3d10
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L3d10
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L3d10
        add     rsp, 0x8
        mov     ecx, r12d
        mov     edx, ebp
        lea     rdi, [rbx+0x258]
        mov     rsi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        jmp     L3d10
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_keccakf1600x4_xor_bytes (0x3df0)

L3df0:
        push    r15
        mov     r15, rdx
        mov     edx, r9d
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, r8
        push    r12
        push    rbp
        mov     ebp, r9d
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rsp+0x40]
        mov     ecx, r12d
        call    L3d40
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L3d40
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L3d40
        add     rsp, 0x8
        mov     ecx, r12d
        mov     edx, ebp
        lea     rdi, [rbx+0x258]
        mov     rsi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        jmp     L3d40
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_keccakf1600_permute (0x3e70)

L3e70:
        push    r15
        mov     rax, rdi
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        sub     rsp, 0x58
        mov     rdx, QWORD PTR [rdi+0x8]
        mov     r13, QWORD PTR [rdi+0x18]
        mov     r15, QWORD PTR [rdi]
        mov     r12, QWORD PTR [rdi+0x60]
        mov     QWORD PTR [rsp-0x70], rdx
        mov     rdx, QWORD PTR [rdi+0x10]
        mov     QWORD PTR [rsp-0x68], rdx
        mov     rdx, QWORD PTR [rdi+0x20]
        mov     QWORD PTR [rsp-0x60], rdx
        mov     rdx, QWORD PTR [rdi+0x28]
        mov     QWORD PTR [rsp-0x58], rdx
        mov     rdx, QWORD PTR [rdi+0x30]
        mov     QWORD PTR [rsp-0x50], rdx
        mov     rdx, QWORD PTR [rdi+0x38]
        mov     QWORD PTR [rsp-0x48], rdx
        mov     rdx, QWORD PTR [rdi+0x40]
        mov     QWORD PTR [rsp-0x40], rdx
        mov     rdx, QWORD PTR [rdi+0x48]
        mov     QWORD PTR [rsp-0x38], rdx
        mov     rdx, QWORD PTR [rdi+0x50]
        mov     QWORD PTR [rsp-0x30], rdx
        mov     rdx, QWORD PTR [rdi+0x58]
        mov     QWORD PTR [rsp-0x28], rdx
        mov     rdx, QWORD PTR [rdi+0x68]
        mov     QWORD PTR [rsp-0x20], rdx
        mov     rdx, QWORD PTR [rdi+0x70]
        mov     QWORD PTR [rsp+0x18], r13
        mov     r11, QWORD PTR [rax+0x90]
        mov     QWORD PTR [rsp-0x18], rdx
        mov     rdx, QWORD PTR [rdi+0x78]
        mov     QWORD PTR [rsp+0x50], rax
        mov     rdi, QWORD PTR [rdi+0x80]
        mov     QWORD PTR [rsp-0x10], rdx
        mov     rdx, QWORD PTR [rax+0x88]
        mov     r14, QWORD PTR [rax+0xa0]
        mov     r8, QWORD PTR [rax+0xb0]
        mov     QWORD PTR [rsp-0x8], rdx
        mov     rdx, QWORD PTR [rax+0x98]
        mov     rbx, QWORD PTR [rax+0xc0]
        mov     QWORD PTR [rsp], rdx
        mov     rdx, QWORD PTR [rax+0xa8]
        mov     QWORD PTR [rsp+0x8], rdx
        mov     rdx, QWORD PTR [rax+0xb8]
        mov     QWORD PTR [rsp+0x10], rdx
        lea     rdx, [rip+L80c0]
        mov     QWORD PTR [rsp-0x78], rdx
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L3f70:
        mov     rcx, QWORD PTR [rsp-0x58]
        mov     rax, QWORD PTR [rsp-0x30]
        mov     rsi, QWORD PTR [rsp-0x10]
        mov     r13, QWORD PTR [rsp-0x70]
        xor     rcx, r15
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     rbp, QWORD PTR [rsp+0x8]
        xor     rcx, rax
        mov     r9, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp-0x68]
        xor     rcx, rsi
        mov     rsi, QWORD PTR [rsp-0x50]
        mov     rax, QWORD PTR [rsp-0x8]
        xor     rcx, r14
        xor     r13, rsi
        mov     rsi, QWORD PTR [rsp-0x20]
        xor     r13, rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        xor     r13, rdi
        xor     r13, rbp
        xor     r9, rdx
        mov     rbp, QWORD PTR [rsp-0x48]
        mov     rdx, QWORD PTR [rsp+0x10]
        xor     r9, rsi
        xor     r10, rbp
        xor     r9, r11
        mov     rbp, QWORD PTR [rsp-0x38]
        xor     r9, rdx
        xor     r10, r12
        mov     rdx, QWORD PTR [rsp-0x60]
        xor     r10, rax
        mov     rax, QWORD PTR [rsp-0x18]
        xor     rdx, rbp
        mov     rbp, r13
        xor     r10, r8
        xor     rdx, rax
        mov     rax, QWORD PTR [rsp]
        rol     rbp, 1
        mov     rsi, r10
        rol     rsi, 1
        xor     rdx, rax
        xor     rsi, rcx
        mov     rax, r9
        rol     rcx, 1
        xor     rdx, rbx
        rol     rax, 1
        xor     rcx, r9
        xor     rbp, rdx
        rol     rdx, 1
        xor     rax, r13
        xor     rdx, r10
        mov     r10, QWORD PTR [rsp-0x50]
        xor     r15, rbp
        mov     r9, r15
        xor     r10, rsi
        ror     r10, 0x14
        xor     r12, rax
        xor     r11, rdx
        xor     rbx, rcx
        mov     r15, r10
        ror     r12, 0x15
        xor     rdi, rsi
        xor     r8, rax
        rol     r11, 0x15
        not     r15
        rol     rbx, 0xe
        ror     rdi, 0x13
        mov     r13, r15
        mov     r15, QWORD PTR [rsp-0x78]
        ror     r8, 0x3
        and     r13, r12
        mov     QWORD PTR [rsp-0x50], r13
        mov     r13, QWORD PTR [r15]
        xor     r13, r9
        mov     r15, r13
        mov     r13, QWORD PTR [rsp-0x50]
        xor     r15, r13
        mov     r13, r12
        not     r13
        and     r13, r11
        xor     r13, r10
        mov     QWORD PTR [rsp+0x20], r13
        mov     r13, r11
        not     r13
        and     r13, rbx
        xor     r13, r12
        mov     r12, rbx
        not     r12
        mov     QWORD PTR [rsp+0x28], r13
        and     r12, r9
        not     r9
        and     r9, r10
        xor     r12, r11
        mov     r11, QWORD PTR [rsp-0x30]
        mov     r10, r9
        mov     r9, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rsp-0x50], r12
        mov     r12, rdi
        xor     r10, rbx
        xor     r11, rbp
        not     r12
        mov     QWORD PTR [rsp+0x30], r10
        mov     r10, QWORD PTR [rsp-0x38]
        rol     r11, 0x3
        xor     r9, rdx
        rol     r9, 0x1c
        xor     r10, rcx
        rol     r10, 0x14
        mov     rbx, r10
        not     rbx
        and     rbx, r11
        xor     rbx, r9
        mov     QWORD PTR [rsp+0x38], rbx
        mov     rbx, r11
        not     rbx
        and     rbx, rdi
        xor     rbx, r10
        mov     QWORD PTR [rsp+0x18], rbx
        mov     rbx, r12
        and     rbx, r8
        xor     r14, rbp
        mov     r12, rbx
        rol     r14, 0x12
        xor     r12, r11
        mov     r11, r8
        not     r11
        mov     QWORD PTR [rsp-0x30], r12
        mov     rbx, QWORD PTR [rsp-0x58]
        and     r11, r9
        not     r9
        and     r9, r10
        xor     r11, rdi
        mov     rdi, QWORD PTR [rsp-0x70]
        xor     rbx, rbp
        xor     r9, r8
        mov     r8, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp+0x40], r11
        ror     rbx, 0x1c
        mov     r11, QWORD PTR [rsp-0x20]
        xor     rdi, rsi
        mov     QWORD PTR [rsp-0x38], r9
        xor     r8, rax
        mov     r9, QWORD PTR [rsp]
        rol     rdi, 1
        rol     r8, 0x6
        xor     r11, rdx
        mov     r10, r8
        rol     r11, 0x19
        xor     r9, rcx
        not     r10
        mov     r13, r11
        rol     r9, 0x8
        and     r10, r11
        not     r13
        xor     r10, rdi
        mov     QWORD PTR [rsp-0x48], r10
        mov     r10, r13
        mov     r13, r9
        and     r10, r9
        not     r13
        xor     r10, r8
        mov     QWORD PTR [rsp], r10
        mov     r10, r13
        and     r10, r14
        xor     r10, r11
        mov     r11, r14
        not     r11
        and     r11, rdi
        not     rdi
        and     rdi, r8
        xor     r11, r9
        mov     r8, QWORD PTR [rsp-0x60]
        mov     r9, QWORD PTR [rsp-0x28]
        xor     rdi, r14
        mov     QWORD PTR [rsp-0x20], r11
        mov     r14, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rsp+0x48], rdi
        mov     rdi, QWORD PTR [rsp-0x8]
        xor     r8, rcx
        xor     r9, rsi
        rol     r9, 0xa
        rol     r8, 0x1b
        xor     rdi, rax
        xor     rax, r14
        mov     r14, QWORD PTR [rsp-0x40]
        mov     r12, rdi
        mov     rdi, QWORD PTR [rsp+0x10]
        ror     rax, 0x2
        rol     r12, 0xf
        xor     rdi, rdx
        mov     r13, r12
        xor     rdx, r14
        mov     r14, QWORD PTR [rsp-0x18]
        mov     r11, rdi
        mov     rdi, rbx
        not     r13
        ror     rdx, 0x9
        not     rdi
        ror     r11, 0x8
        xor     rcx, r14
        and     rdi, r9
        and     r13, r11
        ror     rcx, 0x19
        xor     rdi, r8
        xor     r13, r9
        mov     QWORD PTR [rsp+0x10], rdi
        mov     rdi, r9
        mov     r9, r11
        not     r9
        not     rdi
        and     r9, r8
        not     r8
        and     rdi, r12
        and     r8, rbx
        xor     rdi, rbx
        xor     r9, r12
        mov     r12, QWORD PTR [rsp+0x20]
        xor     r8, r11
        mov     r11, rcx
        mov     rcx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rsp-0x28], r8
        xor     rbp, rcx
        mov     rcx, QWORD PTR [rsp+0x8]
        ror     rbp, 0x17
        xor     rsi, rcx
        mov     rcx, rdx
        rol     rsi, 0x2
        not     rcx
        mov     r8, rsi
        mov     rsi, r11
        and     rcx, r11
        not     rsi
        mov     r14, r8
        xor     rcx, rax
        and     rsi, rbp
        not     r14
        mov     QWORD PTR [rsp-0x18], rcx
        xor     rsi, rdx
        mov     rbx, rsi
        mov     rsi, rbp
        not     rsi
        mov     QWORD PTR [rsp+0x8], rbx
        and     rsi, r8
        xor     rsi, r11
        mov     r11, r14
        and     r11, rax
        not     rax
        mov     r14, r11
        xor     r14, rbp
        and     rax, rdx
        mov     rbp, QWORD PTR [rsp+0x10]
        mov     rdx, QWORD PTR [rsp]
        xor     rax, r8
        mov     r8, QWORD PTR [rsp+0x38]
        mov     QWORD PTR [rsp-0x10], r14
        mov     r14, QWORD PTR [rsp-0x48]
        xor     r8, r15
        xor     r8, r14
        xor     r8, rbp
        mov     rbp, QWORD PTR [rsp+0x28]
        xor     r8, rcx
        mov     rcx, QWORD PTR [rsp+0x18]
        xor     r12, rcx
        xor     r12, rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     r11, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rsp-0x8], r13
        xor     r12, rdi
        mov     r14, QWORD PTR [rsp-0x10]
        xor     rbp, rdx
        xor     r12, rbx
        mov     rbx, QWORD PTR [rsp+0x40]
        mov     rdx, QWORD PTR [rsp-0x38]
        xor     rbp, r10
        xor     rbp, r13
        mov     r13, QWORD PTR [rsp-0x20]
        xor     r11, rbx
        mov     rbx, QWORD PTR [rsp+0x48]
        xor     rbp, rsi
        xor     r11, r13
        xor     rdx, rbx
        mov     rbx, QWORD PTR [rsp+0x30]
        mov     r13, rbp
        xor     r11, r9
        rol     r13, 1
        xor     r11, r14
        mov     r14, QWORD PTR [rsp-0x28]
        xor     rdx, rbx
        xor     r13, r8
        mov     rbx, r11
        rol     r8, 1
        xor     rdx, r14
        mov     r14, r12
        rol     rbx, 1
        xor     r8, r11
        xor     rdx, rax
        rol     r14, 1
        xor     rbx, r12
        xor     r14, rdx
        rol     rdx, 1
        xor     rdx, rbp
        mov     rbp, rcx
        xor     r15, r14
        xor     r10, rbx
        xor     rbp, r13
        mov     r11, r15
        ror     r10, 0x15
        xor     r9, rdx
        ror     rbp, 0x14
        rol     r9, 0x15
        xor     rax, r8
        xor     rdi, r13
        rol     rax, 0xe
        mov     r15, rbp
        ror     rdi, 0x13
        xor     rsi, rbx
        not     r15
        ror     rsi, 0x3
        mov     r12, r15
        mov     r15, QWORD PTR [rsp-0x78]
        and     r12, r10
        mov     rcx, QWORD PTR [r15+0x8]
        xor     rcx, r11
        mov     r15, rcx
        mov     rcx, QWORD PTR [rsp-0x18]
        xor     r15, r12
        mov     r12, r10
        not     r12
        and     r12, r9
        xor     r12, rbp
        mov     QWORD PTR [rsp-0x70], r12
        mov     r12, r9
        not     r12
        and     r12, rax
        xor     r12, r10
        mov     r10, rax
        not     r10
        mov     QWORD PTR [rsp-0x68], r12
        mov     r12, QWORD PTR [rsp+0x20]
        and     r10, r11
        not     r11
        and     r11, rbp
        xor     r10, r9
        mov     r9, QWORD PTR [rsp-0x38]
        xor     r11, rax
        mov     QWORD PTR [rsp+0x18], r10
        mov     r10, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp-0x60], r11
        mov     r11, QWORD PTR [rsp-0x50]
        xor     r9, r8
        rol     r9, 0x14
        xor     r10, r14
        xor     r11, rdx
        rol     r10, 0x3
        mov     rax, r11
        mov     r11, r9
        not     r11
        rol     rax, 0x1c
        and     r11, r10
        xor     r11, rax
        mov     QWORD PTR [rsp-0x58], r11
        mov     r11, r10
        not     r11
        and     r11, rdi
        xor     r12, r13
        xor     rcx, r14
        xor     r11, r9
        rol     rcx, 0x12
        mov     QWORD PTR [rsp-0x50], r11
        mov     r11, rdi
        not     r11
        and     r11, rsi
        xor     r11, r10
        mov     r10, rsi
        not     r10
        mov     QWORD PTR [rsp-0x48], r11
        and     r10, rax
        not     rax
        xor     r10, rdi
        and     rax, r9
        mov     rdi, QWORD PTR [rsp-0x20]
        mov     r11, rax
        mov     QWORD PTR [rsp-0x40], r10
        mov     rax, r12
        xor     r11, rsi
        xor     rdi, rdx
        mov     rsi, QWORD PTR [rsp-0x30]
        rol     rax, 1
        mov     r9, rdi
        mov     rdi, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rsp-0x38], r11
        xor     rsi, rbx
        rol     r9, 0x19
        rol     rsi, 0x6
        xor     rdi, r8
        rol     rdi, 0x8
        mov     r10, rsi
        mov     r12, rdi
        not     r10
        and     r10, r9
        not     r12
        xor     r10, rax
        and     r12, rcx
        mov     QWORD PTR [rsp-0x30], r10
        xor     r12, r9
        mov     r10, r9
        mov     r9, rcx
        not     r9
        not     r10
        and     r9, rax
        not     rax
        and     r10, rdi
        and     rax, rsi
        xor     r9, rdi
        xor     r10, rsi
        mov     rdi, rax
        mov     QWORD PTR [rsp-0x28], r10
        xor     rdi, rcx
        mov     QWORD PTR [rsp-0x20], r9
        mov     QWORD PTR [rsp-0x18], rdi
        mov     rax, QWORD PTR [rsp+0x30]
        mov     rsi, QWORD PTR [rsp+0x38]
        mov     r9, QWORD PTR [rsp]
        mov     r10, QWORD PTR [rsp-0x8]
        xor     rax, r8
        mov     rcx, QWORD PTR [rsp-0x10]
        xor     rsi, r14
        rol     rax, 0x1b
        mov     rbp, QWORD PTR [rsp+0x28]
        ror     rsi, 0x1c
        xor     r9, r13
        xor     r10, rbx
        xor     rcx, rdx
        rol     r10, 0xf
        ror     rcx, 0x8
        mov     rdi, rsi
        xor     rbx, rbp
        rol     r9, 0xa
        mov     r11, r10
        not     rdi
        ror     rbx, 0x2
        not     r11
        and     rdi, r9
        and     r11, rcx
        xor     rdi, rax
        xor     r11, r9
        mov     QWORD PTR [rsp-0x10], rdi
        mov     rdi, r9
        mov     QWORD PTR [rsp-0x8], r11
        mov     r11, rcx
        not     rdi
        not     r11
        and     rdi, r10
        and     r11, rax
        not     rax
        xor     rdi, rsi
        and     rax, rsi
        mov     rsi, QWORD PTR [rsp+0x8]
        xor     r11, r10
        mov     r9, rax
        mov     rax, QWORD PTR [rsp+0x40]
        xor     r9, rcx
        mov     rcx, QWORD PTR [rsp+0x48]
        xor     rsi, r13
        xor     rax, rdx
        mov     rdx, QWORD PTR [rsp+0x10]
        rol     rsi, 0x2
        mov     QWORD PTR [rsp], r9
        xor     rcx, r8
        ror     rax, 0x9
        ror     rcx, 0x19
        xor     rdx, r14
        mov     r14, rax
        mov     r8, rcx
        ror     rdx, 0x17
        not     r14
        not     r8
        and     r14, rcx
        and     r8, rdx
        xor     r14, rbx
        xor     r8, rax
        mov     QWORD PTR [rsp+0x8], r8
        mov     r8, rdx
        not     r8
        and     r8, rsi
        xor     r8, rcx
        mov     rcx, rsi
        not     rcx
        and     rcx, rbx
        not     rbx
        add     QWORD PTR [rsp-0x78], 0x10
        and     rbx, rax
        mov     rax, QWORD PTR [rsp-0x78]
        xor     rcx, rdx
        lea     rdx, [rip+L8180]
        mov     QWORD PTR [rsp+0x10], rcx
        xor     rbx, rsi
        cmp     rdx, rax
        jne     L3f70
        mov     rax, QWORD PTR [rsp+0x50]
        mov     rdx, QWORD PTR [rsp-0x70]
        mov     r13, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rax+0x8], rdx
        mov     rdx, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rax], r15
        mov     QWORD PTR [rax+0x10], rdx
        mov     rdx, QWORD PTR [rsp-0x60]
        mov     QWORD PTR [rax+0x18], r13
        mov     QWORD PTR [rax+0x20], rdx
        mov     rdx, QWORD PTR [rsp-0x58]
        mov     QWORD PTR [rax+0x60], r12
        mov     QWORD PTR [rax+0x28], rdx
        mov     rdx, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rax+0x80], rdi
        mov     QWORD PTR [rax+0x30], rdx
        mov     rdx, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rax+0x38], rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        mov     QWORD PTR [rax+0x40], rdx
        mov     rdx, QWORD PTR [rsp-0x38]
        mov     QWORD PTR [rax+0x48], rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     QWORD PTR [rax+0x50], rdx
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rax+0x58], rdx
        mov     rdx, QWORD PTR [rsp-0x20]
        mov     QWORD PTR [rax+0x68], rdx
        mov     rdx, QWORD PTR [rsp-0x18]
        mov     QWORD PTR [rax+0x70], rdx
        mov     rdx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rax+0x78], rdx
        mov     rdx, QWORD PTR [rsp-0x8]
        mov     QWORD PTR [rax+0x90], r11
        mov     QWORD PTR [rax+0x88], rdx
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     QWORD PTR [rax+0x98], r9
        mov     QWORD PTR [rax+0xa0], r14
        mov     QWORD PTR [rax+0xa8], rdx
        mov     QWORD PTR [rax+0xb0], r8
        mov     QWORD PTR [rax+0xb8], rcx
        mov     QWORD PTR [rax+0xc0], rbx
        add     rsp, 0x58
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_keccakf1600x4_permute (0x4740)

L4740:
        push    rbx
        mov     rbx, rdi
        call    L3e70
        lea     rdi, [rbx+0xc8]
        call    L3e70
        lea     rdi, [rbx+0x190]
        call    L3e70
        lea     rdi, [rbx+0x258]
        pop     rbx
        jmp     L3e70
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem512_gen_matrix (0x4770)

L4770:
        push    rbp
        mov     rbp, rsp
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     rbx, rsp
        lea     rcx, [rsp+0x100]
        mov     rax, rbx
L4797:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     rcx, rax
        jne     L4797
        cmp     edx, 0x1
        lea     rcx, [rdi+0x600]
        mov     r8, rbx
        mov     WORD PTR [rsp+0x20], 0x0
        sbb     eax, eax
        lea     rsi, [rdi+0x200]
        add     eax, 0x1
        cmp     edx, 0x1
        setb    dl
        mov     BYTE PTR [rsp+0x61], al
        mov     BYTE PTR [rsp+0xa0], al
        movzx   eax, WORD PTR [rip+L8180]
        mov     BYTE PTR [rsp+0x60], dl
        mov     BYTE PTR [rsp+0xa1], dl
        lea     rdx, [rdi+0x400]
        mov     WORD PTR [rsp+0xe0], ax
        call    L60e0
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rbp-0x8]
        leave
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem512_indcpa_keypair_derand (0x4820)

L4820:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0x1670]
        lea     r11, [rbp-0x16b0]
        push    r13
        lea     r15, [rbp-0x830]
        lea     r13, [rbp-0x1430]
        push    r12
        lea     r14, [rbp-0x1630]
        lea     r12, [rbp-0x1030]
        push    r10
        push    rbx
        mov     rbx, rax
        sub     rsp, 0x16a0
        movdqu  xmm1, XMMWORD PTR [rdx]
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     QWORD PTR [rbp-0x16b8], rdi
        mov     QWORD PTR [rbp-0x16c0], rsi
        mov     rdi, rax
        mov     rsi, r11
        mov     edx, 0x21
        mov     QWORD PTR [rbp-0x16d0], r11
        movaps  XMMWORD PTR [rbp-0x16b0], xmm1
        movaps  XMMWORD PTR [rbp-0x16a0], xmm2
        mov     BYTE PTR [rbp-0x1690], 0x2
        call    L3570
        xor     edx, edx
        mov     rsi, rbx
        mov     rdi, r15
        mov     QWORD PTR [rbp-0x16c8], rbx
        lea     rbx, [rbp-0xc30]
        call    L4770
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     rdx, r13
        push    0x3
        lea     r8, [rbp-0x1650]
        mov     rdi, rbx
        lea     rcx, [rbp-0x1230]
        push    0x2
        lea     rsi, [rbp-0xa30]
        push    0x1
        call    L5cd0
        add     rsp, 0x20
        mov     rdi, rbx
        call    L5b10
        mov     rdi, r13
        call    L5b10
        mov     rsi, rbx
        mov     rdi, r14
        call    L5c30
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, r15
        mov     rdi, r12
        call    L5b50
        mov     rcx, r14
        mov     rdx, rbx
        lea     rsi, [rbp-0x430]
        lea     rdi, [rbp-0xe30]
        call    L5b50
        mov     rdi, r12
        call    L5cb0
        mov     rsi, r13
        mov     rdi, r12
        call    L5c80
        mov     rdi, r12
        call    L5c60
        mov     rdi, rbx
        call    L5c60
        mov     rdi, QWORD PTR [rbp-0x16c0]
        mov     rsi, rbx
        call    L5ab0
        mov     rdi, QWORD PTR [rbp-0x16b8]
        mov     rsi, r12
        call    L5ab0
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x40
        mov     rdx, QWORD PTR [rbp-0x16b8]
        movdqa  xmm3, XMMWORD PTR [rbp-0x1670]
        rep stos QWORD PTR es:[rdi], rax
        movdqa  xmm4, XMMWORD PTR [rbp-0x1660]
        movups  XMMWORD PTR [rdx+0x300], xmm3
        movups  XMMWORD PTR [rdx+0x310], xmm4
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x100
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        mov     BYTE PTR [rbp-0x1690], 0x0
        mov     r11, QWORD PTR [rbp-0x16d0]
        movaps  XMMWORD PTR [rbp-0x16b0], xmm0
        movaps  XMMWORD PTR [rbp-0x16a0], xmm0
        mov     rax, QWORD PTR [rbp-0x16c8]
        movaps  XMMWORD PTR [rbp-0x1670], xmm0
        movaps  XMMWORD PTR [rbp-0x1660], xmm0
        movaps  XMMWORD PTR [rbp-0x1650], xmm0
        movaps  XMMWORD PTR [rbp-0x1640], xmm0
        lea     rsp, [rbp-0x30]
        xor     eax, eax
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem512_indcpa_enc (0x4a40)

L4a40:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x1430]
        lea     r14, [rbp-0x1a30]
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        mov     rbx, rsi
        mov     rsi, rdx
        sub     rsp, 0x2060
        mov     QWORD PTR [rbp-0x2068], rdi
        mov     rdi, r15
        call    L5ae0
        lea     r11, [rbp-0x1e30]
        mov     rsi, rbx
        movdqu  xmm1, XMMWORD PTR [r13+0x300]
        movdqu  xmm2, XMMWORD PTR [r13+0x310]
        mov     rdi, r11
        mov     QWORD PTR [rbp-0x2088], r11
        lea     rbx, [rbp-0x1830]
        movaps  XMMWORD PTR [rbp-0x2050], xmm1
        lea     r13, [rbp-0xc30]
        movaps  XMMWORD PTR [rbp-0x2040], xmm2
        call    L3210
        lea     rax, [rbp-0x830]
        mov     edx, 0x1
        lea     r10, [rbp-0x2050]
        mov     rsi, r10
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x2058], rax
        mov     QWORD PTR [rbp-0x2080], r10
        call    L4770
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     r8, r12
        push    0x3
        lea     rcx, [rbp-0xe30]
        mov     rdi, rbx
        lea     rdx, [rbp-0x1030]
        push    0x2
        lea     rsi, [rbp-0x1630]
        push    0x1
        mov     QWORD PTR [rbp-0x2060], rdx
        call    L5ed0
        lea     r8, [rbp-0x1c30]
        add     rsp, 0x20
        mov     rsi, r12
        mov     rdi, r8
        mov     edx, 0x4
        mov     QWORD PTR [rbp-0x2070], r8
        lea     r12, [rbp-0x2030]
        call    L5e50
        mov     rdi, rbx
        call    L5b10
        mov     rsi, rbx
        mov     rdi, r14
        call    L5c30
        mov     rcx, r14
        mov     rdx, rbx
        mov     rdi, r13
        mov     rsi, QWORD PTR [rbp-0x2058]
        call    L5b50
        lea     rsi, [rbp-0x430]
        mov     rcx, r14
        mov     rdx, rbx
        lea     rdi, [rbp-0xa30]
        call    L5b50
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, r15
        mov     rdi, r12
        call    L5b50
        mov     rdi, r13
        call    L5b30
        mov     rdi, r12
        call    L5860
        mov     rsi, QWORD PTR [rbp-0x2060]
        mov     rdi, r13
        call    L5c80
        mov     r8, QWORD PTR [rbp-0x2070]
        mov     rdi, r12
        mov     rsi, r8
        mov     QWORD PTR [rbp-0x2078], r8
        call    L56b0
        mov     r11, QWORD PTR [rbp-0x2088]
        mov     rdi, r12
        mov     rsi, r11
        mov     QWORD PTR [rbp-0x2070], r11
        call    L56b0
        mov     rdi, r13
        call    L5c60
        mov     rdi, r12
        call    L5660
        mov     rdi, QWORD PTR [rbp-0x2068]
        mov     rsi, r13
        call    L5a50
        mov     rdi, QWORD PTR [rbp-0x2068]
        mov     rsi, r12
        add     rdi, 0x280
        call    L2460
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x40
        rep stos QWORD PTR es:[rdi], rax
        mov     r8, QWORD PTR [rbp-0x2078]
        mov     ecx, 0x40
        mov     rdi, r8
        rep stos QWORD PTR es:[rdi], rax
        mov     r11, QWORD PTR [rbp-0x2070]
        mov     ecx, 0x40
        mov     rdi, r11
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2060]
        mov     ecx, 0x80
        mov     rdx, QWORD PTR [rbp-0x2060]
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2058]
        mov     ecx, 0x100
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2058]
        pxor    xmm0, xmm0
        mov     r10, QWORD PTR [rbp-0x2080]
        movaps  XMMWORD PTR [rbp-0x2050], xmm0
        movaps  XMMWORD PTR [rbp-0x2040], xmm0
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlkem512_indcpa_dec (0x4cf0)

L4cf0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xe20
        lea     rbx, [rsp+0x620]
        mov     QWORD PTR [rsp+0x18], rdi
        lea     r15, [rsp+0xa20]
        mov     rdi, rbx
        lea     r14, [rsp+0x420]
        call    L5a80
        lea     rsi, [r12+0x280]
        lea     r12, [rsp+0x20]
        mov     rdi, r12
        call    L2740
        mov     rsi, r13
        mov     rdi, r15
        lea     r13, [rsp+0x220]
        call    L5ae0
        mov     rdi, rbx
        call    L5b10
        mov     rsi, rbx
        mov     rdi, r14
        call    L5c30
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, r15
        mov     rdi, r13
        call    L5b50
        mov     rdi, r13
        call    L5860
        mov     rsi, r13
        mov     rdi, r12
        call    L56e0
        mov     rdi, r12
        call    L5660
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     rsi, r12
        call    L3260
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x40
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem512_check_pk (0x4df0)

L4df0:
        push    rbp
        mov     rsi, rdi
        mov     rbp, rsp
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x700
        lea     rbx, [rsp+0x300]
        mov     r12, rsp
        mov     rdi, rbx
        call    L5ae0
        mov     rdi, rbx
        call    L5c60
        mov     rsi, rbx
        mov     rdi, r12
        call    L5ab0
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L4e40:
        movdqu  xmm1, XMMWORD PTR [r13+rax*1+0x0]
        pxor    xmm1, XMMWORD PTR [r12+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x300
        jne     L4e40
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x8
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        mov     rdi, r12
        mov     ecx, 0x60
        sete    dl
        xor     eax, eax
        rep stos QWORD PTR es:[rdi], rax
        movzx   edx, dl
        lea     edx, [rdx*4-0x4]
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x18]
        mov     eax, edx
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem512_check_sk (0x4f10)

L4f10:
        push    rbp
        lea     rsi, [rdi+0x300]
        mov     edx, 0x320
        mov     rbp, rsp
        push    r12
        push    rbx
        mov     rbx, rdi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     r12, rsp
        mov     rdi, r12
        call    L3510
        movdqu  xmm1, XMMWORD PTR [rbx+0x620]
        movdqu  xmm2, XMMWORD PTR [rbx+0x630]
        pxor    xmm1, XMMWORD PTR [rsp]
        pxor    xmm2, XMMWORD PTR [rsp+0x10]
        movdqa  xmm0, xmm1
        pxor    xmm1, xmm2
        por     xmm0, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        pxor    xmm0, xmm0
        sete    al
        movaps  XMMWORD PTR [rsp], xmm0
        movzx   eax, al
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     eax, [rax+rax*4-0x5]
        lea     rsp, [rbp-0x10]
        pop     rbx
        pop     r12
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem512_keypair_derand (0x5000)

L5000:
        push    r13
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsp, 0x8
        call    L4820
        mov     r13d, eax
        test    eax, eax
        jne     L50a8
        mov     rax, QWORD PTR [rbp+0x0]
        lea     rdi, [rbx+0x308]
        lea     rcx, [rbx+0x300]
        mov     rsi, rbp
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rbx+0x300], rax
        sub     rcx, rdi
        mov     rdx, QWORD PTR [rbp+0x318]
        lea     rax, [rbx+0x620]
        sub     rsi, rcx
        add     ecx, 0x320
        mov     QWORD PTR [rbx+0x618], rdx
        shr     ecx, 0x3
        mov     edx, 0x320
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbp
        mov     rdi, rax
        call    L3510
        movdqu  xmm0, XMMWORD PTR [r12+0x20]
        mov     eax, r13d
        movups  XMMWORD PTR [rbx+0x640], xmm0
        movdqu  xmm1, XMMWORD PTR [r12+0x30]
        movups  XMMWORD PTR [rbx+0x650], xmm1
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L50a8:
        lea     rdi, [rbp+0x8]
        mov     rcx, rbp
        xor     eax, eax
        mov     QWORD PTR [rbp+0x0], 0x0
        mov     QWORD PTR [rbp+0x318], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x658], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x660
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0x8
        mov     eax, r13d
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem512_keypair (0x5120)

L5120:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x40
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x40
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L5180
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L5000
L5159:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5180:
        mov     eax, 0xfffffffd
        jmp     L5159
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_enc_derand (0x5190)

L5190:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        push    r13
        mov     r13, rsi
        push    r12
        mov     r12, rdi
        mov     rdi, rdx
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        add     rsp, 0xffffffffffffff80
        call    L4df0
        mov     r14, rsp
        test    eax, eax
        je      L5200
        lea     r15, [rsp+0x40]
L51c5:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90
L5200:
        movdqu  xmm1, XMMWORD PTR [r15]
        movdqu  xmm2, XMMWORD PTR [r15+0x10]
        lea     rdi, [rsp+0x20]
        mov     rsi, rbx
        mov     edx, 0x320
        lea     r15, [rsp+0x40]
        movaps  XMMWORD PTR [rsp], xmm1
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        call    L3510
        mov     edx, 0x40
        mov     rsi, r14
        mov     rdi, r15
        call    L3570
        lea     rcx, [rsp+0x60]
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r12
        call    L4a40
        test    eax, eax
        jne     L51c5
        movdqa  xmm3, XMMWORD PTR [rsp+0x40]
        movdqa  xmm4, XMMWORD PTR [rsp+0x50]
        movups  XMMWORD PTR [r13+0x0], xmm3
        movups  XMMWORD PTR [r13+0x10], xmm4
        jmp     L51c5
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem512_enc (0x5280)

L5280:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L52e0
        mov     rcx, rbx
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, r12
        call    L5190
L52c1:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L52e0:
        mov     eax, 0xfffffffd
        jmp     L52c1
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_dec (0x52f0)

L52f0:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        push    r14
        mov     r14, rdi
        mov     rdi, rdx
        push    r13
        mov     r13, rdx
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x3c0
        call    L4f10
        test    eax, eax
        je      L5388
        mov     ebx, eax
        lea     r10, [rsp+0x20]
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
L5331:
        xor     eax, eax
        mov     rdi, r8
        mov     ecx, 0x64
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, ebx
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L5388:
        lea     r10, [rsp+0x20]
        mov     rdx, r13
        mov     rsi, r15
        mov     rdi, r10
        mov     QWORD PTR [rsp+0x18], r10
        call    L4cf0
        mov     r10, QWORD PTR [rsp+0x18]
        test    eax, eax
        mov     ebx, eax
        je      L53c0
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
        jmp     L5331
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L53c0:
        lea     r9, [rsp+0x60]
        mov     rsi, r10
        mov     edx, 0x40
        mov     QWORD PTR [rsp+0x18], r10
        movdqu  xmm3, XMMWORD PTR [r13+0x620]
        mov     rdi, r9
        mov     QWORD PTR [rsp+0x8], r9
        movdqu  xmm4, XMMWORD PTR [r13+0x630]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        call    L3570
        mov     r10, QWORD PTR [rsp+0x18]
        lea     r8, [rsp+0xa0]
        lea     rcx, [rsp+0x80]
        mov     rdi, r8
        lea     rdx, [r13+0x300]
        mov     QWORD PTR [rsp+0x18], r8
        mov     rsi, r10
        mov     QWORD PTR [rsp+0x10], r10
        call    L4a40
        mov     r8, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp+0x10]
        test    eax, eax
        mov     r9, QWORD PTR [rsp+0x8]
        mov     ebx, eax
        jne     L5331
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop
        .byte   0x90
L5450:
        movdqu  xmm1, XMMWORD PTR [r15+rax*1]
        pxor    xmm1, XMMWORD PTR [r8+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x300
        jne     L5450
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x8], r10
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x10], r9
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    eax, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    r12d, xmm0
        movzx   r12d, r12b
        neg     r12d
        sar     r12d, 0x10
        xor     r12d, eax
        xor     r12d, eax
        mov     rdx, r8
        mov     ecx, 0x60
        mov     rsi, r15
        movdqu  xmm6, XMMWORD PTR [r13+0x650]
        mov     QWORD PTR [rsp+0x18], r8
        movzx   r12d, r12b
        lea     rax, [rsp+0xc0]
        movdqu  xmm5, XMMWORD PTR [r13+0x640]
        mov     rdi, rax
        neg     r12d
        movaps  XMMWORD PTR [rsp+0xb0], xmm6
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     ecx, 0x320
        mov     esi, 0x20
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0xa0], xmm5
        call    L3480
        mov     r10, QWORD PTR [rsp+0x8]
        mov     r9, QWORD PTR [rsp+0x10]
        xor     eax, eax
        mov     r8, QWORD PTR [rsp+0x18]
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L5570:
        movzx   esi, BYTE PTR [r9+rax*1]
        mov     ecx, r12d
        movzx   edx, BYTE PTR [r14+rax*1]
        sar     ecx, 0x10
        xor     edx, esi
        and     edx, ecx
        xor     edx, esi
        mov     BYTE PTR [r14+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x20
        jne     L5570
        jmp     L5331
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_poly_tomont (0x55a0)

L55a0:
        movdqa  xmm5, XMMWORD PTR [rip+L8070]
        movdqa  xmm6, XMMWORD PTR [rip+L8080]
        lea     rax, [rdi+0x200]
        movdqa  xmm4, XMMWORD PTR [rip+L8090]
        // nop
        .byte   0x90
L55c0:
        movdqa  xmm3, XMMWORD PTR [rdi]
        movdqa  xmm0, xmm5
        pmulhw  xmm0, XMMWORD PTR [rdi]
        add     rdi, 0x10
        pmullw  xmm3, xmm5
        movdqa  xmm7, xmm3
        punpckhwd xmm3, xmm0
        punpcklwd xmm7, xmm0
        movdqa  xmm0, xmm7
        movdqa  xmm1, xmm7
        punpcklwd xmm0, xmm3
        punpckhwd xmm1, xmm3
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm2
        pmullw  xmm0, xmm6
        movdqa  xmm2, xmm0
        movdqa  xmm1, xmm0
        pmulhw  xmm1, xmm4
        pmullw  xmm2, xmm4
        movdqa  xmm0, xmm2
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm1
        movdqa  xmm1, xmm2
        paddd   xmm0, xmm7
        paddd   xmm1, xmm3
        psrad   xmm1, 0x10
        psrad   xmm0, 0x10
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        movaps  XMMWORD PTR [rdi-0x10], xmm0
        cmp     rax, rdi
        jne     L55c0
        ret

// mlkem_poly_reduce (0x5660)

L5660:
        mov     rcx, rdi
        lea     rsi, [rdi+0x200]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5670:
        movsx   edx, WORD PTR [rcx]
        mov     eax, edx
        imul    edx, edx, 0x4ebf
        add     edx, 0x2000000
        sar     edx, 0x1a
        imul    dx, dx, 0xf2ff
        add     edx, eax
        movsx   eax, dx
        shr     eax, 0x10
        neg     eax
        lea     edi, [rdx+0xd01]
        sar     eax, 0x10
        add     rcx, 0x2
        xor     edi, edx
        and     eax, edi
        xor     eax, edx
        mov     WORD PTR [rcx-0x2], ax
        cmp     rcx, rsi
        jne     L5670
        ret

// mlkem_poly_add (0x56b0)

L56b0:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L56b8:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        paddw   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x200
        jne     L56b8
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_poly_sub (0x56e0)

L56e0:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L56e8:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        psubw   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x200
        jne     L56e8
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mlkem_poly_mulcache_compute (0x5710)

L5710:
        xor     ecx, ecx
        lea     r8, [rip+L8220]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L5720:
        movsx   eax, WORD PTR [r8+rcx*1]
        movsx   r9d, WORD PTR [rsi+rcx*4+0x2]
        imul    r9d, eax
        mov     edx, eax
        neg     edx
        movsx   edx, dx
        imul    ax, r9w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r9d
        sar     eax, 0x10
        mov     WORD PTR [rdi+rcx*2], ax
        movsx   eax, WORD PTR [rsi+rcx*4+0x6]
        imul    edx, eax
        imul    ax, dx, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, edx
        sar     eax, 0x10
        mov     WORD PTR [rdi+rcx*2+0x2], ax
        add     rcx, 0x2
        cmp     rcx, 0x80
        jne     L5720
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_poly_ntt (0x5780)

L5780:
        push    r15
        mov     edx, 0x1
        mov     r15d, 0x100
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12d, 0x1
        push    rbp
        lea     rbp, [rdi+0x2]
        push    rbx
        lea     rbx, [rip+L81a0]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L57b0:
        lea     ecx, [rdx-0x1]
        mov     r8d, r12d
        mov     edi, r15d
        mov     DWORD PTR [rsp-0x4], edx
        shl     r8d, cl
        mov     ecx, edx
        shr     edi, cl
        xor     ecx, ecx
        lea     r11d, [rdi+rdi*1]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L57d0:
        mov     eax, r8d
        add     r8d, 0x1
        movsx   r9d, WORD PTR [rbx+rax*2]
        cmp     ecx, edi
        jae     L5834
        mov     esi, edi
        mov     eax, ecx
        sub     esi, ecx
        lea     rdx, [r13+rax*2+0x0]
        sub     esi, 0x1
        add     rsi, rax
        lea     r10, [rbp+rsi*2+0x0]
        mov     esi, edi
        sub     rsi, rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5800:
        movsx   r14d, WORD PTR [rdx+rsi*2]
        imul    r14d, r9d
        imul    ax, r14w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r14d
        movzx   r14d, WORD PTR [rdx]
        sar     eax, 0x10
        sub     r14d, eax
        mov     WORD PTR [rdx+rsi*2], r14w
        add     WORD PTR [rdx], ax
        add     rdx, 0x2
        cmp     r10, rdx
        jne     L5800
L5834:
        add     ecx, r11d
        add     edi, r11d
        cmp     ecx, 0xff
        jbe     L57d0
        mov     edx, DWORD PTR [rsp-0x4]
        add     edx, 0x1
        cmp     edx, 0x8
        jne     L57b0
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_poly_invntt_tomont (0x5860)

L5860:
        push    r15
        movdqa  xmm5, XMMWORD PTR [rip+L80a0]
        lea     rdx, [rdi+0x200]
        mov     rax, rdi
        push    r14
        movdqa  xmm6, XMMWORD PTR [rip+L8080]
        push    r13
        movdqa  xmm4, XMMWORD PTR [rip+L8090]
        push    r12
        mov     r12, rdi
        push    rbp
        push    rbx
        // nop
        .byte   0x90
L5890:
        movdqu  xmm3, XMMWORD PTR [rax]
        movdqu  xmm0, XMMWORD PTR [rax]
        add     rax, 0x10
        pmullw  xmm3, xmm5
        pmulhw  xmm0, xmm5
        movdqa  xmm7, xmm3
        punpckhwd xmm3, xmm0
        punpcklwd xmm7, xmm0
        movdqa  xmm0, xmm7
        movdqa  xmm1, xmm7
        punpcklwd xmm0, xmm3
        punpckhwd xmm1, xmm3
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm2
        pmullw  xmm0, xmm6
        movdqa  xmm2, xmm0
        movdqa  xmm1, xmm0
        pmulhw  xmm1, xmm4
        pmullw  xmm2, xmm4
        movdqa  xmm0, xmm2
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm1
        movdqa  xmm1, xmm2
        paddd   xmm0, xmm7
        paddd   xmm1, xmm3
        psrad   xmm1, 0x10
        psrad   xmm0, 0x10
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        movups  XMMWORD PTR [rax-0x10], xmm0
        cmp     rax, rdx
        jne     L5890
        mov     r9d, 0x65c
        mov     ecx, 0x7
        mov     r15d, 0x1
        lea     r14, [r12+0x2]
        lea     r13, [rip+L81a0]
        movsx   r8d, r9w
L5950:
        mov     edi, 0x100
        mov     r10d, r15d
        xor     esi, esi
        mov     r11d, ecx
        shr     edi, cl
        shl     r10d, cl
        sub     r10d, 0x1
        lea     ebx, [rdi+rdi*1]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L5970:
        sub     r10d, 0x1
        cmp     esi, edi
        jae     L59fd
        mov     eax, edi
        mov     r9d, esi
        mov     DWORD PTR [rsp-0xc], esi
        lea     rdx, [r12+rax*2]
        mov     eax, edi
        lea     rcx, [r12+r9*2]
        sub     eax, esi
        sub     eax, 0x1
        add     rax, r9
        lea     rbp, [r14+rax*2]
        mov     rsi, rbp
        // xchg    ax, ax
        .byte   0x66,0x90
L59a0:
        movzx   r9d, WORD PTR [rcx]
        movzx   ebp, WORD PTR [rdx]
        add     rcx, 0x2
        add     rdx, 0x2
        add     ebp, r9d
        movsx   eax, bp
        imul    eax, eax, 0x4ebf
        add     eax, 0x2000000
        sar     eax, 0x1a
        imul    ax, ax, 0xf2ff
        add     eax, ebp
        mov     WORD PTR [rcx-0x2], ax
        movzx   eax, WORD PTR [rdx-0x2]
        sub     eax, r9d
        movsx   r9d, ax
        imul    r9d, r8d
        imul    ax, r9w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r9d
        sar     eax, 0x10
        mov     WORD PTR [rdx-0x2], ax
        cmp     rcx, rsi
        jne     L59a0
        mov     esi, DWORD PTR [rsp-0xc]
L59fd:
        add     esi, ebx
        add     edi, ebx
        cmp     esi, 0xff
        ja      L5a20
        mov     eax, r10d
        movsx   r8d, WORD PTR [r13+rax*2+0x0]
        jmp     L5970
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L5a20:
        mov     ecx, r11d
        sub     ecx, 0x1
        je      L5a3b
        mov     eax, r15d
        shl     eax, cl
        sub     eax, 0x1
        movsx   r8d, WORD PTR [r13+rax*2+0x0]
        jmp     L5950
L5a3b:
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_polyvec_compress_du (0x5a50)

L5a50:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L2660
        add     rsp, 0x8
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x140]
        pop     rbx
        pop     rbp
        jmp     L2660
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_decompress_du (0x5a80)

L5a80:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L2790
        add     rsp, 0x8
        lea     rsi, [rbp+0x140]
        lea     rdi, [rbx+0x200]
        pop     rbx
        pop     rbp
        jmp     L2790
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_tobytes (0x5ab0)

L5ab0:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L3180
        add     rsp, 0x8
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x180]
        pop     rbx
        pop     rbp
        jmp     L3180
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_frombytes (0x5ae0)

L5ae0:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L31c0
        add     rsp, 0x8
        lea     rsi, [rbp+0x180]
        lea     rdi, [rbx+0x200]
        pop     rbx
        pop     rbp
        jmp     L31c0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_ntt (0x5b10)

L5b10:
        push    rbx
        mov     rbx, rdi
        call    L5780
        lea     rdi, [rbx+0x200]
        pop     rbx
        jmp     L5780
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_polyvec_invntt_tomont (0x5b30)

L5b30:
        push    rbx
        mov     rbx, rdi
        call    L5860
        lea     rdi, [rbx+0x200]
        pop     rbx
        jmp     L5860
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_polyvec_basemul_acc_montgomery_cached (0x5b50)

L5b50:
        push    r13
        mov     r8, rdx
        mov     r9, rcx
        xor     eax, eax
        push    r12
        push    rbp
        push    rbx
        // xchg    ax, ax
        .byte   0x66,0x90
L5b60:
        movsx   r11d, WORD PTR [r8+rax*4]
        movsx   r12d, WORD PTR [rsi+rax*4+0x2]
        movsx   r13d, WORD PTR [rsi+rax*4]
        movsx   ecx, WORD PTR [r9+rax*2]
        mov     edx, r11d
        imul    r11d, r12d
        movsx   r10d, WORD PTR [rsi+rax*4+0x202]
        movsx   ebp, WORD PTR [rsi+rax*4+0x200]
        movsx   ebx, WORD PTR [r8+rax*4+0x200]
        imul    edx, r13d
        imul    ecx, r12d
        add     ecx, edx
        movsx   edx, WORD PTR [r9+rax*2+0x100]
        imul    edx, r10d
        imul    r10d, ebx
        add     ecx, edx
        mov     edx, ebp
        imul    edx, ebx
        add     ecx, edx
        movsx   edx, WORD PTR [r8+rax*4+0x2]
        imul    edx, r13d
        add     edx, r11d
        movsx   r11d, WORD PTR [r8+rax*4+0x202]
        imul    r11d, ebp
        add     edx, r11d
        add     edx, r10d
        imul    r10w, cx, 0xf301
        movsx   r10d, r10w
        imul    r10d, r10d, 0xfffff2ff
        add     ecx, r10d
        sar     ecx, 0x10
        mov     WORD PTR [rdi+rax*4], cx
        imul    cx, dx, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     edx, ecx
        sar     edx, 0x10
        mov     WORD PTR [rdi+rax*4+0x2], dx
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L5b60
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem512_polyvec_mulcache_compute (0x5c30)

L5c30:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L5710
        add     rsp, 0x8
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x100]
        pop     rbx
        pop     rbp
        jmp     L5710
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_reduce (0x5c60)

L5c60:
        push    rbx
        mov     rbx, rdi
        call    L5660
        lea     rdi, [rbx+0x200]
        pop     rbx
        jmp     L5660
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_polyvec_add (0x5c80)

L5c80:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L56b0
        add     rsp, 0x8
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x200]
        pop     rbx
        pop     rbp
        jmp     L56b0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem512_polyvec_tomont (0x5cb0)

L5cb0:
        push    rbx
        mov     rbx, rdi
        call    L55a0
        lea     rdi, [rbx+0x200]
        pop     rbx
        jmp     L55a0
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem512_poly_getnoise_eta1_4x (0x5cd0)

L5cd0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x430]
        lea     r14, [rbp-0x1b0]
        push    r13
        lea     r13, [rbp-0xf0]
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        lea     rbx, [rbp-0x330]
        sub     rsp, 0x420
        mov     r11d, DWORD PTR [r10]
        mov     ecx, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x448], rdx
        movdqu  xmm1, XMMWORD PTR [r8]
        mov     edx, DWORD PTR [r10+0x10]
        mov     QWORD PTR [rbp-0x438], rdi
        lea     rdi, [rbp-0x3b0]
        movdqu  xmm0, XMMWORD PTR [r8+0x10]
        mov     QWORD PTR [rbp-0x440], rsi
        lea     r8, [rbp-0x370]
        lea     rsi, [rbp-0x3f0]
        mov     BYTE PTR [rbp-0x3d0], r11b
        lea     r10, [rbp-0x270]
        movaps  XMMWORD PTR [rbp-0x430], xmm1
        movaps  XMMWORD PTR [rbp-0x420], xmm0
        movaps  XMMWORD PTR [rbp-0x3f0], xmm1
        movaps  XMMWORD PTR [rbp-0x3e0], xmm0
        movaps  XMMWORD PTR [rbp-0x3b0], xmm1
        movaps  XMMWORD PTR [rbp-0x3a0], xmm0
        movaps  XMMWORD PTR [rbp-0x370], xmm1
        movaps  XMMWORD PTR [rbp-0x360], xmm0
        mov     BYTE PTR [rbp-0x410], r9b
        mov     r9, r15
        mov     BYTE PTR [rbp-0x390], cl
        mov     rcx, r13
        mov     BYTE PTR [rbp-0x350], dl
        mov     rdx, r14
        push    0x21
        push    r8
        mov     r8d, 0xc0
        push    rdi
        mov     rdi, rbx
        push    rsi
        mov     rsi, r10
        mov     QWORD PTR [rbp-0x450], r10
        call    L3870
        mov     rdi, QWORD PTR [rbp-0x438]
        add     rsp, 0x20
        mov     rsi, rbx
        call    L6420
        mov     rsi, QWORD PTR [rbp-0x450]
        mov     rdi, QWORD PTR [rbp-0x440]
        call    L6420
        mov     rdi, QWORD PTR [rbp-0x448]
        mov     rsi, r14
        call    L6420
        test    r12, r12
        je      L5e17
        mov     rsi, r13
        mov     rdi, r12
        call    L6420
L5e17:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x20
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mlkem512_poly_getnoise_eta2 (0x5e50)

L5e50:
        push    rbp
        mov     ecx, 0x21
        mov     rbp, rsp
        push    r13
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xc0
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm2, XMMWORD PTR [rsi+0x10]
        mov     esi, 0x80
        lea     rbx, [rsp+0x40]
        mov     r13, rsp
        mov     BYTE PTR [rsp+0x20], dl
        mov     rdi, rbx
        mov     rdx, r13
        movaps  XMMWORD PTR [rsp], xmm1
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        call    L3480
        mov     rdi, r12
        mov     rsi, rbx
        call    L63b0
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x10
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        mov     BYTE PTR [rsp+0x20], 0x0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem512_poly_getnoise_eta1122_4x (0x5ed0)

L5ed0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x270]
        lea     r14, [rbp-0x1b0]
        push    r13
        lea     r13, [rbp-0xf0]
        push    r12
        lea     r12, [rbp-0x430]
        push    r10
        push    rbx
        lea     rbx, [rbp-0x330]
        sub     rsp, 0x420
        mov     eax, DWORD PTR [r10+0x10]
        mov     r11d, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x448], rdx
        movdqu  xmm1, XMMWORD PTR [r8]
        mov     edx, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x438], rdi
        lea     rdi, [rbp-0x370]
        movdqu  xmm0, XMMWORD PTR [r8+0x10]
        mov     QWORD PTR [rbp-0x440], rsi
        lea     rsi, [rbp-0x3b0]
        mov     r8d, 0xc0
        mov     QWORD PTR [rbp-0x450], rcx
        lea     rcx, [rbp-0x3f0]
        mov     BYTE PTR [rbp-0x350], al
        mov     BYTE PTR [rbp-0x3d0], r11b
        movaps  XMMWORD PTR [rbp-0x430], xmm1
        movaps  XMMWORD PTR [rbp-0x420], xmm0
        movaps  XMMWORD PTR [rbp-0x3f0], xmm1
        movaps  XMMWORD PTR [rbp-0x3e0], xmm0
        movaps  XMMWORD PTR [rbp-0x3b0], xmm1
        movaps  XMMWORD PTR [rbp-0x3a0], xmm0
        movaps  XMMWORD PTR [rbp-0x370], xmm1
        movaps  XMMWORD PTR [rbp-0x360], xmm0
        mov     BYTE PTR [rbp-0x410], r9b
        mov     r9, r12
        mov     BYTE PTR [rbp-0x390], dl
        mov     rdx, r14
        push    0x21
        push    rdi
        mov     rdi, rbx
        push    rsi
        mov     rsi, r15
        push    rcx
        mov     rcx, r13
        call    L3870
        mov     rdi, QWORD PTR [rbp-0x438]
        add     rsp, 0x20
        mov     rsi, rbx
        call    L6420
        mov     rdi, QWORD PTR [rbp-0x440]
        mov     rsi, r15
        call    L6420
        mov     rdi, QWORD PTR [rbp-0x448]
        mov     rsi, r14
        call    L63b0
        mov     rdi, QWORD PTR [rbp-0x450]
        mov     rsi, r13
        call    L63b0
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x20
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlk_rej_uniform_c.constprop.0 (0x6040)

L6040:
        mov     r8, rdi
        mov     r9d, ecx
        cmp     esi, 0xff
        ja      L60d8
        mov     r10d, 0x3
        sub     r10d, edx
        jmp     L608d
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L6060:
        cmp     esi, 0xff
        ja      L6080
        mov     edi, esi
        cmp     ax, 0xd00
        jg      L6080
L6070:
        lea     esi, [rdi+0x1]
        mov     WORD PTR [r8+rdi*2], ax
        cmp     esi, 0x100
        je      L60d8
L6080:
        add     rdx, 0x3
        lea     eax, [r10+rdx*1]
        cmp     r9d, eax
        jb      L60d8
L608d:
        movzx   eax, BYTE PTR [rdx+0x1]
        movzx   edi, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        shl     ecx, 0x8
        movzx   eax, al
        or      ecx, edi
        movzx   edi, BYTE PTR [rdx+0x2]
        and     cx, 0xfff
        shl     edi, 0x4
        or      eax, edi
        cmp     cx, 0xd00
        jg      L6060
        lea     edi, [rsi+0x1]
        mov     esi, esi
        mov     WORD PTR [r8+rsi*2], cx
        cmp     edi, 0xff
        ja      L60ce
        cmp     ax, 0xd00
        jle     L6070
L60ce:
        mov     esi, edi
        cmp     esi, 0x100
        jne     L6080
L60d8:
        mov     eax, esi
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlkem_poly_rej_uniform_x4 (0x60e0)

L60e0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbx
        mov     rbx, r8
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xb60
        lea     r15, [rsp+0x40]
        mov     QWORD PTR [rsp+0x8], rdi
        lea     r14, [rsp+0x360]
        mov     rdi, r15
        mov     QWORD PTR [rsp], rsi
        mov     QWORD PTR [rsp+0x20], rdx
        mov     QWORD PTR [rsp+0x18], rcx
        mov     QWORD PTR [rsp+0x10], r15
        call    L3820
        lea     rdx, [rbx+0x40]
        mov     rsi, rbx
        mov     rdi, r15
        lea     rcx, [rbx+0x80]
        lea     r8, [rbx+0xc0]
        mov     rbx, r15
        mov     r9d, 0x22
        call    L3720
        lea     r15, [rsp+0x560]
        mov     r9, rbx
        mov     rdi, r14
        lea     rax, [rsp+0x960]
        lea     r11, [rsp+0x760]
        mov     r8d, 0x3
        mov     rsi, r15
        mov     rcx, rax
        mov     rdx, r11
        mov     rbx, r11
        mov     QWORD PTR [rsp+0x38], rax
        mov     QWORD PTR [rsp+0x30], r11
        call    L3780
        xor     esi, esi
        mov     rdi, r13
        mov     ecx, 0x1f8
        mov     rdx, r14
        call    L6040
        xor     esi, esi
        mov     rdi, r12
        mov     ecx, 0x1f8
        mov     rdx, r15
        mov     r13d, eax
        call    L6040
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     rdx, rbx
        xor     esi, esi
        mov     ecx, 0x1f8
        mov     r12d, eax
        call    L6040
        mov     rdx, QWORD PTR [rsp+0x38]
        mov     rdi, QWORD PTR [rsp+0x18]
        xor     esi, esi
        mov     ecx, 0x1f8
        mov     ebx, eax
        call    L6040
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L62a0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6208:
        mov     r9, QWORD PTR [rsp+0x10]
        mov     rcx, QWORD PTR [rsp+0x38]
        mov     rsi, r15
        mov     rdi, r14
        mov     rdx, QWORD PTR [rsp+0x30]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x2c], r10d
        call    L3780
        mov     rdi, QWORD PTR [rsp+0x8]
        mov     esi, r13d
        mov     rdx, r14
        mov     ecx, 0xa8
        call    L6040
        mov     rdi, QWORD PTR [rsp]
        mov     esi, r12d
        mov     rdx, r15
        mov     ecx, 0xa8
        mov     r13d, eax
        call    L6040
        mov     rdx, QWORD PTR [rsp+0x30]
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     esi, ebx
        mov     ecx, 0xa8
        mov     r12d, eax
        call    L6040
        mov     rdx, QWORD PTR [rsp+0x38]
        mov     esi, DWORD PTR [rsp+0x2c]
        mov     ecx, 0xa8
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     ebx, eax
        call    L6040
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L62a0:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L6208
        cmp     r10d, 0xff
        jbe     L6208
        mov     rdi, QWORD PTR [rsp+0x10]
        call    L3830
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x100
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem_poly_rej_uniform (0x62f0)

L62f0:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        mov     rbx, rsi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x2e0
        mov     r13, rsp
        lea     r12, [rsp+0xe0]
        mov     rdi, r13
        call    L3430
        mov     edx, 0x22
        mov     rsi, rbx
        mov     rdi, r13
        call    L33c0
        mov     rdx, r13
        mov     esi, 0x3
        mov     rdi, r12
        call    L33e0
        xor     esi, esi
        mov     ecx, 0x1f8
        mov     rdx, r12
        mov     rdi, r14
        call    L6040
        cmp     eax, 0xff
        ja      L638b
        mov     ebx, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6360:
        mov     rdx, r13
        mov     esi, 0x1
        mov     rdi, r12
        call    L33e0
        mov     esi, ebx
        mov     ecx, 0xa8
        mov     rdx, r12
        mov     rdi, r14
        call    L6040
        mov     ebx, eax
        cmp     eax, 0xff
        jbe     L6360
L638b:
        mov     rdi, r13
        call    L3440
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x3f
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem_poly_cbd2 (0x63b0)

L63b0:
        push    rbx
        mov     r8, rdi
        mov     r10, rsi
        xor     r9d, r9d
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L63c0:
        mov     edi, DWORD PTR [r10+r9*4]
        lea     esi, [r9*8+0x0]
        xor     edx, edx
        mov     eax, edi
        shr     edi, 1
        and     eax, 0x55555555
        and     edi, 0x55555555
        add     edi, eax
        // nop
        .byte   0x90
L63e0:
        mov     ecx, edx
        mov     eax, edi
        mov     ebx, edi
        mov     r11d, esi
        shr     eax, cl
        lea     ecx, [rdx+0x2]
        add     edx, 0x4
        add     esi, 0x1
        shr     ebx, cl
        and     eax, 0x3
        mov     ecx, ebx
        and     ecx, 0x3
        sub     eax, ecx
        mov     WORD PTR [r8+r11*2], ax
        cmp     edx, 0x20
        jne     L63e0
        add     r9, 0x1
        cmp     r9, 0x20
        jne     L63c0
        pop     rbx
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem_poly_cbd3 (0x6420)

L6420:
        push    rbx
        mov     r8, rdi
        xor     r9d, r9d
        mov     rdi, rsi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6430:
        movzx   eax, BYTE PTR [rdi+0x1]
        movzx   edx, BYTE PTR [rdi+0x2]
        mov     r10d, r9d
        movzx   ecx, BYTE PTR [rdi]
        shl     edx, 0x10
        shl     eax, 0x8
        or      eax, edx
        or      eax, ecx
        mov     esi, eax
        mov     edx, eax
        shr     eax, 0x2
        shr     esi, 1
        and     eax, 0x249249
        and     edx, 0x249249
        and     esi, 0x249249
        add     esi, eax
        add     esi, edx
        xor     edx, edx
L6468:
        mov     ecx, edx
        mov     eax, esi
        mov     ebx, esi
        mov     r11d, r10d
        shr     eax, cl
        lea     ecx, [rdx+0x3]
        add     edx, 0x6
        add     r10d, 0x1
        shr     ebx, cl
        and     eax, 0x7
        mov     ecx, ebx
        and     ecx, 0x7
        sub     eax, ecx
        mov     WORD PTR [r8+r11*2], ax
        cmp     edx, 0x18
        jne     L6468
        add     r9d, 0x4
        add     rdi, 0x3
        cmp     r9d, 0x100
        jne     L6430
        pop     rbx
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem768_gen_matrix (0x64b0)

L64b0:
        push    rbp
        mov     rbp, rsp
        push    r12
        push    rbx
        mov     rbx, rdi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     r12, rsp
        lea     rcx, [rsp+0x100]
        mov     rax, r12
L64dc:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     rax, rcx
        jne     L64dc
        mov     WORD PTR [rsp+0x20], 0x0
        test    edx, edx
        jne     L65e0
        mov     esi, 0x1
        mov     edi, 0x2
        mov     r8d, 0x100
        mov     WORD PTR [rsp+0x60], si
        lea     rdx, [rbx+0x400]
        lea     rsi, [rbx+0x200]
        mov     WORD PTR [rsp+0xa0], di
        lea     rcx, [rbx+0x600]
        mov     rdi, rbx
        mov     WORD PTR [rsp+0xe0], r8w
        mov     r8, r12
        call    L60e0
        mov     edi, 0x2
        xor     esi, esi
        mov     eax, 0x1
        mov     edx, 0x2
L6552:
        movzx   ecx, WORD PTR [rip+L8180]
        mov     BYTE PTR [rsp+0x60], dl
        mov     r8, r12
        mov     BYTE PTR [rsp+0xa1], dil
        lea     rdi, [rbx+0x800]
        mov     WORD PTR [rsp+0x20], cx
        lea     rcx, [rbx+0xe00]
        mov     BYTE PTR [rsp+0xa0], sil
        lea     rsi, [rbx+0xa00]
        mov     BYTE PTR [rsp+0xe1], dl
        lea     rdx, [rbx+0xc00]
        mov     BYTE PTR [rsp+0x61], al
        mov     BYTE PTR [rsp+0xe0], al
        call    L60e0
        movzx   eax, WORD PTR [rip+L8182]
        lea     rdi, [rbx+0x1000]
        mov     rsi, r12
        mov     WORD PTR [rsp+0x20], ax
        call    L62f0
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x10]
        pop     rbx
        pop     r12
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L65e0:
        mov     edx, 0x200
        mov     ecx, 0x1
        mov     rdi, rbx
        mov     r8, r12
        mov     eax, 0x100
        mov     WORD PTR [rsp+0xa0], dx
        lea     rsi, [rbx+0x200]
        lea     rdx, [rbx+0x400]
        mov     WORD PTR [rsp+0xe0], cx
        lea     rcx, [rbx+0x600]
        mov     WORD PTR [rsp+0x60], ax
        call    L60e0
        xor     edi, edi
        mov     esi, 0x2
        mov     eax, 0x2
        mov     edx, 0x1
        jmp     L6552
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mlkem768_indcpa_keypair_derand (0x6640)

L6640:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x1230]
        push    r13
        lea     r13, [rbp-0x2730]
        push    r12
        lea     r12, [rbp-0x2750]
        push    r10
        push    rbx
        lea     rbx, [rbp-0x2770]
        sub     rsp, 0x27c0
        movdqu  xmm1, XMMWORD PTR [rdx]
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     QWORD PTR [rbp-0x27c8], rdi
        mov     QWORD PTR [rbp-0x27d0], rsi
        mov     rdi, rbx
        lea     rsi, [rbp-0x27b0]
        mov     edx, 0x21
        movaps  XMMWORD PTR [rbp-0x27b0], xmm1
        movaps  XMMWORD PTR [rbp-0x27a0], xmm2
        mov     QWORD PTR [rbp-0x27d8], rsi
        mov     QWORD PTR [rbp-0x27e0], rbx
        mov     BYTE PTR [rbp-0x2790], 0x3
        call    L3570
        mov     rsi, rbx
        xor     edx, edx
        mov     rdi, r15
        mov     QWORD PTR [rbp-0x27c0], r15
        lea     rbx, [rbp-0x1830]
        call    L64b0
        sub     rsp, 0x8
        mov     r8, r12
        xor     r9d, r9d
        push    0xff
        lea     rdx, [rbp-0x1430]
        xor     ecx, ecx
        mov     rdi, rbx
        push    0x2
        lea     rsi, [rbp-0x1630]
        push    0x1
        call    L7790
        add     rsp, 0x18
        mov     r8, r12
        xor     ecx, ecx
        lea     rax, [rbp-0x2430]
        lea     rdx, [rbp-0x2030]
        mov     r9d, 0x3
        mov     QWORD PTR [rbp-0x27b8], rax
        mov     rdi, rax
        lea     rsi, [rbp-0x2230]
        mov     r14, rax
        push    0xff
        lea     r12, [rbp-0x1e30]
        push    0x5
        push    0x4
        call    L7790
        add     rsp, 0x20
        mov     rdi, rbx
        call    L7570
        mov     rdi, r14
        call    L7570
        mov     rsi, rbx
        mov     rdi, r13
        call    L76b0
        mov     QWORD PTR [rbp-0x27e8], r12
        lea     rax, [rbp-0x30]
        mov     r14, rax
L6786:
        mov     rsi, r15
        mov     rdi, r12
        mov     rcx, r13
        mov     rdx, rbx
        add     r15, 0x600
        add     r12, 0x200
        call    L75d0
        cmp     r15, r14
        jne     L6786
        mov     r12, QWORD PTR [rbp-0x27e8]
        mov     rdi, r12
        call    L7760
        mov     r15, QWORD PTR [rbp-0x27b8]
        mov     rdi, r12
        mov     rsi, r15
        call    L7720
        mov     rdi, r12
        call    L76f0
        mov     rdi, rbx
        call    L76f0
        mov     rdi, QWORD PTR [rbp-0x27d0]
        mov     rsi, rbx
        call    L74f0
        mov     r14, QWORD PTR [rbp-0x27c8]
        mov     rsi, r12
        mov     rdi, r14
        call    L74f0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x60
        movdqa  xmm3, XMMWORD PTR [rbp-0x2770]
        movdqa  xmm4, XMMWORD PTR [rbp-0x2760]
        rep stos QWORD PTR es:[rdi], rax
        movups  XMMWORD PTR [r14+0x480], xmm3
        movups  XMMWORD PTR [r14+0x490], xmm4
        mov     ecx, 0xc0
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0xc0
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0xc0
        mov     rdi, r15
        mov     QWORD PTR [rbp-0x27b8], r15
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x27c0]
        mov     ecx, 0x240
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x27c0]
        pxor    xmm0, xmm0
        mov     BYTE PTR [rbp-0x2790], 0x0
        mov     rax, QWORD PTR [rbp-0x27d8]
        movaps  XMMWORD PTR [rbp-0x27b0], xmm0
        movaps  XMMWORD PTR [rbp-0x27a0], xmm0
        mov     rax, QWORD PTR [rbp-0x27e0]
        movaps  XMMWORD PTR [rbp-0x2770], xmm0
        movaps  XMMWORD PTR [rbp-0x2760], xmm0
        movaps  XMMWORD PTR [rbp-0x2750], xmm0
        movaps  XMMWORD PTR [rbp-0x2740], xmm0
        lea     rsp, [rbp-0x30]
        xor     eax, eax
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem768_indcpa_enc (0x68d0)

L68d0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0x2430]
        lea     r14, [rbp-0x2d30]
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        mov     rbx, rsi
        mov     rsi, rdx
        sub     rsp, 0x3360
        mov     QWORD PTR [rbp-0x3380], rdi
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3370], rax
        call    L7530
        lea     rax, [rbp-0x3130]
        mov     rsi, rbx
        movdqu  xmm1, XMMWORD PTR [r13+0x480]
        movdqu  xmm2, XMMWORD PTR [r13+0x490]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3378], rax
        lea     rbx, [rbp-0x2a30]
        movaps  XMMWORD PTR [rbp-0x3350], xmm1
        lea     r13, [rbp-0x1830]
        movaps  XMMWORD PTR [rbp-0x3340], xmm2
        call    L3210
        lea     rax, [rbp-0x1230]
        mov     edx, 0x1
        lea     rsi, [rbp-0x3350]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3360], rax
        mov     QWORD PTR [rbp-0x3388], rsi
        call    L64b0
        sub     rsp, 0x8
        mov     r8, r12
        xor     r9d, r9d
        push    0xff
        lea     rdx, [rbp-0x2630]
        xor     ecx, ecx
        mov     rdi, rbx
        push    0x2
        lea     rsi, [rbp-0x2830]
        push    0x1
        call    L7790
        lea     rax, [rbp-0x1e30]
        add     rsp, 0x18
        mov     r8, r12
        lea     rcx, [rbp-0x2f30]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3368], rax
        lea     rdx, [rbp-0x1a30]
        mov     QWORD PTR [rbp-0x3358], rcx
        lea     rsi, [rbp-0x1c30]
        mov     r9d, 0x3
        push    0x6
        push    0x5
        push    0x4
        call    L7790
        add     rsp, 0x20
        mov     rdi, rbx
        call    L7570
        mov     rsi, rbx
        mov     rdi, r14
        call    L76b0
        mov     QWORD PTR [rbp-0x3390], r13
        lea     rax, [rbp-0x30]
        mov     r12, QWORD PTR [rbp-0x3360]
        mov     r15, rax
L6a2f:
        mov     rsi, r12
        mov     rdi, r13
        mov     rcx, r14
        mov     rdx, rbx
        add     r12, 0x600
        add     r13, 0x200
        call    L75d0
        cmp     r12, r15
        jne     L6a2f
        lea     r12, [rbp-0x3330]
        mov     r13, QWORD PTR [rbp-0x3390]
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, QWORD PTR [rbp-0x3370]
        mov     rdi, r12
        call    L75d0
        mov     rdi, r13
        call    L75a0
        mov     rdi, r12
        call    L5860
        mov     rsi, QWORD PTR [rbp-0x3368]
        mov     rdi, r13
        call    L7720
        mov     rsi, QWORD PTR [rbp-0x3358]
        mov     rdi, r12
        call    L56b0
        mov     rsi, QWORD PTR [rbp-0x3378]
        mov     rdi, r12
        call    L56b0
        mov     rdi, r13
        call    L76f0
        mov     rdi, r12
        call    L5660
        mov     r15, QWORD PTR [rbp-0x3380]
        mov     rsi, r13
        mov     rdi, r15
        call    L7470
        mov     rax, r15
        mov     rsi, r12
        add     rax, 0x3c0
        mov     rdi, rax
        call    L2460
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3358]
        mov     ecx, 0x40
        mov     rdx, QWORD PTR [rbp-0x3358]
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3378]
        mov     ecx, 0x40
        mov     rdx, QWORD PTR [rbp-0x3378]
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0xc0
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3368]
        mov     ecx, 0xc0
        mov     rdx, QWORD PTR [rbp-0x3368]
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3370]
        mov     ecx, 0xc0
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3370]
        mov     ecx, 0xc0
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3360]
        mov     ecx, 0x240
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3360]
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rbp-0x3388]
        movaps  XMMWORD PTR [rbp-0x3350], xmm0
        movaps  XMMWORD PTR [rbp-0x3340], xmm0
        lea     rsp, [rbp-0x30]
        xor     eax, eax
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem768_indcpa_dec (0x6bc0)

L6bc0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x1320
        lea     rbx, [rsp+0x720]
        mov     QWORD PTR [rsp+0x18], rdi
        lea     r15, [rsp+0xd20]
        mov     rdi, rbx
        lea     r14, [rsp+0x420]
        call    L74b0
        lea     rsi, [r12+0x3c0]
        lea     r12, [rsp+0x20]
        mov     rdi, r12
        call    L2740
        mov     rsi, r13
        mov     rdi, r15
        lea     r13, [rsp+0x220]
        call    L7530
        mov     rdi, rbx
        call    L7570
        mov     rsi, rbx
        mov     rdi, r14
        call    L76b0
        mov     rcx, r14
        mov     rdx, rbx
        mov     rsi, r15
        mov     rdi, r13
        call    L75d0
        mov     rdi, r13
        call    L5860
        mov     rsi, r13
        mov     rdi, r12
        call    L56e0
        mov     rdi, r12
        call    L5660
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     rsi, r12
        call    L3260
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x40
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0xc0
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0xc0
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem768_check_pk (0x6cc0)

L6cc0:
        push    rbp
        mov     rsi, rdi
        mov     rbp, rsp
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xa80
        lea     rbx, [rsp+0x480]
        mov     r12, rsp
        mov     rdi, rbx
        call    L7530
        mov     rdi, rbx
        call    L76f0
        mov     rsi, rbx
        mov     rdi, r12
        call    L74f0
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6d10:
        movdqu  xmm1, XMMWORD PTR [r13+rax*1+0x0]
        pxor    xmm1, XMMWORD PTR [r12+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x480
        jne     L6d10
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x8
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        mov     rdi, r12
        mov     ecx, 0x90
        sete    dl
        xor     eax, eax
        rep stos QWORD PTR es:[rdi], rax
        movzx   edx, dl
        lea     edx, [rdx*4-0x4]
        mov     ecx, 0xc0
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x18]
        mov     eax, edx
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop
        .byte   0x90

// mlkem768_check_sk (0x6de0)

L6de0:
        push    rbp
        lea     rsi, [rdi+0x480]
        mov     edx, 0x4a0
        mov     rbp, rsp
        push    r12
        push    rbx
        mov     rbx, rdi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     r12, rsp
        mov     rdi, r12
        call    L3510
        movdqu  xmm1, XMMWORD PTR [rbx+0x920]
        movdqu  xmm2, XMMWORD PTR [rbx+0x930]
        pxor    xmm1, XMMWORD PTR [rsp]
        pxor    xmm2, XMMWORD PTR [rsp+0x10]
        movdqa  xmm0, xmm1
        pxor    xmm1, xmm2
        por     xmm0, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     eax
        sar     eax, 0x10
        xor     eax, edx
        cmp     al, dl
        pxor    xmm0, xmm0
        sete    al
        movaps  XMMWORD PTR [rsp], xmm0
        movzx   eax, al
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     eax, [rax+rax*4-0x5]
        lea     rsp, [rbp-0x10]
        pop     rbx
        pop     r12
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem768_keypair_derand (0x6ed0)

L6ed0:
        push    r13
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsp, 0x8
        call    L6640
        mov     r13d, eax
        test    eax, eax
        jne     L6f78
        mov     rax, QWORD PTR [rbp+0x0]
        lea     rdi, [rbx+0x488]
        lea     rcx, [rbx+0x480]
        mov     rsi, rbp
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [rbx+0x480], rax
        sub     rcx, rdi
        mov     rdx, QWORD PTR [rbp+0x498]
        lea     rax, [rbx+0x920]
        sub     rsi, rcx
        add     ecx, 0x4a0
        mov     QWORD PTR [rbx+0x918], rdx
        shr     ecx, 0x3
        mov     edx, 0x4a0
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbp
        mov     rdi, rax
        call    L3510
        movdqu  xmm0, XMMWORD PTR [r12+0x20]
        mov     eax, r13d
        movups  XMMWORD PTR [rbx+0x940], xmm0
        movdqu  xmm1, XMMWORD PTR [r12+0x30]
        movups  XMMWORD PTR [rbx+0x950], xmm1
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6f78:
        lea     rdi, [rbp+0x8]
        mov     rcx, rbp
        xor     eax, eax
        mov     QWORD PTR [rbp+0x0], 0x0
        mov     QWORD PTR [rbp+0x498], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x4a0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x958], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x960
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0x8
        mov     eax, r13d
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem768_keypair (0x6ff0)

L6ff0:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x40
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x40
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L7050
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L6ed0
L7029:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L7050:
        mov     eax, 0xfffffffd
        jmp     L7029
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem768_enc_derand (0x7060)

L7060:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        push    r13
        mov     r13, rsi
        push    r12
        mov     r12, rdi
        mov     rdi, rdx
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        add     rsp, 0xffffffffffffff80
        call    L6cc0
        mov     r14, rsp
        test    eax, eax
        je      L70d0
        lea     r15, [rsp+0x40]
L7095:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90
L70d0:
        movdqu  xmm1, XMMWORD PTR [r15]
        movdqu  xmm2, XMMWORD PTR [r15+0x10]
        lea     rdi, [rsp+0x20]
        mov     rsi, rbx
        mov     edx, 0x4a0
        lea     r15, [rsp+0x40]
        movaps  XMMWORD PTR [rsp], xmm1
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        call    L3510
        mov     edx, 0x40
        mov     rsi, r14
        mov     rdi, r15
        call    L3570
        lea     rcx, [rsp+0x60]
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r12
        call    L68d0
        test    eax, eax
        jne     L7095
        movdqa  xmm3, XMMWORD PTR [rsp+0x40]
        movdqa  xmm4, XMMWORD PTR [rsp+0x50]
        movups  XMMWORD PTR [r13+0x0], xmm3
        movups  XMMWORD PTR [r13+0x10], xmm4
        jmp     L7095
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mlkem768_enc (0x7150)

L7150:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1010
        test    eax, eax
        jne     L71b0
        mov     rcx, rbx
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, r12
        call    L7060
L7191:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L71b0:
        mov     eax, 0xfffffffd
        jmp     L7191
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mlkem768_dec (0x71c0)

L71c0:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        push    r14
        mov     r14, rdi
        mov     rdi, rdx
        push    r13
        mov     r13, rdx
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x500
        call    L6de0
        test    eax, eax
        je      L7258
        mov     ebx, eax
        lea     r10, [rsp+0x20]
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
L7201:
        xor     eax, eax
        mov     rdi, r8
        mov     ecx, 0x8c
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, ebx
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7258:
        lea     r10, [rsp+0x20]
        mov     rdx, r13
        mov     rsi, r15
        mov     rdi, r10
        mov     QWORD PTR [rsp+0x18], r10
        call    L6bc0
        mov     r10, QWORD PTR [rsp+0x18]
        test    eax, eax
        mov     ebx, eax
        je      L7290
        lea     r9, [rsp+0x60]
        lea     r8, [rsp+0xa0]
        jmp     L7201
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L7290:
        lea     r9, [rsp+0x60]
        mov     rsi, r10
        mov     edx, 0x40
        mov     QWORD PTR [rsp+0x18], r10
        movdqu  xmm3, XMMWORD PTR [r13+0x920]
        mov     rdi, r9
        mov     QWORD PTR [rsp+0x8], r9
        movdqu  xmm4, XMMWORD PTR [r13+0x930]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        call    L3570
        mov     r10, QWORD PTR [rsp+0x18]
        lea     r8, [rsp+0xa0]
        lea     rcx, [rsp+0x80]
        mov     rdi, r8
        lea     rdx, [r13+0x480]
        mov     QWORD PTR [rsp+0x18], r8
        mov     rsi, r10
        mov     QWORD PTR [rsp+0x10], r10
        call    L68d0
        mov     r8, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp+0x10]
        test    eax, eax
        mov     r9, QWORD PTR [rsp+0x8]
        mov     ebx, eax
        jne     L7201
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop
        .byte   0x90
L7320:
        movdqu  xmm1, XMMWORD PTR [r15+rax*1]
        pxor    xmm1, XMMWORD PTR [r8+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x440
        jne     L7320
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x8], r10
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x10], r9
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    eax, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    r12d, xmm0
        movzx   r12d, r12b
        neg     r12d
        sar     r12d, 0x10
        xor     r12d, eax
        xor     r12d, eax
        mov     rdx, r8
        mov     ecx, 0x88
        mov     rsi, r15
        movdqu  xmm6, XMMWORD PTR [r13+0x950]
        mov     QWORD PTR [rsp+0x18], r8
        movzx   r12d, r12b
        lea     rax, [rsp+0xc0]
        movdqu  xmm5, XMMWORD PTR [r13+0x940]
        mov     rdi, rax
        neg     r12d
        movaps  XMMWORD PTR [rsp+0xb0], xmm6
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     ecx, 0x460
        mov     esi, 0x20
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0xa0], xmm5
        call    L3480
        mov     r10, QWORD PTR [rsp+0x8]
        mov     r9, QWORD PTR [rsp+0x10]
        xor     eax, eax
        mov     r8, QWORD PTR [rsp+0x18]
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L7440:
        movzx   esi, BYTE PTR [r9+rax*1]
        mov     ecx, r12d
        movzx   edx, BYTE PTR [r14+rax*1]
        sar     ecx, 0x10
        xor     edx, esi
        and     edx, ecx
        xor     edx, esi
        mov     BYTE PTR [r14+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x20
        jne     L7440
        jmp     L7201
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mlkem768_polyvec_compress_du (0x7470)

L7470:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L2660
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x140]
        call    L2660
        add     rsp, 0x8
        lea     rsi, [rbp+0x400]
        lea     rdi, [rbx+0x280]
        pop     rbx
        pop     rbp
        jmp     L2660
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_decompress_du (0x74b0)

L74b0:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L2790
        lea     rsi, [rbp+0x140]
        lea     rdi, [rbx+0x200]
        call    L2790
        add     rsp, 0x8
        lea     rsi, [rbp+0x280]
        lea     rdi, [rbx+0x400]
        pop     rbx
        pop     rbp
        jmp     L2790
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_tobytes (0x74f0)

L74f0:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L3180
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x180]
        call    L3180
        add     rsp, 0x8
        lea     rsi, [rbp+0x400]
        lea     rdi, [rbx+0x300]
        pop     rbx
        pop     rbp
        jmp     L3180
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_frombytes (0x7530)

L7530:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L31c0
        lea     rsi, [rbp+0x180]
        lea     rdi, [rbx+0x200]
        call    L31c0
        add     rsp, 0x8
        lea     rsi, [rbp+0x300]
        lea     rdi, [rbx+0x400]
        pop     rbx
        pop     rbp
        jmp     L31c0
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_ntt (0x7570)

L7570:
        push    rbx
        mov     rbx, rdi
        call    L5780
        lea     rdi, [rbx+0x200]
        call    L5780
        lea     rdi, [rbx+0x400]
        pop     rbx
        jmp     L5780
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_invntt_tomont (0x75a0)

L75a0:
        push    rbx
        mov     rbx, rdi
        call    L5860
        lea     rdi, [rbx+0x200]
        call    L5860
        lea     rdi, [rbx+0x400]
        pop     rbx
        jmp     L5860
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_basemul_acc_montgomery_cached (0x75d0)

L75d0:
        push    r15
        lea     r8, [rdx+0x2]
        mov     rax, rcx
        mov     r9, rsi
        push    r14
        lea     rdx, [rdi+0x2]
        lea     r14, [rcx+0x100]
        push    r13
        push    r12
        push    rbp
        push    rbx
        // nop
        .byte   0x90
L75f0:
        mov     r11, rax
        xor     ecx, ecx
        xor     edi, edi
        xor     esi, esi
        lea     r12, [r9+0x2]
        lea     rbp, [r8-0x2]
L7601:
        movsx   ebx, WORD PTR [r12+rcx*1]
        movsx   r10d, WORD PTR [r11]
        add     r11, 0x100
        movsx   r13d, WORD PTR [r9+rcx*1]
        movsx   r15d, WORD PTR [rbp+rcx*1+0x0]
        imul    r10d, ebx
        mov     DWORD PTR [rsp-0x4], ebx
        mov     ebx, r10d
        mov     r10d, r13d
        imul    r10d, r15d
        add     ebx, r10d
        movsx   r10d, WORD PTR [r8+rcx*1]
        add     rcx, 0x200
        add     esi, ebx
        mov     ebx, DWORD PTR [rsp-0x4]
        imul    r10d, r13d
        imul    ebx, r15d
        add     ebx, r10d
        add     edi, ebx
        cmp     rcx, 0x600
        jne     L7601
        add     rax, 0x2
        add     r9, 0x4
        add     r8, 0x4
        add     rdx, 0x4
        imul    cx, si, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, esi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x6], cx
        imul    cx, di, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, edi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x4], cx
        cmp     r14, rax
        jne     L75f0
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mlkem768_polyvec_mulcache_compute (0x76b0)

L76b0:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L5710
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x100]
        call    L5710
        add     rsp, 0x8
        lea     rsi, [rbp+0x400]
        lea     rdi, [rbx+0x200]
        pop     rbx
        pop     rbp
        jmp     L5710
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_reduce (0x76f0)

L76f0:
        push    rbx
        mov     rbx, rdi
        call    L5660
        lea     rdi, [rbx+0x200]
        call    L5660
        lea     rdi, [rbx+0x400]
        pop     rbx
        jmp     L5660
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_add (0x7720)

L7720:
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        call    L56b0
        lea     rsi, [rbp+0x200]
        lea     rdi, [rbx+0x200]
        call    L56b0
        add     rsp, 0x8
        lea     rsi, [rbp+0x400]
        lea     rdi, [rbx+0x400]
        pop     rbx
        pop     rbp
        jmp     L56b0
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_polyvec_tomont (0x7760)

L7760:
        push    rbx
        mov     rbx, rdi
        call    L55a0
        lea     rdi, [rbx+0x200]
        call    L55a0
        lea     rdi, [rbx+0x400]
        pop     rbx
        jmp     L55a0
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mlkem768_poly_getnoise_eta1_4x (0x7790)

L7790:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x330]
        lea     r14, [rbp-0x130]
        push    r13
        lea     r13, [rbp-0xb0]
        push    r12
        mov     r12, rcx
        push    r10
        push    rbx
        lea     rbx, [rbp-0x230]
        sub     rsp, 0x320
        mov     r11d, DWORD PTR [r10]
        mov     ecx, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x348], rdx
        movdqu  xmm1, XMMWORD PTR [r8]
        mov     edx, DWORD PTR [r10+0x10]
        mov     QWORD PTR [rbp-0x338], rdi
        lea     rdi, [rbp-0x2b0]
        movdqu  xmm0, XMMWORD PTR [r8+0x10]
        mov     QWORD PTR [rbp-0x340], rsi
        lea     r8, [rbp-0x270]
        lea     rsi, [rbp-0x2f0]
        mov     BYTE PTR [rbp-0x2d0], r11b
        lea     r10, [rbp-0x1b0]
        movaps  XMMWORD PTR [rbp-0x330], xmm1
        movaps  XMMWORD PTR [rbp-0x320], xmm0
        movaps  XMMWORD PTR [rbp-0x2f0], xmm1
        movaps  XMMWORD PTR [rbp-0x2e0], xmm0
        movaps  XMMWORD PTR [rbp-0x2b0], xmm1
        movaps  XMMWORD PTR [rbp-0x2a0], xmm0
        movaps  XMMWORD PTR [rbp-0x270], xmm1
        movaps  XMMWORD PTR [rbp-0x260], xmm0
        mov     BYTE PTR [rbp-0x310], r9b
        mov     r9, r15
        mov     BYTE PTR [rbp-0x290], cl
        mov     rcx, r13
        mov     BYTE PTR [rbp-0x250], dl
        mov     rdx, r14
        push    0x21
        push    r8
        mov     r8d, 0x80
        push    rdi
        mov     rdi, rbx
        push    rsi
        mov     rsi, r10
        mov     QWORD PTR [rbp-0x350], r10
        call    L3870
        mov     rdi, QWORD PTR [rbp-0x338]
        add     rsp, 0x20
        mov     rsi, rbx
        call    L63b0
        mov     rsi, QWORD PTR [rbp-0x350]
        mov     rdi, QWORD PTR [rbp-0x340]
        call    L63b0
        mov     rdi, QWORD PTR [rbp-0x348]
        mov     rsi, r14
        call    L63b0
        test    r12, r12
        je      L78d7
        mov     rsi, r13
        mov     rdi, r12
        call    L63b0
L78d7:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x40
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x20
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret

// Padding (0x7904 to 0x8000)

        .zero   1788

// The read-only data (0x8000 to 0x82a0)

L8000:
        .quad   0x0800000008000000
L8008:
        .quad   0x00ff00ff00ff00ff
L8010:
        .quad   0x0000020000000200
L8018:
        .quad   0x0400000004000000
L8020:
        .quad   0x0000001000000010
        .quad   0x0000000000000000
L8030:
        .quad   0x0000000100000000
        .quad   0x0000000100000000
L8040:
        .quad   0x07ff07ff07ff07ff
        .quad   0x07ff07ff07ff07ff
L8050:
        .quad   0x0d010d010d010d01
        .quad   0x0d010d010d010d01
L8060:
        .quad   0x0000040000000400
        .quad   0x0000040000000400
L8070:
        .quad   0x0549054905490549
        .quad   0x0549054905490549
L8080:
        .quad   0xf301f301f301f301
        .quad   0xf301f301f301f301
L8090:
        .quad   0xf2fff2fff2fff2ff
        .quad   0xf2fff2fff2fff2ff
L80a0:
        .quad   0x05a105a105a105a1
        .quad   0x05a105a105a105a1
        .zero   16
L80c0:
        .quad   0x0000000000000001
        .quad   0x0000000000008082
        .quad   0x800000000000808a
        .quad   0x8000000080008000
        .quad   0x000000000000808b
        .quad   0x0000000080000001
        .quad   0x8000000080008081
        .quad   0x8000000000008009
        .quad   0x000000000000008a
        .quad   0x0000000000000088
        .quad   0x0000000080008009
        .quad   0x000000008000000a
        .quad   0x000000008000808b
        .quad   0x800000000000008b
        .quad   0x8000000000008089
        .quad   0x8000000000008003
        .quad   0x8000000000008002
        .quad   0x8000000000000080
        .quad   0x000000000000800a
        .quad   0x800000008000000a
        .quad   0x8000000080008081
        .quad   0x8000000000008080
        .quad   0x0000000080000001
        .quad   0x8000000080008008
L8180:
        .byte   0x01
        .byte   0x01
L8182:
        .byte   0x02
        .byte   0x02
        .zero   28
L81a0:
        .quad   0xfa13fe99fd0afbec
        .quad   0x00ca011f058e05d5
        .quad   0x00b60629026eff55
        .quad   0x05bcfa3efb4e03c2
        .quad   0x017f0108fad3023d
        .quad   0xff7ef9be05b2fcc3
        .quad   0x026002dc03f9fd57
        .quad   0xf9ddff33019bf9fa
        .quad   0x03f7fdd8028c04c7
        .quad   0xf9f8fee605d3faf3
        .quad   0xfd66fec0fff80204
        .quad   0x05bd007efb76f9ae
        .quad   0x033efef1ffa6fcab
        .quad   0xfc49ff09fa73006b
        .quad   0xfd2bfa1c03c1fe72
        .quad   0xfb0502a5fbd701c0
L8220:
        .quad   0x034b022b01aefbb1
        .quad   0x0069060e0367fb1d
        .quad   0xff1500b1024b01a6
        .quad   0x06750626fe34fedd
        .quad   0xff6d0487030aff0a
        .quad   0x045ffda605cbfcf7
        .quad   0x015dfc980284f9ca
        .quad   0xffb5ff64014901a2
        .quad   0x0262025b04490331
        .quad   0x0180fa47fafb052a
        .quad   0xfac904c2ff78fb41
        .quad   0xf985fb5d00dcfc96
        .quad   0x031afb02fa06fb5f
        .quad   0x01defc9afcaafa1a
        .quad   0x03df03e4feccff94
        .quad   0x065c05f2fa4c03be

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
