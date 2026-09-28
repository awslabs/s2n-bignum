// -------------------------------------------------------------------------
// Simulator for single x86 register-only instruction:
//
//         uint64_t harness(uint64_t *regfile);
//
// Copies state from "regfile" into registers, flags and a small buffer
// starting at the stack pointer as follows:
//
//      RAX = regfile[0]
//      RCX = regfile[1]
//      RDX = regfile[2]
//      RBX = regfile[3]
//      OF:DF:0:0:SF:ZF:0:AF:0:PF:0:CF = regfile[4]
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
//
//      ...
//
// executes the instruction at "modinst", then copies the new state
// back into the same array, also returning new value RAX directly.
//
// The flags are encoded at the bits they occur in EFLAGS and packed
// into the field corresponding to RSP (which is not modified) in the
// standard x86 register numbering:
// -------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  harness, _harness
        .text

harness:
_harness:

// Save the original flag settings, so that we can restore them.
// This seems to be worth doing in the case of DF, at least, which
// is a control flag and is expected to be zero by standard ABIs

        pushfq

// Force the stack to be 32-aligned

        mov     rax, 0x1F
        and     rax, rsp
        xor     rsp, rax
        or      rax, rsp

// Save the original stack pointer (now in rax), the non-modifiable
// registers rbx, rbp, r12, ..., r15, and the input argument rdi.
// We subtract 64 from the stack pointer and hence maintain alignment.

        push    rax
        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        push    rdi

// Create little 256-byte buffer and copy in the contents
        sub rsp, 256
        vmovdqu ymm0, [rdi+2240+0*32]
        vmovdqu [rsp], ymm0
        vmovdqu ymm0, [rdi+2240+1*32]
        vmovdqu [rsp+1*32], ymm0
        vmovdqu ymm0, [rdi+2240+2*32]
        vmovdqu [rsp+2*32], ymm0
        vmovdqu ymm0, [rdi+2240+3*32]
        vmovdqu [rsp+3*32], ymm0
        vmovdqu ymm0, [rdi+2240+4*32]
        vmovdqu [rsp+4*32], ymm0
        vmovdqu ymm0, [rdi+2240+5*32]
        vmovdqu [rsp+5*32], ymm0
        vmovdqu ymm0, [rdi+2240+6*32]
        vmovdqu [rsp+6*32], ymm0
        vmovdqu ymm0, [rdi+2240+7*32]
        vmovdqu [rsp+7*32], ymm0

// Load new register contents from rdi (last overwrites the input pointer)

        pushfq
        pop     rcx
        mov     rax, [rdi+4*8]
        mov     rbx, 0b110011010101
        and     rax, rbx
        not     rbx
        and     rcx, rbx
        or      rax, rcx
        push    rax
        popfq

        mov     rax, [rdi+0*8]
        mov     rcx, [rdi+1*8]
        mov     rdx, [rdi+2*8]
        mov     rbx, [rdi+3*8]
        mov     rbp, [rdi+5*8]
        mov     rsi, [rdi+6*8]
        mov      r8, [rdi+8*8]
        mov      r9, [rdi+9*8]
        mov     r10, [rdi+10*8]
        mov     r11, [rdi+11*8]
        mov     r12, [rdi+12*8]
        mov     r13, [rdi+13*8]
        mov     r14, [rdi+14*8]
        mov     r15, [rdi+15*8]

        vmovdqu64 zmm0,  [rdi+128+0*64]
        vmovdqu64 zmm1,  [rdi+128+1*64]
        vmovdqu64 zmm2,  [rdi+128+2*64]
        vmovdqu64 zmm3,  [rdi+128+3*64]
        vmovdqu64 zmm4,  [rdi+128+4*64]
        vmovdqu64 zmm5,  [rdi+128+5*64]
        vmovdqu64 zmm6,  [rdi+128+6*64]
        vmovdqu64 zmm7,  [rdi+128+7*64]
        vmovdqu64 zmm8,  [rdi+128+8*64]
        vmovdqu64 zmm9,  [rdi+128+9*64]
        vmovdqu64 zmm10, [rdi+128+10*64]
        vmovdqu64 zmm11, [rdi+128+11*64]
        vmovdqu64 zmm12, [rdi+128+12*64]
        vmovdqu64 zmm13, [rdi+128+13*64]
        vmovdqu64 zmm14, [rdi+128+14*64]
        vmovdqu64 zmm15, [rdi+128+15*64]
        vmovdqu64 zmm16, [rdi+128+16*64]
        vmovdqu64 zmm17, [rdi+128+17*64]
        vmovdqu64 zmm18, [rdi+128+18*64]
        vmovdqu64 zmm19, [rdi+128+19*64]
        vmovdqu64 zmm20, [rdi+128+20*64]
        vmovdqu64 zmm21, [rdi+128+21*64]
        vmovdqu64 zmm22, [rdi+128+22*64]
        vmovdqu64 zmm23, [rdi+128+23*64]
        vmovdqu64 zmm24, [rdi+128+24*64]
        vmovdqu64 zmm25, [rdi+128+25*64]
        vmovdqu64 zmm26, [rdi+128+26*64]
        vmovdqu64 zmm27, [rdi+128+27*64]
        vmovdqu64 zmm28, [rdi+128+28*64]
        vmovdqu64 zmm29, [rdi+128+29*64]
        vmovdqu64 zmm30, [rdi+128+30*64]
        vmovdqu64 zmm31, [rdi+128+31*64]

        kmovq   k1, [rdi+273*8]
        kmovq   k2, [rdi+274*8]
        kmovq   k3, [rdi+275*8]
        kmovq   k4, [rdi+276*8]
        kmovq   k5, [rdi+277*8]
        kmovq   k6, [rdi+278*8]
        kmovq   k7, [rdi+279*8]

        mov     rdi, [rdi+7*8]

// Execute the instruction, which may be modified from this placeholder

modinst:
        .byte ICODE

// Copy new state back to the buffer

        push    rdi
        mov     rdi, [rsp+256+8]
        mov     [rdi+0*8], rax

        pushfq
        pop     rax
        and     rax, 0b110011010101
        mov     [rdi+4*8], rax

        vmovdqu64 [rdi+128+0*64],  zmm0
        vmovdqu64 [rdi+128+1*64],  zmm1
        vmovdqu64 [rdi+128+2*64],  zmm2
        vmovdqu64 [rdi+128+3*64],  zmm3
        vmovdqu64 [rdi+128+4*64],  zmm4
        vmovdqu64 [rdi+128+5*64],  zmm5
        vmovdqu64 [rdi+128+6*64],  zmm6
        vmovdqu64 [rdi+128+7*64],  zmm7
        vmovdqu64 [rdi+128+8*64],  zmm8
        vmovdqu64 [rdi+128+9*64],  zmm9
        vmovdqu64 [rdi+128+10*64], zmm10
        vmovdqu64 [rdi+128+11*64], zmm11
        vmovdqu64 [rdi+128+12*64], zmm12
        vmovdqu64 [rdi+128+13*64], zmm13
        vmovdqu64 [rdi+128+14*64], zmm14
        vmovdqu64 [rdi+128+15*64], zmm15
        vmovdqu64 [rdi+128+16*64], zmm16
        vmovdqu64 [rdi+128+17*64], zmm17
        vmovdqu64 [rdi+128+18*64], zmm18
        vmovdqu64 [rdi+128+19*64], zmm19
        vmovdqu64 [rdi+128+20*64], zmm20
        vmovdqu64 [rdi+128+21*64], zmm21
        vmovdqu64 [rdi+128+22*64], zmm22
        vmovdqu64 [rdi+128+23*64], zmm23
        vmovdqu64 [rdi+128+24*64], zmm24
        vmovdqu64 [rdi+128+25*64], zmm25
        vmovdqu64 [rdi+128+26*64], zmm26
        vmovdqu64 [rdi+128+27*64], zmm27
        vmovdqu64 [rdi+128+28*64], zmm28
        vmovdqu64 [rdi+128+29*64], zmm29
        vmovdqu64 [rdi+128+30*64], zmm30
        vmovdqu64 [rdi+128+31*64], zmm31

        kmovq   [rdi+273*8], k1
        kmovq   [rdi+274*8], k2
        kmovq   [rdi+275*8], k3
        kmovq   [rdi+276*8], k4
        kmovq   [rdi+277*8], k5
        kmovq   [rdi+278*8], k6
        kmovq   [rdi+279*8], k7

        mov     [rdi+1*8],  rcx
        mov     [rdi+2*8],  rdx
        mov     [rdi+3*8],  rbx
        mov     [rdi+5*8],  rbp
        mov     [rdi+6*8],  rsi
        mov     [rdi+8*8],   r8
        mov     [rdi+9*8],   r9
        mov     [rdi+10*8], r10
        mov     [rdi+11*8], r11
        mov     [rdi+12*8], r12
        mov     [rdi+13*8], r13
        mov     [rdi+14*8], r14
        mov     [rdi+15*8], r15
        pop     rcx
        mov     [rdi+7*8],  rcx

// Copy back contents of the buffer and deallocate stack
        vmovdqu ymm0, [rsp]
        vmovdqu [rdi+2240+0*32], ymm0
        vmovdqu ymm0, [rsp+1*32]
        vmovdqu [rdi+2240+1*32], ymm0
        vmovdqu ymm0, [rsp+2*32]
        vmovdqu [rdi+2240+2*32], ymm0
        vmovdqu ymm0, [rsp+3*32]
        vmovdqu [rdi+2240+3*32], ymm0
        vmovdqu ymm0, [rsp+4*32]
        vmovdqu [rdi+2240+4*32], ymm0
        vmovdqu ymm0, [rsp+5*32]
        vmovdqu [rdi+2240+5*32], ymm0
        vmovdqu ymm0, [rsp+6*32]
        vmovdqu [rdi+2240+6*32], ymm0
        vmovdqu ymm0, [rsp+7*32]
        vmovdqu [rdi+2240+7*32], ymm0
        add rsp, 256

// Dummy pop to match push of rdi

        pop     rdi

// Load back the preserved registers

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

// Finally restore the original stack pointer

        pop     rsp

// Pop back the original flags register too

        popfq

// Also return rax from the instruction

        mov     rax, [rdi+0*8]
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
