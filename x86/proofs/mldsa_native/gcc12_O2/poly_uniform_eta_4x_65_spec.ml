(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-4,4] for ML-DSA-65 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa65_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which extends the seed of 64 bytes with each of  *)
(* the four nonce bytes and a zero byte, absorbs the four into a fourfold    *)
(* SHAKE256 state, squeezes 2 blocks of 136 bytes of each and samples the    *)
(* coefficients from them with mld_rej_eta_c65, and then squeezes one more   *)
(* block of each and samples from all four until each polynomial has 256     *)
(* coefficients, before releasing the state and zeroing the buffers and the  *)
(* extended seeds, with memsets that gcc inlines with REP STOSQ, so the      *)
(* direction flag must be clear, as the ABI requires on entry. It is         *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_poly_uniform_eta of common/mldsa_native_sampling.ml, using the        *)
(* theorems for the callees, and assuming that the SHAKE256 output of each   *)
(* extended seed has 256 acceptable nibbles (mld_rej_eta_terminates),        *)
(* without which the code does not terminate. The nonces are the low bytes   *)
(* of the sixth argument and of the three arguments that the caller puts on  *)
(* the stack, as the System V ABI passes them. It is also shown to be        *)
(* constant time and memory safe, with the events depending on the seed only *)
(* through which nibbles of the SHAKE256 outputs mld_rej_eta_c accepts,      *)
(* which it declassifies (mld_poly_uniform_eta_declass).                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_absorb_once_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_squeezeblocks_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/rej_eta_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_uniform_eta_4x:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0x980
      +0x18  movdqu  xmm3, XMMWORD PTR [r8]
      +0x1d  movdqu  xmm2, XMMWORD PTR [r8+0x10]
      +0x23  movdqu  xmm1, XMMWORD PTR [r8+0x20]
      +0x29  movdqu  xmm0, XMMWORD PTR [r8+0x30]
      +0x2f  lea     r14, [rsp+0x60]
      +0x34  mov     QWORD PTR [rsp+0x38], rsi
      +0x39  movaps  XMMWORD PTR [rsp+0x60], xmm3
      +0x3e  lea     rbx, [rsp+0xc0]
      +0x46  lea     r13, [rsp+0x120]
      +0x4e  movaps  XMMWORD PTR [rsp+0x70], xmm2
      +0x53  lea     r12, [rsp+0x180]
      +0x5b  movaps  XMMWORD PTR [rsp+0x80], xmm1
      +0x63  movaps  XMMWORD PTR [rsp+0x90], xmm0
      +0x6b  movaps  XMMWORD PTR [rsp+0xc0], xmm3
      +0x73  movaps  XMMWORD PTR [rsp+0xd0], xmm2
      +0x7b  movaps  XMMWORD PTR [rsp+0xe0], xmm1
      +0x83  movaps  XMMWORD PTR [rsp+0xf0], xmm0
      +0x8b  movaps  XMMWORD PTR [rsp+0x120], xmm3
      +0x93  movaps  XMMWORD PTR [rsp+0x130], xmm2
      +0x9b  movaps  XMMWORD PTR [rsp+0x140], xmm1
      +0xa3  movaps  XMMWORD PTR [rsp+0x150], xmm0
      +0xab  movaps  XMMWORD PTR [rsp+0x180], xmm3
      +0xb3  movaps  XMMWORD PTR [rsp+0x190], xmm2
      +0xbb  movaps  XMMWORD PTR [rsp+0x1a0], xmm1
      +0xc3  movaps  XMMWORD PTR [rsp+0x1b0], xmm0
      +0xcb  mov     QWORD PTR [rsp+0x30], rdx
      +0xd0  mov     QWORD PTR [rsp+0x28], rcx
      +0xd5  mov     QWORD PTR [rsp+0x40], rdi
      +0xda  mov     QWORD PTR [rsp+0x18], r14
      +0xdf  mov     BYTE PTR [rsp+0xa0], r9b
      +0xe7  mov     eax, DWORD PTR [rbp+0x10]
      +0xea  mov     BYTE PTR [rsp+0x100], al
      +0xf1  mov     eax, DWORD PTR [rbp+0x18]
      +0xf4  mov     BYTE PTR [rsp+0x160], al
      +0xfb  mov     eax, DWORD PTR [rbp+0x20]
      +0xfe  mov     BYTE PTR [rsp+0xa1], 0x0
     +0x106  mov     BYTE PTR [rsp+0x1c0], al
     +0x10d  lea     rax, [rsp+0x1e0]
     +0x115  mov     r15, rax
     +0x118  mov     rdi, rax
     +0x11b  mov     QWORD PTR [rsp+0x20], rax
     +0x120  mov     BYTE PTR [rsp+0x101], 0x0
     +0x128  mov     BYTE PTR [rsp+0x161], 0x0
     +0x130  mov     BYTE PTR [rsp+0x1c1], 0x0
     +0x138  call    mldsa_shake256x4_init
     after_mldsa_shake256x4_init:
     +0x13d  mov     r8, r12
     +0x140  mov     rcx, r13
     +0x143  mov     rdx, rbx
     +0x146  mov     rsi, r14
     +0x149  mov     rdi, r15
     +0x14c  mov     r9d, 0x42
     +0x152  mov     rbx, r15
     +0x155  call    mldsa_shake256x4_absorb_once
     after_mldsa_shake256x4_absorb_once:
     +0x15a  lea     r14, [rsp+0x500]
     +0x162  lea     r11, [rsp+0x620]
     +0x16a  mov     r9, rbx
     +0x16d  mov     rsi, r11
     +0x170  mov     r8d, 0x2
     +0x176  mov     rdi, r14
     +0x179  mov     rbx, r11
     +0x17c  lea     rax, [rsp+0x860]
     +0x184  lea     r15, [rsp+0x740]
     +0x18c  mov     QWORD PTR [rsp+0x50], r11
     +0x191  mov     rcx, rax
     +0x194  mov     rdx, r15
     +0x197  mov     QWORD PTR [rsp+0x58], rax
     +0x19c  call    mldsa_shake256x4_squeezeblocks
     after_mldsa_shake256x4_squeezeblocks_1:
     +0x1a1  mov     rdi, QWORD PTR [rsp+0x40]
     +0x1a6  xor     esi, esi
     +0x1a8  mov     rdx, r14
     +0x1ab  mov     ecx, 0x110
     +0x1b0  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_1:
     +0x1b5  mov     rdi, QWORD PTR [rsp+0x38]
     +0x1ba  mov     rdx, rbx
     +0x1bd  xor     esi, esi
     +0x1bf  mov     ecx, 0x110
     +0x1c4  mov     r13d, eax
     +0x1c7  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_2:
     +0x1cc  mov     rdi, QWORD PTR [rsp+0x30]
     +0x1d1  xor     esi, esi
     +0x1d3  mov     rdx, r15
     +0x1d6  mov     ecx, 0x110
     +0x1db  mov     r12d, eax
     +0x1de  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_3:
     +0x1e3  mov     rdx, QWORD PTR [rsp+0x58]
     +0x1e8  mov     rdi, QWORD PTR [rsp+0x28]
     +0x1ed  xor     esi, esi
     +0x1ef  mov     ecx, 0x110
     +0x1f4  mov     ebx, eax
     +0x1f6  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_4:
     +0x1fb  cmp     r12d, 0xff
     +0x202  mov     r10d, eax
     +0x205  setbe   al
     +0x208  cmp     r13d, 0xff
     +0x20f  jmp     join2
     +0x214  nop     DWORD PTR [rax+0x0]
     join1:
     +0x218  mov     r9, QWORD PTR [rsp+0x20]
     +0x21d  mov     rcx, QWORD PTR [rsp+0x58]
     +0x222  mov     rdx, r15
     +0x225  mov     rdi, r14
     +0x228  mov     rsi, QWORD PTR [rsp+0x50]
     +0x22d  mov     r8d, 0x1
     +0x233  mov     DWORD PTR [rsp+0x4c], r10d
     +0x238  call    mldsa_shake256x4_squeezeblocks
     after_mldsa_shake256x4_squeezeblocks_2:
     +0x23d  mov     rdi, QWORD PTR [rsp+0x40]
     +0x242  mov     esi, r13d
     +0x245  mov     rdx, r14
     +0x248  mov     ecx, 0x88
     +0x24d  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_5:
     +0x252  mov     rdx, QWORD PTR [rsp+0x50]
     +0x257  mov     rdi, QWORD PTR [rsp+0x38]
     +0x25c  mov     esi, r12d
     +0x25f  mov     ecx, 0x88
     +0x264  mov     r13d, eax
     +0x267  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_6:
     +0x26c  mov     rdi, QWORD PTR [rsp+0x30]
     +0x271  mov     esi, ebx
     +0x273  mov     rdx, r15
     +0x276  mov     ecx, 0x88
     +0x27b  mov     r12d, eax
     +0x27e  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_7:
     +0x283  mov     rdx, QWORD PTR [rsp+0x58]
     +0x288  mov     esi, DWORD PTR [rsp+0x4c]
     +0x28c  mov     ecx, 0x88
     +0x291  mov     rdi, QWORD PTR [rsp+0x28]
     +0x296  mov     ebx, eax
     +0x298  call    mld_rej_eta_c65
     after_mld_rej_eta_c65_8:
     +0x29d  cmp     r13d, 0xff
     +0x2a4  mov     r10d, eax
     +0x2a7  setbe   al
     +0x2aa  cmp     r12d, 0xff
     join2:
     +0x2b1  setbe   dl
     +0x2b4  or      eax, edx
     +0x2b6  cmp     ebx, 0xff
     +0x2bc  setbe   dl
     +0x2bf  or      al, dl
     +0x2c1  jne     join1
     +0x2c7  cmp     r10d, 0xff
     +0x2ce  jbe     join1
     +0x2d4  mov     rdi, QWORD PTR [rsp+0x20]
     +0x2d9  call    mldsa_shake256x4_release
     after_mldsa_shake256x4_release:
     +0x2de  xor     eax, eax
     +0x2e0  mov     rdi, r14
     +0x2e3  mov     ecx, 0x90
     +0x2e8  rep stos QWORD PTR es:[rdi], rax
     +0x2eb  mov     rdi, QWORD PTR [rsp+0x18]
     +0x2f0  mov     ecx, 0x30
     +0x2f5  rep stos QWORD PTR es:[rdi], rax
     +0x2f8  mov     rdi, QWORD PTR [rsp+0x18]
     +0x2fd  lea     rsp, [rbp-0x28]
     +0x301  pop     rbx
     +0x302  pop     r12
     +0x304  pop     r13
     +0x306  pop     r14
     +0x308  pop     r15
     +0x30a  pop     rbp
     ret:
     +0x30b  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_uniform_eta_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j        *)
(* becomes mld_poly_uniform_eta 4 sd of the nonce j, the low byte of nj, if  *)
(* the SHAKE256 output of the extended seed has 256 acceptable nibbles. The  *)
(* nonces n1, n2 and n3 are in the 8 bytes each above the return address.    *)
(* The function saves RBP, the frame pointer, and five more registers below  *)
(* the return address, lowers RSP by up to 31 bytes to align it to 32 bytes, *)
(* and then reserves 2432 bytes for the arguments, the extended seeds, the   *)
(* buffers and the state, below which the call of                            *)
(* mldsa_shake256x4_absorb_once uses 424 bytes, with its return address:     *)
(* 2935 bytes of stack below the return address in all.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n3) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2935),2935)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the stack and the lists of the    *)
(* values that mld_rej_eta_c declassifies for each polynomial, with all      *)
(* accesses within the arguments, the stack, the return address and the      *)
(* stack arguments and the round constants of Keccak, and the writes within  *)
(* the polynomials and the stack.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n3) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            pc (word_sub stackpointer (word 2935))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2935),2935; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2935),2935]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2935),2935)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2935),2935)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            pc (word_sub stackpointer (word 2935))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2935),2935; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2935),2935]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2935),2935)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
