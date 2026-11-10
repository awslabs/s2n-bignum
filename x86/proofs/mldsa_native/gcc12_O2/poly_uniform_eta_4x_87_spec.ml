(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-87 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa87_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which extends the seed of 64 bytes with each of  *)
(* the four nonce bytes and a zero byte, absorbs the four into a fourfold    *)
(* SHAKE256 state, squeezes 1 block of 136 bytes of each and samples the     *)
(* coefficients from them with mld_rej_eta_c87, and then squeezes one more   *)
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
needs "x86/proofs/mldsa_native/gcc12_O2/rej_eta_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_poly_uniform_eta_4x:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0x780
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
     +0x10d  lea     rax, [rsp+0x460]
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
     +0x15a  lea     r14, [rsp+0x1e0]
     +0x162  lea     r11, [rsp+0x320]
     +0x16a  mov     r9, rbx
     +0x16d  mov     rdx, r11
     +0x170  mov     r8d, 0x1
     +0x176  mov     rdi, r14
     +0x179  mov     rbx, r11
     +0x17c  lea     rax, [rsp+0x3c0]
     +0x184  lea     r15, [rsp+0x280]
     +0x18c  mov     QWORD PTR [rsp+0x50], r11
     +0x191  mov     rcx, rax
     +0x194  mov     rsi, r15
     +0x197  mov     QWORD PTR [rsp+0x58], rax
     +0x19c  call    mldsa_shake256x4_squeezeblocks
     after_mldsa_shake256x4_squeezeblocks_1:
     +0x1a1  mov     rdi, QWORD PTR [rsp+0x40]
     +0x1a6  xor     esi, esi
     +0x1a8  mov     rdx, r14
     +0x1ab  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_1:
     +0x1b0  mov     rdi, QWORD PTR [rsp+0x38]
     +0x1b5  xor     esi, esi
     +0x1b7  mov     rdx, r15
     +0x1ba  mov     r13d, eax
     +0x1bd  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_2:
     +0x1c2  mov     rdi, QWORD PTR [rsp+0x30]
     +0x1c7  mov     rdx, rbx
     +0x1ca  xor     esi, esi
     +0x1cc  mov     r12d, eax
     +0x1cf  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_3:
     +0x1d4  mov     rdx, QWORD PTR [rsp+0x58]
     +0x1d9  mov     rdi, QWORD PTR [rsp+0x28]
     +0x1de  xor     esi, esi
     +0x1e0  mov     ebx, eax
     +0x1e2  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_4:
     +0x1e7  cmp     r12d, 0xff
     +0x1ee  mov     r10d, eax
     +0x1f1  setbe   al
     +0x1f4  cmp     r13d, 0xff
     +0x1fb  jmp     loop1
     join1:
     +0x200  mov     r9, QWORD PTR [rsp+0x20]
     +0x205  mov     rcx, QWORD PTR [rsp+0x58]
     +0x20a  mov     rsi, r15
     +0x20d  mov     rdi, r14
     +0x210  mov     rdx, QWORD PTR [rsp+0x50]
     +0x215  mov     r8d, 0x1
     +0x21b  mov     DWORD PTR [rsp+0x4c], r10d
     +0x220  call    mldsa_shake256x4_squeezeblocks
     after_mldsa_shake256x4_squeezeblocks_2:
     +0x225  mov     rdi, QWORD PTR [rsp+0x40]
     +0x22a  mov     esi, r13d
     +0x22d  mov     rdx, r14
     +0x230  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_5:
     +0x235  mov     rdi, QWORD PTR [rsp+0x38]
     +0x23a  mov     esi, r12d
     +0x23d  mov     rdx, r15
     +0x240  mov     r13d, eax
     +0x243  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_6:
     +0x248  mov     rdx, QWORD PTR [rsp+0x50]
     +0x24d  mov     rdi, QWORD PTR [rsp+0x30]
     +0x252  mov     esi, ebx
     +0x254  mov     r12d, eax
     +0x257  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_7:
     +0x25c  mov     rdx, QWORD PTR [rsp+0x58]
     +0x261  mov     esi, DWORD PTR [rsp+0x4c]
     +0x265  mov     rdi, QWORD PTR [rsp+0x28]
     +0x26a  mov     ebx, eax
     +0x26c  call    mld_rej_eta_c87
     after_mld_rej_eta_c87_8:
     +0x271  cmp     r13d, 0xff
     +0x278  mov     r10d, eax
     +0x27b  setbe   al
     loop1_back:
     +0x27e  cmp     r12d, 0xff
     loop1:
     +0x285  setbe   dl
     +0x288  or      eax, edx
     +0x28a  cmp     ebx, 0xff
     +0x290  setbe   dl
     +0x293  or      al, dl
     +0x295  jne     join1
     loop1_test:
     +0x29b  cmp     r10d, 0xff
     +0x2a2  jbe     join1
     loop1_exit:
     +0x2a8  mov     rdi, QWORD PTR [rsp+0x20]
     +0x2ad  call    mldsa_shake256x4_release
     after_mldsa_shake256x4_release:
     +0x2b2  xor     eax, eax
     +0x2b4  mov     rdi, r14
     +0x2b7  mov     ecx, 0x50
     +0x2bc  rep stos QWORD PTR es:[rdi], rax
     +0x2bf  mov     rdi, QWORD PTR [rsp+0x18]
     +0x2c4  mov     ecx, 0x30
     +0x2c9  rep stos QWORD PTR es:[rdi], rax
     +0x2cc  mov     rdi, QWORD PTR [rsp+0x18]
     +0x2d1  lea     rsp, [rbp-0x28]
     +0x2d5  pop     rbx
     +0x2d6  pop     r12
     +0x2d8  pop     r13
     +0x2da  pop     r14
     +0x2dc  pop     r15
     +0x2de  pop     rbp
     ret:
     +0x2df  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_poly_uniform_eta_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j        *)
(* becomes mld_poly_uniform_eta 2 sd of the nonce j, the low byte of nj, if  *)
(* the SHAKE256 output of the extended seed has 256 acceptable nibbles. The  *)
(* nonces n1, n2 and n3 are in the 8 bytes each above the return address.    *)
(* The function saves RBP, the frame pointer, and five more registers below  *)
(* the return address, lowers RSP by up to 31 bytes to align it to 32 bytes, *)
(* and then reserves 1920 bytes for the arguments, the extended seeds, the   *)
(* buffers and the state, below which the call of                            *)
(* mldsa_shake256x4_absorb_once uses 424 bytes, with its return address:     *)
(* 2423 bytes of stack below the return address in all.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
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
                             s = mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n3) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2423),2423)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the stack and the lists of the    *)
(* values that mld_rej_eta_c declassifies for each polynomial, with all      *)
(* accesses within the arguments, the stack, the return address and the      *)
(* stack arguments and the round constants of Keccak, and the writes within  *)
(* the polynomials and the stack.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
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
                             s = mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n3) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            pc (word_sub stackpointer (word 2423))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2423),2423; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2423),2423]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2423),2423)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2423),2423)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
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
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            pc (word_sub stackpointer (word 2423))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2423),2423; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2423),2423]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2423),2423)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
