(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-44 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa44_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which extends the seed of 64 bytes with each of  *)
(* the four nonce bytes and a zero byte, absorbs the four into a fourfold    *)
(* SHAKE256 state, squeezes 1 block of 136 bytes of each and samples the     *)
(* coefficients from them with mld_rej_eta_c44, and then squeezes one more   *)
(* block of each and samples from all four until each polynomial has 256     *)
(* coefficients, before releasing the state and zeroing the buffers with two *)
(* calls of mld_zeroize_1 (which calls memset). It is verified in the whole  *)
(* image (see libmldsa.ml) against mld_poly_uniform_eta of                   *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset, and assuming that the SHAKE256 output of each extended seed has   *)
(* 256 acceptable nibbles (mld_rej_eta_terminates), without which the code   *)
(* does not terminate. The first three nonces are the low bytes of the sixth *)
(* to eighth arguments, the fourth the byte that the caller puts on the      *)
(* stack. It is also shown to be constant time and memory safe, with the     *)
(* events depending on the seed only through which nibbles of the SHAKE256   *)
(* outputs mld_rej_eta_c accepts, which it declassifies                      *)
(* (mld_poly_uniform_eta_declass).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_absorb_once_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/rej_eta_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_1_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_uniform_eta_4x:
       +0x0: sub     sp, sp, #0x7c0
       +0x4: stp     x19, x20, [sp]
       +0x8: add     x19, sp, #0x9f
       +0xc: and     x19, x19, #0xffffffffffffffe0
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x20, x19, #0x2e0
      +0x18: add     x21, x19, #0x340
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: add     x24, x19, #0x280
      +0x24: add     x22, x19, #0x3a0
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: add     x23, sp, #0x498
      +0x30: mov     x25, x3
      +0x34: stp     x27, x28, [sp, #64]
      +0x38: add     x26, x19, #0x1e0
      +0x3c: add     x27, x19, #0x140
      +0x40: str     x30, [sp, #80]
      +0x44: add     x28, x19, #0xa0
      +0x48: stp     x0, x1, [sp, #96]
      +0x4c: ldp     q0, q1, [x4, #32]
      +0x50: str     x2, [sp, #112]
      +0x54: adrp    x0, <page>
      +0x58: ldr     x0, [x0, #4088]
      +0x5c: ldp     q2, q3, [x4]
      +0x60: ldr     x1, [x0]
      +0x64: str     x1, [sp, #1976]
      +0x68: mov     x1, #0x0
      +0x6c: stp     q0, q1, [x20, #32]
      +0x70: stp     q0, q1, [x24, #32]
      +0x74: stp     q2, q3, [x20]
      +0x78: stp     q2, q3, [x21]
      +0x7c: stp     q2, q3, [x24]
      +0x80: stp     q0, q1, [x21, #32]
      +0x84: stp     q2, q3, [x22]
      +0x88: ldrb    w0, [sp, #1984]
      +0x8c: stp     q0, q1, [x22, #32]
      +0x90: strb    w5, [x24, #64]
      +0x94: strb    wzr, [x24, #65]
      +0x98: strb    w6, [x24, #160]
      +0x9c: strb    wzr, [x24, #161]
      +0xa0: strb    w7, [x24, #256]
      +0xa4: strb    wzr, [x24, #257]
      +0xa8: strb    w0, [x24, #352]
      +0xac: mov     x0, x23
      +0xb0: strb    wzr, [x24, #353]
      +0xb4: bl      <mldsa_shake256x4_init>
      +0xb8: mov     x4, x22
      +0xbc: mov     x3, x21
      +0xc0: mov     x2, x20
      +0xc4: mov     x1, x24
      +0xc8: mov     x0, x23
      +0xcc: mov     x5, #0x42
      +0xd0: bl      <mldsa_shake256x4_absorb_once>
      +0xd4: mov     x5, x23
      +0xd8: mov     x3, x26
      +0xdc: mov     x4, #0x1
      +0xe0: mov     x2, x27
      +0xe4: mov     x1, x28
      +0xe8: mov     x0, x19
      +0xec: bl      <mldsa_shake256x4_squeezeblocks>
      +0xf0: ldr     x0, [sp, #96]
      +0xf4: mov     x2, x19
      +0xf8: mov     w1, #0x0
      +0xfc: bl      <mld_rej_eta_c44>
     +0x100: mov     w21, w0
     +0x104: ldr     x0, [sp, #104]
     +0x108: mov     x2, x28
     +0x10c: mov     w1, #0x0
     +0x110: bl      <mld_rej_eta_c44>
     +0x114: mov     w22, w0
     +0x118: ldr     x0, [sp, #112]
     +0x11c: mov     x2, x27
     +0x120: mov     w1, #0x0
     +0x124: bl      <mld_rej_eta_c44>
     +0x128: mov     x2, x26
     +0x12c: mov     w20, w0
     +0x130: mov     w1, #0x0
     +0x134: mov     x0, x25
     +0x138: bl      <mld_rej_eta_c44>
     +0x13c: mov     w6, w0
     +0x140: cmp     w21, #0xff
     +0x144: b.ls    <mldsa44_poly_uniform_eta_4x+0x1a0>
     +0x148: cmp     w22, #0xff
     +0x14c: b.ls    <mldsa44_poly_uniform_eta_4x+0x1a0>
     +0x150: cmp     w20, #0xff
     +0x154: b.ls    <mldsa44_poly_uniform_eta_4x+0x1a0>
     +0x158: cmp     w0, #0xff
     +0x15c: b.ls    <mldsa44_poly_uniform_eta_4x+0x1a0>
     +0x160: mov     x0, x23
     +0x164: bl      <mldsa_shake256x4_release>
     +0x168: mov     x0, x19
     +0x16c: mov     x1, #0x280
     +0x170: bl      <mld_zeroize_1>
     +0x174: mov     x0, x24
     +0x178: mov     x1, #0x180
     +0x17c: bl      <mld_zeroize_1>
     +0x180: adrp    x0, <page>
     +0x184: ldr     x0, [x0, #4088]
     +0x188: ldr     x2, [sp, #1976]
     +0x18c: ldr     x1, [x0]
     +0x190: subs    x2, x2, x1
     +0x194: mov     x1, #0x0
     +0x198: b.eq    <mldsa44_poly_uniform_eta_4x+0x20c>
     +0x19c: bl      <stack_chk_fail>
     +0x1a0: mov     x5, x23
     +0x1a4: mov     x3, x26
     +0x1a8: mov     x4, #0x1
     +0x1ac: mov     x2, x27
     +0x1b0: mov     x1, x28
     +0x1b4: mov     x0, x19
     +0x1b8: str     w6, [sp, #124]
     +0x1bc: bl      <mldsa_shake256x4_squeezeblocks>
     +0x1c0: ldr     x0, [sp, #96]
     +0x1c4: mov     w1, w21
     +0x1c8: mov     x2, x19
     +0x1cc: bl      <mld_rej_eta_c44>
     +0x1d0: mov     w21, w0
     +0x1d4: ldr     x0, [sp, #104]
     +0x1d8: mov     w1, w22
     +0x1dc: mov     x2, x28
     +0x1e0: bl      <mld_rej_eta_c44>
     +0x1e4: mov     w22, w0
     +0x1e8: ldr     x0, [sp, #112]
     +0x1ec: mov     w1, w20
     +0x1f0: mov     x2, x27
     +0x1f4: bl      <mld_rej_eta_c44>
     +0x1f8: mov     x2, x26
     +0x1fc: ldr     w6, [sp, #124]
     +0x200: mov     w20, w0
     +0x204: mov     w1, w6
     +0x208: b       <mldsa44_poly_uniform_eta_4x+0x134>
     +0x20c: ldp     x19, x20, [sp]
     +0x210: ldp     x21, x22, [sp, #16]
     +0x214: ldp     x23, x24, [sp, #32]
     +0x218: ldp     x25, x26, [sp, #48]
     +0x21c: ldp     x27, x28, [sp, #64]
     +0x220: ldr     x30, [sp, #80]
     +0x224: add     sp, sp, #0x7c0
     +0x228: ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_poly_uniform_eta_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_eta 2 sd of the     *)
(* nonce j, if the SHAKE256 output of the extended seed has 256 acceptable   *)
(* nibbles. The stack is the 1984 bytes of the function and the 336 below    *)
(* them of mldsa_shake256x4_absorb_once, and the fourth nonce is the byte at *)
(* the stack pointer.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2320),2320)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset, the stack  *)
(* and the lists of the values that mld_rej_eta_c declassifies for each      *)
(* polynomial, with all accesses within the arguments, the stack, the GOT    *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomials and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd n3 i) /\
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
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2320))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2320),2320;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2320),2320]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2320),2320)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2320),2320)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
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
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2320))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2320),2320;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2320),2320]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2320),2320)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
