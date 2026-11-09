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
(* coefficients, before zeroing the state and the buffers. It is verified in *)
(* the whole image (see libmldsa.ml) against mld_poly_uniform_eta of         *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_absorb_once_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/rej_eta_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_poly_uniform_eta_4x:
       +0x0: sub     sp, sp, #0x9d0
       +0x4: mov     x8, x4
       +0x8: adrp    x4, <page>
       +0xc: ldr     x4, [x4, #4088]
      +0x10: stp     x19, x20, [sp]
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x22, sp, #0xaf
      +0x1c: and     x22, x22, #0xffffffffffffffe0
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: add     x9, x22, #0x480
      +0x28: add     x19, x22, #0x4e0
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: add     x20, x22, #0x540
      +0x34: add     x21, x22, #0x5a0
      +0x38: stp     x27, x28, [sp, #64]
      +0x3c: add     x26, sp, #0x6a8
      +0x40: mov     x28, x9
      +0x44: str     x30, [sp, #80]
      +0x48: add     x23, x22, #0x360
      +0x4c: str     x9, [sp, #136]
      +0x50: add     x24, x22, #0x240
      +0x54: ldp     q2, q3, [x8, #32]
      +0x58: add     x25, x22, #0x120
      +0x5c: ldp     q0, q1, [x8]
      +0x60: ldr     x8, [x4]
      +0x64: str     x8, [sp, #2504]
      +0x68: mov     x8, #0x0
      +0x6c: ldrb    w4, [sp, #2512]
      +0x70: mov     w27, #0xff
      +0x74: stp     q2, q3, [x9, #32]
      +0x78: stp     q2, q3, [x19, #32]
      +0x7c: stp     q0, q1, [x19]
      +0x80: stp     q0, q1, [x20]
      +0x84: stp     q2, q3, [x20, #32]
      +0x88: stp     x0, x1, [sp, #104]
      +0x8c: mov     x0, x26
      +0x90: stp     x2, x3, [sp, #120]
      +0x94: stp     q0, q1, [x21]
      +0x98: stp     q2, q3, [x21, #32]
      +0x9c: stp     q0, q1, [x9]
      +0xa0: strb    w5, [x9, #64]
      +0xa4: strb    wzr, [x9, #65]
      +0xa8: strb    w6, [x9, #160]
      +0xac: strb    wzr, [x9, #161]
      +0xb0: strb    w7, [x9, #256]
      +0xb4: strb    wzr, [x9, #257]
      +0xb8: strb    w4, [x9, #352]
      +0xbc: strb    wzr, [x9, #353]
      +0xc0: bl      <mldsa_shake256x4_init>
      +0xc4: mov     x4, x21
      +0xc8: mov     x3, x20
      +0xcc: mov     x2, x19
      +0xd0: mov     x1, x28
      +0xd4: mov     x0, x26
      +0xd8: mov     x5, #0x42
      +0xdc: bl      <mldsa_shake256x4_absorb_once>
      +0xe0: mov     x5, x26
      +0xe4: mov     x4, #0x2
      +0xe8: mov     x3, x23
      +0xec: mov     x2, x24
      +0xf0: mov     x1, x25
      +0xf4: mov     x0, x22
      +0xf8: bl      <mldsa_shake256x4_squeezeblocks>
      +0xfc: ldr     x0, [sp, #104]
     +0x100: mov     w3, #0x110
     +0x104: mov     x2, x22
     +0x108: mov     w1, #0x0
     +0x10c: bl      <mld_rej_eta_c65>
     +0x110: mov     w19, w0
     +0x114: ldr     x0, [sp, #112]
     +0x118: mov     x2, x25
     +0x11c: mov     w1, #0x0
     +0x120: bl      <mld_rej_eta_c65>
     +0x124: mov     w20, w0
     +0x128: ldr     x0, [sp, #120]
     +0x12c: mov     x2, x24
     +0x130: mov     w1, #0x0
     +0x134: bl      <mld_rej_eta_c65>
     +0x138: mov     w21, w0
     +0x13c: ldr     x0, [sp, #128]
     +0x140: mov     w1, #0x0
     +0x144: mov     x2, x23
     +0x148: bl      <mld_rej_eta_c65>
     +0x14c: mov     w28, w0
     +0x150: cmp     w21, w27
     +0x154: ccmp    w0, w27, #0x0, hi
     +0x158: cset    w0, ls
     +0x15c: cmp     w20, w27
     +0x160: ccmp    w19, w27, #0x0, hi
     +0x164: cset    w1, ls
     +0x168: orr     w0, w0, w1
     +0x16c: cbz     w0, <mldsa65_poly_uniform_eta_4x+0x200>
     +0x170: mov     x5, x26
     +0x174: mov     x4, #0x1
     +0x178: mov     x3, x23
     +0x17c: mov     x2, x24
     +0x180: mov     x1, x25
     +0x184: mov     x0, x22
     +0x188: bl      <mldsa_shake256x4_squeezeblocks>
     +0x18c: ldr     x0, [sp, #104]
     +0x190: mov     w3, #0x88
     +0x194: mov     w1, w19
     +0x198: mov     x2, x22
     +0x19c: bl      <mld_rej_eta_c65>
     +0x1a0: mov     w19, w0
     +0x1a4: ldr     x0, [sp, #112]
     +0x1a8: mov     w1, w20
     +0x1ac: mov     x2, x25
     +0x1b0: bl      <mld_rej_eta_c65>
     +0x1b4: mov     w20, w0
     +0x1b8: ldr     x0, [sp, #120]
     +0x1bc: mov     w1, w21
     +0x1c0: mov     x2, x24
     +0x1c4: bl      <mld_rej_eta_c65>
     +0x1c8: mov     w21, w0
     +0x1cc: ldr     x0, [sp, #128]
     +0x1d0: mov     w1, w28
     +0x1d4: mov     x2, x23
     +0x1d8: bl      <mld_rej_eta_c65>
     +0x1dc: cmp     w0, #0xff
     +0x1e0: ccmp    w21, w27, #0x0, hi
     +0x1e4: mov     w28, w0
     +0x1e8: cset    w0, ls
     +0x1ec: cmp     w19, #0xff
     +0x1f0: ccmp    w20, w27, #0x0, hi
     +0x1f4: cset    w1, ls
     +0x1f8: orr     w0, w0, w1
     +0x1fc: cbnz    w0, <mldsa65_poly_uniform_eta_4x+0x170>
     +0x200: mov     x0, x26
     +0x204: bl      <mldsa_shake256x4_release>
     +0x208: mov     x0, x22
     +0x20c: mov     x2, #0x480
     +0x210: mov     w1, #0x0
     +0x214: bl      <memset@plt>
     +0x218: ldr     x19, [sp, #136]
     +0x21c: mov     x2, #0x180
     +0x220: mov     w1, #0x0
     +0x224: mov     x0, x19
     +0x228: bl      <memset@plt>
     +0x22c: adrp    x0, <page>
     +0x230: ldr     x0, [x0, #4088]
     +0x234: ldr     x2, [sp, #2504]
     +0x238: ldr     x1, [x0]
     +0x23c: subs    x2, x2, x1
     +0x240: mov     x1, #0x0
     +0x244: b.ne    <mldsa65_poly_uniform_eta_4x+0x268>
     +0x248: ldp     x19, x20, [sp]
     +0x24c: ldp     x21, x22, [sp, #16]
     +0x250: ldp     x23, x24, [sp, #32]
     +0x254: ldp     x25, x26, [sp, #48]
     +0x258: ldp     x27, x28, [sp, #64]
     +0x25c: ldr     x30, [sp, #80]
     +0x260: add     sp, sp, #0x9d0
     +0x264: ret
     +0x268: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_uniform_eta_4x"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_eta 4 sd of the     *)
(* nonce j, if the SHAKE256 output of the extended seed has 256 acceptable   *)
(* nibbles. The stack is the 2512 bytes of the function and the 304 below    *)
(* them of mldsa_shake256x4_absorb_once, and the fourth nonce is the byte at *)
(* the stack pointer.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2816),2816)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset, the stack  *)
(* and the lists of the values that mld_rej_eta_c declassifies for each      *)
(* polynomial, with all accesses within the arguments, the stack, the GOT    *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomials and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd n3 i) /\
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
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2816))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2816),2816;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2816),2816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2816),2816)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2816),2816)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2816))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2816),2816;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2816),2816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2816),2816)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
