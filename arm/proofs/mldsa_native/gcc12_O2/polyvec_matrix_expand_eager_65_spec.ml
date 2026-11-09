(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa65_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack, samples 28 of the 30 entries four at a time    *)
(* with mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), and *)
(* the last two with mldsa_poly_uniform, before zeroing the buffers. It is   *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_polyvec_matrix_expand of common/mldsa_native_sampling.ml, using the   *)
(* theorems for the callees, assuming that sampling terminates for           *)
(* each entry (mld_matrix_terminates), and shown to be constant time and     *)
(* memory safe, with the events depending on rho, which is public.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_expand_eager:
       +0x0: stp     x19, x20, [sp, #-336]!
       +0x4: adrp    x3, <page>
       +0x8: ldr     x3, [x3, #4088]
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x21, x0
      +0x14: stp     x23, x30, [sp, #32]
      +0x18: add     x23, sp, #0x4f
      +0x1c: and     x23, x23, #0xffffffffffffffe0
      +0x20: add     x2, x23, #0x100
      +0x24: mov     x0, x23
      +0x28: ldr     x4, [x3]
      +0x2c: str     x4, [sp, #328]
      +0x30: mov     x4, #0x0
      +0x34: ldp     q0, q1, [x1]
      +0x38: stp     q0, q1, [x0]
      +0x3c: add     x0, x0, #0x40
      +0x40: cmp     x2, x0
      +0x44: b.ne    <+0x34>
      +0x48: mov     w20, #0xcccd
      +0x4c: mov     w19, #0x4
      +0x50: movk    w20, #0xcccc, lsl #16
      +0x54: mov     w22, #0x5
      +0x58: sub     w0, w19, #0x4
      +0x5c: mov     x3, x23
      +0x60: mov     w2, w0
      +0x64: umull   x1, w2, w20
      +0x68: add     x3, x3, #0x40
      +0x6c: lsr     x1, x1, #34
      +0x70: sturb   w1, [x3, #-31]
      +0x74: add     w1, w1, w1, lsl #2
      +0x78: sub     w1, w2, w1
      +0x7c: add     w2, w2, #0x1
      +0x80: sturb   w1, [x3, #-32]
      +0x84: cmp     w19, w2
      +0x88: b.ne    <+0x64>
      +0x8c: sub     w8, w19, #0x3
      +0x90: sub     w7, w19, #0x2
      +0x94: sub     w6, w19, #0x1
      +0x98: umull   x5, w0, w20
      +0x9c: add     w19, w19, #0x4
      +0xa0: mov     x4, x23
      +0xa4: umull   x1, w8, w20
      +0xa8: umull   x2, w7, w20
      +0xac: lsr     x5, x5, #34
      +0xb0: umull   x3, w6, w20
      +0xb4: lsr     x1, x1, #34
      +0xb8: add     w9, w5, w5, lsl #2
      +0xbc: lsr     x2, x2, #34
      +0xc0: sub     w0, w0, w9
      +0xc4: lsr     x3, x3, #34
      +0xc8: add     w9, w1, w1, lsl #2
      +0xcc: add     w10, w2, w2, lsl #2
      +0xd0: sub     w8, w8, w9
      +0xd4: add     w9, w3, w3, lsl #2
      +0xd8: sub     w7, w7, w10
      +0xdc: sub     w6, w6, w9
      +0xe0: umaddl  x0, w5, w22, x0
      +0xe4: umaddl  x1, w1, w22, x8
      +0xe8: umaddl  x2, w2, w22, x7
      +0xec: umaddl  x3, w3, w22, x6
      +0xf0: add     x0, x21, x0, lsl #10
      +0xf4: add     x1, x21, x1, lsl #10
      +0xf8: add     x2, x21, x2, lsl #10
      +0xfc: add     x3, x21, x3, lsl #10
     +0x100: bl      <mldsa_poly_uniform_4x>
     +0x104: cmp     w19, #0x20
     +0x108: b.ne    <+0x58>
     +0x10c: mov     w2, #0x503
     +0x110: mov     x1, x23
     +0x114: add     x0, x21, #0x7, lsl #12
     +0x118: strh    w2, [x23, #32]
     +0x11c: bl      <mldsa_poly_uniform>
     +0x120: mov     w2, #0x504
     +0x124: mov     x1, x23
     +0x128: mov     x0, #0x7400
     +0x12c: add     x0, x21, x0
     +0x130: strh    w2, [x23, #32]
     +0x134: bl      <mldsa_poly_uniform>
     +0x138: movi    v0.4s, #0x0
     +0x13c: stp     q0, q0, [x23]
     +0x140: stp     q0, q0, [x23, #32]
     +0x144: stp     q0, q0, [x23, #64]
     +0x148: stp     q0, q0, [x23, #96]
     +0x14c: stp     q0, q0, [x23, #128]
     +0x150: stp     q0, q0, [x23, #160]
     +0x154: stp     q0, q0, [x23, #192]
     +0x158: stp     q0, q0, [x23, #224]
     +0x15c: adrp    x0, <page>
     +0x160: ldr     x0, [x0, #4088]
     +0x164: ldr     x2, [sp, #328]
     +0x168: ldr     x1, [x0]
     +0x16c: subs    x2, x2, x1
     +0x170: mov     x1, #0x0
     +0x174: b.ne    <+0x188>
     +0x178: ldp     x21, x22, [sp, #16]
     +0x17c: ldp     x23, x30, [sp, #32]
     +0x180: ldp     x19, x20, [sp], #336
     +0x184: ret
     +0x188: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (used by the callee). The   *)
(* 32 bytes r of rho; the matrix at mat, 6 rows of 5 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 5 r if sampling terminates for each entry. The  *)
(* stack is the 336 bytes of the function and the 4720 of the callees below  *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa65_polyvec_matrix_expand_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [mat; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    !n. n < 7680
                        ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                              s = mld_polyvec_matrix_expand 5 r n)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,30720);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa65_polyvec_matrix_expand_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [mat; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!n. n < 7680
                         ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                               s = mld_polyvec_matrix_expand 5 r n) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events mat rho r guard mf pc
                              (word_sub stackpointer (word 5056))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,30720;
                         word_sub stackpointer (word 5056),5056;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,30720; word_sub stackpointer (word 5056),5056]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,30720);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa65_polyvec_matrix_expand_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [mat; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events mat rho r guard mf pc
                              (word_sub stackpointer (word 5056))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,30720;
                         word_sub stackpointer (word 5056),5056;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,30720; word_sub stackpointer (word 5056),5056]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,30720);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
