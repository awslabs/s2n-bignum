(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa87_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 56 entries four at a time with  *)
(* mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), before   *)
(* zeroing the buffers. It is verified in the whole image (see libmldsa.ml)  *)
(* against mld_polyvec_matrix_expand of common/mldsa_native_sampling.ml,     *)
(* using the theorems for the callee, assuming that sampling terminates for  *)
(* each entry (mld_matrix_terminates), and shown to be constant time and     *)
(* memory safe, with the events depending on rho, which is public.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvec_matrix_expand_eager:
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
      +0x48: mov     w20, #0x4925
      +0x4c: mov     w19, #0x4
      +0x50: movk    w20, #0x2492, lsl #16
      +0x54: mov     w22, #0x7
      +0x58: sub     w6, w19, #0x4
      +0x5c: mov     x5, x23
      +0x60: mov     w2, w6
      +0x64: umull   x3, w2, w20
      +0x68: add     x5, x5, #0x40
      +0x6c: lsr     x3, x3, #32
      +0x70: sub     w1, w2, w3
      +0x74: add     w1, w3, w1, lsr #1
      +0x78: lsr     w1, w1, #2
      +0x7c: sturb   w1, [x5, #-31]
      +0x80: lsl     w3, w1, #3
      +0x84: sub     w1, w3, w1
      +0x88: sub     w1, w2, w1
      +0x8c: add     w2, w2, #0x1
      +0x90: sturb   w1, [x5, #-32]
      +0x94: cmp     w19, w2
      +0x98: b.ne    <+0x64>
      +0x9c: sub     w9, w19, #0x3
      +0xa0: sub     w8, w19, #0x2
      +0xa4: sub     w7, w19, #0x1
      +0xa8: umull   x10, w6, w20
      +0xac: add     w19, w19, #0x4
      +0xb0: mov     x4, x23
      +0xb4: umull   x12, w9, w20
      +0xb8: umull   x11, w8, w20
      +0xbc: lsr     x10, x10, #32
      +0xc0: umull   x5, w7, w20
      +0xc4: sub     w0, w6, w10
      +0xc8: lsr     x12, x12, #32
      +0xcc: lsr     x11, x11, #32
      +0xd0: sub     w1, w9, w12
      +0xd4: lsr     x5, x5, #32
      +0xd8: sub     w2, w8, w11
      +0xdc: sub     w3, w7, w5
      +0xe0: add     w1, w12, w1, lsr #1
      +0xe4: add     w2, w11, w2, lsr #1
      +0xe8: add     w0, w10, w0, lsr #1
      +0xec: add     w3, w5, w3, lsr #1
      +0xf0: lsr     w1, w1, #2
      +0xf4: lsr     w2, w2, #2
      +0xf8: lsr     w0, w0, #2
      +0xfc: lsr     w3, w3, #2
     +0x100: lsl     w12, w1, #3
     +0x104: lsl     w11, w2, #3
     +0x108: lsl     w5, w0, #3
     +0x10c: lsl     w10, w3, #3
     +0x110: sub     w12, w12, w1
     +0x114: sub     w11, w11, w2
     +0x118: sub     w10, w10, w3
     +0x11c: sub     w5, w5, w0
     +0x120: sub     w9, w9, w12
     +0x124: sub     w8, w8, w11
     +0x128: sub     w7, w7, w10
     +0x12c: sub     w5, w6, w5
     +0x130: umaddl  x1, w1, w22, x9
     +0x134: umaddl  x2, w2, w22, x8
     +0x138: umaddl  x3, w3, w22, x7
     +0x13c: umaddl  x0, w0, w22, x5
     +0x140: add     x1, x21, x1, lsl #10
     +0x144: add     x2, x21, x2, lsl #10
     +0x148: add     x3, x21, x3, lsl #10
     +0x14c: add     x0, x21, x0, lsl #10
     +0x150: bl      <mldsa_poly_uniform_4x>
     +0x154: cmp     w19, #0x3c
     +0x158: b.ne    <+0x58>
     +0x15c: movi    v0.4s, #0x0
     +0x160: stp     q0, q0, [x23]
     +0x164: stp     q0, q0, [x23, #32]
     +0x168: stp     q0, q0, [x23, #64]
     +0x16c: stp     q0, q0, [x23, #96]
     +0x170: stp     q0, q0, [x23, #128]
     +0x174: stp     q0, q0, [x23, #160]
     +0x178: stp     q0, q0, [x23, #192]
     +0x17c: stp     q0, q0, [x23, #224]
     +0x180: adrp    x0, <page>
     +0x184: ldr     x0, [x0, #4088]
     +0x188: ldr     x2, [sp, #328]
     +0x18c: ldr     x1, [x0]
     +0x190: subs    x2, x2, x1
     +0x194: mov     x1, #0x0
     +0x198: b.ne    <+0x1ac>
     +0x19c: ldp     x21, x22, [sp, #16]
     +0x1a0: ldp     x23, x30, [sp, #32]
     +0x1a4: ldp     x19, x20, [sp], #336
     +0x1a8: ret
     +0x1ac: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (used by the callee). The   *)
(* 32 bytes r of rho; the matrix at mat, 8 rows of 7 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 7 r if sampling terminates for each entry. The  *)
(* stack is the 336 bytes of the function and the 4720 of the callees below  *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa87_polyvec_matrix_expand_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [mat; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    !n. n < 14336
                        ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                              s = mld_polyvec_matrix_expand 7 r n)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,57344);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa87_polyvec_matrix_expand_eager) /\
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
                    (!n. n < 14336
                         ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                               s = mld_polyvec_matrix_expand 7 r n) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events mat rho r guard mf pc
                              (word_sub stackpointer (word 5056))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,57344;
                         word_sub stackpointer (word 5056),5056;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,57344; word_sub stackpointer (word 5056),5056]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,57344);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5056),5056) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5056),5056)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa87_polyvec_matrix_expand_eager) /\
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
                        [rho,32; mat,57344;
                         word_sub stackpointer (word 5056),5056;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,57344; word_sub stackpointer (word 5056),5056]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,57344);
                  memory :> bytes(word_sub stackpointer (word 5056),5056)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
