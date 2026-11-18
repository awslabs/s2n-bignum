(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa44_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 16 entries four at a time with  *)
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

    mldsa44_polyvec_matrix_expand_eager:
       +0x0: stp     x19, x20, [sp, #-352]!
       +0x4: adrp    x3, <page>
       +0x8: ldr     x3, [x3, #4088]
       +0xc: add     x20, sp, #0x5f
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: and     x20, x20, #0xffffffffffffffe0
      +0x18: mov     x2, x20
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x24, x0
      +0x24: add     x0, x20, #0x100
      +0x28: stp     x25, x30, [sp, #48]
      +0x2c: ldr     x4, [x3]
      +0x30: str     x4, [sp, #344]
      +0x34: mov     x4, #0x0
      +0x38: ldp     q0, q1, [x1]
      +0x3c: stp     q0, q1, [x2]
      +0x40: add     x2, x2, #0x40
      +0x44: cmp     x0, x2
      +0x48: b.ne    <+0x38>
      +0x4c: mov     w19, #0x4
      +0x50: mov     w25, #0x1000
      +0x54: mov     x23, #0xc00
      +0x58: mov     x22, #0x800
      +0x5c: mov     x21, #0x400
      +0x60: sub     w5, w19, #0x4
      +0x64: mov     x2, x20
      +0x68: mov     w1, w5
      +0x6c: and     w4, w1, #0x3
      +0x70: lsr     w3, w1, #2
      +0x74: add     w1, w1, #0x1
      +0x78: strb    w4, [x2, #32]
      +0x7c: strb    w3, [x2, #33]
      +0x80: add     x2, x2, #0x40
      +0x84: cmp     w19, w1
      +0x88: b.ne    <+0x6c>
      +0x8c: sub     w3, w19, #0x1
      +0x90: sub     w2, w19, #0x2
      +0x94: sub     w1, w19, #0x3
      +0x98: lsr     w5, w5, #2
      +0x9c: lsr     w3, w3, #2
      +0xa0: lsr     w2, w2, #2
      +0xa4: lsr     w1, w1, #2
      +0xa8: add     w19, w19, #0x4
      +0xac: add     x0, x24, x5, lsl #12
      +0xb0: mov     x4, x20
      +0xb4: umaddl  x3, w3, w25, x23
      +0xb8: umaddl  x2, w2, w25, x22
      +0xbc: umaddl  x1, w1, w25, x21
      +0xc0: add     x3, x24, x3
      +0xc4: add     x2, x24, x2
      +0xc8: add     x1, x24, x1
      +0xcc: bl      <mldsa_poly_uniform_4x>
      +0xd0: cmp     w19, #0x14
      +0xd4: b.ne    <+0x60>
      +0xd8: movi    v0.4s, #0x0
      +0xdc: stp     q0, q0, [x20]
      +0xe0: stp     q0, q0, [x20, #32]
      +0xe4: stp     q0, q0, [x20, #64]
      +0xe8: stp     q0, q0, [x20, #96]
      +0xec: stp     q0, q0, [x20, #128]
      +0xf0: stp     q0, q0, [x20, #160]
      +0xf4: stp     q0, q0, [x20, #192]
      +0xf8: stp     q0, q0, [x20, #224]
      +0xfc: adrp    x0, <page>
     +0x100: ldr     x0, [x0, #4088]
     +0x104: ldr     x2, [sp, #344]
     +0x108: ldr     x1, [x0]
     +0x10c: subs    x2, x2, x1
     +0x110: mov     x1, #0x0
     +0x114: b.ne    <+0x12c>
     +0x118: ldp     x21, x22, [sp, #16]
     +0x11c: ldp     x23, x24, [sp, #32]
     +0x120: ldp     x25, x30, [sp, #48]
     +0x124: ldp     x19, x20, [sp], #352
     +0x128: ret
     +0x12c: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (used by the callee). The   *)
(* 32 bytes r of rho; the matrix at mat, 4 rows of 4 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 4 r if sampling terminates for each entry. The  *)
(* stack is the 352 bytes of the function and the 4720 of the callee below   *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5072),5072) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5072),5072)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa44_polyvec_matrix_expand_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [mat; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    !n. n < 4096
                        ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                              s = mld_polyvec_matrix_expand 4 r n)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,16384);
                  memory :> bytes(word_sub stackpointer (word 5072),5072)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5072),5072) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5072),5072)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa44_polyvec_matrix_expand_eager) /\
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
                    (!n. n < 4096
                         ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                               s = mld_polyvec_matrix_expand 4 r n) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events mat rho r guard mf pc
                              (word_sub stackpointer (word 5072))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,16384;
                         word_sub stackpointer (word 5072),5072;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,16384; word_sub stackpointer (word 5072),5072]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,16384);
                  memory :> bytes(word_sub stackpointer (word 5072),5072)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5072),5072) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5072),5072)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word (pc + mldsa44_polyvec_matrix_expand_eager) /\
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
                              (word_sub stackpointer (word 5072))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,16384;
                         word_sub stackpointer (word 5072),5072;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,16384; word_sub stackpointer (word 5072),5072]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,16384);
                  memory :> bytes(word_sub stackpointer (word 5072),5072)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
