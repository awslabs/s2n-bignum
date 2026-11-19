(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa65_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -Os (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack, samples 28 of the 30 entries four at a time    *)
(* with mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), and *)
(* the last two with mldsa_poly_uniform, before zeroing the buffers with     *)
(* memset, which it calls through the PLT of the image. It is verified in    *)
(* the whole image (see libmldsa.ml) against mld_polyvec_matrix_expand of    *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset, assuming that sampling terminates for each entry                  *)
(* (mld_matrix_terminates), and shown to be constant time and memory safe,   *)
(* with the events depending on rho, which is public.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_uniform_4x_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_polyvec_matrix_expand_eager:
       +0x0: stp     x19, x20, [sp, #-336]!
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x22, x0
       +0xc: add     x19, sp, #0x4f
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]
      +0x18: str     x30, [sp, #32]
      +0x1c: and     x19, x19, #0xffffffffffffffe0
      +0x20: ldr     x2, [x0]
      +0x24: str     x2, [sp, #328]
      +0x28: mov     x2, #0x0
      +0x2c: mov     x0, x19
      +0x30: ldp     q0, q1, [x1]
      +0x34: add     w2, w2, #0x1
      +0x38: stp     q0, q1, [x0]
      +0x3c: add     x0, x0, #0x40
      +0x40: cmp     w2, #0x4
      +0x44: b.ne    <mldsa65_polyvec_matrix_expand_eager+0x30>
      +0x48: mov     w20, #0x0
      +0x4c: mov     w21, #0x5
      +0x50: mov     x1, x19
      +0x54: mov     w0, #0x0
      +0x58: add     w2, w20, w0
      +0x5c: add     w0, w0, #0x1
      +0x60: add     x1, x1, #0x40
      +0x64: udiv    w3, w2, w21
      +0x68: add     w4, w3, w3, lsl #2
      +0x6c: sturb   w3, [x1, #-31]
      +0x70: sub     w2, w2, w4
      +0x74: sturb   w2, [x1, #-32]
      +0x78: cmp     w0, #0x4
      +0x7c: b.ne    <mldsa65_polyvec_matrix_expand_eager+0x58>
      +0x80: add     w2, w20, #0x3
      +0x84: add     w1, w20, #0x2
      +0x88: add     w0, w20, #0x1
      +0x8c: udiv    w3, w2, w21
      +0x90: add     w4, w3, w3, lsl #2
      +0x94: sub     w2, w2, w4
      +0x98: umaddl  x3, w3, w21, x2
      +0x9c: udiv    w2, w1, w21
      +0xa0: add     x3, x22, x3, lsl #10
      +0xa4: add     w4, w2, w2, lsl #2
      +0xa8: sub     w1, w1, w4
      +0xac: umaddl  x2, w2, w21, x1
      +0xb0: udiv    w1, w0, w21
      +0xb4: add     x2, x22, x2, lsl #10
      +0xb8: add     w4, w1, w1, lsl #2
      +0xbc: sub     w0, w0, w4
      +0xc0: umaddl  x1, w1, w21, x0
      +0xc4: udiv    w0, w20, w21
      +0xc8: add     x1, x22, x1, lsl #10
      +0xcc: add     w4, w0, w0, lsl #2
      +0xd0: sub     w4, w20, w4
      +0xd4: add     w20, w20, #0x4
      +0xd8: umaddl  x0, w0, w21, x4
      +0xdc: mov     x4, x19
      +0xe0: add     x0, x22, x0, lsl #10
      +0xe4: bl      <mldsa_poly_uniform_4x>
      +0xe8: cmp     w20, #0x1c
      +0xec: b.ne    <mldsa65_polyvec_matrix_expand_eager+0x50>
      +0xf0: mov     w0, #0x503
      +0xf4: mov     x1, x19
      +0xf8: strh    w0, [x19, #32]
      +0xfc: add     x0, x22, #0x7, lsl #12
     +0x100: bl      <mldsa_poly_uniform>
     +0x104: mov     w0, #0x504
     +0x108: mov     x1, x19
     +0x10c: strh    w0, [x19, #32]
     +0x110: mov     x0, #0x7400
     +0x114: add     x0, x22, x0
     +0x118: bl      <mldsa_poly_uniform>
     +0x11c: mov     x0, x19
     +0x120: mov     x2, #0x100
     +0x124: mov     w1, #0x0
     +0x128: bl      <memset>
     +0x12c: adrp    x0, <page>
     +0x130: ldr     x0, [x0, #4088]
     +0x134: ldr     x2, [sp, #328]
     +0x138: ldr     x1, [x0]
     +0x13c: subs    x2, x2, x1
     +0x140: mov     x1, #0x0
     +0x144: b.eq    <mldsa65_polyvec_matrix_expand_eager+0x14c>
     +0x148: bl      <stack_chk_fail>
     +0x14c: ldp     x21, x22, [sp, #16]
     +0x150: ldr     x30, [sp, #32]
     +0x154: ldp     x19, x20, [sp], #336
     +0x158: ret

    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_polyvec_matrix_expand_eager";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (also used by the callees).*)
(* 32 bytes r of rho; the matrix at mat, 6 rows of 5 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 5 r if sampling terminates for each entry. The  *)
(* stack is the 336 bytes of the function and the 4752 of the callees below  *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5088))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,30720;
                         word_sub stackpointer (word 5088),5088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,30720; word_sub stackpointer (word 5088),5088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,30720);
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          nonoverlapping (mat,30720) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,30720); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5088))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,30720;
                         word_sub stackpointer (word 5088),5088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,30720; word_sub stackpointer (word 5088),5088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,30720);
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
