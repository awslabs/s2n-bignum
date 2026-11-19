(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa87_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -Os (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 56 entries four at a time with  *)
(* mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), before   *)
(* zeroing the buffers with memset, which it calls through the PLT of the    *)
(* image. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_polyvec_matrix_expand of common/mldsa_native_sampling.ml, using the   *)
(* theorems for the callee and the contract memset_full_contract of          *)
(* utils/mlkem_native_libc_full.ml for memset, assuming that sampling        *)
(* terminates for each entry (mld_matrix_terminates), and shown to be        *)
(* constant time and memory safe, with the events depending on rho, which is *)
(* public.                                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_uniform_4x_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_polyvec_matrix_expand_eager:
       +0x0: stp     x19, x20, [sp, #-336]!
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x22, x0
       +0xc: add     x21, sp, #0x4f
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]
      +0x18: str     x30, [sp, #32]
      +0x1c: and     x21, x21, #0xffffffffffffffe0
      +0x20: ldr     x2, [x0]
      +0x24: str     x2, [sp, #328]
      +0x28: mov     x2, #0x0
      +0x2c: mov     x0, x21
      +0x30: ldp     q0, q1, [x1]
      +0x34: add     w2, w2, #0x1
      +0x38: stp     q0, q1, [x0]
      +0x3c: add     x0, x0, #0x40
      +0x40: cmp     w2, #0x4
      +0x44: b.ne    <mldsa87_polyvec_matrix_expand_eager+0x30>
      +0x48: mov     w20, #0x0
      +0x4c: mov     w19, #0x7
      +0x50: mov     x1, x21
      +0x54: mov     w0, #0x0
      +0x58: add     w2, w20, w0
      +0x5c: add     w0, w0, #0x1
      +0x60: add     x1, x1, #0x40
      +0x64: udiv    w3, w2, w19
      +0x68: msub    w2, w3, w19, w2
      +0x6c: sturb   w3, [x1, #-31]
      +0x70: sturb   w2, [x1, #-32]
      +0x74: cmp     w0, #0x4
      +0x78: b.ne    <mldsa87_polyvec_matrix_expand_eager+0x58>
      +0x7c: add     w2, w20, #0x3
      +0x80: add     w1, w20, #0x2
      +0x84: add     w0, w20, #0x1
      +0x88: udiv    w3, w2, w19
      +0x8c: msub    w2, w3, w19, w2
      +0x90: umaddl  x3, w3, w19, x2
      +0x94: udiv    w2, w1, w19
      +0x98: add     x3, x22, x3, lsl #10
      +0x9c: msub    w1, w2, w19, w1
      +0xa0: umaddl  x2, w2, w19, x1
      +0xa4: udiv    w1, w0, w19
      +0xa8: add     x2, x22, x2, lsl #10
      +0xac: msub    w0, w1, w19, w0
      +0xb0: umaddl  x1, w1, w19, x0
      +0xb4: udiv    w0, w20, w19
      +0xb8: add     x1, x22, x1, lsl #10
      +0xbc: msub    w4, w0, w19, w20
      +0xc0: add     w20, w20, #0x4
      +0xc4: umaddl  x0, w0, w19, x4
      +0xc8: mov     x4, x21
      +0xcc: add     x0, x22, x0, lsl #10
      +0xd0: bl      <mldsa_poly_uniform_4x>
      +0xd4: cmp     w20, #0x38
      +0xd8: b.ne    <mldsa87_polyvec_matrix_expand_eager+0x50>
      +0xdc: mov     x0, x21
      +0xe0: mov     x2, #0x100
      +0xe4: mov     w1, #0x0
      +0xe8: bl      <memset>
      +0xec: adrp    x0, <page>
      +0xf0: ldr     x0, [x0, #4088]
      +0xf4: ldr     x2, [sp, #328]
      +0xf8: ldr     x1, [x0]
      +0xfc: subs    x2, x2, x1
     +0x100: mov     x1, #0x0
     +0x104: b.eq    <mldsa87_polyvec_matrix_expand_eager+0x10c>
     +0x108: bl      <stack_chk_fail>
     +0x10c: ldp     x21, x22, [sp, #16]
     +0x110: ldr     x30, [sp, #32]
     +0x114: ldp     x19, x20, [sp], #336
     +0x118: ret

    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_polyvec_matrix_expand_eager";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (also used by the callees).*)
(* 32 bytes r of rho; the matrix at mat, 8 rows of 7 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 7 r if sampling terminates for each entry. The  *)
(* stack is the 336 bytes of the function and the 4752 of the callees below  *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5088))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,57344;
                         word_sub stackpointer (word 5088),5088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,57344; word_sub stackpointer (word 5088),5088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,57344);
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          nonoverlapping (mat,57344) (word_sub stackpointer (word 5088),5088) /\
          ALLPAIRS nonoverlapping
           [(mat,57344); (word_sub stackpointer (word 5088),5088)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5088))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,57344;
                         word_sub stackpointer (word 5088),5088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,57344; word_sub stackpointer (word 5088),5088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,57344);
                  memory :> bytes(word_sub stackpointer (word 5088),5088)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
