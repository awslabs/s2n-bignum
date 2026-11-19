(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa44_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -Os (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 16 entries four at a time with  *)
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

    mldsa44_polyvec_matrix_expand_eager:
       +0x0: stp     x19, x20, [sp, #-352]!
       +0x4: mov     x20, x0
       +0x8: adrp    x0, <page>
       +0xc: ldr     x0, [x0, #4088]
      +0x10: add     x19, sp, #0x5f
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: stp     x25, x30, [sp, #48]
      +0x24: ldr     x2, [x0]
      +0x28: str     x2, [sp, #344]
      +0x2c: mov     x2, #0x0
      +0x30: mov     x0, x19
      +0x34: ldp     q0, q1, [x1]
      +0x38: add     w2, w2, #0x1
      +0x3c: stp     q0, q1, [x0]
      +0x40: add     x0, x0, #0x40
      +0x44: cmp     w2, #0x4
      +0x48: b.ne    <mldsa44_polyvec_matrix_expand_eager+0x34>
      +0x4c: mov     w5, #0x0
      +0x50: mov     w22, #0x1000
      +0x54: mov     x23, #0xc00
      +0x58: mov     x24, #0x800
      +0x5c: mov     x25, #0x400
      +0x60: mov     x1, x19
      +0x64: mov     w0, w5
      +0x68: add     w21, w5, #0x4
      +0x6c: and     w2, w0, #0x3
      +0x70: strb    w2, [x1, #32]
      +0x74: lsr     w2, w0, #2
      +0x78: add     w0, w0, #0x1
      +0x7c: strb    w2, [x1, #33]
      +0x80: add     x1, x1, #0x40
      +0x84: cmp     w21, w0
      +0x88: b.ne    <mldsa44_polyvec_matrix_expand_eager+0x6c>
      +0x8c: add     w3, w5, #0x3
      +0x90: add     w2, w5, #0x2
      +0x94: add     w1, w5, #0x1
      +0x98: lsr     w5, w5, #2
      +0x9c: lsr     w3, w3, #2
      +0xa0: lsr     w2, w2, #2
      +0xa4: lsr     w1, w1, #2
      +0xa8: mov     x4, x19
      +0xac: add     x0, x20, x5, lsl #12
      +0xb0: umaddl  x3, w3, w22, x23
      +0xb4: umaddl  x2, w2, w22, x24
      +0xb8: umaddl  x1, w1, w22, x25
      +0xbc: add     x3, x20, x3
      +0xc0: add     x2, x20, x2
      +0xc4: add     x1, x20, x1
      +0xc8: bl      <mldsa_poly_uniform_4x>
      +0xcc: cmp     w21, #0x10
      +0xd0: b.eq    <mldsa44_polyvec_matrix_expand_eager+0xdc>
      +0xd4: mov     w5, w21
      +0xd8: b       <mldsa44_polyvec_matrix_expand_eager+0x60>
      +0xdc: mov     x0, x19
      +0xe0: mov     x2, #0x100
      +0xe4: mov     w1, #0x0
      +0xe8: bl      <memset>
      +0xec: adrp    x0, <page>
      +0xf0: ldr     x0, [x0, #4088]
      +0xf4: ldr     x2, [sp, #344]
      +0xf8: ldr     x1, [x0]
      +0xfc: subs    x2, x2, x1
     +0x100: mov     x1, #0x0
     +0x104: b.eq    <mldsa44_polyvec_matrix_expand_eager+0x10c>
     +0x108: bl      <stack_chk_fail>
     +0x10c: ldp     x21, x22, [sp, #16]
     +0x110: ldp     x23, x24, [sp, #32]
     +0x114: ldp     x25, x30, [sp, #48]
     +0x118: ldp     x19, x20, [sp], #352
     +0x11c: ret

    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_polyvec_matrix_expand_eager";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset (also used by the callees).*)
(* 32 bytes r of rho; the matrix at mat, 4 rows of 4 polynomials, becomes    *)
(* mld_polyvec_matrix_expand 4 r if sampling terminates for each entry. The  *)
(* stack is the 352 bytes of the function and the 4752 of the callee below   *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5104),5104) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5104),5104)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 5104),5104)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within rho, the matrix, the stack, the GOT   *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the matrix and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5104),5104) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5104),5104)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5104))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,16384;
                         word_sub stackpointer (word 5104),5104;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,16384; word_sub stackpointer (word 5104),5104]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,16384);
                  memory :> bytes(word_sub stackpointer (word 5104),5104)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e mat rho r guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          nonoverlapping (mat,16384) (word_sub stackpointer (word 5104),5104) /\
          ALLPAIRS nonoverlapping
           [(mat,16384); (word_sub stackpointer (word 5104),5104)]
           [(rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 5104))
                              returnaddress /\
                       memaccess_inbounds e2
                        [rho,32; mat,16384;
                         word_sub stackpointer (word 5104),5104;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [mat,16384; word_sub stackpointer (word 5104),5104]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(mat,16384);
                  memory :> bytes(word_sub stackpointer (word 5104),5104)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
