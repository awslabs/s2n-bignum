(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a vector of 4 polynomials from 11 bits per coefficient.  *)
(* This is the code for mlkem1024_polyvec_decompress_du from mlkem-native's  *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_decompress_d11 for each   *)
(* of the polynomials, in a loop. It is verified in the whole image (see     *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_poly_decompress_d11 in the image.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_decompress_d11_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_decompress_du:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: stp     x21, x30, [sp, #16]
      +0x10: add     x21, x0, #0x800
      +0x14: mov     x1, x20
      +0x18: mov     x0, x19
      +0x1c: add     x19, x19, #0x200
      +0x20: bl      <mlkem_poly_decompress_d11>
      +0x24: add     x20, x20, #0x160
      +0x28: cmp     x19, x21
      +0x2c: b.ne    <mlkem1024_polyvec_decompress_du+0x14>
      +0x30: ldp     x21, x30, [sp, #16]
      +0x34: ldp     x19, x20, [sp], #32
      +0x38: ret     
 ***)

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem1024_polyvec_decompress_du"];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_DECOMPRESS_DU_SPLIT_STMT =
  `!a n s j.
        read (memory :> bytes(a,1408)) s = n /\ j < 4
        ==> read (memory :> bytes(word_add a (word(352 * j)),352)) s =
            (n DIV 2 EXP (2816 * j)) MOD 2 EXP 2816`;;

let POLYVEC_DECOMPRESS_DU_SPLIT =
  assume_spec POLYVEC_DECOMPRESS_DU_SPLIT_STMT;;

let POLYVEC_DECOMPRESS_DU_FIELD_STMT =
  `!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2816 DIV 2 EXP (11 * i)) MOD 2 EXP 11 =
            (n DIV 2 EXP (k + 11 * i)) MOD 2 EXP 11`;;

let POLYVEC_DECOMPRESS_DU_FIELD =
  assume_spec POLYVEC_DECOMPRESS_DU_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DECOMPRESS_D11_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,2048); (a,1408); (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(r,2048); (word_sub stackpointer (word 80),80)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_decompress_du) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(a,1408)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,2048);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let LOCAL_DECOMPRESS_D11_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `guard:int64`;
       `pc:num`; `read SP s`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,2048; a,1408; word_sub stackpointer (word 80),80] /\
       ALLPAIRS nonoverlapping
        [r,2048; word_sub stackpointer (word 80),80]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem1024_polyvec_decompress_du) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 80)) returnaddress /\
                    memaccess_inbounds e2
                     [a,1408; r,2048; word_sub stackpointer (word 80),80;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,2048; word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,2048);
                        memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
