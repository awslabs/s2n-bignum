(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 2 polynomials to 10 bits per coefficient. This *)
(* is the code for mlkem512_polyvec_compress_du from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d10 for each of  *)
(* the polynomials, the last time as a tail call. It is verified in the      *)
(* whole image (see libmlkem.ml), using the theorems                         *)
(* for mlkem_poly_compress_d10 in the image. Besides its own 32 bytes, the   *)
(* stack below that is used by mlkem_poly_compress_d10 for the first call.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_compress_d10_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_compress_du:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: str     x30, [sp, #16]
      +0x10: bl      <mlkem_poly_compress_d10>
      +0x14: ldr     x30, [sp, #16]
      +0x18: add     x1, x20, #0x200
      +0x1c: add     x0, x19, #0x140
      +0x20: ldp     x19, x20, [sp], #32
      +0x24: b       <mlkem_poly_compress_d10>
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem512_polyvec_compress_du"];;

(* ------------------------------------------------------------------------- *)
(* The output for the vector from those for the polynomials.                 *)
(* ------------------------------------------------------------------------- *)

let NSUM_SHIFT_EXP_STMT =
  `!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`;;

let NSUM_SHIFT_EXP = assume_spec NSUM_SHIFT_EXP_STMT;;

let POLYVEC_COMPRESS_DU_JOIN_STMT =
  `!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,640)) s =
         nsum {i | i < 512} (\i. g i * 2 EXP (10 * i))`;;

let POLYVEC_COMPRESS_DU_JOIN = assume_spec POLYVEC_COMPRESS_DU_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for the polynomials, the result as a number is the  *)
(* sum of the 10-bit compressed coefficients, assuming them to be in         *)
(* [0,3329) as the C code does.                                              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_COMPRESS_D10_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,640); (a,1024); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,640); (word_sub stackpointer (word 64),64)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem512_polyvec_compress_du) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 512
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 512 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,640)) s =
                       nsum {i | i < 512}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,640);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d10.                                                  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let LOCAL_COMPRESS_D10_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `guard:int64`;
       `pc:num`; `read SP s`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,640; a,1024; word_sub stackpointer (word 64),64] /\
       ALLPAIRS nonoverlapping
        [r,640; word_sub stackpointer (word 64),64]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem512_polyvec_compress_du) /\
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
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,1024; r,640; word_sub stackpointer (word 64),64;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,640; word_sub stackpointer (word 64),64]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,640);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
