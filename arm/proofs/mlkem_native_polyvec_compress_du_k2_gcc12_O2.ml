(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 2 polynomials to 10 bits per coefficient.      *)
(* This is the code for mlkem512_polyvec_compress_du from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d10 for each of  *)
(* the polynomials, the last time as a tail call. It is verified in the      *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x44e0, using the theorems for mlkem_poly_compress_d10 at 0x1cd0  *)
(* in the image. Besides its own 32 bytes, the stack below that is used by   *)
(* mlkem_poly_compress_d10 for the first call.                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_compress_d10_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    44e0: stp     x19, x20, [sp, #-32]!
    44e4: mov     x19, x0
    44e8: mov     x20, x1
    44ec: str     x30, [sp, #16]
    44f0: bl      1cd0 <mlkem_poly_compress_d10>
    44f4: ldr     x30, [sp, #16]
    44f8: add     x1, x20, #0x200
    44fc: add     x0, x19, #0x140
    4500: ldp     x19, x20, [sp], #32
    4504: b       1cd0 <mlkem_poly_compress_d10>
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x44e0,0x4508];;

(* ------------------------------------------------------------------------- *)
(* The output for the vector from those for the polynomials.                 *)
(* ------------------------------------------------------------------------- *)

let NSUM_SHIFT_EXP = prove
 (`!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM NSUM_LMUL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let POLYVEC_COMPRESS_DU_JOIN = prove
 (`!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,640)) s =
         nsum {i | i < 512} (\i. g i * 2 EXP (10 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `640 = 320 + 320`;
              ARITH_RULE `512 = 256 + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[NSUM_SHIFT_EXP] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXP_ADD] THEN
  SPEC_TAC(`2 EXP 2560`,`e:num`) THEN CONV_TAC NUM_RING);;

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

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,640); (a,1024); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,640); (word_sub stackpointer (word 64),64)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x44e0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
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
                                                  (word 64),64)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 2 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC (1--5) THEN
  LOCAL_COMPRESS_D10_TAC [`read X0 s`; `read X1 s`; `x:num->int16`;
                          `guard:int64`; `pc:num`; `read SP s`;
                          `read X30 s`] 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC (7--11) THEN
  LOCAL_COMPRESS_D10_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(256 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN POLYVEC_SPLIT_TAC 2 THEN
  MATCH_MP_TAC(BETA_RULE(SPEC
   `\i. ((2048 * val((x:num->int16) i) + 3329) DIV 6658) MOD 1024`
   (SPECL [`r:int64`; `s12:armstate`] POLYVEC_COMPRESS_DU_JOIN))) THEN
  ASM_SIMP_TAC[]);;

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

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,640; a,1024; word_sub stackpointer (word 64),64] /\
       ALLPAIRS nonoverlapping
        [r,640; word_sub stackpointer (word 64),64]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x44e0) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,1024; r,640; word_sub stackpointer (word 64),64;
                      word(pc + 0x1fff8),8; guard,8]
                     [r,640; word_sub stackpointer (word 64),64]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,640);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_D10" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC (1--5) THEN
  LOCAL_COMPRESS_D10_SAFETY_TAC "H_COMPRESS_D10" 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_EXEC (7--11) THEN
  LOCAL_COMPRESS_D10_SAFETY_TAC "H_COMPRESS_D10" 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
