(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 4 polynomials to 11 bits per coefficient. This *)
(* is the code for mlkem1024_polyvec_compress_du from mlkem-native's         *)
(* portable C implementation compiled by clang 17 with -O3 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d11 for each of  *)
(* the polynomials, the last time as a tail call. It is verified in the whole image (see        *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_poly_compress_d11 in the image. Besides its own 32 bytes, the stack *)
(* below that is used by mlkem_poly_compress_d11 for the first three calls.          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/poly_compress_d11.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_compress_du:
       +0x0: str     x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x19, x1
       +0xc: mov     x20, x0
      +0x10: bl      mlkem_poly_compress_d11
      +0x14: add     x0, x20, #0x160
      +0x18: add     x1, x19, #0x200
      +0x1c: bl      mlkem_poly_compress_d11
      +0x20: add     x0, x20, #0x2c0
      +0x24: add     x1, x19, #0x400
      +0x28: bl      mlkem_poly_compress_d11
      +0x2c: add     x0, x20, #0x420
      +0x30: add     x1, x19, #0x600
      +0x34: ldp     x20, x19, [sp, #16]
      +0x38: ldr     x30, [sp], #32
      +0x3c: b       mlkem_poly_compress_d11
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_polyvec_compress_du"];;

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
     read (memory :> bytes(r,352)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 352),352)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 704),352)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 1056),352)) s =
     nsum {i | i < 256} (\i. g(768 + i) * 2 EXP (11 * i))
     ==> read (memory :> bytes(r,1408)) s =
         nsum {i | i < 1024} (\i. g i * 2 EXP (11 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1408 = 352 + 352 + 352 + 352`;
              ARITH_RULE `1024 = 256 + 256 + 256 + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[NSUM_SHIFT_EXP] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `5632 = 2816 + 2816`;
              ARITH_RULE `8448 = 2816 + 2816 + 2816`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP 2816`,`e:num`) THEN CONV_TAC NUM_RING);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for the polynomials, the result as a number is the  *)
(* sum of the 11-bit compressed coefficients, assuming them to be in         *)
(* [0,3329) as the C code does.                                              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_COMPRESS_D11_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,1408); (a,2048); (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(r,1408); (word_sub stackpointer (word 80),80)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_compress_du) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 1024
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 1024 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,1408)) s =
                       nsum {i | i < 1024}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD
                                 2048 * 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,1408);
                         memory :> bytes(word_sub stackpointer
                                                  (word 80),80)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 80 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (1--5) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`; `x:num->int16`;
                          `guard:int64`; `pc:num`; `read SP s`;
                          `read X30 s`] 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (7--9) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(256 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (11--13) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(512 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 14 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (15--19) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(768 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN POLYVEC_SPLIT_TAC 4 THEN
  MATCH_MP_TAC(BETA_RULE(SPEC
   `\i. ((4096 * val((x:num->int16) i) + 3329) DIV 6658) MOD 2048`
   (SPECL [`r:int64`; `s20:armstate`] POLYVEC_COMPRESS_DU_JOIN))) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d11.                                                  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let LOCAL_COMPRESS_D11_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `guard:int64`;
       `pc:num`; `read SP s`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,1408; a,2048; word_sub stackpointer (word 80),80] /\
       ALLPAIRS nonoverlapping
        [r,1408; word_sub stackpointer (word 80),80]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem1024_polyvec_compress_du) /\
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
                     [a,2048; r,1408; word_sub stackpointer (word 80),80;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,1408; word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE [memory :> bytes(r,1408);
                        memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_D11" THEN
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
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (1--5) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (7--9) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (11--13) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 14 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_CLANG17_O3_EXEC (15--19) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 20 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
