(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 4 polynomials to 11 bits per coefficient.      *)
(* This is the code for mlkem1024_polyvec_compress_du from mlkem-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d11 for each of  *)
(* the polynomials, in a loop. It is verified in the whole image (see        *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x16f0, using  *)
(* the theorems for mlkem_poly_compress_d11 at 0x1f74 in the image. Besides  *)
(* its own 32 bytes, the stack below that is used by mlkem_poly_compress_d11 *)
(* for all the calls.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_compress_d11_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    16f0: stp     x19, x20, [sp, #-32]!
    16f4: mov     x19, x0
    16f8: mov     x20, x1
    16fc: stp     x21, x30, [sp, #16]
    1700: add     x21, x0, #0x580
    1704: mov     x1, x20
    1708: mov     x0, x19
    170c: add     x19, x19, #0x160
    1710: bl      1f74 <mlkem_poly_compress_d11>
    1714: add     x20, x20, #0x200
    1718: cmp     x19, x21
    171c: b.ne    1704 <mlkem1024_polyvec_compress_du+0x14>
    1720: ldp     x21, x30, [sp, #16]
    1724: ldp     x19, x20, [sp], #32
    1728: ret
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x16f0,0x172c];;

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
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,1408); (a,2048); (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(r,1408); (word_sub stackpointer (word 80),80)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x16f0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
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
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`; `x:num->int16`;
                          `guard:int64`; `pc:num`; `read SP s`;
                          `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (13--17) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(256 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (21--25) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(512 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (29--33) THEN
  LOCAL_COMPRESS_D11_TAC [`read X0 s`; `read X1 s`;
                          `\i. (x:num->int16)(768 + i)`; `guard:int64`;
                          `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN POLYVEC_SPLIT_TAC 4 THEN
  MATCH_MP_TAC(BETA_RULE(SPEC
   `\i. ((4096 * val((x:num->int16) i) + 3329) DIV 6658) MOD 2048`
   (SPECL [`r:int64`; `s40:armstate`] POLYVEC_COMPRESS_DU_JOIN))) THEN
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
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `guard:int64`;
       `pc:num`; `read SP s`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,1408; a,2048; word_sub stackpointer (word 80),80] /\
       ALLPAIRS nonoverlapping
        [r,1408; word_sub stackpointer (word 80),80]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x16f0) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 80)) returnaddress /\
                    memaccess_inbounds e2
                     [a,2048; r,1408; word_sub stackpointer (word 80),80;
                      word(pc + 0x1fff8),8; guard,8]
                     [r,1408; word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,1408);
                        memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE
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
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (13--17) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (21--25) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (29--33) THEN
  LOCAL_COMPRESS_D11_SAFETY_TAC "H_COMPRESS_D11" 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
