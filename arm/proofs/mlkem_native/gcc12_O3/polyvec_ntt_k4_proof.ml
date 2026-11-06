(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 4 polynomials. This is  *)
(* the code for mlkem1024_polyvec_ntt from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_ntt for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see                       *)
(* libmlkem.ml), using the theorems for mlkem_poly_ntt                       *)
(* in the image.                                                             *)
(* The code is the same as with -O2, but the stack frame is 48 bytes         *)
(* rather than 16, since mlkem_poly_ntt saves four registers at -O3, and     *)
(* the theorem of constant time and memory safety has the vector of          *)
(* constants that it reads as a read-only region.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/poly_ntt_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_ntt:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: bl      <mlkem_poly_ntt>
       +0xc: add     x0, x19, #0x200
      +0x10: bl      <mlkem_poly_ntt>
      +0x14: add     x0, x19, #0x400
      +0x18: bl      <mlkem_poly_ntt>
      +0x1c: add     x0, x19, #0x600
      +0x20: ldp     x19, x30, [sp], #16
      +0x24: b       <mlkem_poly_ntt>
 ***)

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem1024_polyvec_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,2048) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
          [(a,2048); (word_sub stackpointer (word 48),48)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_ntt) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 4 /\
                      (!i. i < 256 ==> abs(ival(x(256 * j + i))) <= &8191)
                      ==> !i. i < 256
                              ==> let zi =
                                    read(memory :> bytes16
                                     (word_add a (word(512 * j + 2 * i)))) s
                                  in (ival zi ==
                                      forward_ntt (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival zi) <= &23594)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,2048);
                memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (1--3) THEN
  LOCAL_NTT_TAC [`read X0 s`; `x:num->int16`; `pc:num`; `read SP s`;
                 `read X30 s`] 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (5--6) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (x:num->int16)(256 + i)`; `pc:num`;
                 `read SP s`; `read X30 s`] 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (8--9) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (x:num->int16)(512 + i)`; `pc:num`;
                 `read SP s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (11--13) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (x:num->int16)(768 + i)`; `pc:num`;
                 `read SP s`; `read X30 s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_ntt_k4_signature =
  ([("a", "int16_t[static 1024]", "false")],
   "void",
   [("a", "1024", 2)],
   [("a", "1024", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`;
                       `word(pc + mlkem_poly_ntt_consts):int64`,
                       `mlkem_poly_ntt_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_polyvec_ntt_k4_signature
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC;;

let LOCAL_NTT_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,2048) (word_sub stackpointer (word 48),48) /\
           ALLPAIRS nonoverlapping
           [a,2048; word_sub stackpointer (word 48),48]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem1024_polyvec_ntt) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 48))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,2048; word_sub stackpointer (word 48),48;
                          word (pc + rodata_mlk_zetas),256;
                          word (pc + mlkem_poly_ntt_consts),
                          mlkem_poly_ntt_consts_size]
                         [a,2048; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,2048);
                 memory :> bytes (word_sub stackpointer (word 48),48)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (1--3) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (5--6) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (8--9) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_EXEC (11--13) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
