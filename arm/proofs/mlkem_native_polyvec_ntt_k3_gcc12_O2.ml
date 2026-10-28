(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 3 polynomials.          *)
(* This is the code for mlkem768_polyvec_ntt from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md), *)
(* which calls mlkem_poly_ntt for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see                      *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x5f00, using  *)
(* the theorems for mlkem_poly_ntt at 0x42b4 in the image.                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_ntt_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5f00: stp     x19, x30, [sp, #-16]!
    5f04: mov     x19, x0
    5f08: bl      42b4 <mlkem_poly_ntt>
    5f0c: add     x0, x19, #0x200
    5f10: bl      42b4 <mlkem_poly_ntt>
    5f14: add     x0, x19, #0x400
    5f18: ldp     x19, x30, [sp], #16
    5f1c: b       42b4 <mlkem_poly_ntt>
 ***)

let MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5f00,0x5f20];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,1536) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
          [(a,1536); (word_sub stackpointer (word 16),16)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5f00) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 3 /\
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
               [memory :> bytes(a,1536);
                memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (1--3) THEN
  LOCAL_NTT_TAC [`read X0 s`; `x:num->int16`; `pc:num`; `read X30 s`] 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (5--6) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (x:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (x:num->int16)(512 + i)`; `pc:num`;
                 `read X30 s`] 11 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_ntt_k3_signature =
  ([("a", "int16_t[static 768]", "false")],
   "void",
   [("a", "768", 2)],
   [("a", "768", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + 0x6380):int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_polyvec_ntt_k3_signature
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC;;

let LOCAL_NTT_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,1536) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
           [a,1536; word_sub stackpointer (word 16),16]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x5f00) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 16))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,1536; word_sub stackpointer (word 16),16;
                          word (pc + 0x6380),256]
                         [a,1536; word_sub stackpointer (word 16),16]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,1536);
                 memory :> bytes (word_sub stackpointer (word 16),16)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (1--3) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (5--6) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 11 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
