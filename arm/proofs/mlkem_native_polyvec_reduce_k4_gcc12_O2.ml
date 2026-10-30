(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Barrett reduction of a vector of 4 polynomials.                           *)
(* This is the code for mlkem1024_polyvec_reduce from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_reduce for each of the    *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x1940, using the theorems for mlkem_poly_reduce at 0x4190 in the image.  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    1940: stp     x19, x30, [sp, #-16]!
    1944: mov     x19, x0
    1948: bl      4190 <mlkem_poly_reduce>
    194c: add     x0, x19, #0x200
    1950: bl      4190 <mlkem_poly_reduce>
    1954: add     x0, x19, #0x400
    1958: bl      4190 <mlkem_poly_reduce>
    195c: add     x0, x19, #0x600
    1960: ldp     x19, x30, [sp], #16
    1964: b       4190 <mlkem_poly_reduce>
 ***)

let MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1940,0x1968];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,2048) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
          [(a,2048); (word_sub stackpointer (word 16),16)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1940) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 1024
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,2048);
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
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (1--3) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `x:num->int16`; `pc:num`; `read X30 s`] 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (5--6) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (x:num->int16)(256 + i)`; `pc:num`;
                    `read X30 s`] 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (8--9) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (x:num->int16)(512 + i)`; `pc:num`;
                    `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (11--13) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (x:num->int16)(768 + i)`; `pc:num`;
                    `read X30 s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 4 THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_reduce_k4_signature =
  ([("a", "int16_t[static 1024]", "false")],
   "void",
   [("a", "1024", 2)],
   [("a", "1024", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_reduce_k4_signature
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC;;

let LOCAL_REDUCE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,2048) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
           [a,2048; word_sub stackpointer (word 16),16]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x1940) /\
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
                         [a,2048; word_sub stackpointer (word 16),16]
                         [a,2048; word_sub stackpointer (word 16),16]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (a,2048);
                 memory :> bytes (word_sub stackpointer (word 16),16)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (1--3) THEN
  LOCAL_REDUCE_SAFETY_TAC "H_REDUCE" 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (5--6) THEN
  LOCAL_REDUCE_SAFETY_TAC "H_REDUCE" 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (8--9) THEN
  LOCAL_REDUCE_SAFETY_TAC "H_REDUCE" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_EXEC (11--13) THEN
  LOCAL_REDUCE_SAFETY_TAC "H_REDUCE" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
