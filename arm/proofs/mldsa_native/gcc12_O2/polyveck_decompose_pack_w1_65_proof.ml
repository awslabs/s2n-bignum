(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of a vector of 6 polynomials with the packing of the high   *)
(* parts: the proof (see polyveck_decompose_pack_w1_65_spec.ml).             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, polynomial i being at v + 1024 * i and the packed form   *)
(* of its high part at r + 128 * i.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C1" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (v:int64) (scratch:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r v scratch pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 6
            (\i. f_ev_loop r v scratch pc stackpointer returnaddress i))
          (f_ev_prol r v scratch pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mldsa65_polyveck_decompose_pack_w1_loop1`
   `pc + mldsa65_polyveck_decompose_pack_w1_loop1_exit`
   `\i s. read X19 s = word_add v (word(1024 * i)) /\
          read X20 s = word_add r (word(128 * i)) /\
          read X21 s = scratch /\
          read X22 s = word_add v (word 6144) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_decompose_lo_32 x j) /\
          (!j. 256 * i <= j /\ j < 1536
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j) /\
          (!j. j < 128 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyvec_pack 128
                    (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC 8
     [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC (1--2) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s2 = x(256 * i + j)` THEN
    VEC_REST_TAC
     `!j. 256 * (i + 1) <= j /\ j < 1536
          ==> read(memory :> bytes32(word_add v (word(4 * j)))) s2 =
              x j` THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC (3--3) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `\j. (x:num->int32)(256 * i + j)`;
      `pc:num`; `read X30 s`]
     [`pc:num`; `r:int64`; `v:int64`; `scratch:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 4 THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC (5--7) THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC (8--8) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC "H_C1"
     [`read X0 s`; `read X1 s`;
      `mld_poly_decompose_hi_32 (\j. (x:num->int32)(256 * i + j))`;
      `pc:num`; `read X30 s`]
     [`pc:num`; `r:int64`; `v:int64`; `scratch:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 9 THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC (10--12) THEN
    VEC_FULL_FINAL_TAC
     [o_THM];

    (*** The return ***)

    VEC_FULL_EXIT_TAC MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC 4
     []]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
