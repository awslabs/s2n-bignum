(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of a vector of 4 polynomials with the packing of the high   *)
(* parts: the proof (see polyveck_decompose_pack_w1_44_spec.ml).             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, polynomial i being at v + 1024 * i and the packed form   *)
(* of its high part at r + 192 * i, with RBX pointing to the packed form of  *)
(* the next high part, RBP to the next polynomial, R12 to the scratch        *)
(* polynomial and R13 to the end of the packed forms.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C1" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (v:int64) (scratch:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r v scratch pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 4
            (\i. f_ev_loop r v scratch pc stackpointer returnaddress i))
          (f_ev_prol r v scratch pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4`
   `pc + mldsa44_polyveck_decompose_pack_w1_loop1`
   `pc + mldsa44_polyveck_decompose_pack_w1_loop1_exit`
   `\i s. read RBX s = word_add r (word(192 * i)) /\
          read RBP s = word_add v (word(1024 * i)) /\
          read R12 s = scratch /\
          read R13 s = word_add r (word 768) /\
          read RSP s = word_add stackpointer (word 8) /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_decompose_lo_88 x j) /\
          (!j. 256 * i <= j /\ j < 1024
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j) /\
          (!j. j < 192 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyvec_pack 192
                    (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC EXEC 9 [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--3) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s3 = x(256 * i + j)` THEN
    VEC_REST_TAC
     `!j. 256 * (i + 1) <= j /\ j < 1024
          ==> read(memory :> bytes32(word_add v (word(4 * j)))) s3 =
              x j` THEN
    X86_STEPS_TAC EXEC (4--4) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C0"
     [`read RDI s`; `read RSI s`; `\j. (x:num->int32)(256 * i + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `r:int64`; `v:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 5 THEN
    X86_STEPS_TAC EXEC (6--9) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C1"
     [`read RDI s`; `read RSI s`;
      `mld_poly_decompose_hi_88 (\j. (x:num->int32)(256 * i + j))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `r:int64`; `v:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 10 THEN
    X86_STEPS_TAC EXEC (11--12) THEN
    VEC_FULL_FINAL_TAC [o_THM];

    (*** The return ***)

    VEC_FULL_EXIT_TAC EXEC 6 []]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
