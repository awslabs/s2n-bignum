(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the proof (see unpack_sk_65_spec.ml).          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/unpack_sk_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The 128 bytes of   *)
(* rho, key and tr are loaded and stored as eight 128-bit words, which the   *)
(* calls for s1 and s2 keep, and split into bytes for the invariant of the   *)
(* loop over the 6 polynomials of t0, polynomial i being at t0 + 1024 * i    *)
(* and its packed form at sk + 1536 + 416 * i. The transform of t0 is a tail *)
(* call.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_EXEC
  and mc = mldsa_native_libmldsa_gcc12_O2_mc
  and vars = [`pc:num`; `rho:int64`; `tr:int64`; `key:int64`; `t0:int64`;
              `s1:int64`; `s2:int64`; `sk:int64`; `stackpointer:int64`;
              `returnaddress:int64`] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C4" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(rho:int64) (tr:int64) (key:int64) (t0:int64) (s1:int64) (s2:int64)
      (sk:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil rho tr key t0 s1 s2 sk pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 6
            (\i. f_ev_loop rho tr key t0 s1 s2 sk pc stackpointer
                           returnaddress i))
          (f_ev_prol rho tr key t0 s1 s2 sk pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + mldsa65_unpack_sk_loop1`
   `pc + mldsa65_unpack_sk_loop1_exit`
   `\i s. read X19 s = word_add sk (word(1536 + 416 * i)) /\
          read X20 s = word_add t0 (word(1024 * i)) /\
          read X21 s = sk /\
          read X22 s = word_add sk (word 4032) /\
          read X23 s = t0 /\
          read X24 s = s2 /\
          read X25 s = s1 /\
          read SP s = word_add stackpointer (word 32) /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 56))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 64))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 72))) s =
            x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 80))) s =
            x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s =
            returnaddress /\
          (!j. j < 32
               ==> read(memory :> bytes8(word_add rho (word j))) s =
                   skb j) /\
          (!j. j < 64
               ==> read(memory :> bytes8(word_add tr (word j))) s =
                   skb(64 + j)) /\
          (!j. j < 32
               ==> read(memory :> bytes8(word_add key (word j))) s =
                   skb(32 + j)) /\
          (!j. j < 1280
               ==> read(memory :> bytes32(word_add s1 (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(128 + j))) j) /\
          (!j. j < 1536
               ==> read(memory :> bytes32(word_add s2 (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(768 + j))) j) /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add t0 (word(4 * j)))) s =
                   mld_polyvec_unpack 416 mld_polyt0_unpack
                    (\j. skb(1536 + j)) j) /\
          (!j. j < 4032
               ==> read(memory :> bytes8(word_add sk (word j))) s =
                   skb j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The copies, and the unpacking and transforms of s1 and s2 ***)

    FULL_INIT_TAC THEN
    GLUE_SLICE_TAC
     `!j. j < 128
          ==> read(memory :> bytes8(word_add sk (word j))) s0 =
              (skb:num->byte) j` THEN
    GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
    ARM_STEPS_TAC EXEC (1--24) THEN
    GLUE_SLICE_TAC
     `!j. j < 640
          ==> read(memory :> bytes8(word_add sk (word(128 + j)))) s24 =
              (skb:num->byte)(128 + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `\j. (skb:num->byte)(128 + j)`;
      `pc:num`; `read SP s`; `read X30 s`]
     vars 25 THEN
    ARM_STEPS_TAC EXEC (26--27) THEN
    FULL_CALL_TAC mc EXEC "H_C1"
     [`read X0 s`;
      `mld_polyvec_unpack 128 mld_polyeta_unpack_4
        (\j. (skb:num->byte)(128 + j))`;
      `pc:num`; `read SP s`; `read X30 s`]
     vars 28 THEN
    ARM_STEPS_TAC EXEC (29--31) THEN
    GLUE_SLICE_TAC
     `!j. j < 768
          ==> read(memory :> bytes8(word_add sk (word(768 + j)))) s31 =
              (skb:num->byte)(768 + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C2"
     [`read X0 s`; `read X1 s`; `\j. (skb:num->byte)(768 + j)`;
      `pc:num`; `read SP s`; `read X30 s`]
     vars 32 THEN
    ARM_STEPS_TAC EXEC (33--34) THEN
    FULL_CALL_TAC mc EXEC "H_C3"
     [`read X0 s`;
      `mld_polyvec_unpack 128 mld_polyeta_unpack_4
        (\j. (skb:num->byte)(768 + j))`;
      `pc:num`; `read SP s`; `read X30 s`]
     vars 35 THEN
    ARM_STEPS_TAC EXEC (36--36) THEN
    GLUE_STORE_TAC `rho:int64` THEN GLUE_STORE_TAC `key:int64` THEN
    GLUE_STORE_TAC `tr:int64` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0]
    THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                   else GLUE_BYTES_FINAL_TAC);

    (*** The unpacking of polynomial i of t0, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--4) THEN
    GLUE_SLICE_TAC
     `!j. j < 416
          ==> read(memory :> bytes8
                (word_add sk (word((1536 + 416 * i) + j)))) s4 =
              (skb:num->byte)(1536 + 416 * i + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C4"
     [`read X0 s`; `read X1 s`; `\j. (skb:num->byte)(1536 + 416 * i + j)`;
      `pc:num`; `read X30 s`]
     (vars @ [`i:num`]) 5 THEN
    ARM_STEPS_TAC EXEC (6--8) THEN
    VEC_FULL_FINAL_TAC [];

    (*** The tail call of the transform of t0 ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--6) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    FULL_CALL_TAC mc EXEC "H_C3"
     [`read X0 s`;
      `mld_polyvec_unpack 416 mld_polyt0_unpack
        (\j. (skb:num->byte)(1536 + j))`;
      `pc:num`; `read SP s`; `read X30 s`]
     vars 7 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
