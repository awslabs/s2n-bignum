(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the proof (see unpack_sk_87_spec.ml).          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/unpack_sk_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The address of the *)
(* secret key is loaded from its slot on the stack. The 128 bytes of rho,    *)
(* key and tr are loaded and stored as eight 128-bit words, which the calls  *)
(* for s1 and s2 keep, and split into bytes for the invariant of the loop    *)
(* over the 8 polynomials of t0, polynomial i being at t0 + 1024 * i and its *)
(* packed form at sk + 1568 + 416 * i. The legacy SSE loads keep the upper   *)
(* halves of the YMM registers, whose initial values are ghost variables.    *)
(* The transform of t0 is a tail call.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_EXEC
  and mc = mldsa_native_libmldsa_gcc12_O2_mc
  and vars = [`pc:num`; `rho:int64`; `tr:int64`; `key:int64`; `t0:int64`;
              `s1:int64`; `s2:int64`; `sk:int64`; `stackpointer:int64`;
              `returnaddress:int64`] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_NTT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_NTT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C4" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(rho:int64) (tr:int64) (key:int64) (t0:int64) (s1:int64) (s2:int64)
      (sk:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil rho tr key t0 s1 s2 sk pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 8
            (\i. f_ev_loop rho tr key t0 s1 s2 sk pc stackpointer
                           returnaddress i))
          (f_ev_prol rho tr key t0 s1 s2 sk pc stackpointer returnaddress))
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
  ENSURES_EVENTS_WHILE_UP2_TAC `8`
   `pc + mldsa87_unpack_sk_loop1`
   `pc + mldsa87_unpack_sk_loop1_exit`
   `\i s. read RBX s = word_add sk (word(1568 + 416 * i)) /\
          read RBP s = word_add t0 (word(1024 * i)) /\
          read R13 s = t0 /\
          read R12 s = word_add sk (word 4896) /\
          read RSP s = word_add stackpointer (word 96) /\
          read (memory :> bytes64 (word_add stackpointer (word 104))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 112))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 120))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 128))) s =
            r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 136))) s =
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
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add s1 (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(128 + j))) j) /\
          (!j. j < 2048
               ==> read(memory :> bytes32(word_add s2 (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(800 + j))) j) /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add t0 (word(4 * j)))) s =
                   mld_polyvec_unpack 416 mld_polyt0_unpack
                    (\j. skb(1568 + j)) j) /\
          (!j. j < 4896
               ==> read(memory :> bytes8(word_add sk (word j))) s =
                   skb j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The copies, and the unpacking and transforms of s1 and s2 ***)

    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    FULL_INIT_TAC THEN
    GLUE_SLICE_TAC
     `!j. j < 128
          ==> read(memory :> bytes8(word_add sk (word j))) s0 =
              (skb:num->byte) j` THEN
    GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
    X86_STEPS_TAC EXEC (1--28) THEN
    GLUE_SLICE_TAC
     `!j. j < 672
          ==> read(memory :> bytes8(word_add sk (word(128 + j)))) s28 =
              (skb:num->byte)(128 + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C0"
     [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)(128 + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars) 29 THEN
    X86_STEPS_TAC EXEC (30--32) THEN
    FULL_CALL_TAC mc EXEC "H_C1"
     [`read RDI s`;
      `mld_polyvec_unpack 96 mld_polyeta_unpack_2
        (\j. (skb:num->byte)(128 + j))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars) 33 THEN
    X86_STEPS_TAC EXEC (34--36) THEN
    GLUE_SLICE_TAC
     `!j. j < 768
          ==> read(memory :> bytes8(word_add sk (word(800 + j)))) s36 =
              (skb:num->byte)(800 + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C2"
     [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)(800 + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars) 37 THEN
    X86_STEPS_TAC EXEC (38--41) THEN
    FULL_CALL_TAC mc EXEC "H_C3"
     [`read RDI s`;
      `mld_polyvec_unpack 96 mld_polyeta_unpack_2
        (\j. (skb:num->byte)(800 + j))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars) 42 THEN
    X86_STEPS_TAC EXEC (43--43) THEN
    GLUE_STORE_TAC `rho:int64` THEN GLUE_STORE_TAC `key:int64` THEN
    GLUE_STORE_TAC `tr:int64` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0]
    THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                   else GLUE_BYTES_FINAL_TAC);

    (*** The unpacking of polynomial i of t0, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--5) THEN
    GLUE_SLICE_TAC
     `!j. j < 416
          ==> read(memory :> bytes8
                (word_add sk (word((1568 + 416 * i) + j)))) s5 =
              (skb:num->byte)(1568 + 416 * i + j)` THEN
    FULL_CALL_TAC mc EXEC "H_C4"
     [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)(1568 + 416 * i + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars @ [`i:num`]) 6 THEN
    X86_STEPS_TAC EXEC (7--8) THEN
    VEC_FULL_FINAL_TAC [];

    (*** The tail call of the transform of t0 ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--7) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    FULL_CALL_TAC mc EXEC "H_C3"
     [`read RDI s`;
      `mld_polyvec_unpack 416 mld_polyt0_unpack
        (\j. (skb:num->byte)(1568 + j))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     (vars) 8 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
