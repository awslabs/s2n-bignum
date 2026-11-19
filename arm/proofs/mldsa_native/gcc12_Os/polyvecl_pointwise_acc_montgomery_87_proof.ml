(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 7 polynomials, accumulated and       *)
(* reduced: the proof (see polyvecl_pointwise_acc_montgomery_87_spec.ml).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_pointwise_acc_montgomery_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_pwacc.ml";;

(* ------------------------------------------------------------------------- *)
(* The coefficient i of polynomial p of a vector of n coefficients at a, as  *)
(* the code addresses it: 4 * i + 1024 * p bytes from a. PWACC_LOADS_TAC l   *)
(* takes each assumption !j. j < n ==> read (bytes32 (a + 4 * j)) s0 = x j   *)
(* with n a numeral and, at the start of the body of iteration i, gives the  *)
(* values of coefficient i of polynomials 0, ..., l - 1 at those addresses   *)
(* as assumptions: the simulation drops a load whose value it cannot find at *)
(* its address in the assumptions.                                           *)
(* ------------------------------------------------------------------------- *)

let PWACC_LOAD = prove
 (`!a (x:num->int32) (s:armstate) n p i.
        (!j. j < n
             ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j) /\
        256 * p + i < n
        ==> read(memory :> bytes32
             (word_add a (word_add (word(4 * i)) (word(1024 * p))))) s =
            x(256 * p + i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `256 * p + i`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word(4 * i)) (word(1024 * p)):int64 = word(4 * (256 * p + i))`
   ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let PWACC_LOADS_TAC =
  let pat = `!j. j < n
                 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                     (x:num->int32) j`
  and norm = NUM_REDUCE_CONV THENC
             REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] in
  fun l ->
    W(fun (asl,w) ->
      let ths = filter (fun th ->
        try is_numeral(instantiate (term_match [] pat (concl th)) `n:num`)
        with Failure _ -> false) (map snd asl) in
      MAP_EVERY (fun th ->
        let i = term_match [] pat (concl th) in
        let a = instantiate i `a:int64` and x = instantiate i `x:num->int32`
        and n = instantiate i `n:num` in
        MAP_EVERY (fun p ->
          MP_TAC(SPECL [a; x; `s0:armstate`; n; mk_small_numeral p; `i:num`]
                       PWACC_LOAD) THEN
          ANTS_TAC THENL
           [CONJ_TAC THENL [ACCEPT_TAC th; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
          DISCH_THEN(fun th -> ASSUME_TAC(CONV_RULE norm th)))
         (0--(l-1))) ths);;

(* ------------------------------------------------------------------------- *)
(* The value stored for coefficient i is the high 32 bits of p + t * -q,     *)
(* where p is the sum of the 7 products as the model computes it, with       *)
(* SMADDL and the registers as integer values, and t is the low half of p    *)
(* times q^-1 mod 2^32. PWACC_LANE_TAC first writes each sum of the model as *)
(* a word_add of word_mul (word_sx _) (word_sx _), as mld_polyvec_dot does,  *)
(* and then shows the stored value to be mld_montgomery_reduce p, with p as  *)
(* a variable, for the term taken from the assumption that the simulation    *)
(* produces, so that it has the zero extensions of the model exactly.        *)
(* ------------------------------------------------------------------------- *)

let PWACC_STEP = prove
 (`!p:int64 a:int32 b:int32.
     iword(ival p + ival a * ival b) =
     word_add p (word_mul (word_sx a) (word_sx b))`,
  REWRITE_TAC[IWORD_INT_ADD; IWORD_INT_MUL; IWORD_IVAL; word_sx]);;

let PWACC_BASE = prove
 (`!a:int32 b:int32.
     iword(&0 + ival a * ival b):int64 =
     word_mul (word_sx a) (word_sx b)`,
  REWRITE_TAC[INT_ADD_LID; IWORD_INT_MUL; word_sx]);;

let PWACC_LANE_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `w:int64` l && free_in `x:num->int32` r then
      let th1 = REWRITE_RULE[WORD_ZX_ZX_32_64_32; PWACC_BASE; PWACC_STEP] th in
      let r1 = rhs(concl th1) in
      let inst = term_match []
       `word_zx(word_ishr(iword(ival(p:int64) + (c:int))) 32):int32` r1 in
      let p0 = instantiate inst `p:int64` and pv = `pp:int64` in
      let lemma = prove
       (mk_forall(pv,mk_eq(subst[pv,p0] r1,
                          mk_comb(`mld_montgomery_reduce`,pv))),
        GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[WORD_ZX_ZX_32_64_32; INT_ADD_LID; ADD_CLAUSES] THEN
        REWRITE_TAC[WORD_RULE
         `word(val(x:int32) * c):int32 = word_mul x (word c)`] THEN
        SPEC_TAC(`word_mul (word_zx (pp:int64)) (word 58728449):int32`,
                 `t:int32`) THEN
        GEN_TAC THEN
        SUBGOAL_THEN `ival (t:int32) = ival (word_sx t:int64)` SUBST1_TAC THENL
         [MATCH_MP_TAC(GSYM(ISPEC `t:int32` IVAL_WORD_SX)) THEN
          REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        SPEC_TAC(`word_sx (t:int32):int64`,`u:int64`) THEN GEN_TAC THEN
        SUBGOAL_THEN
         `iword(ival pp + ival u * -- &8380417):int64 =
          word_sub pp (word_mul u (word 8380417))`
        SUBST1_TAC THENL
         [REWRITE_TAC[IWORD_INT_ADD; IWORD_INT_MUL; IWORD_IVAL;
                      IWORD_INT_NEG; GSYM word_sub] THEN
          CONV_TAC WORD_RULE;
          ALL_TAC] THEN
        SPEC_TAC(`word_sub pp (word_mul u (word 8380417)):int64`,
                 `v:int64`) THEN
        GEN_TAC THEN BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th1)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256 iterations  *)
(* of the outer loop handles coefficient i of the 7 polynomials, with the    *)
(* inner loop over the polynomials unrolled; the loop test is the end of the *)
(* body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an      *)
(* iteration depend on its index only.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(w:int64) (u:int64) (v:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil w u v pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop w u v pc returnaddress i))
          (f_ev_prol w u v pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `w:int64`; `u:int64`; `v:int64`;
    `x:num->int32`; `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              mld_polyvec_pointwise_acc_montgomery; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   `pc + mldsa87_polyvecl_pointwise_acc_montgomery_loop1`
   `pc + mldsa87_polyvecl_pointwise_acc_montgomery_loop1_exit`
   `\i s. read X0 s = w /\ read X1 s = u /\ read X2 s = v /\
          read X3 s = word(4 * i) /\
          read X7 s = word 58728449 /\ read X8 s = word 4286586879 /\
          read X30 s = returnaddress /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add u (word(4 * j)))) s =
                   x j) /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add w (word(4 * j)))) s =
                   mld_montgomery_reduce (mld_polyvec_dot 7 x y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The outer loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    PWACC_LOADS_TAC 7 THEN
    ARM_STEPS_TAC EXEC (1--59) THEN
    PWACC_LANE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV PWACC_DOT_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
