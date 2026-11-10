(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the x86-64 functions of mldsa-native that    *)
(* call others for the polynomials of vectors and keys (polyvec.c,           *)
(* polyvec_lazy.c, packing.c), beyond those of                               *)
(* utils/mldsa_native_polyvec.ml: the forms in which the compiled code steps *)
(* its pointers, the copy of a vector that gcc inlines as REP MOVSQ, and the *)
(* argument that the System V ABI passes on the stack.                       *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* A pointer stepped by 128 bytes, which gcc does as SUB of the 8-bit -128,  *)
(* the simulation giving word_sub x (word (2^64 - 128)): WORD_SUB_M128 puts  *)
(* it in the form word_add x (word 128) of the invariants and of the loop    *)
(* tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

let WORD_SUB_M128 = prove
 (`!x:int64. word_sub x (word 18446744073709551488) = word_add x (word 128)`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_neg(word 128):int64`)) THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* A vector copied by REP MOVSQ, the memcpy of a multiple of 8 bytes that    *)
(* gcc inlines, with the direction flag clear, as in the x86 proofs of       *)
(* mlkem-native (KEM_MOVSQ_STEP_TAC of utils/mlkem_native_kem.ml). The       *)
(* simulation gives the bytes of the destination as x86_qstringcopy of those *)
(* of the source and of the destination before; MOVSQ_STEP_TAC execth n q    *)
(* steps the REP MOVSQ of q quadwords, step n, and turns that into the fact  *)
(* that the destination has the bytes of the source, using an assumption     *)
(* read (memory :> bytes(a,8 * q)) s = x for the source (as GHOST_INTRO_TAC  *)
(* gives) and that source and destination do not overlap.                    *)
(* ------------------------------------------------------------------------- *)

let MOVSQ_FACT = prove
 (`!df a b n x s s' t.
        read (memory :> bytes(b,8 * n)) s' =
        read (memory :> bytes(b,8 * n))
         (write (memory :> bytes(b,8 * n))
           (x86_qstringcopy df a b n x (read (memory :> bytes(b,8 * n)) s))
           t)
        ==> nonoverlapping (a,8 * n) (b,8 * n) /\
            read (memory :> bytes(a,8 * n)) s = x /\
            8 * n <= 2 EXP 64
            ==> read (memory :> bytes(b,8 * n)) s' = x`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[X86_QSTRINGCOPY_NONOVERLAPPING] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[REWRITE_RULE[valid_component]
    (VALID_COMPONENT_CONV `valid_component memory`)] THEN
  ASM_SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[READ_BYTES_BOUND]);;

let MOVSQ_STEP_TAC execth st n =
  let sname = "s" ^ string_of_int st in
  let sv = mk_var(sname,`:x86state`) in
  let is_qsc t = match strip_comb t with
                   Const("x86_qstringcopy",_),_ -> true | _ -> false in
  let lemma = GEN_ALL(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                (INST [mk_small_numeral n,`n:num`] (SPEC_ALL MOVSQ_FACT))) in
  X86_VSTEPS_TAC execth [st] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(a,k)) s`) (lhand c) &&
       rand(lhand c) = sv && can (find_term is_qsc) (rand c)
    then MP_TAC(MATCH_MP lemma th) else NO_TAC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]; CONV_TAC NUM_REDUCE_CONV];
    DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC sname;;

(* ------------------------------------------------------------------------- *)
(* VEC_ROW_ADDR_TAC of utils/mldsa_native_polyvec.ml for the address of row  *)
(* i of a matrix that the code computes with LEA, SUB and a shift, whose     *)
(* value for each i < k needs the arithmetic on numbers and on words         *)
(* repeated: ROW_ADDR_TAC tm, for tm of the form read X s = word_add a       *)
(* (word(n * i)), replaces the assumption read X s = t by tm, checking that  *)
(* t and the right side of tm are equal for each i < k, given an assumption  *)
(* i < k for a numeral k.                                                    *)
(* ------------------------------------------------------------------------- *)

let ROW_ADDR_TAC tm =
  let l = lhs tm and r = rhs tm in
  let iv = rand(rand(rand r)) in
  FIRST_X_ASSUM(fun th ->
    if lhs(concl th) <> l then failwith "ROW_ADDR_TAC" else
    SUBGOAL_THEN (mk_eq(rhs(concl th),r))
      (fun eq -> ASSUME_TAC(TRANS th eq)) THENL
     [FIRST_ASSUM(fun bth ->
        let c = concl bth in
        if is_binary "<" c && lhand c = iv && is_numeral(rand c) then
          MP_TAC bth THEN SPEC_TAC(iv,iv) THEN
          CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC
                                        WORD_REDUCE_CONV))) THEN
          REWRITE_TAC[WORD_ADD; WORD_VAL; WORD_ADD_0] THEN NO_TAC
        else failwith "ROW_ADDR_TAC");
      ALL_TAC]);;
