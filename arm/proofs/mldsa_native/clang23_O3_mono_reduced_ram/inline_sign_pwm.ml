(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the inlined loops of poly_pointwise_montgomery in verify_      *)
(* internal and signature_internal of mldsa-native's clang 23 -O3            *)
(* monolithic reduced-RAM build (see inline_sign.ml for the conventions).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;

(* ------------------------------------------------------------------------- *)
(* The Montgomery reduction as clang computes it in 64-bit registers:        *)
(*   p = smull x y; t = asr (p * (q^-1 << 32)) 32 (the low word of p * q^-1  *)
(*   sign-extended); p' = smaddl t (-q) p; the result is bits 32..63 of p',  *)
(* with the sign-extensions and the signed products as the model writes them *)
(* (iword, ival, word_zx). The lemmas keep clear of bit-blasting products.   *)
(* ------------------------------------------------------------------------- *)

let INLINE_ZX_USHR = prove
 (`!y:int64. word_zx (word_ushr y 32):int32 = word_subword y (32,32)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INLINE_ZX_ISHR = prove
 (`!y:int64. word_zx (word_ishr y 32):int32 = word_subword y (32,32)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INLINE_ZX_SX = prove
 (`!y:int32. word_zx (word_sx y:int64):int32 = y`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INLINE_SUBWORD_SHL = prove
 (`!y:int64. word_subword (word_shl y 32) (32,32):int32 = word_zx y`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INLINE_MUL_SHL = prove
 (`!y:int64. word_mul y (word 4294967296) = word_shl y 32`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INLINE_ZX_MUL_QINV = prove
 (`!y:int64. word_zx (word_mul y (word 58728449)):int32 =
             word_mul (word_zx y) (word 58728449)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`y:int64`; `word 58728449:int64`]
          (INST_TYPE [`:32`,`:N`; `:64`,`:M`] WORD_ZX_MUL)) THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[]);;

(*** t = the low word of p * (q^-1 * 2^32), shifted down arithmetically ***)

let INLINE_MONT_T = prove
 (`!P:int64. word_zx (word_ishr (word (0 + val P * 252236767799803904):int64) 32):int32 =
             word_mul (word_zx P) (word 58728449)`,
  GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `word (val (P:int64) * 252236767799803904):int64 =
                word_shl (word_mul P (word 58728449)) 32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INLINE_MUL_SHL; word_mul; modular; VAL_WORD;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[INLINE_ZX_ISHR; INLINE_SUBWORD_SHL; INLINE_ZX_MUL_QINV;
                WORD_ZX_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]]);;

let INLINE_MONTRED_LANE = prove
 (`!P:int64.
     word_zx (word_ushr
       (iword (ival P +
               ival (word_zx (word_ishr
                      (word (0 + val P * 252236767799803904):int64) 32):int32) *
               --(&8380417)):int64) 32):int32 = mld_montgomery_reduce P`,
  GEN_TAC THEN REWRITE_TAC[INLINE_MONT_T; mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[IWORD_INT_ADD; IWORD_INT_MUL; IWORD_IVAL; IWORD_INT_NEG;
              GSYM WORD_IWORD] THEN
  REWRITE_TAC[GSYM word_sx; INLINE_ZX_USHR] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(*** The signed product of two 32-bit values, as SMULL leaves it ***)

let INLINE_SMULL = prove
 (`!(x:int32) (y:int32).
     iword (&0 + ival (word_zx (word_sx y:int64):int32) *
                 ival (word_zx (word_sx x:int64):int32)):int64 =
     word_mul (word_sx x) (word_sx y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INLINE_ZX_SX; INT_ADD_LID; IWORD_INT_MUL; IWORD_IVAL;
              GSYM word_sx] THEN
  CONV_TAC WORD_RULE);;

(*** 4 coefficients per iteration with scalar loads: the inputs split into ***)
(*** the coefficients of the iteration (as VEC4_LOOP_BODY_TAC does, but    ***)
(*** without merging them into 128-bit words)                              ***)

let INLINE_SPLIT4_TAC =
  let pat_rw = `!j. 4 * i <= j /\ j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_ro = `!j. j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and j_tm = `j:num` and k_tm = `k:num`
  and j4_tm = `4 * i + k` and k4_tm = `k < 4` in
  let lanes_tac =
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC in
  let split_rw th =
    MP_TAC(GEN_REWRITE_RULE I
            [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)] th) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN lanes_tac
  and split_ro th =
    let eqn = rand(snd(dest_forall(concl th))) in
    let t = mk_forall(k_tm,mk_imp(k4_tm,subst [j4_tm,j_tm] eqn)) in
    SUBGOAL_THEN t MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_ARITH_TAC;
      lanes_tac] in
  W(fun (asl,w) ->
      let rws = filter (can (term_match [] pat_rw) o concl o snd) asl
      and ros = filter (can (term_match [] pat_ro) o concl o snd) asl in
      MAP_EVERY (fun (_,th) -> UNDISCH_THEN (concl th) split_rw) rws THEN
      MAP_EVERY (fun (_,th) -> split_ro th) ros);;

(*** The addresses of the loads that the code forms from a pointer with an ***)
(*** offset (word_add (word_add b (word 8)) (word (16 * i)) and so on) are ***)
(*** not those of the lanes as INLINE_SPLIT4_TAC writes them; each equation ***)
(*** "new = old" (a string, proved by WORD_RULE) gives the fact about the  ***)
(*** lane at old also at new.                                              ***)

let INLINE_NEG4 = prove
 (`word 18446744073709551612:int64 = word_neg (word 4)`,
  CONV_TAC WORD_REDUCE_CONV);;

let sublist a n l =
  let rec go i = function [] -> [] | h::t ->
    if i >= a + n then [] else if i >= a then h :: go (i+1) t else go (i+1) t in
  go 0 l;;

(*** word K with K >= 2^63 as the negation of a small word, for WORD_RULE ***)

let INLINE_NEGNUM_CONV =
  fun tm ->
    match tm with
      Comb(Const("word",_),n) when is_numeral n && type_of tm = `:int64`
        && dest_numeral n >=/ ((Num.num_of_int 2) **/ (Num.num_of_int 63)) ->
        let m = ((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/ dest_numeral n in
        let rhs_tm = mk_comb(`word_neg:int64->int64`,
                             mk_comb(`word:num->int64`,mk_numeral m)) in
        prove(mk_eq(tm,rhs_tm),CONV_TAC WORD_REDUCE_CONV)
    | _ -> failwith "INLINE_NEGNUM_CONV";;

let INLINE_ALIAS_THM (s:string) =
  let eq = parse_term s in
  let nth = (REWRITE_CONV[WORD_ADD; INLINE_NEG4] THENC
             DEPTH_CONV INLINE_NEGNUM_CONV) eq in
  let eq' = rand(concl nth) in
  let atoms = setify(find_terms (fun t -> is_comb t && rator t = `word:num->int64` &&
                                          not(is_numeral(rand t))) eq') in
  let vs = map (fun t -> genvar `:int64`) atoms in
  let eqv = subst (zip vs atoms) eq' in
  let th' = SPECL atoms (prove(list_mk_forall(vs,eqv),
                               REPEAT GEN_TAC THEN CONV_TAC WORD_RULE)) in
  EQ_MP (SYM nth) th';;

(*** The address of a fact read (memory :> bytes32 addr) s = v ***)

let INLINE_FACT_ADDR th =
  try let l = lhs(concl th) in
      if is_comb l && is_comb(rator l) &&
         fst(dest_const(rator(rator l))) = "read"
      then rand(rand(rand(rator l))) else failwith ""
  with Failure _ -> failwith "INLINE_FACT_ADDR";;

let INLINE_ALIAS_TAC (eqs:string list) =
  MAP_EVERY (fun s ->
    let eqth = INLINE_ALIAS_THM s in
    let old_tm = rhs(concl eqth) in
    FIRST_X_ASSUM(fun th ->
      if INLINE_FACT_ADDR th = old_tm
      then ASSUME_TAC th THEN
           ASSUME_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(SYM eqth)))) th)
      else failwith "INLINE_ALIAS_TAC")) eqs;;

(*** The converse, for the facts about the stores: the fact at the address ***)
(*** new (as the code forms it) is also stated at old (the lane).          ***)

let INLINE_ALIAS_BACK_TAC (eqs:string list) =
  MAP_EVERY (fun s ->
    let eqth = INLINE_ALIAS_THM s in
    let new_tm = lhs(concl eqth) in
    TRY(FIRST_X_ASSUM(fun th ->
      if INLINE_FACT_ADDR th = new_tm
      then ASSUME_TAC th THEN
           ASSUME_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV eqth))) th)
      else failwith "INLINE_ALIAS_BACK_TAC"))) eqs;;

(*** The frame assumption of the steps, with the addresses of the stores ***)
(*** as the lanes (the tactic for the frame goal needs the form a + n)  ***)

let INLINE_FRAME_TAC (eqs:string list) =
  let ths = map INLINE_ALIAS_THM eqs in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "MAYCHANGE"))
           (concl th)
    then REWRITE_RULE ths th else th);;

(*** The lanes of the output as the code writes them, in the goal ***)

let INLINE_ALIAS_GOAL_TAC (eqs:string list) =
  REWRITE_TAC(map (SYM o INLINE_ALIAS_THM) eqs);;

(*** The events of the loads and stores in the form that the memory-safety ***)
(*** tactic handles: each equation "code = clean" is applied to the goal, ***)
(*** one list after the other (an equation of a list may match a subterm   ***)
(*** of one of an earlier list).                                          ***)

let INLINE_EVENT_TAC (eqss:string list list) =
  MAP_EVERY (fun eqs -> REWRITE_TAC(map INLINE_ALIAS_THM eqs)) eqss;;

(* ------------------------------------------------------------------------- *)
(* Shape 4 (32 instructions, 27 instances): 4 coefficients per iteration, a  *)
(* at R1 (written), b at R6, b + 8 at R4, the byte offset at R2 (from 0, +16  *)
(* per iteration), the constants q^-1 << 32 at R12 and -q at R14:            *)
(*   add R0, R1, R2; add R3, R4, R2; ldrsw R5, [R6, R2]; ldpsw R7, R8, [R0]; *)
(*   ldursw R9, [R3, #-4]; add R2, R2, #16; ldpsw R10, R11, [R0, #8];        *)
(*   smull ...; cmp R2, #1024; ...; stp w, w, [R0]; stp w, w, [R0, #8];      *)
(*   b.ne                                                                    *)
(* ------------------------------------------------------------------------- *)

let INLINE_PWM_ALIASES = [
  "word_add a (word (16 * i + 4)):int64 = word_add (word_add a (word (16 * i))) (word 4)";
  "word_add a (word (16 * i + 8)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
  "word_add a (word (16 * i + 12)):int64 = word_add (word_add a (word (16 * i))) (word 12)";
  "word_add b (word (8 + 16 * i + 18446744073709551612)):int64 = word_add (word_add b (word (16 * i))) (word 4)";
  "word_add b (word (8 + 16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)";
  "word_add (word_add b (word 8)) (word (16 * i + 4)):int64 = word_add (word_add b (word (16 * i))) (word 12)"];;

let INLINE_PWM_EVENTS = [
  ["word_add (word_add (word_add b (word 8)) (word (16 * i))) (word 18446744073709551612):int64 = word_add (word_add b (word (16 * i))) (word 4)"];
  ["word_add (word_add b (word 8)) (word (16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)"]];;

let INLINE_PWM_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  let modregs = map r [0;2;3;5;7;8;9;10;11;13] in
  let tm = INLINE_PWM_LOOP_TERM mc loop exit (r 1) (r 6) (r 4) (r 2) (r 12)
             (r 14) modregs in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @a@ s = a /\\ read @b@ s = b /\\
          read @b8@ s = word_add b (word 8) /\\
          read @i@ s = word(16 * i) /\\
          read @qi@ s = word 0x0380200100000000 /\\
          read @nq@ s = word 0xffffffffff801fff /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   (y:num->int32) j) /\\
          (!j. 4 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))"
   ["a",r 1; "b",r 6; "b8",r 4; "i",r 2; "qi",r 12; "nq",r 14]) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `b:int64`;
                       `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS;
              mld_poly_pointwise_montgomery; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN INLINE_SPLIT4_TAC THEN
    INLINE_ALIAS_TAC INLINE_PWM_ALIASES THEN
    ARM_STEPS_TAC exec (1--32) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_SMULL; INLINE_MONTRED_LANE]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[WORD_ADD_0] THEN
        INLINE_ALIAS_GOAL_TAC(sublist 0 3 INLINE_PWM_ALIASES) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    INLINE_EVENT_TAC INLINE_PWM_EVENTS THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    INLINE_EXIT_TAC]);;

(*** The instances of shape 4: function, label of the head, label of the ***)
(*** exit, registers R0..R14                                            ***)

let INLINE_PWM4_INSTANCES = [
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop6", "mldsa44_signature_internal_loop6_exit", ["X9"; "X19"; "X8"; "X12"; "X20"; "X10"; "X23"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop7", "mldsa44_signature_internal_loop7_exit", ["X9"; "X19"; "X8"; "X12"; "X20"; "X10"; "X23"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop8", "mldsa44_signature_internal_loop8_exit", ["X9"; "X19"; "X8"; "X12"; "X20"; "X10"; "X23"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop9", "mldsa44_signature_internal_loop9_exit", ["X9"; "X19"; "X8"; "X12"; "X20"; "X10"; "X23"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop38", "mldsa44_signature_internal_loop38_exit", ["X9"; "X23"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop42", "mldsa44_signature_internal_loop42_exit", ["X9"; "X23"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa44_verify_internal", "mldsa44_verify_internal_loop8", "mldsa44_verify_internal_loop8_exit", ["X9"; "X27"; "X8"; "X12"; "X25"; "X10"; "X21"; "X11"; "X13"; "X14"; "X15"; "X16"; "X22"; "X17"; "X20"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop6", "mldsa65_signature_internal_loop6_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop7", "mldsa65_signature_internal_loop7_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop8", "mldsa65_signature_internal_loop8_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop9", "mldsa65_signature_internal_loop9_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop10", "mldsa65_signature_internal_loop10_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop11", "mldsa65_signature_internal_loop11_exit", ["X9"; "X22"; "X8"; "X12"; "X28"; "X10"; "X20"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop48", "mldsa65_signature_internal_loop48_exit", ["X9"; "X20"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop52", "mldsa65_signature_internal_loop52_exit", ["X9"; "X20"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa65_verify_internal", "mldsa65_verify_internal_loop9", "mldsa65_verify_internal_loop9_exit", ["X9"; "X28"; "X8"; "X12"; "X24"; "X10"; "X21"; "X11"; "X13"; "X14"; "X15"; "X16"; "X23"; "X17"; "X20"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop6", "mldsa87_signature_internal_loop6_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop7", "mldsa87_signature_internal_loop7_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop8", "mldsa87_signature_internal_loop8_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop9", "mldsa87_signature_internal_loop9_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop10", "mldsa87_signature_internal_loop10_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop11", "mldsa87_signature_internal_loop11_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop12", "mldsa87_signature_internal_loop12_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop13", "mldsa87_signature_internal_loop13_exit", ["X9"; "X21"; "X8"; "X12"; "X23"; "X10"; "X27"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop55", "mldsa87_signature_internal_loop55_exit", ["X9"; "X27"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop59", "mldsa87_signature_internal_loop59_exit", ["X9"; "X27"; "X8"; "X12"; "X0"; "X10"; "X18"; "X11"; "X13"; "X14"; "X15"; "X16"; "X26"; "X17"; "X28"]);
  ("mldsa87_verify_internal", "mldsa87_verify_internal_loop11", "mldsa87_verify_internal_loop11_exit", ["X9"; "X28"; "X8"; "X12"; "X24"; "X10"; "X21"; "X11"; "X13"; "X14"; "X15"; "X16"; "X25"; "X17"; "X20"]);

];;

let INLINE_PWM4_OF_INSTANCE (fn,hl,el,rs) =
  INLINE_PWM_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el rs;;

(* ------------------------------------------------------------------------- *)
(* Shape 7 (30 instructions, 15 instances; shape 6 is its 28 instructions   *)
(* variant and shape 16 a variant with indexed addressing): the pointers    *)
(* step, the count R8 goes from 256 down to 0 in steps of 4 (SUBS), the    *)
(* input b is read at R2 = b + 8 (stepped by the post-indexed LDPSW) and    *)
(* the output a is read and written at R5 = a + 12:                         *)
(*   ldpsw R0, R1, [R2, #-8]; ldpsw R3, R4, [R5, #-12];                      *)
(*   ldpsw R6, R7, [R2], #16; subs R8, R8, #4; smull ...; ldursw R4, [R5, #-4]; *)
(*   ...; ldrsw R6, [R5]; ...; stp w, w, [R5, #-12]; stp w, w, [R5, #-4];   *)
(*   add R5, R5, #16; b.ne                                                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_CNT4_STEP = prove
 (`!i. i < 64 ==> word_sub (word (256 - 4 * i)) (word 4):int64 =
                  word (256 - 4 * (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 - 4 * (i + 1) = (256 - 4 * i) - 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let INLINE_CNT4_TEST = prove
 (`!i. i < 64 ==> (val (word_sub (word (256 - 4 * i)) (word 4):int64) = 0 <=>
                   i + 1 = 64)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INLINE_CNT4_STEP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(256 - 4 * (i + 1)) MOD 2 EXP 64 = 256 - 4 * (i + 1)`
    SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

let INLINE_PTR_STEP = prove
 (`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let INLINE_PWM7_ALIASES = [
  "word_add a (word (12 + 16 * i)):int64 = word_add (word_add a (word (16 * i))) (word 12)";
  "word_add b (word (8 + 16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)";
  "word_add b (word ((8 + 16 * i) + 4)):int64 = word_add (word_add b (word (16 * i))) (word 12)";
  "word_add a (word ((12 + 16 * i) + 18446744073709551612)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
  "word_add a (word_sub (word (12 + 16 * i)) (word 12)):int64 = word_add a (word (16 * i))";
  "word_add a (word_sub (word (12 + 16 * i)) (word 8)):int64 = word_add (word_add a (word (16 * i))) (word 4)";
  "word_add a (word_sub (word (12 + 16 * i)) (word 4)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
  "word_add a (word_sub (word (12 + 16 * i)) (word 0)):int64 = word_add (word_add a (word (16 * i))) (word 12)";
  "word_add b (word_sub (word (8 + 16 * i)) (word 8)):int64 = word_add b (word (16 * i))";
  "word_add b (word_sub (word (8 + 16 * i)) (word 4)):int64 = word_add (word_add b (word (16 * i))) (word 4)"];;

let INLINE_PWM7_EVENTS = [
  ["word_sub (word_add a (word (12 + 16 * i))) (word 4):int64 = word_add (word_add a (word (16 * i))) (word 8)";
   "word_sub (word_add a (word (12 + 16 * i))) (word 12):int64 = word_add a (word (16 * i))";
   "word_add (word_add a (word (12 + 16 * i))) (word 18446744073709551612):int64 = word_add (word_add a (word (16 * i))) (word 8)";
   "word_add a (word ((12 + 16 * i) + 18446744073709551612)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
   "word_sub (word_add b (word (8 + 16 * i))) (word 8):int64 = word_add b (word (16 * i))"];
  ["word_add a (word (12 + 16 * i)):int64 = word_add (word_add a (word (16 * i))) (word 12)";
   "word_add b (word (8 + 16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)"]];;

(*** The loops with stepping pointers: bp (b + 8, read), ap (a + aoff, ***)
(*** read and written), the count cnt (from 256, SUBS #4), the constants ***)
(*** at qi and nq. idx = indices of (bp, ap, cnt, qi, nq, the registers ***)
(*** that the loop changes) in the canonical vector.                    ***)

let INLINE_PWMP_LOOP_TERM mc loop exit aoff idx (rs:string list) =
  let r k = List.nth rs k in
  let (ibp,iap,icnt,iqi,inq) = idx in
  let modidx = filter (fun k -> k <> iqi && k <> inq) (0--(length rs - 1)) in
  INLINE_FILL
   "exists f_events.
      forall e a b (x:num->int32) (y:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read @bp@ s = word_add b (word 8) /\\
                  read @ap@ s = word_add a (word @aoff@) /\\
                  read @cnt@ s = word 256 /\\
                  read @qi@ s = word 0x0380200100000000 /\\
                  read @nq@ s = word 0xffffffffff801fff /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i)))) s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @bp@ s = word_add b (word 1032) /\\
                  read @ap@ s = word_add a (word @aend@) /\\
                  read @cnt@ s = word 0 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_poly_pointwise_montgomery x y i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,1024; b,1024] [a,1024]))
             (MAYCHANGE [PC; @mod@] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   ["mc",mc; "loop",loop; "exit",exit; "bp",r ibp; "ap",r iap; "cnt",r icnt;
    "qi",r iqi; "nq",r inq; "aoff",string_of_int aoff;
    "aend",string_of_int (aoff + 1024);
    "mod",String.concat "; " (map r modidx)];;

let INLINE_PWMP_LOOP mc exec loop exit aoff idx nsteps aliases events
                     (rs:string list) =
  let r k = List.nth rs k in
  let (ibp,iap,icnt,iqi,inq) = idx in
  let tm = parse_term(INLINE_PWMP_LOOP_TERM mc loop exit aoff idx rs) in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @bp@ s = word_add b (word (8 + 16 * i)) /\\
          read @ap@ s = word_add a (word (@aoff@ + 16 * i)) /\\
          read @cnt@ s = word (256 - 4 * i) /\\
          read @qi@ s = word 0x0380200100000000 /\\
          read @nq@ s = word 0xffffffffff801fff /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   (y:num->int32) j) /\\
          (!j. 4 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))"
   ["bp",r ibp; "ap",r iap; "cnt",r icnt; "qi",r iqi; "nq",r inq;
    "aoff",string_of_int aoff]) in
  let rewr = [ARITH_RULE `4 * 64 = 256`; ARITH_RULE `8 + 16 * 64 = 1032`;
              ARITH_RULE `256 - 4 * 64 = 0`;
              ARITH_RULE `8 + 16 * 64 = 1032`;
              ARITH_RULE `12 + 16 * 64 = 1036`] in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `b:int64`;
                       `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS;
              mld_poly_pointwise_montgomery; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES;
                SUB_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN INLINE_SPLIT4_TAC THEN
    INLINE_ALIAS_TAC aliases THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_SMULL; INLINE_MONTRED_LANE]) THEN
    INLINE_ALIAS_BACK_TAC aliases THEN
    INLINE_FRAME_TAC aliases THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INLINE_CNT4_STEP; INLINE_CNT4_TEST] THEN
    REWRITE_TAC[INLINE_PTR_STEP] THEN
    LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[WORD_ADD_0] THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    INLINE_EVENT_TAC events THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE rewr) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let INLINE_PWM7_LOOP mc exec loop exit (rs:string list) =
  INLINE_PWMP_LOOP mc exec loop exit 12 (2,5,8,9,12) 30
    INLINE_PWM7_ALIASES INLINE_PWM7_EVENTS rs;;

(*** The instances of shape 7: function, label of the head, label of the ***)
(*** exit, registers R0..R12                                            ***)

let INLINE_PWM7_INSTANCES = [
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop11", "mldsa44_signature_internal_loop11_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X28"; "X17"; "X18"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop12", "mldsa44_signature_internal_loop12_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X28"; "X17"; "X18"; "X25"]);
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop13", "mldsa44_signature_internal_loop13_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X28"; "X17"; "X18"; "X25"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop13", "mldsa65_signature_internal_loop13_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X19"; "X17"; "X18"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop14", "mldsa65_signature_internal_loop14_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X19"; "X17"; "X18"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop15", "mldsa65_signature_internal_loop15_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X19"; "X17"; "X18"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop16", "mldsa65_signature_internal_loop16_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X19"; "X17"; "X18"; "X26"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop17", "mldsa65_signature_internal_loop17_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X19"; "X17"; "X18"; "X26"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop15", "mldsa87_signature_internal_loop15_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop16", "mldsa87_signature_internal_loop16_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop17", "mldsa87_signature_internal_loop17_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop18", "mldsa87_signature_internal_loop18_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop19", "mldsa87_signature_internal_loop19_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop20", "mldsa87_signature_internal_loop20_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop21", "mldsa87_signature_internal_loop21_exit", ["X11"; "X14"; "X8"; "X12"; "X13"; "X10"; "X15"; "X16"; "X9"; "X26"; "X17"; "X18"; "X28"]);

];;

let INLINE_PWM7_OF_INSTANCE (fn,hl,el,rs) =
  INLINE_PWM7_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el rs;;

(* ------------------------------------------------------------------------- *)
(* Shape 6 (28 instructions, 3 instances): as shape 7, with a at R5 = a + 8  *)
(* (LDPSW [R5, #-8] and [R5]; STP [R5, #-8] and [R5], #16 for the stores).   *)
(*   ldpsw R0, R1, [R2, #-8]; ldpsw R3, R4, [R5, #-8]; ldpsw R6, R7, [R5];    *)
(*   subs R8, R8, #4; ...; ldpsw R4, R9, [R2], #16; ...; b.ne                *)
(* ------------------------------------------------------------------------- *)

let INLINE_PWM6_ALIASES = [
  "word_add a (word_sub (word (8 + 16 * i)) (word 8)):int64 = word_add a (word (16 * i))";
  "word_add a (word_sub (word (8 + 16 * i)) (word 4)):int64 = word_add (word_add a (word (16 * i))) (word 4)";
  "word_add a (word (8 + 16 * i)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
  "word_add a (word ((8 + 16 * i) + 4)):int64 = word_add (word_add a (word (16 * i))) (word 12)";
  "word_add b (word_sub (word (8 + 16 * i)) (word 8)):int64 = word_add b (word (16 * i))";
  "word_add b (word_sub (word (8 + 16 * i)) (word 4)):int64 = word_add (word_add b (word (16 * i))) (word 4)";
  "word_add b (word (8 + 16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)";
  "word_add b (word ((8 + 16 * i) + 4)):int64 = word_add (word_add b (word (16 * i))) (word 12)"];;

let INLINE_PWM6_EVENTS = [
  ["word_sub (word_add a (word (8 + 16 * i))) (word 8):int64 = word_add a (word (16 * i))";
   "word_sub (word_add b (word (8 + 16 * i))) (word 8):int64 = word_add b (word (16 * i))"];
  ["word_add a (word (8 + 16 * i)):int64 = word_add (word_add a (word (16 * i))) (word 8)";
   "word_add b (word (8 + 16 * i)):int64 = word_add (word_add b (word (16 * i))) (word 8)"]];;

let INLINE_PWM6_LOOP mc exec loop exit (rs:string list) =
  INLINE_PWMP_LOOP mc exec loop exit 8 (2,5,8,10,12) 28
    INLINE_PWM6_ALIASES INLINE_PWM6_EVENTS rs;;


(* ------------------------------------------------------------------------- *)
(* Shape 16 (31 instructions, 3 instances): as shape 4, with a at R1 and b at *)
(* R4 both addressed with the byte offset R2 (from 0, + 16 per iteration):    *)
(*   add R0, R1, R2; add R3, R4, R2; add R2, R2, #16; ldpsw R5, R6, [R3];     *)
(*   ldpsw R7, R8, [R0]; ldpsw R9, R10, [R0, #8]; cmp R2, #1024; ...;         *)
(*   ldpsw R8, R3, [R3, #8]; ...; stp w, w, [R0]; stp w, w, [R0, #8]; b.ne    *)
(* with the constants q^-1 << 32 at R11 and -q at R13.                        *)
(* ------------------------------------------------------------------------- *)

let INLINE_PWM16_ALIASES =
  List.concat(map (fun p -> map (fun k ->
    Printf.sprintf "word_add %s (word (16 * i + %d)):int64 = word_add (word_add %s (word (16 * i))) (word %d)" p k p k)
   [4;8;12]) ["a";"b"]);;
let INLINE_PWM16_EVENTS = [];;

let INLINE_PWM16_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_FILL
   "exists f_events.
      forall e a b (x:num->int32) (y:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read @a@ s = a /\\ read @b@ s = b /\\
                  read @i@ s = word 0 /\\
                  read @qi@ s = word 0x0380200100000000 /\\
                  read @nq@ s = word 0xffffffffff801fff /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i)))) s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @i@ s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_poly_pointwise_montgomery x y i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,1024; b,1024] [a,1024]))
             (MAYCHANGE [PC; @mod@] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   ["mc",mc; "loop",loop; "exit",exit; "a",r 1; "b",r 4; "i",r 2;
    "qi",r 11; "nq",r 13;
    "mod",String.concat "; " (map r [0;2;3;5;6;7;8;9;10;12])];;

let INLINE_PWM16_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  let tm = parse_term(INLINE_PWM16_LOOP_TERM mc loop exit rs) in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @a@ s = a /\\ read @b@ s = b /\\
          read @i@ s = word(16 * i) /\\
          read @qi@ s = word 0x0380200100000000 /\\
          read @nq@ s = word 0xffffffffff801fff /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   (y:num->int32) j) /\\
          (!j. 4 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))"
   ["a",r 1; "b",r 4; "i",r 2; "qi",r 11; "nq",r 13]) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `b:int64`;
                       `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS;
              mld_poly_pointwise_montgomery; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN INLINE_SPLIT4_TAC THEN
    INLINE_ALIAS_TAC INLINE_PWM16_ALIASES THEN
    ARM_STEPS_TAC exec (1--31) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_SMULL; INLINE_MONTRED_LANE]) THEN
    INLINE_ALIAS_BACK_TAC INLINE_PWM16_ALIASES THEN
    INLINE_FRAME_TAC INLINE_PWM16_ALIASES THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[WORD_ADD_0] THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    INLINE_EVENT_TAC INLINE_PWM16_EVENTS THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    INLINE_EXIT_TAC]);;

(*** The instances of shape 6: function, label of the head, label of the ***)
(*** exit, registers R0..                                                ***)

let INLINE_PWM6_INSTANCES = [
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop10", "mldsa44_signature_internal_loop10_exit", ["X11"; "X14"; "X9"; "X12"; "X13"; "X8"; "X15"; "X16"; "X10"; "X17"; "X28"; "X18"; "X25"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop12", "mldsa65_signature_internal_loop12_exit", ["X11"; "X14"; "X9"; "X12"; "X13"; "X8"; "X15"; "X16"; "X10"; "X17"; "X19"; "X18"; "X26"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop14", "mldsa87_signature_internal_loop14_exit", ["X11"; "X14"; "X9"; "X12"; "X13"; "X8"; "X15"; "X16"; "X10"; "X17"; "X26"; "X18"; "X28"]);

];;

let INLINE_PWM6_OF_INSTANCE (fn,hl,el,rs) =
  INLINE_PWM6_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el rs;;

(*** The instances of shape 16: function, label of the head, label of the ***)
(*** exit, registers R0..                                                ***)

let INLINE_PWM16_INSTANCES = [
  ("mldsa44_signature_internal", "mldsa44_signature_internal_loop29", "mldsa44_signature_internal_loop29_exit", ["X9"; "X20"; "X8"; "X10"; "X18"; "X11"; "X14"; "X12"; "X13"; "X15"; "X16"; "X28"; "X17"; "X25"]);
  ("mldsa65_signature_internal", "mldsa65_signature_internal_loop39", "mldsa65_signature_internal_loop39_exit", ["X9"; "X22"; "X8"; "X10"; "X18"; "X11"; "X14"; "X12"; "X13"; "X15"; "X16"; "X19"; "X17"; "X26"]);
  ("mldsa87_signature_internal", "mldsa87_signature_internal_loop46", "mldsa87_signature_internal_loop46_exit", ["X9"; "X23"; "X8"; "X10"; "X18"; "X11"; "X14"; "X12"; "X13"; "X15"; "X16"; "X26"; "X17"; "X28"]);

];;

let INLINE_PWM16_OF_INSTANCE (fn,hl,el,rs) =
  INLINE_PWM16_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el rs;;
