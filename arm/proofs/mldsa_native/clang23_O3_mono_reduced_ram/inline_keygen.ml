(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for mldsa{44,65,87}_pk_from_sk and keypair_internal of the  *)
(* clang 23 -O3 monolithic reduced-RAM build.                                *)
(*                                                                           *)
(* The comparison of the recomputed packed t0 with the one in the secret key *)
(* is mld_ct_memcmp (ct.h), which clang vectorizes: a loop over 32 bytes at  *)
(* a time that loads two chunks of 16 bytes of each side (LDP and two LDR),  *)
(* XORs them, ORs the two differences into the accumulators v0 and v18 and   *)
(* folds permutations of them (TBL) into the accumulators v1 to v7 and v16   *)
(* for the useless XOR sum s of mld_ct_memcmp. The lemma INLINE_MEMCMP_LOOP  *)
(* says what the loop does to v0 and v18, as mld_or_fold of the even and odd *)
(* chunks, and that it changes v1 to v7 and v16 in a way it does not say:    *)
(* the sum s is XORed twice into the result and so cancels.                  *)
(*   add X10, XB, X9; ldp q23, q24, [X8, #-16]; sub X11, X10, #K1;           *)
(*   sub X10, X10, #K2; add X9, X9, #32; ldr q22, [X11]; ldr q25, [X10];     *)
(*   cmp X9, #END; add X8, X8, #32; eor, eor, 8 tbl, 2 orr, 8 eor; b.ne      *)
(* with K1 = OFS + 16 and K2 = OFS (the offset of t0 in the secret key).     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pwm.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;

(*** rs = [X8 (pointer into sk); X9 (index); X10; X11; XB (the buffer)]. The ***)
(*** chunks of t0 in sk are at sk + OFS + 16 k, the lemma is stated for sk  ***)
(*** itself so that the pointer X8 = sk + OFS + 16 is that of the caller    ***)

let INLINE_MEMCMP_TERM mc loop exit n ofs (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (sk:int64) (bb:int64) (a:num->int128) (b:num->int128) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add sk (word %d) /\\
                  read %s s = word %d /\\
                  read %s s = bb /\\
                  read Q0 s = word 0 /\\ read Q18 s = word 0 /\\
                  (!k. k < %d
                       ==> read(memory :> bytes128(word_add sk (word(%d + 16 * k))))
                             s = a k) /\\
                  (!k. k < %d
                       ==> read(memory :> bytes128(word_add bb (word(16 * k))))
                             s = b k) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add sk (word %d) /\\
                  read %s s = word %d /\\
                  read %s s = bb /\\
                  read Q0 s = mld_or_fold (\\k. a (2 * k)) (\\k. b (2 * k)) %d /\\
                  read Q18 s = mld_or_fold (\\k. a (2 * k + 1))
                                           (\\k. b (2 * k + 1)) %d /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events sk bb pc /\\
                     memaccess_inbounds e2 [word_add sk (word %d),%d; bb,%d] []))
             (MAYCHANGE [PC; %s; %s; %s; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                         Q16; Q18; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29;
                         Q30; Q31] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events])"
   mc loop (r 0) (ofs + 16) (r 1) (ofs + 16) (r 4) (2 * n) ofs (2 * n) exit (r 0)
   (ofs + 16 + 32 * n) (r 1) (ofs + 16 + 32 * n) (r 4) n n ofs (32 * n) (32 * n)
   (r 0) (r 1) (r 2) (r 3));;

let INLINE_MEMCMP_INV n ofs (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "\\i s. read %s s = word_add sk (word(%d + 32 * i)) /\\
          read %s s = word(%d + 32 * i) /\\
          read %s s = bb /\\
          read Q0 s = mld_or_fold (\\k. a (2 * k)) (\\k. b (2 * k)) i /\\
          read Q18 s = mld_or_fold (\\k. a (2 * k + 1))
                                   (\\k. b (2 * k + 1)) i /\\
          (!k. k < %d
               ==> read(memory :> bytes128(word_add sk (word(%d + 16 * k)))) s =
                   a k) /\\
          (!k. k < %d
               ==> read(memory :> bytes128(word_add bb (word(16 * k)))) s =
                   b k)"
   (r 0) (ofs + 16) (r 1) (ofs + 16) (r 4) (2 * n) ofs (2 * n));;

(*** The loads of the body at the lane of iteration i, as the simulator    ***)
(*** writes the addresses: the facts about chunks 2i and 2i+1 of both sides ***)
(*** (the LDP of two Q registers reads 256 bits, which is also given).      ***)

let INLINE_MEMCMP_SPEC_FACT_X extra x k ofs tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC k o check (fun th ->
      is_forall (concl th) && free_in x (concl th))) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC([ARITH_RULE `16 * (2 * i) = 32 * i`;
                   ARITH_RULE `16 * (2 * i + 1) = 32 * i + 16`] @ extra) THEN
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;

let INLINE_MEMCMP_SPEC_FACT = INLINE_MEMCMP_SPEC_FACT_X [];;

(*** The alias of every fact at the address old (the right side of the   ***)
(*** equation) also at the address new (the left side)                    ***)

let INLINE_MEMCMP_ALIAS_ALL (eqs:string list) =
  MAP_EVERY (fun s ->
    let eqth = INLINE_ALIAS_THM s in
    let old_tm = rhs(concl eqth) in
    W(fun (asl,_) ->
      let ths = mapfilter (fun (_,th) ->
        if INLINE_FACT_ADDR th = old_tm
        then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(SYM eqth)))) th
        else failwith "no") asl in
      MAP_EVERY ASSUME_TAC ths)) eqs;;

let INLINE_MEMCMP_256_TAC base =
  W(fun (asl,_) ->
    let f128 = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         can (term_match [] `read (memory :> bytes128 a) (s0:armstate)`) (lhs c)
      then th else fail()) asl in
    let tm = subst [base,`A:int64`] `read (memory :> bytes256 A) (s0:armstate)` in
    let eth = GEN_REWRITE_CONV I [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm in
    let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
    ASSUME_TAC(REWRITE_RULE f128 eth));;

let INLINE_MEMCMP_FACTS_TAC ofs =
  let k1 = string_of_int(ofs + 16) in
  let k0 = string_of_int ofs in
  let ss = Printf.sprintf in
  INLINE_MEMCMP_SPEC_FACT `sk:int64` `2*i` ofs
    (parse_term(ss "read (memory :> bytes128 (word_add (sk:int64) (word (%d + 32 * i)))) s0 = (a:num->int128) (2 * i)" ofs)) THEN
  INLINE_MEMCMP_SPEC_FACT `sk:int64` `2*i+1` ofs
    (parse_term(ss "read (memory :> bytes128 (word_add (sk:int64) (word (%d + 32 * i + 16)))) s0 = (a:num->int128) (2 * i + 1)" ofs)) THEN
  INLINE_MEMCMP_SPEC_FACT `bb:int64` `2*i` ofs
    `read (memory :> bytes128 (word_add bb (word (32 * i)))) s0 = b (2 * i)` THEN
  INLINE_MEMCMP_SPEC_FACT `bb:int64` `2*i+1` ofs
    `read (memory :> bytes128 (word_add bb (word (32 * i + 16)))) s0 =
     b (2 * i + 1)` THEN
  INLINE_MEMCMP_256_TAC (parse_term(ss "word_add (sk:int64) (word (%d + 32 * i))" ofs)) THEN
  INLINE_MEMCMP_ALIAS_ALL
   [ss "word_add sk (word_sub (word (%s + 32 * i)) (word 16)):int64 = word_add sk (word (%s + 32 * i))" k1 k0;
    ss "word_add sk (word_sub (word (%s + 32 * i)) (word 0)):int64 = word_add sk (word (%s + 32 * i + 16))" k1 k0;
    ss "word_sub (word_add sk (word (%s + 32 * i))) (word 16):int64 = word_add sk (word (%s + 32 * i))" k1 k0;
    ss "word_add sk (word (%s + 32 * i)):int64 = word_add sk (word (%s + 32 * i + 16))" k1 k0;
    ss "word_add bb (word_sub (word (%s + 32 * i)) (word %s)):int64 = word_add bb (word (32 * i))" k1 k1;
    ss "word_add bb (word_sub (word (%s + 32 * i)) (word %s)):int64 = word_add bb (word (32 * i + 16))" k1 k0;
    ss "word_sub (word_add bb (word (%s + 32 * i))) (word %s):int64 = word_add bb (word (32 * i))" k1 k1;
    ss "word_sub (word_add bb (word (%s + 32 * i))) (word %s):int64 = word_add bb (word (32 * i + 16))" k1 k0];;

let INLINE_MEMCMP_LOOP mc exec loop exit n ofs (rs:string list) =
  let tm = INLINE_MEMCMP_TERM mc loop exit n ofs rs in
  let inv = INLINE_MEMCMP_INV n ofs rs in
  let nt = mk_small_numeral n in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   (subst [nt,`NN:num`]
   `\(sk:int64) (bb:int64) (pc:num).
      APPEND (f_ev_epil sk bb pc)
       (APPEND (ENUMERATEL NN (\i. f_ev_loop sk bb pc i)) (f_ev_prol sk bb pc))
    :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sk:int64`; `bb:int64`;
                       `a:num->int128`; `b:num->int128`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nt (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES;
                mld_or_fold] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    INLINE_MEMCMP_FACTS_TAC ofs THEN
    ARM_STEPS_TAC exec (1--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `!i. 32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[MLD_OR_FOLD_ADD1] THEN BETA_TAC THEN
        W(fun (_,w) -> ACCEPT_TAC(WORD_BITWISE_RULE w)) THEN NO_TAC) THEN
    INLINE_EVENT_TAC
     [[Printf.sprintf "word_sub (word_add bb (word (%d + 32 * i))) (word %d):int64 = word_add bb (word (32 * i + 16))" (ofs + 16) ofs;
       Printf.sprintf "word_sub (word_add bb (word (%d + 32 * i))) (word %d):int64 = word_add bb (word (32 * i))" (ofs + 16) (ofs + 16);
       Printf.sprintf "word_sub (word_add sk (word (%d + 32 * i))) (word 16):int64 = word_add sk (word (%d + 32 * i))" (ofs + 16) ofs]] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The same comparison in mldsa87_pk_from_sk, with the registers allocated   *)
(* differently: the offset X8 counts from 0 in steps of 32, the buffer is at *)
(* XB and the secret key at XS, with the chunks of t0 at XS + OFS:           *)
(*   add X9, XB, X8; add X10, XS, X8; add X8, X8, #32; ldp q23, q24, [X9];   *)
(*   ldr q22, [X10, #OFS]; ldr q25, [X10, #OFS + 16]; cmp X8, #END;          *)
(*   eor v22, v22, v23; eor v23, v25, v24; 8 tbl; orr vA, v22, vA;           *)
(*   orr v18, v23, v18; 8 eor; b.ne                                          *)
(* The accumulators are vA (here v2) and v18.                                *)
(* ------------------------------------------------------------------------- *)

let INLINE_MEMCMPB_TERM mc loop exit n ofs (rs:string list) acc =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (sk:int64) (bb:int64) (a:num->int128) (b:num->int128) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word 0 /\\
                  read %s s = sk /\\ read %s s = bb /\\
                  read %s s = word 0 /\\ read Q18 s = word 0 /\\
                  (!k. k < %d
                       ==> read(memory :> bytes128(word_add sk (word(%d + 16 * k))))
                             s = a k) /\\
                  (!k. k < %d
                       ==> read(memory :> bytes128(word_add bb (word(16 * k))))
                             s = b k) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word %d /\\
                  read %s s = sk /\\ read %s s = bb /\\
                  read %s s = mld_or_fold (\\k. a (2 * k)) (\\k. b (2 * k)) %d /\\
                  read Q18 s = mld_or_fold (\\k. a (2 * k + 1))
                                           (\\k. b (2 * k + 1)) %d /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events sk bb pc /\\
                     memaccess_inbounds e2 [word_add sk (word %d),%d; bb,%d] []))
             (MAYCHANGE [PC; %s; %s; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                         Q16; Q18; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29;
                         Q30; Q31] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events])"
   mc loop (r 0) (r 1) (r 2) acc (2 * n) ofs (2 * n) exit (r 0) (32 * n)
   (r 1) (r 2) acc n n ofs (32 * n) (32 * n)
   (r 0) (r 3) (r 4));;

let INLINE_MEMCMPB_INV n ofs (rs:string list) acc =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "\\i s. read %s s = word(32 * i) /\\ read %s s = sk /\\ read %s s = bb /\\
          read %s s = mld_or_fold (\\k. a (2 * k)) (\\k. b (2 * k)) i /\\
          read Q18 s = mld_or_fold (\\k. a (2 * k + 1))
                                   (\\k. b (2 * k + 1)) i /\\
          (!k. k < %d
               ==> read(memory :> bytes128(word_add sk (word(%d + 16 * k)))) s =
                   a k) /\\
          (!k. k < %d
               ==> read(memory :> bytes128(word_add bb (word(16 * k)))) s =
                   b k)"
   (r 0) (r 1) (r 2) acc (2 * n) ofs (2 * n));;

(*** The four chunks of the pass i, at the addresses the simulator forms ***)
let INLINE_MEMCMPB_FACTS_TAC ofs =
  let ss = Printf.sprintf in
  INLINE_MEMCMP_SPEC_FACT_X
    [ARITH_RULE(parse_term(ss "%d + 32 * i = 32 * i + %d" ofs ofs))]
    `sk:int64` `2*i` ofs
    (parse_term(ss "read (memory :> bytes128 (word_add (sk:int64) (word (32 * i + %d)))) s0 = (a:num->int128) (2 * i)" ofs)) THEN
  INLINE_MEMCMP_SPEC_FACT_X
    [ARITH_RULE(parse_term(ss "%d + (32 * i + 16) = 32 * i + %d" ofs (ofs + 16)))]
    `sk:int64` `2*i+1` ofs
    (parse_term(ss "read (memory :> bytes128 (word_add (sk:int64) (word (32 * i + %d)))) s0 = (a:num->int128) (2 * i + 1)" (ofs + 16))) THEN
  INLINE_MEMCMP_SPEC_FACT `bb:int64` `2*i` ofs
    `read (memory :> bytes128 (word_add bb (word (32 * i)))) s0 = b (2 * i)` THEN
  INLINE_MEMCMP_SPEC_FACT `bb:int64` `2*i+1` ofs
    `read (memory :> bytes128 (word_add bb (word (32 * i + 16)))) s0 = b (2 * i + 1)`;;

let INLINE_MEMCMPB_LOOP mc exec loop exit n ofs (rs:string list) acc =
  let tm = INLINE_MEMCMPB_TERM mc loop exit n ofs rs acc in
  let inv = INLINE_MEMCMPB_INV n ofs rs acc in
  let nt = mk_small_numeral n in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   (subst [nt,`NN:num`]
   `\(sk:int64) (bb:int64) (pc:num).
      APPEND (f_ev_epil sk bb pc)
       (APPEND (ENUMERATEL NN (\i. f_ev_loop sk bb pc i)) (f_ev_prol sk bb pc))
    :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sk:int64`; `bb:int64`;
                       `a:num->int128`; `b:num->int128`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nt (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES;
                mld_or_fold] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    INLINE_MEMCMPB_FACTS_TAC ofs THEN
    ARM_STEPS_TAC exec (1--28) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `!i. 32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[MLD_OR_FOLD_ADD1] THEN BETA_TAC THEN
        W(fun (_,w) -> ACCEPT_TAC(WORD_BITWISE_RULE w)) THEN NO_TAC) THEN
    INLINE_EVENT_TAC
     [[Printf.sprintf "word_add (word_add sk (word (32 * i))) (word %d):int64 = word_add sk (word (32 * i + %d))" ofs ofs]] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
