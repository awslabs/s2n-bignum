(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The packing of the hints of row k (the loop of mld_pack_sig_h over the    *)
(* coefficients of polynomial k) as clang 23 -O3 inlines it into             *)
(* mldsa44_signature_internal: the region lemma HROW, from the head of the   *)
(* loop with RCX = 0 and RAX the number of hints of the rows before k, to    *)
(* the end of the store of the count of row k (sig + 2416 + k), or to the    *)
(* rejection at join26 if a hint does not fit into the 80 bytes.             *)
(*                                                                           *)
(* x is w0 - c s2 + c t0 (row k at rsp0 + 0x1500 + 1024 k), b the packed w1  *)
(* (row k unpacked at rsp0 + 0x320) and H = mld_polyvec_make_hint_88 x b the *)
(* hint bits of the positions p = 256 k + i. In iteration i the code tests   *)
(* x p + gamma2 <= 2 gamma2 as unsigned numbers (glue_hint_inr_88), and in   *)
(* range whether x p = -gamma2 and w1 <> 0 (GLUE_HINT_INR_88); a hint then   *)
(* fails if 80 are stored already (glue_hint_fail), else its coefficient i   *)
(* is stored at sig + 2336 + count. The loop is the one of                   *)
(* utils/mldsa_native_hints.ml for the gcc code, restricted to row k: it     *)
(* goes through glue_hint_steps 80 (256 (k + 1)) H - 256 k iterations, all   *)
(* 256 if there are at most 80 hints up to row k, and the last one being     *)
(* the hint that fails otherwise.                                            *)
(*                                                                           *)
(* Rows 0 and 2 have the test of the index before the head and the hint path *)
(* after it, rows 1 and 3 the hint path before the head (hr_late), which     *)
(* adds a jump on the path of a hint in range and saves one on the path of a *)
(* hint out of range.                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_attempt.ml";;

type hrow_cfg =
 { hr_fn : string; hr_k : int; hr_head : int; hr_store : int; hr_fin : int;
   hr_rej : int; hr_late : bool; hr_lo : int };;

let hrow_sub c s =
  subst_tokens
   ["@MC@",image_mc; "@FN@",c.hr_fn; "@K@",string_of_int c.hr_k;
    "@HEAD@",string_of_int (layout c.hr_fn + c.hr_head);
    "@STORE@",string_of_int (layout c.hr_fn + c.hr_store);
    "@FIN@",string_of_int (layout c.hr_fn + c.hr_fin);
    "@REJ@",string_of_int (layout c.hr_fn + c.hr_rej);
    "@W@",string_of_int (0x1500 + 1024 * c.hr_k);
    "@WB@",string_of_int (192 * c.hr_k); "@P0@",string_of_int (256 * c.hr_k);
    "@P1@",string_of_int (256 * (c.hr_k + 1)); "@CB@",string_of_int (2416 + c.hr_k)] s;;

(* The events: the iterations, each by its path (a hint that fails, in range *)
(* or not; for the other positions and for the last, a hint in range or not, *)
(* or none), and the store of the count unless a hint fails.                 *)

let HROW_TEMPLATE c = parse_term(hrow_sub c
 "\\(x:num->int32) (b:num->byte) (sig:int64) (rsp0:int64) (pc:num).
   APPEND
    (if mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
     then f_ev_st x b sig rsp0 pc else f_ev_rj x b sig rsp0 pc)
    (APPEND
      (ENUMERATEL (glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_88 x b) - @P0@)
        (\\i. if glue_hint_fail 80 (mld_polyvec_make_hint_88 x b) (@P0@ + i)
             then if glue_hint_inr_88 (x(@P0@ + i))
                  then f_ev_f2 x b sig rsp0 pc i else f_ev_f1 x b sig rsp0 pc i
             else if i < 255
             then if mld_polyvec_make_hint_88 x b (@P0@ + i)
                  then if glue_hint_inr_88 (x(@P0@ + i))
                       then f_ev_m2 x b sig rsp0 pc i else f_ev_m1 x b sig rsp0 pc i
                  else f_ev_m3 x b sig rsp0 pc i
             else if mld_polyvec_make_hint_88 x b (@P0@ + i)
                  then if glue_hint_inr_88 (x(@P0@ + i))
                       then f_ev_l2 x b sig rsp0 pc i else f_ev_l1 x b sig rsp0 pc i
                  else f_ev_l3 x b sig rsp0 pc i))
      (f_ev_pro x b sig rsp0 pc)) :(uarch_event)list");;

let HROW_STMT c = parse_term(hrow_sub c
 "exists f_events.
    forall e (x:num->int32) (b:num->byte) (sig:int64) (rsp0:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      mld_hint_count (mld_polyvec_make_hint_88 x b) @P0@ <= 80 /\\
      ALL (nonoverlapping (word_add sig (word 2336),84))
          [(word_add rsp0 (word @W@),1024); (word_add rsp0 (word 800),1024);
           (word_add rsp0 (word 8),8); (word_add rsp0 (word 24),8);
           (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @HEAD@) /\\
                read RSP s = rsp0 /\\ read RCX s = word 0 /\\
                read RAX s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) @P0@) /\\
                read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
                read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@W@ + 4 * i)))) s =
                                 x (@P0@ + i)) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s =
                                 mld_polyw1_unpack_88 (\\t. b (@WB@ + t)) i) /\\
                (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                mld_hint_index (mld_polyvec_make_hint_88 x b) @P0@ t) /\\
                read events s = e)
           (\\s. read RIP s =
                (if mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
                 then word (pc + @FIN@) else word (pc + @REJ@)) /\\
                read RSP s = rsp0 /\\
                (mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
                 ==> read RAX s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@) /\\
                     (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                     mld_hint_index (mld_polyvec_make_hint_88 x b) @P1@ t) /\\
                     read (memory :> bytes8 (word_add sig (word @CB@))) s =
                     word (mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events x b sig rsp0 pc /\\
                   memaccess_inbounds e2
                    [word_add rsp0 (word @W@),1024; word_add rsp0 (word 800),1024;
                     word_add rsp0 (word 8),8; word_add rsp0 (word 24),8;
                     word_add sig (word 2336),84]
                    [word_add sig (word 2336),84]))
           (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sig (word 2336),80);
                       memory :> bytes(word_add sig (word @CB@),1)])");;

(* The invariant at the head for iteration i: the frame, and, if the code    *)
(* goes through i or there are at most 80 hints, the index, the count and    *)
(* the hint bytes so far.                                                    *)

let HROW_INV c = parse_term(hrow_sub c
 "\\i s. read RSP s = rsp0 /\\
        read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
        read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@W@ + 4 * i)))) s =
                         x (@P0@ + i)) /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s =
                         mld_polyw1_unpack_88 (\\t. b (@WB@ + t)) i) /\\
        (i < glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_88 x b) - @P0@ \\/
         mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
         ==> read RCX s = word i /\\
             read RAX s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) (@P0@ + i)) /\\
             (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                             mld_hint_index (mld_polyvec_make_hint_88 x b) (@P0@ + i) t))");;

let HROW_EXEC c =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout c.hr_fn + c.hr_head - c.hr_lo, layout c.hr_fn + c.hr_fin)];;

(* ------------------------------------------------------------------------- *)
(* Arithmetic and the forms of the simulation.                               *)
(* ------------------------------------------------------------------------- *)

(*** The row has at least one iteration if the count before it fits ***)

let HROW_STEPS_POS = prove
 (`!h omega p0 p1. p0 < p1 /\ mld_hint_count h p0 <= omega
                   ==> p0 < glue_hint_steps omega p1 h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[glue_hint_steps] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `p1:num`] GLUE_HINT_FAIL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. glue_hint_fail omega (h:num->bool) p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal p. glue_hint_fail omega (h:num->bool) p` THEN
  REWRITE_TAC[glue_hint_fail] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `p0 < m + 1 <=> ~(m < p0)`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `m + 1`; `p0:num`] MLD_HINT_COUNT_MONO) THEN
  ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1] THEN ASM_ARITH_TAC);;

let HROW_DIVMOD = prove
 (`!k i. i < 256 ==> (256 * k + i) DIV 256 = k /\ (256 * k + i) MOD 256 = i`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num`] THEN ASM_ARITH_TAC);;

(*** The range test (ja): x - (2^32 - gamma2) compared with 2 gamma2 ***)

let HROW_SUB_G2_88 = prove
 (`!a:int32. word_sub a (word 4294872064) = word_add a (word 95232)`,
  GEN_TAC THEN SUBGOAL_THEN `word 4294872064:int32 = word_neg(word 95232)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

let HROW_JA = prove
 (`!v:int32.
     (~(~(&(val v) - &190464:int = &(val(word_sub v (word 190464)))) \/
        val(word_sub v (word 190464)) = 0)) <=> ~(val v <= 190464)`,
  GEN_TAC THEN MP_TAC(SPECL [`v:int32`; `190464`] GLUE_FLAGS_LS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC TAUT);;

(*** The test in range (or of SETNE and SETE, jne) ***)

let HROW_BYTE_JOIN = prove
 (`!(h:56 word) (b:byte). word(val(word_join h b:int64) MOD 256):byte = b`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word(val(word_join h b:int64) MOD 256):byte = word_zx(word_join h b:int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    CONV_TAC WORD_BLAST]);;

let HROW_JNE = prove
 (`!(h1:56 word) (h2:56 word) A B.
     val(word(val(word_join h1 (if A then word 1 else word 0:byte):int64) MOD 256) ||
         word(val(word_join h2 (if B then word 1 else word 0:byte):int64) MOD 256):byte) = 0
     <=> ~A /\ ~B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HROW_BYTE_JOIN] THEN
  MAP_EVERY BOOL_CASES_TAC [`A:bool`; `B:bool`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let HROW_ADDG2_EQ0 = prove
 (`!a:int32. val(word_add a (word 95232)) = 0 <=> a = word 4294872064`,
  GEN_TAC THEN REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN `word 4294872064:int32 = word_neg(word 95232)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

(*** The test of the count (je), its copy to EDX and its increment ***)

let HROW_CNT80 = prove
 (`!n. n <= 80
       ==> (val(word_sub (word_zx (word n:int64):int32) (word 80)) = 0 <=> n = 80)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; REFL_TAC]);;

let HROW_ZX_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let HROW_INC32 = prove
 (`!n. n < 80
       ==> word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64 =
           word (n + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n /\
                (n + 1) MOD 4294967296 = n + 1 /\
                (n + 1) MOD 18446744073709551616 = n + 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let HROW_VAL_BYTE = prove
 (`!n. word(val(word n:int64) MOD 256):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 256 * 72057594037927936`;
              MOD_MOD; MOD_MOD_REFL]);;

(*** The test of the index (je after inc rcx; cmp rcx, 256) ***)

let HROW_LAST = prove
 (`!i. i < 256
       ==> (val(word_add (word i:int64) (word 18446744073709551361)) = 0 <=>
            ~(i < 255))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i MOD 18446744073709551616 = i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 255` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(i + 18446744073709551361) MOD 18446744073709551616 =
                  i + 18446744073709551361`
    SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC];
    SUBGOAL_THEN `i = 255` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the paths of an iteration.                                    *)
(* ------------------------------------------------------------------------- *)

let hrow_num k n = mk_small_numeral(n k);;
let HROW_CNT_TM k = subst [mk_small_numeral(256 * k),`P0:num`]
  `mld_hint_count (mld_polyvec_make_hint_88 x b) (P0 + i)`;;
let HROW_FAIL_TM k = subst [mk_small_numeral(256 * k),`P0:num`]
  `glue_hint_fail 80 (mld_polyvec_make_hint_88 x b) (P0 + i)`;;
let HROW_H_TM k = subst [mk_small_numeral(256 * k),`P0:num`]
  `mld_polyvec_make_hint_88 x b (P0 + i)`;;
let HROW_INR_TM k = subst [mk_small_numeral(256 * k),`P0:num`]
  `glue_hint_inr_88 (x (P0 + i))`;;
let HROW_STEPS_TM k = subst [mk_small_numeral(256 * (k + 1)),`P1:num`]
  `glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b)`;;

(*** The fact for position i of a forall fact matching pat, rewritten ***)

let HROW_SPEC_TAC pat eqs =
  FIRST_ASSUM(fun th -> if can (term_match [] pat) (concl th) then
    MP_TAC(SPEC `i:num` th) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(ASSUME_TAC o REWRITE_RULE eqs)]
    else NO_TAC);;

(*** A conditional branch: its condition, in the RIP fact, as target ***)

let HROW_RIP_COND (asl,w) =
  let ths = filter (fun (_,th) -> let c = concl th in
     is_eq c && can (term_match [] `read RIP s`) (lhs c) && is_cond (rhs c)) asl in
  fst(dest_cond (rhs(concl(snd(hd ths)))));;

let HROW_DECIDE_TAC target prover =
  W(fun (asl,w) -> let c = HROW_RIP_COND (asl,w) in
     SUBGOAL_THEN (mk_iff(c,target)) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [prover; ALL_TAC]);;

(*** Cases on t, rewriting the other assumptions with the case ***)

let HROW_CASES_TAC t =
  ASM_CASES_TAC t THEN
  FIRST_ASSUM(fun th -> if concl th = t || concl th = mk_neg t
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC);;

(*** The hint bit of position 256 k + i from the coefficients, as a fact, ***)
(*** used for the tests and then dropped (it would rewrite the predicate ***)
(*** in the template)                                                    ***)

let HROW_UNFOLD_TAC k =
  let p0 = mk_small_numeral(256 * k) and wb = mk_small_numeral(192 * k) in
  let th = CONV_RULE NUM_REDUCE_CONV
    (MP (SPECL [mk_small_numeral k; `i:num`] HROW_DIVMOD) (ASSUME `i < 256`)) in
  let t = subst [p0,`P0:num`; wb,`WB:num`]
   `mld_polyvec_make_hint_88 x b (P0 + i) <=>
    mld_make_hint_88 (x (P0 + i)) (mld_polyw1_unpack_88 (\t. b (WB + t)) i)` in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GLUE_POLYVEC_HINT_88; th] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC];;

let is_hrow_unfold th =
  is_iff(concl th) && can (find_term ((=) `mld_make_hint_88`)) (concl th);;

let HROW_DROP_UNFOLD_TAC =
  FIRST_X_ASSUM(K ALL_TAC o check is_hrow_unfold);;

let HROW_HINT_INR_TAC =
  FIRST_ASSUM(fun th -> if is_hrow_unfold th then REWRITE_TAC[th] else NO_TAC) THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) GLUE_HINT_INR_88
      (find_term (fun t -> can (term_match [] `mld_make_hint_88 a b`) t) w))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN CONV_TAC TAUT;;

let HROW_HINT_OUT_TAC k =
  SUBGOAL_THEN (HROW_H_TM k) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_hrow_unfold th then REWRITE_TAC[th] else NO_TAC) THEN
    MATCH_MP_TAC GLUE_HINT_OUT_88 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(*** The next position (GLUE_HINT_NEXT): the number of iterations and the ***)
(*** count of the row, in the cases of a failure, of another position and ***)
(*** of the last                                                         ***)

let HROW_IDX_ARITH_TAC =
  MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < 255`; `~(i < 255)`; `i < 256`] THEN
  ARITH_TAC;;

let HROW_NOFAIL_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE (REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]);;

let HROW_NEXT_TAC p0 p1 =
  let p = mk_binop `(+):num->num->num` (mk_small_numeral p0) `i:num` in
  MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; mk_small_numeral p1; p]
               GLUE_HINT_NEXT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let fl = list_mk_comb(`glue_hint_fail 80 (mld_polyvec_make_hint_88 x b)`,[p]) in
    let has t = exists (fun (_,th) -> concl th = t) asl in
    if has fl then DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else
    (if has (mk_neg fl) then ALL_TAC
     else SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL [HROW_NOFAIL_TAC; ALL_TAC]) THEN
    if has `~(i < 255)` then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [HROW_NOFAIL_TAC; HROW_IDX_ARITH_TAC]; STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [HROW_NOFAIL_TAC; HROW_IDX_ARITH_TAC]; STRIP_TAC]);;

(*** The count below 80 on the path of a hint that fits: EDX and the store ***)
(*** address from it                                                      ***)

let HROW_CNT_FACTS_TAC (cnt:term) =
  let lt80 = mk_binop `(<):num->num->bool` cnt `80` in
  let lt80_tac = FIRST_ASSUM(MP_TAC o check (fun th -> concl th = lt80)) THEN ARITH_TAC in
  SUBGOAL_THEN lt80 ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
       can (term_match [] `glue_hint_fail 80 h p`) (rand(concl th)))) THEN
    REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` cnt `80`)) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`word_zx:int32->int64`,
                       mk_comb(`word_zx:int64->int32`,mk_comb(`word:num->int64`,cnt))),
                      mk_comb(`word:num->int64`,cnt))) ASSUME_TAC THENL
   [MATCH_MP_TAC HROW_ZX_SMALL THEN lt80_tac; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,cnt)),cnt))
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN lt80_tac;
    ALL_TAC];;

(*** The end of an iteration: the next invariant and the events ***)

let HROW_STEPS_LT_TAC p0 p1 =
  let tm = subst [mk_small_numeral p0,`P0:num`; mk_small_numeral p1,`P1:num`]
   `i + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b) - P0 <=>
    (P0 + i) + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b)` in
  SUBGOAL_THEN tm SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];;

let HROW_BYTES_TAC k =
  let th = CONV_RULE NUM_REDUCE_CONV
    (MP (SPECL [mk_small_numeral k; `i:num`] HROW_DIVMOD) (ASSUME `i < 256`)) in
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[MLD_HINT_INDEX_ADD1] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[CONJUNCT2 th] THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HROW_EVENTS_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let HROW_REGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; MULT_CLAUSES]) THEN
  TRY(FIRST_ASSUM(fun th ->
    if is_comb(concl th) && can (term_match [] `mld_hint_count h p < 80`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HROW_INC32 th]) else NO_TAC));;

let HROW_FINAL_TAC k =
  HROW_REGS_TAC THEN
  HROW_NEXT_TAC (256 * k) (256 * (k + 1)) THEN ENSURES_FINAL_STATE_TAC THEN
  HROW_STEPS_LT_TAC (256 * k) (256 * (k + 1)) THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; LT_REFL] THEN
  REWRITE_TAC[ADD_ASSOC; MLD_HINT_COUNT_ADD1] THEN ASM_REWRITE_TAC[ADD_0] THEN
  REPEAT CONJ_TAC THEN
  TRY(HROW_BYTES_TAC k THEN NO_TAC) THEN
  HROW_EVENTS_TAC;;

(*** The test of the index from step n, and the end of the iteration ***)

let HROW_LOOPTEST_TAC ex k n =
  X86_STEPS_TAC ex (n--(n+2)) THEN
  HROW_DECIDE_TAC `~(i < 255)` (MATCH_MP_TAC HROW_LAST THEN FIRST_ASSUM ACCEPT_TAC) THEN
  HROW_CASES_TAC `i < 255` THEN HROW_FINAL_TAC k;;

(*** The path of a hint from the test of the count at step n; jmp = 1 if ***)
(*** the code jumps back to the test of the index                        ***)

let HROW_HINT_PATH_TAC ex k jmp n =
  let cnt = HROW_CNT_TM k and fl = HROW_FAIL_TM k in
  let cntz = mk_eq(mk_comb(`word_zx:int32->int64`,
                    mk_comb(`word_zx:int64->int32`,mk_comb(`word:num->int64`,cnt))),
                   mk_comb(`word:num->int64`,cnt)) in
  let excl = vsubst [cnt,`c:num`; mk_small_numeral(256 * k),`P0:num`]
   `!t. t < 80 /\ ~(t = c)
        ==> read(memory :> bytes8(word_add sig (word(2336 + t)))) s =
            mld_hint_index (mld_polyvec_make_hint_88 x b) (P0 + i) t` in
  X86_STEPS_TAC ex (n--(n+1)) THEN
  HROW_DECIDE_TAC fl
   (REWRITE_TAC[glue_hint_fail; ASSUME (HROW_H_TM k)] THEN MATCH_MP_TAC HROW_CNT80 THEN
    FIRST_ASSUM ACCEPT_TAC) THEN
  HROW_CASES_TAC fl THENL
   [HROW_FINAL_TAC k;
    HROW_CNT_FACTS_TAC cnt THEN
    W(fun (asl,w) ->
      let s = mk_var("s"^string_of_int(n+1),`:x86state`) in
      SUBGOAL_THEN (vsubst [s,`s:x86state`] excl) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC]) THEN
    X86_STEPS_TAC ex [n+2] THEN RULE_ASSUM_TAC(REWRITE_RULE[ASSUME cntz]) THEN
    X86_STEPS_TAC ex ((n+3)--(n+5+jmp)) THEN
    HROW_LOOPTEST_TAC ex k (n+6+jmp)];;

(*** An iteration ***)

let HROW_BODY_TAC c ex =
  let k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and w = 0x1500 + 1024 * k in
  let steps = HROW_STEPS_TM k in
  let n = mk_binop `(-):num->num->num` steps p0 in
  let lt_n = mk_binop `(<):num->num->bool` `i:num` n in
  let p_lt = mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` p0 `i:num`) steps in
  let late = if c.hr_late then 1 else 0 in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN p_lt ASSUME_TAC THENL
   [UNDISCH_TAC lt_n THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL
   [UNDISCH_TAC p_lt THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` steps (mk_small_numeral(256 * (k + 1))))) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (HROW_CNT_TM k) `80`) ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] `!p. p < n ==> mld_hint_count h p <= 80`) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME lt_n] THEN
  GHOST_INTRO_TAC `rdx_init:int64` `read RDX` THEN
  GHOST_INTRO_TAC `rsi_init:int64` `read RSI` THEN
  FULL_INIT_TAC THEN
  HROW_SPEC_TAC (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s0 = y i" w))
    [ARITH_RULE(parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" w w))] THEN
  HROW_SPEC_TAC
    `!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s0 = y i`
    [ARITH_RULE `800 + 4 * i = 4 * i + 800`] THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC ex (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; HROW_SUB_G2_88]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HROW_JA; GLUE_INR_88]) THEN
  HROW_UNFOLD_TAC k THEN HROW_CASES_TAC (HROW_INR_TM k) THENL
   [X86_STEPS_TAC ex (8--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HROW_JNE; HROW_ADDG2_EQ0; VAL_EQ_0; WORD_SUB_0]) THEN
    HROW_DECIDE_TAC (mk_neg(HROW_H_TM k)) HROW_HINT_INR_TAC THEN
    HROW_DROP_UNFOLD_TAC THEN
    HROW_CASES_TAC (HROW_H_TM k) THENL
     [(if c.hr_late then X86_STEPS_TAC ex [10] else ALL_TAC) THEN
      HROW_HINT_PATH_TAC ex k (1 - late) (10 + late);
      HROW_LOOPTEST_TAC ex k 10];
    HROW_HINT_OUT_TAC k THEN HROW_DROP_UNFOLD_TAC THEN
    HROW_HINT_PATH_TAC ex k (1 - late) 8];;

(*** After the loop: the store of the count, or the rejection ***)

let HROW_EXIT_TAC c ex =
  let k = c.hr_k in
  let cntok = subst [mk_small_numeral(256 * (k + 1)),`P1:num`]
    `mld_hint_count (mld_polyvec_make_hint_88 x b) P1 <= 80` in
  REWRITE_TAC[] THEN HROW_CASES_TAC cntok THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC ex (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[HROW_VAL_BYTE] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let HROW_TAC c =
  let ex = HROW_EXEC c and k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and p1 = mk_small_numeral(256 * (k + 1)) in
  let pcn off = mk_binop `(+):num->num->num` `pc:num`
                  (mk_small_numeral(layout c.hr_fn + off)) in
  CONCRETIZE_F_EVENTS_TAC (HROW_TEMPLATE c) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `x:num->int32`; `b:num->byte`;
                       `sig:int64`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; p1] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_binop `(-):num->num->num` (HROW_STEPS_TM k) p0)
   (pcn c.hr_head)
   (mk_cond(subst [p1,`P1:num`] `mld_hint_count (mld_polyvec_make_hint_88 x b) P1 <= 80`,
            pcn c.hr_store, pcn c.hr_rej))
   (HROW_INV c) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; p0; p1] HROW_STEPS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    HROW_BODY_TAC c ex;
    HROW_EXIT_TAC c ex];;

let PROVE_HROW c = prove(HROW_STMT c, HROW_TAC c);;

let HROW44_CFGS =
  let f k head store fin late lo =
    {hr_fn = "mldsa44_signature_internal"; hr_k = k; hr_head = head;
     hr_store = store; hr_fin = fin; hr_rej = 0x2780; hr_late = late; hr_lo = lo} in
  [f 0 0x24cc 0x251a 0x2525 false 0xc;
   f 1 0x25b1 0x25dc 0x25e7 true 0x21;
   f 2 0x266c 0x26ac 0x26b7 false 0xc;
   f 3 0x2751 0x2842 0x284d true 0x21];;
