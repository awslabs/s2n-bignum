(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* BytesToBits, BitsToBytes, ByteDecode, ByteEncode and the vector wrappers. *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A driver for the generated loops: a fold over the schedule 0, 1, ..., n-1 *)
(* with a state invariant Q indexed by the number of completed iterations.   *)
(* ------------------------------------------------------------------------- *)

let BYTES_RESULT_CLAUSES = prove
 (`(!(x:A) y. Value x = Value y <=> x = y) /\
   (!(x:A) e. ~(Value x = Fault e)) /\
   (!(x:A). ~(Value x = Nontermination))`,
  REWRITE_TAC[injectivity "native_result"; distinctness "native_result"]);;

let BYTES_BIND_NONTERM = prove
 (`!(f:A->(B)native_result). native_bind Nontermination f = Nontermination`,
  REWRITE_TAC[native_bind_DEF; case_native_result_DEF]);;

let BYTES_BIND_CASES = prove
 (`!(a:(A)native_result) (f:A->(B)native_result) t.
     native_bind a f = Value t ==> ?x. a = Value x /\ f x = Value t`,
  MATCH_MP_TAC native_result_INDUCT THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; NATIVE_BIND_FAULT; BYTES_BIND_NONTERM] THEN
  REWRITE_TAC[BYTES_RESULT_CLAUSES] THEN MESON_TAC[]);;

let BYTES_FOLDL_APPEND = prove
 (`!(body:I->S->(S)native_result) l1 l2 s t.
     native_foldl body l1 s = Value t
     ==> native_foldl body (APPEND l1 l2) s = native_foldl body l2 t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; native_foldl_DEF; BYTES_RESULT_CLAUSES] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BYTES_BIND_CASES) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN ASM_MESON_TAC[]);;

let BYTES_FOLDL_UPTO = prove
 (`!(body:int->S->(S)native_result) (Q:num->S->bool) n s fuel.
     n < fuel /\ Q 0 s /\
     (!k t. k < n /\ Q k t ==> ?u. body (&k) t = Value u /\ Q (SUC k) u)
     ==> ?t. native_foldl body
              (native_schedule fuel (\i. int_lt i (&n)) (\i. int_add i (&1))
                                    (&0)) s = Value t /\
             Q n t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fuel:num`; `0`; `n:num`] NATIVE_SCHEDULE_UPTO) THEN
  ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!m. m <= n
        ==> ?t. native_foldl (body:int->S->(S)native_result)
                 (list_of_seq (\i. &i) m) s = Value t /\ Q m t`
   (fun th -> MP_TAC(SPEC `n:num` th) THEN REWRITE_TAC[LE_REFL]) THEN
  INDUCT_TAC THEN REWRITE_TAC[list_of_seq; native_foldl_DEF] THENL
   [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `s:S` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC th THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:S` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BYTES_FOLDL_APPEND th]) THEN
  REWRITE_TAC[native_foldl_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `t:S`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND_VALUE; native_foldl_DEF] THEN
  EXISTS_TAC `u:S` THEN ASM_REWRITE_TAC[]);;

(* An OCaml helper that applies BYTES_FOLDL_UPTO to the first loop of the   *)
(* goal, with a given invariant.                                            *)

let bytes_is_foldl tm =
  match strip_comb tm with
    f,[_;_;_] -> (try fst(dest_const f) = "native_foldl" with Failure _ -> false)
  | _ -> false;;

let BYTES_LOOP_TAC q =
  W(fun (_,w) ->
      let tm = find_term bytes_is_foldl w in
      let body = rand(rator(rator tm))
      and sched = rand(rator tm)
      and st = rand tm in
      let fuel = rand(rator(rator(rator sched)))
      and guard = rand(rator(rator sched)) in
      let n = rand(rand(snd(dest_abs guard))) in
      MP_TAC(ISPECL [body; q; n; st; fuel] BYTES_FOLDL_UPTO));;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of byte strings and binary digits.                            *)
(* ------------------------------------------------------------------------- *)

let BYTES_BITVAL_ODD = prove
 (`!x. bitval (ODD x) = x MOD 2`,
  GEN_TAC THEN REWRITE_TAC[bitval; ODD_MOD] THEN
  MP_TAC(SPECL [`x:num`; `2`] MOD_LT_EQ) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* BytesToBits_N: the bits of the number that the byte string denotes.      *)
(* ------------------------------------------------------------------------- *)

let BYTES_ISA_ARITH = prove
 (`(!a. isa_int_mod a (&2) = a rem &2) /\
   (!a. typed_hol_int_arithmetic ADiv a (&2) = Value (a div &2))`,
  SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH_ADIV; INT_ARITH `&0:int < &2`]);;

let BYTES_INIT_TAC =
  TRY(FIRST
   [ARITH_TAC;
    (ASM_REWRITE_TAC[LENGTH_REPLICATE; MULT_CLAUSES; CONJUNCT1 LT; EXP; DIV_1;
                     ADD_CLAUSES] THEN NO_TAC);
    (REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC THEN NO_TAC)]);;

let BYTES_BYTESTOBITS_GEN = prove
 (`!N (B:((8)word)list).
     LENGTH B = N
     ==>
     (let (v:(bool)list) = (REPLICATE (8 * N) F) in
      (native_bind
       (native_foldl
        (\(i:int).
         (native_foldl
          (\(j:int).
           (UNCURRY
            (\(b:(bool)list).
             (\(Ca:((8)word)list).
              (let (va:int) = (int_mul (&8:int) i) in
               (let (vb:int) = (int_add va j) in
                (native_bind
                 (typed_hol_read (native_list_index Ca i))
                 (\(vc:(8)word).
                  (native_bind
                   (typed_hol_byte_value vc)
                   (\(vd:int).
                    (let (ve:int) = (isa_int_mod vd (&2:int)) in
                     (native_bind
                      (typed_hol_int_to_bit ve)
                      (\(vf:bool).
                       (native_bind
                        (typed_hol_read (native_list_update b vb vf))
                        (\(vg:(bool)list).
                         (native_bind
                          (typed_hol_read (native_list_index Ca i))
                          (\(vh:(8)word).
                           (native_bind
                            (typed_hol_byte_value vh)
                            (\(vi:int).
                             (native_bind
                              (typed_hol_int_arithmetic ADiv vi (&2:int))
                              (\(vj:int).
                               (native_bind
                                (typed_hol_int_to_byte vj)
                                (\(vk:(8)word).
                                 (native_bind
                                  (typed_hol_read
                                   (native_list_update Ca i vk))
                                  (\(vl:((8)word)list).
                                   (Value (vg,vl)))))))))))))))))))))))))))
          (native_schedule
           9
           (\(j:int). (int_lt j (&8:int)))
           (\(j:int). (int_add j (&1:int)))
           (&0:int))))
        (native_schedule
         (N + 1)
         (\(i:int). (int_lt i (&N:int)))
         (\(i:int). (int_add i (&1:int)))
         (&0:int))
        (v,B))
       (UNCURRY (\(b:(bool)list). (\(Ca:((8)word)list). (Value b)))))) =
       Value (list_of_seq (\i. ODD (num_of_bytelist B DIV 2 EXP i)) (8 * N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BYTES_LOOP_TAC
   `\k (s:(bool)list#((8)word)list).
      LENGTH (FST s) = 8 * N /\ LENGTH (SND s) = N /\
      (!m. m < 8 * k ==> EL m (FST s) = ODD (num_of_bytelist B DIV 2 EXP m)) /\
      (!m. k <= m /\ m < N ==> EL m (SND s) = EL m B)` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN BYTES_INIT_TAC; ALL_TAC] THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:bool list`; `Ca:byte list`] THEN
    REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    BYTES_LOOP_TAC
     `\j (s:(bool)list#((8)word)list).
        LENGTH (FST s) = 8 * N /\ LENGTH (SND s) = N /\
        val (EL k Ca) DIV 2 EXP j = val (EL k (SND s)) /\
        (!m. m < 8 * N
             ==> (EL m (FST s) <=>
                  if 8 * k <= m /\ m < 8 * k + j
                  then ODD (val (EL k Ca) DIV 2 EXP (m - 8 * k))
                  else EL m b)) /\
        (!m. m < N /\ ~(m = k) ==> EL m (SND s) = EL m Ca)` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN BYTES_INIT_TAC; ALL_TAC] THENL
     [X_GEN_TAC `j:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`bb:bool list`; `CC:byte list`] THEN
      REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
      REWRITE_TAC[UNCURRY_DEF; LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
      SUBGOAL_THEN `k < LENGTH (CC:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 * k + j < LENGTH (bb:bool list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `EL k (CC:byte list)` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
      SUBGOAL_THEN `val (EL k (CC:byte list)) DIV 2 < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE;
                   typed_hol_byte_value_DEF; BYTES_ISA_ARITH; INT_OF_NUM_REM;
                   INT_OF_NUM_DIV; GSYM BYTES_BITVAL_ODD;
                   TYPED_HOL_INT_TO_BIT; NATIVE_LIST_UPDATE;
                   TYPED_HOL_INT_TO_BYTE] THEN
      EXISTS_TAC
       `(isa_list_update bb (8 * k + j) (ODD (val (EL k (CC:byte list)))),
         isa_list_update CC k (word (val (EL k (CC:byte list)) DIV 2):byte))` THEN
      REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE];
        ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE];
        SUBGOAL_THEN `2 EXP SUC j = 2 EXP j * 2` SUBST1_TAC THENL
         [REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM DIV_DIV] THEN ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN
        REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[MOD_LT];
        X_GEN_TAC `m:num` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[ARITH_RULE `8 * k <= 8 * k + j`;
                          ARITH_RULE `8 * k + j < 8 * k + SUC j`;
                          ARITH_RULE `(8 * k + j) - 8 * k = j`];
          SUBGOAL_THEN
           `(8 * k <= m /\ m < 8 * k + SUC j) <=>
            (8 * k <= m /\ m < 8 * k + j)`
           SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[]];
        X_GEN_TAC `m:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]];
      REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN
      DISCH_THEN(X_CHOOSE_THEN `bb:bool list`
                  (X_CHOOSE_THEN `CC:byte list` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`bb:bool list`; `CC:byte list`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `m < 8 * N` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL
         [MP_TAC(SPECL [`B:byte list`; `k:num`; `m - 8 * k`]
                       BYTES_BYTELIST_BIT) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `8 * k + (m - 8 * k) = m` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `EL k (Ca:byte list) = EL k (B:byte list)`
           SUBST1_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]);
          ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        X_GEN_TAC `m:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `EL m (CC:byte list) = EL m Ca` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN
    DISCH_THEN(X_CHOOSE_THEN `bb:bool list`
                (X_CHOOSE_THEN `CC:byte list` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]]);;

(* The seven instances: they differ only in the numerals.                   *)

let BYTES_BYTESTOBITS_TAC n def =
  REWRITE_TAC[def] THEN GEN_TAC THEN
  MP_TAC(SPEC n BYTES_BYTESTOBITS_GEN) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_ACCEPT_TAC;;

let BYTESTOBITS_32 = prove
 (BYTESTOBITS_32_STMT, BYTES_BYTESTOBITS_TAC `32` BytesToBits_32_hol_DEF);;

let BYTESTOBITS_128 = prove
 (BYTESTOBITS_128_STMT, BYTES_BYTESTOBITS_TAC `128` BytesToBits_128_hol_DEF);;

let BYTESTOBITS_160 = prove
 (BYTESTOBITS_160_STMT, BYTES_BYTESTOBITS_TAC `160` BytesToBits_160_hol_DEF);;

let BYTESTOBITS_192 = prove
 (BYTESTOBITS_192_STMT, BYTES_BYTESTOBITS_TAC `192` BytesToBits_192_hol_DEF);;

let BYTESTOBITS_320 = prove
 (BYTESTOBITS_320_STMT, BYTES_BYTESTOBITS_TAC `320` BytesToBits_320_hol_DEF);;

let BYTESTOBITS_352 = prove
 (BYTESTOBITS_352_STMT, BYTES_BYTESTOBITS_TAC `352` BytesToBits_352_hol_DEF);;

let BYTESTOBITS_384 = prove
 (BYTESTOBITS_384_STMT, BYTES_BYTESTOBITS_TAC `384` BytesToBits_384_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* BitsToBytes_N: the bytes of the number that the bit string denotes.      *)
(* ------------------------------------------------------------------------- *)

let BYTES_EL_REPLICATE = prove
 (`!n (y:A) i. i < n ==> EL i (REPLICATE n y) = y`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[REPLICATE; EL; HD; TL; LT_SUC]);;

let BYTES_INT_TO_BYTE_0 = prove
 (`typed_hol_int_to_byte (&0) = Value (word 0:byte)`,
  SIMP_TAC[TYPED_HOL_INT_TO_BYTE; ARITH]);;

let BYTES_ADIV_8 = prove
 (`!a. typed_hol_int_arithmetic ADiv a (&8) = Value (a div &8) /\
       isa_int_mod a (&8) = a rem &8`,
  SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH_ADIV; INT_ARITH `&0:int < &8`]);;

let BYTES_MOD_STEP = prove
 (`!y r. y MOD 2 EXP (r + 1) =
         y MOD 2 EXP r + ((y DIV 2 EXP r) MOD 2) * 2 EXP r`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `2 EXP (r + 1) = 2 EXP r * 2` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let BYTES_BITSTOBYTES_GEN = prove
 (`!N x (b:(bool)list).
     LENGTH b = 8 * N /\
     (!m. m < 8 * N ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==>
     (native_bind
      (typed_hol_int_to_byte (&0:int))
      (\(v:(8)word).
       (let (va:((8)word)list) = (REPLICATE N v) in
        (native_foldl
         (\(i:int).
          (\(B:((8)word)list).
           (native_bind
            (typed_hol_int_arithmetic ADiv i (&8:int))
            (\(vb:int).
             (native_bind
              (typed_hol_int_arithmetic ADiv i (&8:int))
              (\(vc:int).
               (native_bind
                (typed_hol_read (native_list_index B vc))
                (\(vd:(8)word).
                 (native_bind
                  (typed_hol_byte_value vd)
                  (\(ve:int).
                   (native_bind
                    (typed_hol_read (native_list_index b i))
                    (\(vf:bool).
                     (native_bind
                      (typed_hol_bit_value vf)
                      (\(vg:int).
                       (let (vh:int) = (isa_int_mod i (&8:int)) in
                        (native_bind
                         (typed_hol_int_arithmetic APow (&2:int) vh)
                         (\(vi:int).
                          (let (vj:int) = (int_mul vg vi) in
                           (let (vk:int) = (int_add ve vj) in
                            (native_bind
                             (typed_hol_int_to_byte vk)
                             (\(vl:(8)word).
                              (typed_hol_read
                               (native_list_update
                                B
                                vb
                                vl)))))))))))))))))))))))
         (native_schedule
          (8 * N + 1)
          (\(i:int). (int_lt i (&(8 * N):int)))
          (\(i:int). (int_add i (&1:int)))
          (&0:int))
         va)))) =
       Value (bytelist_of_num N x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bits")) THEN
  REWRITE_TAC[BYTES_INT_TO_BYTE_0; NATIVE_BIND_VALUE; LET_DEF; LET_END_DEF] THEN
  BYTES_LOOP_TAC
   `\k (B:((8)word)list).
      LENGTH B = N /\
      (!m. m < N
           ==> val (EL m B) =
               (x DIV 2 EXP (8 * m)) MOD 2 EXP (MIN 8 (k - 8 * m)))` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[BYTES_EL_REPLICATE] THEN
      REWRITE_TAC[VAL_WORD_0; ARITH_RULE `MIN 8 (0 - 8 * m) = 0`; EXP; MOD_1];
      ALL_TAC];
    ALL_TAC] THENL
   [X_GEN_TAC `k:num` THEN X_GEN_TAC `B:byte list` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inv"))) THEN
    MP_TAC(SPECL [`k:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    SUBGOAL_THEN `k DIV 8 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (EL (k DIV 8) (B:byte list)) < 2 EXP (k MOD 8)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `MIN 8 (k - 8 * (k DIV 8)) = k MOD 8` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP (k MOD 8) * 2 <= 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `2 EXP (k MOD 8) * 2 = 2 EXP (k MOD 8 + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
      SUBGOAL_THEN `256 = 2 EXP 8` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`x DIV 2 EXP k`; `2`] MOD_LT_EQ) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `val (EL (k DIV 8) (B:byte list)) +
      ((x DIV 2 EXP k) MOD 2) * 2 EXP (k MOD 8) < 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `(x DIV 2 EXP k) MOD 2 = 0 \/ (x DIV 2 EXP k) MOD 2 = 1`
       STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `k DIV 8 < LENGTH (B:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k < LENGTH (b:(bool)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `EL k (b:(bool)list) <=> ODD (x DIV 2 EXP k)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[BYTES_ADIV_8; INT_OF_NUM_DIV; INT_OF_NUM_REM;
             NATIVE_BIND_VALUE; NATIVE_LIST_INDEX;
             typed_hol_byte_value_DEF; TYPED_HOL_BIT_VALUE;
             INT_ARITH_APOW; INT_OF_NUM_POW; INT_OF_NUM_MUL;
             INT_OF_NUM_ADD; TYPED_HOL_INT_TO_BYTE; NATIVE_LIST_UPDATE;
             BYTES_BITVAL_ODD;
             ASSUME `k DIV 8 < LENGTH (B:byte list)`;
             ASSUME `k < LENGTH (b:(bool)list)`;
             ASSUME `EL k (b:(bool)list) <=> ODD (x DIV 2 EXP k)`;
             ASSUME `val (EL (k DIV 8) (B:byte list)) +
                     ((x DIV 2 EXP k) MOD 2) * 2 EXP (k MOD 8) < 256`] THEN
    EXISTS_TAC
     `isa_list_update (B:byte list) (k DIV 8)
       (word (val (EL (k DIV 8) B) +
              (x DIV 2 EXP k) MOD 2 * 2 EXP (k MOD 8)):byte)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `m < LENGTH (B:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[EL_ISA_LIST_UPDATE; ASSUME `m < LENGTH (B:byte list)`] THEN
      ASM_CASES_TAC `m = k DIV 8` THEN ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[MOD_LT;
                 ASSUME `val (EL (k DIV 8) (B:byte list)) +
                         ((x DIV 2 EXP k) MOD 2) * 2 EXP (k MOD 8) < 256`] THEN
        ASM_SIMP_TAC[] THEN
        SUBGOAL_THEN `MIN 8 (k - 8 * (k DIV 8)) = k MOD 8` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `MIN 8 (SUC k - 8 * (k DIV 8)) = k MOD 8 + 1`
        SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[BYTES_MOD_STEP] THEN
        SUBGOAL_THEN
         `(x DIV 2 EXP (8 * (k DIV 8))) DIV 2 EXP (k MOD 8) = x DIV 2 EXP k`
        SUBST1_TAC THENL
         [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
          SUBGOAL_THEN `8 * (k DIV 8) + k MOD 8 = k` SUBST1_TAC THENL
           [ASM_ARITH_TAC; REFL_TAC];
          ALL_TAC] THEN
        ARITH_TAC;
        SUBGOAL_THEN `MIN 8 (SUC k - 8 * m) = MIN 8 (k - 8 * m)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `t:byte list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC BYTES_BYTELIST_OF_NUM_EL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `MIN 8 (8 * N - 8 * m) = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* The six instances needed by ByteEncode_d, d = 1, 4, 5, 10, 11, 12.       *)

let BYTES_BITSTOBYTES_TAC n def =
  REWRITE_TAC[def] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC n BYTES_BITSTOBYTES_GEN) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_ACCEPT_TAC;;

let BYTES_BITSTOBYTES_32 = prove
 (`!x (b:(bool)list).
     LENGTH b = 256 /\ (!m. m < 256 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_32_hol b = Value (bytelist_of_num 32 x)`,
  BYTES_BITSTOBYTES_TAC `32` BitsToBytes_32_hol_DEF);;

let BYTES_BITSTOBYTES_128 = prove
 (`!x (b:(bool)list).
     LENGTH b = 1024 /\ (!m. m < 1024 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_128_hol b = Value (bytelist_of_num 128 x)`,
  BYTES_BITSTOBYTES_TAC `128` BitsToBytes_128_hol_DEF);;

let BYTES_BITSTOBYTES_160 = prove
 (`!x (b:(bool)list).
     LENGTH b = 1280 /\ (!m. m < 1280 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_160_hol b = Value (bytelist_of_num 160 x)`,
  BYTES_BITSTOBYTES_TAC `160` BitsToBytes_160_hol_DEF);;

let BYTES_BITSTOBYTES_320 = prove
 (`!x (b:(bool)list).
     LENGTH b = 2560 /\ (!m. m < 2560 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_320_hol b = Value (bytelist_of_num 320 x)`,
  BYTES_BITSTOBYTES_TAC `320` BitsToBytes_320_hol_DEF);;

let BYTES_BITSTOBYTES_352 = prove
 (`!x (b:(bool)list).
     LENGTH b = 2816 /\ (!m. m < 2816 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_352_hol b = Value (bytelist_of_num 352 x)`,
  BYTES_BITSTOBYTES_TAC `352` BitsToBytes_352_hol_DEF);;

let BYTES_BITSTOBYTES_384 = prove
 (`!x (b:(bool)list).
     LENGTH b = 3072 /\ (!m. m < 3072 ==> (EL m b <=> ODD (x DIV 2 EXP m)))
     ==> BitsToBytes_384_hol b = Value (bytelist_of_num 384 x)`,
  BYTES_BITSTOBYTES_TAC `384` BitsToBytes_384_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* ByteDecode_d: the d-bit fields of the number that the bytes denote.      *)
(* ------------------------------------------------------------------------- *)

let BYTES_INDEX_BOUND = prove
 (`!i j d n. i < n /\ j < d ==> i * d + j < n * d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i * d + d <= n * d` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i * d + d = (i + 1) * d`] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `i < n ==> i + 1 <= n`];
    ASM_ARITH_TAC]);;

let BYTES_LIST_OF_SEQ_EQ = prove
 (`!(f:num->A) g n.
     (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let BYTES_SCHEDULE_256 = prove
 (`native_schedule 257 (\i. int_lt i (&256)) (\i. int_add i (&1)) (&0) =
   list_of_seq (\i. &i) 256`,
  MP_TAC(SPECL [`257`; `0`; `256`] NATIVE_SCHEDULE_UPTO) THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let BYTES_BYTEDECODE_GEN = prove
 (`!d m (h:int->A) s (bits:(bool)list) v.
     0 < m /\ LENGTH s = 256 /\ LENGTH bits = 256 * d /\
     (!i. i < 256 * d ==> (EL i bits <=> ODD (v DIV 2 EXP i)))
     ==> native_foldl
          (\(i:int).
           (\(Fa:(A)list).
            (native_bind
             (native_foldl
              (\(j:int).
               (\(acc:int).
                (native_bind
                 (typed_hol_read
                   (native_list_index bits (int_add (int_mul i (&d:int)) j)))
                 (\(ve:bool).
                  (native_bind
                   (typed_hol_bit_value ve)
                   (\(vf:int).
                    (native_bind
                     (typed_hol_int_arithmetic APow (&2:int) j)
                     (\(vg:int).
                      (Value (int_add acc (int_mul vf vg)))))))))))
              (native_schedule
                (SUC d)
                (\(j:int). (int_lt j (&d:int)))
                (\(j:int). (int_add j (&1:int)))
                (&0:int))
              (&0:int))
             (\(vc:int).
              (typed_hol_read
                (native_list_update Fa i (h (isa_int_mod vc (&m:int)))))))))
          (native_schedule
            257
            (\(i:int). (int_lt i (&256:int)))
            (\(i:int). (int_add i (&1:int)))
            (&0:int))
          s =
         Value (list_of_seq
                 (\i. h (&((v DIV 2 EXP (i * d)) MOD 2 EXP d) rem &m)) 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bits")))) THEN
  REWRITE_TAC[BYTES_SCHEDULE_256] THEN
  MATCH_MP_TAC NATIVE_FOLDL_FILL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`iv:num`; `t:A list`] THEN STRIP_TAC THEN
  BYTES_LOOP_TAC `\j (acc:int). acc = &((v DIV 2 EXP (iv * d)) MOD 2 EXP j)` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[EXP; MOD_1];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`jv:num`; `acc:int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `iv * d + jv < LENGTH (bits:(bool)list)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[BYTES_INDEX_BOUND]; ALL_TAC] THEN
    SUBGOAL_THEN `EL (iv * d + jv) (bits:(bool)list) <=>
                  ODD (v DIV 2 EXP (iv * d + jv))` ASSUME_TAC THENL
     [USE_THEN "bits" (fun th -> MP_TAC(SPEC `iv * d + jv` th)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[BYTES_INDEX_BOUND]; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; NATIVE_LIST_INDEX;
                 NATIVE_BIND_VALUE; TYPED_HOL_BIT_VALUE; INT_ARITH_APOW;
                 INT_OF_NUM_POW; BYTES_BITVAL_ODD] THEN
    SUBGOAL_THEN `v DIV 2 EXP (iv * d + jv) =
                  (v DIV 2 EXP (iv * d)) DIV 2 EXP jv` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ADD1; BYTES_MOD_STEP] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `acc:int` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[NATIVE_BIND_VALUE; ISA_INT_MOD_POS; INT_OF_NUM_LT;
               NATIVE_LIST_UPDATE] THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE]);;

let BYTES_BYTEDECODE_TAC pre tms b2b def =
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC(def :: LET_DEF :: LET_END_DEF :: pre) THEN
  ASM_SIMP_TAC[b2b; NATIVE_BIND_VALUE] THEN
  MP_TAC(ISPECL tms BYTES_BYTEDECODE_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_REPLICATE; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  REWRITE_TAC[INT_MUL_RID] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[ISA_NAT_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC BYTES_LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT AP_TERM_TAC THEN
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[INT_OF_NUM_REM; MOD_MOD_REFL];;


let BYTEDECODE_1 = prove
 (BYTEDECODE_1_STMT,
  BYTES_BYTEDECODE_TAC []
   [`1`; `2`; `\z:int. residue_of_int_mod z :(2)residue`;
    `REPLICATE 256 (residue_of_int_mod (&0):(2)residue)`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 256`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_32 ByteDecode_d_1_2_hol_DEF);;

let BYTEDECODE_4 = prove
 (BYTEDECODE_4_STMT,
  BYTES_BYTEDECODE_TAC []
   [`4`; `16`; `\z:int. residue_of_int_mod z :(16)residue`;
    `REPLICATE 256 (residue_of_int_mod (&0):(16)residue)`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 1024`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_128 ByteDecode_d_4_16_hol_DEF);;

let BYTEDECODE_5 = prove
 (BYTEDECODE_5_STMT,
  BYTES_BYTEDECODE_TAC []
   [`5`; `32`; `\z:int. residue_of_int_mod z :(32)residue`;
    `REPLICATE 256 (residue_of_int_mod (&0):(32)residue)`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 1280`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_160 ByteDecode_d_5_32_hol_DEF);;

let BYTEDECODE_10 = prove
 (BYTEDECODE_10_STMT,
  BYTES_BYTEDECODE_TAC []
   [`10`; `1024`; `\z:int. residue_of_int_mod z :(1024)residue`;
    `REPLICATE 256 (residue_of_int_mod (&0):(1024)residue)`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 2560`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_320 ByteDecode_d_10_1024_hol_DEF);;

let BYTEDECODE_11 = prove
 (BYTEDECODE_11_STMT,
  BYTES_BYTEDECODE_TAC []
   [`11`; `2048`; `\z:int. residue_of_int_mod z :(2048)residue`;
    `REPLICATE 256 (residue_of_int_mod (&0):(2048)residue)`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 2816`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_352 ByteDecode_d_11_2048_hol_DEF);;

let BYTEDECODE_12 = prove
 (BYTEDECODE_12_STMT,
  BYTES_BYTEDECODE_TAC [zqlist]
   [`12`; `3329`; `\z:int. FIPS203_Zq (residue_of_int_mod z)`;
    `MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0):(3329)residue))`;
    `list_of_seq (\i. ODD (num_of_bytelist (b:byte list) DIV 2 EXP i)) 3072`;
    `num_of_bytelist (b:byte list)`]
   BYTESTOBITS_384 ByteDecode_d_12_3329_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* ByteEncode_d: the d-bit fields of the values, as a bit string.           *)
(* ------------------------------------------------------------------------- *)

let BYTES_BIT_DIGIT_GEN = prove
 (`!x y r e. r < e /\ x MOD 2 EXP e = y MOD 2 EXP e
             ==> (ODD (x DIV 2 EXP r) <=> ODD (y DIV 2 EXP r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (r + 1) * 2 EXP (e - (r + 1)) = 2 EXP e` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x MOD 2 EXP (r + 1) = y MOD 2 EXP (r + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`x:num`; `2 EXP (r + 1)`; `2 EXP (e - (r + 1))`] MOD_MOD) THEN
    MP_TAC(SPECL [`y:num`; `2 EXP (r + 1)`; `2 EXP (e - (r + 1))`] MOD_MOD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD; DIV_MOD] THEN
  SUBGOAL_THEN `2 EXP r * 2 = 2 EXP (r + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let BYTES_AQUOT_2 = prove
 (`!x. typed_hol_int_arithmetic AQuot (&x - &(x MOD 2)) (&2) =
       Value (&(x DIV 2))`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&x - &(x MOD 2):int = &(2 * (x DIV 2))` SUBST1_TAC THENL
   [SUBGOAL_THEN `2 * (x DIV 2) = x - x MOD 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[INT_ARITH_AQUOT; INT_ARITH `&0:int < &2`; INT_OF_NUM_REM;
           INT_OF_NUM_DIV; INT_OF_NUM_EQ; MOD_MULT; DIV_MULT; ARITH_EQ]);;

let BYTES_NSUM_DIGIT = prove
 (`!d n (g:num->num) k.
     (!i. i < n ==> g i < 2 EXP d) /\ k < n
     ==> (nsum {i | i < n} (\i. g i * 2 EXP (i * d)) DIV 2 EXP (k * d))
         MOD 2 EXP d = g k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nsum {i | i < n} (\i. g i * 2 EXP (i * d)) =
                nsum {i | i < n} (\i. (2 EXP d) EXP i * g i)` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; EXP_EXP] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (k * d) = (2 EXP d) EXP k` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2 EXP d`; `g:num->num`; `{i | i < n}`; `k:num`]
                DIGITSUM_DIV_MOD) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]);;

let BYTES_BIT_VALUE_ODD = prove
 (`!y. typed_hol_bit_value (ODD y) = Value (&(y MOD 2))`,
  REWRITE_TAC[TYPED_HOL_BIT_VALUE; BYTES_BITVAL_ODD]);;

let BYTES_INT_TO_BIT_MOD = prove
 (`!y. typed_hol_int_to_bit (&(y MOD 2)) = Value (ODD y)`,
  REWRITE_TAC[GSYM BYTES_BITVAL_ODD; TYPED_HOL_INT_TO_BIT]);;

let BYTES_BYTEENCODE_GEN = prove
 (`
 !d (w:A->num) (Fa:(A)list).
   0 < d /\ LENGTH Fa = 256
   ==> native_foldl
        (\(i:int) (b:(bool)list).
          native_bind (typed_hol_read (native_list_index Fa i))
           (\(va:A).
             native_bind
              (native_foldl
                (\(j:int). UNCURRY
                  (\(ba:(bool)list) (a:int).
                    native_bind (typed_hol_int_to_bit (isa_int_mod a (&2)))
                     (\(vf:bool).
                       native_bind
                        (typed_hol_read
                          (native_list_update ba
                            (int_add (int_mul i (&d)) j) vf))
                        (\(vg:(bool)list).
                          native_bind
                           (typed_hol_read
                             (native_list_index vg
                               (int_add (int_mul i (&d)) j)))
                           (\(vj:bool).
                             native_bind (typed_hol_bit_value vj)
                              (\(vk:int).
                                native_bind
                                 (typed_hol_int_arithmetic AQuot
                                   (int_sub a vk) (&2))
                                 (\(vm:int). Value (vg,vm))))))))
                (native_schedule (SUC d) (\(j:int). int_lt j (&d))
                                 (\(j:int). int_add j (&1)) (&0))
                (b,int_of_num (w va)))
              (UNCURRY (\(ba:(bool)list) (a:int). Value ba))))
        (native_schedule 257 (\(i:int). int_lt i (&256))
                         (\(i:int). int_add i (&1)) (&0))
        (REPLICATE (256 * d) F) =
       Value (list_of_seq
               (\n. ODD (nsum {i | i < 256}
                            (\i. (w (EL i Fa) MOD 2 EXP d) * 2 EXP (i * d))
                         DIV 2 EXP n))
               (256 * d))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (nsum {i | i < 256}
               (\i. (w (EL i (Fa:(A)list)) MOD 2 EXP d) * 2 EXP (i * d))
             DIV 2 EXP (i * d)) MOD 2 EXP d = w (EL i Fa) MOD 2 EXP d`
   (LABEL_TAC "dig") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BYTES_NSUM_DIGIT THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  BYTES_LOOP_TAC
   `\k (bits:(bool)list).
      LENGTH bits = 256 * d /\
      (!n. n < k * d
           ==> (EL n bits <=>
                ODD (nsum {i | i < 256}
                       (\i. (w (EL i (Fa:(A)list)) MOD 2 EXP d) *
                            2 EXP (i * d))
                     DIV 2 EXP n)))` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN X_GEN_TAC `bits:(bool)list` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oinv"))) THEN
    SUBGOAL_THEN `k < LENGTH (Fa:(A)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `SUC k * d <= 256 * d` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `k < 256 ==> SUC k <= 256`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE] THEN
    BYTES_LOOP_TAC
     `\j (s:(bool)list#int).
        LENGTH (FST s) = 256 * d /\
        SND s = &(w (EL k (Fa:(A)list)) DIV 2 EXP j) /\
        (!n. n < 256 * d
             ==> (EL n (FST s) <=>
                  if k * d <= n /\ n < k * d + j
                  then ODD (w (EL k Fa) DIV 2 EXP (n - k * d))
                  else EL n bits))` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        ASM_REWRITE_TAC[];
        REWRITE_TAC[EXP; DIV_1];
        REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`bb:(bool)list`; `a:int`] THEN
      REWRITE_TAC[FST; SND] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 SUBST1_TAC (LABEL_TAC "iinv")))) THEN
      REWRITE_TAC[UNCURRY_DEF] THEN
      SUBGOAL_THEN `k * d + j < LENGTH (bb:(bool)list)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[BYTES_INDEX_BOUND]; ALL_TAC] THEN
      SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; ISA_INT_MOD_POS;
               INT_ARITH `&0:int < &2`; INT_OF_NUM_REM;
               BYTES_INT_TO_BIT_MOD; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
               LENGTH_ISA_LIST_UPDATE; NATIVE_LIST_INDEX; EL_ISA_LIST_UPDATE;
               BYTES_BIT_VALUE_ODD; BYTES_AQUOT_2;
               ASSUME `k * d + j < LENGTH (bb:(bool)list)`] THEN
      EXISTS_TAC
       `(isa_list_update bb (k * d + j)
          (ODD (w (EL k (Fa:(A)list)) DIV 2 EXP j)),
         &(w (EL k Fa) DIV 2 EXP j DIV 2):int)` THEN
      REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE];
        SUBGOAL_THEN `2 EXP SUC j = 2 EXP j * 2` SUBST1_TAC THENL
         [REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM DIV_DIV];
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `n < LENGTH (bb:(bool)list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[EL_ISA_LIST_UPDATE;
                 ASSUME `n < LENGTH (bb:(bool)list)`] THEN
        COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[ARITH_RULE `k * d <= k * d + j`;
                          ARITH_RULE `k * d + j < k * d + SUC j`;
                          ARITH_RULE `(k * d + j) - k * d = j`];
          SUBGOAL_THEN
           `(k * d <= n /\ n < k * d + SUC j) <=>
            (k * d <= n /\ n < k * d + j)`
           SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          USE_THEN "iinv" (fun th -> ASM_SIMP_TAC[th])]];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN
    DISCH_THEN(X_CHOOSE_THEN `bb:(bool)list`
                (X_CHOOSE_THEN `a:int` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF] THEN
    EXISTS_TAC `bb:(bool)list` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `n < 256 * d` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL
     [MP_TAC(SPECL
       [`nsum {i | i < 256}
           (\i. (w (EL i (Fa:(A)list)) MOD 2 EXP d) * 2 EXP (i * d))
         DIV 2 EXP (k * d)`;
        `(w:A->num) (EL k (Fa:(A)list))`; `n - k * d`; `d:num`]
       BYTES_BIT_DIGIT_GEN) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `k * d <= n /\ n < k * d + d` THEN ARITH_TAC;
          USE_THEN "dig" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(nsum {i | i < 256}
           (\i. (w (EL i (Fa:(A)list)) MOD 2 EXP d) * 2 EXP (i * d))
         DIV 2 EXP (k * d)) DIV 2 EXP (n - k * d) =
        nsum {i | i < 256} (\i. (w (EL i Fa) MOD 2 EXP d) * 2 EXP (i * d))
        DIV 2 EXP n`
       SUBST1_TAC THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
        SUBGOAL_THEN `k * d + (n - k * d) = n` SUBST1_TAC THENL
         [UNDISCH_TAC `k * d <= n /\ n < k * d + d` THEN ARITH_TAC;
          REFL_TAC];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      USE_THEN "oinv" MATCH_MP_TAC THEN
      UNDISCH_TAC `~(k * d <= n /\ n < k * d + d)` THEN
      UNDISCH_TAC `n < SUC k * d` THEN ARITH_TAC];
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `bits:(bool)list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]]
);;

let BYTES_BITSTOBYTES_APPLY th =
  GEN_TAC THEN MATCH_MP_TAC th THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ];;

let BYTES_B2B_32 = prove
 (`!x. BitsToBytes_32_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 256) =
       Value (bytelist_of_num 32 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_32);;

let BYTES_B2B_128 = prove
 (`!x. BitsToBytes_128_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 1024) =
       Value (bytelist_of_num 128 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_128);;

let BYTES_B2B_160 = prove
 (`!x. BitsToBytes_160_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 1280) =
       Value (bytelist_of_num 160 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_160);;

let BYTES_B2B_320 = prove
 (`!x. BitsToBytes_320_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 2560) =
       Value (bytelist_of_num 320 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_320);;

let BYTES_B2B_352 = prove
 (`!x. BitsToBytes_352_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 2816) =
       Value (bytelist_of_num 352 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_352);;

let BYTES_B2B_384 = prove
 (`!x. BitsToBytes_384_hol (list_of_seq (\n. ODD (x DIV 2 EXP n)) 3072) =
       Value (bytelist_of_num 384 x)`,
  BYTES_BITSTOBYTES_APPLY BYTES_BITSTOBYTES_384);;

let BYTES_BYTEENCODE_TAC pre tms g b2b def =
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC(def :: LET_DEF :: LET_END_DEF :: pre) THEN
  MP_TAC(ISPECL tms BYTES_BYTEENCODE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[INT_MUL_RID] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[ISA_NAT_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; b2b] THEN
  MP_TAC(ISPECL g BYTES_MLKEM_ENCODE_NSUM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC;;


let BYTEENCODE_4 = prove
 (BYTEENCODE_4_STMT,
  BYTES_BYTEENCODE_TAC []
   [`4`; `\r:(16)residue. residue_rep r`; `l:((16)residue)list`]
   [`4`; `256`; `\i. residue_rep (EL i (l:((16)residue)list))`]
   BYTES_B2B_128 ByteEncode_d_4_hol_DEF);;

let BYTEENCODE_1 = prove
 (BYTEENCODE_1_STMT,
  BYTES_BYTEENCODE_TAC []
   [`1`; `\r:(2)residue. residue_rep r`; `l:((2)residue)list`]
   [`1`; `256`; `\i. residue_rep (EL i (l:((2)residue)list))`]
   BYTES_B2B_32 ByteEncode_d_1_hol_DEF);;

let BYTEENCODE_5 = prove
 (BYTEENCODE_5_STMT,
  BYTES_BYTEENCODE_TAC []
   [`5`; `\r:(32)residue. residue_rep r`; `l:((32)residue)list`]
   [`5`; `256`; `\i. residue_rep (EL i (l:((32)residue)list))`]
   BYTES_B2B_160 ByteEncode_d_5_hol_DEF);;

let BYTEENCODE_10 = prove
 (BYTEENCODE_10_STMT,
  BYTES_BYTEENCODE_TAC []
   [`10`; `\r:(1024)residue. residue_rep r`; `l:((1024)residue)list`]
   [`10`; `256`; `\i. residue_rep (EL i (l:((1024)residue)list))`]
   BYTES_B2B_320 ByteEncode_d_10_hol_DEF);;

let BYTEENCODE_11 = prove
 (BYTEENCODE_11_STMT,
  BYTES_BYTEENCODE_TAC []
   [`11`; `\r:(2048)residue. residue_rep r`; `l:((2048)residue)list`]
   [`11`; `256`; `\i. residue_rep (EL i (l:((2048)residue)list))`]
   BYTES_B2B_352 ByteEncode_d_11_hol_DEF);;

let BYTEENCODE_12 = prove
 (BYTEENCODE_12_STMT,
  BYTES_BYTEENCODE_TAC [zarr; fz]
   [`12`; `\z:fips203_zq. residue_rep (fips203_zq_residue z)`;
    `l:(fips203_zq)list`]
   [`12`; `256`; `\i. residue_rep (fips203_zq_residue (EL i (l:(fips203_zq)list)))`]
   BYTES_B2B_384 ByteEncode_d_12_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* Byte-slice helpers for the vector wrappers.                             *)
(* ------------------------------------------------------------------------- *)
let BYTES_SCHEDULE_N = prove
 (`!n. native_schedule (n + 1) (\i. int_lt i (&n)) (\i. int_add i (&1)) (&0) =
       list_of_seq (\i. &i) n`,
  GEN_TAC THEN MP_TAC(SPECL [`n + 1`; `0`; `n:num`] NATIVE_SCHEDULE_UPTO) THEN
  REWRITE_TAC[SUB_0; ADD_CLAUSES; ARITH_RULE `n < n + 1`] THEN
  DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* ZqByteDecodeVector12_k: unpack k polynomials from 384*k bytes.           *)
(* ------------------------------------------------------------------------- *)

let ZQBYTEDECODEVECTOR12_2 = prove
 (ZQBYTEDECODEVECTOR12_2_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteDecodeVector12_2_MLKEM512_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF; zvec] THEN
  BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((fips203_zq)list)list)).
       LENGTH (FST s) = 384 /\ LENGTH (SND s) = 2 /\
       (!i. i < k
            ==> EL i (SND s) =
                zqlist (\n. mlkem_decode 12 b (256 * i + n)))` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE];
      REWRITE_TAC[CONJUNCT1 LT];
      ALL_TAC] THEN
    X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`row:byte list`; `values:((fips203_zq)list)list`] THEN
    REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    SUBGOAL_THEN `kv * 384 + 384 <= 768` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    BYTES_LOOP_TAC
     `\j (rowa:byte list).
        LENGTH rowa = 384 /\
        (!q. q < j ==> EL q rowa = EL (384 * kv + q) b)` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        ASM_REWRITE_TAC[];
        REWRITE_TAC[CONJUNCT1 LT];
        ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC THEN
      SUBGOAL_THEN `384 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               ARITH_RULE `384 * kv = kv * 384`;
               NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
               ASSUME `384 * kv + j < LENGTH (b:byte list)`;
               ASSUME `j < LENGTH (rr:byte list)`] THEN
      EXISTS_TAC `isa_list_update rr j (EL (384 * kv + j) (b:byte list))` THEN
      ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `kv * 384 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE] THEN
        SUBGOAL_THEN `kv * 384 + j = 384 * kv + j` SUBST1_TAC THENL
         [ARITH_TAC; REFL_TAC];
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ASM_ARITH_TAC;
          FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ARITH_TAC]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `rowa = mlkem_slice (384 * kv) 384 (b:byte list)`
      SUBST1_TAC THENL
       [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_MLKEM_SLICE];
        ALL_TAC] THEN
      MP_TAC(SPEC `mlkem_slice (384 * kv) 384 (b:byte list)` BYTEDECODE_12) THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `kv < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE] THEN
      EXISTS_TAC
       `(mlkem_slice (384 * kv) 384 (b:byte list),
         isa_list_update values kv
           (zqlist (mlkem_decode 12 (mlkem_slice (384 * kv) 384 b))))` THEN
      REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZQLIST_EQ THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`12`; `b:byte list`; `384 * kv`; `384`; `256 * kv`;
                       `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN
           UNDISCH_TAC `kv * 384 + 384 <= 768` THEN
           UNDISCH_TAC `LENGTH (b:byte list) = 768` THEN
           UNDISCH_TAC `n < 256` THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
                (X_CHOOSE_THEN `vals:((fips203_zq)list)list` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND; NATIVE_BIND_VALUE; UNCURRY_DEF] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `LENGTH (vals:((fips203_zq)list)list) = 2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (vals:((fips203_zq)list)list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ]]);;
let ZQBYTEDECODEVECTOR12_3 = prove
 (ZQBYTEDECODEVECTOR12_3_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteDecodeVector12_3_MLKEM768_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF; zvec] THEN
  BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((fips203_zq)list)list)).
       LENGTH (FST s) = 384 /\ LENGTH (SND s) = 3 /\
       (!i. i < k
            ==> EL i (SND s) =
                zqlist (\n. mlkem_decode 12 b (256 * i + n)))` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE];
      REWRITE_TAC[CONJUNCT1 LT];
      ALL_TAC] THEN
    X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`row:byte list`; `values:((fips203_zq)list)list`] THEN
    REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    SUBGOAL_THEN `kv * 384 + 384 <= 1152` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    BYTES_LOOP_TAC
     `\j (rowa:byte list).
        LENGTH rowa = 384 /\
        (!q. q < j ==> EL q rowa = EL (384 * kv + q) b)` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        ASM_REWRITE_TAC[];
        REWRITE_TAC[CONJUNCT1 LT];
        ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC THEN
      SUBGOAL_THEN `384 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               ARITH_RULE `384 * kv = kv * 384`;
               NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
               ASSUME `384 * kv + j < LENGTH (b:byte list)`;
               ASSUME `j < LENGTH (rr:byte list)`] THEN
      EXISTS_TAC `isa_list_update rr j (EL (384 * kv + j) (b:byte list))` THEN
      ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `kv * 384 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE] THEN
        SUBGOAL_THEN `kv * 384 + j = 384 * kv + j` SUBST1_TAC THENL
         [ARITH_TAC; REFL_TAC];
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ASM_ARITH_TAC;
          FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ARITH_TAC]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `rowa = mlkem_slice (384 * kv) 384 (b:byte list)`
      SUBST1_TAC THENL
       [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_MLKEM_SLICE];
        ALL_TAC] THEN
      MP_TAC(SPEC `mlkem_slice (384 * kv) 384 (b:byte list)` BYTEDECODE_12) THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `kv < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE] THEN
      EXISTS_TAC
       `(mlkem_slice (384 * kv) 384 (b:byte list),
         isa_list_update values kv
           (zqlist (mlkem_decode 12 (mlkem_slice (384 * kv) 384 b))))` THEN
      REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZQLIST_EQ THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`12`; `b:byte list`; `384 * kv`; `384`; `256 * kv`;
                       `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN
           UNDISCH_TAC `kv * 384 + 384 <= 1152` THEN
           UNDISCH_TAC `LENGTH (b:byte list) = 1152` THEN
           UNDISCH_TAC `n < 256` THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
                (X_CHOOSE_THEN `vals:((fips203_zq)list)list` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND; NATIVE_BIND_VALUE; UNCURRY_DEF] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `LENGTH (vals:((fips203_zq)list)list) = 3` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (vals:((fips203_zq)list)list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ]]);;
let ZQBYTEDECODEVECTOR12_4 = prove
 (ZQBYTEDECODEVECTOR12_4_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteDecodeVector12_4_MLKEM1024_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF; zvec] THEN
  BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((fips203_zq)list)list)).
       LENGTH (FST s) = 384 /\ LENGTH (SND s) = 4 /\
       (!i. i < k
            ==> EL i (SND s) =
                zqlist (\n. mlkem_decode 12 b (256 * i + n)))` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE];
      REWRITE_TAC[CONJUNCT1 LT];
      ALL_TAC] THEN
    X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`row:byte list`; `values:((fips203_zq)list)list`] THEN
    REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    SUBGOAL_THEN `kv * 384 + 384 <= 1536` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    BYTES_LOOP_TAC
     `\j (rowa:byte list).
        LENGTH rowa = 384 /\
        (!q. q < j ==> EL q rowa = EL (384 * kv + q) b)` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        ASM_REWRITE_TAC[];
        REWRITE_TAC[CONJUNCT1 LT];
        ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC THEN
      SUBGOAL_THEN `384 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               ARITH_RULE `384 * kv = kv * 384`;
               NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
               ASSUME `384 * kv + j < LENGTH (b:byte list)`;
               ASSUME `j < LENGTH (rr:byte list)`] THEN
      EXISTS_TAC `isa_list_update rr j (EL (384 * kv + j) (b:byte list))` THEN
      ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `kv * 384 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE] THEN
        SUBGOAL_THEN `kv * 384 + j = 384 * kv + j` SUBST1_TAC THENL
         [ARITH_TAC; REFL_TAC];
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ASM_ARITH_TAC;
          FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          ARITH_TAC]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `rowa = mlkem_slice (384 * kv) 384 (b:byte list)`
      SUBST1_TAC THENL
       [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[EL_MLKEM_SLICE];
        ALL_TAC] THEN
      MP_TAC(SPEC `mlkem_slice (384 * kv) 384 (b:byte list)` BYTEDECODE_12) THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `kv < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE] THEN
      EXISTS_TAC
       `(mlkem_slice (384 * kv) 384 (b:byte list),
         isa_list_update values kv
           (zqlist (mlkem_decode 12 (mlkem_slice (384 * kv) 384 b))))` THEN
      REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i < LENGTH (values:((fips203_zq)list)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZQLIST_EQ THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`12`; `b:byte list`; `384 * kv`; `384`; `256 * kv`;
                       `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN
           UNDISCH_TAC `kv * 384 + 384 <= 1536` THEN
           UNDISCH_TAC `LENGTH (b:byte list) = 1536` THEN
           UNDISCH_TAC `n < 256` THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
                (X_CHOOSE_THEN `vals:((fips203_zq)list)list` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND; NATIVE_BIND_VALUE; UNCURRY_DEF] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `LENGTH (vals:((fips203_zq)list)list) = 4` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (vals:((fips203_zq)list)list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ]]);;

(* ZqByteEncodeVector12_k lemmas *)

g `!v. (!i. i < 2 ==> zq_list_ok (v i))
       ==> ZqByteEncodeVector12_2_FIPS203_NTT_MLKEM512_Configuration_hol
             (zvec 2 v) =
           Value (mlkem_encode 12 512 (\n. zarr (v (n DIV 256)) (n MOD 256)))`;;
e(GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteEncodeVector12_2_FIPS203_NTT_MLKEM512_Configuration_hol_DEF;
              zvec; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[common_vec_entries_DEF; common_vec_SEL_CTR]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 (256 * 2)
             (\n. zarr ((v:num->fips203_zq list) (n DIV 256)) (n MOD 256))) =
    768`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 768 /\
      (!n. n < 384 * k
           ==> EL n output =
               EL n (mlkem_encode 12 (256 * 2)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(REWRITE_TAC[fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN
   `kv < LENGTH (list_of_seq (\n. FIPS203_Poly ((v:num->fips203_zq list) n)) 2)`
   ASSUME_TAC THENL [REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_ARITH_TAC;
                     ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; EL_LIST_OF_SEQ; NATIVE_BIND_VALUE;
               LENGTH_LIST_OF_SEQ; ISA_NAT_NUM; fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN `zq_list_ok ((v:num->fips203_zq list) kv)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;
e(POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[zq_list_ok]));;
e(MP_TAC(SPEC `(v:num->fips203_zq list) kv` BYTEENCODE_12));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))) = 384`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 768 /\
      (!n. n < 384 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 12 (256 * 2)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 384` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv)))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `384 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 768` THEN
    UNDISCH_TAC `kv < 2` THEN UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (384 * kv + p)
     (EL p (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 768` THEN
    UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 2` THEN
    UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`;
                 `\m. zarr ((v:num->fips203_zq list) (m DIV 256)) (m MOD 256)`;
                 `kv:num`; `p:num`] BYTES_ENCODE_12_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 384 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 384 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `384 * 2 = 768`;
                              ARITH_RULE `256 * 2 = 512`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(12 * 512) DIV 8 = 768`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(12 * 512) DIV 8 = 768`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ZQBYTEENCODEVECTOR12_2 = top_thm();;

g `!v. (!i. i < 3 ==> zq_list_ok (v i))
       ==> ZqByteEncodeVector12_3_FIPS203_NTT_MLKEM768_Configuration_hol
             (zvec 3 v) =
           Value (mlkem_encode 12 768 (\n. zarr (v (n DIV 256)) (n MOD 256)))`;;
e(GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteEncodeVector12_3_FIPS203_NTT_MLKEM768_Configuration_hol_DEF;
              zvec; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[common_vec_entries_DEF; common_vec_SEL_CTR]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 (256 * 3)
             (\n. zarr ((v:num->fips203_zq list) (n DIV 256)) (n MOD 256))) =
    1152`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 1152 /\
      (!n. n < 384 * k
           ==> EL n output =
               EL n (mlkem_encode 12 (256 * 3)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(REWRITE_TAC[fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN
   `kv < LENGTH (list_of_seq (\n. FIPS203_Poly ((v:num->fips203_zq list) n)) 3)`
   ASSUME_TAC THENL [REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_ARITH_TAC;
                     ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; EL_LIST_OF_SEQ; NATIVE_BIND_VALUE;
               LENGTH_LIST_OF_SEQ; ISA_NAT_NUM; fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN `zq_list_ok ((v:num->fips203_zq list) kv)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;
e(POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[zq_list_ok]));;
e(MP_TAC(SPEC `(v:num->fips203_zq list) kv` BYTEENCODE_12));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))) = 384`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 1152 /\
      (!n. n < 384 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 12 (256 * 3)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 384` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv)))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `384 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1152` THEN
    UNDISCH_TAC `kv < 3` THEN UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (384 * kv + p)
     (EL p (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1152` THEN
    UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 3` THEN
    UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`3`;
                 `\m. zarr ((v:num->fips203_zq list) (m DIV 256)) (m MOD 256)`;
                 `kv:num`; `p:num`] BYTES_ENCODE_12_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 384 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 384 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `384 * 3 = 1152`;
                              ARITH_RULE `256 * 3 = 768`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(12 * 768) DIV 8 = 1152`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(12 * 768) DIV 8 = 1152`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ZQBYTEENCODEVECTOR12_3 = top_thm();;

g `!v. (!i. i < 4 ==> zq_list_ok (v i))
       ==> ZqByteEncodeVector12_4_FIPS203_NTT_MLKEM1024_Configuration_hol
             (zvec 4 v) =
           Value (mlkem_encode 12 1024 (\n. zarr (v (n DIV 256)) (n MOD 256)))`;;
e(GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ZqByteEncodeVector12_4_FIPS203_NTT_MLKEM1024_Configuration_hol_DEF;
              zvec; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[common_vec_entries_DEF; common_vec_SEL_CTR]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 (256 * 4)
             (\n. zarr ((v:num->fips203_zq list) (n DIV 256)) (n MOD 256))) =
    1536`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 1536 /\
      (!n. n < 384 * k
           ==> EL n output =
               EL n (mlkem_encode 12 (256 * 4)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(REWRITE_TAC[fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN
   `kv < LENGTH (list_of_seq (\n. FIPS203_Poly ((v:num->fips203_zq list) n)) 4)`
   ASSUME_TAC THENL [REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_ARITH_TAC;
                     ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; EL_LIST_OF_SEQ; NATIVE_BIND_VALUE;
               LENGTH_LIST_OF_SEQ; ISA_NAT_NUM; fips203_poly_SEL_CTR]);;
e(SUBGOAL_THEN `zq_list_ok ((v:num->fips203_zq list) kv)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;
e(POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[zq_list_ok]));;
e(MP_TAC(SPEC `(v:num->fips203_zq list) kv` BYTEENCODE_12));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))) = 384`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 1536 /\
      (!n. n < 384 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 12 (256 * 4)
                      (\m. zarr ((v:num->fips203_zq list) (m DIV 256))
                                (m MOD 256))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 384` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv)))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `384 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1536` THEN
    UNDISCH_TAC `kv < 4` THEN UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (384 * kv + p)
     (EL p (mlkem_encode 12 256 (zarr ((v:num->fips203_zq list) kv))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1536` THEN
    UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 4` THEN
    UNDISCH_TAC `p < 384` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`;
                 `\m. zarr ((v:num->fips203_zq list) (m DIV 256)) (m MOD 256)`;
                 `kv:num`; `p:num`] BYTES_ENCODE_12_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 384 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 384 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 384 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `384 * 4 = 1536`;
                              ARITH_RULE `256 * 4 = 1024`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(12 * 1024) DIV 8 = 1536`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(12 * 1024) DIV 8 = 1536`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ZQBYTEENCODEVECTOR12_4 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* DecodeCompressedVector_d_c_K_k: k blocks of 32*d bytes to k lists of 256 *)
(* residues (reusing the ByteDecode_d lemmas and the slice decoder).       *)
(* ------------------------------------------------------------------------- *)

g DECODECOMPRESSEDVECTOR_2_STMT;;
e(GEN_TAC THEN DISCH_TAC);;
e(REWRITE_TAC[DecodeCompressedVector_d_10_1024_2_MLKEM512_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((1024)residue)list)list).
       LENGTH (FST s) = 320 /\ LENGTH (SND s) = 2 /\
       (!i. i < k
            ==> EL i (SND s) =
                list_of_seq
                  (\n. residue_of_int_mod (mlkem_decode 10 b (256 * i + n)))
                  256)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND]);;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
p();;
e(X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`row:byte list`; `values:(((1024)residue)list)list`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC);;
e(REWRITE_TAC[UNCURRY_DEF]);;
e(SUBGOAL_THEN `kv * 320 + 320 <= 640` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (rowa:byte list).
      LENGTH rowa = 320 /\
      (!q. q < j ==> EL q rowa = EL (320 * kv + q) b)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
e(X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `320 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
           ARITH_RULE `320 * kv = kv * 320`;
           NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
           ASSUME `320 * kv + j < LENGTH (b:byte list)`;
           ASSUME `j < LENGTH (rr:byte list)`]);;
e(EXISTS_TAC `isa_list_update rr j (EL (320 * kv + j) (b:byte list))`);;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(CONJ_TAC);;
e(SUBGOAL_THEN `kv * 320 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE]);;
e(SUBGOAL_THEN `kv * 320 + j = 320 * kv + j` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;
e(X_GEN_TAC `q:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;
e(DISCH_TAC);;
e(FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `rowa = mlkem_slice (320 * kv) 320 (b:byte list)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MLKEM_SLICE];
    ALL_TAC]);;
e(MP_TAC(SPEC `mlkem_slice (320 * kv) 320 (b:byte list)` BYTEDECODE_10));;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `kv < LENGTH (values:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE]);;
e(EXISTS_TAC
   `(mlkem_slice (320 * kv) 320 (b:byte list),
     isa_list_update values kv
       ((list_of_seq
         (\n. residue_of_int_mod
                (mlkem_decode 10 (mlkem_slice (320 * kv) 320 b) n))
         256
        ):((1024)residue)list))`);;
e(REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE]);;
e(X_GEN_TAC `i:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `i < LENGTH (values:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`10`; `b:byte list`; `320 * kv`; `320`; `256 * kv`;
                   `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
       UNDISCH_TAC `kv * 320 + 320 <= 640` THEN
       UNDISCH_TAC `LENGTH (b:byte list) = 640` THEN
       UNDISCH_TAC `n < 256` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
e(REWRITE_TAC[EXISTS_PAIR_THM]);;
e(DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
              (X_CHOOSE_THEN `vals:(((1024)residue)list)list`
                STRIP_ASSUME_TAC)));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF]);;
e(AP_TERM_TAC);;
e(REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `i:num`);;
e(SUBGOAL_THEN `LENGTH (vals:(((1024)residue)list)list) = 2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(DISCH_TAC);;
e(ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;
let DECODECOMPRESSEDVECTOR_2 = top_thm();;


g DECODECOMPRESSEDVECTOR_3_STMT;;
e(GEN_TAC THEN DISCH_TAC);;
e(REWRITE_TAC[DecodeCompressedVector_d_10_1024_3_MLKEM768_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((1024)residue)list)list).
       LENGTH (FST s) = 320 /\ LENGTH (SND s) = 3 /\
       (!i. i < k
            ==> EL i (SND s) =
                list_of_seq
                  (\n. residue_of_int_mod (mlkem_decode 10 b (256 * i + n)))
                  256)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND]);;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
p();;
e(X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`row:byte list`; `values:(((1024)residue)list)list`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC);;
e(REWRITE_TAC[UNCURRY_DEF]);;
e(SUBGOAL_THEN `kv * 320 + 320 <= 960` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (rowa:byte list).
      LENGTH rowa = 320 /\
      (!q. q < j ==> EL q rowa = EL (320 * kv + q) b)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
e(X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `320 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
           ARITH_RULE `320 * kv = kv * 320`;
           NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
           ASSUME `320 * kv + j < LENGTH (b:byte list)`;
           ASSUME `j < LENGTH (rr:byte list)`]);;
e(EXISTS_TAC `isa_list_update rr j (EL (320 * kv + j) (b:byte list))`);;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(CONJ_TAC);;
e(SUBGOAL_THEN `kv * 320 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE]);;
e(SUBGOAL_THEN `kv * 320 + j = 320 * kv + j` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;
e(X_GEN_TAC `q:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;
e(DISCH_TAC);;
e(FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `rowa = mlkem_slice (320 * kv) 320 (b:byte list)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MLKEM_SLICE];
    ALL_TAC]);;
e(MP_TAC(SPEC `mlkem_slice (320 * kv) 320 (b:byte list)` BYTEDECODE_10));;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `kv < LENGTH (values:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE]);;
e(EXISTS_TAC
   `(mlkem_slice (320 * kv) 320 (b:byte list),
     isa_list_update values kv
       ((list_of_seq
         (\n. residue_of_int_mod
                (mlkem_decode 10 (mlkem_slice (320 * kv) 320 b) n))
         256
        ):((1024)residue)list))`);;
e(REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE]);;
e(X_GEN_TAC `i:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `i < LENGTH (values:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`10`; `b:byte list`; `320 * kv`; `320`; `256 * kv`;
                   `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
       UNDISCH_TAC `kv * 320 + 320 <= 960` THEN
       UNDISCH_TAC `LENGTH (b:byte list) = 960` THEN
       UNDISCH_TAC `n < 256` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
e(REWRITE_TAC[EXISTS_PAIR_THM]);;
e(DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
              (X_CHOOSE_THEN `vals:(((1024)residue)list)list`
                STRIP_ASSUME_TAC)));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF]);;
e(AP_TERM_TAC);;
e(REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `i:num`);;
e(SUBGOAL_THEN `LENGTH (vals:(((1024)residue)list)list) = 3` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(DISCH_TAC);;
e(ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;
let DECODECOMPRESSEDVECTOR_3 = top_thm();;


g DECODECOMPRESSEDVECTOR_4_STMT;;
e(GEN_TAC THEN DISCH_TAC);;
e(REWRITE_TAC[DecodeCompressedVector_d_11_2048_4_MLKEM1024_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(BYTES_LOOP_TAC
   `\k (s:((8)word)list#(((2048)residue)list)list).
       LENGTH (FST s) = 352 /\ LENGTH (SND s) = 4 /\
       (!i. i < k
            ==> EL i (SND s) =
                list_of_seq
                  (\n. residue_of_int_mod (mlkem_decode 11 b (256 * i + n)))
                  256)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND]);;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[LENGTH_REPLICATE]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
p();;
e(X_GEN_TAC `kv:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`row:byte list`; `values:(((2048)residue)list)list`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC);;
e(REWRITE_TAC[UNCURRY_DEF]);;
e(SUBGOAL_THEN `kv * 352 + 352 <= 1408` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (rowa:byte list).
      LENGTH rowa = 352 /\
      (!q. q < j ==> EL q rowa = EL (352 * kv + q) b)`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[CONJUNCT1 LT]);;
e(X_GEN_TAC `j:num` THEN X_GEN_TAC `rr:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `352 * kv + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `j < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD;
           ARITH_RULE `352 * kv = kv * 352`;
           NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE;
           ASSUME `352 * kv + j < LENGTH (b:byte list)`;
           ASSUME `j < LENGTH (rr:byte list)`]);;
e(EXISTS_TAC `isa_list_update rr j (EL (352 * kv + j) (b:byte list))`);;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(CONJ_TAC);;
e(SUBGOAL_THEN `kv * 352 + j < LENGTH (b:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE]);;
e(SUBGOAL_THEN `kv * 352 + j = 352 * kv + j` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;
e(X_GEN_TAC `q:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `q < LENGTH (rr:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `q:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;
e(DISCH_TAC);;
e(FIRST_X_ASSUM(X_CHOOSE_THEN `rowa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `rowa = mlkem_slice (352 * kv) 352 (b:byte list)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `q < LENGTH (rowa:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MLKEM_SLICE];
    ALL_TAC]);;
e(MP_TAC(SPEC `mlkem_slice (352 * kv) 352 (b:byte list)` BYTEDECODE_11));;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE]);;
e(SUBGOAL_THEN `kv < LENGTH (values:(((2048)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_NAT_NUM; NATIVE_BIND_VALUE]);;
e(EXISTS_TAC
   `(mlkem_slice (352 * kv) 352 (b:byte list),
     isa_list_update values kv
       ((list_of_seq
         (\n. residue_of_int_mod
                (mlkem_decode 11 (mlkem_slice (352 * kv) 352 b) n))
         256
        ):((2048)residue)list))`);;
e(REWRITE_TAC[FST; SND; LENGTH_ISA_LIST_UPDATE] THEN ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[LENGTH_MLKEM_SLICE]);;
e(X_GEN_TAC `i:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `i < LENGTH (values:(((2048)residue)list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`11`; `b:byte list`; `352 * kv`; `352`; `256 * kv`;
                   `n:num`] BYTES_MLKEM_DECODE_SLICE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
       UNDISCH_TAC `kv * 352 + 352 <= 1408` THEN
       UNDISCH_TAC `LENGTH (b:byte list) = 1408` THEN
       UNDISCH_TAC `n < 256` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
e(REWRITE_TAC[EXISTS_PAIR_THM]);;
e(DISCH_THEN(X_CHOOSE_THEN `rr:byte list`
              (X_CHOOSE_THEN `vals:(((2048)residue)list)list`
                STRIP_ASSUME_TAC)));;
e(ASM_REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF]);;
e(AP_TERM_TAC);;
e(REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `i:num`);;
e(SUBGOAL_THEN `LENGTH (vals:(((2048)residue)list)list) = 4` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(DISCH_TAC);;
e(ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;
let DECODECOMPRESSEDVECTOR_4 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* EncodeCompressedVector_d_c_K_k: k polynomial rows to k*32*d bytes.     *)
(* ------------------------------------------------------------------------- *)

g `!(c:(((1024)residue)list)list).
     LENGTH c = 2 /\ (!i. i < 2 ==> LENGTH (EL i c) = 256)
     ==> EncodeCompressedVector_d_10_1024_2_MLKEM512_Configuration_hol c =
         Value (mlkem_encode 10 512
                  (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) c)))))`;;
e(GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EncodeCompressedVector_d_10_1024_2_MLKEM512_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 10 (256 * 2)
             (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) (c:(((1024)residue)list)list)))))) =
    640`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 640 /\
      (!n. n < 320 * k
           ==> EL n output =
               EL n (mlkem_encode 10 (256 * 2)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((1024)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `kv < LENGTH (c:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; ISA_NAT_NUM]);;
e(SUBGOAL_THEN `LENGTH (EL kv (c:(((1024)residue)list)list)) = 256` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;

e(MP_TAC(SPEC `EL kv (c:(((1024)residue)list)list)` BYTEENCODE_10));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list)))))) = 320`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 640 /\
      (!n. n < 320 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 10 (256 * 2)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((1024)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 320` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list))))))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `320 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 640` THEN
    UNDISCH_TAC `kv < 2` THEN UNDISCH_TAC `p < 320` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (320 * kv + p)
     (EL p (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list)))))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 640` THEN
    UNDISCH_TAC `n < 320 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 2` THEN
    UNDISCH_TAC `p < 320` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`;
                 `\m. &(residue_rep (EL (m MOD 256)
                           (EL (m DIV 256) (c:(((1024)residue)list)list)))):int`;
                 `kv:num`; `p:num`] BYTES_ENCODE_10_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 320 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 320 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 320 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `320 * 2 = 640`;
                              ARITH_RULE `256 * 2 = 512`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(10 * 512) DIV 8 = 640`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(10 * 512) DIV 8 = 640`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ENCODECOMPRESSEDVECTOR_2 = top_thm();;

g `!(c:(((1024)residue)list)list).
     LENGTH c = 3 /\ (!i. i < 3 ==> LENGTH (EL i c) = 256)
     ==> EncodeCompressedVector_d_10_1024_3_MLKEM768_Configuration_hol c =
         Value (mlkem_encode 10 768
                  (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) c)))))`;;
e(GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EncodeCompressedVector_d_10_1024_3_MLKEM768_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 10 (256 * 3)
             (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) (c:(((1024)residue)list)list)))))) =
    960`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 960 /\
      (!n. n < 320 * k
           ==> EL n output =
               EL n (mlkem_encode 10 (256 * 3)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((1024)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `kv < LENGTH (c:(((1024)residue)list)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; ISA_NAT_NUM]);;
e(SUBGOAL_THEN `LENGTH (EL kv (c:(((1024)residue)list)list)) = 256` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;

e(MP_TAC(SPEC `EL kv (c:(((1024)residue)list)list)` BYTEENCODE_10));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list)))))) = 320`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 960 /\
      (!n. n < 320 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 10 (256 * 3)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((1024)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 320` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list))))))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `320 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 960` THEN
    UNDISCH_TAC `kv < 3` THEN UNDISCH_TAC `p < 320` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (320 * kv + p)
     (EL p (mlkem_encode 10 256 (\n. &(residue_rep (EL n (EL kv (c:(((1024)residue)list)list)))))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 960` THEN
    UNDISCH_TAC `n < 320 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 3` THEN
    UNDISCH_TAC `p < 320` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`3`;
                 `\m. &(residue_rep (EL (m MOD 256)
                           (EL (m DIV 256) (c:(((1024)residue)list)list)))):int`;
                 `kv:num`; `p:num`] BYTES_ENCODE_10_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 320 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 320 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 320 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `320 * 3 = 960`;
                              ARITH_RULE `256 * 3 = 768`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(10 * 768) DIV 8 = 960`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(10 * 768) DIV 8 = 960`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ENCODECOMPRESSEDVECTOR_3 = top_thm();;

g `!(c:(((2048)residue)list)list).
     LENGTH c = 4 /\ (!i. i < 4 ==> LENGTH (EL i c) = 256)
     ==> EncodeCompressedVector_d_11_2048_4_MLKEM1024_Configuration_hol c =
         Value (mlkem_encode 11 1024
                  (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) c)))))`;;
e(GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EncodeCompressedVector_d_11_2048_4_MLKEM1024_Configuration_hol_DEF;
              LET_DEF; LET_END_DEF]);;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 11 (256 * 4)
             (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) (c:(((2048)residue)list)list)))))) =
    1408`
   (LABEL_TAC "target_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC;
    ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\k (output:byte list).
      LENGTH output = 1408 /\
      (!n. n < 352 * k
           ==> EL n output =
               EL n (mlkem_encode 11 (256 * 4)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((2048)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LENGTH_REPLICATE];
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];
      ALL_TAC];
    ALL_TAC]);;
p();;
e(X_GEN_TAC `kv:num` THEN X_GEN_TAC `output:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `kv < LENGTH (c:(((2048)residue)list)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; ISA_NAT_NUM]);;
e(SUBGOAL_THEN `LENGTH (EL kv (c:(((2048)residue)list)list)) = 256` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]);;

e(MP_TAC(SPEC `EL kv (c:(((2048)residue)list)list)` BYTEENCODE_11));;
e(ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC);;
e(REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;
e(SUBGOAL_THEN
   `LENGTH (mlkem_encode 11 256 (\n. &(residue_rep (EL n (EL kv (c:(((2048)residue)list)list)))))) = 352`
   (LABEL_TAC "blk_len") THENL
   [REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC; ALL_TAC]);;
e(BYTES_LOOP_TAC
   `\j (outputa:byte list).
      LENGTH outputa = 1408 /\
      (!n. n < 352 * kv + j
           ==> EL n outputa =
               EL n (mlkem_encode 11 (256 * 4)
                      (\m. &(residue_rep (EL (m MOD 256) (EL (m DIV 256) (c:(((2048)residue)list)list)))))))`);;
e(CONV_TAC(DEPTH_CONV BETA_CONV));;
e(ANTS_TAC);;
p();;
e(REPEAT CONJ_TAC);;
e(ARITH_TAC);;
e(ASM_REWRITE_TAC[]);;
e(REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]);;
e(X_GEN_TAC `p:num` THEN X_GEN_TAC `outputa:byte list` THEN STRIP_TAC);;
e(SUBGOAL_THEN `p < 352` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]);;
e(SUBGOAL_THEN
   `p < LENGTH (mlkem_encode 11 256 (\n. &(residue_rep (EL n (EL kv (c:(((2048)residue)list)list))))))`
   ASSUME_TAC THENL
   [USE_THEN "blk_len" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC]);;
e(SUBGOAL_THEN `352 * kv + p < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1408` THEN
    UNDISCH_TAC `kv < 4` THEN UNDISCH_TAC `p < 352` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[NATIVE_LIST_INDEX; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
               NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE; ISA_NAT_NUM]);;
e(EXISTS_TAC
   `isa_list_update outputa (352 * kv + p)
     (EL p (mlkem_encode 11 256 (\n. &(residue_rep (EL n (EL kv (c:(((2048)residue)list)list)))))))`);;
e(REWRITE_TAC[] THEN REPEAT CONJ_TAC);;
p();;
e(ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE]);;
e(X_GEN_TAC `n:num` THEN DISCH_TAC);;
e(SUBGOAL_THEN `n < LENGTH (outputa:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (outputa:byte list) = 1408` THEN
    UNDISCH_TAC `n < 352 * kv + SUC p` THEN
    UNDISCH_TAC `kv < 4` THEN
    UNDISCH_TAC `p < 352` THEN ARITH_TAC;
    ALL_TAC]);;
e(ASM_SIMP_TAC[EL_ISA_LIST_UPDATE]);;
e(COND_CASES_TAC);;
p();;
e(ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`;
                 `\m. &(residue_rep (EL (m MOD 256)
                           (EL (m DIV 256) (c:(((2048)residue)list)list)))):int`;
                 `kv:num`; `p:num`] BYTES_ENCODE_11_BLOCK_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[mlkem_encode] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(256 * kv + i) DIV 256 = kv /\
                (256 * kv + i) MOD 256 = i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      ASM_SIMP_TAC[ARITH_RULE `256 * (kv:num) + i = kv * 256 + i`;
                   MOD_MULT_ADD; MOD_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
p();;
e(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 352 * kv + SUC p` THEN
    UNDISCH_TAC `~(n = 352 * kv + p)` THEN ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;
p();;
e(DISCH_THEN(X_CHOOSE_THEN `outa:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(EXISTS_TAC `outa:byte list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `n < 352 * SUC kv` THEN ARITH_TAC);;
e(DISCH_THEN(X_CHOOSE_THEN `outb:byte list` STRIP_ASSUME_TAC));;
e(ASM_REWRITE_TAC[]);;
e(AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ]);;
e(CONJ_TAC);;
e(ASM_REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN ARITH_TAC);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `352 * 4 = 1408`;
                              ARITH_RULE `256 * 4 = 1024`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_ENCODE_LENGTH;
                              ARITH_RULE `(11 * 1024) DIV 8 = 1408`]) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH; ARITH_RULE `(11 * 1024) DIV 8 = 1408`] THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;
p();;


let ENCODECOMPRESSEDVECTOR_4 = top_thm();;
