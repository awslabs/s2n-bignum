(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment, the segment from loop4 (phase 2 of the model, the       *)
(* search loop with skipping): the probe of the table at the hash of the 4   *)
(* bytes at ip, then                                                         *)
(*  - no match: to loop4 with the next ip, or to join4 (emit_remainder) if   *)
(*    the next probe would pass ip_limit (1 or 2 model steps);               *)
(*  - a match: EmitLiteral of [next_emit, ip) (phase 3) to loop6 (phase 4):  *)
(*    a literal of at most 16 bytes with one 16-byte copy, a longer one with *)
(*    loop5 (SNAPPY_CF1_LOOP5) after a tag of 1, 2 or 3 bytes.               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* loop5, the copy of a literal in chunks of 16 bytes (EmitLiteral): from    *)
(* the header with the literal [a, a + len) of the input to copy to e0 in   *)
(* the output (len >= 1), to the exit, with the literal there. The last     *)
(* chunk reads and writes up to 15 bytes beyond the literal.                *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_LOOP5_STMT =
 `!pc src (inp:byte list) op a e0 len (e:uarch_event list).
    aligned 4096 (word pc:int64) /\
    1 <= len /\ a + len + 15 <= LENGTH inp /\
    val src + LENGTH inp < 2 EXP 64 /\
    val op + e0 + len + 15 < 2 EXP 64 /\
    nonoverlapping (word_add op (word e0),len + 15) (src,LENGTH inp) /\
    nonoverlapping (word_add op (word e0),len + 15)
                   (word pc,libsnappy_rw + libsnappy_rw_size)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragment_loop5) /\
              read X6 s = word_add src (word a) /\
              read X8 s = word_add op (word e0) /\
              read X0 s = word_add op (word(e0 + len)) /\
              read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
              read events s = e)
         (\s. read PC s = word(pc + CompressFragment_loop5_exit) /\
              read (memory :> bytes(word_add op (word e0),len)) s =
              num_of_bytelist(SUB_LIST(a,len) inp) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [word_add src (word a),len + 15]
                                         [word_add op (word e0),len + 15])
         (MAYCHANGE [PC; X6; X8; X10; X11] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add op (word e0),len + 15)])`;;
let SNAPPY_CF1_LOOP5 = prove
 (SNAPPY_CF1_LOOP5_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. ensures arm
   (\s. ?i. m = len - 16 * i /\ 16 * i < len /\
            aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
            read PC s = word(pc + CompressFragment_loop5) /\
            read X6 s = word_add src (word (a + 16 * i)) /\
            read X8 s = word_add op (word (e0 + 16 * i)) /\
            read X0 s = word_add op (word(e0 + len)) /\
            read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
            read (memory :> bytes(word_add op (word e0),16 * i)) s =
            num_of_bytelist(SUB_LIST(a,16 * i) inp) /\
            ?e2. read events s = APPEND e2 e /\
                 memaccess_inbounds e2 [word_add src (word a),len + 15]
                                       [word_add op (word e0),len + 15])
   (\s. read PC s = word(pc + CompressFragment_loop5_exit) /\
              read (memory :> bytes(word_add op (word e0),len)) s =
              num_of_bytelist(SUB_LIST(a,len) inp) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [word_add src (word a),len + 15]
                                         [word_add op (word e0),len + 15])
         (MAYCHANGE [PC; X6; X8; X10; X11] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add op (word e0),len + 15)])`
  MP_TAC THENL [ALL_TAC;
   DISCH_THEN(fun th -> MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
     EXISTS_TAC (el 1 (snd(strip_comb(concl(SPEC `len:num` th))))) THEN
     CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC(SPEC `len:num` th)]) THEN
   REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
   SNAPPY_EV_FIRST_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; SUB_LIST_CLAUSES; num_of_bytelist] THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]] THEN
  MATCH_MP_TAC ENSURES_MEASURE_INDUCT THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  SNAPPY_EV_CHOOSE_TAC THEN
  SNAPPY_LOAD_TAC [64,`a + 16 * i`; 64,`(a + 16 * i) + 8`] THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (1--4) THEN
  SNAPPY_PC_NUM_TAC [] THEN
  ARM_PC_CASES_TAC NO_TAC THEN
  BSTEP_FINAL_TAC THEN SNAPPY_EV_FIRST_TAC THENL
   [DISJ2_TAC THEN EXISTS_TAC `len - 16 * (i + 1)` THEN
    CONJ_TAC THENL [SNAPPY_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `i + 1` THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY SNAPPY_ARITH_TAC THEN TRY(SNAPPY_FACT_TAC SNAPPY_WORD_NUM_TAC) THEN
    REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    MATCH_MP_TAC SNAPPY_READ_STEP16 THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_ARITH_TAC;
    DISJ1_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SNAPPY_READ_PREFIX THEN EXISTS_TAC `16 * i + 16` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SNAPPY_READ_STEP16 THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_ARITH_TAC;
      SNAPPY_ARITH_TAC; SNAPPY_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics of the segment.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The byte count of a long literal from the leading zeros of len - 1.     *)

let SNAPPY_CF1_S2_CLZ_COUNT = prove
 (`!L. 60 <= L /\ L < 65536
       ==> word_xor (word_ishr (word (word_clz (word L:int32)):int32) 3) (word 3) =
           word (if L < 256 then 0 else 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = word_clz (word L:int32)` THEN
  SUBGOAL_THEN `16 <= z /\ z <= 26 /\ (L < 256 <=> 24 <= z)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[WORD_LE_CLZ_VAL; ARITH_RULE `z <= 26 <=> ~(27 <= z)`] THEN
    REWRITE_TAC[DIMINDEX_32; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `L < 65536 ==> L < 4294967296`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ARITH_RULE `16 <= z /\ z <= 26
    ==> z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/
        z = 23 \/ z = 24 \/ z = 25 \/ z = 26`) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SLE_TAC l k = W(fun (asl,w) ->
  let th = SPECL [l; k] SNAPPY_WORD32_SLE in
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), CONV_TAC NUM_REDUCE_CONV THEN SNAPPY_ARITH_TAC) in
  ARM_PC_REWRITE_TAC[MP th ath]);;

let S2_HEAD_TAC =
  SNAPPY_CF1_SEG_START_TAC THEN
  SNAPPY_ABBREV_TAC `h = snappy_hash1 ts (snappy_load32 inp ip)` THEN
  SNAPPY_TABLE_SPLIT_TAC `h:num`
   (EXPAND_TAC "h" THEN MATCH_MP_TAC SNAPPY_HASH1_LT THEN SNAPPY_ARITH_TAC) THEN
  SUBGOAL_THEN `t1(h:num) + 4 <= LENGTH(inp:byte list) /\ t1 h < 65536`
    STRIP_ASSUME_TAC THENL [SNAPPY_TBOUND_TAC `h:num`; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word (t1(h:num)):int16):int64 = word (t1 h)` ASSUME_TAC THENL
   [REWRITE_TAC[word_zx] THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_16] THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
  SNAPPY_LOAD_TAC [32,`t1(h:num):num`] THEN
  ARM_BSTEP_TAC ~rewrites:[ASSUME `word_zx (word (t1(h:num)):int16):int64 = word (t1 h)`]
    SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (1--11) THEN
  ARM_PC_REWRITE_TAC[MATCH_MP SNAPPY_WORD32_SUB_EQ_0
    (CONJ (SPECL [`inp:byte list`; `t1(h:num):num`] SNAPPY_LOAD32_BOUND)
          (SPECL [`inp:byte list`; `ip:num`] SNAPPY_LOAD32_BOUND))] THEN
  ARM_PC_CASES_TAC NO_TAC;;

let S2_NOMATCH_TAC =
  SNAPPY_LOAD_TAC [32,`ip + sk DIV 32`] THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (12--20) THEN
  SNAPPY_REWRITE_FACTS_TAC [`X0`]
   [MATCH_MP SNAPPY_HASH1_WORD (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
    SNAPPY_VAL_WORD_LOAD32] THEN
  SNAPPY_PC_NUM_TAC [] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (21--22) THEN SNAPPY_TABLE_JOIN_TAC `h:num` `ip:num` THEN
    BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 2 THEN SNAPPY_CF1_MACH2_TAC;
    SNAPPY_TABLE_JOIN_TAC `h:num` `ip:num` THEN
    BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 1 THEN SNAPPY_CF1_MACH2_TAC];;

let S2_MATCH_HEAD_TAC =
  SUBGOAL_THEN `word_sub (word_add src (word ip)) (word_add src (word ne)):int64 = word(ip - ne) /\
                word_sub (word(ip - ne):int32) (word 1) = word(ip - ne - 1)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SNAPPY_WORD_SUB_ADD_ADD THEN SNAPPY_ARITH_TAC;
                    REWRITE_TAC[ARITH_RULE `ip - ne - 1 = (ip - ne) - 1`; WORD_SUB] THEN
                    COND_CASES_TAC THEN REWRITE_TAC[] THEN SNAPPY_ARITH_TAC];
    ALL_TAC] THEN
  ARM_BSTEP_TAC ~rewrites:[ASSUME `word_sub (word_add src (word ip)) (word_add src (word ne)):int64 = word(ip - ne)`;
                            ASSUME `word_sub (word(ip - ne):int32) (word 1) = word(ip - ne - 1)`;
                            SNAPPY_WORD_ZX_WORD_64_32] SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (12--15) THEN
  SLE_TAC `ip - ne:num` `16` THEN
  SUBGOAL_THEN `LENGTH(out:byte list) + 17 <= 27 + LENGTH(inp:byte list) + LENGTH inp DIV 6 /\
                LENGTH out + (ip - ne) + 20 <= 27 + LENGTH inp + LENGTH inp DIV 6`
  STRIP_ASSUME_TAC THENL [SNAPPY_ARITH_TAC; ALL_TAC] THEN
  SNAPPY_ABBREV_TAC `lo = LENGTH(out:byte list)` THEN
  ARM_PC_CASES_TAC NO_TAC;;

let S2_LIT_CLOSE_TAC =
  SNAPPY_TABLE_JOIN_TAC `h:num` `ip:num` THEN
  BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 2 THEN
  MP_TAC(SPEC `SUB_LIST(ne,ip - ne) (inp:byte list)` SNAPPY_EMIT_LITERAL_SHORT) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN (ip - ne) (LENGTH(inp:byte list) - ne) = ip - ne` SUBST1_TAC THENL
   [SNAPPY_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word_add (src:int64) (word (LENGTH(inp:byte list)))) (word 16) =
    word_add src (word (LENGTH inp - 16))`
   (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X10`] [th]) THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word_add a b) c = word_add a (word_sub b c)`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  SNAPPY_CF1_MACH2_TAC THEN
  TRY(MATCH_MP_TAC SNAPPY_READ_APPEND_TAG THEN
      MAP_EVERY EXISTS_TAC [`lo:num`; `ip - ne:num`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        W(fun (asl,w) -> FIRST_ASSUM(fun th ->
          if lhs(concl th) = lhs w then GEN_REWRITE_TAC LAND_CONV [th]
          else NO_TAC)) THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SHL; VAL_WORD_SUBWORD;
                    VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
        (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
        REFL_TAC;
        FIRST_ASSUM ACCEPT_TAC ORELSE
        (MATCH_MP_TAC SNAPPY_READ_COPY16 THEN REPEAT CONJ_TAC THEN
         TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_ARITH_TAC);
        REWRITE_TAC[LENGTH_SUB_LIST] THEN SNAPPY_ARITH_TAC]) THEN
  TRY(SNAPPY_FACT_TAC
   (REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST;
                ASSUME `LENGTH(out:byte list) = lo`] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC SNAPPY_VAL_THMS THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
    SNAPPY_ARITH_TAC));;
let CLZ_FIX_TAC b =
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term (fun t -> try fst(dest_const t) = "word_clz" with Failure _ -> false)) (concl th)
     then SNAPPY_REWRITE_FACTS_TAC [`X0`; `X8`; `X10`]
            [REWRITE_RULE[if b then ASSUME `ip - ne - 1 < 256` else ASSUME `~(ip - ne - 1 < 256)`] th]
     else NO_TAC);;
let S2_LONG_TAC c =
  let num = mk_small_numeral in
  let e0 = mk_binary "+" (`lo:num`, num (c+1)) in
  let fx = subst [num (c-1),`k1:num`; e0,`e0:num`]
   `word_add (word_add op (word lo)) (word_sx (word_add (word k1) (word 2):int32)):int64 =
    word_add op (word e0)` in
  let fx0 = subst [num (c-1),`k1:num`; e0,`e0:num`]
   `word_add (word_add (word_add op (word lo)) (word_sx (word_add (word k1) (word 2):int32)))
             (word_sx (word (ip - ne):int32)):int64 =
    word_add op (word (e0 + (ip - ne)))` in
  let fxt = subst [num (c-1),`k1:num`; num (4*(59+c)),`tg:num`]
   `word_zx (word_shl ((word_subword (word_add (word k1) (word 60):int32) (0,6)):int32) 2):byte = word tg` in
  SUBGOAL_THEN (list_mk_conj [fx;fx0])
   (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X0`; `X8`] [th]) THENL
   [W(fun (asl,w) -> let th = TAC_PROOF((asl,`ip - ne < 2 EXP 31`), SNAPPY_ARITH_TAC) in
      REWRITE_TAC[MATCH_MP SNAPPY_WORD_SX_32_64 th]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN fxt ASSUME_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if (try lhand(lhs(concl th)) = `memory :> bytes32 (word_add op (word (lo + 1)))`
        with Failure _ -> false)
    then ASSUME_TAC(MP (ISPECL [`memory:(armstate,int64->byte)component`;
            `word_add (op:int64) (word (lo + 1))`; rand(concl th); num c; rand(lhs(concl th))]
            SNAPPY_READ_BYTES_OF_WORD)
           (CONJ (REWRITE_RULE[BYTES32_WBYTES] th)
                 (TAC_PROOF(([],subst [num c,`c:num`] `8 * c <= dimindex(:32)`),
                            REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC))))
    else NO_TAC) THEN
  W(fun (asl,w) ->
   let th = SPECL [`pc:num`; `src:int64`; `inp:byte list`; `op:int64`; `ne:num`; e0; `ip - ne:num`;
                   snappy_current_events (asl,w)]
     SNAPPY_CF1_LOOP5 in
   let ant = lhand(concl th) in
   let ath = TAC_PROOF((asl,ant), REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
                        TRY SNAPPY_ARITH_TAC THEN NONOVERLAPPING_TAC) in
   ARM_BSTEP_CALL_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (MP th ath) "s29") THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (30--34);;
let S2_LONG_CLOSE_TAC c =
  let num = mk_small_numeral in
  SNAPPY_TABLE_JOIN_TAC `h:num` `ip:num` THEN
  BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 2 THEN
  MP_TAC(SPEC `SUB_LIST(ne,ip - ne) (inp:byte list)` SNAPPY_EMIT_LITERAL_LONG) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN (ip - ne) (LENGTH(inp:byte list) - ne) = ip - ne` SUBST1_TAC THENL
   [SNAPPY_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(fun (asl,w) ->
    let cc = `ip - ne - 1 < 256` in
    let cth = if c = 1 then EQT_INTRO(TAC_PROOF((asl,cc),SNAPPY_ARITH_TAC))
              else EQF_INTRO(TAC_PROOF((asl,mk_neg cc),SNAPPY_ARITH_TAC)) in
    REWRITE_TAC[cth]) THEN
  SUBGOAL_THEN
   `word_sub (word_add (src:int64) (word (LENGTH(inp:byte list)))) (word 16) =
    word_add src (word (LENGTH inp - 16))`
   (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X10`] [th]) THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word_add a b) c = word_add a (word_sub b c)`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  SNAPPY_CF1_MACH2_TAC THEN
  TRY(MATCH_MP_TAC SNAPPY_READ_APPEND_TAG_HDR THEN
      MAP_EVERY EXISTS_TAC [`lo:num`; num c; mk_binary "+" (`lo:num`,num (c+1)); `ip - ne:num`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        W(fun (asl,w) -> FIRST_ASSUM(fun th ->
          if lhs(concl th) = lhs w then GEN_REWRITE_TAC LAND_CONV [th]
          else NO_TAC)) THEN
        W(fun (asl,w) ->
          let th = MATCH_MP SNAPPY_CF1_S2_CLZ_COUNT
            (TAC_PROOF((asl,`60 <= ip - ne - 1 /\ ip - ne - 1 < 65536`),
                       SNAPPY_ARITH_TAC)) in
          let cc = `ip - ne - 1 < 256` in
          let cth = if c = 1 then EQT_INTRO(TAC_PROOF((asl,cc),SNAPPY_ARITH_TAC))
                    else EQF_INTRO(TAC_PROOF((asl,mk_neg cc),SNAPPY_ARITH_TAC)) in
          REWRITE_TAC[REWRITE_RULE[cth] th]) THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
        W(fun (asl,w) -> FIRST_ASSUM(fun th ->
          if lhs(concl th) = lhs w then GEN_REWRITE_TAC LAND_CONV [th]
          else NO_TAC)) THEN
        REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
        W(fun (asl,w) -> let th = TAC_PROOF((asl,`ip - ne - 1 < 2 EXP 32`), SNAPPY_ARITH_TAC) in
          REWRITE_TAC[MATCH_MP MOD_LT th]);
        REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[LENGTH_SUB_LIST] THEN SNAPPY_ARITH_TAC;
        ARITH_TAC]) THEN
  TRY(SNAPPY_FACT_TAC
   (REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST; LENGTH_BYTELIST_OF_NUM;
                ASSUME `LENGTH(out:byte list) = lo`] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC SNAPPY_VAL_THMS THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
    SNAPPY_ARITH_TAC));;

let S2_SHORT_TAC =
  SNAPPY_LOAD_TAC [64,`ne:num`; 64,`ne + 8`] THEN
  ARM_BSTEP_TAC ~rewrites:[SNAPPY_WORD_ZX_WORD_64_32] SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (16--27) THEN
  SUBGOAL_THEN
   `word_add (word_add op (word lo)) (word_sx (word_add (word (ip - ne)) (word 1):int32)):int64 =
    word_add op (word (lo + (ip - ne + 1)))`
   (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X0`] [th]) THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN
    W(fun (asl,w) -> let th = TAC_PROOF((asl,`ip - ne + 1 < 2 EXP 31`), SNAPPY_ARITH_TAC) in
      REWRITE_TAC[MATCH_MP SNAPPY_WORD_SX_32_64 th]) THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
    ALL_TAC] THEN
  S2_LIT_CLOSE_TAC;;

let S2_MEDIUM_TAC =
  ARM_BSTEP_TAC ~rewrites:[SNAPPY_WORD_ZX_WORD_64_32] SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (18--23) THEN
  SUBGOAL_THEN `word_add (word_add op (word lo)) (word 1):int64 = word_add op (word (lo + 1)) /\
                word_add (word_add (word_add op (word lo)) (word 1)) (word_sx (word (ip - ne):int32)):int64 =
                word_add op (word ((lo + 1) + (ip - ne)))`
   (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X0`; `X8`] [th]) THENL
  [W(fun (asl,w) -> let th = TAC_PROOF((asl,`ip - ne < 2 EXP 31`), SNAPPY_ARITH_TAC) in
      REWRITE_TAC[MATCH_MP SNAPPY_WORD_SX_32_64 th]) THEN
   CONV_TAC WORD_RULE; ALL_TAC] THEN
  W(fun (asl,w) ->
   let th = SPECL [`pc:num`; `src:int64`; `inp:byte list`; `op:int64`; `ne:num`; `lo + 1`; `ip - ne:num`;
                   snappy_current_events (asl,w)] SNAPPY_CF1_LOOP5 in
   let ant = lhand(concl th) in
   let ath = TAC_PROOF((asl,ant), REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY SNAPPY_ARITH_TAC THEN NONOVERLAPPING_TAC) in
   ARM_BSTEP_CALL_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (MP th ath) "s24") THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (25--29) THEN
  S2_LIT_CLOSE_TAC;;

let S2_LONGCASES_TAC =
  ARM_BSTEP_TAC ~rewrites:[SNAPPY_WORD_ZX_WORD_64_32] SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (18--28) THEN
  MP_TAC(SPEC `ip - ne - 1` SNAPPY_CF1_S2_CLZ_COUNT) THEN
  ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_TAC] THEN
  ASM_CASES_TAC `ip - ne - 1 < 256` THENL
   [CLZ_FIX_TAC true THEN S2_LONG_TAC 1 THEN S2_LONG_CLOSE_TAC 1;
    CLZ_FIX_TAC false THEN S2_LONG_TAC 2 THEN S2_LONG_CLOSE_TAC 2];;

let SNAPPY_CF1_SEG2_TAC =
  S2_HEAD_TAC THENL
   [S2_NOMATCH_TAC;
    S2_MATCH_HEAD_TAC THENL
     [S2_SHORT_TAC;
      ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (16--17) THEN
      SLE_TAC `ip - ne - 1:num` `59` THEN
      ARM_PC_CASES_TAC NO_TAC THENL [S2_MEDIUM_TAC; S2_LONGCASES_TAC]]];;

(* ------------------------------------------------------------------------- *)
(* The segment.                                                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_SEG2 = prove
 (SNAPPY_CF1_SEG2_STMT,
  SNAPPY_CF1_SEG2_TAC);;
