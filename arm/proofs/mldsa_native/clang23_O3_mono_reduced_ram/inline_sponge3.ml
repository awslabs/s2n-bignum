(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for the SHAKE256 sponge that clang 23 -O3 inlines into the  *)
(* functions of the clang23_O3_mono_reduced_ram image, continued from        *)
(* inline_sponge2.ml: the XOR of the last r = mlen MOD 136 bytes of the      *)
(* message into the state (the tail, which takes one of the paths over the   *)
(* loops over blocks of 32 bytes, of 8 bytes and of single bytes, by r), and *)
(* the lemmas on the squeezing of the first 64 bytes.                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge2.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the masks AND 0xe0, 0xf8, 0x18 of the length that is left.  *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_AND_MASK = prove
 (`!n k. n < 256 /\ k <= 8
         ==> word_and (word n:int64) (word (2 EXP k - 1)) = word (n MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 8` THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `n MOD 2 EXP k < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `n:num` THEN ASM_REWRITE_TAC[MOD_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let SPONGE2_AND_MASK3 = prove
 (`!n. n < 256
       ==> word_and (word n:int64) (word 255) = word (n MOD 256) /\
           word_and (word n:int64) (word 31) = word (n MOD 32) /\
           word_and (word n:int64) (word 7) = word (n MOD 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `8`] SPONGE2_AND_MASK) THEN
  MP_TAC(SPECL [`n:num`; `5`] SPONGE2_AND_MASK) THEN
  MP_TAC(SPECL [`n:num`; `3`] SPONGE2_AND_MASK) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SPONGE2_WSUB = prove
 (`!a b c. b <= a /\ a - b = c ==> word_sub (word a:int64) (word b) = word c`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[]);;

let SPONGE2_MASK = prove
 (`!n. n < 256
       ==> word_and (word n:int64) (word 224) = word(32 * (n DIV 32)) /\
           word_and (word n:int64) (word 248) = word(8 * (n DIV 8)) /\
           word_and (word n:int64) (word 24) = word(8 * ((n DIV 8) MOD 4))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPONGE2_AND_MASK3) THEN
  SUBGOAL_THEN `n MOD 256 = n` ASSUME_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:int64. word_and x (word 224) = word_sub (word_and x (word 255)) (word_and x (word 31)) /\
              word_and x (word 248) = word_sub (word_and x (word 255)) (word_and x (word 7)) /\
              word_and x (word 24) = word_sub (word_and x (word 31)) (word_and x (word 7))`
   (MP_TAC o SPEC `word n:int64`) THENL [GEN_TAC THEN CONV_TAC BITBLAST_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC SPONGE2_WSUB THEN CONJ_TAC THEN MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`n:num`; `8`; `4`] MOD_MULT_MOD)) THEN
  REWRITE_TAC[ASSUME `n MOD 256 = n`] THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC);;

(* ---- pieces of the tail proof ---- *)

let SPONGE2_VAL_ADD_SMALL = prove
 (`!a:int64 n. val a + n < 2 EXP 64 ==> val(word_add a (word n):int64) = val a + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
(*** More facts on r: r MOD 32 = 8 * ((r DIV 8) MOD 4) + r MOD 8 ***)

let TL_MOD4 = prove
 (`!r. (r MOD 32 < 8 <=> 8 * (r DIV 8) MOD 4 = 0) /\
       32 * r DIV 32 + 8 * (r DIV 8) MOD 4 = 8 * r DIV 8`,
  GEN_TAC THEN MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `8`; `4`] MOD_MULT_MOD)) THEN
  DISJ_CASES_TAC(ARITH_RULE `(r DIV 8) MOD 4 = 0 \/ 1 <= (r DIV 8) MOD 4`) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The first 64 bytes of the final state are the SHAKE256 of the message.    *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_PH2 = prove
 (`!mlen M.
        num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) =
        val(keccak_f1600 (mld_keccak_finalize 136 31
              (FST(mld_keccak_absorb 136 (word 0) 0 mlen M)) (mlen MOD 136))) MOD 2 EXP 512`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`keccak_f1600 (mld_keccak_finalize 136 31 (FST(mld_keccak_absorb 136 (word 0) 0 mlen M)) (mlen MOD 136))`; `64`] NUM_OF_BYTELIST_STATE_BYTES) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 64 = 512`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; mld_keccak_squeeze_byte] THEN
  SUBGOAL_THEN `(136 + j) DIV 136 = 1` ASSUME_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(136 + j) MOD 136 = j` ASSUME_TAC THENL [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[num_CONV `1`; keccak_squeeze] THEN
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** 128-bit chunks of the state in memory ***)

let SPONGE2_BYTES128_OF_WBYTES = prove
 (`!(a:int64) (X:1600 word) k (s:armstate).
        read (memory :> wbytes a) s = X /\ k < 12
        ==> read (memory :> bytes128 (word_add a (word (16 * k)))) s =
            word_subword X (128 * k,128)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `16 * k`; `s:armstate`]
         READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
      ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 * 16 * k = 128 * k`; MOD_MOD_REFL]]);;

let SPONGE2_BYTES_OF_BYTES128 = prove
 (`!(a:int64) n x (s:armstate).
        (!j. j < n
             ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s =
                 word((x DIV 2 EXP (128 * j)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL;
                EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`;
              ARITH_RULE `128 * SUC n = 128 * n + 128`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 * n = 128 * n`; EXP_ADD] THEN
  GEN_REWRITE_TAC (RAND_CONV) [MOD_MULT_MOD] THEN
  ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The XOR of the rest of the message into the state (SPONGE2_TAIL_STMT), as *)
(* a proof of the paths over the loops of the instance of the function fn,   *)
(* with the instances of the three loop lemmas of inline_sponge.ml and the   *)
(* lemmas above for the registers that the masks give. The path is by r:     *)
(* r = 0, 0 < r < 8 (bytes), 8 <= r < 32 (8-byte blocks, then bytes) and     *)
(* r >= 32 (32-byte blocks, then 8-byte blocks, then bytes).                 *)
(* ------------------------------------------------------------------------- *)

let PROVE_SPONGE3_TAIL fn pr lr =
  let mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc" in
  let exec = SPONGE2_L1_EXEC fn in
  let TL_PTR = INLINE_XOR_BYTES_PTR_LOOP mc exec (fn^"_loop2") (fn^"_loop2_exit") "X8" "X10" "X9" "X11" "X12" in
  let TL_D = INLINE_XOR_BYTES_D_LOOP mc exec (fn^"_loop4") (fn^"_loop4_exit") "X11" "X10" "X9" ["Q0";"Q1"] in
  let TL_Q = INLINE_XOR_BYTES_Q_LOOP mc exec (fn^"_loop3") (fn^"_loop3_exit") "X11" "X10" "X12" ["Q0";"Q1";"Q2";"Q3"] in
  let sp2_tail_setup =
    ASSUME_CALLEE_SAFETY_TAILED_TAC TL_PTR "H_PTR" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC TL_D "H_D" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC TL_Q "H_Q" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(d:int64) (r:num) (sp:int64) (pc:num).
        if r = 0 then f_ev_0 d r sp pc
        else if r < 8 then f_ev_1 d r sp pc
        else if r < 32 then
          (if r MOD 8 = 0 then f_ev_2a d r sp pc else f_ev_2b d r sp pc)
        else if r MOD 32 = 0 then f_ev_3a d r sp pc
        else if r MOD 32 < 8 then f_ev_3b d r sp pc
        else if r MOD 8 = 0 then f_ev_3c d r sp pc
        else f_ev_3d d r sp pc
      :(uarch_event)list` THEN
    REPEAT META_EXISTS_TAC THEN
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `d:int64`; `r:num`; `R:num`; `S1:1600 word`;
      `sp:int64`; `pc:num`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
                ALL; fst exec] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add sp (word 64),200)) (s0:armstate) = val (S1:1600 word)`
     ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if concl th = `read (memory :> wbytes (word_add sp (word 64))) (s0:armstate) = (S1:1600 word)` then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[READ_MEMORY_WBYTES_1600]; ALL_TAC] in

  let sp2_flag_rewrite name = fun (asl,w) ->
    let th = snd(find (fun (_,th) -> try is_iff(concl th) && string_of_term(lhs(concl th)) = name with _ -> false) asl) in
    REWRITE_TAC[th] (asl,w) in

  (*** The start: facts on r ***)
  
  let tl_facts =
    SUBGOAL_THEN `val(word r:int64) = r` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP SPONGE2_MASK
      (MP (ARITH_RULE `r < 136 ==> r < 256`) th))) THEN STRIP_TAC in

  let tl_ar hs =
    MAP_EVERY (fun h -> FIRST_ASSUM(fun th -> if concl th = h then MP_TAC th else NO_TAC)) hs THEN
    ARITH_TAC in

  (*** r = 0 ***)
  
  let sp2_r0_tac =
    FIRST_X_ASSUM(fun th -> if concl th = `read (memory :> bytes(d,0)) (s0:armstate) = R` then
      SUBST_ALL_TAC(SYM(REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] th)) else NO_TAC) in

  let tl_r0 =
    FIRST_X_ASSUM(fun th -> if concl th = `r = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
    sp2_r0_tac THEN ARM_STEPS_TAC exec (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN
    CONJ_TAC THENL [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; DISCHARGE_SAFETY_PROPERTY_TAC] in

  (*** The end: from the bytes up to r and the rest to the state ***)
  
  let sp2_end sname =
    MP_TAC (SPONGE2_NORMADDR (SPONGE2_SIMP (SPECL [`word_add sp (word 64):int64`; `d:int64`; `S1:1600 word`; `R:num`; `0`; `r:num`; mk_var(sname,`:armstate`)] XOR_FINAL))) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; tl_ar [`r < 136`]]; DISCH_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN FIRST_ASSUM ACCEPT_TAC; MONOTONE_MAYCHANGE_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] in

  (*** The call of a loop lemma ***)
  
  let sp2_callp name n =
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec name []
       [`d:int64`; `r:num`; `sp:int64`; `pc:num`] n in

  (*** r < 8 ***)
  
  let tl_lt8 =
    ARM_STEPS_TAC exec (1--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; WORD_ADD_0]) THEN
    SPONGE2_SPEC_HYP "H_PTR" "H_PTR0" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `0`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    SUBGOAL_THEN `read (memory :> bytes (word_add sp (word 64),0)) (s8:armstate) = val (word_xor S1 (word R):1600 word) MOD 1` ASSUME_TAC THENL
       [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MOD_1]; ALL_TAC] THEN
    SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [tl_ar [`~(r = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `r <= 200` ASSUME_TAC THENL [tl_ar [`r < 136`]; ALL_TAC] THEN
    sp2_callp "H_PTR0" 9 THEN
    sp2_end "s9" in

  (*** r >= 8: the code checks that the data does not overlap the state ***)
  
  let tl_ge8 =
    ARM_STEPS_TAC exec (1--9) THEN
    SUBGOAL_THEN `val(word_add sp (word 64):int64) = val sp + 64` ASSUME_TAC THENL
       [MATCH_MP_TAC SPONGE2_VAL_ADD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add sp (word 64):int64) + r <= val(d:int64) \/ val d + r <= val(word_add sp (word 64):int64)` ASSUME_TAC THENL
       [MATCH_MP_TAC SPONGE2_NOOV_DISJ THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add sp (word 64):int64`; `d:int64`; `r:num`] SPONGE2_NOOV_CF) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
    DISCH_THEN(fun cf -> RULE_ASSUM_TAC(REWRITE_RULE[cf])) THEN
    ARM_STEPS_TAC exec (10--10) in

  let sp2_spec_hyp name newname args =
    USE_THEN name (fun th ->
      let e0 = `e0:(uarch_event)list` in
      LABEL_TAC newname
        (GEN e0 (SPONGE2_NORMADDR_ALL (SPONGE2_SIMP (SPECL (e0::args) th))))) in

  let sp2_norm_reg r s = RULE_ASSUM_TAC(fun th ->
    if (try string_of_term(lhs(concl th)) = "read "^r^" "^s with _ -> false) then SPONGE2_NORMADDR th else th) in

  (*** A call of the loop over bytes from byte j0 on, after r was split ***)
  
  let sp2_zero_mem sname =
    SUBGOAL_THEN (subst [mk_var(sname,`:armstate`),`s:armstate`]
      `read (memory :> bytes (word_add sp (word 64),0)) (s:armstate) = val (word_xor S1 (word R):1600 word) MOD 1`) ASSUME_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MOD_1]; ALL_TAC] in

  (*** 8 <= r < 32 ***)
  
  let tl_lt32_a =
    SUBGOAL_THEN `~(32 <= r)` ASSUME_TAC THENL [tl_ar [`r < 32`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (11--19) THEN
    sp2_spec_hyp "H_D" "H_D0" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `0`; `r DIV 8`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_zero_mem "s19" THEN
    SUBGOAL_THEN `0 < r DIV 8` ASSUME_TAC THENL [tl_ar [`~(r < 8)`]; ALL_TAC] THEN
    SUBGOAL_THEN `8 * r DIV 8 <= r` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r <= 200` ASSUME_TAC THENL [tl_ar [`r < 136`]; ALL_TAC] THEN
    sp2_callp "H_D0" 20 in

  let tl_lt32_b0 =
    SUBGOAL_THEN `8 * r DIV 8 = r` ASSUME_TAC THENL [tl_ar [`r MOD 8 = 0`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (21--22) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * r DIV 8 = r`]) THEN sp2_end "s22" in

  let tl_lt32_b1 =
    SUBGOAL_THEN `8 * r DIV 8 < r` ASSUME_TAC THENL [tl_ar [`~(r MOD 8 = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `~(r <= 8 * r DIV 8)` ASSUME_TAC THENL [tl_ar [`~(r MOD 8 = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word r:int64) (word (8 * r DIV 8)) = word (r - 8 * r DIV 8)` ASSUME_TAC THENL
     [MATCH_MP_TAC SPONGE2_WSUB THEN CONJ_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word (r - 8 * r DIV 8):int64) = r - 8 * r DIV 8` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN tl_ar [`r < 136`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (21--27) THEN
    SPONGE2_SPEC_HYP "H_PTR" "H_PTR1" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `8 * (r DIV 8)`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_norm_reg "X10" "s27" THEN
    sp2_callp "H_PTR1" 28 THEN
    sp2_end "s28" in

  let tl_lt32 = tl_lt32_a THEN ASM_CASES_TAC `r MOD 8 = 0` THENL [tl_lt32_b0; tl_lt32_b1] in

  let tl_facts2 =
    SUBGOAL_THEN `val(word (8 * (r DIV 8) MOD 4):int64) = 8 * (r DIV 8) MOD 4` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
    ASSUME_TAC(CONJUNCT2(SPEC `r:num` TL_MOD4)) in

  let sp2_rw name th = REMOVE_THEN name (fun h -> LABEL_TAC name (REWRITE_RULE[th] h)) in

  (*** r >= 32: 32 bytes at a time, then 8, then 1 ***)
  
  let tl_ge32_a =
    SUBGOAL_THEN `32 <= r` ASSUME_TAC THENL [tl_ar [`~(r < 32)`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (11--17) THEN
    sp2_norm_reg "X10" "s17" THEN
    SPONGE2_SPEC_HYP "H_Q" "H_Q0" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `0`; `r DIV 32`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_zero_mem "s17" THEN
    SUBGOAL_THEN `0 < r DIV 32` ASSUME_TAC THENL [tl_ar [`32 <= r`]; ALL_TAC] THEN
    SUBGOAL_THEN `32 * r DIV 32 <= r` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r <= 200` ASSUME_TAC THENL [tl_ar [`r < 136`]; ALL_TAC] THEN
    sp2_callp "H_Q0" 18 in

  let tl_ge32_b0 =
    SUBGOAL_THEN `32 * r DIV 32 = r` ASSUME_TAC THENL [tl_ar [`r MOD 32 = 0`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (19--20) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `32 * r DIV 32 = r`]) THEN sp2_end "s20" in

  (*** The facts that the comparison of r with the part that is done needs ***)
  
  let tl_cmp_facts q h =
    let t s =
      let rec go i acc =
        if i >= String.length s then acc
        else if i + 1 < String.length s && s.[i] = '%' && s.[i+1] = 's' then go (i+2) (acc ^ q)
        else go (i+1) (acc ^ String.make 1 s.[i]) in
      parse_term(go 0 "") in
    SUBGOAL_THEN (t "%s < r") ASSUME_TAC THENL [tl_ar [h]; ALL_TAC] THEN
    SUBGOAL_THEN (t "~(r <= %s)") ASSUME_TAC THENL [tl_ar [h]; ALL_TAC] THEN
    SUBGOAL_THEN (t "word_sub (word r:int64) (word (%s)) = word (r - %s)") ASSUME_TAC THENL
     [MATCH_MP_TAC SPONGE2_WSUB THEN CONJ_TAC THEN tl_ar [h]; ALL_TAC] THEN
    SUBGOAL_THEN (t "val(word (r - %s):int64) = r - %s") ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN tl_ar [`r < 136`]; ALL_TAC] in

  let tl_modfact_arith = MP_TAC(CONJUNCT1(SPEC `r:num` TL_MOD4)) THEN ASM_REWRITE_TAC[] in

  let tl_ge32_c0 =
    SUBGOAL_THEN `8 * (r DIV 8) MOD 4 = 0` ASSUME_TAC THENL [tl_modfact_arith; ALL_TAC] THEN
    tl_cmp_facts "32 * r DIV 32" `~(r MOD 32 = 0)` THEN
    ARM_STEPS_TAC exec (19--25) THEN
    SPONGE2_SPEC_HYP "H_PTR" "H_PTR1" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `32 * (r DIV 32)`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_norm_reg "X10" "s25" THEN
    sp2_callp "H_PTR1" 26 THEN
    sp2_end "s26" in

  let tl_ge32_c1 =
    SUBGOAL_THEN `~(8 * (r DIV 8) MOD 4 = 0)` ASSUME_TAC THENL [tl_modfact_arith; ALL_TAC] THEN
    tl_cmp_facts "32 * r DIV 32" `~(r MOD 32 = 0)` THEN
    ARM_STEPS_TAC exec (19--27) THEN
    SPONGE2_SPEC_HYP "H_D" "H_D1" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `32 * (r DIV 32)`; `(r DIV 8) MOD 4`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_rw "H_D1" (ASSUME `32 * r DIV 32 + 8 * (r DIV 8) MOD 4 = 8 * r DIV 8`) THEN
    sp2_norm_reg "X10" "s27" THEN
    SUBGOAL_THEN `0 < (r DIV 8) MOD 4` ASSUME_TAC THENL [tl_ar [`~(8 * (r DIV 8) MOD 4 = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `8 * r DIV 8 <= r` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r <= 200` ASSUME_TAC THENL [tl_ar [`r < 136`]; ALL_TAC] THEN
    sp2_callp "H_D1" 28 in

  let tl_ge32_d0 =
    SUBGOAL_THEN `8 * r DIV 8 = r` ASSUME_TAC THENL [tl_ar [`r MOD 8 = 0`]; ALL_TAC] THEN
    ARM_STEPS_TAC exec (29--30) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * r DIV 8 = r`]) THEN sp2_end "s30" in

  let tl_ge32_d1 =
    tl_cmp_facts "8 * r DIV 8" `~(r MOD 8 = 0)` THEN
    ARM_STEPS_TAC exec (29--35) THEN
    SPONGE2_SPEC_HYP "H_PTR" "H_PTR2" [`word_add sp (word 64):int64`; `d:int64`; `0`; `r:num`; `8 * (r DIV 8)`; `S1:1600 word`; `R:num`; `pc:num`] THEN
    sp2_norm_reg "X10" "s35" THEN
    sp2_callp "H_PTR2" 36 THEN
    sp2_end "s36" in

  let tl_ge32 =
    tl_ge32_a THEN tl_facts2 THEN ASM_CASES_TAC `r MOD 32 = 0` THENL
     [tl_ge32_b0;
      ASM_CASES_TAC `r MOD 32 < 8` THENL
       [tl_ge32_c0;
        tl_ge32_c1 THEN ASM_CASES_TAC `r MOD 8 = 0` THENL [tl_ge32_d0; tl_ge32_d1]]] in

  prove(SPONGE2_TAIL_STMT fn pr lr,
    sp2_tail_setup THEN tl_facts THEN ASM_CASES_TAC `r = 0` THENL
     [tl_r0;
      ASM_CASES_TAC `r < 8` THENL
       [tl_lt8; tl_ge8 THEN ASM_CASES_TAC `r < 32` THENL [tl_lt32; tl_ge32]]]);;


(* ------------------------------------------------------------------------- *)
(* The absorbing of a message of mlen bytes from the head of the code that    *)
(* tests mlen < 136 to the padding, from the zero state at sp + 64: the loop *)
(* over the blocks of 136 bytes (if mlen >= 136), then the XOR of the rest.   *)
(* The state is that of mld_keccak_absorb, and the length that is left, r =   *)
(* mlen MOD 136, and the pointer past the full blocks are in the registers.   *)
(* It is made from the lemmas L1 (PROVE_SPONGE2_L1) and TAIL                  *)
(* (PROVE_SPONGE3_TAIL) for the function.                                     *)
(* ------------------------------------------------------------------------- *)

let SPONGE3_ABS_STMT fn pr lr = parse_term(Printf.sprintf
 "exists f_events. forall e d mlen M sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ val sp + 464 < 2 EXP 63 /\\ mlen < 2 EXP 64 /\\
   nonoverlapping (d,mlen) (word_sub sp (word 240),504) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),504)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read PC s = word (pc + %s_in_shake256_absorb_part2) /\\
          read SP s = sp /\\
          read %s s = d /\\ read %s s = word mlen /\\
          (read CF s <=> 136 <= mlen) /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes (word_add sp (word 64))) s = (word 0:1600 word) /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s_join4) /\\ read SP s = sp /\\
          read %s s = word_add d (word (136 * (mlen DIV 136))) /\\
          read %s s = word (mlen MOD 136) /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes (word_add sp (word 64))) s =
            FST(mld_keccak_absorb 136 (word 0) 0 mlen M) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d mlen sp pc /\\
             memaccess_inbounds e2
              [d,mlen; word_add sp (word 64),200; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add sp (word 64),200; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add sp (word 64),200);
                memory :> bytes(word_sub sp (word 240),240)])"
  fn pr lr fn pr lr pr lr);;


(*** The state of mld_keccak_absorb in terms of the blocks and the rest ***)

let SPONGE3_ABSORB_FST = prove
 (`!mlen M.
        M < 2 EXP (8 * mlen)
        ==> FST(mld_keccak_absorb 136 (word 0) 0 mlen M) =
            word_xor (mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136))
                     (word ((M DIV 2 EXP (8 * 136 * (mlen DIV 136))) MOD
                            2 EXP (8 * (mlen MOD 136))):1600 word)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(M DIV 2 EXP (8 * 136 * (mlen DIV 136))) < 2 EXP (8 * (mlen MOD 136))` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP (8 * mlen)` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(M DIV 2 EXP (8 * 136 * (mlen DIV 136))) MOD 2 EXP (8 * (mlen MOD 136)) = M DIV 2 EXP (8 * 136 * (mlen DIV 136))` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP (8 * (mlen MOD 136))` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC);;

let SPONGE3_ABS_TAC fn pr lr l1th tailth =
  let exec = SPONGE2_L1_EXEC fn in
  let mc = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc in
  let abs_fst_fact =
    MP_TAC(SPECL [`mlen:num`; `M:num`] SPONGE3_ABSORB_FST) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] in
  (*** mlen < 136: only the XOR of the message into the state ***)
  let abs_c1 =
    SUBGOAL_THEN `~(136 <= mlen)` ASSUME_TAC THENL [UNDISCH_TAC `mlen < 136` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC exec (1--1) THEN
    SPONGE2_SPEC_HYP "H_TAIL" "H_T0" [`d:int64`; `mlen:num`; `M:num`; `word 0:1600 word`; `sp:int64`; `pc:num`] THEN
    FULL_CALL_TAC mc exec "H_T0" [] [`d:int64`; `mlen:num`; `sp:int64`; `pc:num`] 2 THEN
    abs_fst_fact THEN
    SUBGOAL_THEN `mlen DIV 136 = 0 /\ mlen MOD 136 = mlen` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; mld_keccak_absorb_blocks; EXP; DIV_1; WORD_XOR_0] THEN
           ASM_SIMP_TAC[MOD_LT; WORD_VAL; WORD_XOR_0; ARITH_RULE `8 * 0 = 0`] THEN NO_TAC;
           MONOTONE_MAYCHANGE_TAC;
           DISCHARGE_SAFETY_PROPERTY_TAC] in
  (*** mlen >= 136: the loop over the blocks, then the XOR of the rest ***)
  let abs_c2 =
    SUBGOAL_THEN `136 <= mlen` ASSUME_TAC THENL [UNDISCH_TAC `~(mlen < 136)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `0 < mlen DIV 136` ASSUME_TAC THENL [UNDISCH_TAC `136 <= mlen` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC exec (1--1) THEN
    SPONGE2_SPEC_HYP "H_L1" "H_L10" [`d:int64`; `mlen:num`; `M:num`; `mlen DIV 136`; `word 0:1600 word`; `sp:int64`; `pc:num`] THEN
    FULL_CALL_TAC mc exec "H_L10" [] [`d:int64`; `mlen:num`; `sp:int64`; `pc:num`] 2 THEN
    SUBGOAL_THEN `mlen - 136 * (mlen DIV 136) < 136` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add d (word (136 * (mlen DIV 136))), mlen - 136 * (mlen DIV 136))) (s2:armstate) =
                  (M DIV 2 EXP (8 * (136 * (mlen DIV 136)))) MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136)))` ASSUME_TAC THENL
     [MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `mlen:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SPONGE2_SPEC_HYP "H_TAIL" "H_T0" [`word_add d (word (136 * (mlen DIV 136))):int64`; `mlen - 136 * (mlen DIV 136)`; `(M DIV 2 EXP (8 * (136 * (mlen DIV 136)))) MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136)))`; `mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136)`; `sp:int64`; `pc:num`] THEN
    FULL_CALL_TAC mc exec "H_T0" [] [`d:int64`; `mlen:num`; `sp:int64`; `pc:num`] 3 THEN
    abs_fst_fact THEN
    SUBGOAL_THEN `mlen MOD 136 = mlen - 136 * (mlen DIV 136)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MONOTONE_MAYCHANGE_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 l1th) "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 tailth) "H_TAIL" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(d:int64) (mlen:num) (sp:int64) (pc:num).
      if mlen < 136 then f_ev_a d mlen sp pc else f_ev_b d mlen sp pc
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `mlen:num`; `M:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes(d,mlen)) (s0:armstate) = M`
    then ASSUME_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC) THEN
  ASM_CASES_TAC `mlen < 136` THENL [abs_c1; abs_c2];;

let PROVE_SPONGE3_ABS fn pr lr l1th tailth =
  prove(SPONGE3_ABS_STMT fn pr lr, SPONGE3_ABS_TAC fn pr lr l1th tailth);;

(* ------------------------------------------------------------------------- *)
(* The zero state of the sponge in memory: the 200 bytes at a are zero if the *)
(* 12 chunks of 16 bytes at a are and the 8 bytes at a + 192 are, as the     *)
(* stores of zero vectors of the prologue leave them.                        *)
(* ------------------------------------------------------------------------- *)

let SPONGE3_ZERO_STATE = prove
 (`!(a:int64) (s:armstate).
      (!j. j < 12 ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s = word 0) /\
      read (memory :> bytes(word_add a (word 192),8)) s = 0
      ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  MP_TAC(SPECL [`a:int64`; `12`; `0`; `s:armstate`] SPONGE2_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16 * 12 = 192`; MOD_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `200 = 192 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(*** The bytes of a stored word of 32 bits as a number ***)

let READ_MEMORY_BYTES_OF_WORD32 = prove
 (`!a:int64 (w:int32) s:armstate.
        read (memory :> bytes32 a) s = w
        ==> read (memory :> bytes(a,4)) s = val w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
