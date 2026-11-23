(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of mlkem_gen_matrix  *)
(* (arm/mlkem_native/asm/mlkem_gen_matrix.S): its events depend on rho,      *)
(* through the rejection sampling, so the proofs follow the lanes of the     *)
(* matrix as the correctness proofs do, with the theorems that are           *)
(* correctness and safety in one ("FULL") for the Keccak permutations and    *)
(* the sampling, and only the safety of the rest                             *)
(* (the hash jobs and the noise), except for the digest of job 0 in          *)
(* decapsulation, H(ek), whose caller branches on it.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/asm/mlkem_gen_matrix.ml";;
needs "arm/proofs/utils/mlkem_native2_safety.ml";;
needs "arm/proofs/utils/mlkem_native2_keccak_full.ml";;
needs "arm/proofs/utils/mlkem_native2_rej_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The FULL theorem of mlkem_rej_uniform_alt_VARIABLE_TIME in the forms of   *)
(* the sampling of a matrix polynomial: from the three blocks in its buffer, *)
(* and from a further block in its lane.                                     *)
(* ------------------------------------------------------------------------- *)

let rej_full_post_tac =
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `wordlist_from_memory(a,n) s = l`) o concl)) THEN
  MATCH_ACCEPT_TAC WORDLIST_FROM_MEMORY_BYTES16_NUM;;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES = prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read (memory :> bytes(res,2 * val n)) s =
                num_of_wordlist curlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (C_RETURN s =
                 word(LENGTH(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist))))) /\
                 read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist)))))) s =
                 num_of_wordlist(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist))))) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL THEN
  EXISTS_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                int64->int64->(uarch_event)list` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
    (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_MLKEM_REJ_UNIFORM_TABLE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
                 `val(buflen:int64)`; `inlist:(12 word)list`]
    (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`;
                 `curlist:int16 list`]
    (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN rej_full_post_tac);;

let MLKEM_REJ_UNIFORM_BUF_OUT_FULL = prove
 (`exists f_events.
     forall e res buf table b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,504); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s =
                num_of_bytelist(list_of_seq (shake128 b) 504) /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (C_RETURN s = word(LENGTH(mlkem_rej_out b 3)) /\
                 read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b 3)))
                      s =
                 num_of_wordlist(mlkem_rej_out b 3)) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res buf table b pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,504; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word 0) buf (word 504) table
       (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 b) 504))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`; `word 0:int64`; `buf:int64`;
    `word 504:int64`; `table:int64`; `[]:int16 list`;
    `wordlist_of_num 336
       (num_of_bytelist(list_of_seq (shake128 b) 504)):(12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 504 = 12 * 336`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM MLKEM_REJ_OUT_BUF]);;

let MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL = prove
 (`exists f_events.
     forall e res buf table b m pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,168); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH(mlkem_rej_out b m)); buf;
                             word 168; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s =
                num_of_bytelist
                 (list_of_seq (\j. shake128 b (168 * m + j)) 168) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b m))) s =
                num_of_wordlist(mlkem_rej_out b m) /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (C_RETURN s = word(LENGTH(mlkem_rej_out b (m + 1))) /\
                 read (memory :>
                       bytes(res,2 * LENGTH(mlkem_rej_out b (m + 1)))) s =
                 num_of_wordlist(mlkem_rej_out b (m + 1))) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res buf table b m pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,168; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (m:num) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word(LENGTH(mlkem_rej_out b m))) buf (word 168) table
       (wordlist_of_num 112
          (num_of_bytelist
            (list_of_seq (\j. shake128 b (168 * m + j)) 168))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`;
    `word(LENGTH(mlkem_rej_out b m)):int64`; `buf:int64`;
    `word 168:int64`; `table:int64`; `mlkem_rej_out b m`;
    `wordlist_of_num 112
       (num_of_bytelist(list_of_seq (\j. shake128 b (168 * m + j)) 168)):
     (12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b m)):int64) =
                LENGTH(mlkem_rej_out b m)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`b:byte list`; `m:num`] LENGTH_MLKEM_REJ_OUT_LE) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH_MLKEM_REJ_OUT_LE] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 168 = 12 * 112`] THEN
  REWRITE_TAC[MLKEM_REJ_OUT_BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* The sampling of a matrix polynomial as one step, as in                    *)
(* MLKEM_GEN_MATRIX_SAMPLEPOLY, with its events a function of the seed b:    *)
(* those of the three blocks in the buffer and then of each further block,   *)
(* mlkem_rej_blocks b - 3 of them.                                           *)
(* ------------------------------------------------------------------------- *)

let gm_samplepoly_safe_tm =
  subst [mk_small_numeral(gm_pc "rejloop" 4),`pc0:num`;
         mk_small_numeral(gm_pc "rejloop" 116),`pc1:num`]
 `exists f_events.
   forall e b (A:1600 word) a c l ei stackpointer pc.
     mlkem_samplentt_terminates b /\
     (!t. num_of_bytelist(list_of_seq (\j. shake128 b (168 * t + j)) 168) =
          val(keccak_squeeze (t + 1) A) MOD 2 EXP 1344) /\
     l < 4 /\ ei < 16 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (stackpointer,3216))
         [(word pc,mlkem_native2_image_size);
          (word_add a (word(512 * ei)),512); (c,6656)] /\
     ALL (nonoverlapping (word_add a (word(512 * ei)),512))
         [(word pc,mlkem_native2_image_size); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + pc0) /\
               read SP s = word_add stackpointer (word 128) /\
               read X19 s = a /\ read X23 s = c /\
               read X27 s = word ei /\ read X28 s = word l /\
               read (memory :> bytes(word_add stackpointer
                                      (word(1024 + 504 * l)),504)) s =
               num_of_bytelist(list_of_seq (shake128 b) 504) /\
               read (memory :> bytes(word_add stackpointer
                                      (word(224 + 200 * l)),200)) s =
               val(keccak_squeeze 3 A) /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read events s = e)
          (\s. read PC s = word(pc + pc1) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events b a c l ei stackpointer pc /\
                  memaccess_inbounds e2
                   [word_add a (word(512 * ei)),512; c,6656;
                    stackpointer,3216]
                   [word_add a (word(512 * ei)),512; stackpointer,3216]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X30] ,,
           MAYCHANGE [memory :> bytes(word_add a (word(512 * ei)),512);
                      memory :> bytes(word_add stackpointer
                                       (word(224 + 200 * l)),200);
                      memory :> bytes(word_add stackpointer (word 3208),8);
                      memory :> bytes(stackpointer,128)])`;;

let gsp_vars = [`b:byte list`; `a:int64`; `c:int64`; `l:num`; `ei:num`;
                `stackpointer:int64`; `pc:num`];;

(*** A call in the sampling by its theorem with the label, at the new state
 *** k, the events in the variables vars
 ***)

let GM_SAFE_CALL_TAC vars label (off,mc) ilist k =
  NATIVE2_SAFE_THM_TAC MLKEM_GEN_MATRIX_EXEC vars label (off,mc) I ilist
    (k-1);;

let MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE = prove
 (gm_samplepoly_safe_tm,
  let sp_inv m = vsubst [`ei:num`,`e:num`] (samplepoly_inv m) in
  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`; WORD_ADD_0;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 504)) (word 896)):int64 =
              word_add stackpointer (word(1024 + 504 * l))`;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 200)) (word 96)):int64 =
              word_add stackpointer (word(224 + 200 * l))`;
      ASSUME `word_shl (word ei:int64) 9 = word(512 * ei)`]) in
  let REJ0_TAC =
    GM_SAFE_CALL_TAC gsp_vars "H_REJ0"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X2 s`; `read X4 s`;
      `b:byte list`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`;
      `read SP s`; `read X30 s`] 10 in
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BUF_OUT_FULL "H_REJ0" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL "H_REJ1" THEN
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_SUBROUTINE_FULL_F1600
    "H_K1" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(b:byte list) (a:int64) (c:int64) (l:num) (ei:num) (stackpointer:int64)
     (pc:num).
      if mlkem_rej_blocks b - 3 = 0
      then f_ev_skip b a c l ei stackpointer pc
      else APPEND (f_ev_exit b a c l ei stackpointer pc)
             (APPEND (ENUMERATEL (mlkem_rej_blocks b - 3)
                       (\i. f_ev_loop b a c l ei stackpointer pc i))
                     (f_ev_enter b a c l ei stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 504)) (word 896)):int64 =
    word_add stackpointer (word(1024 + 504 * l)) /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 200)) (word 96)):int64 =
    word_add stackpointer (word(224 + 200 * l)) /\
    word_shl (word ei:int64) 9 = word(512 * ei)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `l < 4` THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `mlkem_rej_blocks b - 3 = 0` THEN ASM_REWRITE_TAC[] THENL
   [(*** No more blocks: the three in the buffer suffice ***)
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `mlkem_rej_blocks b = 3` (SUBST1_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `mlkem_rej_blocks b - 3`
   (gm_pc_tm(gm_pc "rejloop" 48)) (gm_pc_tm(gm_pc "rejloop" 116))
   (mk_abs(`i:num`,sp_inv `3 + i`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The buffer, and the test the first time ***)

    REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b 3)):int64) =
                  LENGTH(mlkem_rej_out b 3)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ENUMERATEL; APPEND; GSYM NOT_LT] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: another block from the lane, its fields, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * ei)),
                      2 * LENGTH(mlkem_rej_out b (3 + i)))
                     (stackpointer:int64,3216)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(256 <= LENGTH(mlkem_rej_out b ((3 + i) + 1)) <=>
       ~(i + 1 < mlkem_rej_blocks b - 3)) /\
      val(word(LENGTH(mlkem_rej_out b ((3 + i) + 1))):int64) =
      LENGTH(mlkem_rej_out b ((3 + i) + 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `i + 1 < mlkem_rej_blocks b - 3` THEN
        ASM_REWRITE_TAC[NOT_LE] THENL
         [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          SUBGOAL_THEN `(3 + i) + 1 = mlkem_rej_blocks b` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]] THEN
          ARITH_TAC];
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        MP_TAC(SPECL [`b:byte list`; `(3 + i) + 1`]
                     LENGTH_MLKEM_REJ_OUT_LE) THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--7) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(224 + 200 * l)):int64` 7 THEN
    RC_TAC `c:int64` 7 THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_K1"
     (layout "sha3_keccak_f1600",sha3_keccak_f1600_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
      `keccak_squeeze (3 + i) (A:1600 word)`;
      `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 8 THEN
    FROM_WBYTES_TAC 8 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (9--17) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(224 + 200 * l)),
                            168)) s17 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + i) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(224 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + i)
                                       (A:1600 word)))`;
                    `s17:armstate`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_REJ1"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X2 s`; `read X4 s`;
      `b:byte list`; `3 + i`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`;
      `read SP s`; `read X30 s`] 18 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (19--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + i + 1 = (3 + i) + 1`] THEN
    ASM_REWRITE_TAC[COND_SWAP] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (fun gl -> allowed_vars_e := `i:num` :: !allowed_vars_e; ALL_TAC gl) THEN
    REWRITE_TAC[GSYM ADD1; ENUMERATEL] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit ***)

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One block of a hash job absorbed into its lane, with the events depending *)
(* only on the addresses and the lengths: a whole block, or the last t bytes *)
(* and the padding.                                                          *)
(* ------------------------------------------------------------------------- *)

let gm_absorb_full_safe_tm j ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 8 + 120 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 120),`pc1:num`;
         ns ds,`ds:num`]
  `exists f_events.
   forall e n inp i sp pc.
    n < 2 EXP 63 /\ 136 * (i + 1) <= n /\
    ALL (nonoverlapping (word_add sp (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    ALL (nonoverlapping (word_add sp (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    nonoverlapping (word_add sp (word lane),200) (word_add sp (word st),24)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + pc0) /\
          read SP s = sp /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * i)) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word(n - 136 * i) /\
          read (memory :> bytes64(word_add sp (word st16))) s = word ds /\
          read events s = e)
     (\s. read PC s = word(pc + pc1) /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * (i + 1))) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word(n - 136 * (i + 1)) /\
          (exists e2.
             read events s = APPEND e2 e /\
             e2 = f_events inp i sp pc /\
             memaccess_inbounds e2
              [inp,n; word_add sp (word lane),200; word_add sp (word st),24]
              [word_add sp (word lane),200; word_add sp (word st),16]))
     (MAYCHANGE [PC; X2; X3; X8; X9; X10; X11; X12; X13; X14; X15] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add sp (word st),16);
                 memory :> bytes(word_add sp (word lane),200)])`;;

let GM_ABSORB_FULL_SAFE_PROOF_TAC =
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word(n - 136 * i):int64) = n - 136 * i /\
    ~bit 63 (word(n - 136 * i):int64) /\
    ~(n - 136 * i < 136) /\
    136 <= n - 136 * i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r /\ t ==> p /\ q /\ r /\ t`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `n < 2 EXP 63` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[DIV_LT; ARITH_RULE `x < 2 EXP 63 ==> x - y < 2 EXP 63`;
               ASSUME `n < 2 EXP 63`] THEN
      CONV_TAC NUM_REDUCE_CONV;
      UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC;
      UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [ASSUME `~(n - 136 * i < 136)`]) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (10--115) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [ASSUME `136 <= n - 136 * i`]) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (116--117) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `n - 136 * i = (n - 136 * (i + 1)) + 136` SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let gm_absorb_last_safe_tm j t ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 8 + 120 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 120),`pc1:num`;
         ns t,`t:num`; ns ds,`ds:num`]
  `exists f_events.
   forall e n inp q sp pc.
    n = 136 * q + t /\ n < 2 EXP 63 /\
    ALL (nonoverlapping (word_add sp (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    ALL (nonoverlapping (word_add sp (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    nonoverlapping (word_add sp (word lane),200) (word_add sp (word st),24)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + pc0) /\
          read SP s = sp /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * q)) /\
          read (memory :> bytes64(word_add sp (word st8))) s = word t /\
          read (memory :> bytes64(word_add sp (word st16))) s = word ds /\
          read events s = e)
     (\s. read PC s = word(pc + pc1) /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * q + t)) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word 18446744073709551615 /\
          (exists e2.
             read events s = APPEND e2 e /\
             e2 = f_events inp q sp pc /\
             memaccess_inbounds e2
              [inp,n; word_add sp (word lane),200; word_add sp (word st),24]
              [word_add sp (word lane),200; word_add sp (word st),16]))
     (MAYCHANGE [PC; X2; X3; X8; X9; X10; X11; X12; X13; X14; X15] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add sp (word st),16);
                 memory :> bytes(word_add sp (word lane),200)])`;;

let GM_ABSORB_LAST_SAFE_PROOF_TAC t =
  let nsteps = 13 + 6 * (t / 8) + 9 in
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the Keccak state at the end, as in GM_ZERO_END, with its   *)
(* events.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The zeroing of len bytes at stackpointer + off with stp xzr, xzr and
 *** a count in X1, from start (two setup instructions) to stop
 ***)

let gm_zero_safe_tm start stop off len =
  let ns = mk_small_numeral in
  vsubst [ns start,`start:num`; ns stop,`stop:num`; ns off,`off:num`;
          ns len,`len:num`]
  `exists f_events.
     forall e stackpointer pc.
       nonoverlapping (word_add stackpointer (word off),len)
                      (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + start) /\
                 read SP s = stackpointer /\
                 read events s = e)
            (\s. read PC s = word(pc + stop) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [word_add stackpointer (word off),len]
                     [word_add stackpointer (word off),len]))
            (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(word_add stackpointer (word off),
                                        len)])`;;

let GM_ZERO_SAFE_TAC exec start stop off len =
  let n = len / 16 and ns = mk_small_numeral in
  let inv = vsubst [ns off,`off:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add stackpointer (word(off + 16 * i)) /\
          read X1 s = word(len - 16 * i)` in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  CONCRETIZE_F_EVENTS_TAC
   (vsubst [ns n,`n:num`]
     `\(stackpointer:int64) (pc:num).
        APPEND (f_ev_epil stackpointer pc)
               (APPEND (ENUMERATEL n (\i. f_ev_loop stackpointer pc i))
                       (f_ev_prol stackpointer pc)) :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (ns n) (pcp (start + 8)) (pcp stop) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns len,`len:num`]
     `word_sub (word(len - 16 * i)) (word 16):int64 =
      word(len - 16 * (i + 1)) /\
      val(word(len - 16 * (i + 1)):int64) = len - 16 * (i + 1)`)
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns len)
                         `16 * i`; `16`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
          vsubst [ns len,`len:num`] `16 <= len - 16 * i`))] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--3) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE(vsubst [ns len,`len:num`; ns n,`n:num`]
        `16 * (i + 1) < len <=> i + 1 < n`)] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let GM_ZERO_END_SAFE = prove
 (gm_zero_safe_tm (gm_pc "end" 0) (gm_pc "end" 20) 96 800,
  GM_ZERO_SAFE_TAC MLKEM_GEN_MATRIX_EXEC (gm_pc "end" 0) (gm_pc "end" 20)
    96 800);;

(* ------------------------------------------------------------------------- *)
(* The instances of the absorb lemmas for the jobs of the API.               *)
(* ------------------------------------------------------------------------- *)

(*** The instances of the absorb lemmas for the jobs of the API ***)

let gm_absorb_full_safe_ths =
  map (fun (j,ds) ->
         (j,ds),prove(gm_absorb_full_safe_tm j ds,
                      GM_ABSORB_FULL_SAFE_PROOF_TAC))
      [0,6; 1,6; 1,31];;

let gm_absorb_last_safe_ths =
  map (fun (j,t,ds) ->
         (j,t),prove(gm_absorb_last_safe_tm j t ds,
                     GM_ABSORB_LAST_SAFE_PROOF_TAC t))
      [0,120,6; 1,120,31; 0,96,6; 1,96,6; 1,32,31; 0,72,6; 1,72,6;
       1,104,31];;

let gm_af_label j ds = "H_AF_"^string_of_int j^"_"^string_of_int ds;;
let gm_al_label j t = "H_AL_"^string_of_int j^"_"^string_of_int t;;

(* ------------------------------------------------------------------------- *)
(* For the configurations of decapsulation, the absorbing of job 0 (ek, for  *)
(* H(ek)) with its result and its events: the absorb lemmas of the           *)
(* correctness proof in FULL form.                                           *)
(* ------------------------------------------------------------------------- *)

(*** The absorb lemmas of job j in FULL form ***)

let gm_absorb_full_full_tm j ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j in
  let ns = mk_small_numeral in
  let la = vsubst [ns lane,`n:num`] `word_add (sp:int64) (word n)`
  and sa = vsubst [ns st,`n:num`] `word_add (sp:int64) (word n)` in
  full_tm_of (gm_absorb_full_tm j ds)
   [`inp:int64`; `i:num`; `sp:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; mk_pair(la,`200`); mk_pair(sa,`24`)]
   [mk_pair(la,`200`); mk_pair(sa,`16`)];;

let gm_absorb_last_full_tm j t ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j in
  let ns = mk_small_numeral in
  let la = vsubst [ns lane,`n:num`] `word_add (sp:int64) (word n)`
  and sa = vsubst [ns st,`n:num`] `word_add (sp:int64) (word n)` in
  full_tm_of (gm_absorb_last_tm j t ds)
   [`inp:int64`; `q:num`; `sp:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; mk_pair(la,`200`); mk_pair(sa,`24`)]
   [mk_pair(la,`200`); mk_pair(sa,`16`)];;

let GM_ABSORB_FULL_FULL_PROOF_TAC j ds =
  META_EXISTS_TAC THEN
  GM_ABSORB_FULL_TAC (496 + 200 * j) ds THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    SUBGOAL_THEN
     `LENGTH(m:byte list) - 136 * i = (LENGTH m - 136 * (i + 1)) + 136`
    SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    SUBGOAL_THEN (subst [mk_small_numeral ds,`ds:num`]
     `(keccak_padded 136 ds m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136) =
      B`)
    SUBST1_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[keccak_padded] THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `B:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let GM_ABSORB_LAST_FULL_PROOF_TAC j t ds =
  let w = t / 8 in
  let lanetm = mk_comb(`word_add (sp:int64)`,
                       mk_comb(`word:num->int64`,
                               mk_small_numeral(496 + 200 * j))) in
  let nsteps1 = 13 + 6 * w in
  let tn = mk_small_numeral t and wn = mk_small_numeral w
  and dsn = mk_small_numeral ds in
  let xor_ds = BYTE_XOR_CONST_ZX_RULE ds
  and xor_80 = BYTE_XOR_CONST_ZX_RULE 128 in
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (subst [dsn,`ds:num`]
   `A = keccak_absorb 136 (keccak_padded 136 ds m) q`) THEN
  ABBREV_TAC (subst [tn,`t:num`]
   `L = (num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * t)`) THEN

  (*** The lanes of the state after the last words are XORed in ***)

  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word L)) (64 * j,64):int64 =
            if j < w
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (136 * q + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `L:num`; wn; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) DIV_MOD_EXP_LOW o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the message ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] o
    check (can (term_match [`sp:int64`]
      (subst [lanetm,`l:int64`]
        `read (memory :> bytes(l,200)) s = val(A:1600 word)`)) o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < w
        ==> read (memory :> bytes64(word_add inp (word(136 * q + 8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (136 * q + 8 * j))) MOD
                 2 EXP 64)`)
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC] THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (term_match [`inp:int64`]
            `read (memory :> bytes64 (word_add inp (word(n + k)))) s =
             (y:int64)`) (concl th)) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN

  (*** The XOR of the last words into the lane ***)

  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps1) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; mk_var("s"^string_of_int nsteps1,`:armstate`),
           `s:armstate`]
    `read (memory :> wbytes l) s = word_xor (A:1600 word) (word L)`)
  MP_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `L:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The domain byte at byte t ***)

  REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC tn th) (ARITH_RULE(subst [tn,`t:num`] `t < 200`)))) THEN
    ASSUME_TAC(RESTRICT_RULE tn th)) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+1)--(nsteps1+3)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[xor_ds]) THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(496 + 200 * j),`l:num`;
           mk_var("s"^string_of_int(nsteps1+3),`:armstate`),
           `s:armstate`; tn,`t:num`; dsn,`ds:num`]
    `!j. j < 200
         ==> read (memory :> bytes8(word_add sp (word(l + j)))) s =
             word_subword (word_xor (word_xor (A:1600 word) (word L))
                                    (word(2 EXP (8 * t) * ds))) (8 * j,8)`)
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE(subst [dsn,`ds:num`] `ds < 256`);
                 ARITH_RULE(subst [tn,`t:num`] `t < 200`)] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The final bit at byte 135 ***)

  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `135` th) (ARITH_RULE `135 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `135` th)) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+4)--(nsteps1+6)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[xor_80]) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; mk_var("s"^string_of_int(nsteps1+6),`:armstate`),
           `s:armstate`; tn,`t:num`; dsn,`ds:num`]
    `read (memory :> bytes(l,200)) s =
     val(word_xor (word_xor (word_xor (A:1600 word) (word L))
                            (word(2 EXP (8 * t) * ds)))
                  (word(2 EXP (8 * 135) * 128)))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 135 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+7)--(nsteps1+9)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`136`; dsn; `m:byte list`] KECCAK_LAST_BLOCK_XOR) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN (subst [tn,`t:num`]
   `(136 * q + t) DIV 136 = q /\ (136 * q + t) MOD 136 = t`)
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC tn THEN ARITH_TAC;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `num_of_bytelist m DIV 2 EXP (8 * 136 * q) = L` SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    MP_TAC(ISPEC `m:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
    MATCH_MP_TAC(ARITH_RULE `a = b ==> x < a ==> x < b`) THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

let gm_absorb_full_full_ths =
  map (fun (j,ds) ->
         (j,ds),GM_BLOCK_RULE(prove(gm_absorb_full_full_tm j ds,
                                    GM_ABSORB_FULL_FULL_PROOF_TAC j ds)))
      [0,6];;

let gm_absorb_last_full_ths =
  map (fun (j,t,ds) ->
         (j,t),GM_BLOCK_RULE(prove(gm_absorb_last_full_tm j t ds,
                                   GM_ABSORB_LAST_FULL_PROOF_TAC j t ds)))
      [0,120,6; 0,96,6; 0,72,6];;

(* ------------------------------------------------------------------------- *)
(* The calls: the x4 permutation by its FULL theorem (the lanes of the hash  *)
(* jobs and the noise, whose states are not followed, as ghosts), the        *)
(* sampling of a matrix polynomial, a block of a hash job (job 0 of          *)
(* decapsulation in FULL form), mlkem_getnoise.                              *)
(* ------------------------------------------------------------------------- *)

(*** The calls. A safety theorem is taken from the assumptions by its label
 *** and put back afterwards; for the x4 permutation (a FULL theorem) the
 *** lanes with no known state, those of the hash jobs and the noise, are
 *** given ghost states.
 ***)

let lane_state_opt a k gl =
  try let r = rand(concl(bytes_fact a 200 k gl)) in
      let f,x = dest_comb r in
      if name_of f = "val" && type_of x = `:1600 word` then Some x else None
  with Failure _ -> None;;

let GM_SAFE_SIM_TAC vars label th' th k gl =
  let vs = vars @ fev_vars gl in
  (ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
    (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,0,mlkem_native2_image_mc,
     FRESH_TAIL_RULE th') [] (k+1) THENL
   [EXISTS_E2_TAC (ref vs); LABEL_TAC label th]) gl;;

let GM_K4_SAFE_CALL_TAC vars k (asl,w as gl) =
  let a = find_read_fact `X0` k gl and rc = find_read_fact `X1` k gl in
  let sv = state_of k in
  let ads = map (addr_plus a) [0;200;400;600] in
  let lane i ad =
    match lane_state_opt ad k gl with
      Some x -> TO_WBYTES_TAC ad k,x
    | None ->
        let g = mk_var("ghost"^string_of_int k^"_"^string_of_int i,
                       `:1600 word`) in
        ABBREV_TAC(mk_eq(g,vsubst [ad,`a:int64`; sv,`s:armstate`]
                             `read (memory :> wbytes a) s:1600 word`)),g in
  let ls = map2 lane (0--3) ads in
  (RC_TAC rc k THEN EVERY (map fst ls) THEN
   GM_SAFE_CALL_TAC vars "H_K4"
    (layout "sha3_keccak4_f1600_alt2",sha3_keccak4_f1600_alt2_mc)
    ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`] @ map snd ls @
     [`pc + sha3_keccak4_f1600_alt2`; `read SP s`; `read X30 s`]) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let GM_SAMPLEPOLY_SAFE_TAC vars spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `X28` k gl))
  and ei = dest_small_numeral(rand(find_read_fact `X27` k gl)) in
  let lane = gm_lane_addr spoff l and buf = gm_buf_addr spoff l in
  let sv = state_of k in
  let st = rand(rand(concl(bytes_fact lane 200 k gl))) in
  let aa = rand(rand(rand st)) in
  let y = rand aa and x = rand(rator aa) and rho = rand(rator(rator aa)) in
  let b = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,rho),
                  mk_list([x;y],`:byte`)) in
  let bufth = MP_TAC(SPECL [rho; x; y; buf; sv] MLKEM_MATRIX_BUFFER) THEN
              CONV_TAC(LAND_CONV(KECCAK_SQUEEZE_NUM_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
              ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let spth = SPECL [rho; x; y] MLKEM_MATRIX_SPONGE_BLOCK in
  let tth = find_asm (fun c ->
    let vs,bod = strip_forall c in
    length vs = 2 && type_of(hd vs) = `:num` && is_imp bod &&
    can (find_term (fun t -> is_const t &&
                     name_of t = "mlkem_samplentt_terminates")) (rand bod))
    gl in
  let xn = dest_small_numeral(rand x) and yn = dest_small_numeral(rand y) in
  let term_th =
    let try_ij i j =
      let th = SPECL [mk_small_numeral i; mk_small_numeral j] tth in
      let th' = MP th (EQT_ELIM((NUM_REDUCE_CONV THENC REWRITE_CONV[])
                                   (lhand(concl th)))) in
      if rand(concl th') = b then th' else failwith "order" in
    try try_ij yn xn with Failure _ -> try_ij xn yn in
  (ASSUME_TAC term_th THEN bufth THEN
   MP_TAC spth THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   REMOVE_THEN "H_SP" (fun th ->
     let lemma = SPECL [`e:(uarch_event)list`; b; aa; `a:int64`; `c:int64`;
                        mk_small_numeral l; mk_small_numeral ei;
                        addr_plus `stackpointer:int64` (spoff - 128);
                        `pc:num`] th in
     let lemma' = CONV_RULE(ONCE_DEPTH_CONV KECCAK_SQUEEZE_NUM_CONV) lemma in
     MP_TAC lemma' THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[] THEN
     DISCH_THEN(fun th' -> GM_SAFE_SIM_TAC vars "H_SP" th' th k))) gl;;

let GM_ABSORB_SAFE_CALL_TAC vars lens spoff j k (asl,w as gl) =
  let st = gm_st spoff (2912 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [k+1] gl
  else
  let ds = dest_small_numeral(rand dsv) in
  let pv = rd st and r = dest_small_numeral(rand(rd (addr_plus st 8))) in
  let inp = word_base pv and len = assoc j lens in
  let ns = mk_small_numeral and sp = find_read_fact `SP` k gl in
  let label,args =
    if r >= 136 then
      gm_af_label j ds,[ns len; inp; ns((len - r) / 136); sp; `pc:num`]
    else
      gm_al_label j r,[ns len; inp; ns(len / 136); sp; `pc:num`] in
  REMOVE_THEN label (fun th ->
    let th1 = SPECL (`e:(uarch_event)list` :: args) th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
               (REWRITE_RULE[WORD_ADD_0] (CONV_RULE NUM_REDUCE_CONV th1)) in
    GM_SAFE_SIM_TAC vars label th2 th k) gl;;

let GM_GETNOISE_SAFE_CALL_TAC vars k gl =
  let v reg = mk_small_numeral(dest_small_numeral
                (rand(find_read_fact reg k gl))) in
  REMOVE_THEN "H_GETNOISE" (fun th ->
    let th1 = SPECL [`e:(uarch_event)list`; find_read_fact `X0` k gl;
                     find_read_fact `X1` k gl; v `X2`; v `X3`; v `X4`;
                     v `X5`; find_read_fact `X6` k gl; `pc:num`;
                     find_read_fact `SP` k gl; find_read_fact `X30` k gl]
                    th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[ARITH_EQ] th1) in
    GM_SAFE_SIM_TAC vars "H_GETNOISE" th2 th k) gl;;

(*** The call of an absorb lemma of job j in FULL form: as in the
 *** correctness proof, with the state of the lane first put as
 *** keccak_absorb 136 P i, and the theorem taken from the assumptions
 ***)

let gm_aff_label j ds = "H_AFF_"^string_of_int j^"_"^string_of_int ds;;
let gm_alf_label j t = "H_ALF_"^string_of_int j^"_"^string_of_int t;;

let GM_ABSORB_FULL_CALL_TAC vars spoff j k (asl,w as gl) =
  let sv = state_of k in
  let st = gm_st spoff (2912 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [k+1] gl
  else
  let ds = dest_small_numeral(rand dsv) in
  let pv = rd st and r = dest_small_numeral(rand(rd (addr_plus st 8))) in
  let inp = word_base pv in
  let mth = find_asm (fun c ->
    try let a,n,s = dest_bytes_read(lhand c) in
        a = inp && s = sv && is_numeral n &&
        fst(dest_const(rator(rand c))) = "num_of_bytelist"
    with Failure _ -> false) gl in
  let _,ln,_ = dest_bytes_read(lhand(concl mth)) in
  let len = dest_small_numeral ln and m = rand(rand(concl mth)) in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,m)
    with Failure _ -> false) gl in
  let lane = gm_lane_addr spoff (2 + j) in
  let p = list_mk_comb(`keccak_padded`,[`136`; mk_small_numeral ds; m]) in
  let i = if r >= 136 then (len - r) / 136 else len / 136 in
  let ka = list_mk_comb(`keccak_absorb`,[`136`; p; mk_small_numeral i]) in
  let lane_tac =
    if i = 0 then
      FIRST_X_ASSUM(fun th ->
        if concl th = vsubst [lane,`a:int64`; sv,`s:armstate`]
                       `read (memory :> bytes(a,200)) s = 0`
        then ASSUME_TAC(TRANS th (SYM(REWRITE_CONV[keccak_absorb; VAL_WORD_0]
                                       (mk_comb(`val:1600 word->num`,ka)))))
        else NO_TAC)
    else
      FIRST_X_ASSUM(fun th ->
        if lhand(concl th) = vsubst [lane,`a:int64`; sv,`s:armstate`]
                               `read (memory :> bytes(a,200)) s`
        then ASSUME_TAC(CONV_RULE(RAND_CONV
               (REWRITE_CONV[KECCAK_ABSORB_BLOCK_STEP] THENC
                NUM_REDUCE_CONV)) th)
        else NO_TAC) in
  let sp = find_read_fact `SP` k gl in
  let label = if r >= 136 then gm_aff_label j ds else gm_alf_label j r in
  (lane_tac THEN
   REMOVE_THEN label (fun th ->
     let th1 = SPECL [`e:(uarch_event)list`; m; inp; mk_small_numeral i; sp;
                      `pc:num`] th in
     let th2 = REWRITE_RULE[WORD_ADD_0]
                (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[lenth] th1)) in
     let th3 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                th2 in
     GM_SAFE_SIM_TAC vars label th3 th k)) gl;;

(* ------------------------------------------------------------------------- *)
(* The proof of an instance with stack size n: the hooks (those of the       *)
(* correctness proof for the job and noise structures and the lanes of the   *)
(* matrix, and for job 0 of decapsulation its lane and digest), the          *)
(* variables of the events, the absorb lemmas the jobs need, the setup, the  *)
(* run and the discharge.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** The hooks for the safety proof: the job and noise structures, the
 *** lanes of the matrix and their copies to the buffers (the others are
 *** not needed), and the calls
 ***)

let gm_safe_derive spoff =
  [gm_pc "nonoise" (-8), STRUCT_LOAD128_TAC `X5` [0; 16];
   gm_pc "nonoise" 0,
     (fun k -> TRY(STRUCT_SPLIT128_TAC (gm_st spoff 2976) [0; 16] k));
   gm_pc "nonoise" 8, STRUCT_LOAD128_TAC `X4` [0; 16; 32; 48];
   gm_pc "jobsdone" 0,
     (fun k -> TRY(STRUCT_SPLIT128_TAC (gm_st spoff 2912) [0; 16; 32; 48] k));
   gm_pc "initloop" 108, GM_MATRIX_LANE_TAC spoff;
   gm_pc "copyloop" 0, GM_COPY_LOAD_TAC;
   gm_pc "copyloop" 48, GM_COPY_STORE_TAC];;

let gm_safe_calls spoff lens vars =
  let exec = MLKEM_GEN_MATRIX_EXEC in
  [gm_pc "end" 0,
     NATIVE2_SAFE_THM_TAC exec vars "H_ZERO" (0,mlkem_native2_image_mc) I
      [`e:(uarch_event)list`; `read SP s`; `pc:num`];
   layout "sha3_keccak4_f1600_alt2", GM_K4_SAFE_CALL_TAC vars;
   gm_pc "rejloop" 4, GM_SAMPLEPOLY_SAFE_TAC vars spoff;
   gm_pc "noiseinit_done" 8, GM_ABSORB_SAFE_CALL_TAC vars lens spoff 0;
   gm_pc "noiseinit_done" 128, GM_ABSORB_SAFE_CALL_TAC vars lens spoff 1;
   layout "mlkem_cbd2",
     NATIVE2_SAFE_THM_TAC exec vars "H_CBD2"
      (layout "mlkem_cbd2",mlkem_cbd2_mc) I
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc + mlkem_cbd2`;
       `read X30 s`];
   layout "mlkem_getnoise", GM_GETNOISE_SAFE_CALL_TAC vars];;

(*** The jobs of an instance (index, length, domain byte) from its
 *** statement, those with a nonzero domain byte
 ***)

let gm_jobs_of tm =
  let body = snd(strip_forall(snd(dest_exists tm))) in
  let ens = snd(dest_imp body) in
  let pre = el 1 (snd(strip_comb ens)) in
  let cs = conjuncts(snd(dest_abs pre)) in
  let field off =
    let lhs = vsubst [mk_small_numeral off,`off:num`]
      `read (memory :> bytes64 (word_add jobs (word off))) s` in
    try let c = find (fun c -> is_eq c && lhand c = lhs) cs in
        Some(dest_small_numeral(rand(rand c)))
    with Failure _ -> None in
  flat(map (fun j ->
    match field (8 + 32 * j),field (16 + 32 * j) with
      Some len,Some ds when ds <> 0 -> [j,len,ds]
    | _ -> []) [0; 1]);;

(*** The driver with the jobs in full (those whose message is kept) ***)

let gm_safe_params tm =
  let vars0 = tl(fst(strip_forall(snd(dest_exists tm)))) in
  let vars = filter (fun v -> type_of v <> `:byte list` ||
                              name_of v = "rho") vars0 in
  let full = flat(map (fun v ->
               if name_of v = "m0" then [0] else
               if name_of v = "m1" then [1] else []) vars0) in
  let jobs = gm_jobs_of tm in
  let lens = map (fun (j,len,_) -> j,len) jobs in
  let absorbs = flat(map (fun (j,len,ds) ->
    if mem j full then
      (if len >= 136
       then [gm_aff_label j ds,assoc (j,ds) gm_absorb_full_full_ths] else []) @
      [gm_alf_label j (len mod 136),
       assoc (j,len mod 136) gm_absorb_last_full_ths]
    else
      (if len >= 136
       then [gm_af_label j ds,assoc (j,ds) gm_absorb_full_safe_ths] else []) @
      [gm_al_label j (len mod 136),
       assoc (j,len mod 136) gm_absorb_last_safe_ths]) jobs) in
  vars,lens,absorbs,full;;

let gm_safe_derive_jobs spoff full =
  gm_safe_derive spoff @
  (if full = [] then [] else
   [gm_pc "outer" 0, (fun k -> TRY(GM_ZERO_LANES_TAC spoff k));
    gm_pc "nohash1" 44, (fun k -> TRY(GM_LANE128_TAC `X12` k));
    gm_pc "nohash1" 52, (fun k -> TRY(GM_DIGEST_TAC k));
    gm_pc "nohash1" 80, (fun k -> TRY(GM_LANE128_TAC `X12` k));
    gm_pc "nohash1" 88, (fun k -> TRY(GM_DIGEST_TAC k))]);;

let gm_safe_calls_jobs spoff lens vars full =
  let absorb j =
    if mem j full then GM_ABSORB_FULL_CALL_TAC vars spoff j
    else GM_ABSORB_SAFE_CALL_TAC vars lens spoff j in
  map (fun (off,tac) ->
         if off = gm_pc "noiseinit_done" 8 then off,absorb 0
         else if off = gm_pc "noiseinit_done" 128 then off,absorb 1
         else off,tac)
      (gm_safe_calls spoff lens vars);;

let GM_SAFE_SETUP_TAC n absorbs =
  ASSUME_CALLEE_TAILED_TAC GM_ZERO_END_SAFE "H_ZERO" THEN
  ASSUME_CALLEE_TAILED_TAC
    SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600 "H_K4" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE "H_SP" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED
    "H_CBD2" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE
    "H_GETNOISE" THEN
  MAP_EVERY (fun (l,th) -> ASSUME_CALLEE_TAILED_TAC th l) absorbs THEN
  META_EXISTS_TAC THEN
  REPEAT(W(fun (_,w) ->
    let v = fst(dest_forall w) in
    if fst(dest_var v) = "stackpointer" then NO_TAC else X_GEN_TAC v)) THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  GM_BYTES128_OF_32_TAC `rhop:int64` `num_of_bytelist(rho:byte list)`;;

let GM_SAFE_FINALE_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

let GM_SAFE_INSTANCE_TAC n (asl,w as gl) =
  let vars,lens,absorbs,full = gm_safe_params w in
  let spoff = n - 3088 in
  (GM_SAFE_SETUP_TAC n absorbs THEN
   NATIVE2_SAFE_RUN_TAC MLKEM_GEN_MATRIX_EXEC (gm_safe_derive_jobs spoff full)
     (gm_safe_calls_jobs spoff lens vars full) 0 THEN
   GM_SAFE_FINALE_TAC) gl;;
