(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared support for the RV32 ML-DSA inverse NTT implementations.           *)
(* ========================================================================= *)

(* Prove the setup block shared by one fast and one shift/add inverse-NTT
   phase. The tactic loads the six `(z,w)` table words used by the current
   outer group, advances the table pointer backwards, and preserves the input
   memory and complete zeta-table assertion.

   `group_count` and `table_words` describe the phase layout, `step_count` is
   the final symbolic state number, and `has_t4` records whether the setup also
   initializes T4. For example,

     RV32_MLDSA_INTT_OUTER_SETUP_TAC exec 64 510 7 false

   handles the first phase, whose first group consumes table pairs 252--254. *)

let RV32_MLDSA_INTT_OUTER_SETUP_TAC
      exec group_count table_words step_count has_t4 =
  let group_count_tm = mk_small_numeral group_count
  and table_words_tm = mk_small_numeral table_words
  and next_words_tm = mk_small_numeral (table_words - 6)
  and pair0_tm = mk_small_numeral ((table_words - 6) / 2)
  and pair1_tm = mk_small_numeral ((table_words - 6) / 2 + 1)
  and pair2_tm = mk_small_numeral ((table_words - 6) / 2 + 2)
  and table_bytes_tm = mk_small_numeral (4 * table_words) in
  let inst tm =
    subst
     [group_count_tm,`group_count:num`;
      table_words_tm,`table_words:num`;
      next_words_tm,`next_words:num`;
      pair0_tm,`pair0:num`;
      pair1_tm,`pair1:num`;
      pair2_tm,`pair2:num`;
      table_bytes_tm,`table_bytes:num`]
     tm in
  let final_state_name = "s" ^ string_of_int step_count in
  let final_state =
    mk_var(final_state_name,type_of `s0:riscvstate`) in
  let final_memory_tm =
    subst
     [final_state,`sf:riscvstate`]
     `read memory sf = read memory s0` in
  let final_table_tm =
    subst
     [final_state,`sf:riscvstate`]
     `wordlist_from_memory(zetas,510) sf:int32 list =
      MAP iword rv32_mldsa_ntt_zetas` in
  let first_read_tm =
    inst
     `read
       (memory :>
        bytes32
         (word_add zetas
          (word(4 * (next_words - 6 * g + 0))))) s0 =
      iword(EL (next_words - 6 * g + 0)
        rv32_mldsa_ntt_zetas)` in
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst exec] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   (inst
     `table_bytes - 24 * g = 4 * (table_words - 6 * g)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (ARITH_RULE
       (inst
         `g < group_count
          ==> table_bytes - 24 * g =
              4 * (table_words - 6 * g)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst
     `table_bytes - 24 * (g + 1) =
      4 * (next_words - 6 * g)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (ARITH_RULE
       (inst
         `g < group_count
          ==> table_bytes - 24 * (g + 1) =
              4 * (next_words - 6 * g)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst
     `aligned 4
       (word_add zetas
        (word(table_bytes - 24 * g)):int32)`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst
     `aligned 4
       (word_add zetas
        (word(4 * (table_words - 6 * g))):int32)`)
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst
     `aligned 4
       (word_add zetas
        (word(table_bytes - 24 * (g + 1))):int32)`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM
   (fun th ->
      if can
          (term_match []
            `wordlist_from_memory(zetas,510) (s0:riscvstate):
               int32 list =
             MAP iword rv32_mldsa_ntt_zetas`)
          (concl th)
      then LABEL_TAC "initial_table" th
      else failwith "not the initial table") THEN
  SUBGOAL_THEN
   `!i. i < 510
        ==> read
             (memory :>
              bytes32(word_add zetas (word(4 * i)))) s0 =
            iword(EL i rv32_mldsa_ntt_zetas)`
  (LABEL_TAC "table_reads") THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `EL i
       (wordlist_from_memory(zetas,510) s0:int32 list)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_SYM THEN
      MATCH_MP_TAC RV32_WORDLIST_FROM_MEMORY_EL THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[EL_MAP; RV32_MLDSA_NTT_ZETAS_LENGTH]];
    ALL_TAC] THEN
  MAP_EVERY
   (fun n ->
      let ntm = mk_small_numeral n in
      let index_tm =
        inst(subst [ntm,`n:num`] `next_words - 6 * g + n`) in
      let read_tm =
        subst
         [index_tm,`ii:num`]
         `read
           (memory :>
            bytes32(word_add zetas (word(4 * ii)))) s0 =
          iword(EL ii rv32_mldsa_ntt_zetas)` in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [USE_THEN "table_reads"
         (fun th -> MATCH_MP_TAC(SPEC index_tm th)) THEN
        ASM_ARITH_TAC;
        ALL_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let ntm = mk_small_numeral n in
      let offset_tm = mk_small_numeral (4294967272 + 4 * n) in
      let index_tm =
        inst(subst [ntm,`n:num`] `next_words - 6 * g + n`) in
      let arithmetic_tm =
        inst
         (subst
           [ntm,`n:num`; offset_tm,`offset:num`]
           `4 * (table_words - 6 * g) + offset =
            4294967296 + 4 * (next_words - 6 * g + n)`) in
      let arithmetic_th =
        ARITH_RULE
         (inst
           (subst
             [ntm,`n:num`; offset_tm,`offset:num`]
             `g < group_count
              ==> 4 * (table_words - 6 * g) + offset =
                  4294967296 +
                  4 * (next_words - 6 * g + n)`)) in
      let address_tm =
        inst
         (subst
           [offset_tm,`offset:num`; index_tm,`ii:num`]
           `word_add zetas
              (word
                (4 * (table_words - 6 * g) + offset)):int32 =
            word_add zetas (word(4 * ii))`) in
      let read_tm =
        inst
         (subst
           [offset_tm,`offset:num`; index_tm,`ii:num`]
           `read
             (memory :>
              bytes32
               (word_add zetas
                 (word
                   (4 * (table_words - 6 * g) + offset)))) s0 =
            iword(EL ii rv32_mldsa_ntt_zetas)`) in
      SUBGOAL_THEN arithmetic_tm ASSUME_TAC THENL
       [MATCH_MP_TAC arithmetic_th THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN address_tm ASSUME_TAC THENL
       [ASM_REWRITE_TAC[WORD_32_ADD_MODULUS];
        ALL_TAC] THEN
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  SUBGOAL_THEN
   (inst
     `word_add
        (word_add zetas
          (word(4 * (table_words - 6 * g))))
        (word 4294967272):int32 =
      word_add zetas
        (word(table_bytes - 24 * (g + 1)))`)
  (LABEL_TAC "post_pointer") THENL
   [SUBGOAL_THEN
     (inst
       `4 * (table_words - 6 * g) + 4294967272 =
        4294967296 + (table_bytes - 24 * (g + 1))`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC
       (ARITH_RULE
         (inst
           `g < group_count
            ==> 4 * (table_words - 6 * g) + 4294967272 =
                4294967296 +
                (table_bytes - 24 * (g + 1))`)) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC
       [WORD_RULE
         `word_add (word_add z (word x)) (word y):int32 =
          word_add z (word(x + y))`] THEN
      REWRITE_TAC[WORD_32_ADD_MODULUS; ADD_CLAUSES]];
    ALL_TAC] THEN
  REWRITE_TAC[rv32_mldsa_ntt_pair; FST; SND] THEN
  RISCV_STEP_TAC exec []
   "s1" None
   (fun th -> LABEL_TAC "setup1" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN `aligned 4 (read A1 s1:int32)` ASSUME_TAC THENL
   [ASM_SIMP_TAC
     [ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst
     `aligned 4
       (word_add zetas
        (word(4 * (next_words - 6 * g))):int32)`)
  ASSUME_TAC THENL
   [ASM_SIMP_TAC
     [ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC exec []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("setup" ^ string_of_int n) th THEN
          STRIP_TAC))
   (2--step_count) THEN
  SUBGOAL_THEN final_memory_tm ASSUME_TAC THENL
   [MAP_EVERY
     (fun n ->
        USE_THEN ("setup" ^ string_of_int n)
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))
     (rev(1--step_count)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN final_table_tm ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "initial_table" ACCEPT_TAC];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN
   (inst
     `2 * (pair0 - 3 * g) =
        next_words - 6 * g /\
      2 * (pair0 - 3 * g) + 1 =
        next_words - 6 * g + 1 /\
      2 * (pair1 - 3 * g) =
        next_words - 6 * g + 2 /\
      2 * (pair1 - 3 * g) + 1 =
        next_words - 6 * g + 3 /\
      2 * (pair2 - 3 * g) =
        next_words - 6 * g + 4 /\
      2 * (pair2 - 3 * g) + 1 =
        next_words - 6 * g + 5`)
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC
     (ARITH_RULE
       (inst
         `g < group_count
          ==> 2 * (pair0 - 3 * g) =
                next_words - 6 * g /\
              2 * (pair0 - 3 * g) + 1 =
                next_words - 6 * g + 1 /\
              2 * (pair1 - 3 * g) =
                next_words - 6 * g + 2 /\
              2 * (pair1 - 3 * g) + 1 =
                next_words - 6 * g + 3 /\
              2 * (pair2 - 3 * g) =
                next_words - 6 * g + 4 /\
              2 * (pair2 - 3 * g) + 1 =
                next_words - 6 * g + 5`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY
   (fun n ->
      USE_THEN ("setup" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--step_count)) THEN
  USE_THEN "post_pointer" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC
   (map
     (fun n ->
        let ntm = mk_small_numeral n
        and offset_tm = mk_small_numeral (4 * n) in
        NUM_RING
         (inst
           (subst
             [ntm,`n:num`; offset_tm,`offset:num`]
             `4 * (next_words - 6 * g) + offset =
              4 * (next_words - 6 * g + n)`)))
     (1--5)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  (if has_t4 then
     CONJ_TAC THENL
      [MATCH_ACCEPT_TAC
        (REWRITE_RULE[ADD_CLAUSES] (ASSUME first_read_tm));
       CONV_TAC WORD_RULE]
   else
     MATCH_ACCEPT_TAC
      (REWRITE_RULE[ADD_CLAUSES] (ASSUME first_read_tm)));;
