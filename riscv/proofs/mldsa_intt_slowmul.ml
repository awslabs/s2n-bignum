(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA inverse NTT using shift/add multiplication by the modulus.         *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_ntt_shared.ml";;
needs "riscv/proofs/mldsa_intt_shared.ml";;
needs "riscv/proofs/mldsa_ntt_slowmul_shared.ml";;
needs "riscv/proofs/mldsa_intt_layout.ml";;

(* ------------------------------------------------------------------------- *)
(* Phase 1.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_INTT_SLOW_PHASE1_SETUP = prove
 (`!a zetas:int32. !pc.
      ensures riscv
       (\s.
          aligned_bytes_loaded
            s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 36) /\
          C_ARGUMENTS [a;zetas] s /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas)
       (\s.
          aligned_bytes_loaded
            s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 48) /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 2040) /\
          read T2 s = a /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas)
       (MAYCHANGE [PC; A1; T2; T3] ,,
        MAYCHANGE [events])`,
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC; C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read memory s3 = read memory s0` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (ISPECL
       [`memory`; `[PC;A1;T2;T3]`;
        `s0:riscvstate`; `s3:riscvstate`]
       MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ALL] THEN
      REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
      REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
      FIRST_X_ASSUM
       (fun th ->
          if can
              (term_match []
                `(MAYCHANGE [PC] ,, MAYCHANGE [A1] ,,
                  MAYCHANGE [T2] ,, MAYCHANGE [T3])
                 (s0:riscvstate) s3`)
              (concl th)
          then
            MATCH_ACCEPT_TAC(REWRITE_RULE[MAYCHANGE_SING] th)
          else failwith "not the setup frame")];
    REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM
     (fun th ->
        if can
            (term_match []
              `wordlist_from_memory(zetas,510) (s0:riscvstate):
                 int32 list =
               MAP iword rv32_mldsa_ntt_zetas`)
            (concl th)
        then
          MATCH_ACCEPT_TAC
           (REWRITE_RULE
             [wordlist_from_memory; READ_COMPONENT_COMPOSE]
             th)
        else failwith "not the setup table")]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 64
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 48) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(2040 - 24 * g)) /\
              read T2 s = word_add a (word(16 * g)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 76) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(2040 - 24 * (g + 1))) /\
              read T2 s = word_add a (word(16 * g)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1] ,,
            MAYCHANGE [events])`,
  RV32_MLDSA_INTT_OUTER_SETUP_TAC
    MLDSA_INTT_SLOWMUL_EXEC 64 510 7 false);;

let RV32_MLDSA_INTT_SLOW_PHASE1_BODY = prove
 (`!a z:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 76) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s = word_add a (word(16 * g)) /\
              read T3 s = word_add a (word 1024) /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 256) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s = word_add a (word(16 * (g + 1))) /\
              read T3 s = word_add a (word 1024) /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g + 1 then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4 (word_add a (word(16 * g)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      REWRITE_TAC[NUM_RING `16 * g = 4 * (4 * g)`] THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           can
            (term_match []
              `!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add (a:int32)
                         (word(4 * (4 * h + r)))))
                      (s0:riscvstate) =
                     if h < g then
                       rv32_mldsa_intt_phase1
                        (x:num->int32) h r
                     else x (4 * h + r)`)
            (concl th))
         th in
      LABEL_TAC "memory_invariant" th') THEN
  MAP_EVERY
   (fun r ->
      USE_THEN "memory_invariant"
       (fun th ->
          LABEL_TAC ("input" ^ string_of_int r)
           (REWRITE_RULE
             [LT_REFL; ARITH;
              NUM_RING `4 * (4 * g + 0) = 16 * g`;
              NUM_RING `4 * (4 * g + 1) = 16 * g + 4`;
              NUM_RING `4 * (4 * g + 2) = 16 * g + 8`;
              NUM_RING `4 * (4 * g + 3) = 16 * g + 12`]
             (MP
               (SPECL [`g:num`; mk_small_numeral r] th)
               (CONJ
                 (ASSUME `g < 64`)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral r)
                       (mk_small_numeral 4)))))))))
   (0--3) THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--40) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s40:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s41" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s42" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s43" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s44" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h r.
      h < 64 /\ r < 4
      ==> read
           (memory :>
            bytes32
             (word_add a
              (word(4 * (4 * h + r))))) s44 =
          if h < g + 1 then
            rv32_mldsa_intt_phase1 x h r
          else x (4 * h + r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `r:num`] THEN
    STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `h < g + 1 <=> h < g \/ h = g`] THEN
    ASM_CASES_TAC `h:num = g` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(SPEC `r:num` RV32_NTT_INDEX4_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (4 * g + 0) = 16 * g`;
        NUM_RING `4 * (4 * g + 1) = 16 * g + 4`;
        NUM_RING `4 * (4 * g + 2) = 16 * g + 8`;
        NUM_RING `4 * (4 * g + 3) = 16 * g + 12`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC
       [rv32_mldsa_intt_phase1; rv32_mldsa_intt_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_SLOW_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_SLOW_PAIR;
        ARITH_RULE `g < g \/ g = g`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase1_not_current") THEN
      SUBGOAL_THEN
       `!q.
          q < 4
          ==> orthogonal_components
               ((memory :>
                 bytes32
                  (word_add (a:int32)
                   (word(4 * (4 * h + r)))))
                : (riscvstate,int32)component)
               (memory :>
                bytes32
                 (word_add a
                  (word(4 * (4 * g + q)))))`
      (LABEL_TAC "phase1_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `4 * g + q`; `4 * h + r`]
           RV32_NTT_FLAT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "phase1_orthogonal"
       (fun th ->
          MAP_EVERY
           (fun q ->
              let sth =
                MP
                 (SPEC (mk_small_numeral q) th)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral q)
                       (mk_small_numeral 4)))) in
              LABEL_TAC
               ("phase1_orthogonal" ^ string_of_int q)
               sth)
           (0--3)) THEN
      RULE_ASSUM_TAC
       (REWRITE_RULE
         [ARITH;
          NUM_RING `4 * (4 * g + 0) = 16 * g`;
          NUM_RING `4 * (4 * g + 1) = 16 * g + 4`;
          NUM_RING `4 * (4 * g + 2) = 16 * g + 8`;
          NUM_RING `4 * (4 * g + 3) = 16 * g + 12`]) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "prestore_memory"
       (MP_TAC o SPECL [`h:num`; `r:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
         (fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (4 * g + 0) = 16 * g`;
        NUM_RING `4 * (4 * g + 1) = 16 * g + 4`;
        NUM_RING `4 * (4 * g + 2) = 16 * g + 8`;
        NUM_RING `4 * (4 * g + 3) = 16 * g + 12`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (4 * h + r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase1_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (4 * h + r)))))
           : (riscvstate,int32)component)
          events`
      (LABEL_TAC "phase1_events_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      USE_THEN "phase1_orthogonal0"
       (fun orth0 ->
          USE_THEN "phase1_orthogonal1"
           (fun orth1 ->
              USE_THEN "phase1_orthogonal2"
               (fun orth2 ->
                  USE_THEN "phase1_orthogonal3"
                   (fun orth3 ->
                      USE_THEN "phase1_pc_orthogonal"
                       (fun orthpc ->
                          USE_THEN "phase1_events_orthogonal"
                           (fun orthevents ->
                              SIMP_TAC
                               [READ_WRITE_ORTHOGONAL_COMPONENTS;
                                orth0; orth1; orth2; orth3;
                                orthpc; orthevents]))))))];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s44" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s45" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_INTT_SLOW_PHASE1_BACKEDGE = prove
 (`!a zetas:int32. !x:num->int32. !i pc.
      0 < i /\ i < 64
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 256) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(2040 - 24 * i)) /\
              read T2 s = word_add a (word(16 * i)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < i then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 48) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(2040 - 24 * i)) /\
              read T2 s = word_add a (word(16 * i)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < i then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(16 * i)):int32 =
      word_add a (word 1024))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word x):int32 = word_add a (word y) <=>
        (word x:int32) = word y`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `16 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  SUBGOAL_THEN `read memory s1 = read memory s0` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (ISPECL
       [`memory`; `MAYCHANGE [PC]`; `MAYCHANGE [events]`;
        `s0:riscvstate`; `s1:riscvstate`]
       SEQ_PRESERVES_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC
       [`u:riscvstate`; `v:riscvstate`] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC
       (ISPECL
         [`memory`; `[PC]`; `u:riscvstate`; `v:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
      MAP_EVERY X_GEN_TAC
       [`u:riscvstate`; `v:riscvstate`] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC
       (ISPECL
         [`memory`; `[events]`;
          `u:riscvstate`; `v:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(zetas,510) s1:int32 list =
    MAP iword rv32_mldsa_ntt_zetas`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_EXIT = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s.
          aligned_bytes_loaded
            s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 256) /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 504) /\
          read T2 s = word_add a (word(16 * 64)) /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!h r.
             h < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (4 * h + r))))) s =
                 if h < 64 then
                   rv32_mldsa_intt_phase1 x h r
                 else x (4 * h + r)))
       (\s.
          aligned_bytes_loaded
            s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 268) /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 504) /\
          read T2 s = a /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!h r.
             h < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (4 * h + r))))) s =
                 rv32_mldsa_intt_phase1 x h r))
       (MAYCHANGE [PC; T2; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "exit1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s2" None
   (fun th -> LABEL_TAC "exit2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s3" None
   (fun th -> LABEL_TAC "exit3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN `read memory s3 = read memory s0` ASSUME_TAC THENL
   [MAP_EVERY
     (fun label ->
        USE_THEN label
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))
     ["exit3"; "exit2"; "exit1"] THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(zetas,510) s3:int32 list =
    MAP iword rv32_mldsa_ntt_zetas`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `r:num`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            is_forall(concl th) &&
            vfree_in `s3:riscvstate` (concl th))
         th in
      MP_TAC(SPECL [`h:num`; `r:num`] th')) THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_BODY_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded
                 s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 76) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas
                  (word(2040 - 24 * (g + 1))) /\
               read T2 s = word_add a (word(16 * g)) /\
               read T3 s = word_add a (word 1024) /\
               (!h r.
                  h < 64 /\ r < 4
                  ==> read
                       (memory :>
                        bytes32
                         (word_add a
                          (word(4 * (4 * h + r))))) s =
                      if h < g then
                        rv32_mldsa_intt_phase1 x h r
                      else x (4 * h + r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded
                 s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 256) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas
                  (word(2040 - 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(16 * (g + 1))) /\
               read T3 s = word_add a (word 1024) /\
               (!h r.
                  h < 64 /\ r < 4
                  ==> read
                       (memory :>
                        bytes32
                         (word_add a
                          (word(4 * (4 * h + r))))) s =
                      if h < g + 1 then
                        rv32_mldsa_intt_phase1 x h r
                      else x (4 * h + r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "body_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC
     [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "body_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "body_frame_subsumed"
         (MP_TAC o REWRITE_RULE[subsumed]) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "body_frame" ACCEPT_TAC];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`;
        `word_add zetas
          (word(2040 - 24 * (g + 1))):int32`;
        `x:num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE1_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_OUTER_SETUP_MEMORY = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 zetas /\
      g < 64
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded
                 s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 48) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(2040 - 24 * g)) /\
               read T2 s = word_add a (word(16 * g)) /\
               read T3 s = word_add a (word 1024) /\
               wordlist_from_memory(zetas,510) s:int32 list =
               MAP iword rv32_mldsa_ntt_zetas) /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (\s.
              (aligned_bytes_loaded
                 s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 76) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas
                  (word(2040 - 24 * (g + 1))) /\
               read T2 s = word_add a (word(16 * g)) /\
               read T3 s = word_add a (word 1024) /\
               wordlist_from_memory(zetas,510) s:int32 list =
               MAP iword rv32_mldsa_ntt_zetas) /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC
     [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "memory_before")
       (LABEL_TAC "setup_frame")) THEN
    SUBGOAL_THEN
     `read memory s' = read memory s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
       (ISPECL
         [`memory`;
          `MAYCHANGE
            [PC; S0; S1; S2; S3; S4; S5; A1]`;
          `MAYCHANGE [events]`;
          `s:riscvstate`; `s':riscvstate`]
         SEQ_PRESERVES_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC
         [`u:riscvstate`; `v:riscvstate`] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC
         (ISPECL
           [`memory`;
            `[PC; S0; S1; S2; S3; S4; S5; A1]`;
            `u:riscvstate`; `v:riscvstate`]
           MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
        ASM_REWRITE_TAC[ALL] THEN
        REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
        MAP_EVERY X_GEN_TAC
         [`u:riscvstate`; `v:riscvstate`] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC
         (ISPECL
           [`memory`; `[events]`;
            `u:riscvstate`; `v:riscvstate`]
           MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
        ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`h:num`; `r:num`] THEN
    STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `read
       (memory :>
        bytes32
         (word_add a
          (word(4 * (4 * h + r))))) s` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "memory_before"
       (MATCH_MP_TAC o SPECL [`h:num`; `r:num`]) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE1_OUTER_SETUP) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_ITERATION = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 48) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(2040 - 24 * g)) /\
              read T2 s = word_add a (word(16 * g)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 256) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas
                 (word(2040 - 24 * (g + 1))) /\
              read T2 s =
                word_add a (word(16 * (g + 1))) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     if h < g + 1 then
                       rv32_mldsa_intt_phase1 x h r
                     else x (4 * h + r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 76`
   `\s.
      read S0 s =
        FST(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
      read S1 s =
        SND(rv32_mldsa_ntt_pair (252 - 3 * g)) /\
      read S2 s =
        FST(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
      read S3 s =
        SND(rv32_mldsa_ntt_pair (253 - 3 * g)) /\
      read S4 s =
        FST(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
      read S5 s =
        SND(rv32_mldsa_ntt_pair (254 - 3 * g)) /\
      read A0 s = a /\
      read A1 s =
        word_add zetas
         (word(2040 - 24 * (g + 1))) /\
      read T2 s = word_add a (word(16 * g)) /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h r.
         h < 64 /\ r < 4
         ==> read
              (memory :>
               bytes32
                (word_add a
                 (word(4 * (4 * h + r))))) s =
             if h < g then
               rv32_mldsa_intt_phase1 x h r
             else x (4 * h + r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5; A1] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_OUTER_SETUP_MEMORY) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
      DISCH_THEN
       (fun th -> RV32_NTT_USE_STRONGER_PRE_TAC th)];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_BODY_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
      DISCH_THEN
       (fun th -> RV32_NTT_USE_STRONGER_PRE_TAC th)]]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_LOOP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 48) /\
              read A0 s = a /\
              read A1 s = word_add zetas (word 2040) /\
              read T2 s = a /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     x (4 * h + r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 268) /\
              read A0 s = a /\
              read A1 s = word_add zetas (word 504) /\
              read T2 s = a /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     rv32_mldsa_intt_phase1 x h r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `64` `pc + 48` `pc + 256`
   `\i s.
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(2040 - 24 * i)) /\
      read T2 s = word_add a (word(16 * i)) /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h r.
         h < 64 /\ r < 4
         ==> read
              (memory :>
               bytes32
                (word_add a
                 (word(4 * (4 * h + r))))) s =
             if h < i then
               rv32_mldsa_intt_phase1 x h r
             else x (4 * h + r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES;
      ARITH_RULE `~(h < 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `i:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_ITERATION) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `i:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_BACKEDGE) THEN
      ASM_REWRITE_TAC[]];
    ENSURES_PRECONDITION_TAC
     `\s.
        aligned_bytes_loaded
          s (word pc) mldsa_intt_slowmul_mc /\
        read PC s = word(pc + 256) /\
        read A0 s = a /\
        read A1 s = word_add zetas (word 504) /\
        read T2 s = word_add a (word(16 * 64)) /\
        read T3 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h r.
           h < 64 /\ r < 4
           ==> read
                (memory :>
                 bytes32
                  (word_add a
                   (word(4 * (4 * h + r))))) s =
               if h < 64 then
                 rv32_mldsa_intt_phase1 x h r
               else x (4 * h + r))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:riscvstate` THEN
      BETA_TAC THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC; T2; T3] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_ACCEPT_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `x:num->int32`; `pc:num`]
           RV32_MLDSA_INTT_SLOW_PHASE1_EXIT)]]]);;

let RV32_MLDSA_INTT_SLOW_PHASE1_SETUP_MEMORY = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s.
          (aligned_bytes_loaded
             s (word pc) mldsa_intt_slowmul_mc /\
           read PC s = word(pc + 36) /\
           C_ARGUMENTS [a;zetas] s /\
           wordlist_from_memory(zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas) /\
          (!h r.
             h < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (4 * h + r))))) s =
                 x (4 * h + r)))
       (\s.
          (aligned_bytes_loaded
             s (word pc) mldsa_intt_slowmul_mc /\
           read PC s = word(pc + 48) /\
           read A0 s = a /\
           read A1 s = word_add zetas (word 2040) /\
           read T2 s = a /\
           read T3 s = word_add a (word 1024) /\
           wordlist_from_memory(zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas) /\
          (!h r.
             h < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (4 * h + r))))) s =
                 x (4 * h + r)))
       (MAYCHANGE [PC; A1; T2; T3] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC
     [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "memory_before")
       (LABEL_TAC "setup_frame")) THEN
    SUBGOAL_THEN
     `read memory s' = read memory s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
       (ISPECL
         [`memory`;
          `MAYCHANGE [PC; A1; T2; T3]`;
          `MAYCHANGE [events]`;
          `s:riscvstate`; `s':riscvstate`]
         SEQ_PRESERVES_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC
         [`u:riscvstate`; `v:riscvstate`] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC
         (ISPECL
           [`memory`; `[PC; A1; T2; T3]`;
            `u:riscvstate`; `v:riscvstate`]
           MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
        ASM_REWRITE_TAC[ALL] THEN
        REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
        MAP_EVERY X_GEN_TAC
         [`u:riscvstate`; `v:riscvstate`] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC
         (ISPECL
           [`memory`; `[events]`;
            `u:riscvstate`; `v:riscvstate`]
           MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
        ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`h:num`; `r:num`] THEN
    STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `read
       (memory :>
        bytes32
         (word_add a
          (word(4 * (4 * h + r))))) s` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "memory_before"
       (MATCH_MP_TAC o SPECL [`h:num`; `r:num`]) THEN
      ASM_REWRITE_TAC[]];
    MATCH_ACCEPT_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE1_SETUP)]);;

let RV32_MLDSA_INTT_SLOW_PHASE1 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 36) /\
              C_ARGUMENTS [a;zetas] s /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     x (4 * h + r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 268) /\
              read A0 s = a /\
              read A1 s = word_add zetas (word 504) /\
              read T2 s = a /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas /\
              (!h r.
                 h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     rv32_mldsa_intt_phase1 x h r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC; C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 48`
   `\s.
      read A0 s = a /\
      read A1 s = word_add zetas (word 2040) /\
      read T2 s = a /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h r.
         h < 64 /\ r < 4
         ==> read
              (memory :>
               bytes32
                (word_add a
                 (word(4 * (4 * h + r))))) s =
             x (4 * h + r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; A1; T2; T3] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_SETUP_MEMORY) THEN
      REWRITE_TAC[C_ARGUMENTS] THEN
      DISCH_THEN
       (fun th -> RV32_NTT_USE_STRONGER_PRE_TAC th)];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; T3; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1_LOOP) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]]);;


(* ------------------------------------------------------------------------- *)
(* Phase 2.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 16
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 268) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(504 - 24 * g)) /\
              read T2 s = word_add a (word(64 * g)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              read PC s = word(pc + 300) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(504 - 24 * (g + 1))) /\
              read T2 s = word_add a (word(64 * g)) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(64 * g + 16)) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T4] ,,
            MAYCHANGE [events])`,
  RV32_MLDSA_INTT_OUTER_SETUP_TAC
    MLDSA_INTT_SLOWMUL_EXEC 16 126 8 true);;

let RV32_MLDSA_INTT_SLOW_PHASE2_BODY = prove
 (`!a z:int32. !x:num->int32. !g j pc.
      aligned 4 a /\
      g < 16 /\
      j < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 300) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s =
                word_add a (word(64 * g + 4 * j)) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(64 * g + 16)) /\
              (!h l r.
                 h < 16 /\ l < 4 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (16 * h + l + 4 * r))))) s =
                     if h < g \/ h = g /\ l < j then
                       rv32_mldsa_intt_phase2 x h l r
                     else x (16 * h + l + 4 * r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 480) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s =
                word_add a (word(64 * g + 4 * (j + 1))) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(64 * g + 16)) /\
              (!h l r.
                 h < 16 /\ l < 4 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (16 * h + l + 4 * r))))) s =
                     if h < g \/ h = g /\ l < j + 1 then
                       rv32_mldsa_intt_phase2 x h l r
                     else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add a (word(64 * g + 4 * j)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      REWRITE_TAC
       [NUM_RING `64 * g + 4 * j = 4 * (16 * g + j)`] THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           can
            (term_match []
              `!h l r.
                 h < 16 /\ l < 4 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add (a:int32)
                         (word
                           (4 * (16 * h + l + 4 * r)))))
                      (s0:riscvstate) =
                     if h < g \/ h = g /\ l < j then
                       rv32_mldsa_intt_phase2
                        (x:num->int32) h l r
                     else x (16 * h + l + 4 * r)`)
            (concl th))
         th in
      LABEL_TAC "memory_invariant" th') THEN
  MAP_EVERY
   (fun r ->
      USE_THEN "memory_invariant"
       (fun th ->
          LABEL_TAC ("input" ^ string_of_int r)
           (REWRITE_RULE
             [LT_REFL; ARITH;
              NUM_RING
               `4 * (16 * g + j + 4 * 0) =
                64 * g + 4 * j`;
              NUM_RING
               `4 * (16 * g + j + 4 * 1) =
                64 * g + 4 * j + 16`;
              NUM_RING
               `4 * (16 * g + j + 4 * 2) =
                64 * g + 4 * j + 32`;
              NUM_RING
               `4 * (16 * g + j + 4 * 3) =
                64 * g + 4 * j + 48`]
             (MP
               (SPECL [`g:num`; `j:num`; mk_small_numeral r] th)
               (CONJ
                 (ASSUME `g < 16`)
                 (CONJ
                   (ASSUME `j < 4`)
                   (EQT_ELIM
                     (NUM_REDUCE_CONV
                       (mk_binop `(<)`
                         (mk_small_numeral r)
                         (mk_small_numeral 4))))))))))
   (0--3) THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--40) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s40:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s41" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s42" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s43" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s44" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h l r.
      h < 16 /\ l < 4 /\ r < 4
      ==> read
           (memory :>
            bytes32
             (word_add a
              (word
                (4 * (16 * h + l + 4 * r))))) s44 =
          if h < g \/ h = g /\ l < j + 1 then
            rv32_mldsa_intt_phase2 x h l r
          else x (16 * h + l + 4 * r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `h:num = g /\ (l:num) = j` THENL
     [POP_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      MP_TAC(SPEC `r:num` RV32_NTT_INDEX4_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING
         `4 * (16 * g + j + 4 * 0) =
          64 * g + 4 * j`;
        NUM_RING
         `4 * (16 * g + j + 4 * 1) =
          64 * g + 4 * j + 16`;
        NUM_RING
         `4 * (16 * g + j + 4 * 2) =
          64 * g + 4 * j + 32`;
        NUM_RING
         `4 * (16 * g + j + 4 * 3) =
          64 * g + 4 * j + 48`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC
       [rv32_mldsa_intt_phase2; rv32_mldsa_intt_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_SLOW_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_SLOW_PAIR;
        ARITH_RULE `g < g \/ j < j + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase3_not_current") THEN
      SUBGOAL_THEN
       `!q.
          q < 4
          ==> orthogonal_components
               ((memory :>
                 bytes32
                  (word_add (a:int32)
                   (word
                     (4 * (16 * h + l + 4 * r)))))
                : (riscvstate,int32)component)
               (memory :>
                bytes32
                 (word_add a
                  (word
                    (4 * (16 * g + j + 4 * q)))))`
      (LABEL_TAC "phase3_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `h:num`; `l:num`; `r:num`;
            `g:num`; `j:num`; `q:num`]
           RV32_NTT_PHASE3_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "phase3_not_current" ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "phase3_orthogonal"
       (fun th ->
          MAP_EVERY
           (fun q ->
              let sth =
                MP
                 (SPEC (mk_small_numeral q) th)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral q)
                       (mk_small_numeral 4)))) in
              LABEL_TAC
               ("phase3_orthogonal" ^ string_of_int q)
               sth)
           (0--3)) THEN
      RULE_ASSUM_TAC
       (REWRITE_RULE
         [ARITH;
          NUM_RING
           `4 * (16 * g + j + 4 * 0) =
            64 * g + 4 * j`;
          NUM_RING
           `4 * (16 * g + j + 4 * 1) =
            64 * g + 4 * j + 16`;
          NUM_RING
           `4 * (16 * g + j + 4 * 2) =
            64 * g + 4 * j + 32`;
          NUM_RING
           `4 * (16 * g + j + 4 * 3) =
            64 * g + 4 * j + 48`]) THEN
      SUBGOAL_THEN
       `(h < g \/ h = g /\ l < j + 1) <=>
        h < g \/ h = g /\ l < j`
      ASSUME_TAC THENL
       [MATCH_MP_TAC RV32_NTT_PHASE2_PREFIX_UNCHANGED THEN
        USE_THEN "phase3_not_current" ACCEPT_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "prestore_memory"
       (MP_TAC o SPECL [`h:num`; `l:num`; `r:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
         (fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING
         `4 * (16 * g + j + 4 * 0) =
          64 * g + 4 * j`;
        NUM_RING
         `4 * (16 * g + j + 4 * 1) =
          64 * g + 4 * j + 16`;
        NUM_RING
         `4 * (16 * g + j + 4 * 2) =
          64 * g + 4 * j + 32`;
        NUM_RING
         `4 * (16 * g + j + 4 * 3) =
          64 * g + 4 * j + 48`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (16 * h + l + 4 * r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase3_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (16 * h + l + 4 * r)))))
           : (riscvstate,int32)component)
          events`
      (LABEL_TAC "phase3_events_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      USE_THEN "phase3_orthogonal0"
       (fun orth0 ->
          USE_THEN "phase3_orthogonal1"
           (fun orth1 ->
              USE_THEN "phase3_orthogonal2"
               (fun orth2 ->
                  USE_THEN "phase3_orthogonal3"
                   (fun orth3 ->
                      USE_THEN "phase3_pc_orthogonal"
                       (fun orthpc ->
                          USE_THEN "phase3_events_orthogonal"
                           (fun orthevents ->
                              SIMP_TAC
                               [READ_WRITE_ORTHOGONAL_COMPONENTS;
                                orth0; orth1; orth2; orth3;
                                orthpc; orthevents]))))))];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s44" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s45" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_INTT_SLOW_PHASE2_INNER_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !g i pc.
      g < 16 /\ 0 < i /\ i < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 480) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g + 4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g \/ h = g /\ l < i then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 300) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g + 4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g \/ h = g /\ l < i then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(64 * g + 4 * i)):int32 =
      word_add a (word(64 * g + 16)))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word(64 * g + 4 * i)):int32 =
        word_add a (word(64 * g + 16)) <=>
        (word(4 * i):int32) = word 16`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `4 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RV32_MLDSA_INTT_SLOW_PHASE2_INNER_EXIT = prove
 (`!a z:int32. !x:num->int32. !g pc.
      g < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 480) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g + 4 * 4)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g \/ h = g /\ l < 4 then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 488) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s0:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "phase3_memory" th') THEN
  SUBGOAL_THEN
   `!h l r. h < 16 /\ l < 4 /\ r < 4
            ==> read
                 (memory :>
                  bytes32
                   (word_add a
                    (word
                      (4 * (16 * h + l + 4 * r))))) s0 =
                if h < g + 1 then
                  rv32_mldsa_intt_phase2 x h l r
                else x (16 * h + l + 4 * r)`
  (LABEL_TAC "phase3_memory_done") THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    USE_THEN "phase3_memory"
     (MP_TAC o SPECL [`h:num`; `l:num`; `r:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    SUBGOAL_THEN
     `(h < g \/ h = g /\ l < 4) <=> h < g + 1`
    (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "inner_exit_branch" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s2" None
   (fun th -> LABEL_TAC "inner_exit_advance" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (USE_THEN "inner_exit_advance"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "inner_exit_branch"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_RULE) ORELSE
   (MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    USE_THEN "inner_exit_advance"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "inner_exit_branch"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    USE_THEN "phase3_memory_done"
     (fun th ->
        MATCH_MP_TAC(SPECL [`h:num`; `l:num`; `r:num`] th)) THEN
    ASM_REWRITE_TAC[])));;

let RV32_MLDSA_INTT_SLOW_PHASE2_INNER_LOOP = prove
 (`!a z:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 300) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 488) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)) /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `4` `pc + 300` `pc + 480`
   `\i s.
      read S0 s =
        FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
      read S1 s =
        SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
      read S2 s =
        FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
      read S3 s =
        SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
      read S4 s =
        FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
      read S5 s =
        SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
      read A0 s = a /\
      read A1 s = z /\
      read T2 s =
        word_add a (word(64 * g + 4 * i)) /\
      read T3 s = word_add a (word 1024) /\
      read T4 s =
        word_add a (word(64 * g + 16)) /\
      (!h l r. h < 16 /\ l < 4 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word
                         (4 * (16 * h + l + 4 * r))))) s =
                   if h < g \/ h = g /\ l < i then
                     rv32_mldsa_intt_phase2 x h l r
                   else x (16 * h + l + 4 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(l < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_INNER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_INNER_EXIT) THEN
    ASM_REWRITE_TAC[]]);;

let RV32_MLDSA_INTT_SLOW_PHASE2_INNER_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 300) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(504 - 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(64 * g)) /\
               read T3 s = word_add a (word 1024) /\
               read T4 s =
                 word_add a (word(64 * g + 16)) /\
               (!h l r. h < 16 /\ l < 4 /\ r < 4
                        ==> read
                             (memory :>
                              bytes32
                               (word_add a
                                (word
                                  (4 * (16 * h + l + 4 * r))))) s =
                            if h < g then
                              rv32_mldsa_intt_phase2 x h l r
                            else x (16 * h + l + 4 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 488) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(504 - 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(64 * (g + 1))) /\
               read T3 s = word_add a (word 1024) /\
               read T4 s =
                 word_add a (word(64 * g + 16)) /\
               (!h l r. h < 16 /\ l < 4 /\ r < 4
                        ==> read
                             (memory :>
                              bytes32
                               (word_add a
                                (word
                                  (4 * (16 * h + l + 4 * r))))) s =
                            if h < g + 1 then
                              rv32_mldsa_intt_phase2 x h l r
                            else x (16 * h + l + 4 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "inner_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "inner_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "inner_frame_subsumed"
         (MP_TAC o REWRITE_RULE[subsumed]) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "inner_frame" ACCEPT_TAC];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`;
        `word_add zetas (word(504 - 24 * (g + 1))):int32`;
        `x:num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_INNER_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_BACKEDGE = prove
 (`!a zetas:int32. !x:num->int32. !i pc.
      0 < i /\ i < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 488) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 - 24 * i)) /\
                read T2 s =
                  word_add a (word(64 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < i then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 268) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 - 24 * i)) /\
                read T2 s =
                  word_add a (word(64 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < i then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(64 * i)):int32 =
      word_add a (word 1024))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word(64 * i)):int32 =
        word_add a (word 1024) <=>
        (word(64 * i):int32) = word 1024`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `64 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;

let RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_EXIT = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 488) /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 120) /\
            read T2 s = word_add a (word 1024) /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h l r. h < 16 /\ l < 4 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a
                             (word
                               (4 * (16 * h + l + 4 * r))))) s =
                         rv32_mldsa_intt_phase2 x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 500) /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 120) /\
            read T2 s = a /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h l r. h < 16 /\ l < 4 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a
                             (word
                               (4 * (16 * h + l + 4 * r))))) s =
                         rv32_mldsa_intt_phase2 x h l r))
       (MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "exit1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s2" None
   (fun th -> LABEL_TAC "exit2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s3" None
   (fun th -> LABEL_TAC "exit3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN `read memory s3 = read memory s0` ASSUME_TAC THENL
   [MAP_EVERY
     (fun label ->
        USE_THEN label
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))
     ["exit3"; "exit2"; "exit1"] THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(zetas,510) s3:int32 list =
    MAP iword rv32_mldsa_ntt_zetas`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_BODY = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 268) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 - 24 * g)) /\
                read T2 s =
                  word_add a (word(64 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 488) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 - 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(64 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase2 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC] ,,
     MAYCHANGE [S0] ,,
     MAYCHANGE [S1] ,,
     MAYCHANGE [S2] ,,
     MAYCHANGE [S3] ,,
     MAYCHANGE [S4] ,,
     MAYCHANGE [S5] ,,
     MAYCHANGE [A1] ,,
     MAYCHANGE [T4] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "setup_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 300`
   `\s. read S0 s =
          FST(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
        read S1 s =
          SND(rv32_mldsa_ntt_pair (60 - 3 * g)) /\
        read S2 s =
          FST(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
        read S3 s =
          SND(rv32_mldsa_ntt_pair (61 - 3 * g)) /\
        read S4 s =
          FST(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
        read S5 s =
          SND(rv32_mldsa_ntt_pair (62 - 3 * g)) /\
        read A0 s = a /\
        read A1 s =
          word_add zetas (word(504 - 24 * (g + 1))) /\
        read T2 s =
          word_add a (word(64 * g)) /\
        read T3 s = word_add a (word 1024) /\
        read T4 s =
          word_add a (word(64 * g + 16)) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h l r. h < 16 /\ l < 4 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (16 * h + l + 4 * r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase2 x h l r
                     else x (16 * h + l + 4 * r))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL
         [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_SETUP)
       (CONJ
         (ASSUME `aligned 4 (zetas:int32)`)
         (ASSUME `g < 16`))) THEN
    RISCV_BIGSTEP_TAC MLDSA_INTT_SLOWMUL_EXEC "s1" THEN
    ((ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) ORELSE
     ASM_REWRITE_TAC[]) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s0:riscvstate`; `s1:riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "setup_frame_subsumed"
         (fun th -> MATCH_MP_TAC(REWRITE_RULE[subsumed] th)) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE2_INNER_LOOP_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
      DISCH_THEN(LABEL_TAC "inner_loop") THEN
      MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
      USE_THEN "inner_loop"
       (fun th ->
         let tm = concl th in
         MAP_EVERY EXISTS_TAC
          [rand(rator(rator tm)); rand(rator tm)]) THEN
      REPEAT CONJ_TAC THENL
       [BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE3_USE_COEFFICIENT_TAC;
        BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE3_USE_COEFFICIENT_TAC;
        USE_THEN "inner_loop" ACCEPT_TAC]]]);;

let RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_LOOP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 268) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 504) /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 500) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 120) /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             rv32_mldsa_intt_phase2 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `16` `pc + 268` `pc + 488`
   `\i s.
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(504 - 24 * i)) /\
      read T2 s =
        word_add a (word(64 * i)) /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h l r. h < 16 /\ l < 4 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word
                         (4 * (16 * h + l + 4 * r))))) s =
                   if h < i then
                     rv32_mldsa_intt_phase2 x h l r
                   else x (16 * h + l + 4 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(h < 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    ENSURES_PRECONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 488) /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 120) /\
          read T2 s = word_add a (word 1024) /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!h l r. h < 16 /\ l < 4 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word
                             (4 * (16 * h + l + 4 * r))))) s =
                       rv32_mldsa_intt_phase2 x h l r)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:riscvstate` THEN
      BETA_TAC THEN
      STRIP_TAC THEN
      REPEAT CONJ_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (ASM_REWRITE_TAC[] THEN
        TRY(CONV_TAC NUM_REDUCE_CONV) THEN
        TRY(CONV_TAC WORD_RULE) THEN
        NO_TAC) ORELSE
       (REPEAT GEN_TAC THEN
        STRIP_TAC THEN
        RV32_NTT_PHASE3_FINAL_COEFFICIENT_TAC));
      MATCH_ACCEPT_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
         `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_EXIT)]]);;

let RV32_MLDSA_INTT_SLOW_PHASE12 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 36) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           x (4 * h + r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 500) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 120) /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 16 /\ l < 4 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (16 * h + l + 4 * r))))) s =
                             rv32_mldsa_intt_phase12 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 268`
   `\s. read A0 s = a /\
        read A1 s = word_add zetas (word 504) /\
        read T2 s = a /\
        read T3 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h r. h < 64 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word(4 * (4 * h + r))))) s =
                   rv32_mldsa_intt_phase1 x h r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; T3; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[rv32_mldsa_intt_phase12] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `\n. rv32_mldsa_intt_phase1
                x (n DIV 4) (n MOD 4)`;
          `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE2_OUTER_LOOP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(LABEL_TAC "phase2_loop") THEN
      MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
      USE_THEN "phase2_loop"
       (fun th ->
         let tm = concl th in
         MAP_EVERY EXISTS_TAC
          [rand(rator(rator tm)); rand(rator tm)]) THEN
      REPEAT CONJ_TAC THENL
       [BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        FIRST_ASSUM
         (fun th ->
            let th' =
              check
               (fun th ->
                  let vs,bod = strip_forall(concl th) in
                  List.length vs = 2 && is_imp bod)
               th in
            LABEL_TAC "phase1_memory" th') THEN
        ASM_REWRITE_TAC[] THEN
        RV32_INTT_PHASE12_COEFFICIENT_TAC;
        BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM
         (fun ath -> MATCH_MP_TAC (SPEC_ALL ath)) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "phase2_loop" ACCEPT_TAC]]]);;


(* ------------------------------------------------------------------------- *)
(* Phase 3.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 4
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 500) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(120 - 24 * g)) /\
              read T2 s = word_add a (word(256 * g)) /\
              read T3 s = word_add a (word 1024) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              read PC s = word(pc + 532) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read A0 s = a /\
              read A1 s =
                word_add zetas (word(120 - 24 * (g + 1))) /\
              read T2 s = word_add a (word(256 * g)) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(256 * g + 64)) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T4] ,,
            MAYCHANGE [events])`,
  RV32_MLDSA_INTT_OUTER_SETUP_TAC
    MLDSA_INTT_SLOWMUL_EXEC 4 30 8 true);;

let RV32_MLDSA_INTT_SLOW_PHASE3_BODY = prove
 (`!a z:int32. !x:num->int32. !g j pc.
      aligned 4 a /\
      g < 4 /\
      j < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
        (a,1024)
      ==> ensures riscv
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 532) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s =
                word_add a (word(256 * g + 4 * j)) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(256 * g + 64)) /\
              (!h l r.
                 h < 4 /\ l < 16 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (64 * h + l + 16 * r))))) s =
                     if h < g \/ h = g /\ l < j then
                       rv32_mldsa_intt_phase3 x h l r
                     else x (64 * h + l + 16 * r)))
           (\s.
              aligned_bytes_loaded
                s (word pc) mldsa_intt_slowmul_mc /\
              read PC s = word(pc + 712) /\
              read S0 s =
                FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S1 s =
                SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
              read S2 s =
                FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S3 s =
                SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
              read S4 s =
                FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read S5 s =
                SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
              read A0 s = a /\
              read A1 s = z /\
              read T2 s =
                word_add a (word(256 * g + 4 * (j + 1))) /\
              read T3 s = word_add a (word 1024) /\
              read T4 s =
                word_add a (word(256 * g + 64)) /\
              (!h l r.
                 h < 4 /\ l < 16 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (64 * h + l + 16 * r))))) s =
                     if h < g \/ h = g /\ l < j + 1 then
                       rv32_mldsa_intt_phase3 x h l r
                     else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add a (word(256 * g + 4 * j)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      REWRITE_TAC
       [NUM_RING `256 * g + 4 * j = 4 * (64 * g + j)`] THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           can
            (term_match []
              `!h l r.
                 h < 4 /\ l < 16 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add (a:int32)
                         (word
                           (4 * (64 * h + l + 16 * r)))))
                      (s0:riscvstate) =
                     if h < g \/ h = g /\ l < j then
                       rv32_mldsa_intt_phase3
                        (x:num->int32) h l r
                     else x (64 * h + l + 16 * r)`)
            (concl th))
         th in
      LABEL_TAC "memory_invariant" th') THEN
  MAP_EVERY
   (fun r ->
      USE_THEN "memory_invariant"
       (fun th ->
          LABEL_TAC ("input" ^ string_of_int r)
           (REWRITE_RULE
             [LT_REFL; ARITH;
              NUM_RING
               `4 * (64 * g + j + 16 * 0) =
                256 * g + 4 * j`;
              NUM_RING
               `4 * (64 * g + j + 16 * 1) =
                256 * g + 4 * j + 64`;
              NUM_RING
               `4 * (64 * g + j + 16 * 2) =
                256 * g + 4 * j + 128`;
              NUM_RING
               `4 * (64 * g + j + 16 * 3) =
                256 * g + 4 * j + 192`]
             (MP
               (SPECL [`g:num`; `j:num`; mk_small_numeral r] th)
               (CONJ
                 (ASSUME `g < 4`)
                 (CONJ
                   (ASSUME `j < 16`)
                   (EQT_ELIM
                     (NUM_REDUCE_CONV
                       (mk_binop `(<)`
                         (mk_small_numeral r)
                         (mk_small_numeral 4))))))))))
   (0--3) THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--40) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s40:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s41" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s42" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s43" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s44" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h l r.
      h < 4 /\ l < 16 /\ r < 4
      ==> read
           (memory :>
            bytes32
             (word_add a
              (word
                (4 * (64 * h + l + 16 * r))))) s44 =
          if h < g \/ h = g /\ l < j + 1 then
            rv32_mldsa_intt_phase3 x h l r
          else x (64 * h + l + 16 * r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `h:num = g /\ (l:num) = j` THENL
     [POP_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      MP_TAC(SPEC `r:num` RV32_NTT_INDEX4_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING
         `4 * (64 * g + j + 16 * 0) =
          256 * g + 4 * j`;
        NUM_RING
         `4 * (64 * g + j + 16 * 1) =
          256 * g + 4 * j + 64`;
        NUM_RING
         `4 * (64 * g + j + 16 * 2) =
          256 * g + 4 * j + 128`;
        NUM_RING
         `4 * (64 * g + j + 16 * 3) =
          256 * g + 4 * j + 192`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC
       [rv32_mldsa_intt_phase3; rv32_mldsa_intt_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_SLOW_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_SLOW_PAIR;
        ARITH_RULE `g < g \/ j < j + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase3_not_current") THEN
      SUBGOAL_THEN
       `!q.
          q < 4
          ==> orthogonal_components
               ((memory :>
                 bytes32
                  (word_add (a:int32)
                   (word
                     (4 * (64 * h + l + 16 * r)))))
                : (riscvstate,int32)component)
               (memory :>
                bytes32
                 (word_add a
                  (word
                    (4 * (64 * g + j + 16 * q)))))`
      (LABEL_TAC "phase3_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `h:num`; `l:num`; `r:num`;
            `g:num`; `j:num`; `q:num`]
           RV32_NTT_PHASE2_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "phase3_not_current" ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "phase3_orthogonal"
       (fun th ->
          MAP_EVERY
           (fun q ->
              let sth =
                MP
                 (SPEC (mk_small_numeral q) th)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral q)
                       (mk_small_numeral 4)))) in
              LABEL_TAC
               ("phase3_orthogonal" ^ string_of_int q)
               sth)
           (0--3)) THEN
      RULE_ASSUM_TAC
       (REWRITE_RULE
         [ARITH;
          NUM_RING
           `4 * (64 * g + j + 16 * 0) =
            256 * g + 4 * j`;
          NUM_RING
           `4 * (64 * g + j + 16 * 1) =
            256 * g + 4 * j + 64`;
          NUM_RING
           `4 * (64 * g + j + 16 * 2) =
            256 * g + 4 * j + 128`;
          NUM_RING
           `4 * (64 * g + j + 16 * 3) =
            256 * g + 4 * j + 192`]) THEN
      SUBGOAL_THEN
       `(h < g \/ h = g /\ l < j + 1) <=>
        h < g \/ h = g /\ l < j`
      ASSUME_TAC THENL
       [MATCH_MP_TAC RV32_NTT_PHASE2_PREFIX_UNCHANGED THEN
        USE_THEN "phase3_not_current" ACCEPT_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "prestore_memory"
       (MP_TAC o SPECL [`h:num`; `l:num`; `r:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
         (fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING
         `4 * (64 * g + j + 16 * 0) =
          256 * g + 4 * j`;
        NUM_RING
         `4 * (64 * g + j + 16 * 1) =
          256 * g + 4 * j + 64`;
        NUM_RING
         `4 * (64 * g + j + 16 * 2) =
          256 * g + 4 * j + 128`;
        NUM_RING
         `4 * (64 * g + j + 16 * 3) =
          256 * g + 4 * j + 192`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (64 * h + l + 16 * r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase3_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :>
            bytes32
             (word_add (a:int32)
              (word(4 * (64 * h + l + 16 * r)))))
           : (riscvstate,int32)component)
          events`
      (LABEL_TAC "phase3_events_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      USE_THEN "phase3_orthogonal0"
       (fun orth0 ->
          USE_THEN "phase3_orthogonal1"
           (fun orth1 ->
              USE_THEN "phase3_orthogonal2"
               (fun orth2 ->
                  USE_THEN "phase3_orthogonal3"
                   (fun orth3 ->
                      USE_THEN "phase3_pc_orthogonal"
                       (fun orthpc ->
                          USE_THEN "phase3_events_orthogonal"
                           (fun orthevents ->
                              SIMP_TAC
                               [READ_WRITE_ORTHOGONAL_COMPONENTS;
                                orth0; orth1; orth2; orth3;
                                orthpc; orthevents]))))))];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s44" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s45" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_INTT_SLOW_PHASE3_INNER_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !g i pc.
      g < 4 /\ 0 < i /\ i < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 712) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g + 4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g \/ h = g /\ l < i then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 532) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g + 4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g \/ h = g /\ l < i then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(256 * g + 4 * i)):int32 =
      word_add a (word(256 * g + 64)))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word(256 * g + 4 * i)):int32 =
        word_add a (word(256 * g + 64)) <=>
        (word(4 * i):int32) = word 64`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `4 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RV32_MLDSA_INTT_SLOW_PHASE3_INNER_EXIT = prove
 (`!a z:int32. !x:num->int32. !g pc.
      g < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 712) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g + 4 * 16)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g \/ h = g /\ l < 16 then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 720) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s0:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "phase3_memory" th') THEN
  SUBGOAL_THEN
   `!h l r. h < 4 /\ l < 16 /\ r < 4
            ==> read
                 (memory :>
                  bytes32
                   (word_add a
                    (word
                      (4 * (64 * h + l + 16 * r))))) s0 =
                if h < g + 1 then
                  rv32_mldsa_intt_phase3 x h l r
                else x (64 * h + l + 16 * r)`
  (LABEL_TAC "phase3_memory_done") THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    USE_THEN "phase3_memory"
     (MP_TAC o SPECL [`h:num`; `l:num`; `r:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    SUBGOAL_THEN
     `(h < g \/ h = g /\ l < 16) <=> h < g + 1`
    (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "inner_exit_branch" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s2" None
   (fun th -> LABEL_TAC "inner_exit_advance" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (USE_THEN "inner_exit_advance"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "inner_exit_branch"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_RULE) ORELSE
   (MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    USE_THEN "inner_exit_advance"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "inner_exit_branch"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    USE_THEN "phase3_memory_done"
     (fun th ->
        MATCH_MP_TAC(SPECL [`h:num`; `l:num`; `r:num`] th)) THEN
    ASM_REWRITE_TAC[])));;

let RV32_MLDSA_INTT_SLOW_PHASE3_INNER_LOOP = prove
 (`!a z:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 532) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 720) /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)) /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `16` `pc + 532` `pc + 712`
   `\i s.
      read S0 s =
        FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
      read S1 s =
        SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
      read S2 s =
        FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
      read S3 s =
        SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
      read S4 s =
        FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
      read S5 s =
        SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
      read A0 s = a /\
      read A1 s = z /\
      read T2 s =
        word_add a (word(256 * g + 4 * i)) /\
      read T3 s = word_add a (word 1024) /\
      read T4 s =
        word_add a (word(256 * g + 64)) /\
      (!h l r. h < 4 /\ l < 16 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word
                         (4 * (64 * h + l + 16 * r))))) s =
                   if h < g \/ h = g /\ l < i then
                     rv32_mldsa_intt_phase3 x h l r
                   else x (64 * h + l + 16 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(l < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_INNER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_INNER_EXIT) THEN
    ASM_REWRITE_TAC[]]);;

let RV32_MLDSA_INTT_SLOW_PHASE3_INNER_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 532) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(120 - 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(256 * g)) /\
               read T3 s = word_add a (word 1024) /\
               read T4 s =
                 word_add a (word(256 * g + 64)) /\
               (!h l r. h < 4 /\ l < 16 /\ r < 4
                        ==> read
                             (memory :>
                              bytes32
                               (word_add a
                                (word
                                  (4 * (64 * h + l + 16 * r))))) s =
                            if h < g then
                              rv32_mldsa_intt_phase3 x h l r
                            else x (64 * h + l + 16 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 720) /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(120 - 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(256 * (g + 1))) /\
               read T3 s = word_add a (word 1024) /\
               read T4 s =
                 word_add a (word(256 * g + 64)) /\
               (!h l r. h < 4 /\ l < 16 /\ r < 4
                        ==> read
                             (memory :>
                              bytes32
                               (word_add a
                                (word
                                  (4 * (64 * h + l + 16 * r))))) s =
                            if h < g + 1 then
                              rv32_mldsa_intt_phase3 x h l r
                            else x (64 * h + l + 16 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "inner_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "inner_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "inner_frame_subsumed"
         (MP_TAC o REWRITE_RULE[subsumed]) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "inner_frame" ACCEPT_TAC];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`;
        `word_add zetas (word(120 - 24 * (g + 1))):int32`;
        `x:num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_INNER_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_BACKEDGE = prove
 (`!a zetas:int32. !x:num->int32. !i pc.
      0 < i /\ i < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 720) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 - 24 * i)) /\
                read T2 s =
                  word_add a (word(256 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < i then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 500) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 - 24 * i)) /\
                read T2 s =
                  word_add a (word(256 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < i then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(256 * i)):int32 =
      word_add a (word 1024))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word(256 * i)):int32 =
        word_add a (word 1024) <=>
        (word(256 * i):int32) = word 1024`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `256 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;
let RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_EXIT = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 720) /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 24) /\
            read T2 s = word_add a (word 1024) /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h l r. h < 4 /\ l < 16 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a
                             (word
                               (4 * (64 * h + l + 16 * r))))) s =
                         rv32_mldsa_intt_phase3 x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 724) /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 24) /\
            read T2 s = word_add a (word 1024) /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h l r. h < 4 /\ l < 16 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a
                             (word
                               (4 * (64 * h + l + 16 * r))))) s =
                         rv32_mldsa_intt_phase3 x h l r))
       (MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;

let RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_BODY = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 500) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 - 24 * g)) /\
                read T2 s =
                  word_add a (word(256 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 720) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 - 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(256 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             if h < g + 1 then
                               rv32_mldsa_intt_phase3 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC] ,,
     MAYCHANGE [S0] ,,
     MAYCHANGE [S1] ,,
     MAYCHANGE [S2] ,,
     MAYCHANGE [S3] ,,
     MAYCHANGE [S4] ,,
     MAYCHANGE [S5] ,,
     MAYCHANGE [A1] ,,
     MAYCHANGE [T4] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "setup_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 532`
   `\s. read S0 s =
          FST(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
        read S1 s =
          SND(rv32_mldsa_ntt_pair (12 - 3 * g)) /\
        read S2 s =
          FST(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
        read S3 s =
          SND(rv32_mldsa_ntt_pair (13 - 3 * g)) /\
        read S4 s =
          FST(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
        read S5 s =
          SND(rv32_mldsa_ntt_pair (14 - 3 * g)) /\
        read A0 s = a /\
        read A1 s =
          word_add zetas (word(120 - 24 * (g + 1))) /\
        read T2 s =
          word_add a (word(256 * g)) /\
        read T3 s = word_add a (word 1024) /\
        read T4 s =
          word_add a (word(256 * g + 64)) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h l r. h < 4 /\ l < 16 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (64 * h + l + 16 * r))))) s =
                     if h < g then
                       rv32_mldsa_intt_phase3 x h l r
                     else x (64 * h + l + 16 * r))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL
         [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_SETUP)
       (CONJ
         (ASSUME `aligned 4 (zetas:int32)`)
         (ASSUME `g < 4`))) THEN
    RISCV_BIGSTEP_TAC MLDSA_INTT_SLOWMUL_EXEC "s1" THEN
    ((ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) ORELSE
     ASM_REWRITE_TAC[]) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s0:riscvstate`; `s1:riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "setup_frame_subsumed"
         (fun th -> MATCH_MP_TAC(REWRITE_RULE[subsumed] th)) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `x:num->int32`;
          `g:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE3_INNER_LOOP_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
      DISCH_THEN(LABEL_TAC "inner_loop") THEN
      MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
      USE_THEN "inner_loop"
       (fun th ->
         let tm = concl th in
         MAP_EVERY EXISTS_TAC
          [rand(rator(rator tm)); rand(rator tm)]) THEN
      REPEAT CONJ_TAC THENL
       [BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE2_USE_COEFFICIENT_TAC;
        BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE2_USE_COEFFICIENT_TAC;
        USE_THEN "inner_loop" ACCEPT_TAC]]]);;

let RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_LOOP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 500) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 120) /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 724) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
                read T2 s = word_add a (word 1024) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             rv32_mldsa_intt_phase3 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `4` `pc + 500` `pc + 720`
   `\i s.
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(120 - 24 * i)) /\
      read T2 s =
        word_add a (word(256 * i)) /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h l r. h < 4 /\ l < 16 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word
                         (4 * (64 * h + l + 16 * r))))) s =
                   if h < i then
                     rv32_mldsa_intt_phase3 x h l r
                   else x (64 * h + l + 16 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(h < 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    ENSURES_PRECONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
          read PC s = word(pc + 720) /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 24) /\
          read T2 s = word_add a (word 1024) /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!h l r. h < 4 /\ l < 16 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word
                             (4 * (64 * h + l + 16 * r))))) s =
                       rv32_mldsa_intt_phase3 x h l r)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:riscvstate` THEN
      BETA_TAC THEN
      STRIP_TAC THEN
      REPEAT CONJ_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (ASM_REWRITE_TAC[] THEN
        TRY(CONV_TAC NUM_REDUCE_CONV) THEN
        TRY(CONV_TAC WORD_RULE) THEN
        NO_TAC) ORELSE
       (REPEAT GEN_TAC THEN
        STRIP_TAC THEN
        RV32_NTT_PHASE2_FINAL_COEFFICIENT_TAC));
      MATCH_ACCEPT_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_EXIT)]]);;

let RV32_MLDSA_INTT_SLOW_PHASE123 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 36) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           x (4 * h + r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 724) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
                read T2 s = word_add a (word 1024) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h l r. h < 4 /\ l < 16 /\ r < 4
                         ==> read
                              (memory :>
                               bytes32
                                (word_add a
                                 (word
                                   (4 * (64 * h + l + 16 * r))))) s =
                             rv32_mldsa_intt_phase123 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 500`
   `\s. read A0 s = a /\
        read A1 s = word_add zetas (word 120) /\
        read T2 s = a /\
        read T3 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h l r. h < 16 /\ l < 4 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (16 * h + l + 4 * r))))) s =
                     rv32_mldsa_intt_phase12 x h l r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE12) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rv32_mldsa_intt_phase123] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `\n. rv32_mldsa_intt_phase12 x
                (n DIV 16) (n MOD 4) ((n DIV 4) MOD 4)`;
          `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE3_OUTER_LOOP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(LABEL_TAC "phase3_loop") THEN
      MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
      USE_THEN "phase3_loop"
       (fun th ->
         let tm = concl th in
         MAP_EVERY EXISTS_TAC
          [rand(rator(rator tm)); rand(rator tm)]) THEN
      REPEAT CONJ_TAC THENL
       [BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        FIRST_ASSUM
         (fun th ->
            let th' =
              check
               (fun th ->
                  let vs,bod = strip_forall(concl th) in
                  List.length vs = 3 && is_imp bod)
               th in
            LABEL_TAC "phase12_memory" th') THEN
        ASM_REWRITE_TAC[] THEN
        RV32_INTT_PHASE123_COEFFICIENT_TAC;
        BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM
         (fun ath -> MATCH_MP_TAC (SPEC_ALL ath)) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "phase3_loop" ACCEPT_TAC]]]);;


(* ------------------------------------------------------------------------- *)
(* Phase 4.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_INTT_SLOW_PHASE4_SETUP = prove
 (`!a zetas:int32. !pc.
      aligned 4 zetas
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 724) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
                read T2 s = word_add a (word 1024) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 760) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = zetas /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T2; T4] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4 (word_add zetas (word 24):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_DIVIDES_CONV;
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
  ASSUME_TAC THENL
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
      let read_tm =
        subst
         [ntm,`i:num`]
         `read
           (memory :>
            bytes32(word_add zetas (word(4 * i)))) s0 =
          iword(EL i rv32_mldsa_ntt_zetas)` in
      SUBGOAL_THEN read_tm
       (LABEL_TAC ("table" ^ string_of_int n)) THENL
       [FIRST_ASSUM
         (fun th ->
            if can
                (term_match []
                  `!i. i < 510
                       ==> read
                            (memory :>
                             bytes32
                              (word_add zetas (word(4 * i)))) s0 =
                           iword(EL i rv32_mldsa_ntt_zetas)`)
                (concl th)
            then MATCH_MP_TAC(SPEC ntm th)
            else failwith "not the table-read theorem") THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC])
   (0--5) THEN
  REWRITE_TAC[rv32_mldsa_ntt_pair; FST; SND] THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "setup1" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN `aligned 4 (read A1 s1:int32)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("setup" ^ string_of_int n) th THEN
          STRIP_TAC))
   (2--9) THEN
  SUBGOAL_THEN `read memory s9 = read memory s0` ASSUME_TAC THENL
   [MAP_EVERY
     (fun n ->
        USE_THEN ("setup" ^ string_of_int n)
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))
     (rev(1--9)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(zetas,510) s9:int32 list =
    MAP iword rv32_mldsa_ntt_zetas`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "initial_table" ACCEPT_TAC];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  MAP_EVERY
   (fun n ->
      USE_THEN ("setup" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--9)) THEN
  REWRITE_TAC
   [NUM_REDUCE_CONV `2 * 0`;
    NUM_REDUCE_CONV `2 * 0 + 1`;
    NUM_REDUCE_CONV `2 * 1`;
    NUM_REDUCE_CONV `2 * 1 + 1`;
    NUM_REDUCE_CONV `2 * 2`;
    NUM_REDUCE_CONV `2 * 2 + 1`] THEN
  ASM_REWRITE_TAC
   [NUM_REDUCE_CONV `4 * 0`;
    NUM_REDUCE_CONV `4 * 1`;
    NUM_REDUCE_CONV `4 * 2`;
    NUM_REDUCE_CONV `4 * 3`;
    NUM_REDUCE_CONV `4 * 4`;
    NUM_REDUCE_CONV `4 * 5`;
    WORD_32_ADD_MODULUS; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "table0"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE
           [NUM_REDUCE_CONV `4 * 0`; WORD_ADD_0] th));
    USE_THEN "table1"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE[NUM_REDUCE_CONV `4 * 1`] th));
    USE_THEN "table2"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE[NUM_REDUCE_CONV `4 * 2`] th));
    USE_THEN "table3"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE[NUM_REDUCE_CONV `4 * 3`] th));
    USE_THEN "table4"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE[NUM_REDUCE_CONV `4 * 4`] th));
    USE_THEN "table5"
     (fun th ->
        MATCH_ACCEPT_TAC
         (REWRITE_RULE[NUM_REDUCE_CONV `4 * 5`] th))]);;

let RV32_MLDSA_INTT_SLOW_PHASE4_BODY = prove
 (`!a z:int32. !x:num->int32. !j pc.
      aligned 4 a /\
      j < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 760) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * j)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           if l < j then
                             rv32_mldsa_intt_phase4 x l r
                           else x (l + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 940) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * (j + 1))) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           if l < j + 1 then
                             rv32_mldsa_intt_phase4 x l r
                           else x (l + 64 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `j:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4 (word_add a (word(4 * j)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           can
            (term_match []
              `!l r. l < 64 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add (a:int32)
                             (word(4 * (l + 64 * r)))))
                          (s0:riscvstate) =
                         if l < j then
                           rv32_mldsa_intt_phase4
                            (x:num->int32) l r
                         else x (l + 64 * r)`)
            (concl th))
         th in
      LABEL_TAC "memory_invariant" th') THEN
  MAP_EVERY
   (fun r ->
      USE_THEN "memory_invariant"
       (fun th ->
          LABEL_TAC ("input" ^ string_of_int r)
           (REWRITE_RULE
             [LT_REFL; ARITH;
              NUM_RING `4 * (j + 64 * 0) = 4 * j`;
              NUM_RING `4 * (j + 64 * 1) = 4 * j + 256`;
              NUM_RING `4 * (j + 64 * 2) = 4 * j + 512`;
              NUM_RING `4 * (j + 64 * 3) = 4 * j + 768`]
             (MP
               (SPECL [`j:num`; mk_small_numeral r] th)
               (CONJ
                 (ASSUME `j < 64`)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral r)
                       (mk_small_numeral 4)))))))))
   (0--3) THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--40) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s40:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s41" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s42" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s43" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s44" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!l r. l < 64 /\ r < 4
          ==> read
               (memory :>
                bytes32
                 (word_add a
                  (word(4 * (l + 64 * r))))) s44 =
              if l < j + 1 then
                rv32_mldsa_intt_phase4 x l r
              else x (l + 64 * r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num`; `r:num`] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `l:num = j` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(SPEC `r:num` RV32_NTT_INDEX4_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (j + 64 * 0) = 4 * j`;
        NUM_RING `4 * (j + 64 * 1) = 4 * j + 256`;
        NUM_RING `4 * (j + 64 * 2) = 4 * j + 512`;
        NUM_RING `4 * (j + 64 * 3) = 4 * j + 768`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC
       [rv32_mldsa_intt_phase4; rv32_mldsa_intt_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_SLOW_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_SLOW_PAIR;
        ARITH_RULE `j < j + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase4_not_current") THEN
      SUBGOAL_THEN
       `!q. q < 4
            ==> orthogonal_components
                 ((memory :> bytes32
                   (word_add (a:int32)
                    (word(4 * (l + 64 * r)))))
                  : (riscvstate,int32)component)
                 (memory :> bytes32
                   (word_add a
                    (word(4 * (j + 64 * q)))))`
      (LABEL_TAC "phase4_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `j:num`; `l:num`; `r:num`; `q:num`]
           RV32_NTT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "phase4_not_current" (fun th -> ASM_MESON_TAC[th]);
        ALL_TAC] THEN
      USE_THEN "phase4_orthogonal"
       (fun th ->
          MAP_EVERY
           (fun q ->
              let sth =
                MP
                 (SPEC (mk_small_numeral q) th)
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral q)
                       (mk_small_numeral 4)))) in
              LABEL_TAC
               ("phase4_orthogonal" ^ string_of_int q)
               sth)
           (0--3)) THEN
      RULE_ASSUM_TAC
       (REWRITE_RULE
         [ARITH;
          NUM_RING `4 * (j + 64 * 0) = 4 * j`;
          NUM_RING `4 * (j + 64 * 1) = 4 * j + 256`;
          NUM_RING `4 * (j + 64 * 2) = 4 * j + 512`;
          NUM_RING `4 * (j + 64 * 3) = 4 * j + 768`]) THEN
      SUBGOAL_THEN `(l < j + 1) <=> l < j` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "prestore_memory"
       (MP_TAC o SPECL [`l:num`; `r:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
         (fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (j + 64 * 0) = 4 * j`;
        NUM_RING `4 * (j + 64 * 1) = 4 * j + 256`;
        NUM_RING `4 * (j + 64 * 2) = 4 * j + 512`;
        NUM_RING `4 * (j + 64 * 3) = 4 * j + 768`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (l + 64 * r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase4_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (l + 64 * r)))))
           : (riscvstate,int32)component)
          events`
      (LABEL_TAC "phase4_events_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      USE_THEN "phase4_orthogonal0"
       (fun orth0 ->
          USE_THEN "phase4_orthogonal1"
           (fun orth1 ->
              USE_THEN "phase4_orthogonal2"
               (fun orth2 ->
                  USE_THEN "phase4_orthogonal3"
                   (fun orth3 ->
                      USE_THEN "phase4_pc_orthogonal"
                       (fun orthpc ->
                          USE_THEN "phase4_events_orthogonal"
                           (fun orthevents ->
                              SIMP_TAC
                               [READ_WRITE_ORTHOGONAL_COMPONENTS;
                                orth0; orth1; orth2; orth3;
                                orthpc; orthevents]))))))];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s44" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s45" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_INTT_SLOW_PHASE4_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !i pc.
      0 < i /\ i < 64
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 940) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           if l < i then
                             rv32_mldsa_intt_phase4 x l r
                           else x (l + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 760) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * i)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           if l < i then
                             rv32_mldsa_intt_phase4 x l r
                           else x (l + 64 * r)))
           (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(4 * i)):int32 =
      word_add a (word 256))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word x):int32 = word_add a (word y) <=>
        (word x:int32) = word y`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `4 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RV32_MLDSA_INTT_SLOW_PHASE4_EXIT = prove
 (`!a z:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 940) /\
            read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
            read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
            read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
            read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
            read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
            read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
            read A0 s = a /\
            read A1 s = z /\
            read T2 s = word_add a (word(4 * 64)) /\
            read T3 s = word_add a (word 1024) /\
            read T4 s = word_add a (word 256) /\
            (!l r. l < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (l + 64 * r))))) s =
                       if l < 64 then
                         rv32_mldsa_intt_phase4 x l r
                       else x (l + 64 * r)))
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 944) /\
            read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
            read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
            read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
            read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
            read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
            read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
            read A0 s = a /\
            read A1 s = z /\
            read T2 s = word_add a (word 256) /\
            read T3 s = word_add a (word 1024) /\
            read T4 s = word_add a (word 256) /\
            (!l r. l < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (l + 64 * r))))) s =
                       rv32_mldsa_intt_phase4 x l r))
       (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "phase4_exit" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[NUM_REDUCE_CONV `4 * 64`] THEN
  MAP_EVERY X_GEN_TAC [`l:num`; `r:num`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            is_forall(concl th) &&
            vfree_in `s1:riscvstate` (concl th) &&
            vfree_in `x:num->int32` (concl th))
         th in
      MP_TAC(SPECL [`l:num`; `r:num`] th')) THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_INTT_SLOW_PHASE4_LOOP = prove
 (`!a z:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 760) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = a /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           x (l + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 944) /\
                read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
                read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
                read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
                read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
                read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
                read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word 256) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                (!l r. l < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (l + 64 * r))))) s =
                           rv32_mldsa_intt_phase4 x l r))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `64` `pc + 760` `pc + 940`
   `\i s.
      read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
      read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
      read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
      read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
      read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
      read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
      read A0 s = a /\
      read A1 s = z /\
      read T2 s = word_add a (word(4 * i)) /\
      read T3 s = word_add a (word 1024) /\
      read T4 s = word_add a (word 256) /\
      (!l r. l < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (l + 64 * r))))) s =
                 if l < i then
                   rv32_mldsa_intt_phase4 x l r
                 else x (l + 64 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(l < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE4_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `z:int32`; `x:num->int32`;
          `i:num`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE4_BACKEDGE) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_ACCEPT_TAC
       (SPECL
         [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE4_EXIT)]]);;

let RV32_MLDSA_INTT_SLOW_PHASE4_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 760) /\
               read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
               read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
               read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
               read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
               read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
               read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
               read A0 s = a /\
               read A1 s = zetas /\
               read T2 s = a /\
               read T3 s = word_add a (word 1024) /\
               read T4 s = word_add a (word 256) /\
               (!l r. l < 64 /\ r < 4
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (l + 64 * r))))) s =
                          x (l + 64 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 944) /\
               read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
               read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
               read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
               read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
               read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
               read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
               read A0 s = a /\
               read A1 s = zetas /\
               read T2 s = word_add a (word 256) /\
               read T3 s = word_add a (word 1024) /\
               read T4 s = word_add a (word 256) /\
               (!l r. l < 64 /\ r < 4
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (l + 64 * r))))) s =
                          rv32_mldsa_intt_phase4 x l r)) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "loop_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "loop_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "loop_frame_subsumed"
         (MP_TAC o REWRITE_RULE[subsumed]) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "loop_frame" ACCEPT_TAC];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`;
        `x:num->int32`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE4_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_PHASE4_SETUP_MEMORY = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 zetas
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 724) /\
               read A0 s = a /\
               read A1 s = word_add zetas (word 24) /\
               read T2 s = word_add a (word 1024) /\
               read T3 s = word_add a (word 1024) /\
               wordlist_from_memory(zetas,510) s:int32 list =
               MAP iword rv32_mldsa_ntt_zetas) /\
              (!h l r. h < 4 /\ l < 16 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word
                                 (4 * (64 * h + l + 16 * r))))) s =
                           rv32_mldsa_intt_phase123 x h l r))
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 760) /\
               read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
               read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
               read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
               read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
               read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
               read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
               read A0 s = a /\
               read A1 s = zetas /\
               read T2 s = a /\
               read T3 s = word_add a (word 1024) /\
               read T4 s = word_add a (word 256) /\
               wordlist_from_memory(zetas,510) s:int32 list =
               MAP iword rv32_mldsa_ntt_zetas) /\
              (!j r. j < 64 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a
                             (word(4 * (j + 64 * r))))) s =
                         rv32_mldsa_intt_phase123 x
                          ((j + 64 * r) DIV 64)
                          ((j + 64 * r) MOD 16)
                          (((j + 64 * r) DIV 16) MOD 4)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T2; T4] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_PRECONDITION_TAC
   `\s.
      (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
       read PC s = word(pc + 724) /\
       read A0 s = a /\
       read A1 s = word_add zetas (word 24) /\
       read T2 s = word_add a (word 1024) /\
       read T3 s = word_add a (word 1024) /\
       wordlist_from_memory(zetas,510) s:int32 list =
       MAP iword rv32_mldsa_ntt_zetas) /\
      (!j r. j < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (j + 64 * r))))) s =
                 rv32_mldsa_intt_phase123 x
                  ((j + 64 * r) DIV 64)
                  ((j + 64 * r) MOD 16)
                  (((j + 64 * r) DIV 16) MOD 4))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:riscvstate` THEN
    BETA_TAC THEN
    STRIP_TAC THEN
    FIRST_ASSUM
     (fun th ->
        let th' =
          check
           (fun th ->
              can
               (term_match []
                 `!h l r. h < 4 /\ l < 16 /\ r < 4
                          ==> read
                               (memory :>
                                bytes32
                                 (word_add (a:int32)
                                  (word
                                    (4 *
                                     (64 * h + l + 16 * r)))))
                               (s:riscvstate) =
                              rv32_mldsa_intt_phase123
                               (x:num->int32) h l r`)
               (concl th))
           th in
        LABEL_TAC "phase123_memory" th') THEN
    CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`j:num`; `r:num`] THEN
      STRIP_TAC THEN
      RV32_INTT_PHASE1234_COEFFICIENT_TAC];
    MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC
       [`s:riscvstate`; `s':riscvstate`] THEN
      DISCH_THEN
       (CONJUNCTS_THEN2
         (LABEL_TAC "memory_before")
         (LABEL_TAC "setup_frame")) THEN
      SUBGOAL_THEN
       `read memory s' = read memory s`
      ASSUME_TAC THENL
       [MATCH_MP_TAC
         (ISPECL
           [`memory`;
            `MAYCHANGE
              [PC; S0; S1; S2; S3; S4; S5; A1; T2; T4]`;
            `MAYCHANGE [events]`;
            `s:riscvstate`; `s':riscvstate`]
           SEQ_PRESERVES_COMPONENT) THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC
           [`u:riscvstate`; `v:riscvstate`] THEN
          DISCH_TAC THEN
          MATCH_MP_TAC
           (ISPECL
             [`memory`;
              `[PC; S0; S1; S2; S3; S4; S5; A1; T2; T4]`;
              `u:riscvstate`; `v:riscvstate`]
             MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
          ASM_REWRITE_TAC[ALL] THEN
          REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
          MAP_EVERY X_GEN_TAC
           [`u:riscvstate`; `v:riscvstate`] THEN
          DISCH_TAC THEN
          MATCH_MP_TAC
           (ISPECL
             [`memory`; `[events]`;
              `u:riscvstate`; `v:riscvstate`]
             MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
          ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `r:num`] THEN
      STRIP_TAC THEN
      TRANS_TAC EQ_TRANS
       `read
         (memory :>
          bytes32
           (word_add a
            (word(4 * (j + 64 * r))))) s` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "memory_before"
         (MATCH_MP_TAC o SPECL [`j:num`; `r:num`]) THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE4_SETUP) THEN
      ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]]);;

let RV32_MLDSA_INTT_SLOW_PHASE1234 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 36) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           x (4 * h + r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 944) /\
                read A0 s = a /\
                read A1 s = zetas /\
                read T2 s = word_add a (word 256) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!j r. j < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           rv32_mldsa_intt_phase1234 x j r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 724`
   `\s. read A0 s = a /\
        read A1 s = word_add zetas (word 24) /\
        read T2 s = word_add a (word 1024) /\
        read T3 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h l r. h < 4 /\ l < 16 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word
                           (4 * (64 * h + l + 16 * r))))) s =
                     rv32_mldsa_intt_phase123 x h l r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_PHASE123) THEN
    ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 760`
     `\s. read S0 s = FST(rv32_mldsa_ntt_pair 0) /\
          read S1 s = SND(rv32_mldsa_ntt_pair 0) /\
          read S2 s = FST(rv32_mldsa_ntt_pair 1) /\
          read S3 s = SND(rv32_mldsa_ntt_pair 1) /\
          read S4 s = FST(rv32_mldsa_ntt_pair 2) /\
          read S5 s = SND(rv32_mldsa_ntt_pair 2) /\
          read A0 s = a /\
          read A1 s = zetas /\
          read T2 s = a /\
          read T3 s = word_add a (word 1024) /\
          read T4 s = word_add a (word 256) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!j r. j < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (j + 64 * r))))) s =
                     rv32_mldsa_intt_phase123 x
                      ((j + 64 * r) DIV 64)
                      ((j + 64 * r) MOD 16)
                      (((j + 64 * r) DIV 16) MOD 4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5; A1; T2; T4] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MP_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `x:num->int32`; `pc:num`]
           RV32_MLDSA_INTT_SLOW_PHASE4_SETUP_MEMORY) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC];
      REWRITE_TAC[rv32_mldsa_intt_phase1234] THEN
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MP_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `\n. rv32_mldsa_intt_phase123 x
                  (n DIV 64) (n MOD 16) ((n DIV 16) MOD 4)`;
            `pc:num`]
           RV32_MLDSA_INTT_SLOW_PHASE4_LOOP_TABLE) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC]]]);;


(* ------------------------------------------------------------------------- *)
(* Final scaling pass.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_INTT_SCALE_SLOW = prove
 (`!a:int32.
      let t =
        word_ishr
          (word_add
            (word_subword
              (word_mul
                (word_sx a:int64)
                (word_sx (word 16791564:int32):int64))
              (32,32):int32)
            (word 1))
          1 in
      word_sub
        (word_add
          (word_sub (word_mul a (word 16382)) t)
          (word_shl t 13))
        (word_shl (word_shl t 13) 10) =
      arm_mldsa_barmul (&4197891,word 16382) a`,
  GEN_TAC THEN
  REWRITE_TAC
   [LET_DEF; LET_END_DEF;
    MLDSA_Q_MUL_SHIFT_ADD;
    MLDSA_INTT_SCALE_MULH]);;

let MLDSA_INTT_SCALE_SLOW_EXPANDED =
  REWRITE_RULE[LET_DEF; LET_END_DEF]
    MLDSA_INTT_SCALE_SLOW;;

let RV32_MLDSA_INTT_SLOW_SCALE_SETUP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 944) /\
            read A0 s = a /\
            read A1 s = zetas /\
            read T2 s = word_add a (word 256) /\
            read T3 s = word_add a (word 1024) /\
            read T4 s = word_add a (word 256) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!j r. j < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (j + 64 * r))))) s =
                       rv32_mldsa_intt_phase1234 x j r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
            read PC s = word(pc + 968) /\
            read S6 s = word 16382 /\
            read S7 s = word 16791564 /\
            read A0 s = a /\
            read A1 s = zetas /\
            read T2 s = a /\
            read T3 s = word_add a (word 1024) /\
            read T4 s = word_add a (word 256) /\
            read T5 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!n. n < 256
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a (word(4 * n)))) s =
                     rv32_mldsa_intt_phase1234 x
                      (n MOD 64) (n DIV 64)))
       (MAYCHANGE [PC; S6; S7; T2; T5] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            can
             (find_term
               (fun tm ->
                  is_const tm &&
                  fst(dest_const tm) = "wordlist_from_memory"))
             (concl th))
         th in
      LABEL_TAC "initial_table" th') THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            is_forall(concl th) &&
            vfree_in `s0:riscvstate` (concl th) &&
            vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "phase1234_memory" th') THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s1" None
   (fun th -> LABEL_TAC "scale_setup1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s2" None
   (fun th -> LABEL_TAC "scale_setup2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s3" None
   (fun th -> LABEL_TAC "scale_setup3" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s4" None
   (fun th -> LABEL_TAC "scale_setup4" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s5" None
   (fun th -> LABEL_TAC "scale_setup5" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s6" None
   (fun th -> LABEL_TAC "scale_setup6" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN `read memory s6 = read memory s0` ASSUME_TAC THENL
   [MAP_EVERY
     (fun n ->
        USE_THEN ("scale_setup" ^ string_of_int n)
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))
     (rev(1--6)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(zetas,510) s6:int32 list =
    MAP iword rv32_mldsa_ntt_zetas`
  ASSUME_TAC THENL
   [REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "initial_table"
     (fun th ->
       MATCH_ACCEPT_TAC
        (REWRITE_RULE
          [wordlist_from_memory; READ_COMPONENT_COMPOSE]
          th));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n < 256
        ==> read
             (memory :>
              bytes32
               (word_add a (word(4 * n)))) s6 =
            rv32_mldsa_intt_phase1234 x
             (n MOD 64) (n DIV 64)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:num` RV32_INTT_FLAT_INDEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "column_bound")
       (CONJUNCTS_THEN2
         (LABEL_TAC "row_bound")
         (LABEL_TAC "flat_index"))) THEN
    TRANS_TAC EQ_TRANS
     `read
       (memory :>
        bytes32
         (word_add a (word(4 * n)))) s0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "phase1234_memory"
       (fun memory_th ->
         USE_THEN "column_bound"
          (fun column_th ->
            USE_THEN "row_bound"
             (fun row_th ->
               USE_THEN "flat_index"
                (fun index_th ->
                  let th =
                    MP
                     (SPECL [`n MOD 64`; `n DIV 64`] memory_th)
                     (CONJ column_th row_th) in
                  MATCH_ACCEPT_TAC
                   (REWRITE_RULE[index_th] th)))))];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_INTT_SLOW_SCALE_LOOP = prove
 (`!a:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 968) /\
                read S6 s = word 16382 /\
                read S7 s = word 16791564 /\
                read A0 s = a /\
                read T2 s = a /\
                read T5 s = word_add a (word 1024) /\
                (!j. j < 256
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a (word(4 * j)))) s =
                         rv32_mldsa_intt_phase1234 x
                          (j MOD 64) (j DIV 64)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 1020) /\
                read S6 s = word 16382 /\
                read S7 s = word 16791564 /\
                read A0 s = a /\
                read T2 s = word_add a (word 1024) /\
                read T5 s = word_add a (word 1024) /\
                (!j. j < 256
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a (word(4 * j)))) s =
                         rv32_mldsa_intt_output x j))
           (MAYCHANGE [PC; T2; A2; A3; A6] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `256` `pc + 968` `pc + 1016`
   `\i s.
      read S6 s = word 16382 /\
      read S7 s = word 16791564 /\
      read A0 s = a /\
      read T2 s = word_add a (word(4 * i)) /\
      read T5 s = word_add a (word 1024) /\
      (!j. j < 256
           ==> read
                (memory :>
                 bytes32
                  (word_add a (word(4 * j)))) s =
               if j < i then
                 rv32_mldsa_intt_output x j
               else
                 rv32_mldsa_intt_phase1234 x
                  (j MOD 64) (j DIV 64))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES;
      ARITH_RULE `~(j < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `aligned 4
       (word_add a (word(4 * i)):int32)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC
       [ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN
        REWRITE_TAC[DIVIDES_REFL]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM
     (fun th ->
       let th' =
         check
          (fun th ->
            is_forall(concl th) &&
            vfree_in `a:int32` (concl th) &&
            vfree_in `s0:riscvstate` (concl th))
          th in
       ASSUME_TAC
        (MP (SPEC `i:num` th') (ASSUME `i < 256`))) THEN
    RISCV_VSTEPS_TAC MLDSA_INTT_SLOWMUL_EXEC (1--10) THEN
    RISCV_STEP_TAC MLDSA_INTT_SLOWMUL_EXEC [] "s11" None
     (fun th ->
       LABEL_TAC "scale_store_update" th THEN
       STRIP_TAC) THEN
    SUBGOAL_THEN
     `!j. j < 256
          ==> read
               (memory :>
                bytes32
                 (word_add a (word(4 * j)))) s11 =
              if j < i + 1 then
                rv32_mldsa_intt_output x j
              else
                rv32_mldsa_intt_phase1234 x
                 (j MOD 64) (j DIV 64)`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC
       [ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      ASM_CASES_TAC `j:num = i` THENL
       [ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[rv32_mldsa_intt_output] THEN
        MATCH_ACCEPT_TAC
         (CONV_RULE
           (ONCE_DEPTH_CONV WORD_NUM_RED_CONV)
           (SPEC
             `rv32_mldsa_intt_phase1234 x
               (i MOD 64) (i DIV 64):int32`
             MLDSA_INTT_SCALE_SLOW_EXPANDED));
        ASM_REWRITE_TAC[] THEN
        USE_THEN "scale_store_update"
         (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
        CONV_TAC
         (ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
        TRANS_TAC EQ_TRANS
         `read
           (memory :>
            bytes32
             (word_add a (word(4 * j)))) s10` THEN
        CONJ_TAC THENL
         [READ_OVER_WRITE_TAC;
          FIRST_ASSUM
           (fun th ->
             let th' =
               check
                (fun th ->
                  is_forall(concl th) &&
                  vfree_in `a:int32` (concl th) &&
                  vfree_in `s10:riscvstate` (concl th))
                th in
             ACCEPT_TAC
              (MP
                (SPEC `j:num` th')
                (ASSUME `j < 256`)))]];
      ALL_TAC] THEN
    DISCARD_OLDSTATE_TAC "s11" THEN
    RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [12] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [rv32_mldsa_intt_output;
      MLDSA_INTT_SCALE_SLOW_EXPANDED] THEN
    CONV_TAC WORD_RULE;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~((4 * i) MOD 4294967296 = 1024)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `4 * i < 4294967296`
      ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(word_add a (word(4 * i)):int32 =
        word_add a (word 1024))`
    ASSUME_TAC THENL
     [REWRITE_TAC
       [WORD_RULE
         `word_add a (word x):int32 =
          word_add a (word y) <=>
          (word x:int32) = word y`;
        WORD_EQ; DIMINDEX_32; CONG] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    RISCV_STEPS_TAC MLDSA_INTT_SLOWMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV);
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[]]]);;

let RV32_MLDSA_INTT_SLOW_SCALE_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 968) /\
               read S6 s = word 16382 /\
               read S7 s = word 16791564 /\
               read A0 s = a /\
               read T2 s = a /\
               read T5 s = word_add a (word 1024) /\
               (!j. j < 256
                    ==> read
                         (memory :>
                          bytes32
                           (word_add a (word(4 * j)))) s =
                        rv32_mldsa_intt_phase1234 x
                         (j MOD 64) (j DIV 64))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
               read PC s = word(pc + 1020) /\
               read S6 s = word 16382 /\
               read S7 s = word 16791564 /\
               read A0 s = a /\
               read T2 s = word_add a (word 1024) /\
               read T5 s = word_add a (word 1024) /\
               (!j. j < 256
                    ==> read
                         (memory :>
                          bytes32
                           (word_add a (word(4 * j)))) s =
                        rv32_mldsa_intt_output x j)) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A6] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`;
    `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [PC; T2; A2; A3; A6] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "scale_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC
     [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "scale_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "scale_frame_subsumed"
         (MP_TAC o REWRITE_RULE[subsumed]) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "scale_frame" ACCEPT_TAC];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `x:num->int32`; `pc:num`]
       RV32_MLDSA_INTT_SLOW_SCALE_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC]]);;

let RV32_MLDSA_INTT_SLOW_SCALE = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 944) /\
                read A0 s = a /\
                read A1 s = zetas /\
                read T2 s = word_add a (word 256) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s = word_add a (word 256) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!j r. j < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           rv32_mldsa_intt_phase1234 x j r))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 1020) /\
                read S6 s = word 16382 /\
                read S7 s = word 16791564 /\
                read A0 s = a /\
                read T2 s = word_add a (word 1024) /\
                read T5 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!j. j < 256
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a (word(4 * j)))) s =
                         rv32_mldsa_intt_output x j))
           (MAYCHANGE [PC; S6; S7; T2; T5; A2; A3; A6] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`;
    `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 968`
   `\s. read S6 s = word 16382 /\
        read S7 s = word 16791564 /\
        read A0 s = a /\
        read T2 s = a /\
        read T5 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!j. j < 256
             ==> read
                  (memory :>
                   bytes32
                    (word_add a (word(4 * j)))) s =
                 rv32_mldsa_intt_phase1234 x
                  (j MOD 64) (j DIV 64))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; S6; S7; T2; T5] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      RV32_NTT_USE_STRONGER_PRE_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_SCALE_SETUP)];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; T2; A2; A3; A6] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_SCALE_LOOP_TABLE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC]]);;
let RV32_MLDSA_INTT_SLOW_MACHINE = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_intt_slowmul_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 36) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           x (4 * h + r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
                read PC s = word(pc + 1020) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!j. j < 256
                     ==> read
                          (memory :>
                           bytes32
                            (word_add a (word(4 * j)))) s =
                         rv32_mldsa_intt_output x j))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; S6; S7;
              A1; T2; T3; T4; T5;
              A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`;
    `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 944`
   `\s. read A0 s = a /\
        read A1 s = zetas /\
        read T2 s = word_add a (word 256) /\
        read T3 s = word_add a (word 1024) /\
        read T4 s = word_add a (word 256) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!j r. j < 64 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word(4 * (j + 64 * r))))) s =
                   rv32_mldsa_intt_phase1234 x j r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S0; S1; S2; S3; S4; S5;
        A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_PHASE1234) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; S6; S7; T2; T5; A2; A3; A6] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_INTT_SLOW_SCALE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC]]);;


needs "riscv/proofs/mldsa_intt_arithmetic.ml";;

(* ========================================================================= *)
(* Functional correctness and psABI promotion of the inverse NTT.           *)
(* ========================================================================= *)

let MLDSA_INTT_SLOW_CORE_CORRECT = prove
 (`!a zetas:int32. !x:num->int32. !pc:num.
    aligned 4 a /\
    aligned 4 zetas /\
    nonoverlapping
      ((word pc):int32,LENGTH mldsa_intt_slowmul_mc)
      (a,1024) /\
    nonoverlapping (a,1024) (zetas,2040)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
           read PC s = word (pc + 36) /\
           C_ARGUMENTS [a;zetas] s /\
           wordlist_from_memory (zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas /\
           (!i. i < 256
                ==> abs(ival(x i)) <= &8380416) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i))
      (\s. read PC s = word (pc + 1020) /\
           !i. i < 256
               ==> let zi =
                     read
                      (memory :>
                       bytes32 (word_add a (word (4 * i)))) s in
                   (ival zi ==
                    mldsa_bitreverse_inverse_ntt (ival o x) i)
                   (mod &8380417) /\
                   abs(ival zi) <= &8380416)
      (MAYCHANGE
        [PC; S0; S1; S2; S3; S4; S5; S6; S7;
         A1; T2; T3; T4; T5;
         A2; A3; A4; A5; A6; A7] ,,
       MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC
   (SPECL
     [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
     RV32_MLDSA_INTT_SLOW_MACHINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "machine") THEN
  MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
  USE_THEN "machine"
   (fun th ->
     let tm = concl th in
     MAP_EVERY EXISTS_TAC
      [rand(rator(rator tm)); rand(rator tm)]) THEN
  REPEAT CONJ_TAC THENL
   [BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    BETA_TAC THEN X_GEN_TAC `s:riscvstate` THEN
    DISCH_THEN
     (fun th ->
       let ths = CONJUNCTS th in
       MAP_EVERY ASSUME_TAC ths THEN
       LABEL_TAC "outputs" (last ths)) THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    CONV_TAC let_CONV THEN
    SUBGOAL_THEN
     `read
       (memory :>
        bytes32 (word_add a (word (4 * i)))) s =
      rv32_mldsa_intt_output x i`
    SUBST1_TAC THENL
     [USE_THEN "outputs"
       (fun th -> MATCH_MP_TAC (SPEC `i:num` th)) THEN
      ASM_REWRITE_TAC[];
      MP_TAC
       (SPEC `x:num->int32`
         RV32_MLDSA_INTT_PHASE1234_CORRECT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "machine" ACCEPT_TAC]);;

let MLDSA_INTT_SLOW_SUBROUTINE_CORRECT = prove
 (`!a zetas:int32. !x:num->int32. !pc:num.
    !stackpointer returnaddress:int32.
    aligned 4 a /\
    aligned 4 zetas /\
    aligned 16 stackpointer /\
    aligned 4 returnaddress /\
    ALLPAIRS nonoverlapping
      [(a,1024);
       (word_sub stackpointer (word 32),32)]
      [((word pc):int32,LENGTH mldsa_intt_slowmul_mc);
       (zetas,2040)] /\
    nonoverlapping
      (a,1024)
      (word_sub stackpointer (word 32),32)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) mldsa_intt_slowmul_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read RA s = returnaddress /\
           C_ARGUMENTS [a;zetas] s /\
           wordlist_from_memory (zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas /\
           (!i. i < 256
                ==> abs(ival(x i)) <= &8380416) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           read SP s = stackpointer /\
           !i. i < 256
               ==> let zi =
                     read
                      (memory :>
                       bytes32 (word_add a (word (4 * i)))) s in
                   (ival zi ==
                    mldsa_bitreverse_inverse_ntt (ival o x) i)
                   (mod &8380417) /\
                   abs(ival zi) <= &8380416)
      (MAYCHANGE_REGS_PERMITTED_BY_ABI ,,
       MAYCHANGE
        [memory :> bytes(a,1024);
         memory :>
          bytes(word_sub stackpointer (word 32),32)])`,
  REWRITE_TAC[fst MLDSA_INTT_SLOWMUL_EXEC] THEN
  RISCV_ADD_RETURN_STACK_TAC
    ~core_precondition_tac:RV32_MLDSA_NTT_STACK_TABLE_TAC
    MLDSA_INTT_SLOWMUL_EXEC
    (REWRITE_RULE[fst MLDSA_INTT_SLOWMUL_EXEC]
      MLDSA_INTT_SLOW_CORE_CORRECT)
    `[S0; S1; S2; S3; S4; S5; S6; S7]` 32);;

(* ========================================================================= *)
(* Constant-time and memory-safety proof of the slow inverse NTT.            *)
(*                                                                           *)
(* MUL and MULH have no operand-dependent timing event in the RV32 model.    *)
(* ========================================================================= *)

needs "riscv/proofs/consttime.ml";;

let mldsa_intt_slow_rv32im_signature =
  ([("a","int32_t[static 256]","false");
    ("zetas","int32_t[static 510]","true")],
   "void",
   [("a","256",4);
    ("zetas","510",4)],
   [("a","256",4)],
   []);;

let mldsa_intt_slow_full_spec,mldsa_intt_slow_public_vars =
  mk_safety_spec
    ~keep_maychanges:false
    mldsa_intt_slow_rv32im_signature
    MLDSA_INTT_SLOW_SUBROUTINE_CORRECT
    MLDSA_INTT_SLOWMUL_EXEC;;

let MLDSA_INTT_SLOW_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a zetas pc stackpointer returnaddress.
           aligned 4 a /\
           aligned 4 zetas /\
           aligned 16 stackpointer /\
           aligned 4 returnaddress /\
           ALLPAIRS nonoverlapping
           [a,1024; word_sub stackpointer (word 32),32]
           [word pc,LENGTH mldsa_intt_slowmul_mc; zetas,2040] /\
           nonoverlapping
           (a,1024) (word_sub stackpointer (word 32),32)
           ==> ensures riscv
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_intt_slowmul_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read RA s = returnaddress /\
                    C_ARGUMENTS [a;zetas] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events zetas a pc
                        (word_sub stackpointer (word 32))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,1024; zetas,2040;
                         word_sub stackpointer (word 32),32]
                        [a,1024;
                         word_sub stackpointer (word 32),32])
               (\s s'. true)`,
  ASSERT_CONCL_TAC mldsa_intt_slow_full_spec THEN
  PROVE_SAFETY_SPEC_TAC
    ~public_vars:mldsa_intt_slow_public_vars
    MLDSA_INTT_SLOWMUL_EXEC);;
