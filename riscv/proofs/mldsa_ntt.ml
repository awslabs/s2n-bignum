(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA forward number-theoretic transform.                                *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_ntt_shared.ml";;

(* ------------------------------------------------------------------------- *)
(* Phase 1.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_NTT_PHASE1_SETUP = prove
 (`!a zetas:int32. !pc.
      aligned 4 zetas
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 28) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (\s. read PC s = word(pc + 72) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
                read T2 s = a /\
                read T4 s = word_add a (word 256))
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5; A1; T2; T4] ,,
            MAYCHANGE [events])`,
  REWRITE_TAC[fst MLDSA_NTT_EXEC; C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `!i. i < 510
        ==> read
             (memory :>
              bytes32(word_add zetas (word(4 * i)))) s0 =
            iword(EL i rv32_mldsa_ntt_zetas)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `EL i
       (wordlist_from_memory(zetas,510) s0:int32 list)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_SYM THEN
      MATCH_MP_TAC RV32_WORDLIST_FROM_MEMORY_EL THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[EL_MAP; RV32_MLDSA_NTT_ZETAS_LENGTH]];
    DISCH_THEN
     (fun table_reads ->
        MAP_EVERY
         (fun i ->
            MP_TAC
             (MP
               (SPEC (mk_small_numeral i) table_reads)
               (EQT_ELIM
                 (NUM_REDUCE_CONV
                   (mk_binop `(<)`
                     (mk_small_numeral i)
                     (mk_small_numeral 510))))))
         (0--5))] THEN
  REWRITE_TAC[rv32_mldsa_ntt_zetas; ARITH; WORD_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM
   (fun th ->
      let _ =
        check
         (fun th ->
            can
             (term_match []
               `wordlist_from_memory(zetas,510) (s0:riscvstate):
                  int32 list =
                MAP iword rv32_mldsa_ntt_zetas`)
             (concl th))
         th in
      ALL_TAC) THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
  REWRITE_TAC[]);;

let RV32_MLDSA_BARRETT_PAIR0 = prove
 (`!a:int32.
    word_sub
      (word_mul a (word 4291395073))
      (word_mul
        (word_subword
          (word_mul (word_sx a:int64)
                    (word 18446744071878785801))
          (32,32):int32)
        (word 8380417)) =
    mldsa_barrett_mul
      (iword (-- &3572223),iword (-- &1830765815)) a`,
  GEN_TAC THEN REWRITE_TAC[mldsa_barrett_mul] THEN
  CONV_TAC(DEPTH_CONV WORD_IWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SX_CONV) THEN
  REFL_TAC);;

let RV32_MLDSA_BARRETT_PAIR1 = prove
 (`!a:int32.
    word_sub
      (word_mul a (word 3765607))
      (word_mul
        (word_subword
          (word_mul (word_sx a:int64) (word 1929875198))
          (32,32):int32)
        (word 8380417)) =
    mldsa_barrett_mul
      (iword (&3765607),iword (&1929875198)) a`,
  GEN_TAC THEN REWRITE_TAC[mldsa_barrett_mul] THEN
  CONV_TAC(DEPTH_CONV WORD_IWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SX_CONV) THEN
  REFL_TAC);;

let RV32_MLDSA_BARRETT_PAIR2 = prove
 (`!a:int32.
    word_sub
      (word_mul a (word 3761513))
      (word_mul
        (word_subword
          (word_mul (word_sx a:int64) (word 1927777021))
          (32,32):int32)
        (word 8380417)) =
    mldsa_barrett_mul
      (iword (&3761513),iword (&1927777021)) a`,
  GEN_TAC THEN REWRITE_TAC[mldsa_barrett_mul] THEN
  CONV_TAC(DEPTH_CONV WORD_IWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SX_CONV) THEN
  REFL_TAC);;

let RV32_MLDSA_NTT_PHASE1_BODY = prove
 (`!a z:int32. !x:num->int32. !i pc.
      aligned 4 a /\
      i < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 72) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * i)) /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           if j < i then
                             rv32_mldsa_ntt_phase1 x j r
                           else x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 204) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * (i + 1))) /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           if j < i + 1 then
                             rv32_mldsa_ntt_phase1 x j r
                           else x (j + 64 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4 (word_add a (word(4 * i)):int32)`
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
               `!r j. r < 4 /\ j < 64
                      ==> read
                           (memory :>
                            bytes32
                             (word_add (a:int32)
                              (word(4 * (j + 64 * r)))))
                           (s0:riscvstate) =
                          if j < i then
                            rv32_mldsa_ntt_phase1
                              (x:num->int32) j r
                          else x (j + 64 * r)`)
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
              NUM_RING `4 * (k + 0) = 4 * k`;
              NUM_RING `4 * (k + 64) = 4 * k + 256`;
              NUM_RING `4 * (k + 128) = 4 * k + 512`;
              NUM_RING `4 * (k + 192) = 4 * k + 768`]
             (MP
               (SPECL [mk_small_numeral r; `i:num`] th)
               (CONJ
                 (EQT_ELIM
                   (NUM_REDUCE_CONV
                     (mk_binop `(<)`
                       (mk_small_numeral r)
                       (mk_small_numeral 4))))
                 (ASSUME `i < 64`))))))
   (0--3) THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--28) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s28:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s29" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s30" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s31" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s32" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!r j. r < 4 /\ j < 64
          ==> read
               (memory :>
                bytes32
                 (word_add a
                  (word(4 * (j + 64 * r))))) s32 =
              if j < i + 1 then
                rv32_mldsa_ntt_phase1 x j r
              else x (j + 64 * r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    ASM_CASES_TAC `j:num = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN
       `r = 0 \/ r = 1 \/ r = 2 \/ r = 3`
      MP_TAC THENL
       [ASM_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (k + 0) = 4 * k`;
        NUM_RING `4 * (k + 64) = 4 * k + 256`;
        NUM_RING `4 * (k + 128) = 4 * k + 512`;
        NUM_RING `4 * (k + 192) = 4 * k + 768`] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC
       [rv32_mldsa_ntt_phase1; rv32_mldsa_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_BODY_UPDATES_TAC THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_PAIR0;
        RV32_MLDSA_BARRETT_PAIR1;
        RV32_MLDSA_BARRETT_PAIR2] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES];
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32) (word(4 * (j + 64 * r)))))
           : (riscvstate,int32)component)
          (memory :> bytes32
            (word_add a (word(4 * (i + 64 * 0)))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC
         (SPECL [`a:int32`; `i:num`; `j:num`; `r:num`; `0`]
           RV32_NTT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32) (word(4 * (j + 64 * r)))))
           : (riscvstate,int32)component)
          (memory :> bytes32
            (word_add a (word(4 * (i + 64 * 1)))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC
         (SPECL [`a:int32`; `i:num`; `j:num`; `r:num`; `1`]
           RV32_NTT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32) (word(4 * (j + 64 * r)))))
           : (riscvstate,int32)component)
          (memory :> bytes32
            (word_add a (word(4 * (i + 64 * 2)))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC
         (SPECL [`a:int32`; `i:num`; `j:num`; `r:num`; `2`]
           RV32_NTT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32) (word(4 * (j + 64 * r)))))
           : (riscvstate,int32)component)
          (memory :> bytes32
            (word_add a (word(4 * (i + 64 * 3)))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC
         (SPECL [`a:int32`; `i:num`; `j:num`; `r:num`; `3`]
           RV32_NTT_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      RULE_ASSUM_TAC
       (REWRITE_RULE
         [ARITH;
          NUM_RING `4 * (k + 0) = 4 * k`;
          NUM_RING `4 * (k + 64) = 4 * k + 256`;
          NUM_RING `4 * (k + 128) = 4 * k + 512`;
          NUM_RING `4 * (k + 192) = 4 * k + 768`]) THEN
      ASM_REWRITE_TAC[] THEN
      RV32_NTT_REWRITE_STORES_TAC THEN
      REWRITE_TAC
       [ARITH;
        NUM_RING `4 * (k + 0) = 4 * k`;
        NUM_RING `4 * (k + 64) = 4 * k + 256`;
        NUM_RING `4 * (k + 128) = 4 * k + 512`;
        NUM_RING `4 * (k + 192) = 4 * k + 768`] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      W(fun (asl,w) ->
          let l,_ = dest_eq w in
          TRANS_TAC EQ_TRANS
           (mk_comb(rator l,`s28:riscvstate`))) THEN
      CONJ_TAC THENL
       [RV32_NTT_READ_OVER_WRITES_TAC;
        USE_THEN "prestore_memory"
         (fun th ->
            MATCH_MP_TAC th THEN
            ASM_REWRITE_TAC[])]];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s32" THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s33" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE1_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !i pc.
      0 < i /\ i < 64
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 204) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * i)) /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           if j < i then
                             rv32_mldsa_ntt_phase1 x j r
                           else x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 72) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = word_add a (word(4 * i)) /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           if j < i then
                             rv32_mldsa_ntt_phase1 x j r
                           else x (j + 64 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(4 * i)):int32 =
      word_add a (word 256))`
  ASSUME_TAC THENL
   [REWRITE_TAC[
      WORD_RULE
       `word_add a (word x):int32 = word_add a (word y) <=>
        (word x:int32) = word y`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `4 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RV32_MLDSA_NTT_PHASE1_EXIT = prove
 (`!a z:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 204) /\
            read T0 s = word 8380417 /\
            read S0 s = iword (-- &3572223) /\
            read S1 s = iword (-- &1830765815) /\
            read S2 s = iword (&3765607) /\
            read S3 s = iword (&1929875198) /\
            read S4 s = iword (&3761513) /\
            read S5 s = iword (&1927777021) /\
            read A0 s = a /\
            read A1 s = z /\
            read T2 s = word_add a (word(4 * 64)) /\
            read T4 s = word_add a (word 256) /\
            (!r j. r < 4 /\ j < 64
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (j + 64 * r))))) s =
                       if j < 64 then
                         rv32_mldsa_ntt_phase1 x j r
                       else x (j + 64 * r)))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 212) /\
            read T0 s = word 8380417 /\
            read S0 s = iword (-- &3572223) /\
            read S1 s = iword (-- &1830765815) /\
            read S2 s = iword (&3765607) /\
            read S3 s = iword (&1929875198) /\
            read S4 s = iword (&3761513) /\
            read S5 s = iword (&1927777021) /\
            read A0 s = a /\
            read A1 s = z /\
            read T2 s = a /\
            read T4 s = word_add a (word 256) /\
            (!r j. r < 4 /\ j < 64
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (j + 64 * r))))) s =
                       rv32_mldsa_ntt_phase1 x j r))
       (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
      LABEL_TAC "phase1_memory" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "exit_branch" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s2" None
   (fun th -> LABEL_TAC "exit_reset" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "exit_reset"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "exit_branch"
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    USE_THEN "phase1_memory"
     (fun th ->
        let sth = SPECL [`r:num`; `j:num`] th in
        FIRST_ASSUM
         (fun hr ->
            let hr' =
              check
               (fun th -> aconv (concl th) `r < 4`)
               hr in
            FIRST_ASSUM
             (fun hj ->
                let hj' =
                  check
                   (fun th -> aconv (concl th) `j < 64`)
                   hj in
                ACCEPT_TAC
                 (REWRITE_RULE[hj']
                   (MP sth (CONJ hr' hj')))))))));;

let RV32_MLDSA_NTT_PHASE1_LOOP = prove
 (`!a z:int32. !x:num->int32. !pc.
      aligned 4 a /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 72) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = a /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 212) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s = a /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           rv32_mldsa_ntt_phase1 x j r))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `64` `pc + 72` `pc + 204`
   `\i s.
      read T0 s = word 8380417 /\
      read S0 s = iword (-- &3572223) /\
      read S1 s = iword (-- &1830765815) /\
      read S2 s = iword (&3765607) /\
      read S3 s = iword (&1929875198) /\
      read S4 s = iword (&3761513) /\
      read S5 s = iword (&1927777021) /\
      read A0 s = a /\
      read A1 s = z /\
      read T2 s = word_add a (word(4 * i)) /\
      read T4 s = word_add a (word 256) /\
      (!r j. r < 4 /\ j < 64
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (j + 64 * r))))) s =
                 if j < i then
                   rv32_mldsa_ntt_phase1 x j r
                 else x (j + 64 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ARITH_RULE `~(j < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`; `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE1_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`; `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE1_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC
     (SPECL [`a:int32`; `z:int32`; `x:num->int32`; `pc:num`]
       RV32_MLDSA_NTT_PHASE1_EXIT)]);;

let RV32_MLDSA_NTT_PHASE1 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 28) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 212) /\
                read T0 s = word 8380417 /\
                read S0 s = iword (-- &3572223) /\
                read S1 s = iword (-- &1830765815) /\
                read S2 s = iword (&3765607) /\
                read S3 s = iword (&1929875198) /\
                read S4 s = iword (&3761513) /\
                read S5 s = iword (&1927777021) /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
                read T2 s = a /\
                read T4 s = word_add a (word 256) /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           rv32_mldsa_ntt_phase1 x j r))
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC; C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 72`
   `\s. read T0 s = word 8380417 /\
        read S0 s = iword (-- &3572223) /\
        read S1 s = iword (-- &1830765815) /\
        read S2 s = iword (&3765607) /\
        read S3 s = iword (&1929875198) /\
        read S4 s = iword (&3761513) /\
        read S5 s = iword (&1927777021) /\
        read A0 s = a /\
        read A1 s = word_add zetas (word 24) /\
        read T2 s = a /\
        read T4 s = word_add a (word 256) /\
        (!r j. r < 4 /\ j < 64
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word(4 * (j + 64 * r))))) s =
                   x (j + 64 * r))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL [`a:int32`; `zetas:int32`; `pc:num`]
         RV32_MLDSA_NTT_PHASE1_SETUP)
       (ASSUME `aligned 4 (zetas:int32)`)) THEN
    RISCV_BIGSTEP_TAC MLDSA_NTT_EXEC "s1" THENL
     [REWRITE_TAC[C_ARGUMENTS] THEN ASM_REWRITE_TAC[];
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC
       (SPECL
         [`a:int32`; `word_add zetas (word 24):int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_NTT_PHASE1_LOOP) THEN
      ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC]]]);;

needs "riscv/proofs/mldsa_ntt_layout.ml";;

(* ------------------------------------------------------------------------- *)
(* Phase 2.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_NTT_PHASE2_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 216) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * g)) /\
                read T2 s =
                  word_add a (word(256 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (\s. read PC s = word(pc + 248) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(256 * g)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(256 * g + 64)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T4] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add zetas (word(24 + 24 * g)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_ADD THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN
        CONV_TAC NUM_DIVIDES_CONV]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
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
      let tm =
        subst
         [mk_small_numeral n,`n:num`]
         `6 + 6 * g + n` in
      USE_THEN "table_reads"
       (fun th -> MP_TAC(SPEC tm th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let index_tm =
        mk_binop `(+):num->num->num`
         (mk_small_numeral (6 + n))
         (mk_binop `(*):num->num->num`
           (mk_small_numeral 6) `g:num`) in
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
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add
               (word_add zetas (word(24 + 24 * g)))
               (word(4 * n)))) s0 =
          iword(EL (6 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add
             (word_add zetas (word(24 + 24 * g)))
             (word(4 * n)):int32 =
            word_add zetas
             (word(4 * (6 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let ntm = mk_small_numeral n in
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add zetas
               (word((24 + 24 * g) + 4 * n)))) s0 =
          iword(EL (6 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add zetas
             (word((24 + 24 * g) + 4 * n)):int32 =
            word_add zetas
             (word(4 * (6 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  REWRITE_TAC[rv32_mldsa_ntt_pair; FST; SND] THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("setup" ^ string_of_int n) th THEN
          STRIP_TAC))
   (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC
   [NUM_RING `2 * (3 + 3 * g) = 6 + 6 * g`;
    NUM_RING `2 * (3 + 3 * g) + 1 = 7 + 6 * g`;
    NUM_RING `2 * (4 + 3 * g) = 8 + 6 * g`;
    NUM_RING `2 * (4 + 3 * g) + 1 = 9 + 6 * g`;
    NUM_RING `2 * (5 + 3 * g) = 10 + 6 * g`;
    NUM_RING `2 * (5 + 3 * g) + 1 = 11 + 6 * g`;
    NUM_RING `6 + 6 * g + 1 = 7 + 6 * g`;
    NUM_RING `6 + 6 * g + 2 = 8 + 6 * g`;
    NUM_RING `6 + 6 * g + 3 = 9 + 6 * g`;
    NUM_RING `6 + 6 * g + 4 = 10 + 6 * g`;
    NUM_RING `6 + 6 * g + 5 = 11 + 6 * g`;
    NUM_RING `24 + 24 * g = 4 * (6 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 4 = 4 * (7 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 8 = 4 * (8 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 12 = 4 * (9 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 16 = 4 * (10 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 20 = 4 * (11 + 6 * g)`] THEN
  MAP_EVERY
   (fun n ->
      USE_THEN ("setup" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--8)) THEN
  REWRITE_TAC
   [NUM_RING `24 + 24 * g = 4 * (6 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 4 = 4 * (7 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 8 = 4 * (8 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 12 = 4 * (9 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 16 = 4 * (10 + 6 * g)`;
    NUM_RING `(24 + 24 * g) + 20 = 4 * (11 + 6 * g)`] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE2_BODY = prove
 (`!a z:int32. !x:num->int32. !g j pc.
      aligned 4 a /\
      g < 4 /\
      j < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 248) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g + 4 * j)) /\
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
                             if h < g \/ h = g /\ l < j then
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 380) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(256 * g + 4 * (j + 1))) /\
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
                             if h < g \/ h = g /\ l < j + 1 then
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
              `!h l r. h < 4 /\ l < 16 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add (a:int32)
                               (word
                                 (4 * (64 * h + l + 16 * r)))))
                            (s0:riscvstate) =
                           if h < g \/ h = g /\ l < j then
                             rv32_mldsa_ntt_phase2
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
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--28) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s28:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s29" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s30" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s31" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s32" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h l r. h < 4 /\ l < 16 /\ r < 4
            ==> read
                 (memory :>
                  bytes32
                   (word_add a
                    (word
                      (4 * (64 * h + l + 16 * r))))) s32 =
                if h < g \/ h = g /\ l < j + 1 then
                  rv32_mldsa_ntt_phase2 x h l r
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
       [rv32_mldsa_ntt_phase2; rv32_mldsa_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_PAIR;
        ARITH_RULE `g < g \/ j < j + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase2_not_current") THEN
      SUBGOAL_THEN
       `!q. q < 4
            ==> orthogonal_components
                 ((memory :> bytes32
                   (word_add (a:int32)
                    (word
                      (4 * (64 * h + l + 16 * r)))))
                  : (riscvstate,int32)component)
                 (memory :> bytes32
                   (word_add a
                    (word
                      (4 * (64 * g + j + 16 * q)))))`
      (LABEL_TAC "phase2_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `h:num`; `l:num`; `r:num`;
            `g:num`; `j:num`; `q:num`]
           RV32_NTT_PHASE2_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "phase2_not_current" ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "phase2_orthogonal"
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
               ("phase2_orthogonal" ^ string_of_int q)
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
        USE_THEN "phase2_not_current" ACCEPT_TAC;
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
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (64 * h + l + 16 * r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase2_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (64 * h + l + 16 * r)))))
           : (riscvstate,int32)component)
          events`
      (LABEL_TAC "phase2_events_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      USE_THEN "phase2_orthogonal0"
       (fun orth0 ->
          USE_THEN "phase2_orthogonal1"
           (fun orth1 ->
              USE_THEN "phase2_orthogonal2"
               (fun orth2 ->
                  USE_THEN "phase2_orthogonal3"
                   (fun orth3 ->
                      USE_THEN "phase2_pc_orthogonal"
                       (fun orthpc ->
                          USE_THEN "phase2_events_orthogonal"
                           (fun orthevents ->
                              SIMP_TAC
                               [READ_WRITE_ORTHOGONAL_COMPONENTS;
                                orth0; orth1; orth2; orth3;
                                orthpc; orthevents]))))))];
    ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s32" THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s33" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE2_INNER_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !g i pc.
      g < 4 /\ 0 < i /\ i < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 380) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 248) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;


let RV32_MLDSA_NTT_PHASE2_INNER_EXIT = prove
 (`!a z:int32. !x:num->int32. !g pc.
      g < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 380) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 388) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
      LABEL_TAC "phase2_memory" th') THEN
  SUBGOAL_THEN
   `!h l r. h < 4 /\ l < 16 /\ r < 4
            ==> read
                 (memory :>
                  bytes32
                   (word_add a
                    (word
                      (4 * (64 * h + l + 16 * r))))) s0 =
                if h < g + 1 then
                  rv32_mldsa_ntt_phase2 x h l r
                else x (64 * h + l + 16 * r)`
  (LABEL_TAC "phase2_memory_done") THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
    STRIP_TAC THEN
    USE_THEN "phase2_memory"
     (MP_TAC o SPECL [`h:num`; `l:num`; `r:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    SUBGOAL_THEN
     `(h < g \/ h = g /\ l < 16) <=> h < g + 1`
    (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "inner_exit_branch" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s2" None
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
    USE_THEN "phase2_memory_done"
     (fun th ->
        MATCH_MP_TAC(SPECL [`h:num`; `l:num`; `r:num`] th)) THEN
    ASM_REWRITE_TAC[])));;


let RV32_MLDSA_NTT_PHASE2_INNER_LOOP = prove
 (`!a z:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 248) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 388) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `16` `pc + 248` `pc + 380`
   `\i s.
      read T0 s = word 8380417 /\
      read S0 s =
        FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
      read S1 s =
        SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
      read S2 s =
        FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
      read S3 s =
        SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
      read S4 s =
        FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
      read S5 s =
        SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
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
                     rv32_mldsa_ntt_phase2 x h l r
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
       RV32_MLDSA_NTT_PHASE2_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE2_INNER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE2_INNER_EXIT) THEN
    ASM_REWRITE_TAC[]]);;

let RV32_MLDSA_NTT_PHASE2_OUTER_BACKEDGE = prove
 (`!a zetas:int32. !x:num->int32. !i pc.
      0 < i /\ i < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 388) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * i)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 216) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * i)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;


let RV32_MLDSA_NTT_PHASE2_OUTER_EXIT = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 388) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 120) /\
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
                         rv32_mldsa_ntt_phase2 x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 396) /\
            read T0 s = word 8380417 /\
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
                         rv32_mldsa_ntt_phase2 x h l r))
       (MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1;2] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC
    [RV32_WORDLIST_PRESERVED_BY_OUTER_EXIT_MAYCHANGE]));;

let RV32_MLDSA_NTT_PHASE2_INNER_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 248) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(24 + 24 * (g + 1))) /\
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
                              rv32_mldsa_ntt_phase2 x h l r
                            else x (64 * h + l + 16 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 388) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(24 + 24 * (g + 1))) /\
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
                              rv32_mldsa_ntt_phase2 x h l r
                            else x (64 * h + l + 16 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
        `word_add zetas (word(24 + 24 * (g + 1))):int32`;
        `x:num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE2_INNER_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC]]);;

let RV32_MLDSA_NTT_PHASE2_OUTER_BODY = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 216) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * g)) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 388) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(24 + 24 * (g + 1))) /\
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
                               rv32_mldsa_ntt_phase2 x h l r
                             else x (64 * h + l + 16 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "setup_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 248`
   `\s. read T0 s = word 8380417 /\
        read S0 s =
          FST(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
        read S1 s =
          SND(rv32_mldsa_ntt_pair (3 + 3 * g)) /\
        read S2 s =
          FST(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
        read S3 s =
          SND(rv32_mldsa_ntt_pair (4 + 3 * g)) /\
        read S4 s =
          FST(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
        read S5 s =
          SND(rv32_mldsa_ntt_pair (5 + 3 * g)) /\
        read A0 s = a /\
        read A1 s =
          word_add zetas (word(24 + 24 * (g + 1))) /\
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
                       rv32_mldsa_ntt_phase2 x h l r
                     else x (64 * h + l + 16 * r))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL
         [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
         RV32_MLDSA_NTT_PHASE2_OUTER_SETUP)
       (CONJ
         (ASSUME `aligned 4 (zetas:int32)`)
         (ASSUME `g < 4`))) THEN
    RISCV_BIGSTEP_TAC MLDSA_NTT_EXEC "s1" THEN
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
         RV32_MLDSA_NTT_PHASE2_INNER_LOOP_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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


let RV32_MLDSA_NTT_PHASE2_OUTER_LOOP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 216) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 24) /\
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
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 396) /\
                read T0 s = word 8380417 /\
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
                             rv32_mldsa_ntt_phase2 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `4` `pc + 216` `pc + 388`
   `\i s.
      read T0 s = word 8380417 /\
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(24 + 24 * i)) /\
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
                     rv32_mldsa_ntt_phase2 x h l r
                   else x (64 * h + l + 16 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(h < 0)`];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
       `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE2_OUTER_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
       `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE2_OUTER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    ENSURES_PRECONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
          read PC s = word(pc + 388) /\
          read T0 s = word 8380417 /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 120) /\
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
                       rv32_mldsa_ntt_phase2 x h l r)` THEN
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
         RV32_MLDSA_NTT_PHASE2_OUTER_EXIT)]]);;

let RV32_MLDSA_NTT_PHASE1_TABLE_PRESERVED = prove
 (`!a zetas:int32. !s s':riscvstate.
      nonoverlapping (a,1024) (zetas,2040) /\
      (MAYCHANGE
        [PC; T0; S0; S1; S2; S3; S4; S5;
         A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
       MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events]) s s'
      ==> wordlist_from_memory(zetas,510) s':int32 list =
          wordlist_from_memory(zetas,510) s`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `s:riscvstate`; `s':riscvstate`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC
   (ISPECL
     [`memory :> bytes(zetas,2040)`;
      `MAYCHANGE
        [PC; T0; S0; S1; S2; S3; S4; S5;
         A1; T2; T4; A2; A3; A4; A5; A6; A7]`;
      `MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events]`;
      `s:riscvstate`; `s':riscvstate`]
     SEQ_PRESERVES_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory :> bytes(zetas,2040)`;
        `[PC; T0; S0; S1; S2; S3; S4; S5;
          A1; T2; T4; A2; A3; A4; A5; A6; A7]`;
        `u:riscvstate`; `v:riscvstate`]
       MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
    ASM_REWRITE_TAC[ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
    MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory :> bytes(zetas,2040)`;
        `MAYCHANGE [memory :> bytes(a,1024)]`;
        `MAYCHANGE [events]`;
        `u:riscvstate`; `v:riscvstate`]
       SEQ_PRESERVES_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`w:riscvstate`; `x:riscvstate`] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC
       (ISPECL
         [`memory :> bytes(zetas,2040)`;
          `[memory :> bytes(a,1024)]`;
          `w:riscvstate`; `x:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN
      ORTHOGONAL_COMPONENTS_TAC;
      MAP_EVERY X_GEN_TAC [`w:riscvstate`; `x:riscvstate`] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC
       (ISPECL
         [`memory :> bytes(zetas,2040)`;
          `[events]`;
          `w:riscvstate`; `x:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN
      ORTHOGONAL_COMPONENTS_TAC]]);;


let RV32_MLDSA_NTT_PHASE1_TABLE_RAW = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 28) /\
               C_ARGUMENTS [a;zetas] s /\
               wordlist_from_memory(zetas,510) s:int32 list =
               MAP iword rv32_mldsa_ntt_zetas /\
               (!r j. r < 4 /\ j < 64
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (j + 64 * r))))) s =
                          x (j + 64 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 212) /\
               read T0 s = word 8380417 /\
               read S0 s = iword (-- &3572223) /\
               read S1 s = iword (-- &1830765815) /\
               read S2 s = iword (&3765607) /\
               read S3 s = iword (&1929875198) /\
               read S4 s = iword (&3761513) /\
               read S5 s = iword (&1927777021) /\
               read A0 s = a /\
               read A1 s = word_add zetas (word 24) /\
               read T2 s = a /\
               read T4 s = word_add a (word 256) /\
               (!r j. r < 4 /\ j < 64
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (j + 64 * r))))) s =
                          rv32_mldsa_ntt_phase1 x j r)) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:riscvstate`; `s':riscvstate`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (LABEL_TAC "table_before")
       (LABEL_TAC "phase1_frame")) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s:int32 list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `s:riscvstate`; `s':riscvstate`]
         RV32_MLDSA_NTT_PHASE1_TABLE_PRESERVED) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "table_before" ACCEPT_TAC];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`;
       `x:num->int32`; `pc:num`]
       RV32_MLDSA_NTT_PHASE1) THEN
    ASM_REWRITE_TAC[]]);;


let RV32_MLDSA_NTT_PHASE2_ENTRY = prove
 (`!a:int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 212) /\
            read A0 s = a)
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 216) /\
            read A0 s = a /\
            read T3 s = word_add a (word 1024))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_NTT_PHASE2_ENTRY_FULL = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 212) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 24) /\
            read T2 s = a /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!r j. r < 4 /\ j < 64
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (j + 64 * r))))) s =
                       rv32_mldsa_ntt_phase1 x j r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 216) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 24) /\
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
                         rv32_mldsa_ntt_phase1 x
                          ((64 * h + l + 16 * r) MOD 64)
                          ((64 * h + l + 16 * r) DIV 64)))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
      LABEL_TAC "phase1_memory" th') THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            can
             (term_match []
               `wordlist_from_memory(zetas,510) (s0:riscvstate):
                  int32 list =
                MAP iword rv32_mldsa_ntt_zetas`)
             (concl th))
         th in
      LABEL_TAC "table_before" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "entry_step" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   RV32_NTT_PHASE12_TABLE_TAC ORELSE
   RV32_NTT_PHASE12_UPDATED_COEFFICIENT_TAC));;


let RV32_MLDSA_NTT_PHASE12 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 28) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 396) /\
                read T0 s = word 8380417 /\
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
                             rv32_mldsa_ntt_phase12 x h l r))
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 212`
   `\s.
      (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
       read PC s = word(pc + 212) /\
       read T0 s = word 8380417 /\
       read S0 s = iword (-- &3572223) /\
       read S1 s = iword (-- &1830765815) /\
       read S2 s = iword (&3765607) /\
       read S3 s = iword (&1929875198) /\
       read S4 s = iword (&3761513) /\
       read S5 s = iword (&1927777021) /\
       read A0 s = a /\
       read A1 s = word_add zetas (word 24) /\
       read T2 s = a /\
       read T4 s = word_add a (word 256) /\
       (!r j. r < 4 /\ j < 64
              ==> read
                   (memory :>
                    bytes32
                     (word_add a
                      (word(4 * (j + 64 * r))))) s =
                  rv32_mldsa_ntt_phase1 x j r)) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE
       [PC; T0; S0; S1; S2; S3; S4; S5;
        A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
      MAYCHANGE [memory :> bytes(a,1024)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->int32`; `pc:num`]
         RV32_MLDSA_NTT_PHASE1_TABLE_RAW) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC];
    ENSURES_SEQUENCE_TAC `pc + 216`
     `\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
          read PC s = word(pc + 216) /\
          read T0 s = word 8380417 /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 24) /\
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
                       rv32_mldsa_ntt_phase1 x
                        ((64 * h + l + 16 * r) MOD 64)
                        ((64 * h + l + 16 * r) DIV 64))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC; T3] ,, MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        RV32_NTT_USE_STRONGER_PRE_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `x:num->int32`; `pc:num`]
           RV32_MLDSA_NTT_PHASE2_ENTRY_FULL)];
      REWRITE_TAC[rv32_mldsa_ntt_phase12] THEN
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MP_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `\n. rv32_mldsa_ntt_phase1
                  x (n MOD 64) (n DIV 64)`;
            `pc:num`]
           RV32_MLDSA_NTT_PHASE2_OUTER_LOOP) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 3.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_NTT_PHASE3_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 400) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * g)) /\
                read T2 s =
                  word_add a (word(64 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (\s. read PC s = word(pc + 432) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(64 * g)) /\
                read T3 s = word_add a (word 1024) /\
                read T4 s =
                  word_add a (word(64 * g + 16)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1; T4] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add zetas (word(120 + 24 * g)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_ADD THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN
        CONV_TAC NUM_DIVIDES_CONV]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
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
      let tm =
        subst
         [mk_small_numeral n,`n:num`]
         `30 + 6 * g + n` in
      USE_THEN "table_reads"
       (fun th -> MP_TAC(SPEC tm th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let index_tm =
        mk_binop `(+):num->num->num`
         (mk_small_numeral (30 + n))
         (mk_binop `(*):num->num->num`
           (mk_small_numeral 6) `g:num`) in
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
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add
               (word_add zetas (word(120 + 24 * g)))
               (word(4 * n)))) s0 =
          iword(EL (30 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add
             (word_add zetas (word(120 + 24 * g)))
             (word(4 * n)):int32 =
            word_add zetas
             (word(4 * (30 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let ntm = mk_small_numeral n in
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add zetas
               (word((120 + 24 * g) + 4 * n)))) s0 =
          iword(EL (30 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add zetas
             (word((120 + 24 * g) + 4 * n)):int32 =
            word_add zetas
             (word(4 * (30 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  REWRITE_TAC[rv32_mldsa_ntt_pair; FST; SND] THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("setup" ^ string_of_int n) th THEN
          STRIP_TAC))
   (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC
   [NUM_RING `2 * (15 + 3 * g) = 30 + 6 * g`;
    NUM_RING `2 * (15 + 3 * g) + 1 = 31 + 6 * g`;
    NUM_RING `2 * (16 + 3 * g) = 32 + 6 * g`;
    NUM_RING `2 * (16 + 3 * g) + 1 = 33 + 6 * g`;
    NUM_RING `2 * (17 + 3 * g) = 34 + 6 * g`;
    NUM_RING `2 * (17 + 3 * g) + 1 = 35 + 6 * g`;
    NUM_RING `30 + 6 * g + 1 = 31 + 6 * g`;
    NUM_RING `30 + 6 * g + 2 = 32 + 6 * g`;
    NUM_RING `30 + 6 * g + 3 = 33 + 6 * g`;
    NUM_RING `30 + 6 * g + 4 = 34 + 6 * g`;
    NUM_RING `30 + 6 * g + 5 = 35 + 6 * g`;
    NUM_RING `120 + 24 * g = 4 * (30 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 4 = 4 * (31 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 8 = 4 * (32 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 12 = 4 * (33 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 16 = 4 * (34 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 20 = 4 * (35 + 6 * g)`] THEN
  MAP_EVERY
   (fun n ->
      USE_THEN ("setup" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--8)) THEN
  REWRITE_TAC
   [NUM_RING `120 + 24 * g = 4 * (30 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 4 = 4 * (31 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 8 = 4 * (32 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 12 = 4 * (33 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 16 = 4 * (34 + 6 * g)`;
    NUM_RING `(120 + 24 * g) + 20 = 4 * (35 + 6 * g)`] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE3_ENTRY = prove
 (`!a:int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 396) /\
            read A0 s = a)
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 400) /\
            read A0 s = a /\
            read T3 s = word_add a (word 1024))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_NTT_PHASE3_BODY = prove
 (`!a z:int32. !x:num->int32. !g j pc.
      aligned 4 a /\
      g < 16 /\
      j < 4 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 432) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g + 4 * j)) /\
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
                             if h < g \/ h = g /\ l < j then
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 564) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(64 * g + 4 * (j + 1))) /\
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
                             if h < g \/ h = g /\ l < j + 1 then
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
              `!h l r. h < 16 /\ l < 4 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add (a:int32)
                               (word
                                 (4 * (16 * h + l + 4 * r)))))
                            (s0:riscvstate) =
                           if h < g \/ h = g /\ l < j then
                             rv32_mldsa_ntt_phase3
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
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--28) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s28:riscvstate` (concl th) &&
           vfree_in `x:num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s29" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s30" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s31" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s32" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h l r. h < 16 /\ l < 4 /\ r < 4
            ==> read
                 (memory :>
                  bytes32
                   (word_add a
                    (word
                      (4 * (16 * h + l + 4 * r))))) s32 =
                if h < g \/ h = g /\ l < j + 1 then
                  rv32_mldsa_ntt_phase3 x h l r
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
       [rv32_mldsa_ntt_phase3; rv32_mldsa_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_PAIR;
        ARITH_RULE `g < g \/ j < j + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase3_not_current") THEN
      SUBGOAL_THEN
       `!q. q < 4
            ==> orthogonal_components
                 ((memory :> bytes32
                   (word_add (a:int32)
                    (word
                      (4 * (16 * h + l + 4 * r)))))
                  : (riscvstate,int32)component)
                 (memory :> bytes32
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
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (16 * h + l + 4 * r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase3_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
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
  DISCARD_OLDSTATE_TAC "s32" THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s33" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE3_INNER_BACKEDGE = prove
 (`!a z:int32. !x:num->int32. !g i pc.
      g < 16 /\ 0 < i /\ i < 4
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 564) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 432) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RV32_MLDSA_NTT_PHASE3_INNER_EXIT = prove
 (`!a z:int32. !x:num->int32. !g pc.
      g < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 564) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 572) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
                  rv32_mldsa_ntt_phase3 x h l r
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
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "inner_exit_branch" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s2" None
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

let RV32_MLDSA_NTT_PHASE3_INNER_LOOP = prove
 (`!a z:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 432) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 572) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `4` `pc + 432` `pc + 564`
   `\i s.
      read T0 s = word 8380417 /\
      read S0 s =
        FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
      read S1 s =
        SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
      read S2 s =
        FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
      read S3 s =
        SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
      read S4 s =
        FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
      read S5 s =
        SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
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
                     rv32_mldsa_ntt_phase3 x h l r
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
       RV32_MLDSA_NTT_PHASE3_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE3_INNER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `z:int32`; `x:num->int32`;
        `g:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE3_INNER_EXIT) THEN
    ASM_REWRITE_TAC[]]);;

let RV32_MLDSA_NTT_PHASE3_OUTER_BACKEDGE = prove
 (`!a zetas:int32. !x:num->int32. !i pc.
      0 < i /\ i < 16
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 572) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * i)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 400) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * i)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;

let RV32_MLDSA_NTT_PHASE3_OUTER_EXIT = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 572) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 504) /\
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
                         rv32_mldsa_ntt_phase3 x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 580) /\
            read T0 s = word 8380417 /\
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
                         rv32_mldsa_ntt_phase3 x h l r))
       (MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1;2] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC
    [RV32_WORDLIST_PRESERVED_BY_OUTER_EXIT_MAYCHANGE]));;

let RV32_MLDSA_NTT_PHASE3_INNER_LOOP_TABLE = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 432) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(120 + 24 * (g + 1))) /\
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
                              rv32_mldsa_ntt_phase3 x h l r
                            else x (16 * h + l + 4 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 572) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(120 + 24 * (g + 1))) /\
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
                              rv32_mldsa_ntt_phase3 x h l r
                            else x (16 * h + l + 4 * r))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
        `word_add zetas (word(120 + 24 * (g + 1))):int32`;
        `x:num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE3_INNER_LOOP) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC]]);;

let RV32_MLDSA_NTT_PHASE3_OUTER_BODY = prove
 (`!a zetas:int32. !x:num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 16 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 400) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * g)) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 572) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(120 + 24 * (g + 1))) /\
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
                               rv32_mldsa_ntt_phase3 x h l r
                             else x (16 * h + l + 4 * r)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "setup_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 432`
   `\s. read T0 s = word 8380417 /\
        read S0 s =
          FST(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
        read S1 s =
          SND(rv32_mldsa_ntt_pair (15 + 3 * g)) /\
        read S2 s =
          FST(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
        read S3 s =
          SND(rv32_mldsa_ntt_pair (16 + 3 * g)) /\
        read S4 s =
          FST(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
        read S5 s =
          SND(rv32_mldsa_ntt_pair (17 + 3 * g)) /\
        read A0 s = a /\
        read A1 s =
          word_add zetas (word(120 + 24 * (g + 1))) /\
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
                       rv32_mldsa_ntt_phase3 x h l r
                     else x (16 * h + l + 4 * r))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL
         [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
         RV32_MLDSA_NTT_PHASE3_OUTER_SETUP)
       (CONJ
         (ASSUME `aligned 4 (zetas:int32)`)
         (ASSUME `g < 16`))) THEN
    RISCV_BIGSTEP_TAC MLDSA_NTT_EXEC "s1" THEN
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
         RV32_MLDSA_NTT_PHASE3_INNER_LOOP_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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

let RV32_MLDSA_NTT_PHASE3_OUTER_LOOP = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 400) /\
                read T0 s = word 8380417 /\
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
                             x (16 * h + l + 4 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 580) /\
                read T0 s = word 8380417 /\
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
                             rv32_mldsa_ntt_phase3 x h l r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `16` `pc + 400` `pc + 572`
   `\i s.
      read T0 s = word 8380417 /\
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(120 + 24 * i)) /\
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
                     rv32_mldsa_ntt_phase3 x h l r
                   else x (16 * h + l + 4 * r))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(h < 0)`];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE3_OUTER_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE3_OUTER_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    ENSURES_PRECONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
          read PC s = word(pc + 572) /\
          read T0 s = word 8380417 /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 504) /\
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
                       rv32_mldsa_ntt_phase3 x h l r)` THEN
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
         RV32_MLDSA_NTT_PHASE3_OUTER_EXIT)]]);;

let RV32_MLDSA_NTT_PHASE3_ENTRY_FULL = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 396) /\
            read T0 s = word 8380417 /\
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
                         rv32_mldsa_ntt_phase12 x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 400) /\
            read T0 s = word 8380417 /\
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
                         rv32_mldsa_ntt_phase12 x
                          ((16 * h + l + 4 * r) DIV 64)
                          ((16 * h + l + 4 * r) MOD 16)
                          (((16 * h + l + 4 * r) DIV 16) MOD 4)))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
      LABEL_TAC "phase12_memory" th') THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            can
             (term_match []
               `wordlist_from_memory(zetas,510) (s0:riscvstate):
                  int32 list =
                MAP iword rv32_mldsa_ntt_zetas`)
             (concl th))
         th in
      LABEL_TAC "table_before" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "entry_step" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   RV32_NTT_PHASE12_TABLE_TAC ORELSE
   RV32_NTT_PHASE123_UPDATED_COEFFICIENT_TAC));;

let RV32_MLDSA_NTT_PHASE123 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 28) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 580) /\
                read T0 s = word 8380417 /\
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
                             rv32_mldsa_ntt_phase123 x h l r))
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 396`
   `\s. read T0 s = word 8380417 /\
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
                     rv32_mldsa_ntt_phase12 x h l r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
       RV32_MLDSA_NTT_PHASE12) THEN
    ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 400`
     `\s. read T0 s = word 8380417 /\
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
                       rv32_mldsa_ntt_phase12 x
                        ((16 * h + l + 4 * r) DIV 64)
                        ((16 * h + l + 4 * r) MOD 16)
                        (((16 * h + l + 4 * r) DIV 16) MOD 4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC; T3] ,, MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        RV32_NTT_USE_STRONGER_PRE_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `x:num->int32`; `pc:num`]
           RV32_MLDSA_NTT_PHASE3_ENTRY_FULL)];
      REWRITE_TAC[rv32_mldsa_ntt_phase123] THEN
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MP_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `\n. rv32_mldsa_ntt_phase12 x
                  (n DIV 64) (n MOD 16) ((n DIV 16) MOD 4)`;
            `pc:num`]
           RV32_MLDSA_NTT_PHASE3_OUTER_LOOP) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN RV32_NTT_USE_STRONGER_PRE_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 4.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RV32_MLDSA_NTT_PHASE4_ENTRY = prove
 (`!a:int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 580) /\
            read A0 s = a /\
            read T2 s = a /\
            read T3 s = word_add a (word 1024))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 584) /\
            read A0 s = a /\
            read T2 s = a /\
            read T3 s = word_add a (word 1024))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let RV32_MLDSA_NTT_PHASE4_OUTER_SETUP = prove
 (`!a zetas:int32. !g pc.
      aligned 4 zetas /\
      g < 64
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 584) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * g)) /\
                read T2 s =
                  word_add a (word(16 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas)
           (\s. read PC s = word(pc + 612) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(16 * g)) /\
                read T3 s = word_add a (word 1024))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5; A1] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add zetas (word(504 + 24 * g)):int32)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_DIVIDES_CONV;
      MATCH_MP_TAC DIVIDES_ADD THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN
        CONV_TAC NUM_DIVIDES_CONV]];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
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
      let tm =
        subst
         [mk_small_numeral n,`n:num`]
         `126 + 6 * g + n` in
      USE_THEN "table_reads"
       (fun th -> MP_TAC(SPEC tm th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let index_tm =
        mk_binop `(+):num->num->num`
         (mk_small_numeral (126 + n))
         (mk_binop `(*):num->num->num`
           (mk_small_numeral 6) `g:num`) in
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
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add
               (word_add zetas (word(504 + 24 * g)))
               (word(4 * n)))) s0 =
          iword(EL (126 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add
             (word_add zetas (word(504 + 24 * g)))
             (word(4 * n)):int32 =
            word_add zetas
             (word(4 * (126 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  MAP_EVERY
   (fun n ->
      let ntm = mk_small_numeral n in
      let read_tm =
        subst
         [ntm,`n:num`]
         `read
           (memory :>
            bytes32
             (word_add zetas
               (word((504 + 24 * g) + 4 * n)))) s0 =
          iword(EL (126 + 6 * g + n) rv32_mldsa_ntt_zetas)` in
      let address_th =
        WORD_RULE
         (subst
           [ntm,`n:num`]
           `word_add zetas
             (word((504 + 24 * g) + 4 * n)):int32 =
            word_add zetas
             (word(4 * (126 + 6 * g + n)))`) in
      SUBGOAL_THEN read_tm ASSUME_TAC THENL
       [REWRITE_TAC[address_th] THEN ASM_REWRITE_TAC[];
        ALL_TAC])
   (0--5) THEN
  REWRITE_TAC[rv32_mldsa_ntt_pair; FST; SND] THEN
  MAP_EVERY
   (fun n ->
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("setup" ^ string_of_int n) th THEN
          STRIP_TAC))
   (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC
   [NUM_RING `2 * (63 + 3 * g) = 126 + 6 * g`;
    NUM_RING `2 * (63 + 3 * g) + 1 = 127 + 6 * g`;
    NUM_RING `2 * (64 + 3 * g) = 128 + 6 * g`;
    NUM_RING `2 * (64 + 3 * g) + 1 = 129 + 6 * g`;
    NUM_RING `2 * (65 + 3 * g) = 130 + 6 * g`;
    NUM_RING `2 * (65 + 3 * g) + 1 = 131 + 6 * g`;
    NUM_RING `126 + 6 * g + 1 = 127 + 6 * g`;
    NUM_RING `126 + 6 * g + 2 = 128 + 6 * g`;
    NUM_RING `126 + 6 * g + 3 = 129 + 6 * g`;
    NUM_RING `126 + 6 * g + 4 = 130 + 6 * g`;
    NUM_RING `126 + 6 * g + 5 = 131 + 6 * g`;
    NUM_RING `504 + 24 * g = 4 * (126 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 4 = 4 * (127 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 8 = 4 * (128 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 12 = 4 * (129 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 16 = 4 * (130 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 20 = 4 * (131 + 6 * g)`] THEN
  MAP_EVERY
   (fun n ->
      USE_THEN ("setup" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--7)) THEN
  REWRITE_TAC
   [NUM_RING `504 + 24 * g = 4 * (126 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 4 = 4 * (127 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 8 = 4 * (128 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 12 = 4 * (129 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 16 = 4 * (130 + 6 * g)`;
    NUM_RING `(504 + 24 * g) + 20 = 4 * (131 + 6 * g)`] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE4_BODY = prove
 (`!a z:int32. !x:num->num->num->int32. !g pc.
      aligned 4 a /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 612) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(16 * g)) /\
                read T3 s = word_add a (word 1024) /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < g then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 744) /\
                read T0 s = word 8380417 /\
                read S0 s =
                  FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S1 s =
                  SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
                read S2 s =
                  FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S3 s =
                  SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
                read S4 s =
                  FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read S5 s =
                  SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
                read A0 s = a /\
                read A1 s = z /\
                read T2 s =
                  word_add a (word(16 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < g + 1 then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `z:int32`; `x:num->num->num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aligned 4
      (word_add a (word(16 * g)):int32)`
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
              `!h r. h < 64 /\ r < 4
                     ==> read
                          (memory :>
                           bytes32
                            (word_add (a:int32)
                             (word(4 * (4 * h + r)))))
                          (s0:riscvstate) =
                         if h < g then
                           rv32_mldsa_ntt_phase4
                            (x:num->num->num->int32) h r
                         else x (h DIV 4) r (h MOD 4)`)
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
      RISCV_STEP_TAC MLDSA_NTT_EXEC []
       ("s" ^ string_of_int n) None
       (fun th ->
          LABEL_TAC ("body" ^ string_of_int n) th THEN
          STRIP_TAC) THEN
      RV32_SIMPLIFY_ABBREV_TAC [mldsa_barrett_mul] [])
   (1--28) THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
           is_forall(concl th) &&
           vfree_in `s28:riscvstate` (concl th) &&
           vfree_in `x:num->num->num->int32` (concl th))
         th in
      LABEL_TAC "prestore_memory" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s29" None
   (fun th -> LABEL_TAC "store0" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s30" None
   (fun th -> LABEL_TAC "store1" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s31" None
   (fun th -> LABEL_TAC "store2" th THEN STRIP_TAC) THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s32" None
   (fun th -> LABEL_TAC "store3" th THEN STRIP_TAC) THEN
  SUBGOAL_THEN
   `!h r. h < 64 /\ r < 4
          ==> read
               (memory :>
                bytes32
                 (word_add a
                  (word(4 * (4 * h + r))))) s32 =
              if h < g + 1 then
                rv32_mldsa_ntt_phase4 x h r
              else x (h DIV 4) r (h MOD 4)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `r:num`] THEN
    STRIP_TAC THEN
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
       [rv32_mldsa_ntt_phase4; rv32_mldsa_radix4;
        LET_DEF; LET_END_DEF; ARITH] THEN
      RV32_NTT_REWRITE_BODY_UPDATES_TAC THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MAP_EVERY
       (fun q ->
          USE_THEN ("input" ^ string_of_int q)
           (fun th -> REWRITE_TAC[th]))
       (0--3) THEN
      REWRITE_TAC
       [RV32_MLDSA_BARRETT_PAIR;
        ARITH_RULE `g < g + 1`;
        ADD_CLAUSES];
      POP_ASSUM(LABEL_TAC "phase4_not_current") THEN
      SUBGOAL_THEN
       `!q. q < 4
            ==> orthogonal_components
                 ((memory :> bytes32
                   (word_add (a:int32)
                    (word(4 * (4 * h + r)))))
                  : (riscvstate,int32)component)
                 (memory :> bytes32
                   (word_add a
                    (word(4 * (4 * g + q)))))`
      (LABEL_TAC "phase4_orthogonal") THENL
       [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC
         (SPECL
           [`a:int32`; `h:num`; `r:num`;
            `g:num`; `q:num`]
           RV32_NTT_PHASE4_COEFFICIENT_ORTHOGONAL) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "phase4_not_current" ACCEPT_TAC;
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
          NUM_RING `4 * (4 * g + 0) = 16 * g`;
          NUM_RING `4 * (4 * g + 1) = 16 * g + 4`;
          NUM_RING `4 * (4 * g + 2) = 16 * g + 8`;
          NUM_RING `4 * (4 * g + 3) = 16 * g + 12`]) THEN
      SUBGOAL_THEN `(h < g + 1) <=> h < g` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
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
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (4 * h + r)))))
           : (riscvstate,int32)component)
          PC`
      (LABEL_TAC "phase4_pc_orthogonal") THENL
       [ORTHOGONAL_COMPONENTS_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `orthogonal_components
          ((memory :> bytes32
            (word_add (a:int32)
             (word(4 * (4 * h + r)))))
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
  DISCARD_OLDSTATE_TAC "s32" THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s33" None
   (fun th -> LABEL_TAC "increment" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

let RV32_MLDSA_NTT_PHASE4_BACKEDGE = prove
 (`!a zetas:int32. !x:num->num->num->int32. !i pc.
      0 < i /\ i < 64
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 744) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * i)) /\
                read T2 s =
                  word_add a (word(16 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < i then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 584) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * i)) /\
                read T2 s =
                  word_add a (word(16 * i)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < i then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->num->num->int32`;
    `i:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(word_add a (word(16 * i)):int32 =
      word_add a (word 1024))`
  ASSUME_TAC THENL
   [REWRITE_TAC
     [WORD_RULE
       `word_add a (word(16 * i)):int32 =
        word_add a (word 1024) <=>
        (word(16 * i):int32) = word 1024`;
      WORD_EQ; DIMINDEX_32; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `16 * i < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;

let RV32_MLDSA_NTT_PHASE4_EXIT = prove
 (`!a zetas:int32. !x:num->num->num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 744) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 2040) /\
            read T2 s = word_add a (word 1024) /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h r. h < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (4 * h + r))))) s =
                       rv32_mldsa_ntt_phase4 x h r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 748) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 2040) /\
            read T2 s = word_add a (word 1024) /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!h r. h < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (4 * h + r))))) s =
                       rv32_mldsa_ntt_phase4 x h r))
       (MAYCHANGE
         [PC; S0; S1; S2; S3; S4; S5;
          A1; T2; A2; A3; A4; A5; A6; A7] ,,
        MAYCHANGE [memory :> bytes(a,1024)] ,,
        MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->num->num->int32`;
    `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MLDSA_NTT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   ASM_MESON_TAC[RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE]));;

let RV32_MLDSA_NTT_PHASE4_BODY_TABLE = prove
 (`!a zetas:int32. !x:num->num->num->int32. !g pc.
      aligned 4 a /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 612) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(504 + 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(16 * g)) /\
               read T3 s = word_add a (word 1024) /\
               (!h r. h < 64 /\ r < 4
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (4 * h + r))))) s =
                          if h < g then
                            rv32_mldsa_ntt_phase4 x h r
                          else x (h DIV 4) r (h MOD 4))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (\s.
              (aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
               read PC s = word(pc + 744) /\
               read T0 s = word 8380417 /\
               read S0 s =
                 FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
               read S1 s =
                 SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
               read S2 s =
                 FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
               read S3 s =
                 SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
               read S4 s =
                 FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
               read S5 s =
                 SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
               read A0 s = a /\
               read A1 s =
                 word_add zetas (word(504 + 24 * (g + 1))) /\
               read T2 s =
                 word_add a (word(16 * (g + 1))) /\
               read T3 s = word_add a (word 1024) /\
               (!h r. h < 64 /\ r < 4
                      ==> read
                           (memory :>
                            bytes32
                             (word_add a
                              (word(4 * (4 * h + r))))) s =
                          if h < g + 1 then
                            rv32_mldsa_ntt_phase4 x h r
                          else x (h DIV 4) r (h MOD 4))) /\
              wordlist_from_memory(zetas,510) s:int32 list =
              MAP iword rv32_mldsa_ntt_zetas)
           (MAYCHANGE [PC; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->num->num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
   [MAP_EVERY X_GEN_TAC [`s:riscvstate`; `s':riscvstate`] THEN
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
        `word_add zetas (word(504 + 24 * (g + 1))):int32`;
        `x:num->num->num->int32`; `g:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE4_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC]]);;

let RV32_MLDSA_NTT_PHASE4_OUTER_BODY = prove
 (`!a zetas:int32. !x:num->num->num->int32. !g pc.
      aligned 4 a /\
      aligned 4 zetas /\
      g < 64 /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 584) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * g)) /\
                read T2 s =
                  word_add a (word(16 * g)) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < g then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 744) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s =
                  word_add zetas (word(504 + 24 * (g + 1))) /\
                read T2 s =
                  word_add a (word(16 * (g + 1))) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           if h < g + 1 then
                             rv32_mldsa_ntt_phase4 x h r
                           else x (h DIV 4) r (h MOD 4)))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->num->num->int32`;
    `g:num`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
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
     MAYCHANGE [events])
    subsumed
    (MAYCHANGE
      [PC; S0; S1; S2; S3; S4; S5;
       A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
     MAYCHANGE [memory :> bytes(a,1024)] ,,
     MAYCHANGE [events])`
  (LABEL_TAC "setup_frame_subsumed") THENL
   [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 612`
   `\s. read T0 s = word 8380417 /\
        read S0 s =
          FST(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
        read S1 s =
          SND(rv32_mldsa_ntt_pair (63 + 3 * g)) /\
        read S2 s =
          FST(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
        read S3 s =
          SND(rv32_mldsa_ntt_pair (64 + 3 * g)) /\
        read S4 s =
          FST(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
        read S5 s =
          SND(rv32_mldsa_ntt_pair (65 + 3 * g)) /\
        read A0 s = a /\
        read A1 s =
          word_add zetas (word(504 + 24 * (g + 1))) /\
        read T2 s =
          word_add a (word(16 * g)) /\
        read T3 s = word_add a (word 1024) /\
        wordlist_from_memory(zetas,510) s:int32 list =
        MAP iword rv32_mldsa_ntt_zetas /\
        (!h r. h < 64 /\ r < 4
               ==> read
                    (memory :>
                     bytes32
                      (word_add a
                       (word(4 * (4 * h + r))))) s =
                   if h < g then
                     rv32_mldsa_ntt_phase4 x h r
                   else x (h DIV 4) r (h MOD 4))` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MP_TAC
     (MP
       (SPECL
         [`a:int32`; `zetas:int32`; `g:num`; `pc:num`]
         RV32_MLDSA_NTT_PHASE4_OUTER_SETUP)
       (CONJ
         (ASSUME `aligned 4 (zetas:int32)`)
         (ASSUME `g < 64`))) THEN
    RISCV_BIGSTEP_TAC MLDSA_NTT_EXEC "s1" THEN
    ((ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) ORELSE
     ASM_REWRITE_TAC[]) THEN
    TRANS_TAC EQ_TRANS
     `wordlist_from_memory(zetas,510) s0:int32 list` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(MAYCHANGE
          [PC; S0; S1; S2; S3; S4; S5;
           A1; T2; T4; A2; A3; A4; A5; A6; A7] ,,
         MAYCHANGE [memory :> bytes(a,1024)] ,,
         MAYCHANGE [events])
        (s0:riscvstate) s1`
      (LABEL_TAC "setup_broad_frame") THENL
       [USE_THEN "setup_frame_subsumed"
         (fun th -> MATCH_MP_TAC(REWRITE_RULE[subsumed] th)) THEN
        ASM_REWRITE_TAC[];
        MP_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `s0:riscvstate`; `s1:riscvstate`]
           RV32_MLDSA_NTT_TABLE_PRESERVED) THEN
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
         [`a:int32`; `zetas:int32`;
          `x:num->num->num->int32`; `g:num`; `pc:num`]
         RV32_MLDSA_NTT_PHASE4_BODY_TABLE) THEN
      ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
      DISCH_THEN(LABEL_TAC "phase4_body") THEN
      MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
      USE_THEN "phase4_body"
       (fun th ->
         let tm = concl th in
         MAP_EVERY EXISTS_TAC
          [rand(rator(rator tm)); rand(rator tm)]) THEN
      REPEAT CONJ_TAC THENL
       [BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE4_USE_COEFFICIENT_TAC;
        BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        RV32_NTT_PHASE4_USE_COEFFICIENT_TAC;
        USE_THEN "phase4_body" ACCEPT_TAC]]]);;

let RV32_MLDSA_NTT_PHASE4_OUTER_LOOP = prove
 (`!a zetas:int32. !x:num->num->num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 584) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
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
                           x (h DIV 4) r (h MOD 4)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 748) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 2040) /\
                read T2 s = word_add a (word 1024) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!h r. h < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * h + r))))) s =
                           rv32_mldsa_ntt_phase4 x h r))
           (MAYCHANGE
             [PC; S0; S1; S2; S3; S4; S5;
              A1; T2; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->num->num->int32`;
    `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `64` `pc + 584` `pc + 744`
   `\i s.
      read T0 s = word 8380417 /\
      read A0 s = a /\
      read A1 s =
        word_add zetas (word(504 + 24 * i)) /\
      read T2 s =
        word_add a (word(16 * i)) /\
      read T3 s = word_add a (word 1024) /\
      wordlist_from_memory(zetas,510) s:int32 list =
      MAP iword rv32_mldsa_ntt_zetas /\
      (!h r. h < 64 /\ r < 4
             ==> read
                  (memory :>
                   bytes32
                    (word_add a
                     (word(4 * (4 * h + r))))) s =
                 if h < i then
                   rv32_mldsa_ntt_phase4 x h r
                 else x (h DIV 4) r (h MOD 4))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `~(h < 0)`];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`;
        `x:num->num->num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE4_OUTER_BODY) THEN
    ASM_REWRITE_TAC[fst MLDSA_NTT_EXEC];
    X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`;
        `x:num->num->num->int32`;
        `i:num`; `pc:num`]
       RV32_MLDSA_NTT_PHASE4_BACKEDGE) THEN
    ASM_REWRITE_TAC[];
    ENSURES_PRECONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
          read PC s = word(pc + 744) /\
          read T0 s = word 8380417 /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 2040) /\
          read T2 s = word_add a (word 1024) /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!h r. h < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * h + r))))) s =
                     rv32_mldsa_ntt_phase4 x h r)` THEN
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
        RV32_NTT_PHASE4_FINAL_COEFFICIENT_TAC));
      MATCH_ACCEPT_TAC
       (SPECL
         [`a:int32`; `zetas:int32`;
          `x:num->num->num->int32`; `pc:num`]
         RV32_MLDSA_NTT_PHASE4_EXIT)]]);;

let RV32_MLDSA_NTT_PHASE4_ENTRY_FULL = prove
 (`!a zetas:int32. !x:num->num->num->int32. !pc.
      ensures riscv
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 580) /\
            read T0 s = word 8380417 /\
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
                         x h l r))
       (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
            read PC s = word(pc + 584) /\
            read T0 s = word 8380417 /\
            read A0 s = a /\
            read A1 s = word_add zetas (word 504) /\
            read T2 s = a /\
            read T3 s = word_add a (word 1024) /\
            wordlist_from_memory(zetas,510) s:int32 list =
            MAP iword rv32_mldsa_ntt_zetas /\
            (!g r. g < 64 /\ r < 4
                   ==> read
                        (memory :>
                         bytes32
                          (word_add a
                           (word(4 * (4 * g + r))))) s =
                       x (g DIV 4) r (g MOD 4)))
       (MAYCHANGE [PC; T3] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`;
    `x:num->num->num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            is_forall(concl th) &&
            vfree_in `s0:riscvstate` (concl th) &&
            vfree_in `x:num->num->num->int32` (concl th))
         th in
      LABEL_TAC "phase3_memory" th') THEN
  FIRST_ASSUM
   (fun th ->
      let th' =
        check
         (fun th ->
            can
             (term_match []
               `wordlist_from_memory(zetas,510) (s0:riscvstate):
                  int32 list =
                MAP iword rv32_mldsa_ntt_zetas`)
             (concl th))
         th in
      LABEL_TAC "table_before" th') THEN
  RISCV_STEP_TAC MLDSA_NTT_EXEC [] "s1" None
   (fun th -> LABEL_TAC "entry_step" th THEN STRIP_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   RV32_NTT_PHASE12_TABLE_TAC ORELSE
   RV32_NTT_PHASE34_UPDATED_COEFFICIENT_TAC));;

let RV32_MLDSA_NTT_PHASE1234 = prove
 (`!a zetas:int32. !x:num->int32. !pc.
      aligned 4 a /\
      aligned 4 zetas /\
      nonoverlapping
        ((word pc):int32,LENGTH mldsa_ntt_mc) (a,1024) /\
      nonoverlapping (a,1024) (zetas,2040)
      ==> ensures riscv
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 28) /\
                C_ARGUMENTS [a;zetas] s /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!r j. r < 4 /\ j < 64
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (j + 64 * r))))) s =
                           x (j + 64 * r)))
           (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
                read PC s = word(pc + 748) /\
                read T0 s = word 8380417 /\
                read A0 s = a /\
                read A1 s = word_add zetas (word 2040) /\
                read T2 s = word_add a (word 1024) /\
                read T3 s = word_add a (word 1024) /\
                wordlist_from_memory(zetas,510) s:int32 list =
                MAP iword rv32_mldsa_ntt_zetas /\
                (!g r. g < 64 /\ r < 4
                       ==> read
                            (memory :>
                             bytes32
                              (word_add a
                               (word(4 * (4 * g + r))))) s =
                           rv32_mldsa_ntt_phase1234 x g r))
           (MAYCHANGE
             [PC; T0; S0; S1; S2; S3; S4; S5;
              A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
            MAYCHANGE [memory :> bytes(a,1024)] ,,
            MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 580`
   `\s. read T0 s = word 8380417 /\
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
                     rv32_mldsa_ntt_phase123 x h l r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
     (SPECL
       [`a:int32`; `zetas:int32`;
        `x:num->int32`; `pc:num`]
       RV32_MLDSA_NTT_PHASE123) THEN
    ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 584`
     `\s. read T0 s = word 8380417 /\
          read A0 s = a /\
          read A1 s = word_add zetas (word 504) /\
          read T2 s = a /\
          read T3 s = word_add a (word 1024) /\
          wordlist_from_memory(zetas,510) s:int32 list =
          MAP iword rv32_mldsa_ntt_zetas /\
          (!g r. g < 64 /\ r < 4
                 ==> read
                      (memory :>
                       bytes32
                        (word_add a
                         (word(4 * (4 * g + r))))) s =
                     rv32_mldsa_ntt_phase123 x
                      (g DIV 4) r (g MOD 4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC; T3] ,, MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_ACCEPT_TAC
         (SPECL
           [`a:int32`; `zetas:int32`;
            `rv32_mldsa_ntt_phase123 x`;
            `pc:num`]
           RV32_MLDSA_NTT_PHASE4_ENTRY_FULL)];
      REWRITE_TAC[rv32_mldsa_ntt_phase1234] THEN
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
           [`a:int32`; `zetas:int32`;
            `rv32_mldsa_ntt_phase123 x`;
            `pc:num`]
           RV32_MLDSA_NTT_PHASE4_OUTER_LOOP) THEN
        ASM_REWRITE_TAC[]]]]);;

needs "riscv/proofs/mldsa_ntt_arithmetic.ml";;

(* ========================================================================= *)
(* Functional correctness and psABI promotion of the forward NTT.           *)
(* ========================================================================= *)

let RV32_MLDSA_NTT_STACK_TABLE_PRESERVED = prove
 (`!stack zetas:int32. !s s':riscvstate.
      nonoverlapping (stack,32) (zetas,2040) /\
      (MAYCHANGE [PC] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [memory :> bytes32 stack] ,,
       MAYCHANGE [events] ,,
       MAYCHANGE
        [memory :> bytes32 (word_add stack (word 4))] ,,
       MAYCHANGE
        [memory :> bytes32 (word_add stack (word 8))] ,,
       MAYCHANGE
        [memory :> bytes32 (word_add stack (word 12))] ,,
       MAYCHANGE
        [memory :> bytes32 (word_add stack (word 16))] ,,
       MAYCHANGE
        [memory :> bytes32 (word_add stack (word 20))])
      s s'
      ==> wordlist_from_memory(zetas,510) s':int32 list =
          wordlist_from_memory(zetas,510) s`,
  let table = `memory :> bytes(zetas,2040)` in
  let rec preserves_tac gl =
    (REPEAT STRIP_TAC THEN
     W(fun (asl,w) ->
       let kind,args =
         tryfind
          (fun (_,th) ->
            let head,args = strip_comb(concl th) in
            let name = fst(dest_const head) in
            if name = ",," || name = "MAYCHANGE"
            then name,args
            else failwith "not a frame relation")
          asl in
       if kind = ",," then
         let r = List.nth args 0
         and t = List.nth args 1 in
         MATCH_MP_TAC
          (ISPECL [table; r; t] SEQ_PRESERVES_COMPONENT) THEN
         ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL [preserves_tac; preserves_tac]
       else
         let cs = List.nth args 0 in
         MATCH_MP_TAC
          (ISPECL
            [table; cs]
            MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
         ASM_REWRITE_TAC[ALL] THEN
         REPEAT CONJ_TAC THEN
         ORTHOGONAL_COMPONENTS_TAC)) gl in
  MAP_EVERY X_GEN_TAC
   [`stack:int32`; `zetas:int32`;
    `s:riscvstate`; `s':riscvstate`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  preserves_tac);;

let RV32_MLDSA_NTT_STACK_TABLE_TAC =
  W(fun (asl,w) ->
    if can
       (term_match []
         `wordlist_from_memory(z,510) (s:riscvstate):int32 list =
          MAP iword rv32_mldsa_ntt_zetas`)
       w
    then
      ASM_MESON_TAC[RV32_MLDSA_NTT_STACK_TABLE_PRESERVED]
    else
      NO_TAC);;

let MLDSA_NTT_CORE_CORRECT = prove
 (`!a zetas:int32. !x:num->int32. !pc:num.
    aligned 4 a /\
    aligned 4 zetas /\
    nonoverlapping
      ((word pc):int32,LENGTH mldsa_ntt_mc)
      (a,1024) /\
    nonoverlapping (a,1024) (zetas,2040)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
           read PC s = word (pc + 28) /\
           C_ARGUMENTS [a;zetas] s /\
           wordlist_from_memory (zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas /\
           (!i. i < 256 ==> abs(ival(x i)) < &8380417) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i))
      (\s. read PC s = word (pc + 748) /\
           !i. i < 256
               ==> let zi =
                     read
                      (memory :>
                       bytes32 (word_add a (word (4 * i)))) s in
                   (ival zi ==
                    mldsa_bitreverse_forward_ntt (ival o x) i)
                   (mod &8380417) /\
                   abs(ival zi) < &94279698)
      (MAYCHANGE
        [PC; T0; S0; S1; S2; S3; S4; S5;
         A1; T2; T3; T4; A2; A3; A4; A5; A6; A7] ,,
       MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC
   (SPECL
     [`a:int32`; `zetas:int32`; `x:num->int32`; `pc:num`]
     RV32_MLDSA_NTT_PHASE1234) THEN
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
      rv32_mldsa_ntt_phase1234 x (i DIV 4) (i MOD 4)`
    SUBST1_TAC THENL
     [USE_THEN "outputs"
       (MP_TAC o SPECL [`i DIV 4`; `i MOD 4`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
          REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV];
        SUBGOAL_THEN `4 * (i DIV 4) + i MOD 4 = i`
        ASSUME_TAC THENL
         [MP_TAC(SPECL [`i:num`; `4`] DIVISION) THEN
          CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      MP_TAC
       (SPEC `x:num->int32`
         RV32_MLDSA_NTT_PHASE1234_CORRECT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "machine" ACCEPT_TAC]);;

let MLDSA_NTT_SUBROUTINE_CORRECT = prove
 (`!a zetas:int32. !x:num->int32. !pc:num.
    !stackpointer returnaddress:int32.
    aligned 4 a /\
    aligned 4 zetas /\
    aligned 16 stackpointer /\
    aligned 4 returnaddress /\
    ALLPAIRS nonoverlapping
      [(a,1024);
       (word_sub stackpointer (word 32),32)]
      [((word pc):int32,LENGTH mldsa_ntt_mc);
       (zetas,2040)] /\
    nonoverlapping
      (a,1024)
      (word_sub stackpointer (word 32),32)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) mldsa_ntt_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read RA s = returnaddress /\
           C_ARGUMENTS [a;zetas] s /\
           wordlist_from_memory (zetas,510) s:int32 list =
           MAP iword rv32_mldsa_ntt_zetas /\
           (!i. i < 256 ==> abs(ival(x i)) < &8380417) /\
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
                    mldsa_bitreverse_forward_ntt (ival o x) i)
                   (mod &8380417) /\
                   abs(ival zi) < &94279698)
      (MAYCHANGE_REGS_PERMITTED_BY_ABI ,,
       MAYCHANGE
        [memory :> bytes(a,1024);
         memory :>
          bytes(word_sub stackpointer (word 32),32)])`,
  REWRITE_TAC[fst MLDSA_NTT_EXEC] THEN
  RISCV_ADD_RETURN_STACK_TAC
    ~core_precondition_tac:RV32_MLDSA_NTT_STACK_TABLE_TAC
    MLDSA_NTT_EXEC
    (REWRITE_RULE[fst MLDSA_NTT_EXEC]
      MLDSA_NTT_CORE_CORRECT)
    `[S0; S1; S2; S3; S4; S5]` 32);;
