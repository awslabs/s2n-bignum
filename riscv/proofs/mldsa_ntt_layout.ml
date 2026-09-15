(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared staged layouts for the RV32 ML-DSA forward NTT implementations.    *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_ntt_shared.ml";;

let rv32_mldsa_ntt_pair = define
 `rv32_mldsa_ntt_pair (k:num) =
    ((iword (EL (2 * k) rv32_mldsa_ntt_zetas)):int32,
     (iword (EL (2 * k + 1) rv32_mldsa_ntt_zetas)):int32)`;;

let rv32_mldsa_ntt_phase2 = define
 `rv32_mldsa_ntt_phase2 (x:num->int32) g j r =
    rv32_mldsa_radix4
      (rv32_mldsa_ntt_pair (3 + 3 * g))
      (rv32_mldsa_ntt_pair (4 + 3 * g))
      (rv32_mldsa_ntt_pair (5 + 3 * g))
      (\k. x (64 * g + j + 16 * k)) r`;;

let RV32_NTT_FLAT_COEFFICIENT_NONOVERLAPPING = prove
 (`!a:int32 i j.
      i < 256 /\ j < 256 /\ ~(j = i)
      ==> nonoverlapping
           (word_add a (word(4 * j)),4)
           (word_add a (word(4 * i)),4)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonoverlapping] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_BOTH THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  SUBGOAL_THEN `j:num < i \/ i < j` STRIP_ASSUME_TAC THEN
  ASM_ARITH_TAC);;

let RV32_NTT_FLAT_COEFFICIENT_ORTHOGONAL = prove
 (`!a:int32 i j.
      i < 256 /\ j < 256 /\ ~(j = i)
      ==> orthogonal_components
           ((memory :> bytes32
             (word_add a (word(4 * j))))
            : (riscvstate,int32)component)
           ((memory :> bytes32
             (word_add a (word(4 * i))))
            : (riscvstate,int32)component)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping
      (word_add (a:int32) (word(4 * j)),4)
      (word_add a (word(4 * i)),4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`a:int32`; `i:num`; `j:num`]
       RV32_NTT_FLAT_COEFFICIENT_NONOVERLAPPING) THEN
    ASM_REWRITE_TAC[];
    ORTHOGONAL_COMPONENTS_TAC]);;

let RV32_NTT_INDEX4_CASES = prove
 (`!r. r < 4 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`,
  ARITH_TAC);;

let RV32_NTT_PHASE2_COEFFICIENT_ORTHOGONAL = prove
 (`!a:int32 h l r g j q.
      h < 4 /\ l < 16 /\ r < 4 /\
      g < 4 /\ j < 16 /\ q < 4 /\
      ~(h = g /\ l = j)
      ==> orthogonal_components
           ((memory :> bytes32
             (word_add a
              (word(4 * (64 * h + l + 16 * r)))))
            : (riscvstate,int32)component)
           ((memory :> bytes32
             (word_add a
              (word(4 * (64 * g + j + 16 * q)))))
            : (riscvstate,int32)component)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL
     [`a:int32`;
      `64 * g + j + 16 * q`;
      `64 * h + l + 16 * r`]
     RV32_NTT_FLAT_COEFFICIENT_ORTHOGONAL) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_CASES_TAC `h:num = g` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `r:num = q` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `r:num < q \/ q < r` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]];
      SUBGOAL_THEN `h:num < g \/ g < h` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]]]);;

let RV32_NTT_PHASE2_PREFIX_UNCHANGED = prove
 (`!h l g j.
      ~(h = g /\ l = j)
      ==> ((h < g \/ h = g /\ l < j + 1) <=>
           h < g \/ h = g /\ l < j)`,
  ARITH_TAC);;

let RV32_MEMORY_PRESERVED_BY_CONTROL_MAYCHANGE = prove
 (`!s0 s1:riscvstate.
      (MAYCHANGE [PC] ,, MAYCHANGE [events]) s0 s1
      ==> read memory s1 = read memory s0`,
  MAP_EVERY X_GEN_TAC [`s0:riscvstate`; `s1:riscvstate`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC
   (ISPECL
     [`memory`;
      `MAYCHANGE [PC]`;
      `MAYCHANGE [events]`;
      `s0:riscvstate`; `s1:riscvstate`]
     SEQ_PRESERVES_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory`; `[PC]`; `u:riscvstate`; `v:riscvstate`]
       MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
    ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
    MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory`; `[events]`; `u:riscvstate`; `v:riscvstate`]
       MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
    ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC]);;

let RV32_WORDLIST_PRESERVED_BY_CONTROL_MAYCHANGE = prove
 (`!a:int32. !n s0 s1:riscvstate.
      (MAYCHANGE [PC] ,, MAYCHANGE [events]) s0 s1
      ==> wordlist_from_memory(a,n) s1:int32 list =
          wordlist_from_memory(a,n) s0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read memory s1 = read memory s0` ASSUME_TAC THENL
   [MATCH_MP_TAC RV32_MEMORY_PRESERVED_BY_CONTROL_MAYCHANGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[]]);;

let RV32_MEMORY_PRESERVED_BY_OUTER_EXIT_MAYCHANGE = prove
 (`!s0 s1:riscvstate.
      (MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE [T2]) s0 s1
      ==> read memory s1 = read memory s0`,
  MAP_EVERY X_GEN_TAC [`s0:riscvstate`; `s1:riscvstate`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC
   (ISPECL
     [`memory`;
      `MAYCHANGE [PC]`;
      `MAYCHANGE [events] ,, MAYCHANGE [T2]`;
      `s0:riscvstate`; `s1:riscvstate`]
     SEQ_PRESERVES_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory`; `[PC]`; `u:riscvstate`; `v:riscvstate`]
       MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
    ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
    MAP_EVERY X_GEN_TAC [`u:riscvstate`; `v:riscvstate`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC
     (ISPECL
       [`memory`;
        `MAYCHANGE [events]`;
        `MAYCHANGE [T2]`;
        `u:riscvstate`; `v:riscvstate`]
       SEQ_PRESERVES_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`w:riscvstate`; `x:riscvstate`] THEN
    DISCH_TAC THENL
     [MATCH_MP_TAC
       (ISPECL
         [`memory`; `[events]`; `w:riscvstate`; `x:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
      MATCH_MP_TAC
       (ISPECL
         [`memory`; `[T2]`; `w:riscvstate`; `x:riscvstate`]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
      ASM_REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC]]);;

let RV32_WORDLIST_PRESERVED_BY_OUTER_EXIT_MAYCHANGE = prove
 (`!a:int32. !n s0 s1:riscvstate.
      (MAYCHANGE [PC] ,, MAYCHANGE [events] ,, MAYCHANGE [T2]) s0 s1
      ==> wordlist_from_memory(a,n) s1:int32 list =
          wordlist_from_memory(a,n) s0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read memory s1 = read memory s0` ASSUME_TAC THENL
   [MATCH_MP_TAC RV32_MEMORY_PRESERVED_BY_OUTER_EXIT_MAYCHANGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[]]);;

let RV32_NTT_PHASE2_USE_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 3 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `l:num`; `r:num`] th in
    (MATCH_MP_TAC th' THEN ASM_REWRITE_TAC[]) gl;;

let RV32_NTT_PHASE2_FINAL_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 3 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `l:num`; `r:num`] th in
    let bounds =
      CONJ (ASSUME `h < 4`)
       (CONJ (ASSUME `l < 16`) (ASSUME `r < 4`)) in
    ACCEPT_TAC(ASM_REWRITE_RULE[] (MATCH_MP th' bounds)) gl;;

let RV32_NTT_PHASE12_INDEX = prove
 (`!h l r.
      h < 4 /\ l < 16 /\ r < 4
      ==> l + 16 * r < 64 /\
          64 * h + l + 16 * r =
          (l + 16 * r) + 64 * h /\
          (64 * h + l + 16 * r) MOD 64 =
          l + 16 * r /\
          (64 * h + l + 16 * r) DIV 64 = h`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l + 16 * r < 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ARITH_TAC;
    REWRITE_TAC[ARITH_RULE
     `64 * h + l + 16 * r = (l + 16 * r) + 64 * h`] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    REWRITE_TAC[ARITH_RULE
     `64 * h + l + 16 * r = (l + 16 * r) + 64 * h`] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(l + 16 * r) DIV 64 = 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ]; ARITH_TAC]]);;

let RV32_NTT_PHASE12_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase1_memory" asl in
    let bounds =
      CONJ (ASSUME `h < 4`)
       (CONJ (ASSUME `l < 16`) (ASSUME `r < 4`)) in
    let ith =
      MATCH_MP
       (SPECL [`h:num`; `l:num`; `r:num`]
         RV32_NTT_PHASE12_INDEX)
       bounds in
    let sth =
      MP (SPECL [`h:num`; `l + 16 * r`] th)
       (CONJ (ASSUME `h < 4`) (CONJUNCT1 ith)) in
    let sth' =
      REWRITE_RULE
       [GSYM(CONJUNCT1(CONJUNCT2 ith))]
       sth in
    (REWRITE_TAC
      [CONJUNCT1(CONJUNCT2(CONJUNCT2 ith));
       CONJUNCT2(CONJUNCT2(CONJUNCT2 ith))] THEN
     MATCH_ACCEPT_TAC sth')
    gl;;

let RV32_NTT_PHASE12_TABLE_TAC =
  USE_THEN "entry_step"
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[wordlist_from_memory; READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  USE_THEN "table_before"
   (fun th ->
     MATCH_ACCEPT_TAC
      (REWRITE_RULE
        [wordlist_from_memory; READ_COMPONENT_COMPOSE]
        th));;

let RV32_NTT_PHASE12_UPDATED_COEFFICIENT_TAC =
  USE_THEN "entry_step"
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
  STRIP_TAC THEN
  RV32_NTT_PHASE12_COEFFICIENT_TAC;;

let rv32_mldsa_ntt_phase12 = define
 `rv32_mldsa_ntt_phase12 (x:num->int32) h l r =
    rv32_mldsa_ntt_phase2
      (\n. rv32_mldsa_ntt_phase1 x (n MOD 64) (n DIV 64))
      h l r`;;

let RV32_NTT_USE_STRONGER_PRE_TAC th =
  let tm = concl th in
  let p = rand(rator(rator tm)) in
  let q = rand(rator tm) in
  MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
  MAP_EVERY EXISTS_TAC [p;q] THEN
  REPEAT CONJ_TAC THENL
   [BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM (fun ath -> MATCH_MP_TAC (SPEC_ALL ath)) THEN
    ASM_REWRITE_TAC[];
    BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM (fun ath -> MATCH_MP_TAC (SPEC_ALL ath)) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC th];;

let rv32_mldsa_ntt_phase3 = define
 `rv32_mldsa_ntt_phase3 (x:num->int32) g j r =
    rv32_mldsa_radix4
      (rv32_mldsa_ntt_pair (15 + 3 * g))
      (rv32_mldsa_ntt_pair (16 + 3 * g))
      (rv32_mldsa_ntt_pair (17 + 3 * g))
      (\k. x (16 * g + j + 4 * k)) r`;;

let RV32_NTT_PHASE3_COEFFICIENT_ORTHOGONAL = prove
 (`!a:int32 h l r g j q.
      h < 16 /\ l < 4 /\ r < 4 /\
      g < 16 /\ j < 4 /\ q < 4 /\
      ~(h = g /\ l = j)
      ==> orthogonal_components
           ((memory :> bytes32
             (word_add a
              (word(4 * (16 * h + l + 4 * r)))))
            : (riscvstate,int32)component)
           ((memory :> bytes32
             (word_add a
              (word(4 * (16 * g + j + 4 * q)))))
            : (riscvstate,int32)component)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL
     [`a:int32`;
      `16 * g + j + 4 * q`;
      `16 * h + l + 4 * r`]
     RV32_NTT_FLAT_COEFFICIENT_ORTHOGONAL) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_CASES_TAC `h:num = g` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `r:num = q` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `r:num < q \/ q < r` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]];
      SUBGOAL_THEN `h:num < g \/ g < h` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]]]);;

let RV32_NTT_PHASE3_USE_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 3 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `l:num`; `r:num`] th in
    (MATCH_MP_TAC th' THEN ASM_REWRITE_TAC[]) gl;;

let RV32_NTT_PHASE3_FINAL_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 3 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `l:num`; `r:num`] th in
    let bounds =
      CONJ (ASSUME `h < 16`)
       (CONJ (ASSUME `l < 4`) (ASSUME `r < 4`)) in
    ACCEPT_TAC(ASM_REWRITE_RULE[] (MATCH_MP th' bounds)) gl;;

let RV32_NTT_PHASE123_FLAT_RECONSTRUCT = prove
 (`!n. 64 * (n DIV 64) + n MOD 16 +
       16 * ((n DIV 16) MOD 4) = n`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16`; `4`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_DIV] THEN
  ARITH_TAC);;

let RV32_NTT_PHASE123_INDEX = prove
 (`!h l r.
      h < 16 /\ l < 4 /\ r < 4
      ==> 16 * h + l + 4 * r < 256 /\
          (16 * h + l + 4 * r) DIV 64 < 4 /\
          (16 * h + l + 4 * r) MOD 16 < 16 /\
          ((16 * h + l + 4 * r) DIV 16) MOD 4 < 4 /\
          64 * ((16 * h + l + 4 * r) DIV 64) +
          (16 * h + l + 4 * r) MOD 16 +
          16 * (((16 * h + l + 4 * r) DIV 16) MOD 4) =
          16 * h + l + 4 * r`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `16 * h + l + 4 * r < 256` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_ACCEPT_TAC
     (SPEC `16 * h + l + 4 * r`
       RV32_NTT_PHASE123_FLAT_RECONSTRUCT)]);;

let rv32_mldsa_ntt_phase123 = define
 `rv32_mldsa_ntt_phase123 (x:num->int32) h l r =
    rv32_mldsa_ntt_phase3
      (\n. rv32_mldsa_ntt_phase12 x
            (n DIV 64) (n MOD 16) ((n DIV 16) MOD 4))
      h l r`;;

let RV32_NTT_PHASE123_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase12_memory" asl in
    let bounds =
      CONJ (ASSUME `h < 16`)
       (CONJ (ASSUME `l < 4`) (ASSUME `r < 4`)) in
    let ith =
      MATCH_MP
       (SPECL [`h:num`; `l:num`; `r:num`]
         RV32_NTT_PHASE123_INDEX)
       bounds in
    let sth =
      MP
       (SPECL
         [`(16 * h + l + 4 * r) DIV 64`;
          `(16 * h + l + 4 * r) MOD 16`;
          `((16 * h + l + 4 * r) DIV 16) MOD 4`]
         th)
       (CONJ
         (CONJUNCT1(CONJUNCT2 ith))
         (CONJ
           (CONJUNCT1(CONJUNCT2(CONJUNCT2 ith)))
           (CONJUNCT1
             (CONJUNCT2(CONJUNCT2(CONJUNCT2 ith)))))) in
    let eq =
      CONJUNCT2
       (CONJUNCT2
        (CONJUNCT2
         (CONJUNCT2 ith))) in
    let sth' = REWRITE_RULE[eq] sth in
    (USE_THEN "entry_step"
      (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
     CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
     MATCH_ACCEPT_TAC sth')
    gl;;

let RV32_NTT_PHASE123_UPDATED_COEFFICIENT_TAC =
  USE_THEN "entry_step"
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
  STRIP_TAC THEN
  RV32_NTT_PHASE123_COEFFICIENT_TAC;;

let rv32_mldsa_ntt_phase4 = define
 `rv32_mldsa_ntt_phase4 (x:num->num->num->int32) g r =
    rv32_mldsa_radix4
      (rv32_mldsa_ntt_pair (63 + 3 * g))
      (rv32_mldsa_ntt_pair (64 + 3 * g))
      (rv32_mldsa_ntt_pair (65 + 3 * g))
      (\k. x (g DIV 4) k (g MOD 4)) r`;;

let RV32_NTT_PHASE4_COEFFICIENT_ORTHOGONAL = prove
 (`!a:int32 h r g q.
      h < 64 /\ r < 4 /\ g < 64 /\ q < 4 /\ ~(h = g)
      ==> orthogonal_components
           ((memory :> bytes32
             (word_add a (word(4 * (4 * h + r)))))
            : (riscvstate,int32)component)
           ((memory :> bytes32
             (word_add a (word(4 * (4 * g + q)))))
            : (riscvstate,int32)component)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL
     [`a:int32`; `4 * g + q`; `4 * h + r`]
     RV32_NTT_FLAT_COEFFICIENT_ORTHOGONAL) THEN
  REPEAT CONJ_TAC THEN ASM_ARITH_TAC);;

let RV32_NTT_PHASE4_USE_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 2 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `r:num`] th in
    (MATCH_MP_TAC th' THEN ASM_REWRITE_TAC[]) gl;;

let RV32_NTT_PHASE4_FINAL_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th =
      tryfind
       (fun (_,th) ->
         let vs,bod = strip_forall(concl th) in
         if List.length vs = 2 && is_imp bod then th
         else failwith "not the coefficient invariant")
       asl in
    let th' = SPECL [`h:num`; `r:num`] th in
    let bounds = CONJ (ASSUME `h < 64`) (ASSUME `r < 4`) in
    ACCEPT_TAC(ASM_REWRITE_RULE[] (MATCH_MP th' bounds)) gl;;

let RV32_NTT_PHASE34_INDEX = prove
 (`!g r.
      g < 64 /\ r < 4
      ==> g DIV 4 < 16 /\
          g MOD 4 < 4 /\
          16 * (g DIV 4) + r + 4 * (g MOD 4) =
          4 * g + r`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `g DIV 4 < 16` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`g:num`; `4`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC]);;

let RV32_NTT_PHASE34_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase3_memory" asl in
    let bounds = CONJ (ASSUME `g < 64`) (ASSUME `r < 4`) in
    let ith =
      MATCH_MP
       (SPECL [`g:num`; `r:num`]
         RV32_NTT_PHASE34_INDEX)
       bounds in
    let sth =
      MP
       (SPECL
         [`g DIV 4`; `r:num`; `g MOD 4`]
         th)
       (CONJ
         (CONJUNCT1 ith)
         (CONJ
           (ASSUME `r < 4`)
           (CONJUNCT1(CONJUNCT2 ith)))) in
    let eq = CONJUNCT2(CONJUNCT2 ith) in
    let sth' = REWRITE_RULE[eq] sth in
    (USE_THEN "entry_step"
      (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
     CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
     MATCH_ACCEPT_TAC sth')
    gl;;

let RV32_NTT_PHASE34_UPDATED_COEFFICIENT_TAC =
  USE_THEN "entry_step"
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  MAP_EVERY X_GEN_TAC [`g:num`; `r:num`] THEN
  STRIP_TAC THEN
  RV32_NTT_PHASE34_COEFFICIENT_TAC;;

let rv32_mldsa_ntt_phase1234 = define
 `rv32_mldsa_ntt_phase1234 (x:num->int32) g r =
    rv32_mldsa_ntt_phase4 (rv32_mldsa_ntt_phase123 x) g r`;;
