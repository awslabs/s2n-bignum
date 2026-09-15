(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared staged layouts for the RV32 ML-DSA inverse NTT implementations.    *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_ntt_shared.ml";;

(* These definitions mirror the four reverse-order radix-4 passes of the
   inverse assembly. Phase 1 starts with adjacent coefficients and table pairs
   252--254; later phases increase the coefficient stride while consuming the
   table backwards. `rv32_mldsa_intt_output` applies the final inverse-scale
   reduction after the fourth phase. *)

let rv32_mldsa_intt_radix4 = define
 `rv32_mldsa_intt_radix4
    (zw0:int32#int32) (zw1:int32#int32) (zw2:int32#int32)
    (f:num->int32) k =
    let u0 = word_add (f 0) (f 1)
    and u1 = mldsa_barrett_mul zw2 (word_sub (f 1) (f 0))
    and u2 = word_add (f 2) (f 3)
    and u3 = mldsa_barrett_mul zw1 (word_sub (f 3) (f 2)) in
    if k = 0 then word_add u0 u2
    else if k = 1 then word_add u1 u3
    else if k = 2 then mldsa_barrett_mul zw0 (word_sub u2 u0)
    else mldsa_barrett_mul zw0 (word_sub u3 u1)`;;

let rv32_mldsa_intt_phase1 = define
 `rv32_mldsa_intt_phase1 (x:num->int32) g r =
    rv32_mldsa_intt_radix4
      (rv32_mldsa_ntt_pair (252 - 3 * g))
      (rv32_mldsa_ntt_pair (253 - 3 * g))
      (rv32_mldsa_ntt_pair (254 - 3 * g))
      (\k. x (4 * g + k)) r`;;

let rv32_mldsa_intt_phase2 = define
 `rv32_mldsa_intt_phase2 (x:num->int32) g j r =
    rv32_mldsa_intt_radix4
      (rv32_mldsa_ntt_pair (60 - 3 * g))
      (rv32_mldsa_ntt_pair (61 - 3 * g))
      (rv32_mldsa_ntt_pair (62 - 3 * g))
      (\k. x (16 * g + j + 4 * k)) r`;;

let rv32_mldsa_intt_phase12 = define
 `rv32_mldsa_intt_phase12 (x:num->int32) g j r =
    rv32_mldsa_intt_phase2
      (\n. rv32_mldsa_intt_phase1 x (n DIV 4) (n MOD 4))
      g j r`;;

let rv32_mldsa_intt_phase3 = define
 `rv32_mldsa_intt_phase3 (x:num->int32) g j r =
    rv32_mldsa_intt_radix4
      (rv32_mldsa_ntt_pair (12 - 3 * g))
      (rv32_mldsa_ntt_pair (13 - 3 * g))
      (rv32_mldsa_ntt_pair (14 - 3 * g))
      (\k. x (64 * g + j + 16 * k)) r`;;

let rv32_mldsa_intt_phase123 = define
 `rv32_mldsa_intt_phase123 (x:num->int32) g j r =
    rv32_mldsa_intt_phase3
      (\n. rv32_mldsa_intt_phase12 x
            (n DIV 16) (n MOD 4) ((n DIV 4) MOD 4))
      g j r`;;

let rv32_mldsa_intt_phase4 = define
 `rv32_mldsa_intt_phase4 (x:num->int32) j r =
    rv32_mldsa_intt_radix4
      (rv32_mldsa_ntt_pair 0)
      (rv32_mldsa_ntt_pair 1)
      (rv32_mldsa_ntt_pair 2)
      (\k. x (j + 64 * k)) r`;;

let rv32_mldsa_intt_phase1234 = define
 `rv32_mldsa_intt_phase1234 (x:num->int32) j r =
    rv32_mldsa_intt_phase4
      (\n. rv32_mldsa_intt_phase123 x
            (n DIV 64) (n MOD 16) ((n DIV 16) MOD 4))
      j r`;;

let rv32_mldsa_intt_output = define
 `rv32_mldsa_intt_output (x:num->int32) n =
    arm_mldsa_barmul (&4197891,word 16382)
      (rv32_mldsa_intt_phase1234 x (n MOD 64) (n DIV 64))`;;

let RV32_INTT_PHASE12_INDEX = prove
 (`!g j r.
      g < 16 /\ j < 4 /\ r < 4
      ==> 16 * g + j + 4 * r < 256 /\
          (16 * g + j + 4 * r) DIV 4 = 4 * g + r /\
          (16 * g + j + 4 * r) MOD 4 = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `j < 4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC
     [ARITH_RULE `16 * g + j + 4 * r = j + 4 * (4 * g + r)`] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `j DIV 4 = 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ]; ARITH_TAC];
    REWRITE_TAC
     [ARITH_RULE `16 * g + j + 4 * r = j + 4 * (4 * g + r)`;
      MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT]]);;

let RV32_INTT_PHASE123_INDEX = prove
 (`!g j r.
      g < 4 /\ j < 16 /\ r < 4
      ==> 64 * g + j + 16 * r < 256 /\
          (64 * g + j + 16 * r) DIV 16 = 4 * g + r /\
          (64 * g + j + 16 * r) MOD 4 = j MOD 4 /\
          ((64 * g + j + 16 * r) DIV 4) MOD 4 = j DIV 4 /\
          16 * (4 * g + r) + j MOD 4 + 4 * (j DIV 4) =
          64 * g + j + 16 * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `j DIV 4 < 4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC
     [ARITH_RULE `64 * g + j + 16 * r = j + 16 * (4 * g + r)`] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `j DIV 16 = 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ]; ARITH_TAC];
    REWRITE_TAC
     [ARITH_RULE
       `64 * g + j + 16 * r = j + 4 * (16 * g + 4 * r)`;
      MOD_MULT_ADD];
    REWRITE_TAC
     [ARITH_RULE
       `64 * g + j + 16 * r = j + 4 * (16 * g + 4 * r)`] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    REWRITE_TAC
     [ARITH_RULE `j DIV 4 + 16 * g + 4 * r =
                  j DIV 4 + 4 * (4 * g + r)`;
      MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT];
    MP_TAC(SPECL [`j:num`; `4`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let RV32_INTT_PHASE1234_INDEX = prove
 (`!j r.
      j < 64 /\ r < 4
      ==> j + 64 * r < 256 /\
          (j + 64 * r) DIV 64 = r /\
          (j + 64 * r) MOD 16 = j MOD 16 /\
          ((j + 64 * r) DIV 16) MOD 4 = j DIV 16 /\
          64 * r + j MOD 16 + 16 * (j DIV 16) =
          j + 64 * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `j DIV 16 < 4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `j DIV 64 = 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ]; ARITH_TAC];
    REWRITE_TAC
     [ARITH_RULE `j + 64 * r = j + 16 * (4 * r)`;
      MOD_MULT_ADD];
    REWRITE_TAC
     [ARITH_RULE `j + 64 * r = j + 16 * (4 * r)`] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT];
    MP_TAC(SPECL [`j:num`; `16`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let RV32_INTT_FLAT_INDEX = prove
 (`!n. n < 256
       ==> n MOD 64 < 64 /\
           n DIV 64 < 4 /\
           n MOD 64 + 64 * (n DIV 64) = n`,
  REPEAT STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`n:num`; `64`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let RV32_INTT_PHASE12_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase1_memory" asl in
    (MP_TAC
      (SPECL [`4 * h + r`; `l:num`] th) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN
      (fun sth ->
         let bounds =
           CONJ (ASSUME `h < 16`)
            (CONJ (ASSUME `l < 4`) (ASSUME `r < 4`)) in
         let ith =
           MATCH_MP
            (SPECL [`h:num`; `l:num`; `r:num`]
              RV32_INTT_PHASE12_INDEX)
            bounds in
         let sth' =
           REWRITE_RULE
            [ARITH_RULE
              `4 * (4 * (4 * h + r) + l) =
               4 * (16 * h + l + 4 * r)`]
            sth in
         REWRITE_TAC
          [CONJUNCT1(CONJUNCT2 ith);
           CONJUNCT2(CONJUNCT2 ith)] THEN
         MATCH_ACCEPT_TAC sth')) gl;;

let RV32_INTT_PHASE123_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase12_memory" asl in
    (MP_TAC
      (SPECL
        [`4 * h + r`; `l MOD 4`; `l DIV 4`]
        th) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [ASM_ARITH_TAC;
         REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
         ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC];
       ALL_TAC] THEN
     DISCH_THEN
      (fun sth ->
         let bounds =
           CONJ (ASSUME `h < 4`)
            (CONJ (ASSUME `l < 16`) (ASSUME `r < 4`)) in
         let ith =
           MATCH_MP
            (SPECL [`h:num`; `l:num`; `r:num`]
              RV32_INTT_PHASE123_INDEX)
            bounds in
         let ith1 = CONJUNCT2 ith in
         let ith2 = CONJUNCT2 ith1 in
         let ith3 = CONJUNCT2 ith2 in
         let sth' =
           REWRITE_RULE
            [CONJUNCT2 ith3]
            sth in
         REWRITE_TAC
          [CONJUNCT1 ith1;
           CONJUNCT1 ith2;
           CONJUNCT1 ith3] THEN
         MATCH_ACCEPT_TAC sth')) gl;;

let RV32_INTT_PHASE1234_COEFFICIENT_TAC =
  fun (asl,w as gl) ->
    let th = assoc "phase123_memory" asl in
    (MP_TAC
      (SPECL
        [`r:num`; `j MOD 16`; `j DIV 16`]
        th) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [ASM_ARITH_TAC;
         REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
         ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC];
       ALL_TAC] THEN
     DISCH_THEN
      (fun sth ->
         let bounds =
           CONJ (ASSUME `j < 64`) (ASSUME `r < 4`) in
         let ith =
           MATCH_MP
            (SPECL [`j:num`; `r:num`]
              RV32_INTT_PHASE1234_INDEX)
            bounds in
         let ith1 = CONJUNCT2 ith in
         let ith2 = CONJUNCT2 ith1 in
         let ith3 = CONJUNCT2 ith2 in
         let sth' =
           REWRITE_RULE
            [CONJUNCT2 ith3]
            sth in
         REWRITE_TAC
          [CONJUNCT1 ith1;
           CONJUNCT1 ith2;
           CONJUNCT1 ith3] THEN
         MATCH_ACCEPT_TAC sth')) gl;;

let RV32_INTT_PHASE123_UPDATED_COEFFICIENT_TAC =
  USE_THEN "entry_step"
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `l:num`; `r:num`] THEN
  STRIP_TAC THEN
  RV32_INTT_PHASE123_COEFFICIENT_TAC;;
