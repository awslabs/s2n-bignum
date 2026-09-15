(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "riscv/proofs/mldsa_intt_layout.ml";;
needs "common/mlkem_mldsa_linear.ml";;

(* ========================================================================= *)
(* Radix-4 recurrence for the RV32 ML-DSA inverse NTT.                       *)
(* ========================================================================= *)


let rv32_mldsa_intt_radix4_int_rv32 = define
 `rv32_mldsa_intt_radix4_int_rv32
    (z0:int) (z1:int) (z2:int) (f:num->int) r =
    let u0 = f 0 + f 1
    and u1 = (f 1 - f 0) * z2
    and u2 = f 2 + f 3
    and u3 = (f 3 - f 2) * z1 in
    if r = 0 then u0 + u2
    else if r = 1 then u1 + u3
    else if r = 2 then (u2 - u0) * z0
    else (u3 - u1) * z0`;;

let rv32_mldsa_intt_radix4_coeff_rv32 = define
 `rv32_mldsa_intt_radix4_coeff_rv32
    (z0:int) (z1:int) (z2:int) r k =
    if r = 0 then &1
    else if r = 1 then
      if k = 0 then --z2
      else if k = 1 then z2
      else if k = 2 then --z1
      else z1
    else if r = 2 then
      if k = 0 then --z0
      else if k = 1 then --z0
      else z0
    else
      if k = 0 then z0 * z2
      else if k = 1 then --(z0 * z2)
      else if k = 2 then --(z0 * z1)
      else z0 * z1`;;

let RV32_INTT_RADIX4_COEFF_EXPAND_RV32 = prove
 (`!z0 z1 z2:int. !f:num->int. !r.
     r < 4
     ==> rv32_mldsa_intt_radix4_int_rv32 z0 z1 z2 f r =
         isum (0..3)
          (\k. f k *
               rv32_mldsa_intt_radix4_coeff_rv32 z0 z1 z2 r k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_intt_radix4_int_rv32;
    rv32_mldsa_intt_radix4_coeff_rv32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(RAND_CONV EXPAND_ISUM_CONV) THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC INT_RING);;

let RV32_INTT_COEFF_TRANSPOSE_K0_RV32 = prove
 (`!z0 z1 z2:int. !r.
     r < 4
     ==> rv32_mldsa_intt_radix4_coeff_rv32 z0 z1 z2 r 0 =
         rv32_mldsa_radix4_coeff_fast z0 z1 z2 3 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_intt_radix4_coeff_rv32;
    rv32_mldsa_radix4_coeff_fast] THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  INT_ARITH_TAC);;

let RV32_INTT_COEFF_TRANSPOSE_K1_RV32 = prove
 (`!z0 z1 z2:int. !r.
     r < 4
     ==> rv32_mldsa_intt_radix4_coeff_rv32 z0 z1 z2 r 1 =
         rv32_mldsa_radix4_coeff_fast z0 z1 z2 2 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_intt_radix4_coeff_rv32;
    rv32_mldsa_radix4_coeff_fast] THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  INT_ARITH_TAC);;

let RV32_INTT_COEFF_TRANSPOSE_K2_RV32 = prove
 (`!z0 z1 z2:int. !r.
     r < 4
     ==> rv32_mldsa_intt_radix4_coeff_rv32 z0 z1 z2 r 2 =
         rv32_mldsa_radix4_coeff_fast z0 z1 z2 1 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_intt_radix4_coeff_rv32;
    rv32_mldsa_radix4_coeff_fast] THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  INT_ARITH_TAC);;

let RV32_INTT_COEFF_TRANSPOSE_K3_RV32 = prove
 (`!z0 z1 z2:int. !r.
     r < 4
     ==> rv32_mldsa_intt_radix4_coeff_rv32 z0 z1 z2 r 3 =
         rv32_mldsa_radix4_coeff_fast z0 z1 z2 0 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_intt_radix4_coeff_rv32;
    rv32_mldsa_radix4_coeff_fast] THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  INT_ARITH_TAC);;

let rv32_mldsa_intt_step_exponent_rv32 = define
 `rv32_mldsa_intt_step_exponent_rv32 (a:num) k =
    if k = 0 then a + 384
    else if k = 1 then a + 128
    else if k = 2 then a + 256
    else a`;;

let RV32_INTT_COEFF_PATTERN_RV32 = prove
 (`!a:num. !z0 z1 z2:int.
     ((z0 == (&1753:int) pow (2 * a) rem &8380417)
        (mod &8380417) /\
      (z1 == (&1753:int) pow a rem &8380417)
        (mod &8380417) /\
      (z2 == (&1753:int) pow (a + 128) rem &8380417)
        (mod &8380417))
     ==> !r k. r < 4 /\ k < 4
               ==> (rv32_mldsa_intt_radix4_coeff_rv32
                     z0 z1 z2 r k ==
                    (&1753:int) pow
                     (rv32_mldsa_intt_step_exponent_rv32 a k * r)
                    rem &8380417)
                   (mod &8380417)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `k:num`] THEN
  STRIP_TAC THEN
  MP_TAC
   (MATCH_MP
     (SPEC `k:num` RV32_INDEX4_CASES_RV32)
     (ASSUME `k < 4`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC
     [rv32_mldsa_intt_step_exponent_rv32;
      MATCH_MP RV32_INTT_COEFF_TRANSPOSE_K0_RV32
       (ASSUME `r < 4`)] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_MP_TAC
     (SPEC `r:num`
       (MATCH_MP
         (SPECL [`a:num`; `z0:int`; `z1:int`; `z2:int`]
           RV32_COEFF_PATTERN_R3_FAST)
         (ASSUME
           `(z0 == (&1753:int) pow (2 * a) rem &8380417)
              (mod &8380417) /\
            (z1 == (&1753:int) pow a rem &8380417)
              (mod &8380417) /\
            (z2 == (&1753:int) pow (a + 128) rem &8380417)
              (mod &8380417)`))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
     [rv32_mldsa_intt_step_exponent_rv32;
      MATCH_MP RV32_INTT_COEFF_TRANSPOSE_K1_RV32
       (ASSUME `r < 4`)] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_MP_TAC
     (SPEC `r:num`
       (MATCH_MP
         (SPECL [`a:num`; `z0:int`; `z1:int`; `z2:int`]
           RV32_COEFF_PATTERN_R2_FAST)
         (ASSUME
           `(z0 == (&1753:int) pow (2 * a) rem &8380417)
              (mod &8380417) /\
            (z1 == (&1753:int) pow a rem &8380417)
              (mod &8380417) /\
            (z2 == (&1753:int) pow (a + 128) rem &8380417)
              (mod &8380417)`))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
     [rv32_mldsa_intt_step_exponent_rv32;
      MATCH_MP RV32_INTT_COEFF_TRANSPOSE_K2_RV32
       (ASSUME `r < 4`)] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_MP_TAC
     (SPEC `r:num`
       (MATCH_MP
         (SPECL [`a:num`; `z0:int`; `z1:int`; `z2:int`]
           RV32_COEFF_PATTERN_R1_FAST)
         (ASSUME
           `(z0 == (&1753:int) pow (2 * a) rem &8380417)
              (mod &8380417) /\
            (z1 == (&1753:int) pow a rem &8380417)
              (mod &8380417) /\
            (z2 == (&1753:int) pow (a + 128) rem &8380417)
              (mod &8380417)`))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC
     [rv32_mldsa_intt_step_exponent_rv32;
      MATCH_MP RV32_INTT_COEFF_TRANSPOSE_K3_RV32
       (ASSUME `r < 4`)] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_MP_TAC
     (SPEC `r:num`
       (MATCH_MP
         (SPECL [`a:num`; `z0:int`; `z1:int`; `z2:int`]
           RV32_COEFF_PATTERN_R0_FAST)
         (ASSUME
           `(z0 == (&1753:int) pow (2 * a) rem &8380417)
              (mod &8380417) /\
            (z1 == (&1753:int) pow a rem &8380417)
              (mod &8380417) /\
            (z2 == (&1753:int) pow (a + 128) rem &8380417)
              (mod &8380417)`))) THEN
    ASM_REWRITE_TAC[]]);;

let ISUM_BLOCK_OFFSET_RV32 = prove
 (`!f:num->int. !s k.
     0 < s
     ==> isum (k * s..(k + 1) * s - 1) f =
         isum (0..s - 1) (\j. f (k * s + j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (SPECL
     [`f:num->int`; `(k * s):num`; `((k + 1) * s - 1):num`]
     ISUM_OFFSET_0) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC
     [ARITH_RULE
       `0 < s ==> (k + 1) * s - 1 - k * s = s - 1`;
      ADD_SYM]]);;

let ISUM_SPLIT4_1_RV32 = prove
 (`!f:num->int. !s.
     0 < s
     ==> isum (0..4 * s - 1) f =
         isum (0..s - 1) f + isum (s..4 * s - 1) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (SPECL
     [`f:num->int`; `0`; `(s - 1):num`; `(3 * s):num`]
     ISUM_ADD_SPLIT) THEN
  ANTS_TAC THENL
   [ARITH_TAC;
    ASM_SIMP_TAC
     [ARITH_RULE `0 < s ==> s - 1 + 1 = s`;
      ARITH_RULE `0 < s ==> s - 1 + 3 * s = 4 * s - 1`]]);;

let ISUM_SPLIT4_2_RV32 = prove
 (`!f:num->int. !s.
     0 < s
     ==> isum (s..4 * s - 1) f =
         isum (s..2 * s - 1) f + isum (2 * s..4 * s - 1) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (SPECL
     [`f:num->int`; `s:num`; `(2 * s - 1):num`; `(2 * s):num`]
     ISUM_ADD_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC
     [ARITH_RULE `0 < s ==> 2 * s - 1 + 1 = 2 * s`;
      ARITH_RULE `0 < s ==> 2 * s - 1 + 2 * s = 4 * s - 1`]]);;

let ISUM_SPLIT4_3_RV32 = prove
 (`!f:num->int. !s.
     0 < s
     ==> isum (2 * s..4 * s - 1) f =
         isum (2 * s..3 * s - 1) f +
         isum (3 * s..4 * s - 1) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (SPECL
     [`f:num->int`; `(2 * s):num`; `(3 * s - 1):num`; `s:num`]
     ISUM_ADD_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC
     [ARITH_RULE `0 < s ==> 3 * s - 1 + 1 = 3 * s`;
      ARITH_RULE `0 < s ==> 3 * s - 1 + s = 4 * s - 1`]]);;

let ISUM_BLOCK4_RV32 = prove
 (`!f:num->int. !s.
     0 < s
     ==> isum (0..4 * s - 1) f =
         isum (0..3)
          (\k. isum (0..s - 1) (\j. f (s * k + j)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC(RAND_CONV EXPAND_ISUM_CONV) THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC
   [MATCH_MP
     (SPECL [`f:num->int`; `s:num`] ISUM_SPLIT4_1_RV32)
     (ASSUME `0 < s`);
    MATCH_MP
     (SPECL [`f:num->int`; `s:num`] ISUM_SPLIT4_2_RV32)
     (ASSUME `0 < s`);
    MATCH_MP
     (SPECL [`f:num->int`; `s:num`] ISUM_SPLIT4_3_RV32)
     (ASSUME `0 < s`)] THEN
  let block k =
    SIMP_RULE
     [MULT_CLAUSES; ADD_CLAUSES]
     (CONV_RULE
       (DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV))
       (MATCH_MP
         (SPECL
           [`f:num->int`; `s:num`; mk_small_numeral k]
           ISUM_BLOCK_OFFSET_RV32)
         (ASSUME `0 < s`))) in
  REWRITE_TAC[block 1; block 2; block 3] THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; MULT_SYM; ETA_AX]);;

let RV32_INTT_RADIX4_SUM_TRANSITION_RV32 = prove
 (`!z0 z1 z2:int. !f:num->int. !s l old new r.
     0 < s /\ r < 4 /\
     (!k. k < 4
          ==> !j. j < s
                  ==> (old k j *
                       rv32_mldsa_intt_radix4_coeff_rv32
                        z0 z1 z2 r k ==
                       new (s * k + j))
                      (mod &8380417))
     ==> (rv32_mldsa_intt_radix4_int_rv32 z0 z1 z2
           (\k. isum (0..s - 1)
             (\j. f (l + s * k + j) * old k j)) r ==
          isum (0..4 * s - 1)
           (\n. f (l + n) * new n))
         (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "spos")
    (CONJUNCTS_THEN2
      (LABEL_TAC "rlt") (LABEL_TAC "power"))) THEN
  REWRITE_TAC
   [MATCH_MP RV32_INTT_RADIX4_COEFF_EXPAND_RV32
     (ASSUME `r < 4`)] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `isum (0..3)
     (\k. isum (0..s - 1)
       (\j. (f:num->int) (l + s * k + j) *
            new (s * k + j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
     (REWRITE_RULE[]
       (ISPEC
         `(\x:int y. (x == y) (mod &8380417))`
         ISUM_RELATED)) THEN
    REWRITE_TAC
     [FINITE_NUMSEG; INT_CONG_ADD;
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
    STRIP_TAC THEN
    REWRITE_TAC[GSYM ISUM_RMUL] THEN
    MATCH_MP_TAC
     (REWRITE_RULE[]
       (ISPEC
         `(\x:int y. (x == y) (mod &8380417))`
         ISUM_RELATED)) THEN
    REWRITE_TAC
     [FINITE_NUMSEG; INT_CONG_ADD;
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    MATCH_MP_TAC INT_CONG_LMUL THEN
    USE_THEN "power"
     (fun th ->
        let kth =
          MATCH_MP
           (SPEC `k:num` th)
           (MATCH_MP
             (ARITH_RULE `k <= 3 ==> k < 4`)
             (ASSUME `k <= 3`)) in
        MATCH_MP_TAC(SPEC `j:num` kth)) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC
     [MATCH_MP
       (SPECL
         [`\n. (f:num->int) (l + n) * new n`; `s:num`]
         ISUM_BLOCK4_RV32)
       (ASSUME `0 < s`);
      INTEGER_RULE `(x:int == x) (mod n)`]]);;

let rv32_mldsa_intt_partial_rv32 = define
 `rv32_mldsa_intt_partial_rv32 (f:num->int) l s t =
    isum (0..s - 1)
      (\j. f (l + j) *
           ((&1753 pow
             ((511 * (2 * bitreverse8 (l + j) + 1)) * t))
            rem &8380417))`;;

let RV32_INTT_PARTIAL_1_RV32 = prove
 (`!f:num->int. !l.
     rv32_mldsa_intt_partial_rv32 f l 1 0 = f l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rv32_mldsa_intt_partial_rv32] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
  CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN
  REWRITE_TAC[INT_POW; MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_INT_CONV) THEN
  REWRITE_TAC[INT_MUL_RID]);;

let RV32_INTT_INPUT_PARTIAL_CONG_RV32 = prove
 (`!f:num->int. !l.
     (f l == rv32_mldsa_intt_partial_rv32 f l 1 0)
     (mod &0)`,
  REWRITE_TAC
   [INTEGER_RULE `(x:int == y) (mod &0) <=> x = y`;
    RV32_INTT_PARTIAL_1_RV32]);;

(* ========================================================================= *)
(* Direct inverse-transform connection for the RV32 partial recurrence.      *)
(* ========================================================================= *)


let RV32_INTT_INVERSE_ROOT_CONG_RV32 = prove
 (`!n.
     (((&1753:int) pow (511 * n)) rem &8380417 ==
      (&731434:int) pow n)
     (mod &8380417)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM] THEN
  MATCH_ACCEPT_TAC
   (GSYM(SPEC `n:num` MLDSA_INVERSE_ROOT_POWER)));;

let RV32_INTT_SCALE_CONG_RV32 = prove
 (`((&16382:int) == &2 pow 24) (mod &8380417)`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let RV32_INTT_PARTIAL_256_UNSCALED_CONG_RV32 = prove
 (`!f:num->int. !k.
     (rv32_mldsa_intt_partial_rv32 f 0 256 k ==
      isum (0..255)
       (\j. f j *
            (&731434:int) pow
             ((2 * bitreverse8 j + 1) * k)))
     (mod &8380417)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rv32_mldsa_intt_partial_rv32] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; MULT_ASSOC] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[]
     (ISPEC
       `(\x:int y. (x == y) (mod &8380417))`
       ISUM_RELATED)) THEN
  REWRITE_TAC
   [FINITE_NUMSEG; INT_CONG_ADD;
    INTEGER_RULE `(x:int == x) (mod n)`] THEN
  X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC INT_CONG_LMUL THEN
  REWRITE_TAC
   [ARITH_RULE `(511 * a) * k = 511 * (a * k)`] THEN
  MATCH_ACCEPT_TAC
   (SPEC
     `(2 * bitreverse8 j + 1) * k`
     RV32_INTT_INVERSE_ROOT_CONG_RV32));;

let RV32_INTT_PARTIAL_256_CONG_RV32 = prove
 (`!f:num->int. !k.
     (rv32_mldsa_intt_partial_rv32 f 0 256 k * &16382 ==
      mldsa_bitreverse_inverse_ntt f k)
     (mod &8380417)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLDSA_BITREVERSE_INVERSE_NTT_REORDERED] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `isum (0..255)
     (\j. (f:num->int) j *
          (&731434:int) pow
           ((2 * bitreverse8 j + 1) * k)) *
    &2 pow 24` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MUL THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC
       (SPECL
         [`f:num->int`; `k:num`]
         RV32_INTT_PARTIAL_256_UNSCALED_CONG_RV32);
      MATCH_ACCEPT_TAC RV32_INTT_SCALE_CONG_RV32];
    REWRITE_TAC
     [GSYM INT_REM_EQ; INT_REM_REM; INT_MUL_SYM]]);;

(* ========================================================================= *)
(* Concrete partial-transform transitions for the inverse NTT.              *)
(* ========================================================================= *)


let RV32_INTT_ROOT_PRODUCT_RV32 = prove
 (`!c s r d e t.
     c * s * r = e * 512 + d
     ==> (((&1753:int) pow (c * t) rem &8380417) *
          ((&1753:int) pow d rem &8380417) ==
          (&1753:int) pow (c * (t + s * r)) rem &8380417)
         (mod &8380417)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `(&1753:int) pow (c * t + d) rem &8380417` THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC
     (SPECL [`c * t`; `d:num`]
       MLDSA_ROOT_POWER_REM_MUL_CONG_FAST);
    MATCH_MP_TAC MLDSA_ROOT_POWER_REM_MOD_CONG_FAST THEN
    SUBGOAL_THEN
     `c * (t + s * r) = e * 512 + (c * t + d)`
     SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      ARITH_TAC;
      REWRITE_TAC[MOD_MULT_ADD]]]);;

(* Specialize the root-product theorem to concrete nonnegative parameters.
   The rule checks the required multiple-of-512 identity with arithmetic and
   returns the resulting congruence theorem without reevaluating either root
   power. *)

let RV32_INTT_ROOT_PRODUCT_RULE_FAST c s r d =
  let delta = (c * s * r - d) / 512 in
  if c < 0 || s < 0 || r < 0 || d < 0 ||
     c * s * r < d ||
     c * s * r - d <> 512 * delta
  then failwith "RV32_INTT_ROOT_PRODUCT_RULE_FAST" else
  let ctm = mk_small_numeral c
  and stm = mk_small_numeral s
  and rtm = mk_small_numeral r
  and dtm = mk_small_numeral d
  and deltatm = mk_small_numeral delta in
  let premise =
    EQT_ELIM
     (NUM_REDUCE_CONV
       (subst
         [ctm,`C:num`; stm,`S:num`; rtm,`R:num`;
          dtm,`D:num`; deltatm,`E:num`]
         `C * S * R = E * 512 + D`)) in
  MATCH_MP
   (SPECL [ctm;stm;rtm;dtm;deltatm]
     RV32_INTT_ROOT_PRODUCT_RV32)
   premise;;

let RV32_INTT_BITREVERSE8_NUM n =
  let rec reverse i x y =
    if i = 8 then y
    else reverse (i + 1) (x / 2) (2 * y + x mod 2) in
  reverse 0 n 0;;

let RV32_INTT_BITREVERSE8_NUMS =
  Array.init 256 RV32_INTT_BITREVERSE8_NUM;;

let RV32_INTT_ROOT_CONGS =
  Array.init 256
   (fun n ->
      let ntm = mk_small_numeral n in
      let rtm = mk_comb (`rv32_mldsa_ntt_root`,ntm)
      and btm = mk_comb (`bitreverse8`,ntm) in
      let eth = RV32_MLDSA_NTT_ROOT_CONV rtm
      and bth =
        GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES] btm in
      SUBS[eth;bth]
       (SPEC ntm RV32_MLDSA_NTT_ROOT_CONG_FAST));;

let RV32_INTT_INT_CONG_LHS th =
  let _,args = strip_comb(concl th) in
  List.nth args 0;;

let RV32_INTT_BUILD_ROOT_PATTERN p g =
  let q = 3 - p in
  let groups = 1 lsl (2 * q) in
  if p < 0 || p > 3 || g < 0 || g >= groups
  then failwith "RV32_INTT_BUILD_ROOT_PATTERN" else
  let i = groups - 1 - g in
  let n0 = (1 lsl (2 * q)) + i
  and n1 = (1 lsl (2 * q + 1)) + 2 * i in
  let h0 = RV32_INTT_ROOT_CONGS.(n0)
  and h1 = RV32_INTT_ROOT_CONGS.(n1)
  and h2 = RV32_INTT_ROOT_CONGS.(n1 + 1) in
  let a = mk_small_numeral RV32_INTT_BITREVERSE8_NUMS.(n1) in
  let z0 = RV32_INTT_INT_CONG_LHS h0
  and z1 = RV32_INTT_INT_CONG_LHS h1
  and z2 = RV32_INTT_INT_CONG_LHS h2 in
  let pth =
    CONV_RULE
     (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
     (SPECL [a;z0;z1;z2]
       RV32_INTT_COEFF_PATTERN_RV32) in
  MATCH_MP pth (CONJ h0 (CONJ h1 h2));;

let RV32_INTT_TRANSITION_OFFSET p =
  if p = 0 then 0
  else if p = 1 then 64
  else if p = 2 then 80
  else if p = 3 then 84
  else failwith "RV32_INTT_TRANSITION_OFFSET";;

let RV32_INTT_ROOT_PATTERNS =
  Array.of_list
   (flat
     (map
       (fun p ->
          let s = 1 lsl (2 * p) in
          let groups = 64 / s in
          map (RV32_INTT_BUILD_ROOT_PATTERN p)
            (0--(groups - 1)))
       (0--3)));;

let RV32_INTT_ROOT_PATTERN_ROOTS th =
  let _,body = strip_forall(concl th) in
  let _,cbody = dest_imp body in
  let _,cargs = strip_comb cbody in
  let coeff = List.nth cargs 0 in
  let _,args = strip_comb coeff in
  List.nth args 0,List.nth args 1,List.nth args 2;;

let RV32_INTT_STEP_EXPONENT a k =
  if k = 0 then a + 384
  else if k = 1 then a + 128
  else if k = 2 then a + 256
  else a;;

(* Build the compact congruence for output r of group g in inverse pass p.
   The rule checks `p`, `g`, and `r`, combines the cached table-root facts for
   the four butterfly inputs, and proves one transition between partial
   transforms. *)

let RV32_INTT_PARTIAL_TRANSITION_RULE p g r =
  let s = 1 lsl (2 * p) in
  let groups = 64 / s in
  if p < 0 || p > 3 || g < 0 || g >= groups ||
     r < 0 || r >= 4
  then failwith "RV32_INTT_PARTIAL_TRANSITION_RULE" else
  let q = 3 - p in
  let i = groups - 1 - g in
  let n1 = (1 lsl (2 * q + 1)) + 2 * i in
  let a = RV32_INTT_BITREVERSE8_NUM n1 in
  let l = 4 * s * g in
  let coeff =
    RV32_INTT_ROOT_PATTERNS.
     (RV32_INTT_TRANSITION_OFFSET p + g) in
  let z0,z1,z2 = RV32_INTT_ROOT_PATTERN_ROOTS coeff in
  let rtm = mk_small_numeral r in
  let rlt =
    EQT_ELIM
     (NUM_REDUCE_CONV
       (subst [rtm,`r:num`] `r < 4`)) in
  let coefficient k =
    let ktm = mk_small_numeral k in
    let klt =
      EQT_ELIM
       (NUM_REDUCE_CONV
         (subst [ktm,`k:num`] `k < 4`)) in
    CONV_RULE
     (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
     (REWRITE_RULE
       [rv32_mldsa_intt_step_exponent_rv32]
       (MATCH_MP
         (SPECL [rtm;ktm] coeff)
         (CONJ rlt klt))) in
  let coefficients =
    Array.init 4 coefficient in
  let leaf k j =
    let index = l + s * k + j in
    let c =
      511 * (2 * RV32_INTT_BITREVERSE8_NUMS.(index) + 1) in
    let d = RV32_INTT_STEP_EXPONENT a k * r in
    let cth = coefficients.(k) in
    let _,cargs = strip_comb(concl cth) in
    let clhs = List.nth cargs 0
    and crhs = List.nth cargs 1 in
    let oldexp =
      subst [mk_small_numeral c,`C:num`]
       `C * t` in
    let oldroot =
      subst [oldexp,`E:num`]
       `(&1753:int) pow E rem &8380417` in
    let lifted =
      MATCH_MP
       (SPECL
         [oldroot;clhs;crhs;`&8380417:int`]
         INT_CONG_LMUL)
       cth in
    let product =
      CONV_RULE
       (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
       (SPEC `t:num`
         (RV32_INTT_ROOT_PRODUCT_RULE_FAST c s r d)) in
    RV32_INT_CONG_TRANS_RULE_FAST lifted product in
  let leaves =
    flat
     (map
       (fun k -> map (leaf k) (0--(s - 1)))
       (0--3)) in
  let remaining_leaves = ref leaves in
  let accept_leaf (asl,w as gl) =
    match !remaining_leaves with
      th::oths when aconv (concl th) w ->
        remaining_leaves := oths;
        ACCEPT_TAC th gl
    | _ ->
        let th =
          tryfind
           (fun th ->
              if aconv (concl th) w then th
              else failwith "not this leaf")
           !remaining_leaves in
        remaining_leaves :=
          filter (fun h -> not(aconv (concl h) w))
            !remaining_leaves;
        ACCEPT_TAC th gl in
  let stm = mk_small_numeral s
  and ltm = mk_small_numeral l in
  let old =
    subst [ltm,`L:num`; stm,`S:num`]
     `\k j.
        (&1753:int) pow
          ((511 *
            (2 * bitreverse8 (L + S * k + j) + 1)) * t)
        rem &8380417` in
  let newtm =
    subst [ltm,`L:num`; stm,`S:num`; rtm,`R:num`]
     `\n.
        (&1753:int) pow
          ((511 *
            (2 * bitreverse8 (L + n) + 1)) *
           (t + S * R))
        rem &8380417` in
  let power_goal =
    subst
     [stm,`S:num`; old,`old:num->num->int`;
      newtm,`new:num->int`; z0,`z0:int`; z1,`z1:int`;
      z2,`z2:int`; rtm,`R:num`]
     `!k. k < 4
          ==> !j. j < S
                  ==> (old k j *
                       rv32_mldsa_intt_radix4_coeff_rv32
                        z0 z1 z2 R k ==
                       new (S * k + j))
                      (mod &8380417)` in
  let power =
    TAC_PROOF
     (([],power_goal),
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC
       (DEPTH_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC
       (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
      CONV_TAC
       (TOP_DEPTH_CONV
         (CHANGED_CONV
           (GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES]))) THEN
      CONV_TAC
       (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
      REPEAT CONJ_TAC THEN accept_leaf) in
  let spos =
    EQT_ELIM
     (NUM_REDUCE_CONV
       (subst [stm,`s:num`] `0 < s`)) in
  let raw =
    MATCH_MP
     (SPECL
       [z0;z1;z2;`f:num->int`;stm;ltm;old;newtm;rtm]
       RV32_INTT_RADIX4_SUM_TRANSITION_RV32)
     (CONJ spos (CONJ rlt power)) in
  let raw =
    REWRITE_RULE[ADD_ASSOC]
     (CONV_RULE
       ((DEPTH_CONV BETA_CONV) THENC
        (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV))
       raw) in
  let goal =
    subst
     [z0,`z0:int`; z1,`z1:int`; z2,`z2:int`;
      stm,`S:num`; ltm,`L:num`; rtm,`R:num`]
     `!f:num->int. !t.
       (rv32_mldsa_intt_radix4_int_rv32 z0 z1 z2
         (\k. rv32_mldsa_intt_partial_rv32
                f (L + S * k) S t) R ==
        rv32_mldsa_intt_partial_rv32
         f L (4 * S) (t + S * R))
       (mod &8380417)` in
  TAC_PROOF
   (([],goal),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[rv32_mldsa_intt_partial_rv32] THEN
    CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    MATCH_ACCEPT_TAC raw);;

let RV32_INTT_PARTIAL_TRANSITIONS =
  flat
   (map
     (fun p ->
        let s = 1 lsl (2 * p) in
        let groups = 64 / s in
        flat
         (map
           (fun g ->
              map
               (RV32_INTT_PARTIAL_TRANSITION_RULE p g)
               (0--3))
           (0--(groups - 1))))
     (0--3));;
