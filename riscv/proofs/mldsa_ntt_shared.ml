(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared support for the RV32 ML-DSA forward NTT implementations.           *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_objects.ml";;
needs "riscv/proofs/mldsa_zetas.ml";;
needs "common/mlkem_mldsa.ml";;

(* Read one indexed int32 from an RV32 `wordlist_from_memory` assertion.
   Phase proofs use this theorem to select the zeta values needed by the
   current iteration without expanding all 510 table words. *)

let RV32_WORDLIST_FROM_MEMORY_EL = prove
 (`!a:int32. !n i. !s:riscvstate.
      i < n
      ==> EL i (wordlist_from_memory(a,n) s:int32 list) =
          read
           (memory :> bytes32(word_add a (word(4 * i)))) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`a:int32`; `n:num`; `i:num`; `s:riscvstate`]
     (INST_TYPE [`:4`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[BYTES32_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_THEN ACCEPT_TAC);;

(* Use the common expression-abbreviation tactic only for readable RV32
   register reads. This keeps large butterfly expressions compact while
   leaving their arithmetic structure available to later proof steps. *)

let RV32_SIMPLIFY_ABBREV_TAC =
  let readable =
    can (term_match [] `read X (s:riscvstate):int32 = whatever`) in
  GEN_SIMPLIFY_ABBREV_TAC readable;;

(* One radix-4 forward butterfly as implemented by the machine code. The
   three table pairs supply the low-layer root and two high-layer roots. *)

let rv32_mldsa_radix4 = define
 `rv32_mldsa_radix4
    (zw0:int32#int32) (zw1:int32#int32) (zw2:int32#int32)
    (f:num->int32) k =
    let t2 = mldsa_barrett_mul zw0 (f 2)
    and t3 = mldsa_barrett_mul zw0 (f 3) in
    let u0 = word_add (f 0) t2
    and u1 = word_add (f 1) t3
    and u2 = word_sub (f 0) t2
    and u3 = word_sub (f 1) t3 in
    let v1 = mldsa_barrett_mul zw1 u1
    and v3 = mldsa_barrett_mul zw2 u3 in
    if k = 0 then word_add u0 v1
    else if k = 1 then word_sub u0 v1
    else if k = 2 then word_add u2 v3
    else word_sub u2 v3`;;

(* First forward phase: apply the first root triplet to coefficients separated
   by 64 words. *)

let rv32_mldsa_ntt_phase1 = define
 `rv32_mldsa_ntt_phase1 (x:num->int32) i r =
    rv32_mldsa_radix4
      (iword (-- &3572223),iword (-- &1830765815))
      (iword (&3765607),iword (&1929875198))
      (iword (&3761513),iword (&1927777021))
      (\k. x (i + 64 * k)) r`;;

let RV32_NTT_REWRITE_STORES_TAC =
  MAP_EVERY
   (fun label ->
      USE_THEN label (fun th -> ONCE_REWRITE_TAC[GSYM th]))
   ["store3"; "store2"; "store1"; "store0"];;

let RV32_NTT_COEFFICIENT_NONOVERLAPPING = prove
 (`!a:int32 i j r q.
      i < 64 /\ j < 64 /\ r < 4 /\ q < 4 /\
      ~(j = i /\ r = q)
      ==> nonoverlapping
           (word_add a (word(4 * (j + 64 * r))),4)
           (word_add a (word(4 * (i + 64 * q))),4)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonoverlapping] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_BOTH THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ASM_CASES_TAC `r:num = q` THENL
   [SUBGOAL_THEN `j:num < i \/ i < j` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
    SUBGOAL_THEN `r:num < q \/ q < r` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let RV32_NTT_COEFFICIENT_ORTHOGONAL = prove
 (`!a:int32 i j r q.
      i < 64 /\ j < 64 /\ r < 4 /\ q < 4 /\
      ~(j = i /\ r = q)
      ==> orthogonal_components
           ((memory :> bytes32
             (word_add a (word(4 * (j + 64 * r)))))
            : (riscvstate,int32)component)
           ((memory :> bytes32
             (word_add a (word(4 * (i + 64 * q)))))
            : (riscvstate,int32)component)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping
      (word_add (a:int32) (word(4 * (j + 64 * r))),4)
      (word_add a (word(4 * (i + 64 * q))),4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`a:int32`; `i:num`; `j:num`; `r:num`; `q:num`]
       RV32_NTT_COEFFICIENT_NONOVERLAPPING) THEN
    ASM_REWRITE_TAC[];
    ORTHOGONAL_COMPONENTS_TAC]);;

let RV32_NTT_READ_OVER_WRITES_TAC =
  let tac_orth = (MATCH_MP_TAC o prove)
   (`orthogonal_components c d /\
     read c s' = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]) in
  let rec tac g =
   (REFL_TAC ORELSE
    (tac_orth THEN CONJ_TAC THENL
      [FIRST
        [ASM_REWRITE_TAC[] THEN NO_TAC;
         ORTHOGONAL_COMPONENTS_TAC];
       tac])) g in
  tac;;

(* ========================================================================= *)
(* Shared preservation of the RV32 ML-DSA zeta table.                    *)
(* ========================================================================= *)

let RV32_MLDSA_NTT_TABLE_PRESERVED = prove
 (`!a zetas:int32. !s s':riscvstate.
      nonoverlapping (a,1024) (zetas,2040) /\
      (MAYCHANGE
        [PC; S0; S1; S2; S3; S4; S5;
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
        [PC; S0; S1; S2; S3; S4; S5;
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
        `[PC; S0; S1; S2; S3; S4; S5;
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

(* ========================================================================= *)
(* Radix-4 recurrence for the RV32 ML-DSA forward NTT.                       *)
(* ========================================================================= *)

let ISUM_PAIR_RV32 = INT_OF_REAL_THM SUM_PAIR;;

let ISUM_RADIX4_RV32 = prove
 (`!f:num->int. !m.
      isum (0..4 * m + 3) f =
      isum (0..m)
       (\j. f (4 * j) + f (4 * j + 1) +
            f (4 * j + 2) + f (4 * j + 3))`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `isum (0..2 * m + 1)
      (\i. f (2 * i) + f (2 * i + 1))` THEN
  CONJ_TAC THENL
   [MP_TAC
     (SPECL [`f:num->int`; `0`; `2 * m + 1`]
       ISUM_PAIR_RV32) THEN
    SIMP_TAC[MULT_CLAUSES;
      ARITH_RULE `2 * (2 * m + 1) + 1 = 4 * m + 3`];
    MP_TAC
     (SPECL
       [`\i. (f:num->int) (2 * i) + f (2 * i + 1)`;
        `0`; `m:num`]
       ISUM_PAIR_RV32) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    SIMP_TAC
     [ARITH_RULE `2 * (2 * j) = 4 * j`;
      ARITH_RULE `2 * (2 * j) + 1 = 4 * j + 1`;
      ARITH_RULE `2 * (2 * j + 1) = 4 * j + 2`;
      ARITH_RULE `2 * (2 * j + 1) + 1 = 4 * j + 3`;
      INT_ADD_ASSOC]]);;

let rv32_mldsa_radix4_int_rv32 = define
 `rv32_mldsa_radix4_int_rv32
    (z0:int) (z1:int) (z2:int) (f:num->int) k =
    let t2 = f 2 * z0
    and t3 = f 3 * z0 in
    let u0 = f 0 + t2
    and u1 = f 1 + t3
    and u2 = f 0 - t2
    and u3 = f 1 - t3 in
    let v1 = u1 * z1
    and v3 = u3 * z2 in
    if k = 0 then u0 + v1
    else if k = 1 then u0 - v1
    else if k = 2 then u2 + v3
    else u2 - v3`;;

let RV32_INDEX4_CASES_RV32 = prove
 (`!r. r < 4 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`,
  ARITH_TAC);;

let RV32_RADIX4_INT_ISUM_RV32 = prove
 (`!z0 z1 z2:int. !a:num->num->int. !m r.
      r < 4
      ==> rv32_mldsa_radix4_int_rv32 z0 z1 z2
            (\k. isum (0..m) (a k)) r =
          isum (0..m)
            (\j. rv32_mldsa_radix4_int_rv32 z0 z1 z2
                  (\k. a k j) r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[rv32_mldsa_radix4_int_rv32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC
   (DEPTH_CONV (CHANGED_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC
   [ISUM_ADD_NUMSEG; ISUM_SUB_NUMSEG; ISUM_RMUL; ETA_AX]);;

let RV32_INT_CONG_REM_TAC_RV32 (asl,w as gl) =
  let _,args = strip_comb w in
  let l = List.nth args 0
  and r = List.nth args 1
  and n = rand(List.nth args 2) in
  (MATCH_MP_TAC
    (fst(EQ_IMP_RULE(ISPECL [l;r;n] INT_REM_EQ)))) gl;;

let MLDSA_ROOT_POWER_MOD_CONG_RV32 = prove
 (`!a b.
      a MOD 512 = b MOD 512
      ==> ((&1753:int) pow a == (&1753:int) pow b)
          (mod (&8380417:int))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  RV32_INT_CONG_REM_TAC_RV32 THEN
  GEN_REWRITE_TAC LAND_CONV [MLDSA_ROOT_POWER_PERIODIC] THEN
  GEN_REWRITE_TAC RAND_CONV [MLDSA_ROOT_POWER_PERIODIC] THEN
  ASM_REWRITE_TAC[]);;

(* A stride-s partial transform contains 256 / s coefficients from one
   residue class. The four stages below use strides 64, 16, 4, and 1. *)

let rv32_mldsa_ntt_partial_rv32 = define
 `rv32_mldsa_ntt_partial_rv32 (f:num->int) s l t =
    isum (0..256 DIV s - 1)
      (\j. f (l + s * j) *
           ((&1753 pow
             ((2 * bitreverse8 (s * t) + 1) * s * j))
            rem &8380417))`;;

let MLDSA_ROOT_POWER_REM_MUL_CONG_FAST = prove
 (`!a b.
    ((((&1753:int) pow a rem &8380417) *
      ((&1753:int) pow b rem &8380417) ==
      (&1753:int) pow (a + b) rem &8380417)
     (mod &8380417))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_POW_ADD] THEN
  REWRITE_TAC[INT_MUL_REM; INT_REM_REM]);;

let MLDSA_ROOT_POWER_REM_MOD_CONG_FAST = prove
 (`!a b.
    a MOD 512 = b MOD 512
    ==> (((&1753:int) pow a rem &8380417 ==
          (&1753:int) pow b rem &8380417)
         (mod &8380417))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (MATCH_MP
     (SPECL [`a:num`; `b:num`] MLDSA_ROOT_POWER_MOD_CONG_RV32)
     (ASSUME `a MOD 512 = b MOD 512`)) THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let RV32_8380416_NEG1_CONG_FAST = prove
 (`((&8380416:int) == -- &1) (mod &8380417)`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let RV32_INT_CONG_SYM_RULE_FAST th =
  let _,args = strip_comb(concl th) in
  let l = List.nth args 0
  and r = List.nth args 1
  and n = rand(List.nth args 2) in
  MATCH_MP
   (fst(EQ_IMP_RULE(SPECL [l;r;n] INT_CONG_SYM)))
   th;;

let RV32_INT_CONG_NEG_RULE_FAST th =
  let _,args = strip_comb(concl th) in
  let l = List.nth args 0
  and r = List.nth args 1
  and n = rand(List.nth args 2) in
  REWRITE_RULE[INT_MUL_LNEG; INT_MUL_LID]
   (MATCH_MP
     (SPECL [`--(&1:int)`;l;r;n] INT_CONG_LMUL)
     th);;

let RV32_INT_CONG_TRANS_RULE_FAST th1 th2 =
  MATCH_MP INT_CONG_TRANS (CONJ th1 th2);;

let MLDSA_ROOT_POWER_ADD_256_CONG_FAST =
  let a = `a:num` in
  let pa = `(&1753:int) pow a rem &8380417` in
  let lhs = `((&1753:int) pow a rem &8380417) * &8380416` in
  let pnext = `(&1753:int) pow (a + 256) rem &8380417` in
  let q = `(&8380417:int)` in
  let hm =
    REWRITE_RULE[MLDSA_ROOT_POWERS.(256)]
     (SPECL [a; `256`] MLDSA_ROOT_POWER_REM_MUL_CONG_FAST) in
  let hs =
    MATCH_MP
     (fst(EQ_IMP_RULE(SPECL [lhs;pnext;q] INT_CONG_SYM)))
     hm in
  let hl =
    MATCH_MP
     (SPECL [pa; `(&8380416:int)`; `--(&1:int)`; q]
       INT_CONG_LMUL)
     RV32_8380416_NEG1_CONG_FAST in
  let hl' = REWRITE_RULE[INT_MUL_RNEG; INT_MUL_RID] hl in
  GEN a (RV32_INT_CONG_TRANS_RULE_FAST hs hl');;

let MOD512_ADD_512_FAST = prove
 (`!a. (a + 512) MOD 512 = a MOD 512`,
  GEN_TAC THEN
  SUBGOAL_THEN `a + 512 = a + 1 * 512` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let MOD512_ADD_1024_FAST = prove
 (`!a. (a + 1024) MOD 512 = a MOD 512`,
  GEN_TAC THEN
  SUBGOAL_THEN `a + 1024 = a + 2 * 512` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let MLDSA_ROOT_POWER_ADD_512_CONG_FAST = prove
 (`!a.
    (((&1753:int) pow (a + 512) rem &8380417 ==
      (&1753:int) pow a rem &8380417)
     (mod &8380417))`,
  GEN_TAC THEN
  MATCH_MP_TAC MLDSA_ROOT_POWER_REM_MOD_CONG_FAST THEN
  REWRITE_TAC[MOD512_ADD_512_FAST]);;

let MLDSA_ROOT_POWER_ADD_1024_CONG_FAST = prove
 (`!a.
    (((&1753:int) pow (a + 1024) rem &8380417 ==
      (&1753:int) pow a rem &8380417)
     (mod &8380417))`,
  GEN_TAC THEN
  MATCH_MP_TAC MLDSA_ROOT_POWER_REM_MOD_CONG_FAST THEN
  REWRITE_TAC[MOD512_ADD_1024_FAST]);;

let RV32_MLDSA_NTT_ROOT_CONG_FAST = prove
 (`!n.
    (rv32_mldsa_ntt_root n ==
     (&1753:int) pow (bitreverse8 n) rem &8380417)
    (mod &8380417)`,
  GEN_TAC THEN
  REWRITE_TAC[rv32_mldsa_ntt_root] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC
   [INTEGER_RULE `(x:int == x) (mod n)`;
    INTEGER_RULE `(x - n:int == x) (mod n)`]);;

(* Coefficients of one integer radix-4 butterfly. *)

let rv32_mldsa_radix4_coeff_fast = define
 `rv32_mldsa_radix4_coeff_fast (z0:int) z1 z2 r k =
    if r = 0 then
      if k = 0 then &1
      else if k = 1 then z1
      else if k = 2 then z0
      else if k = 3 then z0 * z1
      else &0
    else if r = 1 then
      if k = 0 then &1
      else if k = 1 then --z1
      else if k = 2 then z0
      else if k = 3 then --(z0 * z1)
      else &0
    else if r = 2 then
      if k = 0 then &1
      else if k = 1 then z2
      else if k = 2 then --z0
      else if k = 3 then --(z0 * z2)
      else &0
    else
      if k = 0 then &1
      else if k = 1 then --z2
      else if k = 2 then --z0
      else if k = 3 then z0 * z2
      else &0`;;

let RV32_COEFF_PATTERN_R0_FAST = prove
 (`!a z0 z1 z2:int.
    ((z0 == (&1753:int) pow (2 * a) rem &8380417)
       (mod &8380417) /\
     (z1 == (&1753:int) pow a rem &8380417)
       (mod &8380417) /\
     (z2 == (&1753:int) pow (a + 128) rem &8380417)
       (mod &8380417))
    ==> !k. k < 4
             ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 0 k ==
                  (&1753:int) pow (a * k) rem &8380417)
                 (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES;
      MLDSA_ROOT_POWERS.(0);
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_ACCEPT_TAC (INTEGER_RULE `(x:int == x) (mod n)`);
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h1" MATCH_ACCEPT_TAC;
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE `a * 2 = 2 * a`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0" MATCH_ACCEPT_TAC;
    REWRITE_TAC[rv32_mldsa_radix4_coeff_fast] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        USE_THEN "h1"
         (fun h1 ->
            let th0 = MATCH_MP INT_CONG_MUL (CONJ h0 h1) in
            let th1 =
              REWRITE_RULE[ARITH_RULE `2 * a + a = a * 3`]
               (SPECL [`2 * a`; `a:num`]
                 MLDSA_ROOT_POWER_REM_MUL_CONG_FAST) in
            MATCH_ACCEPT_TAC
             (RV32_INT_CONG_TRANS_RULE_FAST th0 th1)))
   ]);;

let RV32_COEFF_PATTERN_R1_FAST = prove
 (`!a z0 z1 z2:int.
    ((z0 == (&1753:int) pow (2 * a) rem &8380417)
       (mod &8380417) /\
     (z1 == (&1753:int) pow a rem &8380417)
       (mod &8380417) /\
     (z2 == (&1753:int) pow (a + 128) rem &8380417)
       (mod &8380417))
    ==> !k. k < 4
             ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 1 k ==
                  (&1753:int) pow ((a + 256) * k) rem &8380417)
                 (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES;
      MLDSA_ROOT_POWERS.(0);
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_ACCEPT_TAC (INTEGER_RULE `(x:int == x) (mod n)`);
    REWRITE_TAC[rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h1"
     (fun h1 ->
        let th0 = RV32_INT_CONG_NEG_RULE_FAST h1 in
        let th1 =
          RV32_INT_CONG_SYM_RULE_FAST
           (SPEC `a:num` MLDSA_ROOT_POWER_ADD_256_CONG_FAST) in
        MATCH_ACCEPT_TAC
         (RV32_INT_CONG_TRANS_RULE_FAST th0 th1));
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE `(a + 256) * 2 = 2 * a + 512`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        let th1 =
          RV32_INT_CONG_SYM_RULE_FAST
           (SPEC `2 * a` MLDSA_ROOT_POWER_ADD_512_CONG_FAST) in
        MATCH_ACCEPT_TAC
         (RV32_INT_CONG_TRANS_RULE_FAST h0 th1));
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE
       `(a + 256) * 3 = (3 * a + 256) + 512`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        USE_THEN "h1"
         (fun h1 ->
            let th0 = MATCH_MP INT_CONG_MUL (CONJ h0 h1) in
            let th1 =
              REWRITE_RULE[ARITH_RULE `2 * a + a = 3 * a`]
               (SPECL [`2 * a`; `a:num`]
                 MLDSA_ROOT_POWER_REM_MUL_CONG_FAST) in
            let th2 =
              RV32_INT_CONG_NEG_RULE_FAST
               (RV32_INT_CONG_TRANS_RULE_FAST th0 th1) in
            let th3 =
              RV32_INT_CONG_SYM_RULE_FAST
               (SPEC `3 * a` MLDSA_ROOT_POWER_ADD_256_CONG_FAST) in
            let th4 =
              RV32_INT_CONG_SYM_RULE_FAST
               (SPEC `3 * a + 256`
                 MLDSA_ROOT_POWER_ADD_512_CONG_FAST) in
            MATCH_ACCEPT_TAC
             (RV32_INT_CONG_TRANS_RULE_FAST
               (RV32_INT_CONG_TRANS_RULE_FAST th2 th3)
               th4)))
   ]);;

let RV32_COEFF_PATTERN_R2_FAST = prove
 (`!a z0 z1 z2:int.
    ((z0 == (&1753:int) pow (2 * a) rem &8380417)
       (mod &8380417) /\
     (z1 == (&1753:int) pow a rem &8380417)
       (mod &8380417) /\
     (z2 == (&1753:int) pow (a + 128) rem &8380417)
       (mod &8380417))
    ==> !k. k < 4
             ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 2 k ==
                  (&1753:int) pow ((a + 128) * k) rem &8380417)
                 (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES;
      MLDSA_ROOT_POWERS.(0);
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_ACCEPT_TAC (INTEGER_RULE `(x:int == x) (mod n)`);
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h2" MATCH_ACCEPT_TAC;
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE `(a + 128) * 2 = 2 * a + 256`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        let th0 = RV32_INT_CONG_NEG_RULE_FAST h0 in
        let th1 =
          RV32_INT_CONG_SYM_RULE_FAST
           (SPEC `2 * a` MLDSA_ROOT_POWER_ADD_256_CONG_FAST) in
        MATCH_ACCEPT_TAC
         (RV32_INT_CONG_TRANS_RULE_FAST th0 th1));
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE `(a + 128) * 3 = 3 * a + 384`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        USE_THEN "h2"
         (fun h2 ->
            let th0 = MATCH_MP INT_CONG_MUL (CONJ h0 h2) in
            let th1 =
              REWRITE_RULE
               [ARITH_RULE `2 * a + (a + 128) = 3 * a + 128`]
               (SPECL [`2 * a`; `a + 128`]
                 MLDSA_ROOT_POWER_REM_MUL_CONG_FAST) in
            let th2 =
              RV32_INT_CONG_NEG_RULE_FAST
               (RV32_INT_CONG_TRANS_RULE_FAST th0 th1) in
            let th3 =
              REWRITE_RULE
               [ARITH_RULE `(3 * a + 128) + 256 = 3 * a + 384`]
               (RV32_INT_CONG_SYM_RULE_FAST
                 (SPEC `3 * a + 128`
                   MLDSA_ROOT_POWER_ADD_256_CONG_FAST)) in
            MATCH_ACCEPT_TAC
             (RV32_INT_CONG_TRANS_RULE_FAST th2 th3)))
   ]);;

let RV32_COEFF_PATTERN_R3_FAST = prove
 (`!a z0 z1 z2:int.
    ((z0 == (&1753:int) pow (2 * a) rem &8380417)
       (mod &8380417) /\
     (z1 == (&1753:int) pow a rem &8380417)
       (mod &8380417) /\
     (z2 == (&1753:int) pow (a + 128) rem &8380417)
       (mod &8380417))
    ==> !k. k < 4
             ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 3 k ==
                  (&1753:int) pow ((a + 384) * k) rem &8380417)
                 (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES;
      MLDSA_ROOT_POWERS.(0);
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    MATCH_ACCEPT_TAC (INTEGER_RULE `(x:int == x) (mod n)`);
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast; MULT_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h2"
     (fun h2 ->
        let th0 = RV32_INT_CONG_NEG_RULE_FAST h2 in
        let th1 =
          REWRITE_RULE
           [ARITH_RULE `(a + 128) + 256 = a + 384`]
           (RV32_INT_CONG_SYM_RULE_FAST
             (SPEC `a + 128`
               MLDSA_ROOT_POWER_ADD_256_CONG_FAST)) in
        MATCH_ACCEPT_TAC
         (RV32_INT_CONG_TRANS_RULE_FAST th0 th1));
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE
       `(a + 384) * 2 = (2 * a + 256) + 512`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        let th0 = RV32_INT_CONG_NEG_RULE_FAST h0 in
        let th1 =
          RV32_INT_CONG_SYM_RULE_FAST
           (SPEC `2 * a` MLDSA_ROOT_POWER_ADD_256_CONG_FAST) in
        let th2 =
          RV32_INT_CONG_SYM_RULE_FAST
           (SPEC `2 * a + 256`
             MLDSA_ROOT_POWER_ADD_512_CONG_FAST) in
        MATCH_ACCEPT_TAC
         (RV32_INT_CONG_TRANS_RULE_FAST
           (RV32_INT_CONG_TRANS_RULE_FAST th0 th1)
           th2));
    REWRITE_TAC
     [rv32_mldsa_radix4_coeff_fast;
      ARITH_RULE
       `(a + 384) * 3 = (3 * a + 128) + 1024`] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
    USE_THEN "h0"
     (fun h0 ->
        USE_THEN "h2"
         (fun h2 ->
            let th0 = MATCH_MP INT_CONG_MUL (CONJ h0 h2) in
            let th1 =
              REWRITE_RULE
               [ARITH_RULE `2 * a + (a + 128) = 3 * a + 128`]
               (SPECL [`2 * a`; `a + 128`]
                 MLDSA_ROOT_POWER_REM_MUL_CONG_FAST) in
            let th2 =
              RV32_INT_CONG_TRANS_RULE_FAST th0 th1 in
            let th3 =
              RV32_INT_CONG_SYM_RULE_FAST
               (SPEC `3 * a + 128`
                 MLDSA_ROOT_POWER_ADD_1024_CONG_FAST) in
            MATCH_ACCEPT_TAC
             (RV32_INT_CONG_TRANS_RULE_FAST th2 th3)))
   ]);;

let ISUM_0_3_FAST = prove
 (`!f:num->int.
     isum (0..3) f = f 0 + f 1 + f 2 + f 3`,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  INT_ARITH_TAC);;

let ISUM_RADIX4_NESTED_FAST = prove
 (`!f:num->int. !m.
     isum (0..4 * m + 3) f =
     isum (0..m) (\j. isum (0..3) (\k. f (4 * j + k)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ISUM_RADIX4_RV32; ISUM_0_3_FAST; ADD_CLAUSES]);;

let RV32_RADIX4_COEFF_EXPAND_FAST = prove
 (`!z0 z1 z2:int. !f:num->int. !r.
     r < 4
     ==> rv32_mldsa_radix4_int_rv32 z0 z1 z2 f r =
         isum (0..3)
          (\k. f k *
               rv32_mldsa_radix4_coeff_fast z0 z1 z2 r k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RV32_INDEX4_CASES_RV32) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
   [rv32_mldsa_radix4_int_rv32;
    rv32_mldsa_radix4_coeff_fast] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(RAND_CONV EXPAND_ISUM_CONV) THEN
  CONV_TAC(DEPTH_CONV(CHANGED_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC INT_RING);;

let RV32_RADIX4_ROOT_SUM_CONG_FAST = prove
 (`!z0 z1 z2:int. !f:num->int. !b r.
     r < 4 /\
     (!k. k < 4
          ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 r k ==
               (&1753:int) pow (b * k) rem &8380417)
              (mod &8380417))
     ==> (rv32_mldsa_radix4_int_rv32 z0 z1 z2 f r ==
          isum (0..3)
           (\k. f k *
                ((&1753:int) pow (b * k) rem &8380417)))
         (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "rlt") (LABEL_TAC "coeff")) THEN
  REWRITE_TAC
   [MATCH_MP RV32_RADIX4_COEFF_EXPAND_FAST
     (ASSUME `r < 4`)] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[]
     (ISPEC
       `(\x:int y. (x == y) (mod &8380417))`
       ISUM_RELATED)) THEN
  REWRITE_TAC
   [FINITE_NUMSEG; INT_CONG_ADD;
    INTEGER_RULE `(x:int == x) (mod n)`] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC INT_CONG_LMUL THEN
  USE_THEN "coeff"
   (fun th -> MATCH_MP_TAC(SPEC `k:num` th)) THEN
  ASM_ARITH_TAC);;

let RV32_RADIX4_POWER_BLOCK_CONG_FAST = prove
 (`!z0 z1 z2:int. !f:num->int. !a b r.
     r < 4 /\
     (!k. k < 4
          ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 r k ==
               (&1753:int) pow (b * k) rem &8380417)
              (mod &8380417)) /\
     (!k. k < 4
          ==> (((&1753:int) pow a rem &8380417) *
               ((&1753:int) pow (b * k) rem &8380417) ==
               (&1753:int) pow (b * (4 * j + k)) rem &8380417)
              (mod &8380417))
     ==> (rv32_mldsa_radix4_int_rv32 z0 z1 z2
           (\k. f k * ((&1753:int) pow a rem &8380417)) r ==
          isum (0..3)
           (\k. f k *
                ((&1753:int) pow (b * (4 * j + k))
                 rem &8380417)))
         (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "rlt")
    (CONJUNCTS_THEN2
      (LABEL_TAC "coeff") (LABEL_TAC "power"))) THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `isum (0..3)
     (\k. ((f:num->int) k *
            ((&1753:int) pow a rem &8380417)) *
           ((&1753:int) pow (b * k) rem &8380417))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RV32_RADIX4_ROOT_SUM_CONG_FAST THEN
    USE_THEN "rlt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "coeff" ACCEPT_TAC;
    MATCH_MP_TAC
     (REWRITE_RULE[]
       (ISPEC
         `(\x:int y. (x == y) (mod &8380417))`
         ISUM_RELATED)) THEN
    REWRITE_TAC
     [FINITE_NUMSEG; INT_CONG_ADD;
      INTEGER_RULE `(x:int == x) (mod n)`] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    MATCH_MP_TAC INT_CONG_LMUL THEN
    USE_THEN "power"
     (fun th -> MATCH_MP_TAC(SPEC `k:num` th)) THEN
    ASM_ARITH_TAC]);;

let RV32_RADIX4_SUM_TRANSITION_FAST = prove
 (`!z0 z1 z2:int. !f:num->int. !s l m a b r.
     r < 4 /\
     (!k. k < 4
          ==> (rv32_mldsa_radix4_coeff_fast z0 z1 z2 r k ==
               (&1753:int) pow (b * k) rem &8380417)
              (mod &8380417)) /\
     (!j k. j <= m /\ k < 4
            ==> (((&1753:int) pow (a * j) rem &8380417) *
                 ((&1753:int) pow (b * k) rem &8380417) ==
                 (&1753:int) pow (b * (4 * j + k)) rem &8380417)
                (mod &8380417))
     ==> (rv32_mldsa_radix4_int_rv32 z0 z1 z2
           (\k. isum (0..m)
             (\j. f (l + s * (4 * j + k)) *
                  ((&1753:int) pow (a * j) rem &8380417))) r ==
          isum (0..4 * m + 3)
           (\n. f (l + s * n) *
                ((&1753:int) pow (b * n) rem &8380417)))
         (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "rlt")
    (CONJUNCTS_THEN2
      (LABEL_TAC "coeff") (LABEL_TAC "power"))) THEN
  REWRITE_TAC
   [MATCH_MP RV32_RADIX4_INT_ISUM_RV32
     (ASSUME `r < 4`);
    ISUM_RADIX4_NESTED_FAST] THEN
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
  MATCH_MP_TAC RV32_RADIX4_POWER_BLOCK_CONG_FAST THEN
  USE_THEN "rlt" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "coeff" (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "power"
   (fun th -> MATCH_MP_TAC(SPECL [`j:num`; `k:num`] th)) THEN
  ASM_REWRITE_TAC[]);;

(* Specialize root multiplication without reevaluating concrete powers. *)

let RV32_ROOT_PRODUCT_RULE_FAST a b =
  let c = (4 * b - a) / 512 in
  if a < 0 || b < 0 || 4 * b < a ||
     4 * b - a <> 512 * c
  then failwith "RV32_ROOT_PRODUCT_RULE_FAST" else
  let atm = mk_small_numeral a
  and btm = mk_small_numeral b
  and ctm = mk_small_numeral c
  and jtm = `j:num`
  and ktm = `k:num` in
  let aexp =
    subst [atm,`A:num`]
     `A * j` in
  let bexp =
    subst [btm,`B:num`]
     `B * k` in
  let sumexp =
    subst [atm,`A:num`; btm,`B:num`]
     `A * j + B * k` in
  let rhs =
    subst [btm,`B:num`]
     `B * (4 * j + k)` in
  let eqth =
    ARITH_RULE
     (subst [atm,`A:num`; btm,`B:num`; ctm,`C:num`]
       `B * (4 * j + k) =
        C * j * 512 + (A * j + B * k)`) in
  let modeq =
    if c = 0 then
      CONV_RULE
        (DEPTH_CONV BETA_CONV)
        (AP_TERM `\n:num. n MOD 512`
          (ARITH_RULE (mk_eq(sumexp,rhs))))
    else
      SYM
       (REWRITE_RULE
         [MULT_ASSOC; MULT_CLAUSES; ADD_CLAUSES; MOD_MULT_ADD]
         (AP_TERM `\n:num. n MOD 512` eqth)) in
  let multh =
    SPECL [aexp; bexp]
     MLDSA_ROOT_POWER_REM_MUL_CONG_FAST in
  let modth =
    MATCH_MP
     (SPECL [sumexp; rhs]
       MLDSA_ROOT_POWER_REM_MOD_CONG_FAST)
     modeq in
  GENL [jtm;ktm]
   (RV32_INT_CONG_TRANS_RULE_FAST multh modth);;
