(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_invntt_tomont from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml)    *)
(* with the specification of the -O2 code.                                   *)
(*                                                                           *)
(* As at -O2, the coefficients are first scaled by a vectorized loop, and    *)
(* the layers and blocks are loops, but gcc has vectorized the butterflies   *)
(* of a block in the same way as for mlkem_poly_ntt: 8 at a time with        *)
(* 128-bit vectors unless the two halves of the block may overlap in 16      *)
(* bytes, computing with the addresses modulo 2^64, then any rest 4 at a     *)
(* time with 64-bit vectors and one by one, and one by one otherwise. So the *)
(* blocks of 8 + 8 coefficients or more take the loop over 128-bit vectors,  *)
(* those of 2 + 2 the scalar loop, and those of 4 + 4 the scalar loop unless *)
(* the 24 bytes from the start of the block wrap around the end of the       *)
(* address space, in which case they take the code for 64-bit vectors.       *)
(*                                                                           *)
(* Unlike the -O2 code, which saves X19 and X30, it saves X19, X20, X21 and  *)
(* X30 on the stack, so its specification has a stack frame of 32 bytes      *)
(* rather than 16. It loads its vectors of constants from three places in    *)
(* the block mlkem_poly_invntt_tomont_consts, so the safety theorem lists    *)
(* that block, of mlkem_poly_invntt_tomont_consts_size bytes, as read-only   *)
(* data, where the -O2 theorem lists 32 bytes.                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The coefficients are first scaled by a Montgomery             *)
(* multiplication by 1441 = 2^25 mod 3329, in a loop that the compiler has   *)
(* vectorized. Then the inverse NTT is done in 7 layers, for l = 7 down to   *)
(* 1, layer l consisting of 2^(l-1) blocks of 2^(9-l) consecutive            *)
(* coefficients. A block uses one zeta to do butterflies on pairs of         *)
(* coefficients 2^(8-l) apart, independently, with a Barrett reduction of    *)
(* the sums.                                                                 *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_neon(word_mul (word_sx(x i)) (word 1441))`;;

let invntt_fqmul_c = define
 `invntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let invntt_block_c = define
 `invntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then barred(word_add (m i) (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then invntt_fqmul_c z (word_sub (m i) (m(i - len)))
    else m i`;;

let invntt_blocks_c = define
 `invntt_blocks_c l 0 (r:num->int16) = r /\
  invntt_blocks_c l (SUC b) r =
    invntt_block_c (iword(EL (2 EXP l - 1 - b) mlk_zetas))
                   (2 * 2 EXP (8 - l) * b) (2 EXP (8 - l))
                   (invntt_blocks_c l b r)`;;

let invntt_layers_c = define
 `invntt_layers_c 0 (x:num->int16) = x /\
  invntt_layers_c (SUC n) x =
    invntt_blocks_c (7 - n) (2 EXP (6 - n)) (invntt_layers_c n x)`;;

(* ------------------------------------------------------------------------- *)
(* Some word lemmas for the butterflies.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The address of the lower coefficient, given relative to the upper one ***)

let WORD_2_VAL = prove
 (`!x:int64. word(2 * val x) = word_mul (word 2) x`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

(*** The sign-extension of the 16-bit sum or difference of coefficients ***)

let WORD_SXFROM_ADD_16 = prove
 (`!x y:int16.
      word_sxfrom 15 (word_subword (word_add (word_sx x) (word_zx y):int32)
                                   (0,16)):int32 =
      word_sx (word_add x y)`,
  BITBLAST_TAC);;

let WORD_SXFROM_SUB_16 = prove
 (`!x y:int16.
      word_sxfrom 15 (word_subword (word_sub (word_zx y) (word_sx x):int32)
                                   (0,16)):int32 =
      word_sx (word_sub y x)`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the code.                                                    *)
(* ------------------------------------------------------------------------- *)

let RANGE8_SPLIT = prove
 (`!P i n. 8 * (i + 1) <= n
           ==> ((!j. 8 * i <= j /\ j < n ==> P j) <=>
                (!j. 8 * (i + 1) <= j /\ j < n ==> P j) /\
                (!k. k < 8 ==> P(8 * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `8 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `8 * i <= j ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let NTT_VEC_ADDR = prove
 (`!a n i k. word_add a (word(2 * (n + (8 * i + k)))):int64 =
             word_add (word_add a (word(2 * n + 16 * i))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let NTT_VEC_ADDR2 = prove
 (`!a n l i k. word_add a (word(2 * (n + l + (8 * i + k)))):int64 =
               word_add (word_add a (word(2 * (n + l) + 16 * i)))
                        (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The butterflies of a block, for the lower and the upper half, with the
 *** sum of the coefficients in the order of the code
 ***)

let INVNTT_BLOCK_C_LO8 = prove
 (`!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> invntt_block_c z start len m (start + 8 * i + k) =
         barred(word_add (m(start + len + 8 * i + k)) (m(start + 8 * i + k)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let INVNTT_BLOCK_C_HI8 = prove
 (`!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> invntt_block_c z start len m (start + len + 8 * i + k) =
         invntt_fqmul_c z (word_sub (m(start + len + 8 * i + k))
                                    (m(start + 8 * i + k)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REPEAT AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;

let INVNTT_BLOCK_C_LO = prove
 (`!z start len m j.
     j < len
     ==> invntt_block_c z start len m (start + j) =
         barred(word_add (m(start + len + j)) (m(start + j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let INVNTT_BLOCK_C_HI = prove
 (`!z start len m j.
     j < len
     ==> invntt_block_c z start len m (start + len + j) =
         invntt_fqmul_c z (word_sub (m(start + len + j)) (m(start + j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REPEAT AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;

(*** The coefficients of a block, from its parts below, inside and above ***)

let INVNTT_BLOCK_JOIN = prove
 (`!(P:num->int16) z start len m.
     start + 2 * len <= 256 /\
     (!j. j < start ==> P j = m j) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> P j = m j) /\
     (!j. j < len
          ==> P(start + j) = invntt_block_c z start len m (start + j)) /\
     (!j. j < len
          ==> P(start + len + j) =
              invntt_block_c z start len m (start + len + j))
     ==> !i. i < 256 ==> P i = invntt_block_c z start len m i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let bd,h1,h2,h3,h4 =
      match CONJUNCTS th with
        [bd;h1;h2;h3;h4] -> bd,h1,h2,h3,h4
      | _ -> failwith "INVNTT_BLOCK_JOIN" in
    ASSUME_TAC bd THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < start` THENL
     [ASM_SIMP_TAC[h1; invntt_block_c; ARITH_RULE
       `i < start ==> ~(start <= i) /\ ~(start + len <= i)`];
      ALL_TAC] THEN
    ASM_CASES_TAC `i < start + len` THENL
     [MP_TAC(SPEC `i - start:num` h3) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i < start) ==> start + (i - start) = i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `i < start + 2 * len` THENL
     [MP_TAC(SPEC `i - (start + len):num` h4) THEN
      ASM_SIMP_TAC[ARITH_RULE
       `~(i < start + len) ==> start + len + (i - (start + len)) = i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[invntt_block_c] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC h2 THEN ASM_ARITH_TAC));;

(*** The Barrett reduction of a lane, as the vector code computes it ***)

let BARRED_VEC_LANE = prove
 (`!t:int16.
     word_add t
      (word_mul
        (word_subword
          (word_ishr (word_add (word_mul (word_sx t) (word 20159))
                               (word 33554432)) 26:int32) (0,16))
        (word 62207)) =
     barred t`,
  GEN_TAC THEN REWRITE_TAC[GSYM BARRED_SCALAR] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_mul (word_sx (t:int16)) (word 20159))
             (word 33554432):int32 =
    word_add (word 33554432) (word_mul (word_sx t) (word 20159))`] THEN
  SPEC_TAC(`word_ishr (word_add (word 33554432)
                        (word_mul (word_sx (t:int16)) (word 20159))) 26:int32`,
           `q:int32`) THEN
  GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o rand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o rand o rand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32):int16 = x`;
              WORD_BLAST
               `word_subword (q:int32) (0,16):int16 = word_zx q`] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(*** The zeta duplicated in the lanes of a vector, from W8 ***)

let WORD_ZX_ZX_SX_16 = prove
 (`!z:int16. word_zx(word_zx(word_sx z:int32):int64):int16 = z`,
  BITBLAST_TAC);;

(*** The test of the low 3 bits of the length after the vector loop ***)

let WORD_AND_8N_7 = prove
 (`!n. word_and (word(8 * n):int64) (word 7) = word 0`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_AND_WORD_LE] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  REWRITE_TAC[ARITH_RULE `7 = 2 EXP 3 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * n = n * 8`; MOD_MULT]);;

(*** The values of registers computed from small numbers. REG_SMALL_TAC r v
 *** replaces the value of register r in the assumptions by v, proving the
 *** equation as WORD_SMALL_TAC does, but also with shifts right
 ***)

let NTT_DIV8 = prove
 (`!n. (8 * n) DIV 8 = n`,
  GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN ARITH_TAC);;

let NTT_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(MOD_LT_ASM_TAC ORELSE CHANGED_TAC(REWRITE_TAC[NTT_DIV8]) ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

let REG_SMALL_TAC r v =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then SUBGOAL_THEN (mk_eq(t,v)) (fun eth -> ASSUME_TAC(TRANS th eth)) THENL
          [NTT_SMALL_TAC; ALL_TAC]
    else failwith "REG_SMALL_TAC");;

let REG_REWRITE_TAC r ths =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then ASSUME_TAC(REWRITE_RULE ths th)
    else failwith "REG_REWRITE_TAC");;

(*** The checks before the vector loop: cmp x1, x21 then ccmp x2, x0 set
 *** the carry flag, taking the vector code, unless the lower half of the
 *** block, from x2, and the upper half, from x1, may overlap in 16 bytes,
 *** computing with the addresses modulo 2^64. For a block of 8 * n + 8 * n
 *** coefficients the vector code is taken even if the addresses wrap
 *** around, and for one of 4 + 4 it is not taken unless they do.
 ***)

let MOD_2N_CASES = prove
 (`!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let VAL_WORD_ADD_SMALL_CASES = prove
 (`!a:int64 p. p < 2 EXP 64
     ==> val(word_add a (word p)) =
         if val a + p < 2 EXP 64 then val a + p else (val a + p) - 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_2N_CASES THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let WORD_SUB_FLAG_64 = prove
 (`!x y:int64.
     &(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let VAL_WORD_ADD_CASES_TAC =
  REPEAT(W(fun (asl,w) ->
    let t = find_term
      (can (term_match [] `val(word_add (a:int64) (word p))`)) w in
    MP_TAC(PART_MATCH (lhand o rand) VAL_WORD_ADD_SMALL_CASES t) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]));;

let NTT_ALIAS_VEC = prove
 (`!a:int64 p q.
     q + 16 <= p /\ p + 16 < 2 EXP 64
     ==> (if val(word_add a (word p)) < val(word_add a (word(q + 16)))
          then &(val(word_add a (word q))) -
               &(val(word_add a (word(p + 16)))):int =
               &(val(word_sub (word_add a (word q))
                              (word_add a (word(p + 16)))))
          else T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUB_FLAG_64] THEN
  VAL_WORD_ADD_CASES_TAC THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(a:int64) + p < 2 EXP 64`; `val(a:int64) + p + 16 < 2 EXP 64`;
    `val(a:int64) + q < 2 EXP 64`; `val(a:int64) + q + 16 < 2 EXP 64`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NTT_ALIAS_SCALAR = prove
 (`!a:int64 q.
     val(word_add a (word q)) + 24 < 2 EXP 64 /\ q + 24 < 2 EXP 64
     ==> ((if val(word_add a (word(q + 8))) < val(word_add a (word(q + 16)))
           then &(val(word_add a (word q))) -
                &(val(word_add a (word(q + 24)))):int =
                &(val(word_sub (word_add a (word q))
                               (word_add a (word(q + 24)))))
           else T) <=> F)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[WORD_SUB_FLAG_64] THEN VAL_WORD_ADD_CASES_TAC THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN
  ASM_CASES_TAC `val(a:int64) + q < 2 EXP 64` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `val(a:int64) + q + 8 < 2 EXP 64 /\ val(a:int64) + q + 16 < 2 EXP 64 /\
      val(a:int64) + q + 24 < 2 EXP 64`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN
     `~(val(a:int64) + q + 8 < 2 EXP 64) /\
      ~(val(a:int64) + q + 16 < 2 EXP 64) /\
      ~(val(a:int64) + q + 24 < 2 EXP 64)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One block of the last five layers, with n vectors of 8 coefficients in    *)
(* each half, from the head of the block loop through the vector loop.       *)
(* ------------------------------------------------------------------------- *)

let invntt_vblock_inv =
 `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X0 s = word(16 * i) /\
        read X2 s = word_add a (word(2 * start)) /\
        read X1 s = word_add a (word(2 * (start + 8 * n))) /\
        read X20 s = word(16 * n) /\ read X30 s = word(8 * n) /\
        read Q20 s = word_duplicate z /\
        read X5 s = word start /\ read X7 s = word(start + 8 * n) /\
        read X9 s = word(k - 1) /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X13 s = word(2 * 8 * n) /\ read X14 s = word(8 * n) /\
        read X16 s = word(8 * n) /\
        read X8 s = word_zx(word_sx z:int32) /\
        read X10 s = word 20159 /\ read X12 s = word 33554432 /\
        read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X17 s = w17 /\
        read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q5 s = word 0x02000000020000000200000002000000 /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read Q17 s = word 0xf301f301f301f301 /\
        read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
        read Q19 s = word 0xf2fff2fff2fff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!j. j < start
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. start + 2 * 8 * n <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a (word(2 * (start + j)))))
                   s =
                 invntt_block_c z start (8 * n) m (start + j)) /\
        (!j. 8 * i <= j /\ j < 8 * n
             ==> read(memory :> bytes16(word_add a (word(2 * (start + j)))))
                   s =
                 m (start + j)) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (start + 8 * n + j))))) s =
                 invntt_block_c z start (8 * n) m (start + 8 * n + j)) /\
        (!j. 8 * i <= j /\ j < 8 * n
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (start + 8 * n + j))))) s =
                 m (start + 8 * n + j))`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_VBLOCK = prove
 (`!a zetas pc (z:int16) start n k (m:num->int16) w17.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     1 <= n /\
     start + 2 * 8 * n <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X5 s = word start /\ read X7 s = word(start + 8 * n) /\
               read X9 s = word k /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * 8 * n) /\ read X14 s = word(8 * n) /\
               read X16 s = word(8 * n) /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test1) /\
               read X5 s = word(start + 2 * 8 * n) /\
               read X7 s = word(start + 3 * 8 * n) /\
               read X9 s = word(k - 1) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * 8 * n) /\ read X14 s = word(8 * n) /\
               read X16 s = word(8 * n) /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c z start (8 * n) m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X9; X19; X20; X21; X30] ,,
           MAYCHANGE [Q0; Q1; Q2; Q4; Q20] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc + mlkem_poly_invntt_tomont_loop5`
   `pc + mlkem_poly_invntt_tomont_loop5_test` invntt_vblock_inv THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** From the head of the block to the vector loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
    REG_SMALL_TAC `X30` `word(8 * n):int64` THEN
    REG_SMALL_TAC `X20` `word(8 * n - 1):int64` THEN
    REG_SMALL_TAC `X3` `word start:int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--18) THEN
    REG_SMALL_TAC `X0`
     `word_add a (word(2 * (start + 8 * n) + 16)):int64` THEN
    REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
    REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
    REG_SMALL_TAC `X1` `word_add a (word(2 * (start + 8 * n))):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
    MP_TAC(SPECL [`a:int64`; `2 * (start + 8 * n)`; `2 * start`]
                 NTT_ALIAS_VEC) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--22) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (23--28) THEN
    REG_SMALL_TAC `X20` `word(16 * n):int64` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_SX_16] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;

    (*** The loop body, 8 butterflies at once ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `8 * (i + 1) <= 8 * n` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th ->
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
        [MATCH_MP RANGE8_SPLIT th]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (STRIP_ASSUME_TAC o REWRITE_RULE[WORD_ADD_0] o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        REWRITE_RULE[ADD_CLAUSES] o REWRITE_RULE[NTT_VEC_ADDR] o
        REWRITE_RULE[NTT_VEC_ADDR2] o CONV_RULE EXPAND_CASES_CONV)))
     [ASSUME `8 * (i + 1) <= 8 * n`; ASSUME `8 * (i + 1) <= 8 * n`] THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a
               (word(2 * start + 16 * i)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a
               (word(2 * (start + 8 * n) + 16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--23) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes128 a) s23 = x`)
            (concl th)))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[INVNTT_BLOCK_C_LO8; INVNTT_BLOCK_C_HI8;
             ASSUME `8 * (i + 1) <= 8 * n`] THEN
    CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[NTT_VEC_ADDR2] THEN REWRITE_TAC[NTT_VEC_ADDR] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MONTRED_NEON_SCALAR; BARRED_VEC_LANE]) THEN
    ASM_REWRITE_TAC[invntt_fqmul_c];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_8N_7; VAL_WORD_0]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (6--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [NTT_SMALL_TAC; NTT_SMALL_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INVNTT_BLOCK_JOIN THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One block of the first two layers, with 2 or 4 coefficients in each half, *)
(* from the head of the block loop through the scalar loop. For 4 + 4        *)
(* coefficients, this is the path of the code when the 24 bytes from the     *)
(* start of the block do not wrap around the end of the address space.       *)
(* ------------------------------------------------------------------------- *)

let invntt_sblock_inv =
 `\jj s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
         read X2 s = word_add a (word(2 * (start + len + jj))) /\
         read X3 s = word_neg(word len) /\
         read X30 s = word_add a (word(2 * (start + 2 * len))) /\
         read X5 s = word start /\ read X7 s = word(start + len) /\
         read X9 s = word(k - 1) /\
         read X4 s = a /\ read X18 s = word_add a (word 2) /\
         read X15 s = word zetas /\
         read X13 s = word(2 * len) /\ read X14 s = word len /\
         read X16 s = word len /\
         read X8 s = word_zx(word_sx z:int32) /\
         read X10 s = word 20159 /\ read X12 s = word 33554432 /\
         read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
         read X17 s = w17 /\
         read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
         read Q5 s = word 0x02000000020000000200000002000000 /\
         read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
         read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
         read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
         read Q17 s = word 0xf301f301f301f301 /\
         read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
         read Q19 s = word 0xf2fff2fff2fff2ff /\
         (!k. k < 128
              ==> read(memory :> bytes16(word_add (word zetas)
                                                  (word(2 * k)))) s =
                  iword(EL k mlk_zetas)) /\
         (!i. i < 256
              ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                  if start <= i /\ i < start + jj \/
                     start + len <= i /\ i < start + len + jj
                  then invntt_block_c z start len m i else m i)`;;

(*** The setup of the scalar loop at join1 ***)

let INVNTT_SBLOCK_JOIN1_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
  REPEAT CONJ_TAC THEN NTT_SMALL_TAC;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK = prove
 (`!a zetas pc (z:int16) start len k (m:num->int16) w17.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     (len = 2 \/
      len = 4 /\ val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64) /\
     start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X5 s = word start /\ read X7 s = word(start + len) /\
               read X9 s = word k /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word(len) /\
               read X16 s = word(len) /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test1) /\
               read X5 s = word(start + 2 * len) /\
               read X7 s = word(start + 3 * len) /\
               read X9 s = word(k - 1) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word(len) /\
               read X16 s = word(len) /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c z start (len) m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X9; X19; X20; X21; X30] ,,
           MAYCHANGE [Q0; Q1; Q2; Q4; Q20] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + mlkem_poly_invntt_tomont_loop4`
   `pc + mlkem_poly_invntt_tomont_loop4_test` invntt_sblock_inv THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** From the head of the block to the scalar loop, directly for 2 + 2
     *** coefficients and after the check for 4 + 4 ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                  check (is_disj o concl)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
    REG_SMALL_TAC `X30` `word len:int64` THEN
    REG_SMALL_TAC `X20` `word(len - 1):int64` THEN
    REG_SMALL_TAC `X3` `word start:int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--8) THENL
     [INVNTT_SBLOCK_JOIN1_TAC;
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (9--18) THEN
      REG_SMALL_TAC `X0` `word_add a (word(2 * start + 24)):int64` THEN
      REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
      REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
      REG_SMALL_TAC `X1` `word_add a (word(2 * start + 8)):int64` THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
      MP_TAC(SPECL [`a:int64`; `2 * start`] NTT_ALIAS_SCALAR) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--21) THEN
      INVNTT_SBLOCK_JOIN1_TAC];

    (*** The scalar loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int16` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `word_add (word_add a (word(2 * (start + len + jj))))
               (word(2 * val(word_neg(word len):int64))):int64 =
      word_add a (word(2 * (start + jj)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_2_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[WORD_SXFROM_ADD_16; BARRED_SCALAR] THEN
      REWRITE_TAC[invntt_block_c; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[WORD_SXFROM_SUB_16; GSYM montred_scalar] THEN
      REWRITE_TAC[invntt_block_c; invntt_fqmul_c] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `jj < len ==> ~(start <= start + len + jj /\
                       start + len + jj < start + len) /\
                     start + len <= start + len + jj /\
                     start + len + jj < start + 2 * len`] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [NTT_SMALL_TAC; NTT_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One block of 4 + 4 coefficients when the 24 bytes from its start wrap    *)
(* around the end of the address space. The check before the vector loop   *)
(* then takes the vector code, which goes on to the code for 4 coefficients *)
(* in each half with 64-bit vectors, from join4.                            *)
(* ------------------------------------------------------------------------- *)

let NTT_ALIAS_SCALAR_WRAP = prove
 (`!a:int64 q.
     ~(val(word_add a (word q)) + 24 < 2 EXP 64) /\ q + 24 < 2 EXP 64
     ==> (if val(word_add a (word(q + 8))) < val(word_add a (word(q + 16)))
          then &(val(word_add a (word q))) -
               &(val(word_add a (word(q + 24)))):int =
               &(val(word_sub (word_add a (word q))
                              (word_add a (word(q + 24)))))
          else T)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[WORD_SUB_FLAG_64] THEN VAL_WORD_ADD_CASES_TAC THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(a:int64) + q < 2 EXP 64`; `val(a:int64) + q + 8 < 2 EXP 64`;
    `val(a:int64) + q + 16 < 2 EXP 64`;
    `val(a:int64) + q + 24 < 2 EXP 64`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(*** The lanes of the code for 64-bit vectors, a Montgomery multiplication
 *** with the 32-bit products and quotients sign-extended
 ***)

let WORD_ZX_ZX_SX_32 = prove
 (`!z:int16. word_zx(word_zx(word_sx z:int32):int64):int32 = word_sx z`,
  BITBLAST_TAC);;

let WORD_USHR16_SUBWORD = prove
 (`!x t:int32. word_subword (word_ushr (word_add x t) 16) (0,16):int16 =
               word_subword (word_add t x) (16,16)`,
  BITBLAST_TAC);;

let WORD_SUBWORD_ZX_64 = prove
 (`(!x:int64. word_subword (word_subword x (0,128):int128) (0,16):int16 =
              word_subword x (0,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (16,16):int16 =
              word_subword x (16,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (32,16):int16 =
              word_subword x (32,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (48,16):int16 =
              word_subword x (48,16)) /\
   (!x:int64. word_zx (word_zx x:int128):int64 = x)`,
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let NTT_D_ADDR = prove
 (`!a n k. word_add a (word(2 * (n + k))):int64 =
           word_add (word_add a (word(2 * n))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let NTT_D_ADDR2 = prove
 (`!a n k. word_add a (word(2 * (n + 4 + k))):int64 =
           word_add (word_add a (word(2 * (n + 4)))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** Split the coefficients of the block into those below, inside and above,
 *** with those inside as bytes16 at addresses from the two 64-bit loads
 ***)

let NTT_DBLOCK_SPLIT_TAC =
  SUBGOAL_THEN
   `(!j. j < start
         ==> read(memory :> bytes16(word_add a (word(2 * j)))) s0 = m j) /\
    (!j. start + 8 <= j /\ j < 256
         ==> read(memory :> bytes16(word_add a (word(2 * j)))) s0 = m j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `m:num->int16` (concl th) &&
       can (term_match [] `!i. i < 256 ==> P i`) (concl th) then
      let rule ath =
        REWRITE_RULE[WORD_ADD_0] o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o REWRITE_RULE[ath] in
      let ths = map (fun k -> SPEC (subst [mk_small_numeral k,`K:num`]
                                          `start + K`) th,
                              rule NTT_D_ADDR) (0--3) @
                map (fun k -> SPEC (subst [mk_small_numeral k,`K:num`]
                                          `start + 4 + K`) th,
                              rule NTT_D_ADDR2) (0--3) in
      MAP_EVERY (fun (t,r) -> MP_TAC t THEN ANTS_TAC THENL
                  [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o r)]) ths
    else failwith "NTT_DBLOCK_SPLIT_TAC");;

(*** The statement of the block lemmas for blocks of len + len coefficients
 *** that may not take the 128-bit vector loop, with hypothesis HYP on len
 *** and the addresses
 ***)

let invntt_block_goal hyp =
  let tm =
  `!a zetas pc (z:int16) start len k (m:num->int16) w17.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     HYP /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X5 s = word start /\ read X7 s = word(start + len) /\
               read X9 s = word k /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word len /\
               read X16 s = word len /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test1) /\
               read X5 s = word(start + 2 * len) /\
               read X7 s = word(start + 3 * len) /\
               read X9 s = word(k - 1) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word len /\
               read X16 s = word len /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X17 s = w17 /\
               read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X9; X19; X20; X21; X30] ,,
           MAYCHANGE [Q0; Q1; Q2; Q4; Q20] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])` in
  let vs,body = strip_forall tm in
  list_mk_forall(vs,subst [hyp,`HYP:bool`] body);;

(*** The Barrett reduction of a lane in the code for 64-bit vectors, which
 *** adds the products to the vector of 2^25 rather than the other way
 ***)

let BARRED_VEC_LANE_ALT = prove
 (`!t:int16.
     word_add t
      (word_mul
        (word_subword
          (word_ishr (word_add (word 33554432)
                               (word_mul (word_sx t) (word 20159))) 26:int32)
          (0,16))
        (word 62207)) =
     barred t`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE
   `word_add (word 33554432) (x:int32) = word_add x (word 33554432)`] THEN
  REWRITE_TAC[BARRED_VEC_LANE]);;

let INVNTT_DBLOCK_HALF_TAC ath =
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ath] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MONTRED_NEON_SCALAR; BARRED_VEC_LANE_ALT]) THEN
  ASM_REWRITE_TAC[invntt_fqmul_c];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_DBLOCK = prove
 (invntt_block_goal
   `len = 4 /\ ~(val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `len:num`)) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The coefficients of the block as two 64-bit words ***)

  NTT_DBLOCK_SPLIT_TAC THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read(memory :> bytes64(word_add a (word(2 * start)))) s0`) THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read(memory :> bytes64(word_add a (word(2 * (start + 4))))) s0`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN

  (*** The checks, taking the vector code and then the code at join4 ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
  REG_SMALL_TAC `X30` `word 4:int64` THEN
  REG_SMALL_TAC `X20` `word 3:int64` THEN
  REG_SMALL_TAC `X3` `word start:int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--18) THEN
  REG_SMALL_TAC `X0` `word_add a (word(2 * start + 24)):int64` THEN
  REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
  REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
  REG_SMALL_TAC `X1` `word_add a (word(2 * start + 8)):int64` THEN
  REG_SMALL_TAC `X19` `word(start + 4):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
  MP_TAC(SPECL [`a:int64`; `2 * start`] NTT_ALIAS_SCALAR_WRAP) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--22) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (23--33) THEN
  REG_SMALL_TAC `X0` `word(2 * (start + 4)):int64` THEN
  REG_SMALL_TAC `X3` `word(2 * start):int64` THEN

  (*** The 4 + 4 butterflies with 64-bit vectors ***)

  MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (34--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SHL_ZERO; WORD_ZX_ZX_SX_32;
                               WORD_USHR16_SUBWORD; GSYM montred_neon]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_ZX_64]) THEN
  RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV [])) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes64 a) s53 = x`)
            (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_ZX_64]) THEN
  RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV [])) THEN

  (*** The end of the block ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (54--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC INVNTT_BLOCK_JOIN THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INVNTT_BLOCK_C_LO; INVNTT_BLOCK_C_HI] THEN
  CONJ_TAC THENL
   [INVNTT_DBLOCK_HALF_TAC NTT_D_ADDR; INVNTT_DBLOCK_HALF_TAC NTT_D_ADDR2]);;

(*** A block of 4 + 4 coefficients, wherever it is ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_BLOCK4 = prove
 (invntt_block_goal `len = 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64` THENL
   [MATCH_MP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK;
    MATCH_MP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_DBLOCK] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the last layer).         *)
(* ------------------------------------------------------------------------- *)

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** Assertions at the block head and block end for layer l, block b ***)

let invntt_blockhead_tm,invntt_blockend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X5 s = word(2 * LEN * B) /\
        read X7 s = word(2 * LEN * B + LEN) /\
        read X9 s = word(2 EXP L - 1 - B) /\
        read X8 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1 - B) mlk_zetas):int16):int32) /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X13 s = word(2 * LEN) /\ read X14 s = word LEN /\
        read X16 s = word LEN /\
        read X10 s = word 20159 /\ read X12 s = word 33554432 /\
        read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X17 s = word L /\
        read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q5 s = word 0x02000000020000000200000002000000 /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read Q17 s = word 0xf301f301f301f301 /\
        read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
        read Q19 s = word 0xf2fff2fff2fff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X5 s = word(2 * LEN * B) /\
        read X7 s = word(2 * LEN * B + LEN) /\
        read X9 s = word(2 EXP L - 1 - B) /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X13 s = word(2 * LEN) /\ read X14 s = word LEN /\
        read X16 s = word LEN /\
        read X10 s = word 20159 /\ read X12 s = word 33554432 /\
        read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X17 s = word L /\
        read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q5 s = word 0x02000000020000000200000002000000 /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read Q17 s = word 0xf301f301f301f301 /\
        read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
        read Q19 s = word 0xf2fff2fff2fff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (8 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply a block lemma at the head of block b of layer l: the vector
 *** block for layers 5 down to 1, with 8 * n coefficients in each half for
 *** n = 2^(5 - l), then the block of 4 + 4 and the scalar block of 2 + 2
 *** coefficients
 ***)

let INVNTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th =
    if l <= 5 then
      SPECL [`a:int64`; `zetas:num`; `pc:num`;
             red `iword(EL (2 EXP L - 1 - B) mlk_zetas):int16`;
             red `2 * LEN * B`; mk_small_numeral(1 lsl (5 - l));
             red `2 EXP L - 1 - B`; red `invntt_blocks_c L B r`;
             red `word L:int64`]
            MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_VBLOCK
    else
      SPECL [`a:int64`; `zetas:num`; `pc:num`;
             red `iword(EL (2 EXP L - 1 - B) mlk_zetas):int16`;
             red `2 * LEN * B`; red `LEN:num`;
             red `2 EXP L - 1 - B`; red `invntt_blocks_c L B r`;
             red `word L:int64`]
            (if l = 6 then MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_BLOCK4
             else MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 invntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The layer head, setting up the registers for the first block ***)

let INVNTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3`
   (invntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[invntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let INVNTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (counting down from 7) ***)

let INVNTT_LAYER_TAC l =
  INVNTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_test1`
   (invntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [INVNTT_BLOCK_TAC l `0`;
    if l = 1 then INVNTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl (l - 1) - 1))
      `pc + mlkem_poly_invntt_tomont_loop3_test1`
      `pc + mlkem_poly_invntt_tomont_loop3_test1`
      (mk_abs(`i:num`,invntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3`
       (invntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L - 1 - (i + 1)`)))) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        INVNTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      INVNTT_LAYEREXIT_TAC]];;

let invntt_layer_goal l =
  let tm =
  `!a zetas pc r.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X17 s = word L /\
               read X8 s =
               word_zx(word_sx(iword(EL (2 EXP L - 1) mlk_zetas):int16)
                       :int32) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_exit) /\
               read X17 s = word L /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X10 s = word 20159 /\ read X12 s = word 33554432 /\
               read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read Q5 s = word 0x02000000020000000200000002000000 /\
               read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q17 s = word 0xf301f301f301f301 /\
               read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
               read Q19 s = word 0xf2fff2fff2fff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_blocks_c L (2 EXP (L - 1)) r i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X8; X9; X13; X14; X16;
                      X19; X20; X21; X30] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q16; Q20] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

let INVNTT_LAYER_PROOF_TAC l =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  INVNTT_LAYER_TAC l;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_LAYERS =
  map (fun l -> prove(invntt_layer_goal l,INVNTT_LAYER_PROOF_TAC l)) (1--7);;


(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the inverse NTT, within the same      *)
(* bounds as the hand-written kernel. In fact all the coefficients stay      *)
(* below 3329 in absolute value, because of the reductions in every layer.   *)
(* ------------------------------------------------------------------------- *)

let INVNTT_BLOCKS_C_CLOSED = prove
 (`!l b r i.
     invntt_blocks_c l b r i =
     if i < 2 * 2 EXP (8 - l) * b
     then let z = iword(EL (2 EXP l - 1 - i DIV (2 * 2 EXP (8 - l)))
                           mlk_zetas) in
          if i MOD (2 * 2 EXP (8 - l)) < 2 EXP (8 - l)
          then barred(word_add (r i) (r(i + 2 EXP (8 - l))))
          else invntt_fqmul_c z (word_sub (r i) (r(i - 2 EXP (8 - l))))
     else r i`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[invntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[invntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (8 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (8 - l)` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
  ASM_CASES_TAC `2 * n * b <= i /\ i < 2 * n * b + 2 * n` THENL
   [SUBGOAL_THEN `i DIV (2 * n) = b /\ i MOD (2 * n) = i - 2 * n * b`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + 2 * n
      ==> ~(i < 2 * n * b) /\ ~(i + n < 2 * n * b) /\
          i < 2 * n * b + 2 * n`] THEN
    ASM_CASES_TAC `i < 2 * n * b + n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + n ==> i - 2 * n * b < n`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - 2 * n * b < n)`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - n < 2 * n * b)`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE
     `~(p <= i /\ i < p + 2 * n)
      ==> ~(p <= i /\ i < p + n) /\ ~(p + n <= i /\ i < p + 2 * n)`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let INVNTT_LAYERS_C_STEP = prove
 (`!n x i.
     n < 7 /\ i < 256
     ==> invntt_layers_c (SUC n) x i =
         let z = iword(EL (2 EXP (7 - n) - 1 -
                           i DIV (2 * 2 EXP (8 - (7 - n)))) mlk_zetas) in
         if i MOD (2 * 2 EXP (8 - (7 - n))) < 2 EXP (8 - (7 - n))
         then barred(word_add (invntt_layers_c n x i)
                        (invntt_layers_c n x (i + 2 EXP (8 - (7 - n)))))
         else invntt_fqmul_c z
                (word_sub (invntt_layers_c n x i)
                          (invntt_layers_c n x (i - 2 EXP (8 - (7 - n)))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[invntt_layers_c; INVNTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `2 * 2 EXP (8 - (7 - n)) * 2 EXP (6 - n) = 256`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 7 ==> 8 - (7 - n) + 6 - n = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

(*** The equation for coefficient i after layer n + 1, starting from the ***)
(*** scaled coefficients.                                                ***)

let INVNTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 invntt_layers_c :: invntt_scale_c ::
                 MONTRED_NEON_SCALAR :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[invntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun n i ->
    let th = SPECL [mk_small_numeral n; `invntt_scale_c x`;
                    mk_small_numeral i] INVNTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** The congruences and bounds for all the layers, in order ***)

let INVNTT_LAYERS_CONGBOUND =
  MLKEM_NATIVE_LOCAL_CONGBOUND_RULE undefined
   (map (fun (n,i) -> SYM(INVNTT_LAYER_EQUATION n i))
        (List.concat (map (fun n -> map (fun i -> (n,i)) (0--255)) (0--6))));;

let INVNTT_FINAL_TAC =
  W(fun (asl,w) ->
    let tm = find_term
      (can (term_match [] `invntt_layers_c 7 (invntt_scale_c x) i`)) w in
    let th = apply INVNTT_LAYERS_CONGBOUND tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let INVNTT_LAYERS_C_CORRECT = prove
 (`!x i. i < 256
         ==> (ival(invntt_layers_c 7 (invntt_scale_c x) i) ==
              inverse_ntt (ival o x) i) (mod &3329) /\
             abs(ival(invntt_layers_c 7 (invntt_scale_c x) i)) <= &26624`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN INVNTT_FINAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The scaling loop at the start.                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SCALE = prove
 (`!a (x:num->int16) pc.
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word(pc + mlkem_poly_invntt_tomont_loop1) /\
           read X0 s = a /\ read X1 s = word_add a (word 512) /\
           read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
           read Q4 s = word 0x05a105a105a105a105a105a105a105a1 /\
           read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlkem_poly_invntt_tomont_loop1_exit) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_scale_c x i))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [Q0; Q1; Q2] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_TAC THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_invntt_tomont_loop1`
   `pc + mlkem_poly_invntt_tomont_loop1_test`
   `\i s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_O3_mc /\
          read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          read Q4 s = word 0x05a105a105a105a105a105a105a105a1 /\
          read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   invntt_scale_c x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The loop is entered with i = 0 ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--9) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[invntt_scale_c];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `invntt_scale_c` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* All the layers compute the C version of the inverse NTT.                  *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let invntt_layerhead_tm,invntt_layerend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X17 s = word L /\
        read X8 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1) mlk_zetas):int16):int32) /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X10 s = word 20159 /\ read X12 s = word 33554432 /\
        read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read Q5 s = word 0x02000000020000000200000002000000 /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q17 s = word 0xf301f301f301f301 /\
        read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
        read Q19 s = word 0xf2fff2fff2fff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (7 - L) x i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X17 s = word L /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X10 s = word 20159 /\ read X12 s = word 33554432 /\
        read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read Q5 s = word 0x02000000020000000200000002000000 /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q17 s = word 0xf301f301f301f301 /\
        read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
        read Q19 s = word 0xf2fff2fff2fff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (8 - L) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let INVNTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `zetas:num`; `pc:num`;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `invntt_layers_c (7 - L) x`)))]
                 (el (l - 1)
                     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_LAYERS) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral(7 - l),`n:num`]
          (SPEC_ALL(CONJUNCT2 invntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let INVNTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--5) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l - 1) - 1)) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (6--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_ALL_LAYERS = prove
 (`!a zetas (x:num->int16) pc.
    ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
           read X17 s = word 7 /\
           read X8 s =
           word_zx(word_sx(iword(EL 127 mlk_zetas):int16):int32) /\
           read X4 s = a /\ read X18 s = word_add a (word 2) /\
           read X15 s = word zetas /\
           read X10 s = word 20159 /\ read X12 s = word 33554432 /\
           read X6 s = word 4294963967 /\ read X11 s = word 4294963969 /\
           read Q5 s = word 0x02000000020000000200000002000000 /\
           read Q6 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
           read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
           read Q17 s = word 0xf301f301f301f301 /\
           read Q18 s = word 0x00004ebf00004ebf00004ebf00004ebf /\
           read Q19 s = word 0xf2fff2fff2fff2ff /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlkem_poly_invntt_tomont_loop2_exit) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_layers_c 7 x i))
      (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X8; X9; X13; X14; X16; X17;
                  X19; X20; X21; X30] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q16; Q20] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop2`
   (invntt_layerhead_tm 7) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 invntt_layers_c] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_exit`
     (invntt_layerend_tm l) THEN
    CONJ_TAC THENL [INVNTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 1 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop2`
     (invntt_layerhead_tm (l - 1)) THEN
    CONJ_TAC THENL [INVNTT_LAYERBACK_TAC l; ALL_TAC]) (rev(1--7)) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The vectors of constants, one also as a D register, and the table of
 *** zetas in the image
 ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_CONSTANTS =
  map (fun (c,k) -> MLKEM_NATIVE_IMAGE_CONST_RULE (layout c) k)
   ["mlkem_poly_invntt_tomont_const1",128;
    "mlkem_poly_invntt_tomont_const1",64;
    "mlkem_poly_invntt_tomont_const2",128;
    "mlkem_poly_invntt_tomont_const3",128];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word_sub stackpointer (word 32),32)] /\
    nonoverlapping (word_sub stackpointer (word 32),32) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_CONSTANTS THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
    MATCH_MP MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_ZETAS_IN_IMAGE) THEN

  (*** The setup of the scaling, which also saves X19 to X21 and X30 ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--10) THEN

  (*** The scaling ***)

  MP_TAC(SPECL [`a:int64`; `x:num->int16`; `pc:num`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SCALE) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC "s11" THEN

  (*** The setup of the constants of the layers ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (12--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (13--15) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (16--17) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (18--21) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (22--30) THEN
  REG_REWRITE_TAC `X15` [GSYM WORD_ADD] THEN

  (*** The layers ***)

  SUBGOAL_THEN
   `word_zx(word_sx(iword(EL 127 mlk_zetas):int16):int32):int64 =
    word 1628`
  ASSUME_TAC THENL
   [REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `pc + rodata_mlk_zetas`; `invntt_scale_c x`;
                `pc:num`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_ALL_LAYERS) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC "s31" THEN

  (*** Restoring X19 to X21 and X30 and returning ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (32--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INVNTT_LAYERS_C_CORRECT]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The frame of the lemmas for the blocks and layers, which also use X19,
 *** X20, X21 and X30, saved on the stack by the whole function
 ***)

let INVNTT_SAFE_FRAME_TAC =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC;;

(*** Simulation of a short piece of straight-line code with flags ***)

let INVNTT_SAFE_SIM_TAC pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(CONJ_TAC THENL
   [W(fun (_,w) -> if is_exists w then NO_TAC else ALL_TAC) THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (NTT_SMALL_TAC ORELSE ASM_ARITH_TAC ORELSE
     (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** One block of layers 5 down to 1 ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_VBLOCK_SAFE = prove
 (`exists f_ev_blk.
   forall e a zetas pc start n k w17 sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)] /\
     1 <= n /\ start + 16 * n <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X5 s = word start /\ read X7 s = word(start + 8 * n) /\
               read X9 s = word k /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(16 * n) /\ read X14 s = word(8 * n) /\
               read X16 s = word(8 * n) /\ read X17 s = w17 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test1) /\
               read X5 s = word(start + 16 * n) /\
               read X7 s = word(start + 24 * n) /\
               read X9 s = word(k - 1) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(16 * n) /\ read X14 s = word(8 * n) /\
               read X16 s = word(8 * n) /\ read X17 s = w17 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start n /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21; X30] ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (start:num) (n:num).
      APPEND (f_ev_blkend a zetas pc start n)
        (APPEND (ENUMERATEL n
                   (\i. f_ev_vloop a zetas pc start n i))
                (f_ev_blkhead a zetas pc start n))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  INVNTT_SAFE_FRAME_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + mlkem_poly_invntt_tomont_loop5`
   `pc + mlkem_poly_invntt_tomont_loop5_exit`
   `\i s. read X0 s = word(16 * i) /\
          read X2 s = word_add a (word(2 * start)) /\
          read X1 s = word_add a (word(2 * (start + 8 * n))) /\
          read X20 s = word(16 * n) /\ read X30 s = word(8 * n) /\
          read X5 s = word start /\ read X7 s = word(start + 8 * n) /\
          read X9 s = word(k - 1) /\
          read X4 s = a /\ read X18 s = word_add a (word 2) /\
          read X15 s = word zetas /\
          read X13 s = word(16 * n) /\ read X14 s = word(8 * n) /\
          read X16 s = word(8 * n) /\ read X17 s = w17 /\
          read SP s = sp /\
          read(memory :> bytes64 sp) s = x19v /\
          read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
          read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
          read(memory :> bytes64(word_add sp (word 24))) s = ra` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** From the head of the block to the vector loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
    REG_SMALL_TAC `X30` `word(8 * n):int64` THEN
    REG_SMALL_TAC `X20` `word(8 * n - 1):int64` THEN
    REG_SMALL_TAC `X3` `word start:int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--18) THEN
    REG_SMALL_TAC `X0`
     `word_add a (word(2 * (start + 8 * n) + 16)):int64` THEN
    REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
    REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
    REG_SMALL_TAC `X1` `word_add a (word(2 * (start + 8 * n))):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
    MP_TAC(SPECL [`a:int64`; `2 * (start + 8 * n)`; `2 * start`]
                 NTT_ALIAS_VEC) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--22) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (23--28) THEN
    REG_SMALL_TAC `X20` `word(16 * n):int64` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, 8 butterflies at once, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--23) THEN
    REG_SMALL_TAC `X0` `word(16 * i + 16):int64` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (24--24) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (25--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(16 * n = 16 * i + 16) <=> i + 1 < n`
     SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_8N_7; VAL_WORD_0]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(*** The blocks of layers 7 and 6 ***)

let invntt_sblock_safe_goal hyp =
  let tm =
  `exists f_ev_blk.
   forall e a zetas pc start len k w17 sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)] /\
     HYP /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X5 s = word start /\ read X7 s = word(start + len) /\
               read X9 s = word k /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word len /\
               read X16 s = word len /\ read X17 s = w17 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test1) /\
               read X5 s = word(start + 2 * len) /\
               read X7 s = word(start + 3 * len) /\
               read X9 s = word(k - 1) /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read X13 s = word(2 * len) /\ read X14 s = word len /\
               read X16 s = word len /\ read X17 s = w17 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start len /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21; X30] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  let f,b = dest_exists tm in
  let vs,body = strip_forall b in
  mk_exists(f,list_mk_forall(vs,subst [hyp,`HYP:bool`] body));;

(*** The steps from the head of the block to the scalar loop, directly for
 *** 2 + 2 coefficients, and after the check for 4 + 4
 ***)

let INVNTT_SBLOCK_HEAD_SAFE_TAC long =
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
  REG_SMALL_TAC `X30` `word len:int64` THEN
  REG_SMALL_TAC `X20` `word(len - 1):int64` THEN
  REG_SMALL_TAC `X3` `word start:int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--8) THEN
  (if not long then ALL_TAC else
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (9--18) THEN
   REG_SMALL_TAC `X0` `word_add a (word(2 * start + 24)):int64` THEN
   REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
   REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
   REG_SMALL_TAC `X1` `word_add a (word(2 * start + 8)):int64` THEN
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
   MP_TAC(SPECL [`a:int64`; `2 * start`] NTT_ALIAS_SCALAR) THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--21)) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC
   (if long then 22--26 else 9--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
  REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INVNTT_SBLOCK_SAFE_TAC long =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (start:num) (len:num).
      APPEND (f_ev_blkend a zetas pc start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a zetas pc start len j))
                (f_ev_blkhead a zetas pc start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  INVNTT_SAFE_FRAME_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mlkem_poly_invntt_tomont_loop4`
   `pc + mlkem_poly_invntt_tomont_loop4_exit`
   `\j s. read X2 s = word_add a (word(2 * (start + len + j))) /\
          read X3 s = word_neg(word len) /\
          read X30 s = word_add a (word(2 * (start + 2 * len))) /\
          read X5 s = word start /\ read X7 s = word(start + len) /\
          read X9 s = word(k - 1) /\
          read X4 s = a /\ read X18 s = word_add a (word 2) /\
          read X15 s = word zetas /\
          read X13 s = word(2 * len) /\ read X14 s = word len /\
          read X16 s = word len /\ read X17 s = w17 /\
          read SP s = sp /\
          read(memory :> bytes64 sp) s = x19v /\
          read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
          read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
          read(memory :> bytes64(word_add sp (word 24))) s = ra` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    INVNTT_SBLOCK_HEAD_SAFE_TAC long;

    (*** The scalar loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `len:num`))) THEN
    SUBGOAL_THEN
     `word_add (word_add a (word(2 * (start + len + i))))
               (word(2 * val(word_neg(word len):int64))):int64 =
      word_add a (word(2 * (start + i)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_2_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--17) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (18--18) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) ->
      let t = rand(rator(rator(find_term
                (fun t -> is_cond t && is_neg(rand(rator(rator t)))) w))) in
      SUBGOAL_THEN (mk_eq(t,`i + 1 < len`)) SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK2_SAFE = prove
 (invntt_sblock_safe_goal `len = 2`,INVNTT_SBLOCK_SAFE_TAC false);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK4_SAFE = prove
 (invntt_sblock_safe_goal
   `len = 4 /\ val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64`,
  INVNTT_SBLOCK_SAFE_TAC true);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_DBLOCK_SAFE = prove
 (invntt_sblock_safe_goal
   `len = 4 /\ ~(val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64)`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (start:num) (len:num).
      f_ev_dblk a zetas pc start len:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  INVNTT_SAFE_FRAME_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  REG_SMALL_TAC `X9` `word(k - 1):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
  REG_SMALL_TAC `X30` `word 4:int64` THEN
  REG_SMALL_TAC `X20` `word 3:int64` THEN
  REG_SMALL_TAC `X3` `word start:int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--7) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (8--18) THEN
  REG_SMALL_TAC `X0` `word_add a (word(2 * start + 24)):int64` THEN
  REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
  REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
  REG_SMALL_TAC `X1` `word_add a (word(2 * start + 8)):int64` THEN
  REG_SMALL_TAC `X19` `word(start + 4):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (19--20) THEN
  MP_TAC(SPECL [`a:int64`; `2 * start`] NTT_ALIAS_SCALAR_WRAP) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (21--22) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (23--33) THEN
  REG_SMALL_TAC `X0` `word(2 * (start + 4)):int64` THEN
  REG_SMALL_TAC `X3` `word(2 * start):int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (34--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** A block of 4 + 4 coefficients, wherever it is ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_BLOCK4_SAFE = prove
 (invntt_sblock_safe_goal `len = 4`,
  let fty = type_of(fst(dest_exists
    (concl MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK4_SAFE))) in
  let f4 = mk_var("f4",fty) and fd = mk_var("fd",fty)
  and args = [`a:int64`; `zetas:num`; `pc:num`; `start:num`; `len:num`] in
  X_CHOOSE_TAC f4 MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK4_SAFE THEN
  X_CHOOSE_TAC fd MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_DBLOCK_SAFE THEN
  EXISTS_TAC(list_mk_abs(args,
   mk_cond(`val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64`,
           list_mk_comb(f4,args),list_mk_comb(fd,args)))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let INVNTT_GCC12_O3_VBLOCK_EVENTS =
  new_specification ["invntt_gcc12_O3_vblock_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_VBLOCK_SAFE;;

let INVNTT_GCC12_O3_BLOCK4_EVENTS =
  new_specification ["invntt_gcc12_O3_block4_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_BLOCK4_SAFE;;

let INVNTT_GCC12_O3_SBLOCK2_EVENTS =
  new_specification ["invntt_gcc12_O3_sblock2_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SBLOCK2_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X17 s = word L /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_exit) /\
               read X17 s = word L /\
               read X4 s = a /\ read X18 s = word_add a (word 2) /\
               read X15 s = word zetas /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21; X30] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The events of block b of layer l, from the block lemmas ***)

let invntt_blk_events l b =
  let len = 1 lsl (8 - l) in
  let start = rhs(concl(NUM_REDUCE_CONV(subst
                [mk_small_numeral len,`LEN:num`; b,`B:num`] `2 * LEN * B`))) in
  if l <= 5 then
    list_mk_comb(`invntt_gcc12_O3_vblock_events`,
      [`a:int64`; `zetas:num`; `pc:num`; start; mk_small_numeral(len / 8)])
  else
    list_mk_comb((if l = 6 then `invntt_gcc12_O3_block4_events`
                  else `invntt_gcc12_O3_sblock2_events`),
      [`a:int64`; `zetas:num`; `pc:num`; start; mk_small_numeral len]);;

(*** The event template for layer l ***)

let lsafe_template l =
  let app x y = list_mk_icomb "APPEND" [x;y]
  and fev n args =
    list_mk_comb(mk_var(n,itlist (mk_fun_ty o type_of) args
                                 `:(uarch_event)list`),args) in
  let base = [`a:int64`; `zetas:num`; `pc:num`] in
  let blk0 = app (fev "f_ev_ltest0" base)
                 (app (invntt_blk_events l `0`) (fev "f_ev_lhead" base)) in
  let body =
    if l = 1 then blk0 else
    app (fev "f_ev_lexit" base)
     (app (mk_icomb(mk_icomb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                          (uarch_event)list`,
                              mk_small_numeral(1 lsl (l - 1) - 1)),
           mk_abs(`i:num`,
             app (fev "f_ev_ltest" (base @ [`i:num`]))
                 (app (invntt_blk_events l `i + 1`)
                      (fev "f_ev_lzeta" (base @ [`i:num`]))))))
          blk0) in
  list_mk_abs(base,body);;

(*** The block lemma for block b of layer l ***)

let invntt_block_events_inst l b ev =
  let len = 1 lsl (8 - l) in
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral len,`LEN:num`;
      b,`B:num`] t))) in
  let th =
    if l <= 5 then INVNTT_GCC12_O3_VBLOCK_EVENTS
    else if l = 6 then INVNTT_GCC12_O3_BLOCK4_EVENTS
    else INVNTT_GCC12_O3_SBLOCK2_EVENTS in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`;
         red `2 * LEN * B`;
         (if l <= 5 then mk_small_numeral(len / 8) else red `LEN:num`);
         red `2 EXP L - 1 - B`; red `word L:int64`;
         `sp:int64`; `x19v:int64`; `x20v:int64`; `x21v:int64`; `ra:int64`] th;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. read X5 s = word(2 * LEN * B) /\
        read X7 s = word(2 * LEN * B + LEN) /\
        read X9 s = word(2 EXP L - 1 - B) /\
        read X4 s = a /\ read X18 s = word_add a (word 2) /\
        read X15 s = word zetas /\
        read X13 s = word(2 * LEN) /\ read X14 s = word LEN /\
        read X16 s = word LEN /\ read X17 s = word L /\
        read SP s = sp /\
        read(memory :> bytes64 sp) s = x19v /\
        read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
        read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
        read(memory :> bytes64(word_add sp (word 24))) s = ra` in
  let mk l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] headtm))) in
  mk,mk;;

let LSAFE_TEST_TAC k =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         if c = subst [k,`K:num`] `i + 1 < K` then ALL_TAC (asl,w) else
         (SUBGOAL_THEN (mk_eq(c,subst [k,`K:num`] `~(i + 1 < K)`))
          SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [W(fun (_,w) -> if is_exists w then NO_TAC else ALL_TAC) THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let INVNTT_LAYER_SAFE_TAC l =
  let k = mk_small_numeral(1 lsl (l - 1) - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_test1`
     (lsafe_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3`
       (lsafe_blockhead_tm l `0`) THEN
      CONJ_TAC THENL
       [INVNTT_SAFE_SIM_TAC ALL_TAC 12;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `0`)];
      INVNTT_SAFE_SIM_TAC ALL_TAC 2] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  INVNTT_SAFE_FRAME_TAC THEN
  if l = 1 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mlkem_poly_invntt_tomont_loop3_next1`
   `pc + mlkem_poly_invntt_tomont_loop3_exit`
   (mk_abs(`i:num`,lsafe_blockend_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_test1`
      (lsafe_blockend_tm l `i + 1 + 1`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3`
        (lsafe_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [INVNTT_SAFE_SIM_TAC
         (let n = rhs(concl(NUM_REDUCE_CONV
                   (subst [mk_small_numeral l,`L:num`]
                          `2 EXP L - 1 - (i + 1)`))) in
          MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]) 2;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `i + 1`)];
      LSAFE_TEST_TAC k];
    INVNTT_SAFE_SIM_TAC ALL_TAC 0];;

let INVNTT_GCC12_O3_LAYER_EVENTS =
  map (fun l ->
        new_specification ["invntt_gcc12_O3_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7);;

(*** The scaling loop at the start ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SCALE_SAFE = prove
 (`exists f_ev_scale.
    forall e a pc sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (sp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1) /\
               read X0 s = a /\ read X1 s = word_add a (word 512) /\
               read X4 s = a /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1_exit) /\
               read X4 s = a /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_scale a pc /\
                 memaccess_inbounds e2 [a,512] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_sexit a pc)
        (APPEND (ENUMERATEL 32 (\i. f_ev_sloop a pc i)) (f_ev_shead a pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  INVNTT_SAFE_FRAME_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_invntt_tomont_loop1`
   `pc + mlkem_poly_invntt_tomont_loop1_exit`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read X4 s = a /\
          read SP s = sp /\
          read(memory :> bytes64 sp) s = x19v /\
          read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
          read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
          read(memory :> bytes64(word_add sp (word 24))) s = ra` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for 8 coefficients, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (10--10) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (11--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) ->
      let t = rand(rator(rator(find_term
                (fun t -> is_cond t && is_neg(rand(rator(rator t)))) w))) in
      SUBGOAL_THEN (mk_eq(t,`i + 1 < 32`)) SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    INVNTT_SAFE_SIM_TAC ALL_TAC 0]);;

let INVNTT_GCC12_O3_SCALE_EVENTS =
  new_specification ["invntt_gcc12_O3_scale_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_SCALE_SAFE;;

(*** The whole code, which has the same signature as mlkem_reduce, with the
 *** table of zetas and the vectors of constants as read-only objects. The
 *** stack pointer after saving X19 to X21 and X30 is the parameter sp.
 ***)

let invntt_top_template =
  let lay l = list_mk_comb
   (mk_const("invntt_gcc12_O3_layer_events_" ^ string_of_int l,[]),
    [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev n =
    list_mk_comb
     (mk_var(n,`:int64->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    let acc' = app (lay l) acc in
    if l = 1 then acc' else
    chain (l - 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let start =
    app (fev "f_ev_setup")
     (app `invntt_gcc12_O3_scale_events a pc` (fev "f_ev_init")) in
  let body = app (fev "f_ev_fin") (chain 7 start) in
  list_mk_abs([`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`],body);;

let invntt_safe_stack_tm =
  `read SP s = stackpointer /\
   read(memory :> bytes64 stackpointer) s = x19_init /\
   read(memory :> bytes64(word_add stackpointer (word 8))) s = x20_init /\
   read(memory :> bytes64(word_add stackpointer (word 16))) s = x21_init /\
   read(memory :> bytes64(word_add stackpointer (word 24))) s =
   returnaddress`;;

let invntt_safe_layer_tm l =
  let tm =
   `\s. read X17 s = word L /\ read X4 s = a /\
        read X18 s = word_add a (word 2) /\
        read X15 s = word(pc + rodata_mlk_zetas) /\ STK` in
  let tm' = subst [mk_small_numeral l,`L:num`]
              (mk_abs(`s:armstate`,
                 subst [invntt_safe_stack_tm,`STK:bool`] (body tm))) in
  rhs(concl(NUM_REDUCE_CONV tm'));;

let invntt_safe_scalehead_tm,invntt_safe_scaleend_tm =
  let mk tm = mk_abs(`s:armstate`,
                     subst [invntt_safe_stack_tm,`STK:bool`] (body tm)) in
  mk `\s. read X0 s = a /\ read X1 s = word_add a (word 512) /\
          read X4 s = a /\ STK`,
  mk `\s. read X4 s = a /\ STK`;;

let invntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
         `stackpointer:int64`; `x19_init:int64`; `x20_init:int64`;
         `x21_init:int64`; `returnaddress:int64`]
        (el (l - 1) INVNTT_GCC12_O3_LAYER_EVENTS);;

let invntt_scale_events_inst ev =
  SPECL [ev; `a:int64`; `pc:num`;
         `stackpointer:int64`; `x19_init:int64`; `x20_init:int64`;
         `x21_init:int64`; `returnaddress:int64`]
        INVNTT_GCC12_O3_SCALE_EVENTS;;

(*** The events of a lemma are in bounds for the regions of the whole code ***)

let MEMACCESS_WIDEN_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),e),rr),wr) ->
        (fun (asl,w) ->
          match w with
            Comb(Comb(Comb(Const("memaccess_inbounds",_),e'),rr'),wr')
            when e' = e ->
              (MP_TAC(ISPECL [e;rr;rr';wr;wr'] MEMACCESS_INBOUNDS_MEM) THEN
               REWRITE_TAC[ALL; MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
               ACCEPT_TAC th) (asl,w)
          | _ -> failwith "MEMACCESS_WIDEN_TAC")
    | _ -> failwith "MEMACCESS_WIDEN_TAC");;

let INVNTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC invntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NORMALIZE_ALIGNED_WORD_CONV)) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** Restoring X19 to X21 and X30 and returning after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop3_exit` (invntt_safe_layer_tm 1) THEN
  CONJ_TAC THENL [ALL_TAC; INVNTT_SAFE_SIM_TAC ALL_TAC 5] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop2` (invntt_safe_layer_tm l) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EVENTS_LEMMA_TAC (invntt_layer_events_inst l) THEN
      MEMACCESS_WIDEN_TAC] THEN
    if l = 7 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop3_exit`
     (invntt_safe_layer_tm (l + 1)) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_SAFE_SIM_TAC ALL_TAC 7]) (1--7) THEN

  (*** The setup of the constants for the layers ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop1_exit` invntt_safe_scaleend_tm THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (2--4) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (5--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (11--19) THEN
    REG_REWRITE_TAC `X15` [GSYM WORD_ADD] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The scaling, after saving X19 to X21 and X30 ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop1` invntt_safe_scalehead_tm THEN
  CONJ_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (3--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC (7--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    EVENTS_LEMMA_TAC invntt_scale_events_inst THEN MEMACCESS_WIDEN_TAC];;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_invntt_tomont_consts):int64`,
                       `mlkem_poly_invntt_tomont_consts_size:num`;
                       `word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (a,512))
           [word pc,libmlkem_size; word_sub stackpointer (word 32),32] /\
       nonoverlapping (word_sub stackpointer (word 32),32)
         (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O3_mc /\
                read PC s = word (pc + mlkem_poly_invntt_tomont) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc
                         (word_sub stackpointer (word 32)) returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 32),32;
                    word (pc + mlkem_poly_invntt_tomont_consts),
                    mlkem_poly_invntt_tomont_consts_size;
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 32),32])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN INVNTT_SAFE_TOP_TAC);;
