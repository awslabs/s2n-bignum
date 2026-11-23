(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Checking that bytes encode ML-KEM polynomials with reduced coefficients.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_check_encoding.o";;
 ****)

let mlkem_check_encoding_mc = define_assert_from_elf
  "mlkem_check_encoding_mc" "arm/mlkem/mlkem_check_encoding.o"
[
  0xd503245f;       (* arm_BTI *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a04022;       (* arm_MOVK X2 (word 513) 16 *)
  0xf2c08062;       (* arm_MOVK X2 (word 1027) 32 *)
  0xf2e0a082;       (* arm_MOVK X2 (word 1284) 48 *)
  0xd280e0c3;       (* arm_MOV X3 (rvalue (word 1798)) *)
  0xf2a100e3;       (* arm_MOVK X3 (word 2055) 16 *)
  0xf2c14123;       (* arm_MOVK X3 (word 2569) 32 *)
  0xf2e16143;       (* arm_MOVK X3 (word 2826) 48 *)
  0x9e67005f;       (* arm_FMOV_ItoF Q31 X2 0 *)
  0x4e181c7f;       (* arm_INS_GEN Q31 X3 64 64 *)
  0xd281ffe2;       (* arm_MOV X2 (rvalue (word 4095)) *)
  0xf2bffe02;       (* arm_MOVK X2 (word 65520) 16 *)
  0x4e040c5d;       (* arm_DUP_GEN Q29 X2 32 128 *)
  0x6f00e410;       (* arm_MOVI Q16 (word 0) *)
  0x6f00e411;       (* arm_MOVI Q17 (word 0) *)
  0x6f00e412;       (* arm_MOVI Q18 (word 0) *)
  0x6f00e413;       (* arm_MOVI Q19 (word 0) *)
  0xd37df024;       (* arm_LSL X4 X1 3 *)
  0xb4000284;       (* arm_CBZ X4 (word 80) *)
  0xacc10400;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (iword (&32))) *)
  0x3cc10402;       (* arm_LDR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0x6e016004;       (* arm_EXT Q4 Q0 Q1 96 *)
  0x6e024025;       (* arm_EXT Q5 Q1 Q2 64 *)
  0x6e022046;       (* arm_EXT Q6 Q2 Q2 32 *)
  0x4e1f0003;       (* arm_TBL Q3 [Q0] Q31 128 *)
  0x4e1f0084;       (* arm_TBL Q4 [Q4] Q31 128 *)
  0x4e1f00a5;       (* arm_TBL Q5 [Q5] Q31 128 *)
  0x4e1f00c6;       (* arm_TBL Q6 [Q6] Q31 128 *)
  0x4e3d1c63;       (* arm_AND_VEC Q3 Q3 Q29 128 *)
  0x4e3d1c84;       (* arm_AND_VEC Q4 Q4 Q29 128 *)
  0x4e3d1ca5;       (* arm_AND_VEC Q5 Q5 Q29 128 *)
  0x4e3d1cc6;       (* arm_AND_VEC Q6 Q6 Q29 128 *)
  0x6e636610;       (* arm_UMAX_VEC Q16 Q16 Q3 16 128 *)
  0x6e646631;       (* arm_UMAX_VEC Q17 Q17 Q4 16 128 *)
  0x6e656652;       (* arm_UMAX_VEC Q18 Q18 Q5 16 128 *)
  0x6e666673;       (* arm_UMAX_VEC Q19 Q19 Q6 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffdc1;       (* arm_BNE (word 2097080) *)
  0xd281a022;       (* arm_MOV X2 (rvalue (word 3329)) *)
  0xf2ba0202;       (* arm_MOVK X2 (word 53264) 16 *)
  0x6e716610;       (* arm_UMAX_VEC Q16 Q16 Q17 16 128 *)
  0x6e736652;       (* arm_UMAX_VEC Q18 Q18 Q19 16 128 *)
  0x6e726610;       (* arm_UMAX_VEC Q16 Q16 Q18 16 128 *)
  0x4e040c5d;       (* arm_DUP_GEN Q29 X2 32 128 *)
  0x6e7d3e10;       (* arm_CMHS_VEC Q16 Q16 Q29 16 128 *)
  0x6e70aa10;       (* arm_UMAXV Q16 Q16 8 16 *)
  0x1e260202;       (* arm_FMOV_FtoI W2 Q16 0 32 *)
  0x7100005f;       (* arm_CMP W2 (rvalue (word 0)) *)
  0x9a9f17e0;       (* arm_CSET X0 Condition_EQ *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_check_encoding_tmc =
  define_trimmed "mlkem_check_encoding_tmc" mlkem_check_encoding_mc;;

let MLKEM_CHECK_ENCODING_EXEC = ARM_MK_EXEC_RULE mlkem_check_encoding_tmc;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let WORD_UGE_UMAX = prove
 (`!x y z:N word.
        word_uge (word_umax x y) z <=> word_uge x z \/ word_uge y z`,
  REWRITE_TAC[WORD_UGE; VAL_WORD_UMAX] THEN ARITH_TAC);;

let CHECK_ENCODING_LOADS = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 48 <= m
        ==> !j. j < 3
                ==> read (memory :> bytes128(word_add a (word(k + 16 * j))))
                         s =
                    word_subword
                     (word((n DIV 2 EXP (8 * k)) MOD 2 EXP 384):384 word)
                     (128 * j,128)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `m:num`; `n:num`; `k + 16 * j`; `s:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:384)`;
               ARITH_RULE `j < 3 ==> 128 * j + 128 <= 384`] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW;
               ARITH_RULE `j < 3 ==> 128 * j + 128 <= 384`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD;
              ARITH_RULE `8 * (k + 16 * j) = 8 * k + 128 * j`]);;

let EXISTS_LT_ADD1 = prove
 (`!P i. (?t. t < i + 1 /\ P t) <=> (?t. t < i /\ P t) \/ P i`,
  REWRITE_TAC[GSYM ADD1; LT] THEN MESON_TAC[]);;

(* Whether field i (of 12 bits) is out of range, i.e. at least 3329. *)

let cenc_bad = new_definition
 `cenc_bad n i <=> 3329 <= (n DIV 2 EXP (12 * i)) MOD 2 EXP 12`;;

let CHECK_ENCODING_FIELD = prove
 (`!n i c.
        word((n DIV 2 EXP (8 * (48 * i))) MOD 2 EXP 384) = c
        ==> !j. j < 32
                ==> (cenc_bad n (32 * i + j) <=>
                     word_uge (word_subword (c:384 word) (12 * j,12):12 word)
                              (word 3329))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[cenc_bad; WORD_UGE; GE] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_CONV `dimindex(:384)`;
              DIMINDEX_CONV `dimindex(:12)`; MOD_MOD_REFL;
              ARITH_RULE `MIN 12 12 = 12`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW;
               ARITH_RULE `j < 32 ==> 12 * j + 12 <= 384`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * 48 * i + 12 * j = 12 * (32 * i + j)`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CHECK_ENCODING_MASK_MAX = prove
 (`!b0 b1.
    MAX (val(word_subword (word_neg(word(bitval b0)):int16) (0,16):int128))
        (val(word_subword (word_neg(word(bitval b1)):int16) (0,16):int128)) =
    val(word_subword (word_neg(word(bitval(b0 \/ b1))):int16) (0,16):int128)`,
  REPEAT GEN_TAC THEN
  BOOL_CASES_TAC `b0:bool` THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[MAX] THEN CONV_TAC NUM_REDUCE_CONV);;

let CHECK_ENCODING_ALL = prove
 (`!n k. (!i. i < 256 * k ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329) <=>
         (!j. j < 32 ==> ~(?t. t < 8 * k /\ cenc_bad n (32 * t + j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cenc_bad; NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`;
              NOT_LE] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i MOD 32`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o SPEC `i DIV 32`) THEN
    REWRITE_TAC[ARITH_RULE `32 * i DIV 32 + i MOD 32 = i`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_CORRECT = prove
 (`!a k n pc.
        val k < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n)
             (\s. read PC s = word(pc + 0xc4) /\
                  C_RETURN s =
                  if !i. i < 256 * val k
                         ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                  then word 1 else word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN] THEN
  DISCH_TAC THEN

  (*** The trivial case k = 0, when the loop is skipped ***)

  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The invariant: lane j of the four maxima is at least its bound ***)
  (*** exactly when one of the fields j, 32 + j, ... so far is bad.   ***)

  ENSURES_WHILE_PUP_TAC `8 * k` `pc + 0x4c` `pc + 0x94`
   `\i s. (read X0 s = word_add a (word(48 * i)) /\
           read X4 s = word(8 * k - i) /\
           read Q29 s = word 0xfff00ffffff00ffffff00ffffff00fff /\
           read Q31 s = word 0x0b0a0a09080707060504040302010100 /\
           read (memory :> bytes(a,384 * k)) s = n /\
           !j. j < 32
               ==> (word_uge
                     (word_subword
                       (word_join
                         (word_join (read Q19 s) (read Q18 s):256 word)
                         (word_join (read Q17 s) (read Q16 s):256 word)
                        :512 word) (16 * j,16):int16)
                     (word(if EVEN j then 3329 else 53264)) <=>
                    ?t. t < i /\ cenc_bad n (32 * t + j))) /\
          (read ZF s <=> i = 8 * k)` THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * k = 0 <=> k = 0`] THEN REPEAT CONJ_TAC THENL
   [(*** The initialization, with all lanes 0 ***)

    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `word_shl (word k:int64) 3 = word(8 * k)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 3 * k = 8 * k`];
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(8 * k):int64) = 8 * k /\ ~(8 * k = 0)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0; WORD_UGE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
    ARITH_TAC;

    (*** The loop body, on the 384-bit chunk c of the input ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC
     `c:384 word = word((n DIV 2 EXP (8 * (48 * i))) MOD 2 EXP 384)` THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    MP_TAC(SPECL [`a:int64`; `384 * k`; `n:num`; `48 * i`; `s0:armstate`]
      CHECK_ENCODING_LOADS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 8 * k` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_sub (word (8 * k - i)) (word 1):int64 = word(8 * k - (i + 1))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`8 * k - i`; `1`] (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 8 * k ==> 1 <= 8 * k - i`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(8 * k - (i + 1)):int64) = 8 * k - (i + 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `i < 8 * k` THEN ARITH_TAC] THEN

    (*** The invariant for each lane before, and the new fields ***)

    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                       SIMD_SIMPLIFY_CONV[])) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `i:num`; `c:384 word`] CHECK_ENCODING_FIELD) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN

    (*** Split the maxima into lanes, and check each new one ***)

    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             SIMD_SIMPLIFY_CONV[]) THEN
    REWRITE_TAC[WORD_UGE_UMAX; EXISTS_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
    LANE_ARGS_BITBLAST_TAC 8 [];

    (*** The backward branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
    ASM_REWRITE_TAC[];

    (*** The combination of the maxima and the final comparison ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                       SIMD_SIMPLIFY_CONV[])) THEN
    STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_UGE_UMAX] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CHECK_ENCODING_MASK_MAX; CHECK_ENCODING_ALL] THEN
    CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
                       NUM_REDUCE_CONV)) THEN
    W(fun (asl,w) ->
      let bv = find_term (fun t -> match t with
                   Comb(Const("bitval",_),_) -> true | _ -> false) w in
      let d = rand bv in
      SUBGOAL_THEN (mk_eq(lhand w,mk_cond(d,`word 0:int64`,`word 1:int64`)))
      SUBST1_TAC THENL
       [SPEC_TAC(d,`b:bool`) THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
        REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM COND_SWAP] THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[DE_MORGAN_THM] THEN
        W(fun (_,w) -> ACCEPT_TAC(CONJ_ACI_RULE w))])]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a k n pc returnaddress.
        val k < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  if !i. i < 256 * val k
                         ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                  then word 1 else word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_CHECK_ENCODING_EXEC
    MLKEM_CHECK_ENCODING_CORRECT);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT = prove
 (`!a k n pc returnaddress.
        val k < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  if !i. i < 256 * val k
                         ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                  then word 1 else word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_check_encoding_mc mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_check_encoding" subroutine_signatures)
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CHECK_ENCODING_EXEC;;

(* The loop runs 8 * k times, so the events are those of the setup, of       *)
(* each iteration and of the end, or when k = 0 just those of a setup        *)
(* that skips the loop.                                                      *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a k pc returnaddress.
           val k < 2 EXP 61
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_check_encoding_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; k] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a k pc returnaddress /\
                        memaccess_inbounds e2 [a,(384 * val k) * 1] [])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_zero a k pc returnaddress
      else APPEND (f_ev_epil a k pc returnaddress)
                  (APPEND (ENUMERATEL (8 * val k)
                             (\i. f_ev_loop a k pc returnaddress i))
                          (f_ev_prol a k pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; fst MLKEM_CHECK_ENCODING_EXEC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--31) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_shl (word k:int64) 3 = word(8 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 * k = 8 * k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(8 * k):int64) = 8 * k /\ ~(8 * k = 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8 * k` `pc + 0x4c` `pc + 0x98`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add a (word(48 * i)) /\
          read X4 s = word(8 * k - i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--19) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word (8 * k - i)) (word 1):int64 = word(8 * k - (i + 1)) /\
      val(word(8 * k - (i + 1)):int64) = 8 * k - (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`8 * k - i`; `1`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 8 * k ==> 1 <= 8 * k - i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--19) THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--12) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a k pc returnaddress.
           val k < 2 EXP 61
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; k] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a k pc returnaddress /\
                        memaccess_inbounds e2 [a,(384 * val k) * 1] [])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_check_encoding_mc mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE));;
