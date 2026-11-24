(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O2/poly_ntt_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Word and index lemmas.                                                    *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Word and index lemmas.                                                    *)
(* ------------------------------------------------------------------------- *)


let RANGE8_SPLIT = prove
 (RANGE8_SPLIT_STMT,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `8 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `8 * i <= j ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;



let NTT_VEC_ADDR = prove
 (NTT_VEC_ADDR_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;



let NTT_VEC_ADDR2 = prove
 (NTT_VEC_ADDR2_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;


let NTT_BLOCK_C_LO8 = prove
 (NTT_BLOCK_C_LO8_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_block_c] THEN
  COND_CASES_TAC THENL
   [REPEAT AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;


let NTT_BLOCK_C_HI8 = prove
 (NTT_BLOCK_C_HI8_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_block_c] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;


let NTT_BLOCK_JOIN = prove
 (NTT_BLOCK_JOIN_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let bd,h1,h2,h3,h4 =
      match CONJUNCTS th with
        [bd;h1;h2;h3;h4] -> bd,h1,h2,h3,h4
      | _ -> failwith "NTT_BLOCK_JOIN" in
    ASSUME_TAC bd THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < start` THENL
     [ASM_SIMP_TAC[h1; ntt_block_c; ARITH_RULE
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
    REWRITE_TAC[ntt_block_c] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC h2 THEN ASM_ARITH_TAC));;



let WORD_ZX_ZX_SX_16 = prove
 (WORD_ZX_ZX_SX_16_STMT,
  BITBLAST_TAC);;



let NTT_DIV8 = prove
 (NTT_DIV8_STMT,
  GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN ARITH_TAC);;


let NTT_VAL_LE_64 = prove
 (NTT_VAL_LE_64_STMT,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;


let NTT_VAL_WORD_64 = prove
 (NTT_VAL_WORD_64_STMT,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;


let NTT_WORD_ADD_NUM = prove
 (NTT_WORD_ADD_NUM_STMT,
  REWRITE_TAC[WORD_ADD]);;


let NTT_SHL1 = prove
 (NTT_SHL1_STMT,
  GEN_TAC THEN CONV_TAC WORD_RULE);;


let NTT_WORD_SHL_AND_1 = prove
 (`!w:int64. word_and (word_shl w 1) (word 1) = word 0`,
  BITBLAST_TAC);;


let NTT_WORD_SHL_AND_2 = prove
 (`!w:int64. word_and (word_shl w 2) (word 2) = word 0`,
  BITBLAST_TAC);;


let NTT_WORD_OR_1 = prove
 (NTT_WORD_OR_1_STMT,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP WORD_ADD_OR (SPEC `word m:int64` NTT_WORD_SHL_AND_1)) THEN
  REWRITE_TAC[NTT_SHL1; WORD_ADD; ARITH_RULE `m + m = 2 * m`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ARITH_RULE `2 * m = m + m`]);;


let NTT_WORD_OR_2 = prove
 (NTT_WORD_OR_2_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. x = 4 * m` (CHOOSE_THEN SUBST1_TAC) THENL
   [EXISTS_TAC `x DIV 4` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP WORD_ADD_OR (SPEC `word m:int64` NTT_WORD_SHL_AND_2)) THEN
  SUBGOAL_THEN `word_shl (word m:int64) 2 = word(4 * m)`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(*** The quotient of a Montgomery reduction, as computed from t * q^-1 * 2^16 ***)


(*** The quotient of a Montgomery reduction, as computed from t * q^-1 * 2^16 ***)

let WORD_ISHR_16_SUBWORD = prove
 (`!w:int32. word_ishr w 16 = word_sx(word_subword w (16,16):int16)`,
  BITBLAST_TAC);;


let NTT_LANE = prove
 (NTT_LANE_STMT,
  GEN_TAC THEN REWRITE_TAC[GSYM MONTRED_NEON_SCALAR; montred_neon] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_ISHR_16_SUBWORD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD;
              DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(t:int32)`,`v:num`) THEN GEN_TAC THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1] THEN
  REWRITE_TAC[ARITH_RULE `v * 4076929024 = 65536 * v * 62209`;
              ARITH_RULE `4294967296 = 65536 * 65536`] THEN
  REWRITE_TAC[MOD_MULT2] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MOD; ARITH_EQ; MOD_MULT_LMOD]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the C computation.                                          *)
(* ------------------------------------------------------------------------- *)


let NTT_BLOCKS_C_CLOSED = prove
 (NTT_BLOCKS_C_CLOSED_STMT,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[ntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (7 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (7 - l)` THEN DISCH_TAC THEN
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


let NTT_LAYERS_C_STEP = prove
 (NTT_LAYERS_C_STEP_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_layers_c; NTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `i < 2 * 2 EXP (7 - l) * 2 EXP l`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < 7 ==> 7 - l + l = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;


let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;


let NTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 ntt_layers_c :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[ntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun l i ->
    let th = SPECL [mk_small_numeral l; `x:num->int16`; mk_small_numeral i]
                   NTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;


(*** All the layer equations, in the order of the layers ***)

let NTT_LAYER_EQUATIONS =
  map (fun (l,i) -> SYM(NTT_LAYER_EQUATION l i))
      (List.concat (map (fun l -> map (fun i -> (l,i)) (0--255)) (0--6)));;


let NTT_FINAL_TAC lfn =
  W(fun (asl,w) ->
    let tm = find_term (can (term_match [] `ntt_layers_c 7 x i`)) w in
    let th = apply lfn tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;


let NTT_LAYERS_C_CORRECT = prove
 (NTT_LAYERS_C_CORRECT_STMT,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let lfn = MLKEM_NATIVE_LOCAL_CONGBOUND_RULE
                (PROCESS_BOUND_ASSUMPTIONS (map snd asl))
                NTT_LAYER_EQUATIONS in
    REPEAT CONJ_TAC THEN NTT_FINAL_TAC lfn));;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the blocks, for each layer.                                *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCK_THMS = map2
  (fun l tac -> prove(el l NTT_BLOCK_STMTS, tac))
  (0--6)
  [NTT_VBLOCK_TAC 0; NTT_VBLOCK_TAC 1; NTT_VBLOCK_TAC 2; NTT_VBLOCK_TAC 3;
   NTT_VBLOCK_TAC 4; NTT_SBLOCK_TAC 5; NTT_SBLOCK_TAC 6];;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the layers.                                                *)
(* ------------------------------------------------------------------------- *)

let NTT_LAYER_THMS = map
  (fun l -> prove(el l NTT_LAYER_STMTS, NTT_LAYER_TAC l)) (0--6);;

let NTT_LAYERS = prove
 (NTT_LAYERS_STMT,
  NTT_LAYERS_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   ["x19_init",`X19`; "x20_init",`X20`; "x21_init",`X21`; "x22_init",`X22`;
    "x23_init",`X23`; "x24_init",`X24`; "x25_init",`X25`; "x26_init",`X26`;
    "x27_init",`X27`; "x28_init",`X28`] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The prologue, saving the registers, and the constants ***)

  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC [n] THEN
    MLKEM_NATIVE_ADRP_TAC) (1--15) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
    MATCH_MP (MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data
               (layout "rodata_mlk_zetas"))) THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val (a:int64),512)
                          (pc + rodata_mlk_zetas,256)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2 EXP 64`; `val(a:int64)`; `512`; `pc:num`;
                   `libmlkem_size:num`;
                   `val(a:int64)`; `512`; `pc + rodata_mlk_zetas`; `256`]
            NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    ASM_REWRITE_TAC[CONTAINED_MODULO_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ARITH_TAC; MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ARITH_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("X11",_)),_)),_) ->
      REWRITE_RULE[GSYM WORD_ADD] th
  | _ -> th) THEN

  (*** The seven layers ***)

  MP_TAC(SPECL [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`; `x:num->int16`]
         NTT_LAYERS) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC "s16" THEN

  (*** Restoring the registers and returning ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC (17--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:num->int16` NTT_LAYERS_C_CORRECT) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCK_SAFE_THMS = map2
  (fun l tac -> prove(el l NTT_BLOCK_SAFE_STMTS, tac))
  (0--6)
  [NTT_VBLOCK_SAFE_TAC 0; NTT_VBLOCK_SAFE_TAC 1; NTT_VBLOCK_SAFE_TAC 2;
   NTT_VBLOCK_SAFE_TAC 3; NTT_VBLOCK_SAFE_TAC 4; NTT_SBLOCK_SAFE_TAC 5;
   NTT_SBLOCK_SAFE_TAC 6];;

let NTT_LAYER_SAFE_THMS = map
  (fun l -> prove(el l NTT_LAYER_SAFE_STMTS, NTT_LAYER_SAFE_TAC l))
  (0--6);;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN NTT_SAFE_TOP_TAC);;
