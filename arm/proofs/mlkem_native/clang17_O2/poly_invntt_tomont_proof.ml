(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O2/poly_invntt_tomont_spec.ml";;

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


let INVNTT_BLOCK_C_LO8 = prove
 (INVNTT_BLOCK_C_LO8_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;


let INVNTT_BLOCK_C_HI8 = prove
 (INVNTT_BLOCK_C_HI8_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invntt_block_c] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REPEAT AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;


let INVNTT_BLOCK_JOIN = prove
 (INVNTT_BLOCK_JOIN_STMT,
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


let BARRED_VEC_LANE = prove
 (BARRED_VEC_LANE_STMT,
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


let INVNTT_BLOCKS_C_CLOSED = prove
 (INVNTT_BLOCKS_C_CLOSED_STMT,
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
 (INVNTT_LAYERS_C_STEP_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[invntt_layers_c; INVNTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `2 * 2 EXP (8 - (7 - n)) * 2 EXP (6 - n) = 256`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 7 ==> 8 - (7 - n) + 6 - n = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let INVNTT_LAYERS_C_CORRECT = prove
 (INVNTT_LAYERS_C_CORRECT_STMT,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN INVNTT_FINAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the blocks, for each layer.                                *)
(* ------------------------------------------------------------------------- *)

let INV_BLOCK_THMS = map2
  (fun n tac -> prove(el n INVNTT_BLOCK_STMTS, tac))
  (0--6)
  [INV_SBLOCK_TAC 0; INV_SBLOCK_TAC 1; INV_VBLOCK_TAC 2; INV_VBLOCK_TAC 3;
   INV_VBLOCK_TAC 4; INV_VBLOCK_TAC 5; INV_VBLOCK_TAC 6];;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the layers.                                                *)
(* ------------------------------------------------------------------------- *)

let INV_LAYER_THMS = map
  (fun n -> prove(el n INVNTT_LAYER_STMTS, INV_LAYER_TAC n)) (0--6);;

let INVNTT_LAYERS = prove
 (INVNTT_LAYERS_STMT,
  INV_LAYERS_TAC);;

(* ------------------------------------------------------------------------- *)
(* The scaling loop.                                                         *)
(* ------------------------------------------------------------------------- *)


(*** proofs ***)

let CHUNK16_INPUT_SPLIT = prove
 (CHUNK16_INPUT_SPLIT_STMT,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `16 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `16 * i <= j ==> 16 * i + (j - 16 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;


let CHUNK16_OUTPUT_SPLIT = prove
 (CHUNK16_OUTPUT_SPLIT_STMT,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 16 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 16 * i) ==> 16 * i + (j - 16 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;


let CHUNK16_ADDR = prove
 (CHUNK16_ADDR_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;


let INVNTT_SCALE_FACTOR = prove
 (INVNTT_SCALE_FACTOR_STMT,
  BITBLAST_TAC);;


let INVNTT_SCALE_MONTRED = prove
 (INVNTT_SCALE_MONTRED_STMT,
  REWRITE_TAC[WORD_SHL_ZERO; INVNTT_SCALE_FACTOR; montred_neon]);;


let INVNTT_SCALE = prove
 (INVNTT_SCALE_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `16` `pc + mlkem_poly_invntt_tomont_loop1`
   `pc + mlkem_poly_invntt_tomont_loop1_exit`
   `\i s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_clang17_O2_mc /\
          read X0 s = a /\ read X8 s = word(32 * i) /\
          read Q0 s = word 0x05a105a105a105a105a105a105a105a1 /\
          read Q1 s = word 0xd8a10000d8a10000d8a10000d8a10000 /\
          read Q2 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
          (!j. 16 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 16 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   invntt_scale_c x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the constants and the offset ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    (*** The loop body, for 16 coefficients loaded as two 128-bit words ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK16_INPUT_SPLIT (ASSUME `i < 16`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK16_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(32 * i)))) s0`) THEN
    MP_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                 NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add (word_add a (word(32 * i)))
                                        (word 16))) s0`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--30) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s30 = x`) o
             concl))) THEN
    RULE_ASSUM_TAC(fun th ->
      if free_in `bytes16` (concl th) && not(is_forall(concl th))
      then CONV_RULE ADDR_NORM_CONV th else th) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) =
        0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK16_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invntt_scale_c; INVNTT_SCALE_MONTRED];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `invntt_scale_c` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
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
    "x27_init",`X27`; "x28_init",`X28`; "x29_init",`X29`] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The scaling loop ***)

  MP_TAC(SPECL [`a:int64`; `x:num->int16`; `pc:num`] INVNTT_SCALE) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC "s1" THEN

  (*** The prologue, saving the registers, and the constants ***)

  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [n] THEN
    MLKEM_NATIVE_ADRP_TAC) (2--21) THEN
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
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("X8",_)),_)),_) ->
      REWRITE_RULE[GSYM WORD_ADD] th
  | _ -> th) THEN

  (*** The seven layers ***)

  MP_TAC(SPECL [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`; `invntt_scale_c x`]
         INVNTT_LAYERS) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC "s22" THEN

  (*** Restoring the registers and returning ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC (23--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INVNTT_LAYERS_C_CORRECT]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

let INV_BLOCK_SAFE_THMS = map2
  (fun n tac -> prove(el n INVNTT_BLOCK_SAFE_STMTS, tac))
  (0--6)
  [INV_SBLOCK_SAFE_TAC 0; INV_SBLOCK_SAFE_TAC 1; INV_VBLOCK_SAFE_TAC 2;
   INV_VBLOCK_SAFE_TAC 3; INV_VBLOCK_SAFE_TAC 4; INV_VBLOCK_SAFE_TAC 5;
   INV_VBLOCK_SAFE_TAC 6];;

let INV_LAYER_SAFE_THMS = map
  (fun n -> prove(el n INVNTT_LAYER_SAFE_STMTS, INV_LAYER_SAFE_TAC n))
  (0--6);;

let INVNTT_SCALE_SAFE = prove
 (INVNTT_SCALE_SAFE_STMT,
  INVNTT_SCALE_SAFE_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN INV_SAFE_TOP_TAC);;
