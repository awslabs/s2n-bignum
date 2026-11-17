(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The generation of the ML-KEM matrix with hash jobs and noise in the spare *)
(* lanes of the x4 permutation (arm/mlkem_native2/mlkem_gen_matrix.S) in the *)
(* image: the code and the parts of the proofs of its correctness for the    *)
(* configurations that the API uses, the matrix polynomials as SampleNTT of  *)
(* their seeds, the digests of the hash jobs as SHA3-256 or SHAKE256, and    *)
(* the noise polynomials as the coefficients of SamplePolyCBD_2 of the PRF.  *)
(* The theorems are in mlkem_gen_matrix_k2.ml, mlkem_gen_matrix_k3.ml and    *)
(* mlkem_gen_matrix_k4.ml, one file for each k.                              *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_matrix.ml";;
needs "arm/proofs/mlkem_getnoise.ml";;

(* ------------------------------------------------------------------------- *)
(* The code, and the points in it used below by their labels in the source   *)
(* (the offsets in the stack frame are those of its #defines).               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GEN_MATRIX_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem_gen_matrix"];;

let gm_pc label off = layout ("mlkem_gen_matrix_" ^ label) + off;;

let gm_pc_tm n = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral n);;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the Keccak state before returning, as one step: add x0,    *)
(* sp, #off; mov x1, #len; then stp xzr, xzr, [x0], #16 until x1 = 0, from   *)
(* start to stop (the loop at start + 8).                                    *)
(* ------------------------------------------------------------------------- *)

let gm_zero_tm start stop off len =
  let ns = mk_small_numeral in
  subst [ns start,`start:num`; ns stop,`stop:num`; ns off,`off:num`;
         ns len,`len:num`]
  `!stackpointer pc.
     nonoverlapping (word_add stackpointer (word off),len)
                    (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + start) /\
               read SP s = stackpointer)
          (\s. read PC s = word(pc + stop))
          (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add stackpointer (word off),
                                      len)])`;;

let GM_ZERO_TAC exec start stop off len =
  let n = len / 16 and ns = mk_small_numeral in
  let inv = subst [ns off,`off:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add stackpointer (word(off + 16 * i)) /\
          read X1 s = word(len - 16 * i)` in
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC (ns n) (mk_binop `(+):num->num->num` `pc:num`
                                  (ns(start + 8)))
    (mk_binop `(+):num->num->num` `pc:num` (ns stop)) inv THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    ARM_SIM_TAC exec (1--2) THEN CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (subst [ns len,`len:num`]
     `word_sub (word(len - 16 * i)) (word 16):int64 =
      word(len - 16 * (i + 1)) /\
      val(word(len - 16 * (i + 1)):int64) = len - 16 * (i + 1)`)
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns len) `16 * i`; `16`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE(subst [ns len,`len:num`; ns n,`n:num`]
          `i < n ==> 16 <= len - 16 * i`)] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC exec (1--3) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE(subst [ns len,`len:num`; ns n,`n:num`]
        `16 * (i + 1) < len <=> i + 1 < n`)] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      CONV_TAC WORD_RULE];
    ARM_SIM_TAC exec []];;

let GM_ZERO_END = prove
 (gm_zero_tm (gm_pc "end" 0) (gm_pc "end" 20) 96 800,
  GM_ZERO_TAC MLKEM_GEN_MATRIX_EXEC (gm_pc "end" 0) (gm_pc "end" 20) 96 800);;

(* ------------------------------------------------------------------------- *)
(* The rejection sampling of matrix polynomial e from the three blocks in    *)
(* the buffer of lane l, and of the further blocks squeezed from the lane    *)
(* while it has fewer than 256 coefficients, as one step from the samplepoly *)
(* macro to its end; the stack pointer of the function is stackpointer + 128 *)
(* here, below which the callees use 128 bytes.                              *)
(* ------------------------------------------------------------------------- *)

let samplepoly_inv m =
  subst [m,`m:num`]
  `\s. read SP s = word_add stackpointer (word 128) /\
       read X19 s = a /\ read X23 s = c /\
       read X27 s = word e /\ read X28 s = word l /\
       read X0 s = word(LENGTH(mlkem_rej_out b m)) /\
       read (memory :> bytes(word_add a (word(512 * e)),
                             2 * LENGTH(mlkem_rej_out b m))) s =
       num_of_wordlist(mlkem_rej_out b m) /\
       read (memory :> bytes(word_add stackpointer (word(224 + 200 * l)),200))
            s =
       val(keccak_squeeze m (A:1600 word)) /\
       read (memory :> bytes(word_add c (word 2560),4096)) s =
       num_of_wordlist mlkem_rej_uniform_table /\
       read (memory :> bytes(c,192)) s = num_of_wordlist round_constants`;;

let gm_samplepoly_tm =
  subst [mk_small_numeral(gm_pc "rejloop" 4),`pc0:num`;
         mk_small_numeral(gm_pc "rejloop" 116),`pc1:num`]
 `!b (A:1600 word) a c l e stackpointer pc.
     mlkem_samplentt_terminates b /\
     (!t. num_of_bytelist(list_of_seq (\j. shake128 b (168 * t + j)) 168) =
          val(keccak_squeeze (t + 1) A) MOD 2 EXP 1344) /\
     l < 4 /\ e < 16 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (stackpointer,3216))
         [(word pc,mlkem_native2_image_size);
          (word_add a (word(512 * e)),512); (c,6656)] /\
     ALL (nonoverlapping (word_add a (word(512 * e)),512))
         [(word pc,mlkem_native2_image_size); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + pc0) /\
               read SP s = word_add stackpointer (word 128) /\
               read X19 s = a /\ read X23 s = c /\
               read X27 s = word e /\ read X28 s = word l /\
               read (memory :> bytes(word_add stackpointer
                                      (word(1024 + 504 * l)),504)) s =
               num_of_bytelist(list_of_seq (shake128 b) 504) /\
               read (memory :> bytes(word_add stackpointer
                                      (word(224 + 200 * l)),200)) s =
               val(keccak_squeeze 3 A) /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants)
          (\s. read PC s = word(pc + pc1) /\
               !t. t < 256
                   ==> read (memory :> bytes16(word_add a
                                                 (word(512 * e + 2 * t)))) s =
                       iword(mlkem_sample_ntt b t))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X30] ,,
           MAYCHANGE [memory :> bytes(word_add a (word(512 * e)),512);
                      memory :> bytes(word_add stackpointer
                                       (word(224 + 200 * l)),200);
                      memory :> bytes(word_add stackpointer (word 3208),8);
                      memory :> bytes(stackpointer,128)])`;;

let MLKEM_GEN_MATRIX_SAMPLEPOLY = prove
 (gm_samplepoly_tm,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 504)) (word 896)):int64 =
    word_add stackpointer (word(1024 + 504 * l)) /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 200)) (word 96)):int64 =
    word_add stackpointer (word(224 + 200 * l)) /\
    word_shl (word e:int64) 9 = word(512 * e)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `l < 4` THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`; WORD_ADD_0;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 504)) (word 896)):int64 =
              word_add stackpointer (word(1024 + 504 * l))`;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 200)) (word 96)):int64 =
              word_add stackpointer (word(224 + 200 * l))`;
      ASSUME `word_shl (word e:int64) 9 = word(512 * e)`]) in
  ENSURES_SEQUENCE_TAC (gm_pc_tm(gm_pc "rejloop" 40)) (samplepoly_inv `3`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BUF_OUT)
     [`read X0 s`; `read X2 s`; `read X4 s`; `b:byte list`;
      `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`; `read SP s`;
      `read X30 s`] 10 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = mlkem_rej_blocks b - 3` THEN
  SUBGOAL_THEN `mlkem_rej_blocks b = 3 + N` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `mlkem_rej_blocks b = 3`)) THEN
      ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(mlkem_rej_out b 3) = 256`]) THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SAMPLEPOLY_POST THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ASSUME `LENGTH(mlkem_rej_out b 3) = 256`];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` (gm_pc_tm(gm_pc "rejloop" 48))
   (gm_pc_tm(gm_pc "rejloop" 40))
   (mk_abs(`t:num`,samplepoly_inv `3 + t`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The test, the first time ***)

    REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b 3)):int64) =
                  LENGTH(mlkem_rej_out b 3)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT];

    (*** The body: another block from the lane, and its fields ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * e)),
                      2 * LENGTH(mlkem_rej_out b (3 + t)))
                     (stackpointer:int64,3216)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--7) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(224 + 200 * l)):int64` 7 THEN
    RC_TAC `c:int64` 7 THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "sha3_keccak_f1600",sha3_keccak_f1600_mc,
      SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; `read X1 s`; `keccak_squeeze (3 + t) (A:1600 word)`;
      `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 8 THEN
    FROM_WBYTES_TAC 8 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (9--17) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(224 + 200 * l)),
                            168)) s17 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + t) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(224 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + t)
                                       (A:1600 word)))`;
                    `s17:armstate`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BLOCK_OUT)
     [`read X0 s`; `read X2 s`; `read X4 s`; `b:byte list`; `3 + t`;
      `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`; `read SP s`;
      `read X30 s`] 18 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [19] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + t + 1 = (3 + t) + 1`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze];

    (*** The test, the later times ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b (3 + t)) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b (3 + t))):int64) =
                  LENGTH(mlkem_rej_out b (3 + t))` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT];

    (*** The exit, with the 256 coefficients ***)

    SUBGOAL_THEN `LENGTH(mlkem_rej_out b (3 + N)) = 256` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `mlkem_rej_blocks b = 3 + N`)) THEN
      ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `LENGTH(mlkem_rej_out b (3 + N)) = 256`]) THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SAMPLEPOLY_POST THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ASSUME `LENGTH(mlkem_rej_out b (3 + N)) = 256`]]);;

(* ------------------------------------------------------------------------- *)
(* One block of hash job j (0 or 1) absorbed into its lane (2 or 3), as the  *)
(* absorbjob macro does it, as one step: a whole block of 136 bytes, or the  *)
(* last t < 136 bytes with the padding for the domain byte ds. The state of  *)
(* the lane is the sponge state after i blocks of the padded message, and    *)
(* the copy of the job (p, r, ds, out) on the stack at offset 2912 + 32 * j  *)
(* has the next byte and the number of bytes left. The instances are for the *)
(* lengths and domain bytes of H(ek) and J(z || c) in the API.               *)
(* ------------------------------------------------------------------------- *)

let GM_ABSORB_FULL_TAC lane ds =
  let lanetm = mk_comb(`word_add (sp:int64)`,
                       mk_comb(`word:num->int64`,mk_small_numeral lane)) in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (subst [mk_small_numeral ds,`ds:num`]
   `A = keccak_absorb 136 (keccak_padded 136 ds m) i`) THEN
  ABBREV_TAC
   `B = (num_of_bytelist m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
  SUBGOAL_THEN
   `val(word(LENGTH(m:byte list) - 136 * i):int64) = LENGTH m - 136 * i /\
    ~bit 63 (word(LENGTH(m:byte list) - 136 * i):int64) /\
    ~(LENGTH(m:byte list) - 136 * i < 136) /\
    136 <= LENGTH(m:byte list) - 136 * i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r /\ t ==> p /\ q /\ r /\ t`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `LENGTH(m:byte list) < 2 EXP 63` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[DIV_LT; ARITH_RULE `x < 2 EXP 63 ==> x - y < 2 EXP 63`;
               ASSUME `LENGTH(m:byte list) < 2 EXP 63`] THEN
      CONV_TAC NUM_REDUCE_CONV;
      UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** The lanes of the state after the block is XORed in ***)

  SUBGOAL_THEN
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word B)) (64 * j,64):int64 =
            if j < 17
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (136 * i + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `B:num`; `17`; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[ARITH_RULE `64 * 17 = 8 * 136`; MOD_LT_EQ; EXP_EQ_0;
                  ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC KECCAK_BLOCK_LANE THEN
    UNDISCH_TAC `j < 17` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the block in memory ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] o
    check (can (term_match [`sp:int64`]
      (subst [lanetm,`l:int64`]
        `read (memory :> bytes(l,200)) s = val(A:1600 word)`)) o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j < 17
        ==> read (memory :> bytes64(word_add inp (word(136 * i + 8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (136 * i + 8 * j))) MOD
                 2 EXP 64)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 17`; `136 * (i + 1) <= LENGTH(m:byte list)`] THEN
    ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC] THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (term_match [`inp:int64`]
            `read (memory :> bytes64 (word_add inp (word(n + k)))) s =
             (y:int64)`) (concl th)) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN

  (*** The XOR of the block into the lane, 17 words ***)

  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `~(LENGTH(m:byte list) - 136 * i < 136)`]) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (10--115) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `136 <= LENGTH(m:byte list) - 136 * i`]) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (116--117) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let gm_absorb_full_tm j ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 8 + 120 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 120),`pc1:num`;
         ns ds,`ds:num`]
  `!m inp i sp pc.
    LENGTH m < 2 EXP 63 /\ 136 * (i + 1) <= LENGTH m /\
    ALL (nonoverlapping (word_add sp (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    ALL (nonoverlapping (word_add sp (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    nonoverlapping (word_add sp (word lane),200) (word_add sp (word st),24)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + pc0) /\
          read SP s = sp /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * i)) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word(LENGTH m - 136 * i) /\
          read (memory :> bytes64(word_add sp (word st16))) s = word ds /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(word_add sp (word lane),200)) s =
          val(keccak_absorb 136 (keccak_padded 136 ds m) i))
     (\s. read PC s = word(pc + pc1) /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * (i + 1))) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word(LENGTH m - 136 * (i + 1)) /\
          read (memory :> bytes(word_add sp (word lane),200)) s =
          val(word_xor (keccak_absorb 136 (keccak_padded 136 ds m) i)
               (word((keccak_padded 136 ds m DIV 2 EXP (8 * 136 * i)) MOD
                     2 EXP (8 * 136)))))
     (MAYCHANGE [PC; X2; X3; X8; X9; X10; X11; X12; X13; X14; X15] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add sp (word st),16);
                 memory :> bytes(word_add sp (word lane),200)])`;;

let GM_ABSORB_FULL_PROOF_TAC j ds =
  GM_ABSORB_FULL_TAC (496 + 200 * j) ds THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    SUBGOAL_THEN
     `LENGTH(m:byte list) - 136 * i = (LENGTH m - 136 * (i + 1)) + 136`
    SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    SUBGOAL_THEN (subst [mk_small_numeral ds,`ds:num`]
     `(keccak_padded 136 ds m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136) =
      B`)
    SUBST1_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[keccak_padded] THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `B:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[]];;

let GM_ABSORB_FULL_0_6 = prove
 (gm_absorb_full_tm 0 6, GM_ABSORB_FULL_PROOF_TAC 0 6);;

let GM_ABSORB_FULL_1_6 = prove
 (gm_absorb_full_tm 1 6, GM_ABSORB_FULL_PROOF_TAC 1 6);;

let GM_ABSORB_FULL_1_31 = prove
 (gm_absorb_full_tm 1 31, GM_ABSORB_FULL_PROOF_TAC 1 31);;

let gm_absorb_last_tm j t ds =
  let lane = 496 + 200 * j and st = 2912 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 8 + 120 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 120),`pc1:num`;
         ns t,`t:num`; ns ds,`ds:num`]
  `!m inp q sp pc.
    LENGTH m = 136 * q + t /\ LENGTH m < 2 EXP 63 /\
    ALL (nonoverlapping (word_add sp (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    ALL (nonoverlapping (word_add sp (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    nonoverlapping (word_add sp (word lane),200) (word_add sp (word st),24)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + pc0) /\
          read SP s = sp /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * q)) /\
          read (memory :> bytes64(word_add sp (word st8))) s = word t /\
          read (memory :> bytes64(word_add sp (word st16))) s = word ds /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(word_add sp (word lane),200)) s =
          val(keccak_absorb 136 (keccak_padded 136 ds m) q))
     (\s. read PC s = word(pc + pc1) /\
          read (memory :> bytes64(word_add sp (word st))) s =
          word_add inp (word(136 * q + t)) /\
          read (memory :> bytes64(word_add sp (word st8))) s =
          word 18446744073709551615 /\
          read (memory :> bytes(word_add sp (word lane),200)) s =
          val(word_xor (keccak_absorb 136 (keccak_padded 136 ds m) q)
               (word((keccak_padded 136 ds m DIV 2 EXP (8 * 136 * q)) MOD
                     2 EXP (8 * 136)))))
     (MAYCHANGE [PC; X2; X3; X8; X9; X10; X11; X12; X13; X14; X15] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add sp (word st),16);
                 memory :> bytes(word_add sp (word lane),200)])`;;

let BYTE_XOR_CONST_ZX_RULE c =
  let tm = subst [mk_small_numeral c,`c:num`]
   `!x:byte.
      word_zx(word_zx(word_zx
       (word_xor (word_zx(word_zx(word_zx x:int32):int64):int32)
                 (word c)):int64):int32):byte = word_xor x (word c)` in
  prove(tm,CONV_TAC WORD_BLAST);;

let GM_ABSORB_LAST_PROOF_TAC j t ds =
  let w = t / 8 in
  let lanetm = mk_comb(`word_add (sp:int64)`,
                       mk_comb(`word:num->int64`,
                               mk_small_numeral(496 + 200 * j))) in
  let nsteps1 = 13 + 6 * w in
  let tn = mk_small_numeral t and wn = mk_small_numeral w
  and dsn = mk_small_numeral ds in
  let xor_ds = BYTE_XOR_CONST_ZX_RULE ds
  and xor_80 = BYTE_XOR_CONST_ZX_RULE 128 in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (subst [dsn,`ds:num`]
   `A = keccak_absorb 136 (keccak_padded 136 ds m) q`) THEN
  ABBREV_TAC (subst [tn,`t:num`]
   `L = (num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * t)`) THEN

  (*** The lanes of the state after the last words are XORed in ***)

  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word L)) (64 * j,64):int64 =
            if j < w
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (136 * q + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `L:num`; wn; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) DIV_MOD_EXP_LOW o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the message ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] o
    check (can (term_match [`sp:int64`]
      (subst [lanetm,`l:int64`]
        `read (memory :> bytes(l,200)) s = val(A:1600 word)`)) o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < w
        ==> read (memory :> bytes64(word_add inp (word(136 * q + 8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (136 * q + 8 * j))) MOD
                 2 EXP 64)`)
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC] THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (term_match [`inp:int64`]
            `read (memory :> bytes64 (word_add inp (word(n + k)))) s =
             (y:int64)`) (concl th)) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN

  (*** The XOR of the last words into the lane ***)

  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps1) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; mk_var("s"^string_of_int nsteps1,`:armstate`),
           `s:armstate`]
    `read (memory :> wbytes l) s = word_xor (A:1600 word) (word L)`)
  MP_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `L:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The domain byte at byte t ***)

  REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC tn th) (ARITH_RULE(subst [tn,`t:num`] `t < 200`)))) THEN
    ASSUME_TAC(RESTRICT_RULE tn th)) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+1)--(nsteps1+3)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[xor_ds]) THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(496 + 200 * j),`l:num`;
           mk_var("s"^string_of_int(nsteps1+3),`:armstate`),
           `s:armstate`; tn,`t:num`; dsn,`ds:num`]
    `!j. j < 200
         ==> read (memory :> bytes8(word_add sp (word(l + j)))) s =
             word_subword (word_xor (word_xor (A:1600 word) (word L))
                                    (word(2 EXP (8 * t) * ds))) (8 * j,8)`)
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE(subst [dsn,`ds:num`] `ds < 256`);
                 ARITH_RULE(subst [tn,`t:num`] `t < 200`)] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The final bit at byte 135 ***)

  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `135` th) (ARITH_RULE `135 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `135` th)) THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+4)--(nsteps1+6)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[xor_80]) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; mk_var("s"^string_of_int(nsteps1+6),`:armstate`),
           `s:armstate`; tn,`t:num`; dsn,`ds:num`]
    `read (memory :> bytes(l,200)) s =
     val(word_xor (word_xor (word_xor (A:1600 word) (word L))
                            (word(2 EXP (8 * t) * ds)))
                  (word(2 EXP (8 * 135) * 128)))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 135 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+7)--(nsteps1+9)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`136`; dsn; `m:byte list`] KECCAK_LAST_BLOCK_XOR) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN (subst [tn,`t:num`]
   `(136 * q + t) DIV 136 = q /\ (136 * q + t) MOD 136 = t`)
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC tn THEN ARITH_TAC;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `num_of_bytelist m DIV 2 EXP (8 * 136 * q) = L` SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    MP_TAC(ISPEC `m:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
    MATCH_MP_TAC(ARITH_RULE `a = b ==> x < a ==> x < b`) THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

let GM_ABSORB_LAST_0_120 = prove
 (gm_absorb_last_tm 0 120 6, GM_ABSORB_LAST_PROOF_TAC 0 120 6);;

let GM_ABSORB_LAST_1_120 = prove
 (gm_absorb_last_tm 1 120 31, GM_ABSORB_LAST_PROOF_TAC 1 120 31);;

let GM_ABSORB_LAST_0_96 = prove
 (gm_absorb_last_tm 0 96 6, GM_ABSORB_LAST_PROOF_TAC 0 96 6);;

let GM_ABSORB_LAST_1_96 = prove
 (gm_absorb_last_tm 1 96 6, GM_ABSORB_LAST_PROOF_TAC 1 96 6);;

let GM_ABSORB_LAST_1_32 = prove
 (gm_absorb_last_tm 1 32 31, GM_ABSORB_LAST_PROOF_TAC 1 32 31);;

let GM_ABSORB_LAST_0_72 = prove
 (gm_absorb_last_tm 0 72 6, GM_ABSORB_LAST_PROOF_TAC 0 72 6);;

let GM_ABSORB_LAST_1_72 = prove
 (gm_absorb_last_tm 1 72 6, GM_ABSORB_LAST_PROOF_TAC 1 72 6);;

let GM_ABSORB_LAST_1_104 = prove
 (gm_absorb_last_tm 1 104 31, GM_ABSORB_LAST_PROOF_TAC 1 104 31);;

(* ------------------------------------------------------------------------- *)
(* Addresses in the frame for the stack pointer of the function at           *)
(* stackpointer + spoff (lane l, the buffer of lane l, offset off), facts    *)
(* about memory at a state, and keccak_squeeze 1, 2 and 3 as permutations.   *)
(* ------------------------------------------------------------------------- *)

let gm_lane_addr spoff l =
  addr_plus `stackpointer:int64` (spoff + 96 + 200 * l);;

let gm_buf_addr spoff l =
  addr_plus `stackpointer:int64` (spoff + 896 + 504 * l);;

let gm_st spoff off = addr_plus `stackpointer:int64` (spoff + off);;

let bytes64_fact a k gl =
  asm_with_lhs (vsubst [a,`a:int64`; state_of k,`s:armstate`]
                 `read (memory :> bytes64 a) s`) gl;;

let bytes128_fact a k gl =
  asm_with_lhs (vsubst [a,`a:int64`; state_of k,`s:armstate`]
                 `read (memory :> bytes128 a) s`) gl;;

let dest_bytes_read tm =
  let r,s = dest_comb tm in
  let _,c = dest_comb r in
  let _,b = dest_comb c in
  let bc,an = dest_comb b in
  if fst(dest_const bc) <> "bytes" then failwith "dest_bytes_read" else
  let a,n = dest_pair an in a,n,s;;

let word_base tm =
  try let f,args = strip_comb tm in
      if fst(dest_const f) = "word_add" then hd args else tm
  with Failure _ -> tm;;

let KECCAK_SQUEEZE_NUM_CONV =
  let th1 = prove(`!S. keccak_squeeze 1 S = keccak_f1600 S`,
              REWRITE_TAC[num_CONV `1`; keccak_squeeze])
  and th2 = prove(`!S. keccak_squeeze 2 S = keccak_f1600(keccak_f1600 S)`,
              REWRITE_TAC[num_CONV `2`; num_CONV `1`; keccak_squeeze])
  and th3 = prove(`!S. keccak_squeeze 3 S =
                       keccak_f1600(keccak_f1600(keccak_f1600 S))`,
              REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`;
                          keccak_squeeze]) in
  REWRITE_CONV[th1; th2; th3];;

(* ------------------------------------------------------------------------- *)
(* The facts added on the way, by the PC offset where they are needed: the   *)
(* 16-byte words of the job and noise structures before they are copied and  *)
(* the 8-byte fields of the copies after; lanes 2 and 3 as zero after the    *)
(* zeroing loop; the state of a matrix polynomial's lane after initlane and  *)
(* of a noise polynomial's lane after initnoise; the loads of a lane copied  *)
(* to the buffer and the block stored; the first 32 bytes of a job's lane    *)
(* and its digest once copied out.                                           *)
(* ------------------------------------------------------------------------- *)

let STRUCT_LOAD128_TAC reg offs k gl =
  let b = find_read_fact reg k gl and sv = state_of k in
  let fact a =
    try bytes64_fact a k gl with Failure _ ->
    REFL(vsubst [a,`a:int64`; sv,`s:armstate`]
          `read (memory :> bytes64 a) s`) in
  let mk off =
    let a = addr_plus b off in
    let thx = fact a and thy = fact (addr_plus b (off+8)) in
    let th = SPECL [a; rand(concl thx); rand(concl thy); sv]
                   READ_MEMORY_BYTES128_OF_BYTES64S in
    let th' = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                NORMALIZE_RELATIVE_ADDRESS_CONV)) th in
    MP th' (CONJ thx thy) in
  MAP_EVERY (ASSUME_TAC o mk) offs gl;;

let STRUCT_SPLIT128_TAC base offs k gl =
  let mk off =
    try let th = bytes128_fact (addr_plus base off) k gl in
        let th' = MATCH_MP READ_MEMORY_BYTES64S_OF_BYTES128 th in
        let th'' = CONV_RULE(ONCE_DEPTH_CONV
                     NORMALIZE_RELATIVE_ADDRESS_CONV)
                    (REWRITE_RULE[WORD_JOIN_64_PARTS] th') in
        map (CONV_RULE(RAND_CONV(TRY_CONV WORD_REDUCE_CONV)))
            (CONJUNCTS th'')
    with Failure _ -> [] in
  let ths = flat(map mk offs) in
  if ths = [] then failwith "STRUCT_SPLIT128_TAC" else
  MAP_EVERY ASSUME_TAC ths gl;;

let GM_ZERO_LANES_TAC spoff k =
  let sv = state_of k in
  let mk l =
    let a = gm_lane_addr spoff l in
    let tm = vsubst [a,`a:int64`; sv,`s:armstate`]
               `read (memory :> bytes(a,200)) s = 0` in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC(LAND_CONV(BYTES_PIECES_CONV (replicate 8 25))) THEN
      ASM_REWRITE_TAC[VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      ALL_TAC] in
  mk 2 THEN mk 3;;

let GM_MATRIX_LANE_TAC spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `X28` k gl)) in
  let a = gm_lane_addr spoff l and sv = state_of k in
  let th32 = asm_with_lhs (vsubst [addr_plus a 32,`a:int64`; sv,`s:armstate`]
                `read (memory :> bytes64 a) s`) gl in
  let v = dest_small_numeral(rand(rand(concl th32))) - 2031616 in
  let x = v mod 256 and y = v / 256 in
  (MP_TAC(SPECL [a; `rho:byte list`; mk_small_numeral x; mk_small_numeral y;
                 sv]
                MLKEM_MATRIX_LANE) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC]) gl;;

let GM_NOISE_LANE_TAC spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `X28` k gl)) in
  let a = gm_lane_addr spoff l and sv = state_of k in
  let v = dest_small_numeral
            (rand(rand(concl(bytes64_fact (addr_plus a 32) k gl)))) in
  let y = mk_comb(`word:num->int64`,mk_small_numeral(v - 7936)) in
  (MP_TAC(SPECL [a; `seed:byte list`; y; sv] MLKEM_NOISE_LANE) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
     ASM_REWRITE_TAC[] THEN NO_TAC;
     REWRITE_TAC[WORD_ZX_BYTE_WORD; READ_MEMORY_WBYTES_1600] THEN
     DISCH_TAC]) gl;;

let GM_COPY_LOAD_TAC k gl =
  let a = find_read_fact `X1` k gl and sv = state_of k in
  let th200 = bytes_fact a 200 k gl in
  let x = rand(concl th200) in
  let mk lemma len off =
    let th = SPECL [a; `200`; x; mk_small_numeral off; sv] lemma in
    let th' = MP th (CONJ th200 (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral off)
                 (mk_small_numeral len)) `200`))) in
    CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
              RAND_CONV(NUM_REDUCE_CONV)) (REWRITE_RULE[WORD_ADD_0] th') in
  let ths = map (mk READ_MEMORY_BYTES128_OF_NUM 16) (0--9 |> map (( * ) 16)) @
            [mk READ_MEMORY_BYTES64_OF_NUM 8 160] in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE[DIV_1]) ths gl;;

(*** After the copy of the first 168 bytes of a lane to its buffer, the
 *** buffer as one number, and the facts about the pieces loaded and stored,
 *** which are no longer needed and whose terms (with numerals of hundreds
 *** of digits) every later step would otherwise carry, dropped
 ***)

let GM_COPY_STORE_TAC k gl =
  let buf = find_read_fact `X0` k gl and a = find_read_fact `X1` k gl in
  let x = rand(concl(bytes_fact a 200 k gl)) in
  let sv = state_of k in
  let lhs64 = vsubst [addr_plus buf 160,`a:int64`; sv,`s:armstate`]
                `read (memory :> bytes64 a) s` in
  let piece t =
    match t with
      Comb(Const("word",_),Comb(Comb(Const("MOD",_),
           Comb(Comb(Const("DIV",_),y),_)),_)) -> y = x
    | Comb(Const("word",_),Comb(Comb(Const("MOD",_),y),_)) -> y = x
    | _ -> false in
  let memread t =
    try name_of(fst(strip_comb(rand(rator t)))) = ":>"
    with Failure _ -> false in
  (RULE_ASSUM_TAC(fun th ->
     if (try lhand(concl th) = lhs64 with Failure _ -> false)
     then CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
                   (REWRITE_RULE[WORD_ZX_64_128] th)
     else th) THEN
   MP_TAC(SPECL [buf; x; sv] READ_MEMORY_BYTES_168_OF_PIECES) THEN
   ANTS_TAC THENL
    [CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     REWRITE_TAC[DIV_1; WORD_ADD_0] THEN ASM_REWRITE_TAC[];
     DISCH_TAC THEN
     DISCARD_ASSUMPTIONS_TAC (fun th ->
       let c = concl th in is_eq c && piece(rand c) && memread(lhand c))])
  gl;;

let GM_LANE128_TAC reg k gl =
  let a = find_read_fact reg k gl and sv = state_of k in
  let th200 = bytes_fact a 200 k gl in
  let x = rand(concl th200) in
  let mk off =
    let th = SPECL [a; `200`; x; mk_small_numeral off; sv]
                   READ_MEMORY_BYTES128_OF_NUM in
    let th' = MP th (CONJ th200 (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral off) `16`)
               `200`))) in
    CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
              RAND_CONV(NUM_REDUCE_CONV)) (REWRITE_RULE[WORD_ADD_0] th') in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE[DIV_1] o mk) [0; 16] gl;;

let GM_DIGEST_TAC k (asl,w as gl) =
  let out = find_read_fact `X13` k gl and lane = find_read_fact `X12` k gl in
  let sv = state_of k in
  let x = rand(concl(bytes_fact lane 200 k gl)) in
  let st = rand x in
  let p = rand(rator(lhand(rand st))) in
  let m = rand p and ds = dest_small_numeral(rand(rator p)) in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,m)
    with Failure _ -> false) gl in
  let dlemma = if ds = 6 then SHA3_256_DIGEST else SHAKE256_32_DIGEST in
  let dth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_DIV_CONV))
             (REWRITE_RULE[lenth] (SPEC m dlemma)) in
  let th = SPECL [out; x; sv] READ_MEMORY_BYTES_32_OF_BYTES128S in
  let th' = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
              NORMALIZE_RELATIVE_ADDRESS_CONV THENC
              DEPTH_CONV NUM_EXP_CONV)) th in
  (MP_TAC th' THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN NO_TAC;
     REWRITE_TAC[GSYM dth] THEN DISCH_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* The steps taken as one: the rejection sampling of a matrix polynomial     *)
(* (with the termination of SampleNTT for its seed from the hypothesis of    *)
(* the theorem), a block of a hash job by the lemmas above (or the code if   *)
(* the job is inactive), with the state of its lane first put as             *)
(* keccak_absorb 136 P i, and mlkem_getnoise for the noise polynomials left; *)
(* and the results of the CBD and of mlkem_getnoise in the form of the       *)
(* theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

let GM_SAMPLEPOLY_TAC exec spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `X28` k gl))
  and e = dest_small_numeral(rand(find_read_fact `X27` k gl)) in
  let lane = gm_lane_addr spoff l and buf = gm_buf_addr spoff l in
  let sv = state_of k in
  let st = rand(rand(concl(bytes_fact lane 200 k gl))) in
  let aa = rand(rand(rand st)) in
  let y = rand aa and x = rand(rator aa) and rho = rand(rator(rator aa)) in
  let b = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,rho),
                  mk_list([x;y],`:byte`)) in
  let bufth = MP_TAC(SPECL [rho; x; y; buf; sv] MLKEM_MATRIX_BUFFER) THEN
              CONV_TAC(LAND_CONV(KECCAK_SQUEEZE_NUM_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
              ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let spth = SPECL [rho; x; y] MLKEM_MATRIX_SPONGE_BLOCK in
  let lemma = SPECL [b; aa; `a:int64`; `c:int64`; mk_small_numeral l;
                     mk_small_numeral e;
                     addr_plus `stackpointer:int64` (spoff - 128); `pc:num`]
                    MLKEM_GEN_MATRIX_SAMPLEPOLY in
  let lemma' = CONV_RULE(ONCE_DEPTH_CONV KECCAK_SQUEEZE_NUM_CONV) lemma in
  let tth = find_asm (fun c -> is_forall c && can (find_term (fun t ->
              is_const t && name_of t = "mlkem_samplentt_terminates")) c) gl in
  let xn = dest_small_numeral(rand x) and yn = dest_small_numeral(rand y) in
  let term_th =
    let try_ij i j =
      let th = SPECL [mk_small_numeral i; mk_small_numeral j] tth in
      let th' = MP th (EQT_ELIM((NUM_REDUCE_CONV THENC REWRITE_CONV[])
                                   (lhand(concl th)))) in
      if rand(concl th') = b then th' else failwith "order" in
    try try_ij yn xn with Failure _ -> try_ij xn yn in
  (ASSUME_TAC term_th THEN bufth THEN
   MP_TAC spth THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC lemma' THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(fun th ->
     ARM_SUBROUTINE_SIM_TAC
      (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1))) gl;;

let GM_BLOCK_RULE = REWRITE_RULE[GSYM keccak_absorb_block];;

let gm_absorb_full_ths =
  map (fun (j,ds,th) -> (j,ds),GM_BLOCK_RULE th)
   [0,6,GM_ABSORB_FULL_0_6; 1,6,GM_ABSORB_FULL_1_6; 1,31,GM_ABSORB_FULL_1_31];;

let gm_absorb_last_ths =
  map (fun (j,t,th) -> (j,t),GM_BLOCK_RULE th)
   [0,120,GM_ABSORB_LAST_0_120; 1,120,GM_ABSORB_LAST_1_120;
    0,96,GM_ABSORB_LAST_0_96; 1,96,GM_ABSORB_LAST_1_96;
    1,32,GM_ABSORB_LAST_1_32; 0,72,GM_ABSORB_LAST_0_72;
    1,72,GM_ABSORB_LAST_1_72; 1,104,GM_ABSORB_LAST_1_104];;

let GM_ABSORB_CALL_TAC exec spoff j k (asl,w as gl) =
  let sv = state_of k in
  let st = gm_st spoff (2912 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then ARM_STEPS_TAC exec [k+1] gl else
  let ds = dest_small_numeral(rand dsv) in
  let pv = rd st and r = dest_small_numeral(rand(rd (addr_plus st 8))) in
  let inp = word_base pv in
  let mth = find_asm (fun c ->
    try let a,n,s = dest_bytes_read(lhand c) in
        a = inp && s = sv && is_numeral n &&
        fst(dest_const(rator(rand c))) = "num_of_bytelist"
    with Failure _ -> false) gl in
  let _,ln,_ = dest_bytes_read(lhand(concl mth)) in
  let len = dest_small_numeral ln and m = rand(rand(concl mth)) in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,m)
    with Failure _ -> false) gl in
  let lane = gm_lane_addr spoff (2 + j) in
  let p = list_mk_comb(`keccak_padded`,[`136`; mk_small_numeral ds; m]) in
  let i = if r >= 136 then (len - r) / 136 else len / 136 in
  let ka = list_mk_comb(`keccak_absorb`,[`136`; p; mk_small_numeral i]) in
  let lane_tac =
    if i = 0 then
      FIRST_X_ASSUM(fun th ->
        if concl th = vsubst [lane,`a:int64`; sv,`s:armstate`]
                       `read (memory :> bytes(a,200)) s = 0`
        then ASSUME_TAC(TRANS th (SYM(REWRITE_CONV[keccak_absorb; VAL_WORD_0]
                                       (mk_comb(`val:1600 word->num`,ka)))))
        else NO_TAC)
    else
      FIRST_X_ASSUM(fun th ->
        if lhand(concl th) = vsubst [lane,`a:int64`; sv,`s:armstate`]
                               `read (memory :> bytes(a,200)) s`
        then ASSUME_TAC(CONV_RULE(RAND_CONV
               (REWRITE_CONV[KECCAK_ABSORB_BLOCK_STEP] THENC
                NUM_REDUCE_CONV)) th)
        else NO_TAC) in
  let sp = find_read_fact `SP` k gl in
  let lemma =
    if r >= 136 then
      SPECL [m; inp; mk_small_numeral i; sp; `pc:num`]
            (assoc (j,ds) gm_absorb_full_ths)
    else
      SPECL [m; inp; mk_small_numeral i; sp; `pc:num`]
            (assoc (j,r) gm_absorb_last_ths) in
  let lemma' = REWRITE_RULE[WORD_ADD_0]
                (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[lenth] lemma)) in
  let lemma'' = CONV_RULE(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV) lemma' in
  (lane_tac THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,lemma'') [] (k+1))
  gl;;

let GM_GETNOISE_CALL_TAC exec k gl =
  let v reg = dest_small_numeral(rand(find_read_fact reg k gl)) in
  let ns = mk_small_numeral in
  let th = SPECL [find_read_fact `X0` k gl; find_read_fact `X1` k gl;
                  `seed:byte list`; ns(v `X2`); ns(v `X3`); ns(v `X4`);
                  ns(v `X5`); find_read_fact `X6` k gl; `pc:num`;
                  find_read_fact `SP` k gl; find_read_fact `X30` k gl]
                 MLKEM_GETNOISE_SUBROUTINE_CORRECT in
  let th' = CONV_RULE(LAND_CONV(LAND_CONV(REWRITE_CONV[ARITH_EQ]))) th in
  let th'' = REWRITE_RULE[COND_ID] (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[] th')) in
  let rc = find_read_fact `X6` k gl in
  (RC_TAC rc k THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th'') [] (k+1)) gl;;

let GM_NORMALIZE_OUT_TAC k =
  let sv = state_of k in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && free_in sv c &&
       can (find_term (fun t -> is_const t && name_of t = "mlkem_cbd_coeff")) c
    then CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
          (REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC;
                        ADD_CLAUSES] th)
    else th);;

let GM_SPLIT_NOISE_TAC k =
  let sv = state_of k in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && free_in sv c && length(fst(strip_forall c)) = 2 &&
       can (find_term (fun t -> is_const t && name_of t = "mlkem_prf")) c
    then
      let th1 = CONV_RULE EXPAND_CASES_CONV
                 (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] th) in
      MAP_EVERY ASSUME_TAC (CONJUNCTS th1)
    else NO_TAC) THEN
  GM_NORMALIZE_OUT_TAC k;;

(* ------------------------------------------------------------------------- *)
(* The hooks by PC offset, for the stack pointer of the function at          *)
(* stackpointer + spoff (spoff = 224 for the x4 permutation below it, or     *)
(* 1952 when mlkem_getnoise is called).                                      *)
(* ------------------------------------------------------------------------- *)

let gm_derive spoff =
  [gm_pc "nonoise" (-8), STRUCT_LOAD128_TAC `X5` [0; 16];
   gm_pc "nonoise" 0,
     (fun k -> TRY(STRUCT_SPLIT128_TAC (gm_st spoff 2976) [0; 16] k));
   gm_pc "nonoise" 8, STRUCT_LOAD128_TAC `X4` [0; 16; 32; 48];
   gm_pc "jobsdone" 0,
     (fun k -> TRY(STRUCT_SPLIT128_TAC (gm_st spoff 2912) [0; 16; 32; 48] k));
   gm_pc "outer" 0, (fun k -> TRY(GM_ZERO_LANES_TAC spoff k));
   gm_pc "initloop" 108, GM_MATRIX_LANE_TAC spoff;
   gm_pc "noiseinit_next" 0, (fun k -> TRY(GM_NOISE_LANE_TAC spoff k));
   gm_pc "nohash1" 44, GM_LANE128_TAC `X12`;
   gm_pc "nohash1" 52, GM_DIGEST_TAC;
   gm_pc "nohash1" 80, GM_LANE128_TAC `X12`;
   gm_pc "nohash1" 88, GM_DIGEST_TAC;
   gm_pc "copyloop" 0, GM_COPY_LOAD_TAC;
   gm_pc "copyloop" 48, GM_COPY_STORE_TAC];;

let gm_calls spoff =
  let exec = MLKEM_GEN_MATRIX_EXEC in
  [gm_pc "end" 0,
     (fun k -> ARM_SUBROUTINE_SIM_TAC
       (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,GM_ZERO_END)
       [`read SP s`; `pc:num`] (k+1));
   layout "sha3_keccak4_f1600_alt2", KECCAK4_CALL_TAC exec;
   gm_pc "rejloop" 4, GM_SAMPLEPOLY_TAC exec spoff;
   gm_pc "noiseinit_done" 8, GM_ABSORB_CALL_TAC exec spoff 0;
   gm_pc "noiseinit_done" 128, GM_ABSORB_CALL_TAC exec spoff 1;
   layout "mlkem_cbd2",
     (fun k -> CBD2_CALL_TAC exec k THEN GM_NORMALIZE_OUT_TAC (k+1));
   layout "mlkem_getnoise",
     (fun k -> GM_GETNOISE_CALL_TAC exec k THEN GM_SPLIT_NOISE_TAC (k+1))];;

(* ------------------------------------------------------------------------- *)
(* The proof of an instance with stack size n: the setup (the 16-byte words  *)
(* of rho and of the noise seed), the simulation, and at the end each case   *)
(* of a polynomial of the results as an assumption.                          *)
(* ------------------------------------------------------------------------- *)

let GM_BYTES128_OF_32_TAC p v =
  MP_TAC(SPECL [p; `32`; v; `0`; `s0:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  MP_TAC(SPECL [p; `32`; v; `16`; `s0:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 16 <= 32 /\ 16 + 16 <= 32`; WORD_ADD_0;
                  MULT_CLAUSES; EXP; DIV_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT DISCH_TAC;;

let GM_SETUP_TAC n =
  REPEAT(W(fun (_,w) ->
    let v = fst(dest_forall w) in
    if fst(dest_var v) = "stackpointer" then NO_TAC else X_GEN_TAC v)) THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  GM_BYTES128_OF_32_TAC `rhop:int64` `num_of_bytelist(rho:byte list)` THEN
  W(fun (asl,w) ->
    if can (find_term ((=) `sigma:int64`)) w ||
       exists (fun (_,th) -> free_in `sigma:int64` (concl th)) asl
    then GM_BYTES128_OF_32_TAC `sigma:int64` `num_of_bytelist(seed:byte list)`
    else ALL_TAC);;

let GM_EXPAND_OUTER_TAC (asl,w as gl) =
  let ok = try let _,b = dest_forall w in
               let _,c = dest_imp b in is_forall c
           with Failure _ -> false in
  if ok then (CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC) gl
  else NO_TAC gl;;

let GM_FINALE_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GM_EXPAND_OUTER_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[ADD_CLAUSES]);;

let GM_INSTANCE_TAC n =
  GM_SETUP_TAC n THEN
  NATIVE2_RUN_TAC MLKEM_GEN_MATRIX_EXEC (gm_derive(n - 3088))
    (gm_calls(n - 3088)) 0 THEN
  GM_FINALE_TAC;;
