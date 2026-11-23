(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The generation of the ML-KEM matrix with hash jobs and noise in the spare *)
(* lanes of the x4 permutation (x86/mlkem_native/asm/mlkem_gen_matrix.S) in  *)
(* the image: the code and the parts of the proofs of its correctness for    *)
(* the configurations that the API uses, the matrix polynomials as SampleNTT *)
(* of their seeds in the order of the x86 kernels, the digests of the hash   *)
(* jobs as SHA3-256 or SHAKE256, and the noise polynomials as the            *)
(* coefficients of SamplePolyCBD_2 of the PRF. The theorems are in           *)
(* mlkem_gen_matrix_k2.ml, mlkem_gen_matrix_k3.ml and                        *)
(* mlkem_gen_matrix_k4.ml, one file for each k.                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_matrix.ml";;
needs "x86/proofs/mlkem_native/asm/mlkem_getnoise.ml";;

(* ------------------------------------------------------------------------- *)
(* The code, and the points in it used below by their labels in the source   *)
(* (the offsets in the stack frame are those of its #defines). The frame of  *)
(* 3032 bytes is below the six saved registers, and the constants block is   *)
(* the seventh argument, on the stack above the return address.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GEN_MATRIX_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem_gen_matrix"];;

let gm_pc label off = layout ("mlkem_gen_matrix_" ^ label) + off;;

let gm_pc_tm n = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral n);;

install_layout ["mlkem_gen_matrix_zeroloop",gm_pc "end" 12;
                "mlkem_gen_matrix_zerodone",gm_pc "end" 46];;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the Keccak state before returning, as one step: four       *)
(* 32-byte stores of zero six times and then one more, from the label end to *)
(* the vzeroupper.                                                           *)
(* ------------------------------------------------------------------------- *)

let GM_ZERO_COUNTER = prove
 (`!i. i < 6
       ==> ((~(val(word_zx(word(6 - i):int64):int32) = val(word 1:int32)) <=>
             i + 1 < 6) /\
            word_zx(word_sub (word_zx(word(6 - i):int64):int32) (word 1))
            :int64 = word(6 - (i + 1)))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let GM_ZERO_END = prove
 (`!stackpointer pc.
     nonoverlapping (stackpointer,800) (word pc,mlkem_native2_image_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem_gen_matrix_end) /\
               read RSP s = stackpointer)
          (\s. read RIP s = word(pc + mlkem_gen_matrix_zerodone))
          (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE [ZMM0] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(stackpointer,800)])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `6` `pc + mlkem_gen_matrix_zeroloop`
   (gm_pc_tm(gm_pc "zeroloop" 30))
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(6 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X86_SIM_TAC MLKEM_GEN_MATRIX_EXEC (1--3) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC MLKEM_GEN_MATRIX_EXEC (1--7) THEN
    ASM_SIMP_TAC[GM_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE];
    X86_SIM_TAC MLKEM_GEN_MATRIX_EXEC [1]]);;

(* ------------------------------------------------------------------------- *)
(* The rejection sampling of matrix polynomial idx + l from the three blocks *)
(* in the buffer of lane l, and of the further blocks squeezed from the lane *)
(* with the x1 permutation while it has fewer than 256 coefficients, then    *)
(* their permutation by mlkem_unpack into the order of the x86 kernels, as   *)
(* one step from the samplepoly macro to its end; the stack pointer of the   *)
(* function is stackpointer + 40 here, below which the callees use 40 bytes. *)
(* ------------------------------------------------------------------------- *)

let samplepoly_inv m =
  subst [m,`m:num`]
  `\s. read RSP s = word_add stackpointer (word 40) /\
       read RBX s = a /\ read R15 s = c /\
       read R12 s = word idx /\ read R14 s = word l /\
       read RAX s = word(LENGTH(mlkem_rej_out b m)) /\
       read (memory :> bytes(word_add a (word(512 * (idx + l))),
                             2 * LENGTH(mlkem_rej_out b m))) s =
       num_of_wordlist(mlkem_rej_out b m) /\
       read (memory :> bytes(word_add stackpointer (word(40 + 200 * l)),200))
            s =
       val(keccak_squeeze m (A:1600 word)) /\
       read (memory :> bytes(word_add c (word 1952),4096)) s =
       num_of_wordlist mlkem_rej_uniform_table /\
       read (memory :> bytes(c,192)) s = num_of_wordlist round_constants`;;

let gm_samplepoly_tm =
  subst [mk_small_numeral(gm_pc "rejloop" 0),`pc0:num`;
         mk_small_numeral(gm_pc "rejloop" 148),`pc1:num`]
 `!b (A:1600 word) a c idx l stackpointer pc.
     mlkem_samplentt_terminates b /\
     (!t. num_of_bytelist(list_of_seq (\j. shake128 b (168 * t + j)) 168) =
          val(keccak_squeeze (t + 1) A) MOD 2 EXP 1344) /\
     l < 4 /\ idx + l < 16 /\ aligned 32 a /\
     ALL (nonoverlapping (stackpointer,3072))
         [(word pc,mlkem_native2_image_size);
          (word_add a (word(512 * (idx + l))),512); (c,6048)] /\
     ALL (nonoverlapping (word_add a (word(512 * (idx + l))),512))
         [(word pc,mlkem_native2_image_size); (c,6048)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + pc0) /\
               read RSP s = word_add stackpointer (word 40) /\
               read RBX s = a /\ read R15 s = c /\
               read R12 s = word idx /\ read R14 s = word l /\
               read (memory :> bytes(word_add stackpointer
                                      (word(840 + 504 * l)),504)) s =
               num_of_bytelist(list_of_seq (shake128 b) 504) /\
               read (memory :> bytes(word_add stackpointer
                                      (word(40 + 200 * l)),200)) s =
               val(keccak_squeeze 3 A) /\
               read (memory :> bytes(word_add c (word 1952),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants)
          (\s. read RIP s = word(pc + pc1) /\
               read RSP s = word_add stackpointer (word 40) /\
               read (memory :> bytes(word_add stackpointer
                                      (word(40 + 200 * l)),200)) s =
               val(keccak_squeeze (mlkem_rej_blocks b) A) /\
               !t. t < 256
                   ==> read (memory :> bytes16(word_add a
                                (word(512 * (idx + l) + 2 * t)))) s =
                       iword(mlkem_sample_ntt b (avx_unorder t)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_add a (word(512 * (idx + l))),512);
                      memory :> bytes(word_add stackpointer
                                       (word(40 + 200 * l)),200);
                      memory :> bytes(word_add stackpointer (word 3024),8);
                      memory :> bytes(stackpointer,40)])`;;

let MLKEM_GEN_MATRIX_SAMPLEPOLY = prove
 (gm_samplepoly_tm,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN `aligned 32 (word_add a (word(512 * (idx + l))):int64)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `512 * n = 32 * (16 * n)`] THEN
    ASM_SIMP_TAC[ALIGNED_BLOCK];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    val(word_mul (word l) (word 504):int64) = 504 * l /\
    val(word_mul (word l) (word 200):int64) = 200 * l /\
    val(word_shl (word_add (word idx) (word l)) 9:int64) = 512 * (idx + l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD; WORD_SHL_WORD; VAL_WORD;
                DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);
    ALL_TAC] THEN

  (*** The addresses of the polynomial, buffer and lane as stated ***)

  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`;
      ASSUME `val(word_mul (word l) (word 504):int64) = 504 * l`;
      ASSUME `val(word_mul (word l) (word 200):int64) = 200 * l`;
      ASSUME `val(word_shl (word_add (word idx) (word l)) 9:int64) =
              512 * (idx + l)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (504 * l + 800)) =
        word_add x (word(840 + 504 * l))`;
      WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (200 * l)) =
        word_add x (word(40 + 200 * l))`]) in

  (*** The exit with the 256 entries of m blocks, and mlkem_unpack ***)

  let EXIT_TAC m =
    SUBGOAL_THEN (subst [m,`m:num`] `LENGTH(mlkem_rej_out b m) = 256`)
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_MLKEM_REJ_OUT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME (subst [m,`m:num`] `LENGTH(mlkem_rej_out b m) = 256`);
      ARITH_RULE `2 * 256 = 512`]) THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--6) THEN NORM_TAC THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_unpack",mlkem_unpack_mc,MLKEM_UNPACK_SAMPLE_NTT)
     ([`read RDI s`; `b:byte list`; m; `pc + mlkem_unpack`] @
      return_args) 7 THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    ASM_REWRITE_TAC[] in

  (*** The first call, on the three blocks in the buffer ***)

  ENSURES_SEQUENCE_TAC (gm_pc_tm(gm_pc "rejloop" 46)) (samplepoly_inv `3`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BUF_OUT)
     ([`read RDI s`; `read RDX s`; `read R8 s`; `b:byte list`;
       `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @ return_args) 10 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = mlkem_rej_blocks b - 3` THEN
  SUBGOAL_THEN `mlkem_rej_blocks b = 3 + N` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `256 <= CARD {j | j < 112 * (3 + N) /\
                     mlkem_xof_field (shake128 b) j < 3329}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `mlkem_rej_blocks b = 3 + N`
                            then SUBST1_TAC(SYM th) THEN ASSUME_TAC th
                            else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN EXIT_TAC `3`;
    ALL_TAC] THEN

  (*** Otherwise the loop over the further blocks ***)

  ENSURES_WHILE_UP_TAC `N:num` (gm_pc_tm(gm_pc "rejloop" 54))
   (gm_pc_tm(gm_pc "rejloop" 46))
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
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The body: another block from the lane, and its fields ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * (idx + l))),
                      2 * LENGTH(mlkem_rej_out b (3 + t)))
                     (stackpointer:int64,3072)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--5) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(40 + 200 * l)):int64` 5 THEN
    RC_TAC `c:int64` 5 THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,0,mlkem_native2_image_mc,
      SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT_F1600)
     ([`read RDI s`; `read RSI s`; `keccak_squeeze (3 + t) (A:1600 word)`;
       `pc:num`] @ return_args) 6 THEN
    FROM_WBYTES_TAC 6 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (7--15) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(40 + 200 * l)),168))
           s15 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + t) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(40 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + t) (A:1600 word)))`;
                    `s15:x86state`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BLOCK_OUT)
     ([`read RDI s`; `read RDX s`; `read R8 s`; `b:byte list`; `3 + t`;
       `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @ return_args) 16 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [17] THEN
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
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit, with the 256 coefficients ***)

    EXIT_TAC `3 + N`]);;

(* ------------------------------------------------------------------------- *)
(* One block of hash job j (0 or 1) absorbed into its lane (2 or 3), as the  *)
(* absorbjob macro does it, as one step: a whole block of 136 bytes, or the  *)
(* last t < 136 bytes with the padding for the domain byte ds. The state of  *)
(* the lane is the sponge state after i blocks of the padded message, and    *)
(* the copy of the job (p, r, ds, out) on the stack at offset 2816 + 32 * j  *)
(* has the next byte and the number of bytes left. The instances are for the *)
(* lengths and domain bytes of H(ek) and J(z || c) in the API.               *)
(* ------------------------------------------------------------------------- *)

let GM_ABSORB_FULL_TAC lane ds =
  let lanetm = mk_comb(`word_add (frm:int64)`,
                       mk_comb(`word:num->int64`,mk_small_numeral lane)) in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (subst [mk_small_numeral ds,`ds:num`]
   `A = keccak_absorb 136 (keccak_padded 136 ds m) i`) THEN
  ABBREV_TAC
   `B = (num_of_bytelist m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
  SUBGOAL_THEN
   `val(word(LENGTH(m:byte list) - 136 * i):int64) = LENGTH m - 136 * i /\
    ~(ival(word(LENGTH(m:byte list) - 136 * i):int64) < &0) /\
    ~(LENGTH(m:byte list) - 136 * i < 136) /\
    136 <= LENGTH(m:byte list) - 136 * i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN REWRITE_TAC[BIT_VAL] THEN
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
    check (can (term_match [`frm:int64`]
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

  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `~(LENGTH(m:byte list) - 136 * i < 136)`]) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (13--118) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `~(LENGTH(m:byte list) - 136 * i < 136)`]) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (119--122) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let gm_absorb_full_tm j ds =
  let lane = 400 + 200 * j and st = 2816 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 18 + 124 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 124),`pc1:num`;
         ns ds,`ds:num`]
  `!m inp i frm pc.
    LENGTH m < 2 EXP 63 /\ 136 * (i + 1) <= LENGTH m /\
    ALL (nonoverlapping (word_add frm (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    ALL (nonoverlapping (word_add frm (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    nonoverlapping (word_add frm (word lane),200) (word_add frm (word st),24)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + pc0) /\
          read RSP s = frm /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * i)) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word(LENGTH m - 136 * i) /\
          read (memory :> bytes64(word_add frm (word st16))) s = word ds /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(word_add frm (word lane),200)) s =
          val(keccak_absorb 136 (keccak_padded 136 ds m) i))
     (\s. read RIP s = word(pc + pc1) /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * (i + 1))) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word(LENGTH m - 136 * (i + 1)) /\
          read (memory :> bytes(word_add frm (word lane),200)) s =
          val(word_xor (keccak_absorb 136 (keccak_padded 136 ds m) i)
               (word((keccak_padded 136 ds m DIV 2 EXP (8 * 136 * i)) MOD
                     2 EXP (8 * 136)))))
     (MAYCHANGE [RIP; RAX; RCX; RDX; RDI; R8; R9; R10; R11] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add frm (word st),16);
                 memory :> bytes(word_add frm (word lane),200)])`;;

let GM_ABSORB_FULL_PROOF_TAC j ds =
  GM_ABSORB_FULL_TAC (400 + 200 * j) ds THEN
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
  let lane = 400 + 200 * j and st = 2816 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 18 + 124 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 124),`pc1:num`;
         ns t,`t:num`; ns ds,`ds:num`]
  `!m inp q frm pc.
    LENGTH m = 136 * q + t /\ LENGTH m < 2 EXP 63 /\
    ALL (nonoverlapping (word_add frm (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    ALL (nonoverlapping (word_add frm (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m)] /\
    nonoverlapping (word_add frm (word lane),200) (word_add frm (word st),24)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + pc0) /\
          read RSP s = frm /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * q)) /\
          read (memory :> bytes64(word_add frm (word st8))) s = word t /\
          read (memory :> bytes64(word_add frm (word st16))) s = word ds /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(word_add frm (word lane),200)) s =
          val(keccak_absorb 136 (keccak_padded 136 ds m) q))
     (\s. read RIP s = word(pc + pc1) /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * q + t)) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word 18446744073709551615 /\
          read (memory :> bytes(word_add frm (word lane),200)) s =
          val(word_xor (keccak_absorb 136 (keccak_padded 136 ds m) q)
               (word((keccak_padded 136 ds m DIV 2 EXP (8 * 136 * q)) MOD
                     2 EXP (8 * 136)))))
     (MAYCHANGE [RIP; RAX; RCX; RDX; RDI; R8; R9; R10; R11] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add frm (word st),16);
                 memory :> bytes(word_add frm (word lane),200)])`;;

let GM_ABSORB_LAST_PROOF_TAC j t ds =
  let w = t / 8 in
  let lane = 400 + 200 * j in
  let lanetm = mk_comb(`word_add (frm:int64)`,
                       mk_comb(`word:num->int64`,mk_small_numeral lane)) in
  let nsteps1 = 15 + 6 * w in
  let tn = mk_small_numeral t and wn = mk_small_numeral w
  and dsn = mk_small_numeral ds in
  let stv n = mk_var("s"^string_of_int n,`:x86state`) in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
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
    check (can (term_match [`frm:int64`]
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

  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps1) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; stv nsteps1,`s:x86state`]
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
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+1)--(nsteps1+3)) THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral lane,`l:num`; stv(nsteps1+3),`s:x86state`;
           tn,`t:num`; dsn,`ds:num`]
    `!j. j < 200
         ==> read (memory :> bytes8(word_add frm (word(l + j)))) s =
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
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [nsteps1+4] THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; stv(nsteps1+4),`s:x86state`;
           tn,`t:num`; dsn,`ds:num`]
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
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+5)--(nsteps1+7)) THEN
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

let GM_ABSORB_LAST_0_120_6 = prove
 (gm_absorb_last_tm 0 120 6, GM_ABSORB_LAST_PROOF_TAC 0 120 6);;

let GM_ABSORB_LAST_0_96_6 = prove
 (gm_absorb_last_tm 0 96 6, GM_ABSORB_LAST_PROOF_TAC 0 96 6);;

let GM_ABSORB_LAST_0_72_6 = prove
 (gm_absorb_last_tm 0 72 6, GM_ABSORB_LAST_PROOF_TAC 0 72 6);;

let GM_ABSORB_LAST_1_120_6 = prove
 (gm_absorb_last_tm 1 120 6, GM_ABSORB_LAST_PROOF_TAC 1 120 6);;

let GM_ABSORB_LAST_1_96_6 = prove
 (gm_absorb_last_tm 1 96 6, GM_ABSORB_LAST_PROOF_TAC 1 96 6);;

let GM_ABSORB_LAST_1_72_6 = prove
 (gm_absorb_last_tm 1 72 6, GM_ABSORB_LAST_PROOF_TAC 1 72 6);;

let GM_ABSORB_LAST_1_120_31 = prove
 (gm_absorb_last_tm 1 120 31, GM_ABSORB_LAST_PROOF_TAC 1 120 31);;

let GM_ABSORB_LAST_1_32_31 = prove
 (gm_absorb_last_tm 1 32 31, GM_ABSORB_LAST_PROOF_TAC 1 32 31);;

let GM_ABSORB_LAST_1_104_31 = prove
 (gm_absorb_last_tm 1 104 31, GM_ABSORB_LAST_PROOF_TAC 1 104 31);;

(* ------------------------------------------------------------------------- *)
(* Addresses in the frame for the stack pointer of the function at           *)
(* stackpointer + spoff (lane l, the buffer of lane l, offset off), and      *)
(* keccak_squeeze 1, 2 and 3 as permutations.                                *)
(* ------------------------------------------------------------------------- *)

let gm_lane_addr spoff l = addr_plus `stackpointer:int64` (spoff + 200 * l);;

let gm_buf_addr spoff l =
  addr_plus `stackpointer:int64` (spoff + 800 + 504 * l);;

let gm_st spoff off = addr_plus `stackpointer:int64` (spoff + off);;

let bytes64_fact a k gl =
  asm_with_lhs (vsubst [a,`a:int64`; state_of k,`s:x86state`]
                 `read (memory :> bytes64 a) s`) gl;;

let word_base tm =
  try let f,args = strip_comb tm in
      if fst(dest_const f) = "word_add" then hd args else tm
  with Failure _ -> tm;;

let dest_bytes_read tm =
  let r,s = dest_comb tm in
  let _,c = dest_comb r in
  let _,b = dest_comb c in
  let bc,an = dest_comb b in
  if fst(dest_const bc) <> "bytes" then failwith "dest_bytes_read" else
  let a,n = dest_pair an in a,n,s;;

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
(* The facts added on the way, by the offset of RIP where they are needed:   *)
(* the job and noise structures as 32-byte words before they are copied and  *)
(* the 8-byte fields of the copies after; lanes 2 and 3 as zero after the    *)
(* zeroing loop; the zero bytes of a lane before the store of its final bit, *)
(* as pieces that the store does not overlap, and the state of a matrix      *)
(* polynomial's lane after initlane and of a noise polynomial's lane after   *)
(* initnoise; the loads of a lane copied to the buffer and the block stored; *)
(* the first 32 bytes of a job's lane and its digest once copied out.        *)
(* ------------------------------------------------------------------------- *)

let GM_MERGE_TAC reg offs k gl =
  let b = find_read_fact reg k gl in
  READ_MEMORY_MERGE256_TAC (state_of k) (map (addr_plus b) offs) gl;;

let GM_SPLIT_TAC spoff offs k =
  READ_MEMORY_SPLIT256_TAC (state_of k) (map (gm_st spoff) offs);;

let GM_ZERO_LANES_TAC spoff k =
  let sv = state_of k in
  let a = gm_lane_addr spoff 2 in
  let tm = vsubst [a,`a:int64`; sv,`s:x86state`]
             `read (memory :> bytes(a,400)) s = 0` in
  SUBGOAL_THEN tm MP_TAC THENL
   [CONV_TAC(LAND_CONV(BYTES_PIECES_CONV (replicate 32 12 @ [16]))) THEN
    ASM_REWRITE_TAC[VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
    REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; READ_MEMORY_BYTES_SPLIT] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]];;

let GM_LANE_SPLIT_TAC off k gl =
  let a = find_read_fact `RDI` k gl in
  let sv = state_of k in
  let x = addr_plus a off in
  let th0 = asm_with_lhs (vsubst [x,`x:int64`; sv,`s:x86state`]
              `read (memory :> bytes256 x) s`) gl in
  let split th = CONJ_PAIR(CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                                     DEPTH_CONV WORD_RED_CONV) th) in
  let l1,h1 = split th0 in
  let l2,h2 = split h1 in
  let l3,h3 = split h2 in
  let l4,h4 = split h3 in
  let l5,_ = split h4 in
  MAP_EVERY ASSUME_TAC [l1;l2;l3;l4;l5] gl;;

let GM_MATRIX_LANE_TAC k gl =
  let a = find_read_fact `RDI` k gl and sv = state_of k in
  let th32 = bytes64_fact (addr_plus a 32) k gl in
  let v = dest_small_numeral(rand(rand(concl th32))) - 2031616 in
  let x = v mod 256 and y = v / 256 in
  (MP_TAC(SPECL [a; `rho:byte list`; mk_small_numeral x; mk_small_numeral y;
                 sv]
                MLKEM_MATRIX_LANE) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC]) gl;;

let MLKEM_NOISE_LANE_GM =
  REWRITE_RULE[WORD_NONCE_DS_X86] MLKEM_NOISE_LANE_X86;;

let GM_NOISE_LANE_TAC k gl =
  let a = find_read_fact `RDI` k gl and sv = state_of k in
  let v = dest_small_numeral
            (rand(rand(concl(bytes64_fact (addr_plus a 32) k gl)))) in
  let y = mk_comb(`word:num->byte`,mk_small_numeral(v - 7936)) in
  (MP_TAC(SPECL [a; `seed:byte list`; y; sv] MLKEM_NOISE_LANE_GM) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC]) gl;;

let GM_COPY_LOAD_TAC = LANE_LOAD_TAC [0;32;64;96;128] [] [160];;

(*** After the copy of the first 168 bytes of a lane to its buffer, the
 *** buffer as one number, and the facts about the pieces loaded and stored,
 *** which are no longer needed and whose terms (with numerals of hundreds
 *** of digits) every later step would otherwise carry, dropped
 ***)

let GM_COPY_STORE_TAC k gl =
  let buf = find_read_fact `RDI` k gl in
  let x = rand(concl(bytes_fact (find_read_fact `RSI` k gl) 200 k gl)) in
  let sv = state_of k in
  let piece t =
    match t with
      Comb(Const("word",_),Comb(Comb(Const("MOD",_),
           Comb(Comb(Const("DIV",_),y),_)),_)) -> y = x
    | Comb(Const("word",_),Comb(Comb(Const("MOD",_),y),_)) -> y = x
    | _ -> false in
  let memread t =
    try name_of(fst(strip_comb(rand(rator t)))) = ":>"
    with Failure _ -> false in
  (MP_TAC(SPECL [buf; x; sv] READ_MEMORY_BYTES_168_OF_PIECES) THEN
   ANTS_TAC THENL
    [CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     REWRITE_TAC[DIV_1; WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     DISCH_TAC THEN
     DISCARD_ASSUMPTIONS_TAC (fun th ->
       let c = concl th in is_eq c && piece(rand c) && memread(lhand c))])
  gl;;

let GM_LANE256_TAC off k gl =
  let a = addr_plus (find_read_fact `RSP` k gl) off and sv = state_of k in
  let th200 = bytes_fact a 200 k gl in
  let x = rand(concl th200) in
  let th = SPECL [a; `200`; x; `0`; sv] READ_MEMORY_BYTES256_OF_NUM in
  let th' = MP th (CONJ th200 (ARITH_RULE `0 + 32 <= 200`)) in
  ASSUME_TAC(REWRITE_RULE[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] th') gl;;

let GM_DIGEST_TAC off k (asl,w as gl) =
  let out = find_read_fact `RDI` k gl
  and lane = addr_plus (find_read_fact `RSP` k gl) off in
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
  let th = SPECL [out; x; sv] READ_MEMORY_BYTES_32_OF_BYTES256 in
  (MP_TAC th THEN ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     REWRITE_TAC[GSYM dth] THEN DISCH_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* The steps taken as one: the rejection sampling of a matrix polynomial     *)
(* (with the termination of SampleNTT for its seed of 34 bytes, by           *)
(* MLKEM_SAMPLENTT_TERMINATES_SEED), a block of a hash job by the lemmas     *)
(* above (or the code if the job is inactive), with the state of its lane    *)
(* first put as keccak_absorb 136 P i, and mlkem_getnoise for the noise      *)
(* polynomials left; the x4 permutation, with the lanes that hold no         *)
(* polynomial or job taken as they are; and the results of the CBD and of    *)
(* mlkem_getnoise in the form of the theorems.                               *)
(* ------------------------------------------------------------------------- *)

let GM_SAMPLEPOLY_TAC exec spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `R14` k gl))
  and idx = dest_small_numeral(rand(find_read_fact `R12` k gl)) in
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
  let lemma = SPECL [b; aa; `a:int64`; `c:int64`; mk_small_numeral idx;
                     mk_small_numeral l;
                     addr_plus `stackpointer:int64` (spoff - 40); `pc:num`]
                    MLKEM_GEN_MATRIX_SAMPLEPOLY in
  let lemma' = CONV_RULE(ONCE_DEPTH_CONV KECCAK_SQUEEZE_NUM_CONV) lemma in
  let lth = find_asm (fun c ->
              c = mk_eq(mk_comb(`LENGTH:byte list->num`,rho),`32`)) gl in
  let term_th = MP (SPECL [rho; x; y] MLKEM_SAMPLENTT_TERMINATES_SEED) lth in
  (ASSUME_TAC term_th THEN bufth THEN
   MP_TAC spth THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC lemma' THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(fun th ->
     X86_SUBROUTINE_SIM_TAC
      (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1))) gl;;

let GM_BLOCK_RULE = REWRITE_RULE[GSYM keccak_absorb_block];;

let GM_ABSORB_CALL_TAC lemmas exec spoff j k (asl,w as gl) =
  let full_ths,last_ths = lemmas in
  let sv = state_of k in
  let st = gm_st spoff (2816 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then X86_STEPS_TAC exec [k+1] gl else
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
        if concl th = vsubst [lane,`a:int64`; sv,`s:x86state`]
                       `read (memory :> bytes(a,200)) s = 0`
        then ASSUME_TAC(TRANS th (SYM(REWRITE_CONV[keccak_absorb; VAL_WORD_0]
                                       (mk_comb(`val:1600 word->num`,ka)))))
        else NO_TAC)
    else
      FIRST_X_ASSUM(fun th ->
        if lhand(concl th) = vsubst [lane,`a:int64`; sv,`s:x86state`]
                               `read (memory :> bytes(a,200)) s`
        then ASSUME_TAC(CONV_RULE(RAND_CONV
               (REWRITE_CONV[KECCAK_ABSORB_BLOCK_STEP] THENC
                NUM_REDUCE_CONV)) th)
        else NO_TAC) in
  let sp = find_read_fact `RSP` k gl in
  let lemma =
    if r >= 136 then
      SPECL [m; inp; mk_small_numeral i; sp; `pc:num`] (assoc (j,ds) full_ths)
    else
      SPECL [m; inp; mk_small_numeral i; sp; `pc:num`]
            (assoc (j,r,ds) last_ths) in
  let lemma' = REWRITE_RULE[WORD_ADD_0]
                (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[lenth] lemma)) in
  let lemma'' = CONV_RULE(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV) lemma' in
  (lane_tac THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,lemma'') [] (k+1))
  gl;;

let GM_KECCAK4_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl and rc = find_read_fact `RSI` k gl
  and rho8 = find_read_fact `RDX` k gl and rho56 = find_read_fact `RCX` k gl in
  let sv = state_of k in
  let ads = map (addr_plus a) [0;200;400;600] in
  let state_tm ad =
    try lane_state ad k gl
    with Failure _ ->
      vsubst [ad,`a:int64`; sv,`s:x86state`]
       `read (memory :> wbytes a) s:1600 word` in
  let ss = map state_tm ads in
  (RC_TAC rc k THEN RHO_TAC rho8 rho56 k THEN
   MAP_EVERY (fun ad -> TRY(TO_WBYTES_TAC ad k)) ads THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "sha3_keccak4_f1600_alt",sha3_keccak4_f1600_alt_mc,
     SHA3_KECCAK4_F1600_ALT_SUBROUTINE_CORRECT_F1600)
    ([`read RSI s`; `read RDI s`; `read RDX s`; `read RCX s`] @ ss @
     [`pc + sha3_keccak4_f1600_alt`] @ return_args) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let GM_SWAP_RDI_TAC k gl =
  match find_read_fact `RDI` k gl with
    Comb(Comb(Const("word_add",_),(Comb(Const("word",_),n) as wn)),x)
      when is_numeral n ->
      RULE_ASSUM_TAC(REWRITE_RULE[ISPECL [wn; x] WORD_ADD_SYM]) gl
  | _ -> ALL_TAC gl;;

let GM_GETNOISE_CALL0_TAC exec k gl =
  let v reg = dest_small_numeral(rand(find_read_fact reg k gl)) in
  let ns = mk_small_numeral in
  let sp = find_read_fact `RSP` k gl in
  let c = rand(concl(bytes64_fact (addr_plus sp 8) k gl)) in
  let th = SPECL [find_read_fact `RDI` k gl; find_read_fact `RSI` k gl;
                  `seed:byte list`; ns(v `RDX`); ns(v `RCX`); ns(v `R8`);
                  ns(v `R9`); c; `pc:num`; sp;
                  rand(concl(bytes64_fact sp k gl))]
                 MLKEM_GETNOISE_SUBROUTINE_CORRECT in
  let th' = CONV_RULE(LAND_CONV(LAND_CONV(REWRITE_CONV[ARITH_EQ]))) th in
  let th'' = REWRITE_RULE[COND_ID] (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[] th')) in
  (RC_TAC c k THEN RHO_TAC (addr_plus c 192) (addr_plus c 224) k THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th'') [] (k+1)) gl;;

let GM_GETNOISE_CALL_TAC exec k =
  GM_SWAP_RDI_TAC k THEN GM_GETNOISE_CALL0_TAC exec k;;

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
(* The hooks by the offset of RIP, for the stack pointer of the function at  *)
(* stackpointer + spoff (spoff = 807 for the x4 permutation below it, or     *)
(* 2551 when mlkem_getnoise is called).                                      *)
(* ------------------------------------------------------------------------- *)

let gm_derive spoff =
  [gm_pc "nonoise" (-14), GM_MERGE_TAC `R9` [0];
   gm_pc "nonoise" 0, (fun k -> TRY(GM_SPLIT_TAC spoff [2880] k));
   gm_pc "nonoise" 8, GM_MERGE_TAC `R8` [0; 32];
   gm_pc "jobsdone" 0, (fun k -> TRY(GM_SPLIT_TAC spoff [2816; 2848] k));
   gm_pc "outer" 0, (fun k -> TRY(GM_ZERO_LANES_TAC spoff k));
   gm_pc "initloop" 133, GM_LANE_SPLIT_TAC 136;
   gm_pc "initloop" 140, GM_MATRIX_LANE_TAC;
   gm_pc "noiseinit" 149, GM_LANE_SPLIT_TAC 104;
   gm_pc "noiseinit_next" 0, (fun k -> TRY(GM_NOISE_LANE_TAC k));
   gm_pc "nohash1" 65, GM_LANE256_TAC 400;
   gm_pc "nohash1" 78, GM_DIGEST_TAC 400;
   gm_pc "nohash1" 112, GM_LANE256_TAC 600;
   gm_pc "nohash1" 125, GM_DIGEST_TAC 600;
   gm_pc "copyloop" 0, GM_COPY_LOAD_TAC;
   gm_pc "copyloop" 68, GM_COPY_STORE_TAC];;

let gm_absorb_lemmas =
  map (fun (j,ds,th) -> (j,ds),GM_BLOCK_RULE th)
   [0,6,GM_ABSORB_FULL_0_6; 1,6,GM_ABSORB_FULL_1_6; 1,31,GM_ABSORB_FULL_1_31],
  map (fun (j,t,ds,th) -> (j,t,ds),GM_BLOCK_RULE th)
   [0,120,6,GM_ABSORB_LAST_0_120_6; 0,96,6,GM_ABSORB_LAST_0_96_6;
    0,72,6,GM_ABSORB_LAST_0_72_6; 1,120,6,GM_ABSORB_LAST_1_120_6;
    1,96,6,GM_ABSORB_LAST_1_96_6; 1,72,6,GM_ABSORB_LAST_1_72_6;
    1,120,31,GM_ABSORB_LAST_1_120_31; 1,32,31,GM_ABSORB_LAST_1_32_31;
    1,104,31,GM_ABSORB_LAST_1_104_31];;

let gm_calls spoff =
  let exec = MLKEM_GEN_MATRIX_EXEC in
  [gm_pc "end" 0,
     (fun k -> X86_SUBROUTINE_SIM_TAC
       (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,GM_ZERO_END)
       [`read RSP s`; `pc:num`] (k+1));
   layout "sha3_keccak4_f1600_alt", GM_KECCAK4_CALL_TAC exec;
   gm_pc "rejloop" 0, GM_SAMPLEPOLY_TAC exec spoff;
   gm_pc "noiseinit_done" 18, GM_ABSORB_CALL_TAC gm_absorb_lemmas exec spoff 0;
   gm_pc "noiseinit_done" 142,
     GM_ABSORB_CALL_TAC gm_absorb_lemmas exec spoff 1;
   layout "mlkem_cbd2",
     (fun k -> CBD2_CALL_TAC exec k THEN GM_NORMALIZE_OUT_TAC (k+1));
   layout "mlkem_getnoise",
     (fun k -> GM_GETNOISE_CALL_TAC exec k THEN GM_SPLIT_NOISE_TAC (k+1))];;

(* ------------------------------------------------------------------------- *)
(* The proof of an instance with stack size n: the setup (the 32-byte words  *)
(* of rho and of the noise seed), the simulation, and at the end each case   *)
(* of a polynomial of the results as an assumption.                          *)
(* ------------------------------------------------------------------------- *)

let GM_BYTES256_OF_32_TAC p v =
  MP_TAC(SPECL [p; `32`; v; `0`; `s0:x86state`]
    READ_MEMORY_BYTES256_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 32 <= 32`; WORD_ADD_0; MULT_CLAUSES; EXP;
                  DIV_1] THEN
  DISCH_TAC;;

let GM_SETUP_TAC n =
  REPEAT(W(fun (_,w) ->
    let v = fst(dest_forall w) in
    if fst(dest_var v) = "stackpointer" then NO_TAC else X_GEN_TAC v)) THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS;
              WORDLIST_FROM_MEMORY_RHO8; WORDLIST_FROM_MEMORY_RHO56] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  GM_BYTES256_OF_32_TAC `rhop:int64` `num_of_bytelist(rho:byte list)` THEN
  W(fun (asl,w) ->
    if can (find_term ((=) `sigma:int64`)) w ||
       exists (fun (_,th) -> free_in `sigma:int64` (concl th)) asl
    then GM_BYTES256_OF_32_TAC `sigma:int64` `num_of_bytelist(seed:byte list)`
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
  NATIVE2_RUN_TAC MLKEM_GEN_MATRIX_EXEC (gm_derive(n - 3080))
    (gm_calls(n - 3080)) 0 THEN
  GM_FINALE_TAC;;
