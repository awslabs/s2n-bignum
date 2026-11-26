(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for the SHAKE256 sponge that clang 23 -O3 inlines into the  *)
(* functions of the clang23_O3_mono_reduced_ram image (those of the          *)
(* absorbing of a message of symbolic length, with the loop over the blocks  *)
(* of 136 bytes that calls mldsa_keccakf1600_permute, the XOR of the rest of *)
(* the message, the padding and the squeezing), stated against the model of  *)
(* common/mldsa_native_fips202.ml, as the proofs of the gcc builds state the *)
(* theorems of their callees mldsa_shake256_absorb, _finalize and _squeeze.  *)
(* The byte-level XORing uses the lemmas of inline_sponge.ml.                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;

(*** A block of l bytes of an array after the first k ***)

let SPONGE2_BYTES_SUB = prove
 (`!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 64-bit lanes of the state, as a word and in memory.                   *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_BYTES64_OF_WBYTES = prove
 (`!(a:int64) (X:1600 word) k (s:armstate).
        read (memory :> wbytes a) s = X /\ k < 25
        ==> read (memory :> bytes64 (word_add a (word (8 * k)))) s =
            word_subword X (64 * k,64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `8 * k`; `s:armstate`]
         READ_MEMORY_BYTES64_OF_NUM) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
      ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 * 8 * k = 64 * k`; MOD_MOD_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The loop over the full blocks of 136 bytes (loop1 of the six functions    *)
(* mldsa{44,65,87}_{signature,verify}_pre_hash_shake256): each iteration     *)
(* XORs the next 136 bytes of the message at the register PR into the state  *)
(* of 200 bytes at sp + 64, with ldp/eor/stp of D registers, and calls       *)
(* mldsa_keccakf1600_permute; the register LR has the length that is left,   *)
(* and is decreased by 136. The lemma goes from the head of the loop, for a  *)
(* message of mlen >= 136 bytes, to its exit, where the state is that of     *)
(* mld_keccak_absorb_blocks after the n = mlen DIV 136 blocks.               *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_L1_EXEC fn =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range fn];;

let SPONGE2_L1_STMT fn pr lr = parse_term(Printf.sprintf
 "exists f_events. forall e d mlen M n (S0:1600 word) sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ mlen DIV 136 = n /\\ 0 < n /\\ mlen < 2 EXP 64 /\\
   nonoverlapping (d,mlen) (word_sub sp (word 240),504) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),504)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read PC s = word (pc + %s_loop1) /\\ read SP s = sp /\\
          read %s s = d /\\ read %s s = word mlen /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes (word_add sp (word 64))) s = S0 /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s_loop1_exit) /\\ read SP s = sp /\\
          read %s s = word_add d (word (136 * n)) /\\
          read %s s = word (mlen - 136 * n) /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes (word_add sp (word 64))) s =
            mld_keccak_absorb_blocks 136 S0 M n /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d mlen sp n pc /\\
             memaccess_inbounds e2
              [d,mlen; word_add sp (word 64),200; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add sp (word 64),200; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add sp (word 64),200);
                memory :> bytes(word_sub sp (word 240),240)])"
  fn pr lr fn pr lr pr lr);;

let SPONGE2_L1_INV pr lr = parse_term(Printf.sprintf
 "\\k s. read SP s = sp /\\
        read %s s = word_add d (word (136 * k)) /\\
        read %s s = word (mlen - 136 * k) /\\
        read (memory :> bytes(d,mlen)) s = M /\\
        read (memory :> wbytes (word_add sp (word 64))) s =
          mld_keccak_absorb_blocks 136 S0 M k" pr lr);;

let SPONGE2_L1_VARS = [`d:int64`; `mlen:num`; `sp:int64`; `n:num`; `pc:num`; `i:num`];;

(* The events of the callee are named ec, not e2 as in the postcondition of
   the loop, so that the two do not become one variable when chosen *)

let SPONGE2_RENAME_E2 = CONV_RULE(DEPTH_CONV(fun tm ->
  if is_exists tm && name_of(fst(dest_exists tm)) = "e2"
  then ALPHA_CONV (mk_var("ec",type_of(fst(dest_exists tm)))) tm
  else failwith "SPONGE2_RENAME_E2"));;

let SPONGE2_L1_SETUP fn pr lr =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE2_RENAME_E2
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(d:int64) (mlen:num) (sp:int64) (n:num) (pc:num).
      APPEND (f_ev_epil d mlen sp n pc)
       (APPEND (ENUMERATEL n (\i. f_ev_loop d mlen sp n pc i))
               (f_ev_prol d mlen sp n pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `mlen:num`; `M:num`; `n:num`;
    `S0:1600 word`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst (SPONGE2_L1_EXEC fn)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` (parse_term (Printf.sprintf "pc + %s_loop1" fn))
   (parse_term (Printf.sprintf "pc + %s_loop1_exit" fn)) (SPONGE2_L1_INV pr lr) THEN
  REPEAT CONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state as a word from its 25 lanes of 64 bits in memory.               *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_BYTES_OF_BYTES64 = prove
 (`!(a:int64) n x (s:armstate).
        (!j. j < n
             ==> read (memory :> bytes64 (word_add a (word (8 * j)))) s =
                 word((x DIV 2 EXP (64 * j)) MOD 2 EXP 64))
        ==> read (memory :> bytes(a,8 * n)) s = x MOD 2 EXP (64 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL;
                EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`;
              ARITH_RULE `64 * SUC n = 64 * n + 64`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 8 * n = 64 * n`; EXP_ADD] THEN
  GEN_REWRITE_TAC (RAND_CONV) [MOD_MULT_MOD] THEN
  ARITH_TAC);;

let SPONGE2_WBYTES_OF_LANES = prove
 (`!(a:int64) (X:1600 word) (s:armstate).
        (!j. j < 25
             ==> read (memory :> bytes64 (word_add a (word (8 * j)))) s =
                 word_subword X (64 * j,64))
        ==> read (memory :> wbytes a) s = X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `25`; `val(X:1600 word)`; `s:armstate`]
         SPONGE2_BYTES_OF_BYTES64) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL];
    REWRITE_TAC[ARITH_RULE `8 * 25 = 200`; ARITH_RULE `64 * 25 = 1600`] THEN
    SUBGOAL_THEN `val(X:1600 word) MOD 2 EXP 1600 = val X` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `X:1600 word` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`];
      ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_REWRITE_TAC[]]);;

(*** A lane of a number below 2^1600 as a subword of it as a word ***)

let SPONGE2_NUM_SUBWORD64 = prove
 (`!x p. x < 2 EXP 1600
        ==> (word((x DIV 2 EXP p) MOD 2 EXP 64):int64) =
            word_subword (word x:1600 word) (p,64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `(x MOD 2 EXP 1600) = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

(*** The lanes of a block of 136 bytes above the 17th are zero ***)

let SPONGE2_SUBWORD_HI = prove
 (`!(x:num) j.
        x < 2 EXP 1088 /\ 17 <= j
        ==> word_subword (word x:1600 word) (64 * j,64):int64 = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x < 2 EXP 1600` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 1088` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP SPONGE2_NUM_SUBWORD64 th)]) THEN
  SUBGOAL_THEN `x DIV 2 EXP (64 * j) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 1088` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_0]]);;

(* ------------------------------------------------------------------------- *)
(* The facts for one iteration of the loop: the lanes of the block of the    *)
(* message at d + 136 * i, as subwords of the number BLK (a number below     *)
(* 2^1600), and the lanes of the state, as subwords of the word XX, in the   *)
(* two forms of the addresses (as the instructions give them, nested or     *)
(* as sums).                                                                 *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_NORMADDR =
  CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
            DEPTH_CONV NUM_ADD_CONV);;

let SPONGE2_NORMADDR_ALL =
  CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
            DEPTH_CONV NUM_ADD_CONV);;

let SPONGE2_L1_BLOCK_FACTS_TAC =
  SUBGOAL_THEN `BLK < 2 EXP 1600` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 1088` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun k ->
    let kk = mk_small_numeral (8 * k) in
    let th = SPECL [`word_add d (word (136 * i)):int64`; `136`; `BLK:num`; kk;
                    `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
    let side = ARITH_RULE(mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` kk `8`) `136`) in
    FIRST_ASSUM(fun blk ->
      if concl blk = `read (memory :> bytes(word_add d (word (136 * i)),136))
                           (s0:armstate) = BLK` then
        let f = MP th (CONJ blk side) in
        let f = REWRITE_RULE[MATCH_MP SPONGE2_NUM_SUBWORD64
                              (ASSUME `BLK < 2 EXP 1600`)] f in
        let f = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) f in
        ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)
      else NO_TAC)) (0--16);;

let SPONGE2_L1_STATE_FACTS_TAC =
  FIRST_ASSUM(fun xx ->
    if concl xx = `read (memory :> wbytes (word_add sp (word 64)))
                        (s0:armstate) = (XX:1600 word)` then
      MAP_EVERY (fun k ->
        let th = MP (SPECL [`word_add sp (word 64):int64`; `XX:1600 word`;
                            mk_small_numeral k; `s0:armstate`]
                           SPONGE2_BYTES64_OF_WBYTES)
                    (CONJ xx (ARITH_RULE(mk_binop `(<):num->num->bool`
                                (mk_small_numeral k) `25`))) in
        let th = CONV_RULE (DEPTH_CONV NUM_MULT_CONV) th in
        ASSUME_TAC th THEN ASSUME_TAC (SPONGE2_NORMADDR th)) (0--24)
    else NO_TAC);;

(*** The lane that EOR of D registers and the store of D leave ***)

let SPONGE2_LANE_XOR = prove
 (`!a b:int64. word_zx(word_zx(word_subword (word_zx a ^^ word_zx b:int128) (0,64):int64):int128):int64 = a ^^ b`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(*** The length that is left after block i, and the test of the loop ***)

let SPONGE2_L1_X24 = prove
 (`!mlen i. 136 * (i + 1) <= mlen
    ==> word_sub (word (mlen - 136 * i)) (word 136):int64 = word (mlen - 136 * (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mlen - 136 * (i + 1) = (mlen - 136 * i) - 136` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
  SUBGOAL_THEN `136 <= mlen - 136 * i` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;
let SPONGE2_L1_TEST = prove
 (`!mlen i n. mlen < 2 EXP 64 /\ mlen DIV 136 = n /\ i + 1 <= n
    ==> ((135 <= val(word (mlen - 136 * (i + 1)):int64) /\
          ~(val(word_sub (word (mlen - 136 * (i + 1))) (word 135):int64) = 0)) <=>
         i + 1 < n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word (mlen - 136 * (i + 1)):int64) = mlen - 136 * (i + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word 135:int64) = 135` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of the loop lemma. The body of an iteration is the 47           *)
(* instructions that XOR the block of the message into the state, the call   *)
(* of the permutation (the 48th) and the loop test (the 49th and 50th      *)
(* after the call).                                                          *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_L1_BODY exec =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN `136 * (i + 1) <= mlen` ASSUME_TAC THENL
   [SUBGOAL_THEN `i + 1 <= n` MP_TAC THENL
     [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `mlen DIV 136 = n` THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `BLK = (M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
  ABBREV_TAC `XX = mld_keccak_absorb_blocks 136 S0 M i` THEN
  SUBGOAL_THEN `BLK < 2 EXP 1088` ASSUME_TAC THENL
   [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`; MOD_LT_EQ_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < 2 EXP 1088`]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add d (word (136 * i)),136)) s0 = BLK`
   ASSUME_TAC THENL
   [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 * i = 8 * (136 * i)`] THEN
    MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `mlen:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `136 * (i + 1) <= mlen` THEN ARITH_TAC;
    ALL_TAC] THEN
  SPONGE2_L1_BLOCK_FACTS_TAC THEN SPONGE2_L1_STATE_FACTS_TAC THEN
  ARM_STEPS_TAC exec (1--48) THEN
  MAP_EVERY (fun k ->
    ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)
      (MATCH_MP SPONGE2_SUBWORD_HI
        (CONJ (ASSUME `BLK < 2 EXP 1088`)
              (ARITH_RULE(mk_binop `(<=):num->num->bool` `17`
                                   (mk_small_numeral k))))))) (17--24) THEN
  SUBGOAL_THEN `read (memory :> wbytes (word_add sp (word 64))) (s48:armstate) =
                word_xor (XX:1600 word) (word BLK:1600 word)` ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_WBYTES_OF_LANES THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_XOR; SPONGE2_LANE_XOR; WORD_XOR_0] THEN
    TRY(REWRITE_TAC[WORD_XOR_SYM] THEN NO_TAC);
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERMUTE"
   [`word_add sp (word 64):int64`; `word_xor (XX:1600 word) (word BLK:1600 word)`;
    `pc:num`; `sp:int64`; `read X30 s48`] SPONGE2_L1_VARS 49 THEN
  ARM_STEPS_TAC exec (50--51) THEN
  SUBGOAL_THEN `i + 1 <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                word (mlen - 136 * (i + 1))` ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_L1_X24 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                word (mlen - 136 * (i + 1))`]) THEN
  FIRST_ASSUM(fun th -> if concl th = `mlen < 2 EXP 64` then
    MP_TAC(MATCH_MP SPONGE2_L1_TEST
      (CONJ th (CONJ (ASSUME `mlen DIV 136 = n`) (ASSUME `i + 1 <= n`))))
    else NO_TAC) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let SPONGE2_L1_FIN =
  REPEAT CONJ_TAC THEN
  FIRST
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
    CONV_TAC WORD_RULE THEN NO_TAC;
    REWRITE_TAC[ARITH_RULE `i + 1 = SUC i`; mld_keccak_absorb_blocks] THEN
    MAP_EVERY (fun c -> FIRST_ASSUM(fun th ->
      if concl th = c then SUBST1_TAC(SYM th) else NO_TAC))
     [`mld_keccak_absorb_blocks 136 S0 M i = XX`;
      `(M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136) = BLK`] THEN
    REWRITE_TAC[] THEN NO_TAC;
    MONOTONE_MAYCHANGE_TAC;
    SIGN_LOOP_DISCHARGE_TAC];;

let SPONGE2_L1_TAC fn pr lr =
  SPONGE2_L1_SETUP fn pr lr THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SPONGE2_L1_BODY (SPONGE2_L1_EXEC fn) THEN SPONGE2_L1_FIN;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_SPONGE2_L1 fn pr lr = prove(SPONGE2_L1_STMT fn pr lr, SPONGE2_L1_TAC fn pr lr);;

(* ------------------------------------------------------------------------- *)
(* The padding of the sponge: after the last block of the message has been   *)
(* XORed into the state, the code XORs the byte 0x1f at position r (the     *)
(* number of bytes of the last block) and the byte 0x80 at position 135,    *)
(* with a load, an EOR with an immediate and a store of a byte each. The     *)
(* state is seen in memory as the bytes below position r (or 135), the byte  *)
(* written, the bytes between the two positions and the bytes above 135;     *)
(* these lemmas give the state as a number after the stores.                 *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_XOR_FINAL = prove
 (`!(a:int64) (S:1600 word) m off len (s:armstate).
        off + len <= 200 /\ m < 2 EXP (8 * len) /\
        read (memory :> bytes(a,off + len)) s =
        val(word_xor S (word(2 EXP (8 * off) * m))) MOD 2 EXP (8 * (off + len)) /\
        read (memory :> bytes(word_add a (word(off + len)),200 - (off + len))) s =
        val S DIV 2 EXP (8 * (off + len))
        ==> read (memory :> bytes(a,200)) s =
            val(word_xor S (word(2 EXP (8 * off) * m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `len:num`] XOR_HIGH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `200 = (off + len) + (200 - (off + len))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_binary "DIV" (lhs(concl th)) &&
    can (find_term ((=) `word_xor:1600 word->1600 word->1600 word`))
        (lhs(concl th)))) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[DIVISION_SIMP]);;

let SPONGE2_XOR_EXTEND = prove
 (`!(a:int64) (S:1600 word) c off (s:armstate).
        off < 200 /\ c < 256 /\
        read (memory :> bytes(a,off)) s = val S MOD 2 EXP (8 * off) /\
        read (memory :> bytes8(word_add a (word off))) s =
          word_xor (word((val S DIV 2 EXP (8 * off)) MOD 256)) (word c)
        ==> read (memory :> bytes(a,off + 1)) s =
            val(word_xor S (word(2 EXP (8 * off) * c))) MOD 2 EXP (8 * (off + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `c:num`; `off:num`; `0`] XOR_CHUNK_1) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; DIV_1; EXP; MULT_CLAUSES] THEN
  SUBGOAL_THEN `c MOD 256 = c` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `c:num`; `off:num`] XOR_LOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word off):int64`; `(word_xor (word((val(S:1600 word) DIV 2 EXP (8 * off)) MOD 256)) (word c):byte)`; `s:armstate`] READ_MEMORY_BYTES_OF_WORD8) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_xor S (word(2 EXP (8 * off) * c)):1600 word) MOD 2 EXP (8 * (off + 1)) =
                val(word_xor S (word(2 EXP (8 * off) * c)):1600 word) MOD 2 EXP (8 * off) +
                2 EXP (8 * off) * ((val(word_xor S (word(2 EXP (8 * off) * c)):1600 word) DIV 2 EXP (8 * off)) MOD 256)`
   SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (off + 1) = 8 * off + 8`; EXP_ADD] THEN
    MP_TAC(SPECL [`val(word_xor S (word(2 EXP (8 * off) * c)):1600 word)`; `2 EXP (8 * off)`; `2 EXP 8`] MOD_MULT_MOD) THEN
    SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SPONGE2_PAD2 = prove
 (`!(a:int64) (S2:1600 word) (s:armstate).
        read (memory :> bytes(a,135)) s = val S2 MOD 2 EXP (8 * 135) /\
        read (memory :> bytes8(word_add a (word 135))) s =
          word_xor (word((val S2 DIV 2 EXP (8 * 135)) MOD 256)) (word 128) /\
        read (memory :> bytes(word_add a (word 136),64)) s =
          val S2 DIV 2 EXP (8 * 136)
        ==> read (memory :> bytes(a,200)) s =
            val(word_xor S2 (word(2 EXP (8 * 135) * 128)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `S2:1600 word`; `128`; `135`; `s:armstate`] SPONGE2_XOR_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `S2:1600 word`; `128`; `135`; `1`; `s:armstate`] SPONGE2_XOR_FINAL) THEN
  REWRITE_TAC[ARITH_RULE `135 + 1 = 136`; ARITH_RULE `200 - 136 = 64`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `135 + 1 = 136`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN ACCEPT_TAC]);;

let SPONGE2_PAD1 = prove
 (`!(a:int64) (S1:1600 word) r (s:armstate).
        r < 135 /\
        read (memory :> bytes(a,r)) s = val S1 MOD 2 EXP (8 * r) /\
        read (memory :> bytes8(word_add a (word r))) s =
          word_xor (word((val S1 DIV 2 EXP (8 * r)) MOD 256)) (word 31) /\
        read (memory :> bytes(word_add a (word (r + 1)),134 - r)) s =
          (val S1 DIV 2 EXP (8 * (r + 1))) MOD 2 EXP (8 * (134 - r)) /\
        read (memory :> bytes(word_add a (word 136),64)) s =
          val S1 DIV 2 EXP (8 * 136)
        ==> read (memory :> bytes(a,135)) s =
              val(word_xor S1 (word(2 EXP (8 * r) * 31))) MOD 2 EXP (8 * 135) /\
            read (memory :> bytes(word_add a (word 136),64)) s =
              val(word_xor S1 (word(2 EXP (8 * r) * 31))) DIV 2 EXP (8 * 136) /\
            (val(word_xor S1 (word(2 EXP (8 * r) * 31))) DIV 2 EXP (8 * 135)) MOD 256 =
            (val S1 DIV 2 EXP (8 * 135)) MOD 256`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(SPECL [`a:int64`; `S1:1600 word`; `31`; `r:num`; `s:armstate`] SPONGE2_XOR_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`S1:1600 word`; `31`; `r:num`; `1`] XOR_HIGH) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`S1:1600 word`; `31`; `r:num`; `136 - r`] XOR_HIGH) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r + (136 - r) = 136` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`S1:1600 word`; `31`; `r:num`; `135 - r`] XOR_CHUNK_1) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r + (135 - r) = 135` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `31 DIV 2 EXP (8 * (135 - r)) = 0` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `0 MOD 256 = 0`; WORD_XOR_0; ARITH_RULE `2 EXP (8 * 1) = 256`; MULT_CLAUSES] THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD; DIMINDEX_8; ARITH_RULE `2 EXP 8 = 256`; MOD_MOD_REFL]) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`a:int64`; `r + 1`; `134 - r`; `val(word_xor S1 (word (2 EXP (8 * r) * 31)):1600 word)`; `s:armstate`] READ_MEMORY_BYTES_EXTEND) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r + 1) + (134 - r) = 135` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let SPONGE2_PAD135 = prove
 (`!(a:int64) (S1:1600 word) (s:armstate).
        read (memory :> bytes(a,135)) s = val S1 MOD 2 EXP (8 * 135) /\
        read (memory :> bytes8(word_add a (word 135))) s =
          word_xor (word_xor (word((val S1 DIV 2 EXP (8 * 135)) MOD 256)) (word 31)) (word 128) /\
        read (memory :> bytes(word_add a (word 136),64)) s =
          val S1 DIV 2 EXP (8 * 136)
        ==> read (memory :> bytes(a,200)) s =
            val(word_xor (word_xor S1 (word(2 EXP (8 * 135) * 31))) (word(2 EXP (8 * 135) * 128)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `(word_xor S1 (word(2 EXP (8 * 135) * 31))):1600 word`; `s:armstate`] SPONGE2_PAD2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`S1:1600 word`; `31`; `135`] XOR_LOW) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`S1:1600 word`; `31`; `135`; `0`] XOR_CHUNK_1) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; DIV_1; EXP; MULT_CLAUSES; ARITH_RULE `31 MOD 256 = 31`; ARITH_RULE `2 EXP 8 = 256`] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[WORD_VAL];
      MP_TAC(SPECL [`S1:1600 word`; `31`; `135`; `1`] XOR_HIGH) THEN
      ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `135 + 1 = 136`] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN ACCEPT_TAC]);;

(*** The bytes of the state above 136 are the number from there on ***)

let SPONGE2_HIGH_MOD = prove
 (`!S:1600 word. (val S DIV 2 EXP (8 * 136)) MOD 2 EXP (8 * 64) =
                 val S DIV 2 EXP (8 * 136)`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The padding and the final permutation (from join4, after the last block   *)
(* has been XORed in, to after_mldsa_keccakf1600_permute_2): the state       *)
(* after r = mlen MOD 136 bytes of the last block is S1; the code stores the *)
(* position 136 in the field after the state (sp + 264), XORs 0x1f at byte r *)
(* and 0x80 at byte 135, and permutes: the state is then the permutation of  *)
(* mld_keccak_finalize 136 0x1f S1 r, the state of the model before the      *)
(* squeezing. The register PR holds the address of the state (sp + 64) after *)
(* the padding, which the code sets, and LR the position r.                  *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_FIN_STMT fn pr lr = parse_term(Printf.sprintf
 "exists f_events. forall e (S1:1600 word) r sp pc.
   r < 136 /\\ aligned 16 sp /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (word_sub sp (word 240),508) (word pc,libmldsa_size)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read PC s = word (pc + %s_join4) /\\ read SP s = sp /\\
          read %s s = word r /\\
          read (memory :> wbytes (word_add sp (word 64))) s = S1 /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s_after_mldsa_keccakf1600_permute_2) /\\
          read SP s = sp /\\ read %s s = word r /\\
          read %s s = word_add sp (word 64) /\\
          read (memory :> wbytes (word_add sp (word 64))) s =
            keccak_f1600 (mld_keccak_finalize 136 31 S1 r) /\\
          read (memory :> bytes32 (word_add sp (word 264))) s = word 136 /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events r sp pc /\\
             memaccess_inbounds e2
              [word_add sp (word 64),204; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add sp (word 64),204; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add sp (word 64),204);
                memory :> bytes(word_sub sp (word 240),240)])"
  fn lr fn lr pr pr);;

(*** The pieces of the state: bytes of the number val S1 after k, and a byte ***)

let SPONGE2_PIECE_SIDE tm =
  MP (ARITH_RULE (mk_imp(`r < 136`, tm))) (ASSUME `r < 136`);;

let SPONGE2_FIN_ST = `read (memory :> bytes(word_add sp (word 64),200)) (s0:armstate) = val (S1:1600 word)`;;

let SPONGE2_FIN_BYTES_PIECE k l =
  FIRST_ASSUM(fun th -> if concl th = SPONGE2_FIN_ST then
    let side = SPONGE2_PIECE_SIDE
      (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k l) `200`) in
    let f = MP (SPECL [`word_add sp (word 64):int64`; `200`; `val(S1:1600 word)`;
                       k; l; `s0:armstate`] SPONGE2_BYTES_SUB) (CONJ th side) in
    ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)
  else NO_TAC);;

let SPONGE2_FIN_BYTE_PIECE k def =
  FIRST_ASSUM(fun th -> if concl th = SPONGE2_FIN_ST then
    let side = SPONGE2_PIECE_SIDE (mk_binop `(<):num->num->bool` k `200`) in
    let f = MP (SPECL [`word_add sp (word 64):int64`; `200`; `val(S1:1600 word)`;
                       k; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) (CONJ th side) in
    FIRST_ASSUM(fun d -> if concl d = def then
      let f = REWRITE_RULE[d] f in
      let f = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) f in
      ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f) else NO_TAC)
  else NO_TAC);;

(*** The byte that the simulation stores, a chain of zero extensions of the
     byte b with constants XORed in, as that XOR of b (mkt b) ***)

let SPONGE2_IS_BYTE8 sname a l =
  string_of_term l = "read (memory :> bytes8 (" ^ a ^ ")) " ^ sname;;

let SPONGE2_CHAIN_FIX_TAC sname a base mkt =
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) ->
      try SPONGE2_IS_BYTE8 sname a (lhs(concl th)) &&
          can (find_term (fun t -> try fst(dest_const t) = "word_zx" with _ -> false)) (rhs(concl th))
      with _ -> false) asl) in
    let b = mk_var("b",`:byte`) in
    let rhs' = subst [b,base] (rhs(concl th)) in
    let eq = prove(mk_eq(rhs',mkt b),CONV_TAC WORD_BLAST) in
    ASSUME_TAC (REWRITE_RULE[GEN b eq] th));;

let SPONGE2_FIN_NORM_TAC =
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
           DEPTH_CONV NUM_ADD_CONV);;

(*** The state after the stores, from the lemmas on the pieces ***)

let SPONGE2_FIN_STATE_TAC =
  (*** r = 135 ***)
  MP_TAC(SPECL [`word_add sp (word 64):int64`; `S1:1600 word`; `s12:armstate`]
                SPONGE2_PAD135) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE2_HIGH_MOD]) THEN SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

(*** r < 135: the byte r is XORed with 0x1f and the byte 135 with 0x80 ***)

let SPONGE2_FIN_STATE2_TAC =
  MP_TAC(SPECL [`word_add sp (word 64):int64`; `S1:1600 word`; `r:num`;
                `s12:armstate`] SPONGE2_PAD1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE2_HIGH_MOD]) THEN SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte = b1` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(SPECL [`word_add sp (word 64):int64`;
                `word_xor S1 (word (2 EXP (8 * r) * 31)):1600 word`;
                `s12:armstate`] SPONGE2_PAD2) THEN
  SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if is_eq(concl d) && is_binary "MOD" (lhs(concl d)) &&
      can (find_term (fun t -> t = `word_xor:1600 word->1600 word->1600 word`)) (concl d)
    then REWRITE_TAC[d] else NO_TAC) THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

let SPONGE2_FIN_CALL_TAC exec rt =
  let sb = vsubst [rt,`r:num`] in
  SUBGOAL_THEN (sb `read (memory :> wbytes (word_add sp (word 64))) (s12:armstate) =
                mld_keccak_finalize 136 31 (S1:1600 word) r`) ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_1600; mld_keccak_finalize; ARITH_RULE `136 - 1 = 135`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERMUTE"
   [`word_add sp (word 64):int64`; sb `mld_keccak_finalize 136 31 (S1:1600 word) r`;
    `pc:num`; `sp:int64`; `read X30 s12`]
   [rt; `sp:int64`; `pc:num`] 13 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC; MONOTONE_MAYCHANGE_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

let SPONGE2_FIN_TAC fn pr lr =
  let exec = SPONGE2_L1_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE2_RENAME_E2
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(r:num) (sp:int64) (pc:num).
      if r = 135 then f_ev_a r sp pc else f_ev_b r sp pc
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `S1:1600 word`; `r:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add sp (word 64),200)) (s0:armstate) = val (S1:1600 word)`
   ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `read (memory :> wbytes (word_add sp (word 64))) (s0:armstate) = (S1:1600 word)` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600]; ALL_TAC] THEN
  ABBREV_TAC `b135 = word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte` THEN
  ASM_CASES_TAC `r = 135` THENL
   [(*** r = 135: both bytes are the byte 135 ***)
    FIRST_X_ASSUM(fun th -> if concl th = `r = 135` then SUBST_ALL_TAC th else NO_TAC) THEN
    REWRITE_TAC[] THEN
    SPONGE2_FIN_BYTES_PIECE `0` `135` THEN SPONGE2_FIN_BYTES_PIECE `136` `64` THEN
    SPONGE2_FIN_BYTE_PIECE `135` `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 0 = 0`; EXP; DIV_1]) THEN
    ARM_STEPS_TAC exec (1--12) THEN
    SPONGE2_CHAIN_FIX_TAC "s12" "word_add sp (word 199)" `b135:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,
         mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 31:byte`)),`word 128:byte`)) THEN
    SPONGE2_FIN_STATE_TAC THEN
    SPONGE2_FIN_CALL_TAC exec `135`;

    (*** r < 135 ***)
    SUBGOAL_THEN `r < 135` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `b1 = word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte` THEN
    SPONGE2_FIN_BYTES_PIECE `0` `r:num` THEN SPONGE2_FIN_BYTES_PIECE `r + 1` `134 - r` THEN
    SPONGE2_FIN_BYTES_PIECE `136` `64` THEN
    SPONGE2_FIN_BYTE_PIECE `135` `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` THEN
    SPONGE2_FIN_BYTE_PIECE `r:num` `word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte = b1` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 0 = 0`; EXP; DIV_1]) THEN
    ARM_STEPS_TAC exec (1--12) THEN
    SPONGE2_CHAIN_FIX_TAC "s12" "word_add sp (word (64 + r))" `b1:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 31:byte`)) THEN
    SPONGE2_CHAIN_FIX_TAC "s12" "word_add sp (word 199)" `b135:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 128:byte`)) THEN
    SPONGE2_FIN_STATE2_TAC THEN
    SPONGE2_FIN_CALL_TAC exec `r:num`];;

let PROVE_SPONGE2_FIN fn pr lr = prove(SPONGE2_FIN_STMT fn pr lr, SPONGE2_FIN_TAC fn pr lr);;

(* ------------------------------------------------------------------------- *)
(* The XOR of the rest of the message, r = mlen MOD 136 < 136 bytes at the   *)
(* register PR, into the state at sp + 64 (from loop1_exit to join4, the     *)
(* label where the padding starts). The code runs the loop over blocks of 32 *)
(* bytes (loop3), then that over blocks of 8 bytes (loop4) and then that     *)
(* over single bytes (loop2), each of them only if bytes are left for it,    *)
(* and each is the lemma of inline_sponge.ml. The checks of the code that    *)
(* the data and the state do not overlap are decided by the assumption       *)
(* that they do not, and that the state is below 2^63.                       *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_TAIL_STMT fn pr lr = parse_term(Printf.sprintf
 "exists f_events. forall e d r R (S1:1600 word) sp pc.
   r < 136 /\\ aligned 16 sp /\\ val sp + 464 < 2 EXP 63 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (d,r) (word_add sp (word 64),200) /\\
   nonoverlapping (word_add sp (word 64),200) (word pc,libmldsa_size)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read PC s = word (pc + %s_loop1_exit) /\\ read SP s = sp /\\
          read %s s = d /\\ read %s s = word r /\\
          read (memory :> bytes(d,r)) s = R /\\
          read (memory :> wbytes (word_add sp (word 64))) s = S1 /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s_join4) /\\ read SP s = sp /\\
          read %s s = d /\\ read %s s = word r /\\
          read (memory :> bytes(d,r)) s = R /\\
          read (memory :> wbytes (word_add sp (word 64))) s =
            word_xor S1 (word R) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d r sp pc /\\
             memaccess_inbounds e2
              [d,r; word_add sp (word 64),200]
              [word_add sp (word 64),200]))
    (MAYCHANGE [PC] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add sp (word 64),200)])"
  fn pr lr fn pr lr);;

(*** Specialize a hypothesis for a loop lemma to its arguments, simplified ***)

let SPONGE2_SIMP =
  REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0; SUB_0];;

let SPONGE2_SPEC_HYP name newname args =
  USE_THEN name (fun th ->
    let e0 = `e0:(uarch_event)list` in
    LABEL_TAC newname
      (GEN e0 (SPONGE2_SIMP (SPECL (e0::args) th))));;

(* ------------------------------------------------------------------------- *)
(* The check of the code that the rest of the message and the state do not   *)
(* overlap, before it uses the vector loops: if the regions do not overlap   *)
(* (modulo 2^64), one is above the other, and the carry flag of the          *)
(* comparison that the code makes is set, so that it takes the branch.       *)
(* ------------------------------------------------------------------------- *)

let SPONGE2_NOOV_DISJ = prove
 (`!(d:int64) (a:int64) r.
        0 < r /\ r <= 200 /\
        nonoverlapping_modulo (2 EXP 64) (val d,r) (val a,200)
        ==> val a + r <= val d \/ val d + r <= val a`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN
  DISCH_TAC THEN ASM_CASES_TAC `val(a:int64) + r <= val(d:int64)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `val(d:int64) + r <= val(a:int64)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `val(a:int64) <= val(d:int64)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `val(d:int64) - val(a:int64)`]) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(d:int64) + 0 = val(a:int64) + (val d - val a)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ASM_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPECL [`val(a:int64) - val(d:int64)`; `0`]) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(d:int64) + (val a - val d) = val(a:int64) + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;


let SPONGE2_NOOV_CF = prove
 (`!(a:int64) (d:int64) r.
        0 < r /\ r <= 200 /\ val a + 400 < 2 EXP 63 /\
        (val a + r <= val d \/ val d + r <= val a)
        ==> (if val d < val(word_add a (word r))
             then (&(val a):int) - &(val(word_add d (word r))) =
                  &(val(word_sub a (word_add d (word r))))
             else T)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word_add a (word r):int64) = val a + r` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN
   (SUBGOAL_THEN `val(d:int64) + r <= val(a:int64)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add d (word r):int64) = val d + r` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MOD_LT THEN MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:int64`; `word_add d (word r):int64`] VAL_WORD_SUB_CASES) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    SUBGOAL_THEN `~(val(a:int64) < val(d:int64) + r)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC));;
