(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The SHAKE256 of pk that clang 23 -O3 has inlined into                      *)
(* mldsa{44,65,87}_verify_internal for tr = H(pk, 64), from                    *)
(* in_shake256_init to the bl of mld_H: the state at F + a is zeroed and the *)
(* bytes of pk are XORed into it, 17 lanes of 64 bits at a time, with a call *)
(* of keccakf1600_permute after each full block; then the rest of pk, the    *)
(* padding bytes 0x1F and 0x80, the permutation, the copy of the first 64    *)
(* bytes of the state to tr at F + t, the arguments of mld_H and the zeroing *)
(* of the state. The lemma is generated for each instance (shake_inst: the   *)
(* function, the length of pk, the offsets, the registers, the steps of the  *)
(* calls and the loads and stores of the last block).                        *)
(*                                                                           *)
(* The proof keeps the state as a 1600-bit word at each call (wbytes), takes *)
(* its 25 lanes after each call (SHAKE_WBYTES_SUB) and assembles the next    *)
(* state from the lanes the code stores (SHAKE_WBYTES_OF_LANES, each lane by *)
(* bit-blasting on the lanes of pk, which are abbreviated as variables). In  *)
(* the last block, the 16-byte stores are split into lanes                    *)
(* (SHAKE_SPLIT128), the 16-byte loads of pk are joins of lanes, and the     *)
(* lanes that take the padding bytes are rebuilt from their bytes            *)
(* (SHAKE_BYTES64_OF_BYTES8). The states are those of mld_shake256_state     *)
(* (SHAKE_STATE_EQ), and the 64 bytes of tr are mld_shake256_byte            *)
(* (SHAKE_OUT_EQ).                                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* Lanes of a number in memory.                                              *)
(* ------------------------------------------------------------------------- *)

let SHAKE_LANE_OF_BYTES = prove
 (`!(a:int64) k x n s.
        read (memory :> bytes(a,k)) s = x /\ 8 * n + 8 <= k
        ==> read (memory :> bytes64(word_add a (word(8 * n)))) s =
            word((x DIV 2 EXP (64 * n)) MOD 2 EXP 64)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `64 * n = 8 * 8 * n`;
              ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (k - 8 * n) 8 = 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let SHAKE_BYTES_OF_LANES = prove
 (`!(a:int64) x n s.
        (!i. i < n
             ==> read (memory :> bytes64(word_add a (word(8 * i)))) s =
                 word((x DIV 2 EXP (64 * i)) MOD 2 EXP 64))
        ==> read (memory :> bytes(a,8 * n)) s = x MOD 2 EXP (64 * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * n = 64 * n`] THEN
  REWRITE_TAC[ARITH_RULE `64 * SUC n = 64 * n + 64`; EXP_ADD;
              MOD_MULT_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;


(*** Pieces of a state known as a 1600-bit word, and its lanes ***)

(*** Reading pieces of a state known as a 1600-bit word ***)

let SHAKE_WBYTES_SUB = prove
 (`!(a:int64) (St:1600 word) s k.
        read (memory :> wbytes a) s = St
        ==> (k + 8 <= 200
             ==> read (memory :> bytes64(word_add a (word k))) s =
                 word_subword St (8 * k,64)) /\
            (k + 1 <= 200
             ==> read (memory :> bytes8(word_add a (word k))) s =
                 word_subword St (8 * k,8)) /\
            (k + 16 <= 200
             ==> read (memory :> bytes128(word_add a (word k))) s =
                 word_subword St (8 * k,128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; READ_COMPONENT_COMPOSE] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; BYTES64_WBYTES; BYTES8_WBYTES;
              BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8; DIMINDEX_64; DIMINDEX_128;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (8 * 8)`;
              ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`;
              ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The state from its 25 lanes ***)

let SHAKE_WBYTES_OF_LANES = prove
 (`!(a:int64) (St:1600 word) s.
        (!j. j < 25
             ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                 word_subword St (64 * j,64))
        ==> read (memory :> wbytes a) s = St`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  MP_TAC(SPECL [`a:int64`; `val(St:1600 word)`; `25`; `s:armstate`]
         SHAKE_BYTES_OF_LANES) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `j < 25`)]) THEN
    REWRITE_TAC[word_subword] THEN AP_TERM_TAC THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `St:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]);;

(*** Lane j of the state after XORing a block (of 136 bytes, the 17 lanes ***)
(*** of a number X from bit n on) into it                                 ***)

let SHAKE_BLOCK_NUM = prove
 (`!X n j. j < 17
           ==> (((X DIV 2 EXP n) MOD 2 EXP 1088) DIV 2 EXP (64 * j)) MOD
               2 EXP 64 =
               (X DIV 2 EXP (n + 64 * j)) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `MIN (n + 1088) (n + 64 * j + 64) = (n + 64 * j) + 64`
   SUBST1_TAC THENL [ASM_ARITH_TAC; REFL_TAC]);;

let SHAKE_BLOCK_LANE = prove
 (`!(P:1600 word) X n j.
        j < 17
        ==> word_subword (word_xor P (word((X DIV 2 EXP n) MOD 2 EXP 1088)))
                         (64 * j,64):int64 =
            word_xor (word_subword P (64 * j,64))
                     (word((X DIV 2 EXP (n + 64 * j)) MOD 2 EXP 64))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SHAKE_BLOCK_NUM]);;

let SHAKE_BLOCK_LANE_HIGH = prove
 (`!(P:1600 word) X n j.
        17 <= j /\ j < 25
        ==> word_subword (word_xor P (word((X DIV 2 EXP n) MOD 2 EXP 1088)))
                         (64 * j,64):int64 =
            word_subword P (64 * j,64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
   `word_subword (word((X DIV 2 EXP n) MOD 2 EXP 1088):1600 word)
                 (64 * j,64):int64 = word 0`
   (fun th -> REWRITE_TAC[th; WORD_XOR_0]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `((X DIV 2 EXP n) MOD 2 EXP 1088) DIV 2 EXP (64 * j) = 0`
   (fun th -> REWRITE_TAC[th; MOD_0]) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1088` THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let SHAKE_BLOCK_SUB = prove
 (`!X n j.
        j < 17
        ==> word_subword (word((X DIV 2 EXP n) MOD 2 EXP 1088):1600 word)
                         (64 * j,64):int64 =
            word((X DIV 2 EXP (n + 64 * j)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SHAKE_BLOCK_NUM]);;

let SHAKE_BLOCK_SUB_HIGH = prove
 (`!X n j.
        17 <= j /\ j < 25
        ==> word_subword (word((X DIV 2 EXP n) MOD 2 EXP 1088):1600 word)
                         (64 * j,64):int64 = word 0`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `((X DIV 2 EXP n) MOD 2 EXP 1088) DIV 2 EXP (64 * j) = 0`
   (fun th -> REWRITE_TAC[th; MOD_0]) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1088` THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let SHAKE_PK_HIGH = prove
 (`!X n m. X < 2 EXP n /\ n <= m
           ==> word((X DIV 2 EXP m) MOD 2 EXP 64):int64 = word 0`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `X DIV 2 EXP m = 0` (fun th -> REWRITE_TAC[th; MOD_0]) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP n` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

(*** The subword rules of lane j for the block at bit n ***)

let SHAKE_LANE_RULES n j =
  let jt = mk_small_numeral j and nt = mk_small_numeral n in
  let conv = DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV) in
  if j < 17 then
    CONV_RULE conv (MP (SPECL [`PK:num`; nt; jt] SHAKE_BLOCK_SUB)
                       (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` jt `17`))))
  else
    CONV_RULE conv (MP (SPECL [`PK:num`; nt; jt] SHAKE_BLOCK_SUB_HIGH)
       (EQT_ELIM(NUM_REDUCE_CONV(mk_conj(mk_binop `(<=):num->num->bool` `17` jt,
                                        mk_binop `(<):num->num->bool` jt `25`)))));;

(*** A 64-bit word in memory from its 8 bytes ***)

let SHAKE_NUM_OF_BYTES64 = prove
 (`!(x:int64) n.
        n <= 8
        ==> num_of_bytelist(list_of_seq (\i. word_subword x (8 * i,8)) n) =
            val x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `SUC n <= 8 ==> n <= 8`] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD_SUBWORD; DIMINDEX_8;
              ARITH_RULE `MIN 8 8 = 8`] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let SHAKE_BYTES64_OF_BYTES8 = prove
 (`!(a:int64) (x:int64) s.
        (!t. t < 8
             ==> read (memory :> bytes8(word_add a (word t))) s =
                 word_subword x (8 * t,8))
        ==> read (memory :> bytes64 a) s = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `8`; `\t. (word_subword (x:int64) (8 * t,8)):byte`;
                `s:armstate`] READ_BYTES_OF_BYTES8) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SHAKE_NUM_OF_BYTES64; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[]);;

let SHAKE_READ_BYTES_BOUND = prove
 (`!a n (s:armstate) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let SHAKE_ZERO128_SUB = prove
 (`!(a:int64) s.
     read (memory :> bytes128 a) s = word 0
     ==> read (memory :> bytes64 a) s = word 0 /\
         read (memory :> bytes64 (word_add a (word 4))) s = word 0 /\
         read (memory :> bytes64 (word_add a (word 8))) s = word 0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_WORD_0; BYTES128_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 8 ==> read (bytes(word_add a (word k),8)) (read memory s) = 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:int64`; `16`; `k:num`; `read memory s`]
                  READ_BYTES_DIV) THEN
    ASM_REWRITE_TAC[DIV_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * 8)`) THEN
    REWRITE_TAC[MOD_0; READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN (16 - k) 8 = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_0; BYTES64_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  TRY(FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[WORD_ADD_0; LE_0] THEN NO_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;


(*** A 128-bit store as its two lanes ***)

let SHAKE_SPLIT128 = prove
 (`!(a:int64) (v:int128) s.
        read (memory :> bytes128 a) s = v
        ==> read (memory :> bytes64 a) s = word_subword v (0,64) /\
            read (memory :> bytes64 (word_add a (word 8))) s =
            word_subword v (64,64)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The instances. The region goes from in_shake256_init to the bl of mld_H   *)
(* (the label sh_stop is the instruction after the bl). The state is at      *)
(* fp + sh_a and tr at fp + sh_t; keccakf1600_permute uses the 240 bytes     *)
(* below fp. sh_calls are the steps of the bl of the blocks and of the last  *)
(* permutation; in the last block the code loads the bytes sh_last_bytes and *)
(* the 16-byte chunks sh_last_chunks of the state and the 16-byte chunks     *)
(* sh_pk128 of pk, stores 16-byte chunks at sh_split, and the lanes at       *)
(* sh_rebuild take a padding byte (they are rebuilt from their bytes).       *)
(* sh_vars, sh_pre, sh_post, sh_reads and sh_mods are the parts of the       *)
(* statement that depend on the registers of the instance.                   *)
(* ------------------------------------------------------------------------- *)

type shake_inst =
  { sh_fn : string; sh_start : string; sh_stop : string; sh_pklen : int;
    sh_a : int; sh_t : int;
    sh_vars : string; sh_pre : string; sh_post : string; sh_reads : string;
    sh_mods : string; sh_calls : int list; sh_last_bytes : int list;
    sh_last_chunks : int list; sh_pk128 : int list; sh_split : int list;
    sh_rebuild : int list; sh_steps : int };;

let SHAKE_NB p = p.sh_pklen / 136;;
let SHAKE_REM p = p.sh_pklen mod 136;;

let SHAKE_START p = layout (p.sh_fn ^ "_" ^ p.sh_start);;
let SHAKE_STOP p = layout (p.sh_fn ^ "_" ^ p.sh_stop) - 4;;

(*** The exec theorem of the region, decoded once per function ***)

let SHAKE_EXEC_CACHE = ref [];;

let SHAKE_EXEC p =
  try assoc p.sh_fn (!SHAKE_EXEC_CACHE) with Failure _ ->
  let th =
    ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(SHAKE_START p,SHAKE_STOP p); layout_range "mldsa_keccakf1600_permute"] in
  SHAKE_EXEC_CACHE := (p.sh_fn,th) :: (!SHAKE_EXEC_CACHE); th;;

let INLINE_SHAKE_TERM p =
  let fr = 240 + p.sh_t + 64 in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) (pk:int64) PK %s pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (word_sub fp (word 240),%d) (word pc,libmldsa_size) /\\
      nonoverlapping (word_sub fp (word 240),%d) (pk,%d)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = fp /\\ read X20 s = pk /\\ %s
                read (memory :> bytes(pk,%d)) s = PK /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                read (memory :> bytes(word_add fp (word %d),64)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte %d PK) 64) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pk pc /\\
                   memaccess_inbounds e2
                    [pk,%d; word_add fp (word %d),208;
                     word_add fp (word %d),64; word_sub fp (word 240),240;
                     %sword(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_add fp (word %d),208; word_add fp (word %d),64;
                     word_sub fp (word 240),240]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [%s] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word %d),208);
                       memory :> bytes(word_add fp (word %d),64);
                       memory :> bytes(word_sub fp (word 240),240)])"
  p.sh_vars fr fr p.sh_pklen (SHAKE_START p) p.sh_pre p.sh_pklen
  (SHAKE_STOP p) p.sh_post p.sh_t p.sh_pklen p.sh_pklen p.sh_a p.sh_t
  p.sh_reads p.sh_a p.sh_t p.sh_mods p.sh_a p.sh_t);;

(*** The states: the blocks of pk, the state at the k-th call, the final ***)

let SHAKE_XOR = `word_xor:1600 word->1600 word->1600 word`;;

let SHAKE_B k =
  subst [mk_small_numeral(1088 * k),`n:num`]
   `word((PK DIV 2 EXP n) MOD 2 EXP 1088):1600 word`;;

let rec SHAKE_T k =
  if k = 0 then list_mk_comb(SHAKE_XOR,[`word 0:1600 word`; SHAKE_B 0])
  else list_mk_comb(SHAKE_XOR,
         [mk_comb(`keccak_f1600`,SHAKE_T(k - 1)); SHAKE_B k]);;

let SHAKE_PAD1 p =
  subst [mk_small_numeral(8 * SHAKE_REM p),`n:num`]
   `word(2 EXP n * 31):1600 word`;;

let SHAKE_FINAL p =
  list_mk_comb(SHAKE_XOR,
   [list_mk_comb(SHAKE_XOR,[SHAKE_T (SHAKE_NB p); SHAKE_PAD1 p]);
    `word(2 EXP 1080 * 128):1600 word`]);;

let SHAKE_ABSORB_CONV =
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Comb(Const("mld_keccak_absorb_blocks",_),_),_),_),n)
        when is_numeral n && dest_numeral n <>/ num 0 ->
        (RAND_CONV num_CONV THENC
         REWR_CONV(CONJUNCT2 mld_keccak_absorb_blocks) THENC
         RAND_CONV(LAND_CONV conv)) tm
    | Comb(Comb(Comb(Comb(Const("mld_keccak_absorb_blocks",_),_),_),_),n)
        when is_numeral n ->
        REWR_CONV(CONJUNCT1 mld_keccak_absorb_blocks) tm
    | _ -> failwith "SHAKE_ABSORB_CONV" in
  conv;;

let SHAKE_STATE_EQ p =
  prove
   (mk_eq(mk_comb(mk_comb(`mld_shake256_state`,mk_small_numeral p.sh_pklen),
                  `PK:num`),
          SHAKE_FINAL p),
    REWRITE_TAC[mld_shake256_state; mld_keccak_absorb; mld_keccak_finalize] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
    CONV_TAC(DEPTH_CONV(NUM_DIV_CONV ORELSEC NUM_MOD_CONV)) THEN
    CONV_TAC(ONCE_DEPTH_CONV SHAKE_ABSORB_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_SUB_CONV)) THEN
    REWRITE_TAC[MULT_CLAUSES; EXP]);;

let SHAKE_OUT_EQ p =
  let n = mk_small_numeral p.sh_pklen in
  let steq = SHAKE_STATE_EQ p in
  prove
   (subst [SHAKE_FINAL p,`S:1600 word`; n,`n:num`]
     `num_of_bytelist(list_of_seq (mld_shake256_byte n PK) 64) =
      val(keccak_f1600 S) MOD 2 EXP 512`,
    MP_TAC(SPECL [`136`; list_mk_comb(`mld_shake256_state`,[n;`PK:num`]);
                  `136`; `0`; `1`; `0`; `64`] SQUEEZE_CHUNK) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1; ETA_AX;
                ARITH_RULE `8 * 64 = 512`] THEN
    REWRITE_TAC[GSYM mld_shake256_byte] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[num_CONV `1`; keccak_squeeze] THEN
    REWRITE_TAC[steq; EXP; DIV_1; MULT_CLAUSES]);;

(*** The facts about pk at the start: its lanes (abbreviated as pkw<n>), the ***)
(*** lanes beyond it in the last block (zero) and its 16-byte chunks that   ***)
(*** the last block loads, as joins of two lanes                            ***)

let SHAKE_PK_LANES_TAC p =
  let pkfact = subst [mk_small_numeral p.sh_pklen,`n:num`]
                 `read (memory :> bytes(pk,n)) s0 = PK` in
  FIRST_ASSUM(fun th ->
    if concl th <> pkfact then NO_TAC else
    MAP_EVERY (fun i ->
      let k = mk_small_numeral(8 * i) in
      let th1 = SPECL [`pk:int64`; mk_small_numeral p.sh_pklen; `PK:num`; k;
                       `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
      let th2 = MP th1 (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl th1)))))) in
      ASSUME_TAC(REWRITE_RULE[WORD_ADD_0]
        (CONV_RULE(DEPTH_CONV NUM_MULT_CONV) th2))) (0--(p.sh_pklen / 8 - 1)));;

let SHAKE_PK_ABBREV_TAC p =
  MAP_EVERY (fun i ->
    let m = mk_small_numeral(64 * i) in
    let tm = subst [m,`m:num`] `word((PK DIV 2 EXP m) MOD 2 EXP 64):int64` in
    ABBREV_TAC (mk_eq(mk_var("pkw"^string_of_int i,`:int64`),tm)))
   (0--(p.sh_pklen / 8 - 1));;

let SHAKE_PK_BOUND_TAC p =
  let nb = mk_small_numeral(8 * p.sh_pklen) in
  let pkfact = subst [mk_small_numeral p.sh_pklen,`n:num`]
                 `read (memory :> bytes(pk,n)) s0 = PK` in
  FIRST_ASSUM(fun th ->
    if concl th <> pkfact then NO_TAC else
    let bth = CONV_RULE(DEPTH_CONV NUM_MULT_CONV)
               (MATCH_MP SHAKE_READ_BYTES_BOUND th) in
    MAP_EVERY (fun t ->
      let m = mk_small_numeral(8 * p.sh_pklen + 64 * t) in
      ASSUME_TAC(MP (SPECL [`PK:num`; nb; m] SHAKE_PK_HIGH)
                    (CONJ bth (EQT_ELIM(NUM_REDUCE_CONV
                       (mk_binop `(<=):num->num->bool` nb m))))))
     (0--(16 - SHAKE_REM p / 8)));;

let SHAKE_PK128_TAC p =
  W(fun (asl,w) ->
    let lanes = mapfilter (fun (_,a) ->
      let c = concl a in
      if is_eq c && can (term_match []
           `read (memory :> bytes64 (word_add pk (word k))) s0`) (lhs c)
      then a else fail()) asl in
    MAP_EVERY (fun k ->
      let a = subst [mk_small_numeral k,`k:num`] `word_add (pk:int64) (word k)` in
      let tm = subst [a,`a:int64`] `read (memory :> bytes128 a) s0` in
      let th = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                (GEN_REWRITE_CONV I [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm) in
      ASSUME_TAC(REWRITE_RULE lanes th)) p.sh_pk128);;

(*** Lanes (and some bytes and 16-byte chunks) of the state from wbytes ***)

let SHAKE_A p = mk_comb(`word_add (fp:int64)`,
                        mk_comb(`word:num->int64`,mk_small_numeral p.sh_a));;

let SHAKE_STATE_FACTS_TAC p s lanes bytes chunks =
  let st = subst [s,`s:armstate`; SHAKE_A p,`a:int64`]
             `read (memory :> wbytes (a:int64)) s :1600 word` in
  FIRST_ASSUM(fun th ->
    if not(is_eq(concl th) && lhs(concl th) = st) then NO_TAC else
    let sub = MATCH_MP SHAKE_WBYTES_SUB th in
    let mk sel k =
      let th1 = sel(SPEC (mk_small_numeral k) sub) in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th2 in
    MAP_EVERY ASSUME_TAC
     (map (fun j -> mk CONJUNCT1 (8 * j)) lanes @
      map (fun k -> mk (CONJUNCT1 o CONJUNCT2) k) bytes @
      map (fun k -> mk (CONJUNCT2 o CONJUNCT2) k) chunks));;

(*** Abbreviate the state after a permutation ***)

let SHAKE_ABBREV_STATE_TAC p name s =
  let st = subst [s,`s:armstate`; SHAKE_A p,`a:int64`]
             `read (memory :> wbytes (a:int64)) s :1600 word` in
  FIRST_ASSUM(fun th ->
    if not(is_eq(concl th) && lhs(concl th) = st) then NO_TAC else
    ABBREV_TAC (mk_eq(mk_var(name,`:1600 word`),rhs(concl th))));;

(*** The subwords of the blocks and of constants in the lanes of targets ***)

let SHAKE_SUB_CONV tm =
  match tm with
    Comb(Comb(Const("word_subword",_),Comb(Const("word",_),body)),pair) ->
      (try
         let p = dest_small_numeral(fst(dest_pair pair)) in
         let x = lhand(lhand body) and n = rand(rand(lhand body)) in
         if x = `PK:num` && rand body = `2 EXP 1088` && p mod 64 = 0 &&
            snd(dest_pair pair) = `64`
         then let th = SHAKE_LANE_RULES (dest_small_numeral n) (p / 64) in
              if lhs(concl th) = tm then th else failwith "SHAKE_SUB_CONV"
         else failwith "SHAKE_SUB_CONV"
       with Failure _ ->
         if frees body = [] then CHANGED_CONV WORD_REDUCE_CONV tm
         else failwith "SHAKE_SUB_CONV")
  | _ -> failwith "SHAKE_SUB_CONV";;

let SHAKE_EQ_TAC =
  W(fun (asl,w) ->
    let eqs = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && type_of(lhs c) = `:int64` &&
         can (term_match [] `word((PK DIV 2 EXP m) MOD 2 EXP 64):int64`) (lhs c)
      then th else fail()) asl in
    CONV_TAC(BINOP_CONV(REWRITE_CONV[WORD_SUBWORD_XOR] THENC
                        TOP_DEPTH_CONV SHAKE_SUB_CONV)) THEN
    REWRITE_TAC eqs THEN REWRITE_TAC[WORD_XOR_0] THEN
    (REFL_TAC ORELSE W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))));;

let SHAKE_LANE_TAC =
  W(fun (asl,w) ->
    let l = lhs w in
    let fth = snd(find (fun (_,th) -> let c = concl th in
                          is_eq c && lhs c = l) asl) in
    GEN_REWRITE_TAC LAND_CONV [fth] THEN SHAKE_EQ_TAC);;

let SHAKE_ASSEMBLE_TAC p tgt s =
  SUBGOAL_THEN (subst [s,`s:armstate`; tgt,`St:1600 word`; SHAKE_A p,`a:int64`]
    `read (memory :> wbytes (a:int64)) s = (St:1600 word)`)
   ASSUME_TAC THENL
   [MATCH_MP_TAC SHAKE_WBYTES_OF_LANES THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REPEAT CONJ_TAC THEN SHAKE_LANE_TAC;
    ALL_TAC];;

(*** In the first block, the zero stores of 16 bytes into the state as ***)
(*** pairs of lanes (and the store at a + 188 as the lane at a + 192)  ***)

let SHAKE_SPLIT_TAC p =
  W(fun (asl,w) ->
    let facts = map (concl o snd) asl in
    let ths = flat(mapfilter (fun (_,th) ->
      let c = concl th in
      match c with
        Comb(Comb(Const("=",_),
          Comb(Comb(Const("read",_),
            Comb(Comb(Const(":>",_),Const("memory",_)),
                 Comb(Const("bytes128",_),a))),_)),z)
          when z = `word 0:int128` ->
          let k = dest_small_numeral(rand(rand a)) in
          if not(rand(rator a) = `fp:int64` && p.sh_a <= k && k <= p.sh_a + 192)
          then fail() else
          let cs = CONJUNCTS(CONV_RULE(ONCE_DEPTH_CONV
                     NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (MATCH_MP SHAKE_ZERO128_SUB th)) in
          let sel = if k = p.sh_a + 188 then [el 1 cs] else [el 0 cs; el 2 cs] in
          let nw = filter (fun t -> not(mem (concl t) facts)) sel in
          if nw = [] then fail() else nw
      | _ -> fail()) asl) in
    MAP_EVERY ASSUME_TAC ths);;

(*** In the last block, the 16-byte stores into the state as lanes ***)

let SHAKE_SPLIT_STORES_TAC p s =
  MAP_EVERY (fun k ->
    let a = mk_comb(`word_add (fp:int64)`,
                    mk_comb(`word:num->int64`,mk_small_numeral(p.sh_a + k))) in
    let pat = subst [a,`a:int64`; s,`s:armstate`]
                `read (memory :> bytes128 a) s` in
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if not(is_eq c && lhs c = pat) then NO_TAC else
      STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                        (MATCH_MP SHAKE_SPLIT128 th)))) p.sh_split;;

(*** The call of the permutation at step n with the state tgt; exec is the ***)
(*** exec theorem of the region and vars the arguments of its f_events      ***)

let SHAKE_CALL_WITH_TAC exec vars tgt n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   exec "H_PERM"
   [`read X0 s`; tgt; `pc:num`; `read SP s`; `read X30 s`] vars n;;

let SHAKE_CALL_TAC p =
  SHAKE_CALL_WITH_TAC (SHAKE_EXEC p) [`fp:int64`; `pk:int64`; `pc:num`];;

let SHAKE_PV k = mk_var("P"^string_of_int k,`:1600 word`);;

let SHAKE_TA k =
  list_mk_comb(SHAKE_XOR,
   [(if k = 0 then `word 0:1600 word` else SHAKE_PV k); SHAKE_B k]);;

let SHAKE_TFA p =
  list_mk_comb(SHAKE_XOR,
   [list_mk_comb(SHAKE_XOR,[SHAKE_TA (SHAKE_NB p); SHAKE_PAD1 p]);
    `word(2 EXP 1080 * 128):1600 word`]);;

let SHAKE_SV n = mk_var("s"^string_of_int n,`:armstate`);;

(*** The steps and the call of the middle block k ***)

let SHAKE_BLOCK_WITH_TAC exec call p k =
  let bl0 = el (k - 1) p.sh_calls and bl1 = el k p.sh_calls in
  let sc = SHAKE_SV(bl0 + 1) and sb = SHAKE_SV bl1 in
  SHAKE_ABBREV_STATE_TAC p ("P"^string_of_int k) sc THEN
  SHAKE_STATE_FACTS_TAC p sc (0--24) [] [] THEN
  ARM_STEPS_TAC exec ((bl0 + 2)--bl1) THEN
  SHAKE_ASSEMBLE_TAC p (SHAKE_TA k) sb THEN
  call (SHAKE_TA k) (bl1 + 1);;

let SHAKE_BLOCK_TAC p = SHAKE_BLOCK_WITH_TAC (SHAKE_EXEC p) (SHAKE_CALL_TAC p) p;;

(*** The last block: the lanes that take the padding bytes of the       ***)
(*** finalization, rebuilt from their bytes                              ***)

let SHAKE_REBUILD_TAC p k0 s =
  let a = mk_comb(`word_add (fp:int64)`,
                  mk_comb(`word:num->int64`,mk_small_numeral(p.sh_a + k0))) in
  let x = subst [SHAKE_TFA p,`St:1600 word`; mk_small_numeral(8 * k0),`p:num`]
            `word_subword (St:1600 word) (p,64):int64` in
  SUBGOAL_THEN (subst [a,`a:int64`; x,`x:int64`; s,`s:armstate`]
                 `read (memory :> bytes64 a) s = x`) ASSUME_TAC THENL
   [MATCH_MP_TAC SHAKE_BYTES64_OF_BYTES8 THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN SHAKE_LANE_TAC;
    ALL_TAC];;

let SHAKE_LAST_WITH_TAC exec call p =
  let nb = SHAKE_NB p in
  let c0 = el (nb - 1) p.sh_calls and c1 = el nb p.sh_calls in
  let sc = SHAKE_SV(c0 + 1) and sb = SHAKE_SV c1 in
  SHAKE_ABBREV_STATE_TAC p ("P"^string_of_int nb) sc THEN
  SHAKE_STATE_FACTS_TAC p sc (0--24) p.sh_last_bytes p.sh_last_chunks THEN
  ARM_STEPS_TAC exec ((c0 + 2)--c1) THEN
  SHAKE_SPLIT_STORES_TAC p sb THEN
  MAP_EVERY (fun k -> SHAKE_REBUILD_TAC p k sb) p.sh_rebuild THEN
  SHAKE_ASSEMBLE_TAC p (SHAKE_TFA p) sb THEN
  call (SHAKE_TFA p) (c1 + 1);;

let SHAKE_LAST_TAC p = SHAKE_LAST_WITH_TAC (SHAKE_EXEC p) (SHAKE_CALL_TAC p) p;;

(*** The copy of the first 64 bytes of the state to tr, the zeroing of ***)
(*** the state, and the output as the SHAKE256 of pk                   ***)

let SHAKE_TAIL_WITH_TAC exec p =
  let nb = SHAKE_NB p in
  let c1 = el nb p.sh_calls in
  let sc = SHAKE_SV(c1 + 1) and se = SHAKE_SV p.sh_steps in
  let outeq = SHAKE_OUT_EQ p in
  SHAKE_ABBREV_STATE_TAC p ("P"^string_of_int(nb + 1)) sc THEN
  SHAKE_STATE_FACTS_TAC p sc [] [] [0;16;32;48] THEN
  ARM_STEPS_TAC exec ((c1 + 2)--p.sh_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[outeq] THEN
    W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(rhs c) &&
         (try fst(dest_const(rator(lhs c))) = "keccak_f1600"
          with Failure _ -> false)
      then th else fail()) asl)) THEN
    MP_TAC(SPECL [mk_comb(`word_add (fp:int64)`,
                          mk_comb(`word:num->int64`,mk_small_numeral p.sh_t));
                  mk_comb(`val:1600 word->num`,SHAKE_PV(nb + 1));
                  `4`; se] VERIF_BYTES_OF_BYTES128) THEN
    ANTS_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[word_subword];
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN SIMP_TAC[]];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let SHAKE_TAIL_TAC p = SHAKE_TAIL_WITH_TAC (SHAKE_EXEC p) p;;

(* ------------------------------------------------------------------------- *)
(* The proof: block 0 with the zeroing of the state, the middle blocks, the  *)
(* last block with the padding, and the copy of tr.                          *)
(* ------------------------------------------------------------------------- *)

let INLINE_SHAKE_PROVE p =
  let c0 = hd p.sh_calls in
  prove
   (INLINE_SHAKE_TERM p,
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
     "H_PERM" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(fp:int64) (pk:int64) (pc:num). f_ev_shk fp pk pc :(uarch_event)list` THEN
    META_EXISTS_TAC THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst (SHAKE_EXEC p)] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FULL_INIT_TAC THEN SHAKE_PK_LANES_TAC p THEN
    SHAKE_PK_ABBREV_TAC p THEN SHAKE_PK_BOUND_TAC p THEN SHAKE_PK128_TAC p THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC (SHAKE_EXEC p) [n] THEN SHAKE_SPLIT_TAC p)
     (1--c0) THEN
    SHAKE_ASSEMBLE_TAC p (SHAKE_TA 0) (SHAKE_SV c0) THEN
    SHAKE_CALL_TAC p (SHAKE_TA 0) (c0 + 1) THEN
    MAP_EVERY (SHAKE_BLOCK_TAC p) (1--(SHAKE_NB p - 1)) THEN
    SHAKE_LAST_TAC p THEN SHAKE_TAIL_TAC p);;

(* ------------------------------------------------------------------------- *)
(* The instances of verify_internal.                                          *)
(* ------------------------------------------------------------------------- *)

let SHAKE44_INST =
  { sh_fn = "mldsa44_verify_internal"; sh_start = "in_shake256_init";
    sh_stop = "after_mld_H44_1";
    sh_pklen = 1312; sh_a = 2496; sh_t = 3552;
    sh_vars = "(r21:int64) (r22:int64) (r23:int64) (r24:int64)";
    sh_pre = "read X21 s = r21 /\\ read X22 s = r22 /\\
              read X23 s = r23 /\\ read X24 s = r24 /\\";
    sh_post = "read X0 s = word_add fp (word 8736) /\\ read X1 s = word 64 /\\
               read X2 s = word_add fp (word 3552) /\\ read X3 s = word 64 /\\
               read X4 s = r24 /\\ read X5 s = r22 /\\
               read X6 s = r21 /\\ read X7 s = r23 /\\";
    sh_reads = ""; sh_mods = "X18; X21; X25; X30";
    sh_calls = [74;137;200;264;335;406;477;548;619;674];
    sh_last_bytes = (88--95) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [88;128]; sh_steps = 720 };;

let SHAKE65_INST =
  { sh_fn = "mldsa65_verify_internal"; sh_start = "in_shake256_init";
    sh_stop = "after_mld_H65_1";
    sh_pklen = 1952; sh_a = 2400; sh_t = 3456;
    sh_vars = "(r21:int64) (r23:int64) (r24:int64) (r5:int64)";
    sh_pre = "read X21 s = r21 /\\ read X23 s = r23 /\\ read X24 s = r24 /\\
              read (memory :> bytes64 (word_add fp (word 336))) s = r5 /\\";
    sh_post = "read X0 s = word_add fp (word 9728) /\\ read X1 s = word 64 /\\
               read X2 s = word_add fp (word 3456) /\\ read X3 s = word 64 /\\
               read X4 s = r24 /\\ read X5 s = r5 /\\
               read X6 s = r21 /\\ read X7 s = r23 /\\";
    sh_reads = "word_add fp (word 336),8; "; sh_mods = "X18; X21; X25; X30";
    sh_calls = [74;137;200;264;335;406;477;548;619;690;761;832;903;974;997];
    sh_last_bytes = (48--55) @ (128--135); sh_last_chunks = [0;16;32];
    sh_pk128 = [1904;1920;1936]; sh_split = [0;16;32]; sh_rebuild = [48;128];
    sh_steps = 1043 };;

let SHAKE87_INST =
  { sh_fn = "mldsa87_verify_internal"; sh_start = "in_shake256_init_1";
    sh_stop = "after_mld_H87";
    sh_pklen = 2592; sh_a = 2400; sh_t = 11840;
    sh_vars = "(r21:int64) (r304:int64) (r320:int64) (r336:int64)";
    sh_pre = "read X21 s = r21 /\\
              read (memory :> bytes64 (word_add fp (word 304))) s = r304 /\\
              read (memory :> bytes64 (word_add fp (word 320))) s = r320 /\\
              read (memory :> bytes64 (word_add fp (word 336))) s = r336 /\\";
    sh_post = "read X0 s = word_add fp (word 11776) /\\
               read X1 s = word_add fp (word 11840) /\\ read X2 s = word 64 /\\
               read X3 s = r304 /\\ read X4 s = r336 /\\
               read X5 s = r21 /\\ read X6 s = r320 /\\";
    sh_reads = "word_add fp (word 304),8; word_add fp (word 320),8; \
                word_add fp (word 336),8; ";
    sh_mods = "X18; X21; X25; X30";
    sh_calls = [74;137;200;264;335;406;477;548;619;690;761;832;903;974;1045;
                1116;1187;1258;1329;1344];
    sh_last_bytes = (8--15) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [8;128]; sh_steps = 1391 };;
