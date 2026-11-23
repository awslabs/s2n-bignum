(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the mlkem_native2 functions that run the Keccak   *)
(* sponge of common/fips202/fips202.ml with sha3_keccak_f1600 on a state in  *)
(* memory (mlkem_hash_h and mlkem_hash_g): the state as the 1600-bit word    *)
(* read by wbytes, given by its 25 lanes or its 200 bytes; the theorem for   *)
(* sha3_keccak_f1600 on such a state; the round constants as bytes; and the  *)
(* XOR of the blocks of the message and of the padding into the state, lane  *)
(* by lane or byte by byte, with the padded message as a number for          *)
(* keccak_absorb.                                                            *)
(* ========================================================================= *)

needs "arm/proofs/sha3_keccak_f1600.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;
needs "arm/proofs/utils/mlkem_native_image.ml";;

(* ------------------------------------------------------------------------- *)
(* A Keccak state in memory, as a 1600-bit word, by its 64-bit lanes or by   *)
(* its bytes, and a zero state from stores of 16 and 8 bytes.                *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_OF_BYTES64 = prove
 (`!a:int64 n x s:armstate.
        (!j. j < n
             ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                 word((x DIV 2 EXP (64 * j)) MOD 2 EXP 64))
        ==> read (memory :> bytes(a,8 * n)) s = x MOD 2 EXP (64 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 * SUC n = 64 * n + 64`; EXP_ADD; MOD_MULT_MOD;
              ARITH_RULE `8 * 8 * n = 64 * n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let READ_MEMORY_BYTES_OF_BYTES128 = prove
 (`!a:int64 n x s:armstate.
        (!j. j < n
             ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                 word((x DIV 2 EXP (128 * j)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_128; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * SUC n = 128 * n + 128`; EXP_ADD;
              MOD_MULT_MOD; ARITH_RULE `8 * 16 * n = 128 * n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let READ_MEMORY_WBYTES_LANES = prove
 (`!a (S:1600 word) s:armstate.
        read (memory :> wbytes a) s = S <=>
        !j. j < 25
            ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                word_subword S (64 * j,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `8 * j`; `s:armstate`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; ARITH_RULE `8 * 8 * j = 64 * j`];
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `25`; `val(S:1600 word)`; `s:armstate`]
      READ_MEMORY_BYTES_OF_BYTES64) THEN
    ASM_REWRITE_TAC[GSYM word_subword] THEN
    REWRITE_TAC[ARITH_RULE `8 * 25 = 200 /\ 64 * 25 = 1600`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]]);;

let READ_MEMORY_WBYTES_BYTES = prove
 (`!a (S:1600 word) s:armstate.
        read (memory :> wbytes a) s = S <=>
        !j. j < 200
            ==> read (memory :> bytes8(word_add a (word j))) s =
                word_subword S (8 * j,8)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `j:num`; `s:armstate`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; ARITH_RULE `2 EXP 8 = 256`];
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `s:armstate`]
      READ_MEMORY_BYTES_OF_BYTES8) THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM word_subword] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 200 = 1600`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]]);;

let READ_MEMORY_WBYTES_ZERO = prove
 (`!a:int64 s:armstate.
        (!j. j < 12
             ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                 word 0) /\
        read (memory :> bytes64(word_add a (word 192))) s = word 0
        ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  MP_TAC(SPECL [`a:int64`; `12`; `0`; `s:armstate`]
    READ_MEMORY_BYTES_OF_BYTES128) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0] THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `200 = 16 * 12 + 8`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num` o check (can (term_match []
    `read (memory :> bytes64 a) s = x`) o concl)) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64; VAL_WORD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorem for sha3_keccak_f1600 with the state as a 1600-bit word, and  *)
(* the round constants that it needs as bytes in memory, which unlike        *)
(* wordlist_from_memory are kept by the simulation over other stores.        *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600 = prove
 (`!a rc (S:1600 word) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,200) (word_sub stackpointer (word 128),128) /\
      ALLPAIRS nonoverlapping
               [(a,200); (word_sub stackpointer (word 128),128)]
               [(word pc,0x480); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S /\
                wordlist_from_memory(rc,24) s = round_constants)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,200);
              memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `rc:int64`;
                `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
               SHA3_KECCAK_F1600_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

let WORDLIST_FROM_MEMORY_ROUND_CONSTANTS = prove
 (`!c s. wordlist_from_memory(c,24) s = round_constants <=>
         read (memory :> bytes(c,192)) s = num_of_wordlist round_constants`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `24`; `192`; `round_constants`; `s:armstate`]
    WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `LENGTH round_constants = 24` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[round_constants; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The padded message as a number, as in keccak_sponge: the blocks that      *)
(* keccak_absorb takes from it, the XOR of a block into the state lane by    *)
(* lane, and the last block as the remaining bytes of the message, the       *)
(* domain byte d after them and the final bit at the end of the block.       *)
(* ------------------------------------------------------------------------- *)

let keccak_padded = new_definition
 `keccak_padded r d (m:byte list) =
  num_of_bytelist m +
  2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))`;;

let KECCAK_XOR_LANE = prove
 (`!(S:1600 word) B n j.
        B < 2 EXP (64 * n) /\ j < 25
        ==> word_subword (word_xor S (word B)) (64 * j,64):int64 =
            if j < n then word_xor (word_subword S (64 * j,64))
                                   (word((B DIV 2 EXP (64 * j)) MOD 2 EXP 64))
            else word_subword S (64 * j,64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `B DIV 2 EXP (64 * j) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_0; WORD_XOR_0]]);;

let KECCAK_BLOCK_LANE = prove
 (`!M r i j.
        8 * j + 8 <= r
        ==> (((M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)) DIV
             2 EXP (64 * j)) MOD 2 EXP 64 =
            (M DIV 2 EXP (8 * (r * i + 8 * j))) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE
   `8 * j + 8 <= r ==> 64 * j + 64 <= 8 * r`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let KECCAK_LAST_BLOCK_XOR = prove
 (`!r d (m:byte list).
        0 < r /\ d < 128
        ==> word((keccak_padded r d m DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                 2 EXP (8 * r)):1600 word =
            word_xor
             (word_xor
               (word(num_of_bytelist m DIV 2 EXP (8 * r * LENGTH m DIV r)))
               (word(2 EXP (8 * LENGTH m MOD r) * d)))
             (word(2 EXP (8 * (r - 1)) * 128))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_padded] THEN
  MP_TAC(SPECL [`num_of_bytelist(m:byte list)`;
                `num_of_bytelist(keccak_pad r d (LENGTH(m:byte list)))`;
                `LENGTH(m:byte list)`; `r:num`] KECCAK_BLOCK_LAST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[KECCAK_PAD_BOUND] THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_BOUND];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
  MP_TAC(SPECL [`LENGTH(m:byte list)`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  SUBGOAL_THEN
   `num_of_bytelist m DIV 2 EXP (8 * r * LENGTH(m:byte list) DIV r) <
    2 EXP (8 * LENGTH m MOD r)`
  MP_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `8 * r * q + 8 * t = 8 * (q * r + t)`] THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_BOUND];
    ALL_TAC] THEN
  SPEC_TAC(`num_of_bytelist m DIV 2 EXP (8 * r * LENGTH(m:byte list) DIV r)`,
           `x:num`) THEN
  SPEC_TAC(`LENGTH(m:byte list) MOD r`,`t:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `2 EXP (8 * t) *
    (if t = r - 1 then d + 128 else d + 2 EXP (8 * (r - t - 1)) * 128) =
    2 EXP (8 * t) * d + 2 EXP (8 * (r - 1)) * 128`
  SUBST1_TAC THENL
   [COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      SUBGOAL_THEN
       `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `t < r` THEN ARITH_TAC;
        CONV_TAC NUM_RING]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_XOR_DISJOINT_ADD] THEN
  SUBGOAL_THEN `2 EXP (8 * (r - 1)) * 128 = 2 EXP (8 * (r - 1) + 7) * 1`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * t) * 128` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `x < e /\ e * (d + 1) <= e * 128 ==> x + e * d < e * 128`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    UNDISCH_TAC `d < 128` THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `128 = 2 EXP 7`; GSYM EXP_ADD; LE_EXP;
                ARITH_EQ] THEN
    UNDISCH_TAC `t < r` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The XOR of a prefix of a number into a state, extended by one lane or one *)
(* byte, as for a loop over the last words or bytes of the message; and the  *)
(* bytes of the state after a byte c is XORed into byte p.                   *)
(* ------------------------------------------------------------------------- *)

let ODD_MOD_DIV_POW2 = prove
 (`!n a i. ODD((n MOD 2 EXP a) DIV 2 EXP i) <=> i < a /\ ODD(n DIV 2 EXP i)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num < a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(n MOD 2 EXP a) DIV 2 EXP i = (n DIV 2 EXP i) MOD 2 EXP (a - i)`
    SUBST1_TAC THENL
     [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN AP_THM_TAC THEN
      REPLICATE_TAC 3 AP_TERM_TAC THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ODD_MOD_POW2; ARITH_RULE `i < a ==> ~(a - i = 0)`]];
    SUBGOAL_THEN `(n MOD 2 EXP a) DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP a` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC]);;

let XOR_PREFIX_STEP_TAC =
  let thens = map ARITH_RULE
   [`b < 64 /\ k < 25 ==> (64 * k + b < 1600 <=> T)`;
    `b < 64 ==> (64 * k + b < 64 * (k + 1) <=> T)`;
    `64 * k + b < 64 * k <=> F`;
    `b < 8 /\ k < 200 ==> (8 * k + b < 1600 <=> T)`;
    `b < 8 ==> (8 * k + b < 8 * (k + 1) <=> T)`;
    `8 * k + b < 8 * k <=> F`]
  and elses = map ARITH_RULE
   [`b < 64 /\ j < 25 ==> (64 * j + b < 1600 <=> T)`;
    `~(j = k) /\ b < 64
     ==> (64 * j + b < 64 * (k + 1) <=> 64 * j + b < 64 * k)`;
    `b < 8 /\ j < 200 ==> (8 * j + b < 1600 <=> T)`;
    `~(j = k) /\ b < 8
     ==> (8 * j + b < 8 * (k + 1) <=> 8 * j + b < 8 * k)`] in
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_XOR;
              BIT_WORD; DIMINDEX_64; DIMINDEX_8;
              DIMINDEX_CONV `dimindex(:1600)`;
              ARITH_RULE `MIN 64 64 = 64 /\ MIN 8 8 = 8`] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ODD_MOD_DIV_POW2; DIV_DIV; GSYM EXP_ADD] THENL
   [ASM_SIMP_TAC thens; ASM_SIMP_TAC elses] THEN
  CONV_TAC TAUT;;

let LANE_XOR_STEP = prove
 (`!(S:1600 word) n k j.
        k < 25 /\ j < 25
        ==> word_subword (word_xor S (word(n MOD 2 EXP (64 * (k + 1)))))
                         (64 * j,64):int64 =
            if j = k
            then word_xor
                  (word_subword (word_xor S (word(n MOD 2 EXP (64 * k))))
                                (64 * j,64))
                  (word((n DIV 2 EXP (64 * k)) MOD 2 EXP 64))
            else word_subword (word_xor S (word(n MOD 2 EXP (64 * k))))
                              (64 * j,64)`,
  XOR_PREFIX_STEP_TAC);;

let BYTE_XOR_STEP = prove
 (`!(S:1600 word) n k j.
        k < 200 /\ j < 200
        ==> word_subword (word_xor S (word(n MOD 2 EXP (8 * (k + 1)))))
                         (8 * j,8):byte =
            if j = k
            then word_xor
                  (word_subword (word_xor S (word(n MOD 2 EXP (8 * k))))
                                (8 * j,8))
                  (word((n DIV 2 EXP (8 * k)) MOD 2 EXP 8))
            else word_subword (word_xor S (word(n MOD 2 EXP (8 * k))))
                              (8 * j,8)`,
  XOR_PREFIX_STEP_TAC);;

let BYTE_XOR_SHIFT = prove
 (`!(S:1600 word) c p j.
        c < 256 /\ p < 200 /\ j < 200
        ==> word_subword (word_xor S (word(2 EXP (8 * p) * c)))
                         (8 * j,8):byte =
            if j = p then word_xor (word_subword S (8 * j,8)) (word c)
            else word_subword S (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `2 EXP (8 * p) * c`; `p:num`; `j:num`]
    BYTE_XOR_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(2 EXP (8 * p) * c) MOD 2 EXP (8 * (p + 1)) = 2 EXP (8 * p) * c /\
    (2 EXP (8 * p) * c) MOD 2 EXP (8 * p) = 0 /\
    ((2 EXP (8 * p) * c) DIV 2 EXP (8 * p)) MOD 2 EXP 8 = c`
   (fun th -> REWRITE_TAC[th; WORD_XOR_0]) THEN
  SIMP_TAC[DIV_MULT; MOD_MULT; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `8 * (p + 1) = 8 * p + 8`; EXP_ADD; MOD_MULT2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* The XOR of two bytes, and of a byte and a constant, through the W         *)
(* registers, as the simulation of ldrb, eor and strb gives them.            *)
(* ------------------------------------------------------------------------- *)

let BYTE_XOR_ZX = prove
 (`!x y:byte.
        word_zx(word_zx(word_zx
         (word_xor (word_zx(word_zx(word_zx x:int32):int64):int32)
                   (word_zx(word_zx(word_zx y:int32):int64):int32)):int64)
         :int32):byte = word_xor x y`,
  CONV_TAC WORD_BLAST);;

let BYTE_XOR_CONST_ZX = prove
 (`!x:byte.
        word_zx(word_zx(word_zx
         (word_xor (word_zx(word_zx(word_zx x:int32):int64):int32)
                   (word 6)):int64):int32):byte = word_xor x (word 6) /\
        word_zx(word_zx(word_zx
         (word_xor (word_zx(word_zx(word_zx x:int32):int64):int32)
                   (word 128)):int64):int32):byte = word_xor x (word 128)`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Addresses and quantified facts in the simulation.                         *)
(* ------------------------------------------------------------------------- *)

(*** The address of a load in the form it has after a post-increment ***)

let WORD_ADD_SPLIT_OFFSET = prove
 (`!a:int64 n k.
        word_add a (word(n + k)) = word_add (word_add a (word n)) (word k)`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(*** From |- !j. P j ==> Q j, give |- !j. P j /\ ~(j = t) ==> Q j, which   ***)
(*** the simulation keeps over a store to element t                        ***)

let RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of sha3_keccak_f1600 with the frame   *)
(* of its correctness theorem, as needed to use it as a callee: that of      *)
(* the core without the saving of registers, and the subroutine from it.     *)
(* ------------------------------------------------------------------------- *)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "sha3_keccak_f1600" subroutine_signatures)
    SHA3_KECCAK_F1600_CORRECT
    SHA3_KECCAK_F1600_EXEC;;

let SHA3_KECCAK_F1600_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e a rc pc stackpointer.
           aligned 16 stackpointer /\
           nonoverlapping (a,200) (stackpointer,32) /\
           ALLPAIRS nonoverlapping
           [a,200; stackpointer,32]
           [word pc,0x480; rc,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                    read PC s = word (pc + 0x1c) /\
                    read SP s = stackpointer /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s. read PC s = word (pc + 0x460) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events rc a pc stackpointer /\
                        memaccess_inbounds e2
                        [a,200; rc,192; stackpointer,32]
                        [a,200; stackpointer,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X19; X20; X21; X22; X23; X24;
                           X25; X26; X27; X28; X29; X30] ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(stackpointer,32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars SHA3_KECCAK_F1600_EXEC);;

let SHA3_KECCAK_F1600_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e a rc pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           nonoverlapping (a,200) (word_sub stackpointer (word 128),128) /\
           ALLPAIRS nonoverlapping
           [a,200; word_sub stackpointer (word 128),128]
           [word pc,0x480; rc,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events rc a pc
                               (word_sub stackpointer (word 128))
                               returnaddress /\
                        memaccess_inbounds e2
                        [a,200; rc,192; word_sub stackpointer (word 128),128]
                        [a,200; word_sub stackpointer (word 128),128]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(a,200);
                  memory :> bytes(word_sub stackpointer (word 128),128)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(7,7) SHA3_KECCAK_F1600_EXEC
    SHA3_KECCAK_F1600_SAFE_FRAMED
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 128 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
