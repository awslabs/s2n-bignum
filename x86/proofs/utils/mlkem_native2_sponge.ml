(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the x86 mlkem_native2 functions that run the      *)
(* Keccak sponge of common/fips202/fips202.ml with sha3_keccak_f1600_alt2 on *)
(* a state in memory (mlkem_hash_h and mlkem_hash_g): the state as the       *)
(* 1600-bit word read by wbytes, given by its 25 lanes or its 200 bytes; the *)
(* theorems for sha3_keccak_f1600_alt2 in the image, on such a state; the    *)
(* round constants as bytes; and the XOR of the blocks of the message and of *)
(* the padding into the state, lane by lane or byte by byte, with the padded *)
(* message as a number for keccak_absorb. As                                 *)
(* arm/proofs/utils/mlkem_native2_sponge.ml for AArch64, with the x86 forms  *)
(* of the simulation.                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/asm/mlkem_native2_image.ml";;
needs "x86/proofs/sha3_keccak_f1600_alt2.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;

(* ------------------------------------------------------------------------- *)
(* A Keccak state in memory, as a 1600-bit word, by its 64-bit lanes or by   *)
(* its bytes, and a zero state from stores of 32 and 8 bytes; and a read of  *)
(* 32 bytes from a number in memory.                                         *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_VAL = prove
 (`!a:int64 (x:N word) s:x86state.
        read (memory :> wbytes a) s = x <=>
        read (memory :> bytes(a,dimindex(:N) DIV 8)) s = val x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES]);;

let READ_MEMORY_WBYTES_1600 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_DIV_CONV)
   (INST_TYPE [`:1600`,`:N`] READ_MEMORY_WBYTES_VAL);;

let READ_MEMORY_BYTES_OF_BYTES64 = prove
 (`!a:int64 n x s:x86state.
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
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
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
 (`!a:int64 n x s:x86state.
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
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
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

let READ_MEMORY_BYTES_OF_BYTES256 = prove
 (`!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                 word((x DIV 2 EXP (256 * j)) MOD 2 EXP 256))
        ==> read (memory :> bytes(a,32 * n)) s = x MOD 2 EXP (256 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `32 * SUC n = 32 * n + 32`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int256->num`) THEN
  REWRITE_TAC[BYTES256_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_256; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 * SUC n = 256 * n + 256`; EXP_ADD;
              MOD_MULT_MOD; ARITH_RULE `8 * 32 * n = 256 * n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let READ_MEMORY_WBYTES_LANES = prove
 (`!a (S:1600 word) s:x86state.
        read (memory :> wbytes a) s = S <=>
        !j. j < 25
            ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                word_subword S (64 * j,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `8 * j`; `s:x86state`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; ARITH_RULE `8 * 8 * j = 64 * j`];
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `25`; `val(S:1600 word)`; `s:x86state`]
      READ_MEMORY_BYTES_OF_BYTES64) THEN
    ASM_REWRITE_TAC[GSYM word_subword] THEN
    REWRITE_TAC[ARITH_RULE `8 * 25 = 200 /\ 64 * 25 = 1600`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]]);;

let READ_MEMORY_WBYTES_BYTES = prove
 (`!a (S:1600 word) s:x86state.
        read (memory :> wbytes a) s = S <=>
        !j. j < 200
            ==> read (memory :> bytes8(word_add a (word j))) s =
                word_subword S (8 * j,8)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `j:num`; `s:x86state`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; ARITH_RULE `2 EXP 8 = 256`];
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `s:x86state`]
      READ_MEMORY_BYTES_OF_BYTES8) THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM word_subword] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 200 = 1600`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]]);;

let READ_MEMORY_WBYTES_ZERO = prove
 (`!a:int64 s:x86state.
        (!j. j < 6
             ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                 word 0) /\
        read (memory :> bytes64(word_add a (word 192))) s = word 0
        ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  MP_TAC(SPECL [`a:int64`; `6`; `0`; `s:x86state`]
    READ_MEMORY_BYTES_OF_BYTES256) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0] THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `200 = 32 * 6 + 8`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num` o check (can (term_match []
    `read (memory :> bytes64 a) s = x`) o concl)) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64; VAL_WORD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[] THEN ARITH_TAC);;

let READ_MEMORY_BYTES256_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes256(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES256_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_256] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 256 = 2 EXP (8 * 32)`; MOD_MOD_REFL;
              ARITH_RULE `256 DIV 8 = 32`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* sha3_keccak_f1600_alt2 in the image, at pc + sha3_keccak_f1600_alt2 with  *)
(* its rotation table at pc + sha3_keccak_f1600_alt2_rotations: its code     *)
(* with the reference to the table resolved there is the code in the image,  *)
(* so its theorems hold with the image loaded, without a precondition for    *)
(* the table. Also the theorem with the state as a 1600-bit word, and        *)
(* the round constants as bytes in memory, which unlike wordlist_from_memory *)
(* are kept by the simulation over other stores.                             *)
(* ------------------------------------------------------------------------- *)

let mlkem_native2_keccak_x1_code,MLKEM_NATIVE2_KECCAK_X1_CODE_LOADED =
  x86_image_data mlkem_native2_image_mc "mlkem_native2_keccak_x1_code"
    (layout "sha3_keccak_f1600_alt2") (layout "sha3_keccak_f1600_alt2_size");;

let mlkem_native2_keccak_x1_tables,MLKEM_NATIVE2_KECCAK_X1_TABLES_LOADED =
  x86_image_data mlkem_native2_image_mc "mlkem_native2_keccak_x1_tables"
    (layout "sha3_keccak_f1600_alt2_rotations") 384;;

let MLKEM_NATIVE2_KECCAK_X1_MC = prove
 (`!pc. sha3_keccak_f1600_alt2_mc (pc + sha3_keccak_f1600_alt2)
                                  (pc + sha3_keccak_f1600_alt2_rotations) =
        mlkem_native2_keccak_x1_code`,
  let lemma = prove
   (`!pc a b c. (&(pc + a):int) - (&(pc + b) + &c) = &a - &b - &c`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC) in
  GEN_TAC THEN
  CONV_TAC(LAND_CONV
   (REWRITE_CONV[sha3_keccak_f1600_alt2_mc; lemma] THENC
    DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV) THENC
    REWRITE_CONV[NUM_OF_INT_OF_NUM] THENC
    DEPTH_CONV NUM_RED_CONV)) THEN
  REWRITE_TAC[mlkem_native2_keccak_x1_code]);;

let MLKEM_NATIVE2_KECCAK_X1_TABLES = prove
 (`sha3_keccak_f1600_alt2_data = mlkem_native2_keccak_x1_tables`,
  REWRITE_TAC[sha3_keccak_f1600_alt2_data; mlkem_native2_keccak_x1_tables]);;

let SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
     nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (a,200) (rc,192) /\
     nonoverlapping (a,200) (stackpointer,8)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rc] s /\
               wordlist_from_memory(rc,24) s = round_constants /\
               wordlist_from_memory(a,25) s = A)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(a,25) s = keccak 24 A)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,200)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `rc:int64`; `A:int64 list`;
                `pc + sha3_keccak_f1600_alt2`;
                `pc + sha3_keccak_f1600_alt2_rotations`;
                `stackpointer:int64`; `returnaddress:int64`]
         SHA3_KECCAK_F1600_ALT2_SUBROUTINE_CORRECT) THEN
  REWRITE_TAC[MLKEM_NATIVE2_KECCAK_X1_MC; MLKEM_NATIVE2_KECCAK_X1_TABLES] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[riprel32_within_bounds; GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN
    REPEAT CONJ_TAC THEN TRY INT_ARITH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_CODE_LOADED) THEN
    REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_TABLES_LOADED) THEN
    REWRITE_TAC[]]);;

let SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT_F1600 = prove
 (`!a rc (S:1600 word) pc stackpointer returnaddress.
     nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (a,200) (rc,192) /\
     nonoverlapping (a,200) (stackpointer,8)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rc] s /\
               wordlist_from_memory(rc,24) s = round_constants /\
               read (memory :> wbytes a) s = S)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> wbytes a) s = keccak_f1600 S)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,200)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `rc:int64`;
                `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
               SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

let WORDLIST_FROM_MEMORY_ROUND_CONSTANTS = prove
 (`!c s. wordlist_from_memory(c,24) s = round_constants <=>
         read (memory :> bytes(c,192)) s = num_of_wordlist round_constants`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `24`; `192`; `round_constants`; `s:x86state`]
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
(* The byte AL of the register RAX after a load of a byte into EAX with zero *)
(* extension, as the simulation of movzx and an operation on AL gives it.    *)
(* ------------------------------------------------------------------------- *)

let BYTE_ZX_X86 = prove
 (`!x:byte. word(val(word_zx(word_zx x:int32):int64) MOD 256):byte = x`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ZX_GEN; DIMINDEX_8;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `val(x:byte) MOD 4294967296 = val x /\
    val x MOD 18446744073709551616 = val x /\ val x MOD 256 = val x`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The count t MOD 8 of the single bytes of the last block, as the           *)
(* simulation of the 32-bit "and ecx, 7" on the length t in RCX gives        *)
(* RCX and the test of ZF on it.                                             *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_7_ZX32 = prove
 (`!t. t < 2 EXP 32
       ==> word_zx(word_and (word_zx (word t:int64):int32) (word 7)):int64 =
           word(t MOD 8) /\
           val(word_and (word_zx (word t:int64):int32) (word 7)) = t MOD 8`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_zx (word t:int64):int32 = word t` SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SIMPLE THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word t:int32`; `3`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_ZX_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `t MOD 8 MOD 2 EXP 32 = t MOD 8` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC(ARITH_RULE `x < 8 ==> x < 2 EXP 32`) THEN ARITH_TAC;
    REWRITE_TAC[]]);;

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

(*** The 256-bit loads and stores of the state and the message, which are
 *** known as 64-bit lanes: the facts for the 32 bytes at each address in
 *** the list as joins of the facts for their lanes in state s, before the
 *** simulation, and the facts for the lanes of the 32 bytes stored at each
 *** address in state s, after it
 ***)

let READ_MEMORY_MERGE256_TAC s addrs =
  MAP_EVERY (fun a ->
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      (vsubst [a,`a:int64`; s,`s:x86state`]
              `read (memory :> bytes256 a) s`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) addrs;;

let READ_MEMORY_SPLIT256_TAC s addrs =
  MAP_EVERY (fun a ->
    let pat = vsubst [a,`a:int64`; s,`s:x86state`]
                `read (memory :> bytes256 a) s = x` in
    FIRST_X_ASSUM(fun th ->
      if can (term_match (s::frees a) pat) (concl th)
      then MP_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) THEN
           CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV WORD_SUBWORD_XOR) THENC
                              TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
           STRIP_TAC
      else NO_TAC)) addrs;;

(*** For each memory fact at an address word_add (word_add a (word k)) d,
 *** also the same fact at word_add a (word(k + d)): the simulation takes
 *** the address of a load from a register with value word_add a (word k)
 *** in that form
 ***)

let READ_MEMORY_NORMALIZE_TAC a =
  W(fun (asl,w) ->
    let nested t =
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),Comb(_,ad))),_)),_) ->
          (try let x,_ = dest_binary "word_add" ad in
               let y,_ = dest_binary "word_add" x in y = a
           with Failure _ -> false)
      | _ -> false in
    let ths = filter (nested o concl) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])
      ths);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of sha3_keccak_f1600_alt2 with the    *)
(* frame of its correctness theorem, as needed to use it as a callee (its    *)
(* safety theorems have the frame \s s'. true): the subroutine from the      *)
(* core, and in the image.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
    forall e a rc pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA] THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC
   (REWRITE_RULE[SHA3_KECCAK_F1600_ALT2_DATA] SHA3_KECCAK_F1600_ALT2_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE ~bridge:(Some SHA3_KECCAK_F1600_ALT2_MC_BRIDGE)
   SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let SHA3_KECCAK_F1600_ALT2_IMAGE_SAFE = prove
 (`exists f_events.
    forall e a rc pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192;
                       word(pc + sha3_keccak_f1600_alt2_rotations),384;
                       stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  X_CHOOSE_TAC
   `f:int64->int64->num->num->int64->int64->(uarch_event)list`
   SHA3_KECCAK_F1600_ALT2_SUBROUTINE_SAFE_FRAMED THEN
  EXISTS_TAC
   `\(rc:int64) (a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (f:int64->int64->num->num->int64->int64->(uarch_event)list)
      rc a (pc + sha3_keccak_f1600_alt2_rotations)
      (pc + sha3_keccak_f1600_alt2) stackpointer returnaddress` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`;
    `pc + sha3_keccak_f1600_alt2`; `pc + sha3_keccak_f1600_alt2_rotations`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  REWRITE_TAC[MLKEM_NATIVE2_KECCAK_X1_MC; MLKEM_NATIVE2_KECCAK_X1_TABLES] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[riprel32_within_bounds; GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN
    REPEAT CONJ_TAC THEN TRY INT_ARITH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_CODE_LOADED) THEN
    REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_TABLES_LOADED) THEN
    REWRITE_TAC[]]);;
