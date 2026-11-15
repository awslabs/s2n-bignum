(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the x86 mlkem_native2 functions that sample       *)
(* noise, SamplePolyCBD_eta(PRF_eta(sigma, b)) of FIPS 203, in the lanes of  *)
(* the Keccak permutations: the coefficients of SamplePolyCBD, the PRF       *)
(* output as the state of a lane after one or two permutations, the lane as  *)
(* stored by the code, the theorems for the callees (sha3_keccak4_f1600_alt, *)
(* mlkem_cbd2, mlkem_cbd3) in the forms a caller needs, and the tactics for  *)
(* the simulation driver of utils/mlkem_native2_tools.ml that take each call *)
(* as one step. As arm/proofs/utils/mlkem_native2_noise.ml for AArch64, with *)
(* the x86 forms of the code and the simulation.                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_sponge.ml";;
needs "x86/proofs/mlkem_cbd2.ml";;
needs "x86/proofs/mlkem_cbd3.ml";;
needs "x86/proofs/sha3_keccak4_f1600_alt.ml";;
needs "common/fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* The coefficients of SamplePolyCBD_eta(b) as integers in [-eta,eta], so    *)
(* that mlkem_cbd eta b is their polynomial, and as computed by mlkem_cbd2   *)
(* and mlkem_cbd3.                                                           *)
(* ------------------------------------------------------------------------- *)

let mlkem_cbd_coeff = new_definition
 `mlkem_cbd_coeff eta (b:byte list) i =
    &(nsum {j | j < eta}
           (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * i + j)) MOD 2)) -
    &(nsum {j | j < eta}
           (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * i + eta + j)) MOD 2)):
    int`;;

let MLKEM_CBD_COEFF = prove
 (`!eta b. mlkem_cbd eta b = mlkem_poly(mlkem_cbd_coeff eta b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; mlkem_cbd_coeff]);;

let NSUM_LT_2 = prove
 (`!f. nsum {j | j < 2} f = f 0 + f 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES; ARITH_RULE `SUC 0 = 1`]);;

let NSUM_LT_3 = prove
 (`!f. nsum {j | j < 3} f = f 0 + f 1 + f 2`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES;
              ARITH_RULE `SUC 0 = 1 /\ SUC 1 = 2`; ADD_ASSOC]);;

let MLKEM_CBD_COEFF_2 = prove
 (`!b i. mlkem_cbd_coeff 2 b i =
         &((num_of_bytelist b DIV 2 EXP (4 * i)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (4 * i + 1)) MOD 2) -
         &((num_of_bytelist b DIV 2 EXP (4 * i + 2)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (4 * i + 3)) MOD 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd_coeff; NSUM_LT_2] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * 2 * i + 0 = 4 * i /\ 2 * 2 * i + 1 = 4 * i + 1 /\
    2 * 2 * i + 2 + 0 = 4 * i + 2 /\ 2 * 2 * i + 2 + 1 = 4 * i + 3`]);;

let MLKEM_CBD_COEFF_3 = prove
 (`!b i. mlkem_cbd_coeff 3 b i =
         &((num_of_bytelist b DIV 2 EXP (6 * i)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 1)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 2)) MOD 2) -
         &((num_of_bytelist b DIV 2 EXP (6 * i + 3)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 4)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 5)) MOD 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd_coeff; NSUM_LT_3] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * 3 * i + 0 = 6 * i /\ 2 * 3 * i + 1 = 6 * i + 1 /\
    2 * 3 * i + 2 = 6 * i + 2 /\ 2 * 3 * i + 3 + 0 = 6 * i + 3 /\
    2 * 3 * i + 3 + 1 = 6 * i + 4 /\ 2 * 3 * i + 3 + 2 = 6 * i + 5`]);;

(* ------------------------------------------------------------------------- *)
(* PRF_eta(s, b) = SHAKE256(s || b, 64 * eta) for a 32-byte seed s: the      *)
(* message fits in one block, so the state after absorbing it is the padded  *)
(* block mlkem_noise_state s b, and the output is the bytes of the state     *)
(* after one permutation (the 128 bytes for eta = 2) or of one block and     *)
(* then the next (136 and 56 bytes for eta = 3).                             *)
(* ------------------------------------------------------------------------- *)

let mlkem_noise_state = new_definition
 `mlkem_noise_state (seed:byte list) (b:byte) =
    (word(num_of_bytelist seed + 2 EXP 256 * val b + 2 EXP 264 * 31 +
          2 EXP 1087):1600 word)`;;

let MLKEM_NOISE_ABSORB = prove
 (`!seed:byte list b.
     LENGTH seed = 32
     ==> word_xor
          (keccak_absorb 136
            (num_of_bytelist(APPEND seed [b]) +
             2 EXP (8 * LENGTH(APPEND seed [b])) *
             num_of_bytelist(keccak_pad 136 31 (LENGTH(APPEND seed [b]))))
            (LENGTH(APPEND seed [b]) DIV 136))
          (word(((num_of_bytelist(APPEND seed [b]) +
                  2 EXP (8 * LENGTH(APPEND seed [b])) *
                  num_of_bytelist(keccak_pad 136 31
                                   (LENGTH(APPEND seed [b])))) DIV
                 2 EXP (8 * 136 * LENGTH(APPEND seed [b]) DIV 136)) MOD
                2 EXP (8 * 136))) =
         mlkem_noise_state seed b`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; num_of_bytelist; DIV_1] THEN
  REWRITE_TAC[mlkem_noise_state] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `seed:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let mlkem_noise_padded_tm =
  `num_of_bytelist(APPEND (seed:byte list) [b]) +
   2 EXP (8 * LENGTH(APPEND seed [b])) *
   num_of_bytelist(keccak_pad 136 31 (LENGTH(APPEND seed [b])))`;;

let MLKEM_NOISE_SPONGE_BYTES = prove
 (`!seed:byte list b n.
     LENGTH seed = 32 /\ n <= 136
     ==> num_of_bytelist(list_of_seq (shake256(APPEND seed [b])) n) =
         val(keccak_f1600(mlkem_noise_state seed b)) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake256] THEN
  MP_TAC(SPECL [`512`; `31`; `APPEND (seed:byte list) [b]`; `136`;
                mlkem_noise_padded_tm; `n:num`] KECCAK_SPONGE_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[MLKEM_NOISE_ABSORB]]);;

let MLKEM_NOISE_SPONGE_BLOCK = prove
 (`!seed:byte list b k n.
     LENGTH seed = 32 /\ n <= 136
     ==> num_of_bytelist
          (list_of_seq (\j. shake256(APPEND seed [b]) (136 * k + j)) n) =
         val(keccak_squeeze (k + 1) (mlkem_noise_state seed b)) MOD
         2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake256] THEN
  MP_TAC(SPECL [`512`; `31`; `APPEND (seed:byte list) [b]`; `136`;
                mlkem_noise_padded_tm; `k:num`; `n:num`]
               KECCAK_SPONGE_BLOCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[MLKEM_NOISE_ABSORB]]);;

let MLKEM_PRF_2_NOISE = prove
 (`!seed:byte list b.
     LENGTH seed = 32
     ==> num_of_bytelist(mlkem_prf 2 seed b) =
         val(keccak_f1600(mlkem_noise_state seed b)) MOD 2 EXP 1024`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_prf] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_SIMP_TAC[MLKEM_NOISE_SPONGE_BYTES; ARITH_RULE `128 <= 136`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_PRF_3_NOISE = prove
 (`!seed:byte list b.
     LENGTH seed = 32
     ==> num_of_bytelist(mlkem_prf 3 seed b) =
         val(keccak_f1600(mlkem_noise_state seed b)) MOD 2 EXP 1088 +
         2 EXP 1088 *
         val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b))) MOD
         2 EXP 448`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_prf] THEN
  REWRITE_TAC[ARITH_RULE `64 * 3 = 136 + 56`] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  ASM_SIMP_TAC[MLKEM_NOISE_SPONGE_BYTES; LE_REFL] THEN
  MP_TAC(SPECL [`seed:byte list`; `b:byte`; `1`; `56`]
    MLKEM_NOISE_SPONGE_BLOCK) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `56 <= 136`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 + 1 = SUC(SUC 0)`; keccak_squeeze] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* A read of bytes as the sum of the reads of consecutive pieces, and        *)
(* BYTES_PIECES_CONV [p1; ...; pk] to split read (memory :> bytes(a,n)) s in *)
(* pieces of p1, ..., pk bytes, those of 32, 16, 8, 4, 2 and 1 as bytes256,  *)
(* bytes128, bytes64, bytes32, bytes16 and bytes8.                           *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_SPLIT = prove
 (`!a:int64 m n s:x86state.
     read (memory :> bytes(a,m + n)) s =
     read (memory :> bytes(a,m)) s +
     2 EXP (8 * m) * read (memory :> bytes(word_add a (word m),n)) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

let READ_MEMORY_BYTES_16 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_8 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,8)) s = val(read (memory :> bytes64 a) s)`,
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_32 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,32)) s = val(read (memory :> bytes256 a) s)`,
  REWRITE_TAC[BYTES256_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_4 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,4)) s = val(read (memory :> bytes32 a) s)`,
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_2 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,2)) s = val(read (memory :> bytes16 a) s)`,
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_1 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let BYTES_PIECES_CONV =
  let piece_conv p =
    try REWR_CONV (assoc p [32,READ_MEMORY_BYTES_32; 16,READ_MEMORY_BYTES_16;
                            8,READ_MEMORY_BYTES_8; 4,READ_MEMORY_BYTES_4;
                            2,READ_MEMORY_BYTES_2; 1,READ_MEMORY_BYTES_1])
    with Failure _ -> ALL_CONV in
  let addr_conv c = RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(LAND_CONV c))))
  and len_conv c = RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV c)))) in
  let rec conv pieces tm =
    match pieces with
      [] -> failwith "BYTES_PIECES_CONV: no pieces"
    | [p] -> piece_conv p tm
    | p::rest ->
        let al = rand(rand(rand(rator tm))) in
        let n = dest_small_numeral(rand al) in
        let th0 = SPECL [lhand al; mk_small_numeral p;
                         mk_small_numeral(n - p); rand tm]
                        READ_MEMORY_BYTES_SPLIT in
        let th1 = CONV_RULE(LAND_CONV(len_conv NUM_ADD_CONV)) th0 in
        (REWR_CONV th1 THENC
         LAND_CONV(piece_conv p) THENC
         RAND_CONV(LAND_CONV(RAND_CONV NUM_MULT_CONV) THENC
                   RAND_CONV(addr_conv
                              (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
                             conv rest))) tm in
  conv;;

let READ_MEMORY_WBYTES_PREFIX = prove
 (`!a (S:1600 word) n s:x86state.
        read (memory :> wbytes a) s = S /\ n <= 200
        ==> read (memory :> bytes(a,n)) s = val S MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A lane as stored by the code for the PRF of seed s and nonce byte b: the  *)
(* 32 bytes of s, the nonce byte with the domain byte 0x1f after it (in the  *)
(* forms that the simulation of movzx and or gives), zeros, and the final    *)
(* bit 0x80 in byte 135, written after the zeros, so that the zeros are      *)
(* pieces that its store does not overlap.                                   *)
(* ------------------------------------------------------------------------- *)

let WORD_NONCE_DS_X86 = prove
 (`!b:byte. word_zx(word_or (word_zx(word_zx(word_zx b:int32):int64):int32)
                            (word 7936):int32):int64 =
            word(val b + 7936)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_zx(word_or (word_zx(word_zx(word_zx (b:byte):int32):int64):int32)
                    (word 7936):int32):int64 =
    word_add (word_zx b) (word 7936)`] THEN
  REWRITE_TAC[word_zx; GSYM WORD_ADD]);;

let MLKEM_NOISE_LANE_X86 = prove
 (`!a (seed:byte list) (b:byte) s:x86state.
     LENGTH seed = 32 /\
     read (memory :> bytes256 a) s =
     word(num_of_bytelist seed MOD 2 EXP 256) /\
     read (memory :> bytes64 (word_add a (word 32))) s =
     word_zx(word_or (word_zx(word_zx(word_zx b:int32):int64):int32)
                     (word 7936):int32) /\
     read (memory :> bytes256 (word_add a (word 40))) s = word 0 /\
     read (memory :> bytes256 (word_add a (word 72))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 104))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 120))) s = word 0 /\
     read (memory :> bytes32 (word_add a (word 128))) s = word 0 /\
     read (memory :> bytes16 (word_add a (word 132))) s = word 0 /\
     read (memory :> bytes8 (word_add a (word 134))) s = word 0 /\
     read (memory :> bytes8 (word_add a (word 135))) s = word 128 /\
     read (memory :> bytes256 (word_add a (word 136))) s = word 0 /\
     read (memory :> bytes256 (word_add a (word 168))) s = word 0
     ==> read (memory :> wbytes a) s = mlkem_noise_state seed b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; mlkem_noise_state] THEN
  CONV_TAC(LAND_CONV(BYTES_PIECES_CONV
   [32;8;32;32;16;8;4;2;1;1;32;32])) THEN
  ASM_REWRITE_TAC[WORD_NONCE_DS_X86] THEN
  REWRITE_TAC[VAL_WORD; VAL_WORD_0; DIMINDEX_8; DIMINDEX_64; DIMINDEX_256;
              DIMINDEX_CONV `dimindex(:1600)`; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `seed:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`val(b:byte)`,`v:num`) THEN
  SPEC_TAC(`num_of_bytelist(seed:byte list)`,`x:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `x MOD 2 EXP 256 = x /\ (v + 7936) MOD 2 EXP 64 = v + 7936`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC [`x < 256 EXP 32`; `v < 2 EXP 8`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`x < 256 EXP 32`; `v < 2 EXP 8`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ARITH_TAC);;

let BYTE_OF_WORD64 = prove
 (`!n. word(val(word n:int64) MOD 256):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The PRF output from the lane after the permutation (eta = 2), or as       *)
(* copied to a buffer, 136 bytes after the first permutation and 56 after    *)
(* the second, in the forms that the simulation of the copies gives.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NOISE_LANE_PRF_2 = prove
 (`!a (seed:byte list) b s:x86state.
        LENGTH seed = 32 /\
        read (memory :> wbytes a) s = keccak_f1600(mlkem_noise_state seed b)
        ==> read (memory :> bytes(a,128)) s =
            num_of_bytelist(mlkem_prf 2 seed b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_PRF_2_NOISE] THEN
  MP_TAC(SPECL [`a:int64`; `keccak_f1600(mlkem_noise_state seed b)`;
                `128`; `s:x86state`] READ_MEMORY_WBYTES_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MOD_EXP_ADD_SPLIT = prove
 (`!x a b. x MOD 2 EXP a + 2 EXP a * (x DIV 2 EXP a) MOD 2 EXP b =
           x MOD 2 EXP (a + b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC);;

let READ_MEMORY_BYTES_136_OF_PIECES_X86 = prove
 (`!a x s:x86state.
     (!j. j < 4 ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                    word((x DIV 2 EXP (256 * j)) MOD 2 EXP 256)) /\
     read (memory :> bytes64(word_add a (word 128))) s =
     word((x DIV 2 EXP 1024) MOD 2 EXP 64)
     ==> read (memory :> bytes(a,136)) s = x MOD 2 EXP 1088`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `136 = 32 * 4 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_BYTES256) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MOD_EXP_ADD_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_ZX_128_256 = prove
 (`!w:int128. word_zx(word_zx w:int256):int128 = w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let READ_MEMORY_BYTES_192_PRF_3_X86 = prove
 (`!a (seed:byte list) b s:x86state.
     LENGTH seed = 32 /\
     read (memory :> bytes(a,136)) s =
     val(keccak_f1600(mlkem_noise_state seed b)) MOD 2 EXP 1088 /\
     read (memory :> bytes256(word_add a (word 136))) s =
     word(val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b))) MOD
          2 EXP 256) /\
     read (memory :> bytes128(word_add a (word 168))) s =
     word((val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b))) DIV
           2 EXP 256) MOD 2 EXP 128) /\
     read (memory :> bytes64(word_add a (word 184))) s =
     word((val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b))) DIV
           2 EXP 384) MOD 2 EXP 64)
     ==> read (memory :> bytes(a,192)) s =
         num_of_bytelist(mlkem_prf 3 seed b)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `y = val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b)))` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_PRF_3_NOISE] THEN
  REWRITE_TAC[ARITH_RULE `192 = 136 + 56`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`; EQ_ADD_LCANCEL;
                  EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `56 = 32 + 24`; READ_MEMORY_BYTES_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `24 = 16 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_32; READ_MEMORY_BYTES_16;
              READ_MEMORY_BYTES_8] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256;
                  MOD_MOD_REFL] THEN
  MP_TAC(SPECL [`y:num`; `256`; `128`] MOD_EXP_ADD_SPLIT) THEN
  MP_TAC(SPECL [`y:num`; `384`; `64`] MOD_EXP_ADD_SPLIT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorems for the callees in the forms a caller needs: the x4          *)
(* permutation on four states as 1600-bit words, mlkem_cbd2 and mlkem_cbd3   *)
(* with the coefficients of SamplePolyCBD, and their constant-time and       *)
(* memory safety with the frames of their correctness theorems.              *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_CORRECT_F1600 = prove
 (`!rc_pointer bitstate_in rho8_ptr rho56_ptr
    (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
    pc stackpointer returnaddress.
     PAIRWISE (nonoverlapping_modulo (2 EXP 64))
       [(pc, LENGTH sha3_keccak4_f1600_alt_mc);
        (val (word_sub stackpointer (word 0x31f)), 0x31f);
        (val bitstate_in, 800);
        (val rc_pointer, 192);
        (val rho8_ptr, 32);
        (val rho56_ptr, 32)] /\
     nonoverlapping_modulo (2 EXP 64)
       (val bitstate_in, 800)
       (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr] s /\
               wordlist_from_memory(rc_pointer, 24) s = round_constants /\
               wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
               wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
               read (memory :> wbytes bitstate_in) s = S1 /\
               read (memory :> wbytes(word_add bitstate_in (word 200))) s =
               S2 /\
               read (memory :> wbytes(word_add bitstate_in (word 400))) s =
               S3 /\
               read (memory :> wbytes(word_add bitstate_in (word 600))) s =
               S4)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> wbytes bitstate_in) s = keccak_f1600 S1 /\
               read (memory :> wbytes(word_add bitstate_in (word 200))) s =
               keccak_f1600 S2 /\
               read (memory :> wbytes(word_add bitstate_in (word 400))) s =
               keccak_f1600 S3 /\
               read (memory :> wbytes(word_add bitstate_in (word 600))) s =
               keccak_f1600 S4)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes (bitstate_in, 800);
                      memory :> bytes(word_sub stackpointer (word 0x31f),
                                      0x31f)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`rc_pointer:int64`; `bitstate_in:int64`; `rho8_ptr:int64`;
                `rho56_ptr:int64`;
                `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
               SHA3_KECCAK4_F1600_ALT_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

(*** The rho8 and rho56 tables, like the round constants, as bytes in memory,
 *** which the simulation keeps over other stores
 ***)

let WORDLIST_FROM_MEMORY_RHO8 = prove
 (`!c s. wordlist_from_memory(c,4) s = rho8_constant <=>
         read (memory :> bytes(c,32)) s = num_of_wordlist rho8_constant`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `4`; `32`; `rho8_constant`; `s:x86state`]
    WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `LENGTH rho8_constant = 4` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[rho8_constant; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORDLIST_FROM_MEMORY_RHO56 = prove
 (`!c s. wordlist_from_memory(c,4) s = rho56_constant <=>
         read (memory :> bytes(c,32)) s = num_of_wordlist rho56_constant`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `4`; `32`; `rho56_constant`; `s:x86state`]
    WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `LENGTH rho56_constant = 4` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[rho56_constant; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF = prove
 (`!r a (b:byte list) pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd2_mc); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = num_of_bytelist b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 2 b i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLKEM_CBD_COEFF_2] THEN
  ACCEPT_TAC(SPECL [`r:int64`; `a:int64`; `num_of_bytelist(b:byte list)`;
                    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
                   MLKEM_CBD2_SUBROUTINE_CORRECT));;

let MLKEM_CBD3_SUBROUTINE_CORRECT_COEFF = prove
 (`!r a (b:byte list) pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd3_mc); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd3_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = num_of_bytelist b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 3 b i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLKEM_CBD_COEFF_3] THEN
  ACCEPT_TAC(SPECL [`r:int64`; `a:int64`; `num_of_bytelist(b:byte list)`;
                    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
                   MLKEM_CBD3_SUBROUTINE_CORRECT));;

(*** The framed safety of mlkem_cbd2 and mlkem_cbd3, from their core
 *** safety theorems (which keep the frame) as in their own files
 ***)

let MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd2_tmc; a,128; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,128; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd2_tmc MLKEM_CBD2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd3_tmc; a,192; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,192; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd3_tmc MLKEM_CBD3_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED;;

(* ------------------------------------------------------------------------- *)
(* A simulation driver for code whose control flow is fixed once its         *)
(* parameters are, NATIVE2_RUN_TAC of utils/mlkem_native2_tools.ml, with     *)
(* tactics for the facts it needs and for the calls. The states of the       *)
(* Keccak lanes are kept as read (memory :> bytes(a,200)) s = val S, which   *)
(* unlike the wbytes form the simulation keeps over other stores, and the    *)
(* round constants and the rho tables as bytes in memory likewise.           *)
(* ------------------------------------------------------------------------- *)

let normalize_addr tm =
  try rand(concl(NORMALIZE_RELATIVE_ADDRESS_CONV tm)) with Failure _ -> tm;;

let addr_plus a off =
  if off = 0 then a else
  normalize_addr(mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral off)));;

let bytes_fact a n k gl =
  asm_with_lhs (vsubst [a,`a:int64`; mk_small_numeral n,`n:num`;
                        state_of k,`s:x86state`]
                 `read (memory :> bytes(a,n)) s`) gl;;

let lane_state a k gl = rand(rand(concl(bytes_fact a 200 k gl)));;

let TO_WBYTES_TAC a k gl =
  ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]
                         (bytes_fact a 200 k gl)) gl;;

let FROM_WBYTES_TAC k =
  let sv = state_of k in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> wbytes a) s = x:1600 word`) c &&
       rand(lhand c) = sv
    then REWRITE_RULE[READ_MEMORY_WBYTES_1600] th else th);;

let RC_TAC rc k gl =
  ASSUME_TAC(REWRITE_RULE[GSYM WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]
                         (bytes_fact rc 192 k gl)) gl;;

let RHO_TAC rho8 rho56 k gl =
  (ASSUME_TAC(REWRITE_RULE[GSYM WORDLIST_FROM_MEMORY_RHO8]
                          (bytes_fact rho8 32 k gl)) THEN
   ASSUME_TAC(REWRITE_RULE[GSYM WORDLIST_FROM_MEMORY_RHO56]
                          (bytes_fact rho56 32 k gl))) gl;;

let SIMP_REG_TAC reg thms k =
  let lhs = mk_comb(mk_comb(`read:(x86state,int64)component->x86state->int64`,
                    reg),state_of k) in
  FIRST_X_ASSUM(fun th ->
    if lhand(concl th) = lhs then ASSUME_TAC(REWRITE_RULE thms th)
    else NO_TAC);;

(*** The calls, at the entry of the callee with the return address pushed:
 *** the x4 permutation on the lanes at RDI with the round constants and
 *** the rho tables at RSI, RDX and RCX; the x1 permutation on the lane at
 *** RDI with the round constants at RSI; mlkem_cbd2 on the 128 bytes of the
 *** lane at RSI after a permutation; and mlkem_cbd3 on 192 bytes known at
 *** RSI.
 ***)

let return_args =
  [`read RSP s`; `read (memory :> bytes64 (read RSP s)) s`];;

let KECCAK4_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl and rc = find_read_fact `RSI` k gl
  and rho8 = find_read_fact `RDX` k gl and rho56 = find_read_fact `RCX` k gl in
  let ads = map (addr_plus a) [0;200;400;600] in
  let ss = map (fun ad -> lane_state ad k gl) ads in
  (RC_TAC rc k THEN RHO_TAC rho8 rho56 k THEN
   MAP_EVERY (fun ad -> TO_WBYTES_TAC ad k) ads THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "sha3_keccak4_f1600_alt",sha3_keccak4_f1600_alt_mc,
     SHA3_KECCAK4_F1600_ALT_SUBROUTINE_CORRECT_F1600)
    ([`read RSI s`; `read RDI s`; `read RDX s`; `read RCX s`] @ ss @
     [`pc + sha3_keccak4_f1600_alt`] @ return_args) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let KECCAK1_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl and rc = find_read_fact `RSI` k gl in
  let s1 = lane_state a k gl in
  (RC_TAC rc k THEN TO_WBYTES_TAC a k THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,
     SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT_F1600)
    ([`read RDI s`; `read RSI s`; s1; `pc:num`] @ return_args) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let CBD2_CALL_TAC exec k gl =
  let a = find_read_fact `RSI` k gl in
  let b = rand(rand(lane_state a k gl)) in
  (TO_WBYTES_TAC a k THEN
   MP_TAC(SPECL [a; `seed:byte list`; b; state_of k]
                MLKEM_NOISE_LANE_PRF_2) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   X86_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "mlkem_cbd2",mlkem_cbd2_mc,MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF)
    ([`read RDI s`; `read RSI s`; vsubst [b,`b:byte`] `mlkem_prf 2 seed b`;
      `pc + mlkem_cbd2`] @ return_args) (k+1)) gl;;

let CBD3_CALL_TAC exec k gl =
  let a = find_read_fact `RSI` k gl in
  let bl = rand(rand(concl(bytes_fact a 192 k gl))) in
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_cbd3",mlkem_cbd3_mc,MLKEM_CBD3_SUBROUTINE_CORRECT_COEFF)
   ([`read RDI s`; `read RSI s`; bl; `pc + mlkem_cbd3`] @ return_args)
   (k+1) gl;;

(*** For the safety proofs: the bounds of the callees' accesses evaluated,
 *** and the discharge of the safety property with the APPENDs normalized
 ***)

let MEMACCESS_NUMERALS_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_comb c && is_const(fst(strip_comb c)) &&
       name_of(fst(strip_comb c)) = "memaccess_inbounds"
    then CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV) th else th);;

let NATIVE2_DISCHARGE_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [FULL_UNIFY_F_EVENTS_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_ADD_0; GSYM APPEND_ASSOC; APPEND_NIL]) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM APPEND_ASSOC; APPEND_NIL] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;
