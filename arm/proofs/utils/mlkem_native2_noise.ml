(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the mlkem_native2 functions that sample noise,    *)
(* SamplePolyCBD_eta(PRF_eta(sigma, b)) of FIPS 203, in the lanes of the     *)
(* Keccak permutations: the coefficients of SamplePolyCBD, the PRF output as *)
(* the state of a lane after one or two permutations, the lane as stored by  *)
(* the code, the theorems for the callees (sha3_keccak4_f1600_alt2,          *)
(* mlkem_cbd2, mlkem_cbd3) in the forms a caller needs, and a simulation     *)
(* driver that steps through the code and takes each call as one step.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native2_image.ml";;
needs "arm/proofs/utils/mlkem_native2_sponge.ml";;
needs "arm/proofs/mlkem_cbd2.ml";;
needs "arm/proofs/mlkem_cbd3.ml";;
needs "arm/proofs/sha3_keccak4_f1600_alt2.ml";;
needs "common/fips203/fips203.ml";;

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
(* pieces of p1, ..., pk bytes, those of 16 and 8 as bytes128 and bytes64.   *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_SPLIT = prove
 (`!a:int64 m n s:armstate.
     read (memory :> bytes(a,m + n)) s =
     read (memory :> bytes(a,m)) s +
     2 EXP (8 * m) * read (memory :> bytes(word_add a (word m),n)) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

let READ_MEMORY_BYTES_16 = prove
 (`!a:int64 s:armstate.
     read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_8 = prove
 (`!a:int64 s:armstate.
     read (memory :> bytes(a,8)) s = val(read (memory :> bytes64 a) s)`,
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let BYTES_PIECES_CONV =
  let piece_conv p =
    if p = 16 then REWR_CONV READ_MEMORY_BYTES_16
    else if p = 8 then REWR_CONV READ_MEMORY_BYTES_8
    else ALL_CONV in
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
 (`!a (S:1600 word) n s:armstate.
        read (memory :> wbytes a) s = S /\ n <= 200
        ==> read (memory :> bytes(a,n)) s = val S MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A lane as stored by the code for the PRF of seed s and nonce word y: the  *)
(* 32 bytes of s (as two 16-byte loads), the nonce byte with the domain byte *)
(* 0x1f after it, zeros, and the final bit 0x80 in byte 135.                 *)
(* ------------------------------------------------------------------------- *)

let WORD_NONCE_DS = prove
 (`!y:int64. word_or (word_and y (word 255)) (word 7936) =
             word(val(word_zx y:byte) + 7936)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_or (word_and (y:int64) (word 255)) (word 7936) =
    word_add (word_zx (word_zx y:byte)) (word 7936)`] THEN
  REWRITE_TAC[word_zx; GSYM WORD_ADD]);;

let WORD_ZX_BYTE_WORD = prove
 (`!n. word_zx (word n:int64):byte = word n`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_64; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8;
              MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_NOISE_LANE = prove
 (`!a (seed:byte list) (y:int64) s:armstate.
     LENGTH seed = 32 /\
     read (memory :> bytes128 a) s =
     word(num_of_bytelist seed MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word 16))) s =
     word((num_of_bytelist seed DIV 2 EXP 128) MOD 2 EXP 128) /\
     read (memory :> bytes64 (word_add a (word 32))) s =
     word_or (word_and y (word 255)) (word 7936) /\
     read (memory :> bytes64 (word_add a (word 40))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 48))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 64))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 80))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 96))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 112))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 120))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 128))) s =
     word 9223372036854775808 /\
     read (memory :> bytes64 (word_add a (word 136))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 144))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 160))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 176))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 184))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 192))) s = word 0
     ==> read (memory :> wbytes a) s = mlkem_noise_state seed (word_zx y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; mlkem_noise_state] THEN
  CONV_TAC(LAND_CONV(BYTES_PIECES_CONV
   [16;16;8;8;16;16;16;16;8;8;8;8;16;16;8;8;8])) THEN
  ASM_REWRITE_TAC[WORD_NONCE_DS] THEN
  REWRITE_TAC[VAL_WORD; VAL_WORD_0; DIMINDEX_64; DIMINDEX_128;
              DIMINDEX_CONV `dimindex(:1600)`; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `seed:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `word_zx(y:int64):byte` VAL_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`val(word_zx(y:int64):byte)`,`v:num`) THEN
  SPEC_TAC(`num_of_bytelist(seed:byte list)`,`x:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(x DIV 2 EXP 128) MOD 2 EXP 128 = x DIV 2 EXP 128 /\
    (v + 7936) MOD 2 EXP 64 = v + 7936`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      UNDISCH_TAC `x < 256 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC;
      UNDISCH_TAC `v < 2 EXP 8` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`x < 256 EXP 32`; `v < 2 EXP 8`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`x:num`; `2 EXP 128`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The PRF output from the lane after the permutation (eta = 2), or as       *)
(* copied to a buffer, 136 bytes after the first permutation and 56 after    *)
(* the second, in the forms that the simulation of the copies gives.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NOISE_LANE_PRF_2 = prove
 (`!a (seed:byte list) b s:armstate.
        LENGTH seed = 32 /\
        read (memory :> wbytes a) s = keccak_f1600(mlkem_noise_state seed b)
        ==> read (memory :> bytes(a,128)) s =
            num_of_bytelist(mlkem_prf 2 seed b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_PRF_2_NOISE] THEN
  MP_TAC(SPECL [`a:int64`; `keccak_f1600(mlkem_noise_state seed b)`;
                `128`; `s:armstate`] READ_MEMORY_WBYTES_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let WORD_ZX_64_128 = prove
 (`!w:int64. word_zx(word_zx w:int128):int64 = w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let MOD_EXP_ADD_SPLIT = prove
 (`!x a b. x MOD 2 EXP a + 2 EXP a * (x DIV 2 EXP a) MOD 2 EXP b =
           x MOD 2 EXP (a + b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC);;

let READ_MEMORY_BYTES_136_OF_PIECES = prove
 (`!a x s:armstate.
     (!j. j < 8 ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                    word((x DIV 2 EXP (128 * j)) MOD 2 EXP 128)) /\
     read (memory :> bytes64(word_add a (word 128))) s =
     word((x DIV 2 EXP 1024) MOD 2 EXP 64)
     ==> read (memory :> bytes(a,136)) s = x MOD 2 EXP 1088`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `136 = 16 * 8 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_BYTES128) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MOD_EXP_ADD_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_192_PRF_3 = prove
 (`!a (seed:byte list) b s:armstate.
     LENGTH seed = 32 /\
     read (memory :> bytes(a,136)) s =
     val(keccak_f1600(mlkem_noise_state seed b)) MOD 2 EXP 1088 /\
     (!j. j < 3
          ==> read (memory :> bytes128(word_add a (word(136 + 16 * j)))) s =
              word((val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b)))
                    DIV 2 EXP (128 * j)) MOD 2 EXP 128)) /\
     read (memory :> bytes64(word_add a (word 184))) s =
     word_zx(word((val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b)))
                   DIV 2 EXP 384) MOD 2 EXP 128):int128)
     ==> read (memory :> bytes(a,192)) s =
         num_of_bytelist(mlkem_prf 3 seed b)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `y = val(keccak_f1600(keccak_f1600(mlkem_noise_state seed b)))` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_PRF_3_NOISE] THEN
  REWRITE_TAC[ARITH_RULE `192 = 136 + 56`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`; EQ_ADD_LCANCEL;
                  EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `56 = 16 * 3 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  MP_TAC(ISPECL [`word_add a (word 136):int64`; `3`; `y:num`; `s:armstate`]
    READ_MEMORY_BYTES_OF_BYTES128) THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_8] THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  ASM_REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_128;
                  MOD_MOD_EXP_MIN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  MP_TAC(SPECL [`y:num`; `384`; `64`] MOD_EXP_ADD_SPLIT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The theorems for the callees in the forms a caller needs: the x4          *)
(* permutation on four states as 1600-bit words, mlkem_cbd2 and mlkem_cbd3   *)
(* with the coefficients of SamplePolyCBD, and the constant-time and memory  *)
(* safety of the latter with the frames of their correctness theorems (that  *)
(* of the x4 permutation, SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED, is *)
(* in its file).                                                             *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600 = prove
 (`!a rc (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
    pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S1 /\
                read (memory :> wbytes(word_add a (word 200))) s = S2 /\
                read (memory :> wbytes(word_add a (word 400))) s = S3 /\
                read (memory :> wbytes(word_add a (word 600))) s = S4 /\
                wordlist_from_memory(rc,24) s = round_constants)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S1 /\
                read (memory :> wbytes(word_add a (word 200))) s =
                keccak_f1600 S2 /\
                read (memory :> wbytes(word_add a (word 400))) s =
                keccak_f1600 S3 /\
                read (memory :> wbytes(word_add a (word 600))) s =
                keccak_f1600 S4)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `rc:int64`;
                `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
               SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

let MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF = prove
 (`!r a (b:byte list) pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x10c); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = num_of_bytelist b)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 2 b i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLKEM_CBD_COEFF_2] THEN
  ACCEPT_TAC(SPECL [`r:int64`; `a:int64`; `num_of_bytelist(b:byte list)`;
                    `pc:num`; `returnaddress:int64`]
                   MLKEM_CBD2_SUBROUTINE_CORRECT));;

let MLKEM_CBD3_SUBROUTINE_CORRECT_COEFF = prove
 (`!r a (b:byte list) pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xd4); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = num_of_bytelist b)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 3 b i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLKEM_CBD_COEFF_3] THEN
  ACCEPT_TAC(SPECL [`r:int64`; `a:int64`; `num_of_bytelist(b:byte list)`;
                    `pc:num`; `returnaddress:int64`]
                   MLKEM_CBD3_SUBROUTINE_CORRECT));;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_cbd2" subroutine_signatures)
    MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CBD2_EXEC;;

let MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0x108; a,128]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD2_EXEC);;

let MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0x10c; a,128]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd2_mc mlkem_cbd2_tmc MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE_FRAMED));;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_cbd3" subroutine_signatures)
    MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CBD3_EXEC;;

let MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0xd0; a,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD3_EXEC);;

let MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0xd4; a,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd3_mc mlkem_cbd3_tmc MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED));;

(* ------------------------------------------------------------------------- *)
(* A simulation driver for code whose control flow is fixed once its         *)
(* parameters are: NATIVE2_RUN_TAC exec derive calls k steps from state sk   *)
(* until the return (the PC no longer an offset of pc), first applying the   *)
(* tactic in derive for the PC offset of the current state if there is one   *)
(* (to add facts), and then the one in calls (to take a call as one step to  *)
(* the next state) or otherwise one step of the code. The states of the      *)
(* Keccak lanes are kept as read (memory :> bytes(a,200)) s = val S, which   *)
(* unlike the wbytes form the simulation keeps over other stores, and the    *)
(* round constants as read (memory :> bytes(rc,192)) s = ...                 *)
(* ------------------------------------------------------------------------- *)

let state_of k = mk_var("s"^string_of_int k,`:armstate`);;

let find_asm p (asl,w) = snd(find (fun (_,th) -> p (concl th)) asl);;

let asm_with_lhs lhs gl =
  find_asm (fun c -> try lhand c = lhs with Failure _ -> false) gl;;

let get_pc_offset k (asl,w as gl) =
  let th = asm_with_lhs (mk_comb(`read PC`,state_of k)) gl in
  try let t = rand(rand(concl th)) in
      if is_comb t && is_comb(rator t) && name_of(rator(rator t)) = "+" &&
         rand(rator t) = `pc:num`
      then dest_small_numeral(rand t) else -1
  with Failure _ -> -1;;

let find_read_fact comp k gl =
  rand(concl(asm_with_lhs
    (mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,comp),
             state_of k)) gl));;

let normalize_addr tm =
  try rand(concl(NORMALIZE_RELATIVE_ADDRESS_CONV tm)) with Failure _ -> tm;;

let addr_plus a off =
  if off = 0 then a else
  normalize_addr(mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral off)));;

let bytes_fact a n k gl =
  asm_with_lhs (vsubst [a,`a:int64`; mk_small_numeral n,`n:num`;
                        state_of k,`s:armstate`]
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

let SIMP_REG_TAC reg thms k =
  let lhs = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                    reg),state_of k) in
  FIRST_X_ASSUM(fun th ->
    if lhand(concl th) = lhs then ASSUME_TAC(REWRITE_RULE thms th)
    else NO_TAC);;

(* Each step adds the components it writes to the frame assumption
   (MAYCHANGE ...) s0 sk, which every later step processes again, so over a
   long run it would grow to thousands of terms. NATIVE2_FRAME_TAC replaces
   it by the frame of the postcondition of the goal, which subsumes it as it
   does at the end, and the drivers call it every 50 steps. It leaves a
   frame with variables that the goal's has not (such as the abbreviated
   frame base of the x86 API proofs), as the subsumption then needs more
   than MONOTONE_MAYCHANGE_TAC. *)

let NATIVE2_FRAME_TAC (asl,w as gl) =
  let sv = rand w in
  let isframe c =
    is_comb c && rand c = sv && maychange_term c &&
    is_comb(rator c) && type_of(rand(rator c)) = type_of sv in
  match (try let bv,body = dest_abs(rand(rator w)) in
             let fr = vsubst [sv,bv] (find maychange_term (conjuncts body)) in
             Some(fr,find (isframe o concl) (map snd asl))
         with Failure _ -> None) with
    Some(fr,old) when concl old <> fr &&
                      subset (frees(concl old)) (frees fr) ->
      UNDISCH_THEN (concl old) (fun th ->
        SUBGOAL_THEN fr ASSUME_TAC THENL
         [POP_ASSUM_LIST(K ALL_TAC) THEN ASSUME_TAC th THEN
          MONOTONE_MAYCHANGE_TAC;
          ALL_TAC]) gl
  | _ -> ALL_TAC gl;;

let rec NATIVE2_RUN_TAC exec derive calls k gl =
  let off = get_pc_offset k gl in
  if off < 0 then ALL_TAC gl else
  let dtac = try (assoc off derive) k with Failure _ -> ALL_TAC in
  let ctac = try (assoc off calls) k
             with Failure _ -> ARM_STEPS_TAC exec [k+1] in
  ((if k > 0 && k mod 50 = 0 then NATIVE2_FRAME_TAC else ALL_TAC) THEN
   dtac THEN ctac THEN NATIVE2_RUN_TAC exec derive calls (k+1)) gl;;

(*** The calls: the x4 and x1 permutations on the lanes at X0 with the
 *** round constants at X1, mlkem_cbd2 on the 128 bytes of the lane at X1
 *** after a permutation, and mlkem_cbd3 on 192 bytes known at X1.
 ***)

let KECCAK4_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl and rc = find_read_fact `X1` k gl in
  let ads = map (addr_plus a) [0;200;400;600] in
  let ss = map (fun ad -> lane_state ad k gl) ads in
  (RC_TAC rc k THEN MAP_EVERY (fun ad -> TO_WBYTES_TAC ad k) ads THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "sha3_keccak4_f1600_alt2",sha3_keccak4_f1600_alt2_mc,
     SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600)
    ([`read X0 s`; `read X1 s`] @ ss @
     [`pc + sha3_keccak4_f1600_alt2`; `read SP s`; `read X30 s`]) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let KECCAK1_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl and rc = find_read_fact `X1` k gl in
  let s1 = lane_state a k gl in
  (RC_TAC rc k THEN TO_WBYTES_TAC a k THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "sha3_keccak_f1600",sha3_keccak_f1600_mc,
     SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600)
    [`read X0 s`; `read X1 s`; s1; `pc + sha3_keccak_f1600`; `read SP s`;
     `read X30 s`] (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let CBD2_CALL_TAC exec k gl =
  let a = find_read_fact `X1` k gl in
  let b = rand(rand(lane_state a k gl)) in
  (TO_WBYTES_TAC a k THEN
   MP_TAC(SPECL [a; `seed:byte list`; b; state_of k]
                MLKEM_NOISE_LANE_PRF_2) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "mlkem_cbd2",mlkem_cbd2_mc,MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF)
    [`read X0 s`; `read X1 s`; vsubst [b,`b:byte`] `mlkem_prf 2 seed b`;
     `pc + mlkem_cbd2`; `read X30 s`] (k+1)) gl;;

let CBD3_CALL_TAC exec k gl =
  let a = find_read_fact `X1` k gl in
  let bl = rand(rand(concl(bytes_fact a 192 k gl))) in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_cbd3",mlkem_cbd3_mc,MLKEM_CBD3_SUBROUTINE_CORRECT_COEFF)
   [`read X0 s`; `read X1 s`; bl; `pc + mlkem_cbd3`; `read X30 s`] (k+1) gl;;

(*** For the safety proofs: a call by its theorem in the assumptions with
 *** the label given
 ***)

let NATIVE2_SAFE_CALL_TAC exec vars label (offset,submc) ilist k =
  REMOVE_THEN label (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,offset,submc,th) ilist (k+1) THENL
     [EXISTS_E2_TAC (ref vars); LABEL_TAC label th]);;

(* ------------------------------------------------------------------------- *)
(* For the safety proofs. The events of a long simulation are a big term,    *)
(* which the steps rewrite, and every step of the proof is instantiated with *)
(* them when the events function of the theorem (a metavariable) is found at *)
(* the end. So NATIVE2_SAFE_RUN_TAC, the driver for these proofs, puts the   *)
(* events every 50 steps as APPEND (T x1 ... xn) e, T a new constant defined *)
(* as the events since e in terms of their free variables x1 ... xn, and the *)
(* discharge of the safety property at the end expands these definitions for *)
(* the memory accesses only, which it proves segment by segment: the runs of *)
(* events and the events of the calls.                                       *)
(* ------------------------------------------------------------------------- *)

let native2_trace_count = ref 0;;

let native2_trace_defs = ref ([]:thm list);;

(*** The events at state k, CONS and APPEND down to e, as APPEND (T x1 ...
 *** xn) e, unless they are already in that form
 ***)

let NATIVE2_TRACE_DEFINE_TAC k (asl,w as gl) =
  let lhs = mk_comb(`read events`,state_of k) in
  match List.find_opt (fun (_,th) -> try lhand(concl th) = lhs
                                     with Failure _ -> false) asl with
    None -> ALL_TAC gl
  | Some(_,th) ->
    let t = rand(concl th) and e = `e:(uarch_event)list` in
    let rec prefix t =
      if t = e then None else
      match t with
        Comb(Comb(Const("CONS",_) as c,h),tl) ->
          (match prefix tl with
             None -> Some(mk_comb(mk_comb(c,h),mk_list([],type_of h)))
           | Some x -> Some(mk_comb(mk_comb(c,h),x)))
      | Comb(Comb(Const("APPEND",_) as a,l),tl) ->
          (match prefix tl with
             None -> Some l
           | Some x -> Some(mk_comb(mk_comb(a,l),x)))
      | _ -> failwith "NATIVE2_TRACE_DEFINE_TAC" in
    let defined x =
      let h = fst(strip_comb x) in
      is_const h &&
      (let n = fst(dest_const h) in
       String.length n > 14 && String.sub n 0 14 = "native2_trace_") in
    match (try prefix t with Failure _ -> None) with
      None -> ALL_TAC gl
    | Some x when defined x -> ALL_TAC gl
    | Some x ->
      let fvs = frees x in
      incr native2_trace_count;
      let name = "native2_trace_"^string_of_int(!native2_trace_count) in
      let ty = itlist (mk_fun_ty o type_of) fvs (type_of x) in
      let def = new_definition(mk_eq(list_mk_comb(mk_var(name,ty),fvs),x)) in
      native2_trace_defs := def :: !native2_trace_defs;
      let eqth = prove(mk_eq(t,list_mk_icomb "APPEND" [x; e]),
                       REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]) in
      let th' = TRANS th (TRANS eqth
                  (AP_THM (AP_TERM (rator(rator(rand(concl eqth))))
                                   (SYM(SPECL fvs def))) e)) in
      RULE_ASSUM_TAC(fun th0 -> if concl th0 = concl th then th' else th0) gl;;

(*** The driver for the safety proofs: NATIVE2_RUN_TAC with the events put
 *** as above every 50 steps
 ***)

let rec NATIVE2_SAFE_RUN_TAC exec derive calls k gl =
  let off = get_pc_offset k gl in
  if off < 0 then ALL_TAC gl else
  let dtac = try (assoc off derive) k with Failure _ -> ALL_TAC in
  let ctac = try (assoc off calls) k
             with Failure _ -> ARM_STEPS_TAC exec [k+1] in
  ((if k mod 50 = 0 then NATIVE2_TRACE_DEFINE_TAC k else ALL_TAC) THEN
   (if k > 0 && k mod 50 = 0 then NATIVE2_FRAME_TAC else ALL_TAC) THEN
   dtac THEN ctac THEN NATIVE2_SAFE_RUN_TAC exec derive calls (k+1)) gl;;

(*** The bounds of the callees' accesses evaluated ***)

let MEMACCESS_NUMERALS_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_comb c && is_const(fst(strip_comb c)) &&
       name_of(fst(strip_comb c)) = "memaccess_inbounds"
    then CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV) th else th);;

(*** The memory accesses of the events, the definitions above expanded and
 *** the addresses normalized by normtac, as an APPEND of the runs of
 *** events (as lists) and of the events of the calls, each proved within
 *** the bounds by itself (the latter by the facts of the calls); if that
 *** fails, as for the whole events
 ***)

let rec NATIVE2_SEGMENTS_CONV t =
  match t with
    Comb(Comb(Const("APPEND",_),_),_) -> RAND_CONV NATIVE2_SEGMENTS_CONV t
  | Comb(Comb(Const("CONS",_),_),_) ->
      (CONS_TO_APPEND_CONV THENC RAND_CONV NATIVE2_SEGMENTS_CONV) t
  | _ -> REFL t;;

let NATIVE2_MEMACCESS_SEGMENTS_TAC normtac =
  W(fun _ -> REWRITE_TAC !native2_trace_defs) THEN normtac THEN
  REWRITE_TAC[WORD_ADD_0; GSYM APPEND_ASSOC; APPEND_NIL] THEN
  ((CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV NATIVE2_SEGMENTS_CONV))) THEN
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND; APPEND_NIL] THEN
    REPEAT CONJ_TAC THEN
    ((DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE
     DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC) THEN NO_TAC) ORELSE
   DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** The discharge of the safety property with the APPENDs normalized, and
 *** with normtac for the addresses in the expanded events
 ***)

let NATIVE2_DISCHARGE_SAFETY_NORM_TAC normtac =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [FULL_UNIFY_F_EVENTS_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_ADD_0; GSYM APPEND_ASSOC; APPEND_NIL]) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM APPEND_ASSOC; APPEND_NIL] THEN
    NATIVE2_MEMACCESS_SEGMENTS_TAC normtac];;

let NATIVE2_DISCHARGE_SAFETY_TAC = NATIVE2_DISCHARGE_SAFETY_NORM_TAC ALL_TAC;;
