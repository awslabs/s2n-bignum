(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of the SHA-512 hash computation (FIPS 180-4).               *)
(*                                                                           *)
(* This is the int64 analogue of x86/proofs/utils/sha256_spec.ml.  Unlike    *)
(* SHA-256, the compression-function primitives are defined FRESH here: the  *)
(* ARM SHA-256 intrinsics specification arm/proofs/sha256.ml defines          *)
(* sha_choose/sha_maj/sha_hash_sigma_0/1 monomorphically on int32, so they    *)
(* cannot be reused at int64.  We therefore (re)define the choose/maj/Sigma   *)
(* primitives, the message-schedule sigmas, the round-constant table, the     *)
(* message schedule, the compression rounds and the (multi-)block hash        *)
(* function, all on int64 list state.                                         *)
(*                                                                           *)
(* A message block is a list of 16 int64 words, i.e. the 128 data bytes      *)
(* already assembled big-endian (FIPS 180-4 section 5.2.1); a hash state is  *)
(* a list of 8 int64 words [a;b;c;d;e;f;g;h].                                *)
(*                                                                           *)
(* The rotate/shift amounts are the SHA-512 (FIPS 180-4 section 4.1.3)        *)
(* values: Sigma_0 = ROTR28 xor ROTR34 xor ROTR39, Sigma_1 = ROTR14 xor      *)
(* ROTR18 xor ROTR41, sigma_0 = ROTR1 xor ROTR8 xor SHR7, sigma_1 = ROTR19   *)
(* xor ROTR61 xor SHR6.                                                       *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The "choose" and "majority" functions (FIPS 180-4, section 4.1.3), on      *)
(* int64.  Identical algebraic form to the SHA-256 versions, widened.         *)
(* ------------------------------------------------------------------------- *)

let sha512_choose = new_definition
  `sha512_choose (x:int64) (y:int64) (z:int64) : int64 =
          word_xor (word_and (word_xor y z) x) z`;;

let sha512_maj = new_definition
  `sha512_maj (x:int64) (y:int64) (z:int64) : int64 =
          word_or (word_and x y) (word_and (word_or x y) z)`;;

(* ------------------------------------------------------------------------- *)
(* The "big" Sigma functions (FIPS 180-4, section 4.1.3), on int64.           *)
(* ------------------------------------------------------------------------- *)

let sha512_hash_sigma_0 = new_definition
  `sha512_hash_sigma_0 (x:int64) : int64 =
          word_xor (word_ror x 28) (word_xor (word_ror x 34) (word_ror x 39))`;;

let sha512_hash_sigma_1 = new_definition
  `sha512_hash_sigma_1 (x:int64) : int64 =
          word_xor (word_ror x 14) (word_xor (word_ror x 18) (word_ror x 41))`;;

(* ------------------------------------------------------------------------- *)
(* The message-schedule "small" sigma functions (FIPS 180-4, section 4.1.3). *)
(* ------------------------------------------------------------------------- *)

let sha512_msg_sigma_0 = new_definition
  `sha512_msg_sigma_0 (x:int64) : int64 =
          word_xor (word_ror x 1) (word_xor (word_ror x 8) (word_ushr x 7))`;;

let sha512_msg_sigma_1 = new_definition
  `sha512_msg_sigma_1 (x:int64) : int64 =
          word_xor (word_ror x 19) (word_xor (word_ror x 61) (word_ushr x 6))`;;

(* ------------------------------------------------------------------------- *)
(* The 80 round constants (FIPS 180-4, section 4.2.3).                       *)
(* ------------------------------------------------------------------------- *)

let sha512_constants = define
 `sha512_constants:int64 list =
   [word 0x428a2f98d728ae22; word 0x7137449123ef65cd;
    word 0xb5c0fbcfec4d3b2f; word 0xe9b5dba58189dbbc;
    word 0x3956c25bf348b538; word 0x59f111f1b605d019;
    word 0x923f82a4af194f9b; word 0xab1c5ed5da6d8118;
    word 0xd807aa98a3030242; word 0x12835b0145706fbe;
    word 0x243185be4ee4b28c; word 0x550c7dc3d5ffb4e2;
    word 0x72be5d74f27b896f; word 0x80deb1fe3b1696b1;
    word 0x9bdc06a725c71235; word 0xc19bf174cf692694;
    word 0xe49b69c19ef14ad2; word 0xefbe4786384f25e3;
    word 0x0fc19dc68b8cd5b5; word 0x240ca1cc77ac9c65;
    word 0x2de92c6f592b0275; word 0x4a7484aa6ea6e483;
    word 0x5cb0a9dcbd41fbd4; word 0x76f988da831153b5;
    word 0x983e5152ee66dfab; word 0xa831c66d2db43210;
    word 0xb00327c898fb213f; word 0xbf597fc7beef0ee4;
    word 0xc6e00bf33da88fc2; word 0xd5a79147930aa725;
    word 0x06ca6351e003826f; word 0x142929670a0e6e70;
    word 0x27b70a8546d22ffc; word 0x2e1b21385c26c926;
    word 0x4d2c6dfc5ac42aed; word 0x53380d139d95b3df;
    word 0x650a73548baf63de; word 0x766a0abb3c77b2a8;
    word 0x81c2c92e47edaee6; word 0x92722c851482353b;
    word 0xa2bfe8a14cf10364; word 0xa81a664bbc423001;
    word 0xc24b8b70d0f89791; word 0xc76c51a30654be30;
    word 0xd192e819d6ef5218; word 0xd69906245565a910;
    word 0xf40e35855771202a; word 0x106aa07032bbd1b8;
    word 0x19a4c116b8d2d0c8; word 0x1e376c085141ab53;
    word 0x2748774cdf8eeb99; word 0x34b0bcb5e19b48a8;
    word 0x391c0cb3c5c95a63; word 0x4ed8aa4ae3418acb;
    word 0x5b9cca4f7763e373; word 0x682e6ff3d6b2b8a3;
    word 0x748f82ee5defb2fc; word 0x78a5636f43172f60;
    word 0x84c87814a1f0ab72; word 0x8cc702081a6439ec;
    word 0x90befffa23631e28; word 0xa4506cebde82bde9;
    word 0xbef9a3f7b2c67915; word 0xc67178f2e372532b;
    word 0xca273eceea26619c; word 0xd186b8c721c0c207;
    word 0xeada7dd6cde0eb1e; word 0xf57d4f7fee6ed178;
    word 0x06f067aa72176fba; word 0x0a637dc5a2c898a6;
    word 0x113f9804bef90dae; word 0x1b710b35131c471b;
    word 0x28db77f523047d84; word 0x32caab7b40c72493;
    word 0x3c9ebe0a15c9bebc; word 0x431d67c49c100d4c;
    word 0x4cc5d4becb3e42b6; word 0x597f299cfc657e2a;
    word 0x5fcb6fab3ad6faec; word 0x6c44198c4a475817]`;;

(* ------------------------------------------------------------------------- *)
(* The initial hash value (FIPS 180-4, section 5.3.5).                       *)
(* ------------------------------------------------------------------------- *)

let sha512_iv = define
 `sha512_iv:int64 list =
   [word 0x6a09e667f3bcc908; word 0xbb67ae8584caa73b;
    word 0x3c6ef372fe94f82b; word 0xa54ff53a5f1d36f1;
    word 0x510e527fade682d1; word 0x9b05688c2b3e6c1f;
    word 0x1f83d9abfb41bd6b; word 0x5be0cd19137e2179]`;;

(* ------------------------------------------------------------------------- *)
(* The message schedule W_t for a 16-word block m (FIPS 180-4, sec. 6.4.2).  *)
(* ------------------------------------------------------------------------- *)

let sha512_msg_schedule = define
 `sha512_msg_schedule (m:int64 list) (t:num) : int64 =
        if t < 16 then EL t m
        else word_add
              (word_add (sha512_msg_sigma_1 (sha512_msg_schedule m (t - 2)))
                        (sha512_msg_schedule m (t - 7)))
              (word_add (sha512_msg_sigma_0 (sha512_msg_schedule m (t - 15)))
                        (sha512_msg_schedule m (t - 16)))`;;

(* ------------------------------------------------------------------------- *)
(* A single compression round on the 8-word working state, with round        *)
(* constant k and message-schedule word w (FIPS 180-4, section 6.4.2 step 3).*)
(* ------------------------------------------------------------------------- *)

let sha512_round = new_definition
 `sha512_round (hsh:int64 list) (k:int64) (w:int64) : int64 list =
        let a = EL 0 hsh and b = EL 1 hsh and c = EL 2 hsh and d = EL 3 hsh
        and e = EL 4 hsh and f = EL 5 hsh and g = EL 6 hsh and h = EL 7 hsh in
        let t1 = word_add h
                  (word_add (sha512_hash_sigma_1 e)
                            (word_add (sha512_choose e f g) (word_add k w))) in
        let t2 = word_add (sha512_hash_sigma_0 a) (sha512_maj a b c) in
        [word_add t1 t2; a; b; c; word_add d t1; e; f; g]`;;

(* ------------------------------------------------------------------------- *)
(* n rounds of compression of block m starting from working state hsh.       *)
(* ------------------------------------------------------------------------- *)

let sha512_compress_rounds = define
 `sha512_compress_rounds (m:int64 list) (hsh:int64 list) 0 = hsh /\
  sha512_compress_rounds m hsh (n + 1) =
        sha512_round (sha512_compress_rounds m hsh n)
                     (EL n sha512_constants)
                     (sha512_msg_schedule m n)`;;

(* ------------------------------------------------------------------------- *)
(* The full compression of one block: 80 rounds then the feed-forward        *)
(* addition of the input hash state (FIPS 180-4, section 6.4.2 step 4).      *)
(* ------------------------------------------------------------------------- *)

let sha512_block = new_definition
 `sha512_block (m:int64 list) (hsh:int64 list) : int64 list =
        let res = sha512_compress_rounds m hsh 80 in
        [word_add (EL 0 res) (EL 0 hsh); word_add (EL 1 res) (EL 1 hsh);
         word_add (EL 2 res) (EL 2 hsh); word_add (EL 3 res) (EL 3 hsh);
         word_add (EL 4 res) (EL 4 hsh); word_add (EL 5 res) (EL 5 hsh);
         word_add (EL 6 res) (EL 6 hsh); word_add (EL 7 res) (EL 7 hsh)]`;;

(* ------------------------------------------------------------------------- *)
(* Hashing n consecutive blocks, where m gives the i'th 16-word block.       *)
(* ------------------------------------------------------------------------- *)

let sha512_hash_blocks = define
 `sha512_hash_blocks (m:num->int64 list) (hsh:int64 list) 0 = hsh /\
  sha512_hash_blocks m hsh (n + 1) =
        sha512_block (m n) (sha512_hash_blocks m hsh n)`;;

(* ------------------------------------------------------------------------- *)
(* Length sanity lemmas: everything stays an 8-word state.                   *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA512_ROUND = prove
 (`!hsh k w. LENGTH(sha512_round hsh k w) = 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA512_COMPRESS_ROUNDS = prove
 (`!m hsh n. LENGTH hsh = 8
             ==> LENGTH(sha512_compress_rounds m hsh n) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha512_compress_rounds; ADD1; LENGTH_SHA512_ROUND]);;

let LENGTH_SHA512_BLOCK = prove
 (`!m hsh. LENGTH(sha512_block m hsh) = 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA512_HASH_BLOCKS = prove
 (`!m hsh n. LENGTH hsh = 8
             ==> LENGTH(sha512_hash_blocks m hsh n) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha512_hash_blocks; ADD1; LENGTH_SHA512_BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of sha512_block on literal arguments, by memoizing one         *)
(* theorem per message-schedule word and one per compression round.          *)
(* ------------------------------------------------------------------------- *)

let SHA512_BLOCK_CONV : conv =
  let block_pat = `sha512_block m (h:int64 list)`
  and msched_pat = `sha512_msg_schedule m t`
  and rounds_pat = `sha512_compress_rounds m h t`
  and rounds_succ_pat = `sha512_compress_rounds m h (t + 1)`
  and el_k_pat = `EL t sha512_constants`
  and m_tm = `m:int64 list` and h_tm = `h:int64 list` and t_tm = `t:num` in
  let kthm = Array.init 80 (fun t ->
    (REWRITE_CONV[sha512_constants] THENC EL_CONV)
      (vsubst [mk_small_numeral t,t_tm] el_k_pat)) in
  fun tm ->
    match tm with
      Comb(Comb(Const("sha512_block",_),mtm),htm) ->
        let inst t pat =
          vsubst [mtm,m_tm; htm,h_tm; mk_small_numeral t,t_tm] pat in
        let msched = Array.make 80 TRUTH in
        (for t = 0 to 15 do
           msched.(t) <-
             CONV_RULE(RAND_CONV(DEPTH_CONV NUM_RED_CONV THENC
                                 REWRITE_CONV[] THENC EL_CONV))
               (REWR_CONV sha512_msg_schedule (inst t msched_pat))
         done;
         for t = 16 to 79 do
           msched.(t) <-
             CONV_RULE(RAND_CONV(DEPTH_CONV NUM_RED_CONV THENC
                 REWRITE_CONV[msched.(t-2); msched.(t-7); msched.(t-15);
                              msched.(t-16);
                              sha512_msg_sigma_0; sha512_msg_sigma_1] THENC
                 WORD_REDUCE_CONV))
               (REWR_CONV sha512_msg_schedule (inst t msched_pat))
         done);
        let round_th = Array.make 81 TRUTH in
        round_th.(0) <-
          REWRITE_CONV[sha512_compress_rounds] (inst 0 rounds_pat);
        for t = 0 to 79 do
          round_th.(t+1) <-
            CONV_RULE(LAND_CONV(RAND_CONV NUM_RED_CONV))
              ((REWRITE_CONV[sha512_compress_rounds] THENC
                REWRITE_CONV[round_th.(t); kthm.(t); msched.(t);
                             sha512_round] THENC
                TOP_DEPTH_CONV let_CONV THENC
                DEPTH_CONV EL_CONV THENC
                REWRITE_CONV[sha512_choose; sha512_maj;
                             sha512_hash_sigma_0; sha512_hash_sigma_1] THENC
                WORD_REDUCE_CONV) (inst t rounds_succ_pat))
        done;
        CONV_RULE(RAND_CONV(
            REWRITE_CONV[round_th.(80)] THENC
            TOP_DEPTH_CONV let_CONV THENC
            DEPTH_CONV EL_CONV THENC
            WORD_REDUCE_CONV))
          (REWR_CONV sha512_block tm)
    | _ -> failwith "SHA512_BLOCK_CONV: inapplicable";;

(* ------------------------------------------------------------------------- *)
(* KAT: FIPS 180-4 single-block known answer, SHA512("abc").                 *)
(* "abc" padded per section 5.1.2 and assembled big-endian per 5.2.1;        *)
(* expected digest ddaf35a1 93617aba cc417349 ae204131                       *)
(*                 12e6fa4e 89a97ea2 0a9eeee6 4b55d39a                       *)
(*                 2192992a 274fc1a8 36ba3c23 a3feebbd                       *)
(*                 454d4423 643ce80e 2a9ac94f a54ca49f.                      *)
(* Failure of this proof means the spec is wrong; it gates every load.       *)
(* ------------------------------------------------------------------------- *)

let SHA512_ABC_KAT = prove
 (`sha512_block
    [word 0x6162638000000000; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0x18]
    sha512_iv =
   [word 0xddaf35a193617aba; word 0xcc417349ae204131;
    word 0x12e6fa4e89a97ea2; word 0x0a9eeee64b55d39a;
    word 0x2192992a274fc1a8; word 0x36ba3c23a3feebbd;
    word 0x454d4423643ce80e; word 0x2a9ac94fa54ca49f]`,
  REWRITE_TAC[sha512_iv] THEN
  CONV_TAC(LAND_CONV SHA512_BLOCK_CONV) THEN REFL_TAC);;
