(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of the SHA-256 hash computation (FIPS 180-4).               *)
(*                                                                           *)
(* The compression-function primitives sha_choose (Ch), sha_maj (Maj) and    *)
(* sha_hash_sigma_0/1 (the "big" Sigma_0/Sigma_1) are reused from the ARM    *)
(* SHA-256 intrinsics specification arm/proofs/sha256.ml, which depends      *)
(* only on the word library. This file adds the message-schedule sigmas,     *)
(* the round-constant table, the message schedule, the compression rounds    *)
(* and the (multi-)block hash function, all on int32 list state.             *)
(*                                                                           *)
(* A message block is a list of 16 int32 words, i.e. the 64 data bytes       *)
(* already assembled big-endian (FIPS 180-4 section 5.2.1); a hash state is  *)
(* a list of 8 int32 words [a;b;c;d;e;f;g;h].                                *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "arm/proofs/sha256.ml";;

(* ------------------------------------------------------------------------- *)
(* The message-schedule "small" sigma functions (FIPS 180-4, section 4.1.2). *)
(* ------------------------------------------------------------------------- *)

let sha_msg_sigma_0 = new_definition
  `sha_msg_sigma_0 (x:int32) : int32 =
          word_xor (word_ror x 7) (word_xor (word_ror x 18) (word_ushr x 3))`;;

let sha_msg_sigma_1 = new_definition
  `sha_msg_sigma_1 (x:int32) : int32 =
          word_xor (word_ror x 17) (word_xor (word_ror x 19) (word_ushr x 10))`;;

(* ------------------------------------------------------------------------- *)
(* The 64 round constants (FIPS 180-4, section 4.2.2).                       *)
(* ------------------------------------------------------------------------- *)

let sha256_constants = define
 `sha256_constants:int32 list =
   [word 0x428a2f98; word 0x71374491; word 0xb5c0fbcf; word 0xe9b5dba5;
    word 0x3956c25b; word 0x59f111f1; word 0x923f82a4; word 0xab1c5ed5;
    word 0xd807aa98; word 0x12835b01; word 0x243185be; word 0x550c7dc3;
    word 0x72be5d74; word 0x80deb1fe; word 0x9bdc06a7; word 0xc19bf174;
    word 0xe49b69c1; word 0xefbe4786; word 0x0fc19dc6; word 0x240ca1cc;
    word 0x2de92c6f; word 0x4a7484aa; word 0x5cb0a9dc; word 0x76f988da;
    word 0x983e5152; word 0xa831c66d; word 0xb00327c8; word 0xbf597fc7;
    word 0xc6e00bf3; word 0xd5a79147; word 0x06ca6351; word 0x14292967;
    word 0x27b70a85; word 0x2e1b2138; word 0x4d2c6dfc; word 0x53380d13;
    word 0x650a7354; word 0x766a0abb; word 0x81c2c92e; word 0x92722c85;
    word 0xa2bfe8a1; word 0xa81a664b; word 0xc24b8b70; word 0xc76c51a3;
    word 0xd192e819; word 0xd6990624; word 0xf40e3585; word 0x106aa070;
    word 0x19a4c116; word 0x1e376c08; word 0x2748774c; word 0x34b0bcb5;
    word 0x391c0cb3; word 0x4ed8aa4a; word 0x5b9cca4f; word 0x682e6ff3;
    word 0x748f82ee; word 0x78a5636f; word 0x84c87814; word 0x8cc70208;
    word 0x90befffa; word 0xa4506ceb; word 0xbef9a3f7; word 0xc67178f2]`;;

(* ------------------------------------------------------------------------- *)
(* The initial hash value (FIPS 180-4, section 5.3.3).                       *)
(* ------------------------------------------------------------------------- *)

let sha256_iv = define
 `sha256_iv:int32 list =
   [word 0x6a09e667; word 0xbb67ae85; word 0x3c6ef372; word 0xa54ff53a;
    word 0x510e527f; word 0x9b05688c; word 0x1f83d9ab; word 0x5be0cd19]`;;

(* ------------------------------------------------------------------------- *)
(* The message schedule W_t for a 16-word block m (FIPS 180-4, sec. 6.2.2).  *)
(* ------------------------------------------------------------------------- *)

let sha256_msg_schedule = define
 `sha256_msg_schedule (m:int32 list) (t:num) : int32 =
        if t < 16 then EL t m
        else word_add
              (word_add (sha_msg_sigma_1 (sha256_msg_schedule m (t - 2)))
                        (sha256_msg_schedule m (t - 7)))
              (word_add (sha_msg_sigma_0 (sha256_msg_schedule m (t - 15)))
                        (sha256_msg_schedule m (t - 16)))`;;

(* ------------------------------------------------------------------------- *)
(* A single compression round on the 8-word working state, with round        *)
(* constant k and message-schedule word w (FIPS 180-4, section 6.2.2 step 3).*)
(* ------------------------------------------------------------------------- *)

let sha256_round = new_definition
 `sha256_round (hsh:int32 list) (k:int32) (w:int32) : int32 list =
        let a = EL 0 hsh and b = EL 1 hsh and c = EL 2 hsh and d = EL 3 hsh
        and e = EL 4 hsh and f = EL 5 hsh and g = EL 6 hsh and h = EL 7 hsh in
        let t1 = word_add h
                  (word_add (sha_hash_sigma_1 e)
                            (word_add (sha_choose e f g) (word_add k w))) in
        let t2 = word_add (sha_hash_sigma_0 a) (sha_maj a b c) in
        [word_add t1 t2; a; b; c; word_add d t1; e; f; g]`;;

(* ------------------------------------------------------------------------- *)
(* n rounds of compression of block m starting from working state hsh.       *)
(* ------------------------------------------------------------------------- *)

let sha256_compress_rounds = define
 `sha256_compress_rounds (m:int32 list) (hsh:int32 list) 0 = hsh /\
  sha256_compress_rounds m hsh (n + 1) =
        sha256_round (sha256_compress_rounds m hsh n)
                     (EL n sha256_constants)
                     (sha256_msg_schedule m n)`;;

(* ------------------------------------------------------------------------- *)
(* The full compression of one block: 64 rounds then the feed-forward        *)
(* addition of the input hash state (FIPS 180-4, section 6.2.2 step 4).      *)
(* ------------------------------------------------------------------------- *)

let sha256_block = new_definition
 `sha256_block (m:int32 list) (hsh:int32 list) : int32 list =
        let res = sha256_compress_rounds m hsh 64 in
        [word_add (EL 0 res) (EL 0 hsh); word_add (EL 1 res) (EL 1 hsh);
         word_add (EL 2 res) (EL 2 hsh); word_add (EL 3 res) (EL 3 hsh);
         word_add (EL 4 res) (EL 4 hsh); word_add (EL 5 res) (EL 5 hsh);
         word_add (EL 6 res) (EL 6 hsh); word_add (EL 7 res) (EL 7 hsh)]`;;

(* ------------------------------------------------------------------------- *)
(* Hashing n consecutive blocks, where m gives the i'th 16-word block.       *)
(* ------------------------------------------------------------------------- *)

let sha256_hash_blocks = define
 `sha256_hash_blocks (m:num->int32 list) (hsh:int32 list) 0 = hsh /\
  sha256_hash_blocks m hsh (n + 1) =
        sha256_block (m n) (sha256_hash_blocks m hsh n)`;;

(* ------------------------------------------------------------------------- *)
(* Length sanity lemmas: everything stays an 8-word state.                   *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA256_ROUND = prove
 (`!hsh k w. LENGTH(sha256_round hsh k w) = 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA256_COMPRESS_ROUNDS = prove
 (`!m hsh n. LENGTH hsh = 8
             ==> LENGTH(sha256_compress_rounds m hsh n) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha256_compress_rounds; ADD1; LENGTH_SHA256_ROUND]);;

let LENGTH_SHA256_BLOCK = prove
 (`!m hsh. LENGTH(sha256_block m hsh) = 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_SHA256_HASH_BLOCKS = prove
 (`!m hsh n. LENGTH hsh = 8
             ==> LENGTH(sha256_hash_blocks m hsh n) = 8`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sha256_hash_blocks; ADD1; LENGTH_SHA256_BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of sha256_block on literal arguments, by memoizing one         *)
(* theorem per message-schedule word and one per compression round.          *)
(* ------------------------------------------------------------------------- *)

let SHA256_BLOCK_CONV : conv =
  let block_pat = `sha256_block m (h:int32 list)`
  and msched_pat = `sha256_msg_schedule m t`
  and rounds_pat = `sha256_compress_rounds m h t`
  and rounds_succ_pat = `sha256_compress_rounds m h (t + 1)`
  and el_k_pat = `EL t sha256_constants`
  and m_tm = `m:int32 list` and h_tm = `h:int32 list` and t_tm = `t:num` in
  let kthm = Array.init 64 (fun t ->
    (REWRITE_CONV[sha256_constants] THENC EL_CONV)
      (vsubst [mk_small_numeral t,t_tm] el_k_pat)) in
  fun tm ->
    match tm with
      Comb(Comb(Const("sha256_block",_),mtm),htm) ->
        let inst t pat =
          vsubst [mtm,m_tm; htm,h_tm; mk_small_numeral t,t_tm] pat in
        let msched = Array.make 64 TRUTH in
        (for t = 0 to 15 do
           msched.(t) <-
             CONV_RULE(RAND_CONV(DEPTH_CONV NUM_RED_CONV THENC
                                 REWRITE_CONV[] THENC EL_CONV))
               (REWR_CONV sha256_msg_schedule (inst t msched_pat))
         done;
         for t = 16 to 63 do
           msched.(t) <-
             CONV_RULE(RAND_CONV(DEPTH_CONV NUM_RED_CONV THENC
                 REWRITE_CONV[msched.(t-2); msched.(t-7); msched.(t-15);
                              msched.(t-16);
                              sha_msg_sigma_0; sha_msg_sigma_1] THENC
                 WORD_REDUCE_CONV))
               (REWR_CONV sha256_msg_schedule (inst t msched_pat))
         done);
        let round_th = Array.make 65 TRUTH in
        round_th.(0) <-
          REWRITE_CONV[sha256_compress_rounds] (inst 0 rounds_pat);
        for t = 0 to 63 do
          round_th.(t+1) <-
            CONV_RULE(LAND_CONV(RAND_CONV NUM_RED_CONV))
              ((REWRITE_CONV[sha256_compress_rounds] THENC
                REWRITE_CONV[round_th.(t); kthm.(t); msched.(t);
                             sha256_round] THENC
                TOP_DEPTH_CONV let_CONV THENC
                DEPTH_CONV EL_CONV THENC
                REWRITE_CONV[sha_choose; sha_maj;
                             sha_hash_sigma_0; sha_hash_sigma_1] THENC
                WORD_REDUCE_CONV) (inst t rounds_succ_pat))
        done;
        CONV_RULE(RAND_CONV(
            REWRITE_CONV[round_th.(64)] THENC
            TOP_DEPTH_CONV let_CONV THENC
            DEPTH_CONV EL_CONV THENC
            WORD_REDUCE_CONV))
          (REWR_CONV sha256_block tm)
    | _ -> failwith "SHA256_BLOCK_CONV: inapplicable";;

(* ------------------------------------------------------------------------- *)
(* Spec KAT: FIPS 180-4 single-block known answer, SHA256("abc").            *)
(* "abc" padded per section 5.1.1 and assembled big-endian per 5.2.1;        *)
(* expected digest ba7816bf 8f01cfea 414140de 5dae2223                       *)
(*                 b00361a3 96177a9c b410ff61 f20015ad.                      *)
(* Failure of this proof means the spec is wrong; it gates every load.       *)
(* ------------------------------------------------------------------------- *)

let SHA256_ABC_KAT = prove
 (`sha256_block
    [word 0x61626380; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0;
     word 0; word 0; word 0; word 0x18]
    sha256_iv =
   [word 0xba7816bf; word 0x8f01cfea; word 0x414140de; word 0x5dae2223;
    word 0xb00361a3; word 0x96177a9c; word 0xb410ff61; word 0xf20015ad]`,
  REWRITE_TAC[sha256_iv] THEN
  CONV_TAC(LAND_CONV SHA256_BLOCK_CONV) THEN REFL_TAC);;
