(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Layer-1 algorithmic specification of MD5 block compression (RFC 1321).    *)
(*                                                                           *)
(* The chaining state is an `int32 list` of length 4 holding [A;B;C;D] -- a  *)
(* list rather than a tuple so EL indexing and LENGTH lemmas apply and the   *)
(* four working words sit at stable positions across cut points.             *)
(*                                                                           *)
(* The K / rotate / message-index tables are transcribed in round order      *)
(* from RFC 1321, cross-checked against the C reference reference_md5_block  *)
(* in tests/test.c (differential-tested against the assembly). Round groups: *)
(* F = rounds 0..15, G = 16..31, H = 32..47, I = 48..63.                     *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The four auxiliary functions, canonical RFC 1321 form (X=b, Y=c, Z=d):    *)
(*   F(X,Y,Z) = XY v not(X)Z      G(X,Y,Z) = XZ v Y not(Z)                   *)
(*   H(X,Y,Z) = X xor Y xor Z     I(X,Y,Z) = Y xor (X v not(Z))              *)
(* The assembly computes algebraically equivalent reassociated forms; the    *)
(* Layer-2 bridge lemmas (md5_bridge.ml) prove those equal to these.         *)
(* ------------------------------------------------------------------------- *)

let md5_f = define
 `md5_f (b:int32) (c:int32) (d:int32) : int32 =
    word_or (word_and b c) (word_and (word_not b) d)`;;

let md5_g = define
 `md5_g (b:int32) (c:int32) (d:int32) : int32 =
    word_or (word_and b d) (word_and c (word_not d))`;;

let md5_h = define
 `md5_h (b:int32) (c:int32) (d:int32) : int32 =
    word_xor (word_xor b c) d`;;

let md5_i = define
 `md5_i (b:int32) (c:int32) (d:int32) : int32 =
    word_xor c (word_or b (word_not d))`;;

(* ------------------------------------------------------------------------- *)
(* Additive constants K[0..63] (the RFC 1321 "T" table, T[i+1] =             *)
(* floor(2^32 * |sin(i+1)|)), listed in round order.                         *)
(* ------------------------------------------------------------------------- *)

let md5_k = define
 `md5_k:int32 list =
   [word 0xd76aa478; word 0xe8c7b756; word 0x242070db; word 0xc1bdceee;
    word 0xf57c0faf; word 0x4787c62a; word 0xa8304613; word 0xfd469501;
    word 0x698098d8; word 0x8b44f7af; word 0xffff5bb1; word 0x895cd7be;
    word 0x6b901122; word 0xfd987193; word 0xa679438e; word 0x49b40821;
    word 0xf61e2562; word 0xc040b340; word 0x265e5a51; word 0xe9b6c7aa;
    word 0xd62f105d; word 0x02441453; word 0xd8a1e681; word 0xe7d3fbc8;
    word 0x21e1cde6; word 0xc33707d6; word 0xf4d50d87; word 0x455a14ed;
    word 0xa9e3e905; word 0xfcefa3f8; word 0x676f02d9; word 0x8d2a4c8a;
    word 0xfffa3942; word 0x8771f681; word 0x6d9d6122; word 0xfde5380c;
    word 0xa4beea44; word 0x4bdecfa9; word 0xf6bb4b60; word 0xbebfbc70;
    word 0x289b7ec6; word 0xeaa127fa; word 0xd4ef3085; word 0x04881d05;
    word 0xd9d4d039; word 0xe6db99e5; word 0x1fa27cf8; word 0xc4ac5665;
    word 0xf4292244; word 0x432aff97; word 0xab9423a7; word 0xfc93a039;
    word 0x655b59c3; word 0x8f0ccc92; word 0xffeff47d; word 0x85845dd1;
    word 0x6fa87e4f; word 0xfe2ce6e0; word 0xa3014314; word 0x4e0811a1;
    word 0xf7537e82; word 0xbd3af235; word 0x2ad7d2bb; word 0xeb86d391]`;;

(* ------------------------------------------------------------------------- *)
(* Left-rotation amounts s[0..63]: each group repeats its 4-element pattern. *)
(* ------------------------------------------------------------------------- *)

let md5_rot = define
 `md5_rot:num list =
   [7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22;
    5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20;
    4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23;
    6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21]`;;

(* ------------------------------------------------------------------------- *)
(* Message-word schedule g[0..63]: which of the 16 block words M[0..15] each *)
(* round consumes.  Per group the closed forms are i, 5i+1, 3i+5, 7i mod 16; *)
(* the explicit table is the audited source of truth.                        *)
(* ------------------------------------------------------------------------- *)

let md5_msgidx = define
 `md5_msgidx:num list =
   [0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15;
    1;  6; 11;  0;  5; 10; 15;  4;  9; 14;  3;  8; 13;  2;  7; 12;
    5;  8; 11; 14;  1;  4;  7; 10; 13;  0;  3;  6;  9; 12; 15;  2;
    0;  7; 14;  5; 12;  3; 10;  1;  8; 15;  6; 13;  4; 11;  2;  9]`;;

(* ------------------------------------------------------------------------- *)
(* One MD5 round on state l = [a;b;c;d] consuming message words m.  In the   *)
(* register-rotation formulation,                                            *)
(*    newB = b + rol(a + f(b,c,d) + K[i] + M[g[i]], s[i])                    *)
(* and the new state is [d; newB; b; c], so after every multiple of 4 rounds *)
(* the working words are back in (A,B,C,D) position, and after all 64 the    *)
(* state is ready for the Davies-Meyer add-back.                             *)
(* ------------------------------------------------------------------------- *)

let md5_round = define
 `(md5_round:num -> int32 list -> int32 list -> int32 list) i m l =
    let a = EL 0 l and b = EL 1 l and c = EL 2 l and d = EL 3 l in
    let f = (if i < 16 then md5_f b c d
             else if i < 32 then md5_g b c d
             else if i < 48 then md5_h b c d
             else md5_i b c d) in
    let t = word_add (word_add (word_add a f) (EL i md5_k))
                     (EL (EL i md5_msgidx) m) in
    [d; word_add b (word_rol t (EL i md5_rot)); b; c]`;;

(* The first n rounds, recursively in the keccak `n+1` style so cut-point    *)
(* reasoning is available at every round boundary.                           *)

let md5_rounds = define
 `md5_rounds 0 m l = l /\
  md5_rounds (n + 1) m l = md5_round n m (md5_rounds n m l)`;;

(* ------------------------------------------------------------------------- *)
(* RFC 1321 initial chaining values.                                         *)
(* ------------------------------------------------------------------------- *)

let md5_init = define
 `md5_init:int32 list =
   [word 0x67452301; word 0xefcdab89; word 0x98badcfe; word 0x10325476]`;;

(* ------------------------------------------------------------------------- *)
(* Compression of one 64-byte block (message words m, LENGTH 16): all 64     *)
(* rounds from state s, then the Davies-Meyer feed-forward add-back.         *)
(* ------------------------------------------------------------------------- *)

let md5_block = define
 `md5_block (s:int32 list) (m:int32 list) : int32 list =
    let s' = md5_rounds 64 m s in
    [word_add (EL 0 s) (EL 0 s');
     word_add (EL 1 s) (EL 1 s');
     word_add (EL 2 s) (EL 2 s');
     word_add (EL 3 s) (EL 3 s')]`;;

(* Folding the block compression over a list of blocks.                      *)

let md5_blocks = define
 `md5_blocks s [] = s /\
  md5_blocks s (CONS blk rest) = md5_blocks (md5_block s blk) rest`;;

(* ------------------------------------------------------------------------- *)
(* LENGTH lemmas: every operation yields/preserves a length-4 state.         *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MD5_ROUND = prove
 (`!i m l. LENGTH(md5_round i m l) = 4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[md5_round] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_MD5_ROUNDS = prove
 (`!n m l. LENGTH l = 4 ==> LENGTH(md5_rounds n m l) = 4`,
  INDUCT_TAC THEN
  ASM_SIMP_TAC[md5_rounds; ADD1; LENGTH_MD5_ROUND]);;

let LENGTH_MD5_BLOCK = prove
 (`!s m. LENGTH(md5_block s m) = 4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[md5_block] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_MD5_BLOCKS = prove
 (`!bl s. LENGTH s = 4 ==> LENGTH(md5_blocks s bl) = 4`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[md5_blocks; LENGTH_MD5_BLOCK]);;
