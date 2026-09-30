(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared definitions, lemmas and tactics for the four software-pipelined    *)
(* AES-GCM kernel proofs (aes128_gcm_enc/dec, aes256_gcm_enc/dec).           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;
needs "arm/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block (c:num) nonce rk i =
    word_reversefields 8 (aes128_cipher (ctr_block nonce (i + c)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian.
   Here c is the initial counter value (the value in the input ivec block),
   so the i-th block uses counter c + i.  Fixing c = 2 recovers the standard
   AES-GCM schedule where the first data block uses counter 2. *)

let cipher_block = new_definition
 `cipher_block (c:num) nonce rk inblock i =
    word_xor (aes_ctr_block c nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block (c:num) nonce rk inblock i =
        word_reversefields 8 (cipher_block c nonce rk inblock i)`;;

(* Restricted Htable predicate: only the entries the kernel actually reads.
   The x4-unrolled loop uses H^1..H^4 and their Karatsuba mid terms (the
   first 6 entries = offsets 0..80 of the full htable_mem layout).
   The tail loop only uses H^1..H^2 (offsets 0..32) but we assert all four
   here since the outer loop needs them and the precondition is shared. *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardare specs.         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Scalar counter representation.  Unlike the vector-IV kernels, this variant *)
(* keeps the counter block in scalar registers: after "ldp x11,x12,[x4]" the *)
(* two 64-bit halves of the (little-endian) IV live in X11 (low) and X12      *)
(* (high); the running counter is byte-reversed out of X12's top word into    *)
(* X13.  The loop rebuilds the reversed counter block via                     *)
(*   w14 = rev(w13);  x14 = orr x12 (w14 lsl 32);  Q0 = word_join x14 x11.     *)
(* These lemmas connect that scalar reconstruction back to ctr_block.         *)

let SCALAR_IV_SPLIT = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = w
   ==> ivlo = word_subword w (0,64) /\ ivhi = word_subword w (64,64)`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* Setup-block obligations for the scalar counter registers, phrased directly    *)
(* from the IV-halves join relation so that all widths stay concrete (avoids the  *)
(* type-variable ambiguity that arises if ivhi is substituted before WORD_BLAST). *)

let X11_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce c)
   ==> ivlo = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X12_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce c)
   ==> word_zx (word_zx ivhi:int32):int64 =
       word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X13_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce c)
   ==> word_zx (word_bytereverse (word_zx (word_ushr ivhi 32):int32):int32):int64
       = word_zx (word c:int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC BITBLAST_RULE);;

(* Normalisation rules for the scalar counter.  The counter lives in the 32-bit W13 *)
(* view of X13; each "add w13,w13,#1" is a 32-bit add and each read of W13 is a      *)
(* truncation, so counter expressions accumulate word_zx chains.  These two rules    *)
(* (applied alongside WORD_SIMPLE_SUBWORD_CONV while stepping) keep the counter in a *)
(* single-word_zx normal form: ZX_COUNTER_UD kills up-then-down conversions,         *)
(* ZX_COUNTER_INC pushes the 32-bit increment through the extension.                 *)

let ZX_COUNTER_UD = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`,
  CONV_TAC BITBLAST_RULE);;

let ZX_COUNTER_INC = prove
 (`word_zx (word_add (word_zx (x:int64):int32) (word 1)):int32 =
   word_add (word_zx x:int32) (word 1)`,
  CONV_TAC BITBLAST_RULE);;

(* This variant assembles the counter block on the STACK: "stp x11,x14,[sp,#OFF]"    *)
(* then "ldr q0,[sp,#OFF]".  The load reads back the two stored halves as            *)
(* word_join x14 x11, which reconstructs the reversed ctr_block.                     *)

let CTR_BLOCK_BUILD_INSERT = prove
 (`word_join
     (word_or
       (word_zx ((word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64)):int32):int64)
       (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
     (word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* Each block's counter word is "add w14,w13,#N" from                          *)
(* a fixed base w13, then byte-reversed; the W-register up/down-conversions leave *)
(* a word_zx nest around either the bare base (word (4*i+2), four zx layers) or   *)
(* the offset form word_add (word_zx (word_zx (word (4*i+2)))) (word N).  These   *)
(* two rules (int32) collapse both to word n / word_add (word n) (word m).        *)
let CTR_ZX_NORM = prove
 (`(word_zx (word_zx (word_zx (word_zx (word n:int32):int64):int32):int64):int32 = word n) /\
   (!m. word_zx (word_zx (word_add (word_zx (word_zx (word n:int32):int64):int32)
                                   (word m):int32):int64):int32
        = word_add (word n:int32) (word m))`,
  CONJ_TAC THENL [CONV_TAC BITBLAST_RULE; GEN_TAC THEN CONV_TAC BITBLAST_RULE]);;

(* The s2n-bignum simulator does not auto-merge two 64-bit stores into a       *)
(* 128-bit load, so after "stp x11,x14,[sp,#OFF]" the subsequent               *)
(* "ldr q0,[sp,#OFF]" would leave Q0 symbolic.  This tactic, spliced in AFTER  *)
(* the stp step and BEFORE the ldr step for state s<N>, derives the merged     *)
(* 128-bit read read(bytes128 (sp+OFF)) s<N> = word_join x14 x11 from the two  *)
(* bytes64 store facts, so the simulator can resolve the load against it.      *)
let MERGE_CTR128_TAC off sname =
  MP_TAC(ISPECL [`memory`;
                 mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                         mk_comb(`word:num->int64`,mk_small_numeral off));
                 mk_var(sname,`:armstate`)]
           (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN TRY DISCH_TAC;;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes128_cipher (ctr_block nonce (i + c)) rk) =
   aes_ctr_block c nonce rk i /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + c + 1)) rk) =
   aes_ctr_block c nonce rk (i + 1) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + c + 2)) rk) =
   aes_ctr_block c nonce rk (i + 2) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + c + 3)) rk) =
   aes_ctr_block c nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(i+1)+c = i+c+1`; ARITH_RULE `(i+2)+c = i+c+2`;
              ARITH_RULE `(i+3)+c = i+c+3`]);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block c nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block c nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES128 using the hardware primitives ***)

let AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
   (aese
    (aesmc
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
         rk3))
        rk4))
       rk5))
      rk6))
     rk7))
    rk8))
   rk9)
   rk10 =
   word_reversefields 8
    (aes128_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10]))`,
  REWRITE_TAC[aes128_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
          rk3))
         rk4))
        rk5))
       rk6))
      rk7))
     rk8))
    rk9)
   (word_xor rk10 inblock) =
   word_xor
    (word_reversefields 8
      (aes128_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES128_CIPHER_RECONSTRUCT]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let RECONSTRUCT_POLYVAL_REDUCE_G2 =
  REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM polyval_reduce_g2);;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

let PMUL_KARATSUBA_JOIN_ALT = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (64,64):int64)
                                 (word_subword a (0,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REWRITE_TAC[PMUL_KARATSUBA_JOIN] THEN REWRITE_TAC[WORD_XOR_SYM]);;

(* The Karatsuba recombination of the three 128-bit partial products into the 256-bit product. *)
let karatsuba_join = new_definition
 `karatsuba_join (p1:int128) (p2:int128) (p3:int128) : 256 word =
    word_join (word_join (word_subword p2 (64,64):int64)
                         (word_xor (word_subword (word_xor (word_xor p1 p2) p3) (64,64):int64)
                                   (word_subword p2 (0,64):int64)) : int128)
              (word_join (word_xor (word_subword (word_xor (word_xor p1 p2) p3) (0,64):int64)
                                   (word_subword p1 (64,64):int64))
                         (word_subword p1 (0,64):int64) : int128)`;;

(* It is linear over XOR, so the four blocks of a group may be recombined together or separately. *)
let KARATSUBA_JOIN_XOR4 = prove
 (`!p1 p2 p3 p1' p2' p3' p1'' p2'' p3'' p1''' p2''' p3''':int128.
     karatsuba_join (word_xor p1 (word_xor p1' (word_xor p1'' p1''')))
                    (word_xor p2 (word_xor p2' (word_xor p2'' p2''')))
                    (word_xor p3 (word_xor p3' (word_xor p3'' p3'''))) =
     word_xor (karatsuba_join p1''' p2''' p3''')
              (word_xor (karatsuba_join p1'' p2'' p3'')
                        (word_xor (karatsuba_join p1' p2' p3') (karatsuba_join p1 p2 p3)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[karatsuba_join] THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helpers for stepping the software-pipelined loop bodies.                  *)
(* ------------------------------------------------------------------------- *)

(* Surgical address-fold: inside `word_add in_p (word (...))` ONLY, fold a nested num offset
   (64*i+c)+d -> 64*i+(c+d) (GSYM ADD_ASSOC + NUM_ADD).  Scoped to in_p reads so it can NOT mangle
   nist_cipher_block block indices / counter arith elsewhere in the tower.  The prefetch loads
   `ldp ..,[x0,#K]` (x0=in_p+64i+64 after post-inc) settle as in_p+word((64i+64)+K); NORMALIZE_RELATIVE
   gives that nested form, this folds it to in_p+word(64i+80..) to match the s0 input-split anchors. *)
let IN_P_ADDR_FOLD_CONV : conv =
  let inner = (REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) in
  ONCE_DEPTH_CONV(fun t -> match t with
    | Comb(Comb(Const("word_add",_), v), Comb(Const("word",_), _))
        when (try fst(dest_var v) = "in_p" with _ -> false)
      -> RAND_CONV(RAND_CONV inner) t
    | _ -> failwith "IN_P_ADDR_FOLD_CONV");;

(* The (register, state index) of a fact `read R sK = ..` when R is one of the registers in    *)
(* keeplist; the steppers keep only the latest such fact for each of those registers.           *)
let gc2 keeplist c = try let l=lhs c in let rd,st=dest_comb l in let rr,cc=dest_comb rd in
   if is_const cc && mem (fst(dest_const cc)) keeplist then
     (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
        (try Some(fst(dest_const cc), int_of_string(String.sub nm 1 (String.length nm-1))) with _->None) |_->None) else None
  with _->None;;

(* Discard a fact about an OLD state when the same fact (modulo the state variable) already holds of
   the current state and no other assumption refers to that old state.  A fact refers to a state that
   occurs in it other than as the state its own left-hand read is about: the latest value of a register
   may mention an earlier state's memory read (`read Q5 s148 = .. read (memory :> ..) s99 ..`), which
   keeps s99's facts (the closers resolve that read from them) but says nothing about s148.
   The stepper re-derives the anchored memory facts, the in_p/out_p foralls and aligned_bytes_loaded
   at every step; without this they accumulate one copy per state and every ARM_STEP_TAC and
   ASM_REWRITE_TAC is linear in the assumption list. *)
let DISCARD_STALE_TAC sname : tactic = fun (asl,w) ->
  let sv = mk_var(sname,`:armstate`) in
  let is_st v = is_var v && type_of v = `:armstate` in
  let cs = map (fun (_,th) -> concl th) asl in
  let own c = try (match strip_comb (lhs c) with
                     (Const("read",_),[_;st]) when is_st st -> [st] | _ -> [])
              with Failure _ -> [] in
  let live = itlist (fun c acc ->
      let svs = filter is_st (frees c) in
      if length svs >= 2 then union (subtract svs (own c)) acc else acc) cs [] in
  let cur = filter (vfree_in sv) cs in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in
    match filter is_st (frees c) with
      [s] when s <> sv && not (mem s live) -> exists (aconv (vsubst [sv,s] c)) cur
    | _ -> false) (asl,w);;

(* The state variable of the first `read` inside a fact (used for the quantified memory facts). *)
let state_of_forall c =
  try let rd = find_term (fun t -> match t with
        Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=1 && nm.[0]='s' -> true | _->false) c in
      (match rd with Comb(_,Var(nm,_)) -> Some nm | _ -> None) with _ -> None;;

(* ------------------------------------------------------------------------- *)
(* The pipelined stepper: one ARM step followed by pruning of the assumption *)
(* list under a policy.  After the step we keep the MAYCHANGE fact of the     *)
(* current state; the in_p/out_p foralls and, depending on the policy, either *)
(* every other quantified fact or only those about the current state; the    *)
(* reads at the anchor pointers and at the listed stack-slot offsets; the    *)
(* latest member of each keyed family (a family maps a fact to Some (key,    *)
(* state index); the first matching family decides); any fact the policy    *)
(* exempts; and the latest read of each register in the keep list.  Every    *)
(* other read of an earlier state goes, and DISCARD_STALE_TAC can then sweep *)
(* the superseded copies of the kept facts.                                  *)
(* ------------------------------------------------------------------------- *)
type swp_prune =
 { anchors : term list;
   slots : string list;
   families : (term -> (string * int) option) list;
   exempt : term -> bool;
   all_foralls : bool;
   stale_gc : bool };;

let SWP_STEP_TAC_P (p:swp_prune) keeplist exec sname : tactic =
  ARM_STEP_TAC exec [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) ->
    let cs = map (fun (_,th) -> concl th) asl in
    let latest = map (fun r -> (r, itlist (fun c m ->
                   match gc2 keeplist c with Some(rr,k) when rr = r && k > m -> k | _ -> m) cs (-1)))
                   keeplist in
    let famof f c = try f c with _ -> None in
    let famlatest = map (fun f -> (f, itlist (fun c acc -> match famof f c with
                       | Some(key,k) -> (try if k > List.assoc key acc then (key,k)::List.remove_assoc key acc else acc
                                         with Not_found -> (key,k)::acc)
                       | None -> acc) cs [])) p.families in
    let is_read c = try fst(dest_const(fst(strip_comb(lhs c)))) = "read" with Failure _ -> false in
    let slot_read c = can (find_term (fun t -> match t with
          Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
            when (try fst(dest_var sp) = "stackpointer" with Failure _ -> false) ->
              mem (string_of_term n) p.slots
        | _ -> false)) (lhs c) in
    let anchored c = is_read c && (exists (fun q -> free_in q (lhs c)) p.anchors || slot_read c) in
    let is_maychange c = not (is_eq c) &&
      can (find_term (fun t -> match t with Const("MAYCHANGE",_) -> true | _ -> false)) c in
    let old_state_read c = try (match rand(lhs c) with
          Var(nm,_) -> nm <> sname && String.length nm >= 1 && nm.[0] = 's' | _ -> false)
        with Failure _ -> false in
    let rec family_stale fams c = match fams with
      | [] -> None
      | (f,lat)::rest -> (match famof f c with
                          | Some(key,k) -> Some (try k < List.assoc key lat with Not_found -> false)
                          | None -> family_stale rest c) in
    DISCARD_ASSUMPTIONS_TAC (fun th ->
      let c = concl th in
      if is_maychange c then (try string_of_term(last(snd(strip_comb c))) <> sname with Failure _ -> false)
      else if is_forall c then
        (if p.all_foralls || free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else match state_of_forall c with Some nm -> nm <> sname | None -> false)
      else match family_stale famlatest c with
           | Some stale -> stale
           | None ->
             if p.exempt c || anchored c then false
             else match gc2 keeplist c with
                    Some(r,k) -> k < List.assoc r latest
                  | None -> old_state_read c) (asl,w)) THEN
  (if p.stale_gc then DISCARD_STALE_TAC sname else ALL_TAC);;

(* The plain policy of the 128-bit proofs: anchor pointers and slots, no families, current-state
   foralls only, with the stale sweep. *)
let swp_prune_plain anchors slots =
  { anchors = anchors; slots = slots; families = []; exempt = (fun _ -> false);
    all_foralls = false; stale_gc = true };;
let SWP_STEP_TAC (anchors:term list) (slots:string list) keeplist exec sname : tactic =
  SWP_STEP_TAC_P (swp_prune_plain anchors slots) keeplist exec sname;;

(* Steps k in ks of a leg: SWP_STEP_TAC, the address and subword normalization, a per-leg
   simplification of the fresh facts (extra k), and the counter-slot merge at the recorded store steps. *)
let SWP_STEPS_TAC anchors slots keeplist exec (extra:int->tactic) merges (ks:int list) : tactic =
  MAP_EVERY (fun k ->
    let sname = "s" ^ string_of_int k in
    SWP_STEP_TAC anchors slots keeplist exec sname THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
    extra k THEN
    (if List.mem_assoc k merges then MERGE_CTR128_TAC (List.assoc k merges) sname else ALL_TAC)) ks;;

(* ------------------------------------------------------------------------- *)
(* Leaf closers for the constant-time and memory-safety proofs (shared with  *)
(* the four safety proofs).                                                  *)
(* ------------------------------------------------------------------------- *)

let lc_eq = prove
 (`nblocks DIV 4 = loop_count /\ len_bits DIV 128 = nblocks
    ==> loop_count = len_bits DIV 512`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks DIV 4 = loop_count`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `len_bits DIV 128 = nblocks`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV);;

let lr_eq = prove
 (`nblocks MOD 4 = loop_remain /\ len_bits DIV 128 = nblocks
    ==> loop_remain = len_bits DIV 128 MOD 4`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks MOD 4 = loop_remain`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

let WSUB_BRANCH = prove
 (`!i k:num. i < k /\ k < 2 EXP 64
     ==> (~(val(word_sub (word (k - i):int64) (word 1)) = 0) <=> i + 1 < k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word (k - i):int64) = k - i` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `k:num` THEN ASM_SIMP_TAC[LE_REFL] THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD_1] THEN
    SIMP_TAC[DIMINDEX_64; ARITH_RULE `1 < 2 EXP 64`] THEN ASM_ARITH_TAC]);;

let DEABBR : tactic =
  W(fun (asl,w) ->
    let lcth = try [MATCH_MP lc_eq (CONJ (ASSUME `nblocks DIV 4 = loop_count`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let lrth = try [MATCH_MP lr_eq (CONJ (ASSUME `nblocks MOD 4 = loop_remain`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let vwth = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && (match lhs t with
                         Comb(v,Comb(wd,_)) ->
                           (try name_of v = "val" && name_of wd = "word" with _ -> false)
                       | _ -> false)
        then th else fail()) asl in
    let lclr = lcth @ lrth in
    RULE_ASSUM_TAC(fun th ->
       if is_eq(concl th) && is_var(lhs(concl th)) &&
          type_of(lhs(concl th)) = `:(uarch_event)list`
       then REWRITE_RULE (lclr @ vwth) th
       else REWRITE_RULE lclr th) THEN
    REWRITE_TAC (lclr @ vwth));;

let CTR_RECON : tactic =
  GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
  GEN_REWRITE_TAC (TRY_CONV o ONCE_DEPTH_CONV)
    [ARITH_RULE `word 3:int64 = word(2 EXP 2 - 1)`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM(ASSUME `len_bits DIV 128 = nblocks`);
              GSYM(ASSUME `nblocks DIV 4 = loop_count`);
              GSYM(ASSUME `nblocks MOD 4 = loop_remain`)] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV;;

let ADDR_RECON : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; SUB_0;
              WORD_ADD_0; ADD_ASSOC] THEN
  (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_ARITH);;

let BRANCH_RECON : tactic =
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_SIMP_TAC[WSUB_BRANCH];;

let WSUB_ARITH : tactic =
  W(fun (asl,w) ->
    let l,_ = dest_eq w in
    let cnt_minus_i = (match l with Comb(Comb(_,Comb(_,a)),_) -> a | _ -> failwith "wsub") in
    let cnt,iv = dest_binary "-" cnt_minus_i in
    let lt = mk_binary "<" (iv,cnt) in
    SUBGOAL_THEN (mk_eq(cnt_minus_i, mk_binary "+" (mk_binary "-" (cnt, mk_binary "+" (iv,`1`)), `1`)))
      SUBST1_TAC THENL
     [(FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC th else NO_TAC)) THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let is_branch_goal w =
  can dest_eq w &&
  (let l,r = dest_eq w in
   let strip t = match t with Comb(c,a) when (try name_of c="word" with _->false) -> a | _ -> t in
   is_cond l || is_cond r || is_cond (strip l) || is_cond (strip r));;

let MEMACC_VIA_ASM : tactic =
  fun (asl,w) ->
    let defeqs = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && is_var(lhs t) && type_of(lhs t) = `:(uarch_event)list`
        then (lhs t, th) else fail()) asl in
    if defeqs = [] then DISCHARGE_MEMACCESS_INBOUNDS_TAC (asl,w) else
    let _,defth = hd defeqs in
    (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM defth] THEN
     REPEAT (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
             CONJ_TAC THENL [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC; ALL_TAC]) THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

let DISCHARGE_SAFE_ROBUST : tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] else ALL_TAC) THEN
  MEMACC_VIA_ASM;;

(* Surgical cond reducers (constant condition), no beta-mangle of f_ev_* redexes. *)
let REDUCE_IFEQ (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQT_INTRO(ASSUME(mk_eq(v,k)))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IFNE (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQF_INTRO(ASSUME(mk_neg(mk_eq(v,k))))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IF0 (lv:term)  = REDUCE_IFEQ lv `0`;;
let REDUCE_IFN0 (lv:term) = REDUCE_IFNE lv `0`;;

(* Variants for the whole-subroutine safety proofs, whose memory facts close by rewriting. *)

let MEM_PRESERVE : tactic = ASM_REWRITE_TAC[] THEN NO_TAC;;

(* Leaf closers for the safety proofs.  Every alternative must CLOSE its conjunct (THEN NO_TAC): a closer *)
(* that merely rewrites can then never leave a residual that leaks into the next leg.  The `extra` list  *)
(* lets a proof add its own reconcilers to the equation chain.                                          *)
let LEAF_WITH (disch:tactic) (extra:tactic list) : tactic =
  W(fun (asl,w) ->
    if is_exists w then
      ((disch THEN NO_TAC) ORELSE
       ((DEABBR THEN DISCHARGE_SAFE_ROBUST) THEN NO_TAC) ORELSE
       ((DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC) THEN NO_TAC))
    else if is_branch_goal w then (BRANCH_RECON THEN NO_TAC)
    else if can dest_eq w then
      FIRST (map (fun t -> t THEN NO_TAC) ([WSUB_ARITH; ADDR_RECON; CTR_RECON] @ extra))
    else (disch THEN NO_TAC));;
let CLOSE_WITH extra : tactic = REPEAT CONJ_TAC THEN LEAF_WITH (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC) extra;;
let CLOSE_R2_WITH extra : tactic = REPEAT CONJ_TAC THEN LEAF_WITH (DEABBR THEN DISCHARGE_SAFE_ROBUST) extra;;
let CLOSE : tactic = CLOSE_WITH [];;
let CLOSE_R2 : tactic = CLOSE_R2_WITH [];;
(* Variants for the whole-subroutine safety proofs, whose memory facts close by rewriting. *)
let CLOSE_SUB : tactic = CLOSE_WITH [MEM_PRESERVE];;
let CLOSE_R2_SUB : tactic = CLOSE_R2_WITH [MEM_PRESERVE];;


(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas shared by the four software-pipelined AES-GCM       *)
(* proofs (formerly duplicated in the proof files).                            *)
(* ------------------------------------------------------------------------- *)

let (MUST:tactic->tactic) = fun t (asl,w) ->
  let gs = t (asl,w) in let _,subs,_ = gs in
  if subs = [] then gs else failwith "MUST: goal not closed";;

(* Weaker guard used by the decrypt-128 closers: fail only if the tactic made no progress at all, so a
   closer may leave subgoals for the rest of the leg to finish. *)
let (MUST_PROGRESS:tactic->tactic) = fun t (asl,w) ->
  let (m,gls,f) = t (asl,w) in
  (match gls with [(_,w')] when w' = w -> failwith "MUST_PROGRESS: not closed" | _ -> (m,gls,f));;

let CTR_BLOCK_BUILD_V = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce c)
   ==> word_join
        (word_or (word_zx ((word_zx ivhi):int32):int64)
                 (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
        ivlo :int128
       = word_reversefields 8 (ctr_block nonce cval)`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

(* mk_cbv cval : the CTR_BLOCK_BUILD_V instance folding the reassembled reversed-lane counter
   (built from the ctr-2 lanes + word cval) to word_reversefields 8 (ctr_block nonce cval). *)
let mk_cbv cval =
  let inst = INST [`word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64`,`ivhi:int64`;
                   `word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`,`ivlo:int64`;
                   cval,`cval:num`] CTR_BLOCK_BUILD_V in
  MP inst (prove(lhand(concl inst), REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST));;

(* ADD_ASSOC + NUM_ADD_CONV fold the numeric offset.                                *)
let SPLIT_INPUT_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  ONCE_DEPTH_CONV(REWR_CONV(GSYM ADD_ASSOC)) THENC
  ONCE_DEPTH_CONV NUM_ADD_CONV;;

(* the two different conversions).                                                 *)
let SPLIT_INPUT_TAIL_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV;;

(* the intervening normalisation, so we need both orientations.                     *)
let SCALAR_RK_RECONSTRUCT = prove
 (`(word_xor
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
     (nineround:int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb)) /\
   (word_xor
     (nineround:int128)
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb))`,
  CONJ_TAC THEN CONV_TAC BITBLAST_RULE);;

(* ---- partial-AES abstractions ---- *)
let aes7c = new_definition
 `aes7c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk)))`;;

let JOIN_XOR_LANES = prove
 (`word_join (word_xor (word_subword (a:int128) (64,64):int64) (word_subword (b:int128) (64,64):int64))
             (word_xor (word_subword a (0,64):int64) (word_subword b (0,64):int64)) : int128
   = word_xor a b`,
  CONV_TAC WORD_BLAST);;

(* ---- block-(4i+1) keystream closer.  The AES-128 encrypt kernel carries the pipelined input^rk10 of block 4i+1 across
   the backedge in the two scalar lanes X23 (hi 64) / X28 (lo 64); `stp x28,x23,[sp,#176]`@0x210 stages
   them, Q13 reloads@0x21c.  With X23/X28 pinned to the two subword-lanes of word_xor(inblock(4i+1))(rk10),
   word_join recombines to the full 128 and the keystream folds to the settled nist_cipher_block form. *)
let JOIN_SUBWORD_RECOMBINE = prove
 (`word_join (word_subword (x:int128) (64,64):int64) (word_subword x (0,64):int64) : int128 = x`,
  CONV_TAC WORD_BLAST);;

let ZXNEST4 = prove
 (`word_zx (word_zx (word_zx (word_zx (x:int32):int64):int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;

let nist_input_block = new_definition
 `nist_input_block (inblock:num->int128) (i:num) : int128 =
        word_reversefields 8 (inblock i)`;;

let INBLOCK_REASSEMBLE = prove
 (`(word_join
     (word_join
      (word_join (word_subword (x:int128) (64,8):byte) (word_subword x (72,8):byte):int16)
      (word_join (word_subword x (80,8):byte) (word_subword x (88,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (96,8):byte) (word_subword x (104,8):byte):int16)
      (word_join (word_subword x (112,8):byte) (word_subword x (120,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (0,64)) /\
   (word_join
     (word_join
      (word_join (word_subword (x:int128) (0,8):byte) (word_subword x (8,8):byte):int16)
      (word_join (word_subword x (16,8):byte) (word_subword x (24,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (32,8):byte) (word_subword x (40,8):byte):int16)
      (word_join (word_subword x (48,8):byte) (word_subword x (56,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (64,64))`,
  CONV_TAC WORD_BLAST);;

let DEC_GHASH_NORM_TAC : tactic =
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
  REWRITE_TAC[GSYM nist_input_block] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV);;

let SWP_SUBWORD_JOIN_MID = WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`;;

let aes256_ctr_block = new_definition
 `aes256_ctr_block c nonce rk i =
    word_reversefields 8 (aes256_cipher (ctr_block nonce (i + c)) rk)`;;

let AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor
   (aese
    (aesmc
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc
           (aese
            (aesmc
            (aese
             (aesmc
             (aese
              (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
             rk3))
            rk4))
           rk5))
          rk6))
         rk7))
        rk8))
       rk9))
      rk10))
     rk11))
    rk12))
   rk13)
   rk14 =
   word_reversefields 8
    (aes256_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
              rk11; rk12; rk13; rk14]))`,
  REWRITE_TAC[aes256_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

let XOR_AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc
           (aese
            (aesmc
            (aese
             (aesmc
             (aese
              (aesmc
              (aese
               (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
              rk3))
             rk4))
            rk5))
           rk6))
          rk7))
         rk8))
        rk9))
       rk10))
      rk11))
     rk12))
    rk13)
   (word_xor rk14 inblock) =
   word_xor
    (word_reversefields 8
      (aes256_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
               rk11; rk12; rk13; rk14])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

let aes1c = new_definition
 `aes1c nonce (rk:int128 list) c : int128 =
    aesmc(aese (word_reversefields 8 (ctr_block nonce c)) (word_reversefields 8 (EL 0 rk)))`;;

let aes6c = new_definition
 `aes6c nonce (rk:int128 list) c : int128 = aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (word_reversefields 8 (ctr_block nonce c)) (word_reversefields 8 (EL 0 rk)))) (word_reversefields 8 (EL 1 rk)))) (word_reversefields 8 (EL 2 rk)))) (word_reversefields 8 (EL 3 rk)))) (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk)))`;;

let aes11c = new_definition
 `aes11c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk)))`;;

(* aes14p = pre-final-XOR 14-aese tower (14 aese, 13 aesmc, keys EL 0..13, NO EL14 XOR). *)
let aes14p = new_definition
 `aes14p (nonce:96 word) (rk:int128 list) (c:num) : int128 =
    aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk))))
      (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`;;

(* completion: aes14p ^ rk14 = the full 14-round AES-256 keystream (byte-reversed). *)
let AES14P_COMPLETE = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor (aes14p nonce rk c) (word_reversefields 8 (EL 14 rk))
       = word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)`,
  DISCH_TAC THEN REWRITE_TAC[aes14p] THEN
  GEN_REWRITE_TAC LAND_CONV
   [INST ((`word_reversefields 8 (ctr_block nonce c):int128`,`plaintext:int128`) ::
          map (fun j -> (parse_term(Printf.sprintf "word_reversefields 8 (EL %d rk):int128" j),
                         mk_var("rk"^string_of_int j,`:int128`))) (0--14))
         AES256_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; MAP] THEN ASM_REWRITE_TAC[]);;

(* aes14p reached via the carried partials aes7c / aes11c (rewrite bridges). *)
let AES14P_VIA_AES7C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese (aes7c nonce rk c)
     (word_reversefields 8 (EL 7 rk))))(word_reversefields 8 (EL 8 rk))))
     (word_reversefields 8 (EL 9 rk))))(word_reversefields 8 (EL 10 rk))))
     (word_reversefields 8 (EL 11 rk))))(word_reversefields 8 (EL 12 rk))))
     (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes7c]);;

let AES14P_VIA_AES11C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese (aes11c nonce rk c) (word_reversefields 8 (EL 11 rk))))
     (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes11c]);;

let AES14P_VIA_AES1C = prove
 (`aes14p nonce rk c = aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aes1c nonce rk c) (word_reversefields 8 (EL 1 rk)))) (word_reversefields 8 (EL 2 rk)))) (word_reversefields 8 (EL 3 rk)))) (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk)))) (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk)))) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)))) (word_reversefields 8 (EL 10 rk)))) (word_reversefields 8 (EL 11 rk)))) (word_reversefields 8 (EL 12 rk)))) (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes1c]);;

let AES14P_VIA_AES6C = prove
 (`aes14p nonce rk c = aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aes6c nonce rk c) (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk)))) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)))) (word_reversefields 8 (EL 10 rk)))) (word_reversefields 8 (EL 11 rk)))) (word_reversefields 8 (EL 12 rk)))) (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes6c]);;

(* keystream^input fold: word_xor(aes14p c)(word_xor inb rk14) = word_xor(rev8(cipher(ctr c)))(inb). *)
let KEYSTREAM_FOLD256 = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor (aes14p nonce rk c) (word_xor inb (word_reversefields 8 (EL 14 rk)))
       = word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES14P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;

(* rk-list hyp (15-elt for 256). *)
let rk15 = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
             EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`;;

(* Abstract every FULLY-APPLIED (2-arg) word_pmul subterm as a fresh int128/int256 var, so a subsequent
   BITBLAST proves only the surrounding word_join/word_subword/word_xor SHUFFLE (fast, tiny BDD) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  CRITICAL: match only 2-arg pmuls -- the
   bare `word_pmul` const and partial applications must NOT be abstracted (that only renames the head). *)
let ABBREV_PMULS : tactic =
  fun (asl,w) ->
    let is_full_pmul t = match strip_comb t with Const("word_pmul",_),[_;_] -> true | _ -> false in
    let pmuls = setify (find_terms is_full_pmul w) in
    let mk i t = ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "pm_%d" i, type_of t), t)) in
    (EVERY (List.mapi mk pmuls)) (asl,w);;

(* Karatsuba-mid folding lemmas: canonicalize BOTH word_xor orders of a subword-half pair to karatsuba_mid,
   so the machine's alternating-order mid sub-pmuls and KARATSUBA_JOIN_ALT's mid coincide as atoms. *)
let CMID_HILO = prove
 (`!a:int128. word_xor (word_subword a (64,64)) (word_subword a (0,64)):int64 = karatsuba_mid a`,
  REWRITE_TAC[karatsuba_mid] THEN CONV_TAC WORD_BITWISE_RULE);;

let CMID_LOHI = prove
 (`!a:int128. word_xor (word_subword a (0,64)) (word_subword a (64,64)):int64 = karatsuba_mid a`,
  REWRITE_TAC[karatsuba_mid] THEN CONV_TAC WORD_BITWISE_RULE);;

(* word_join linearity over word_xor (both int256- and int128-level): folds the RHS product tower's xor-of-per-
   lane-joins into a single join-of-xors so it matches reduce_g2's single-join packing.  THE multi-lane key. *)
let JOIN_XOR_256 = prove
 (`!(a1:int128) (b1:int128) (a2:int128) (b2:int128).
     word_xor (word_join a1 b1 :int256) (word_join a2 b2 :int256) =
     word_join (word_xor a1 a2) (word_xor b1 b2) :int256`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let JOIN_XOR_128 = prove
 (`!(a1:int64) (b1:int64) (a2:int64) (b2:int64).
     word_xor (word_join a1 b1 :int128) (word_join a2 b2 :int128) =
     word_join (word_xor a1 a2) (word_xor b1 b2) :int128`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* KEY15_SPLIT: turn the compound wordlist_from_memory(key_p,15) precondition into
   15 atomic per-slot reads so ARM_ADD_RETURN_STACK_TAC's interior big-step can
   propagate them through the prologue (a single list-equation is left orphaned). *)
let KEY15_SPLIT = prove
 (`(wordlist_from_memory (key_p:int64,15) (s:armstate) =
    MAP (word_reversefields 8) (rk:int128 list)) <=>
   LENGTH rk = 15 /\
   read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
   read (memory :> bytes128 (word_add key_p (word 16))) s =
     word_reversefields 8 (EL 1 rk) /\
   read (memory :> bytes128 (word_add key_p (word 32))) s =
     word_reversefields 8 (EL 2 rk) /\
   read (memory :> bytes128 (word_add key_p (word 48))) s =
     word_reversefields 8 (EL 3 rk) /\
   read (memory :> bytes128 (word_add key_p (word 64))) s =
     word_reversefields 8 (EL 4 rk) /\
   read (memory :> bytes128 (word_add key_p (word 80))) s =
     word_reversefields 8 (EL 5 rk) /\
   read (memory :> bytes128 (word_add key_p (word 96))) s =
     word_reversefields 8 (EL 6 rk) /\
   read (memory :> bytes128 (word_add key_p (word 112))) s =
     word_reversefields 8 (EL 7 rk) /\
   read (memory :> bytes128 (word_add key_p (word 128))) s =
     word_reversefields 8 (EL 8 rk) /\
   read (memory :> bytes128 (word_add key_p (word 144))) s =
     word_reversefields 8 (EL 9 rk) /\
   read (memory :> bytes128 (word_add key_p (word 160))) s =
     word_reversefields 8 (EL 10 rk) /\
   read (memory :> bytes128 (word_add key_p (word 176))) s =
     word_reversefields 8 (EL 11 rk) /\
   read (memory :> bytes128 (word_add key_p (word 192))) s =
     word_reversefields 8 (EL 12 rk) /\
   read (memory :> bytes128 (word_add key_p (word 208))) s =
     word_reversefields 8 (EL 13 rk) /\
   read (memory :> bytes128 (word_add key_p (word 224))) s =
     word_reversefields 8 (EL 14 rk)`,
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [FIRST_ASSUM(fun lenth ->
      MP_TAC(GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ] lenth)) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    REWRITE_TAC[LENGTH; LENGTH_MAP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shared scaffolding for the SWP constant-time and memory-safety proofs.    *)
(* ------------------------------------------------------------------------- *)

(* Event-tracking simulator over a given EXEC rule. *)
let SAFE_SIM_TAC exec =
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false exec;;

(* Frugal branch-nonzero fact (no ASM_ over the post-sim context): cv is the counter *)
(* variable (loop_count in the main pipeline).  Needs `val(word cv)=cv` + a `_ <= cv` *)
(* bound among the assumptions.                                                      *)
(* here (main pipeline).  Needs `val(word cv)=cv` + a `_ <= cv` bound from the asms.  *)
let BEQ_NZ_V (cv:term) (k:term) : tactic =
  fun (asl,w) ->
    let vfact = try snd(find (fun (_,th) ->
        concl th = mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,cv)),cv)) asl)
      with Failure _ -> failwith "BEQ_NZ_V: no `val(word cv) = cv` assumption" in
    let bnd = mapfilter (fun (_,th) -> match concl th with
                  Comb(Comb(Const("<=",_),_),c) when c = cv -> th | _ -> fail()) asl in
    (SUBGOAL_THEN (mk_neg(mk_eq(mk_comb(`val:int64->num`,
        list_mk_comb(`word_sub:int64->int64->int64`,
          [mk_comb(`word:num->int64`,cv); mk_comb(`word:num->int64`,k)])),`0`)))
      ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; vfact] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY MP_TAC bnd THEN ARITH_TAC;
      ALL_TAC]) (asl,w);;
let BEQ_NZ (k:term) : tactic = BEQ_NZ_V `loop_count:num` k;;

(* Common opening of a SWP safety goal: introduce the arguments, abbreviate the block  *)
(* counts and establish their word bounds.                                            *)
let OPEN_SWP_SAFE exec : tactic =
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst exec] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64 /\ loop_remain < 4` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN
      SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC];;

(* Drain pointer reconciliation: a loop-exit invariant carries 64*(loop_count-k)+64*k  *)
(* while the sequence post states 64*loop_count.  Linearise loop_count = (loop_count-k)+k *)
(* (valid given k <= loop_count among the assumptions) so WORD_RULE sees only linear     *)
(* combinations.                                                                        *)
let DRAIN_ADDR_K (k:term) : tactic =
  SUBGOAL_THEN (mk_eq(`loop_count:num`, mk_binary "+" (mk_binary "-" (`loop_count:num`,k),k)))
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC] THEN
  CONV_TAC WORD_RULE;;
