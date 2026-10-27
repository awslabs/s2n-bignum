(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The SHA-3 hash functions and XOFs of FIPS 202, for byte-string inputs.    *)
(*                                                                           *)
(* The Keccak-p[1600,24] permutation is defined by its step mappings on the  *)
(* 5 x 5 array of 64-bit lanes (FIPS 202 Section 3.2). The sponge is         *)
(* described at the level of bytes, which suffices for all uses in FIPS 203  *)
(* and is justified by FIPS 202 Appendix B.2: with the bit-numbering         *)
(* convention of FIPS 202 (bit i of a string is bit i MOD 8 of byte i DIV 8, *)
(* and lane (x,y) is bits 64 * (x + 5 * y) .. 64 * (x + 5 * y) + 63 of the   *)
(* state), the state is simply a 1600-bit word, byte strings are read as     *)
(* little-endian numbers, and the domain-separation suffix plus pad10*1      *)
(* padding become the bytes 0x06 ... 0x80 (SHA-3) or 0x1F ... 0x80 (SHAKE).  *)
(* ========================================================================= *)

needs "Library/words.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Little-endian correspondence between byte lists and numbers. These are    *)
(* the same definitions as in common/words2.ml, so both files can be loaded  *)
(* together, but this file only needs the HOL Light library.                 *)
(* ------------------------------------------------------------------------- *)

let num_of_bytelist = define
 `(num_of_bytelist [] = 0) /\
  (!h t. num_of_bytelist (CONS h t) = val(h:byte) + 256 * num_of_bytelist t)`;;

let bytelist_of_num = define
 `(bytelist_of_num 0 n = []) /\
  (bytelist_of_num (SUC k) n =
     CONS (word(n MOD 256):byte) (bytelist_of_num k (n DIV 256)))`;;

(* ------------------------------------------------------------------------- *)
(* The step mappings of Keccak-p[1600] on lanes a x y, 0 <= x,y < 5.         *)
(* ------------------------------------------------------------------------- *)

let keccak_theta = new_definition
 `keccak_theta (a:num->num->int64) =
    let c = \x. word_xor (a x 0)
                 (word_xor (a x 1)
                   (word_xor (a x 2) (word_xor (a x 3) (a x 4)))) in
    \x y. word_xor (a x y)
            (word_xor (c((x + 4) MOD 5)) (word_rol (c((x + 1) MOD 5)) 1))`;;

(* The rotation offsets of FIPS 202 Table 2 (reduced mod 64), in the order   *)
(* x + 5 * y; KECCAK_RHO_OFFSET_ALGORITHM below relates them to Alg. 2.      *)

let keccak_rho_offset = new_definition
 `keccak_rho_offset x y =
    EL (x + 5 * y) [ 0;  1; 62; 28; 27;
                    36; 44;  6; 55; 20;
                     3; 10; 43; 25; 39;
                    41; 45; 15; 21;  8;
                    18;  2; 61; 56; 14]`;;

let keccak_rho = new_definition
 `keccak_rho (a:num->num->int64) =
    \x y. word_rol (a x y) (keccak_rho_offset x y)`;;

let keccak_pi = new_definition
 `keccak_pi (a:num->num->int64) = \x y. a ((x + 3 * y) MOD 5) x`;;

let keccak_chi = new_definition
 `keccak_chi (a:num->num->int64) =
    \x y. word_xor (a x y)
            (word_and (word_not(a ((x + 1) MOD 5) y)) (a ((x + 2) MOD 5) y))`;;

(* The round constants via the LFSR of FIPS 202 Algorithm 5: keccak_lfsr t   *)
(* represents x^t mod (x^8 + x^6 + x^5 + x^4 + 1) over GF(2) as a byte, and  *)
(* rc(t) is its constant term. Algorithm 6 puts rc(j + 7 * i) at bit         *)
(* 2^j - 1 of the round constant for round i.                                *)

let keccak_lfsr = define
 `keccak_lfsr 0 = (word 1:byte) /\
  keccak_lfsr (SUC t) =
    word_xor (word_shl (keccak_lfsr t) 1)
             (if bit 7 (keccak_lfsr t) then word 0x71 else word 0)`;;

let keccak_rc = new_definition
 `keccak_rc t = bit 0 (keccak_lfsr t)`;;

let keccak_round_constant = new_definition
 `keccak_round_constant i:int64 =
    word(nsum (0..6)
           (\j. bitval(keccak_rc(j + 7 * i)) * 2 EXP (2 EXP j - 1)))`;;

let keccak_iota = new_definition
 `keccak_iota i (a:num->num->int64) =
    \x y. if x = 0 /\ y = 0 then word_xor (a 0 0) (keccak_round_constant i)
          else a x y`;;

let keccak_rnd = new_definition
 `keccak_rnd i a =
    keccak_iota i (keccak_chi (keccak_pi (keccak_rho (keccak_theta a))))`;;

(* ------------------------------------------------------------------------- *)
(* Keccak-f[1600] = Keccak-p[1600,24] on the state as a 1600-bit word.       *)
(* ------------------------------------------------------------------------- *)

let keccak_lanes = new_definition
 `keccak_lanes (s:1600 word) =
    \x y. word_subword s (64 * (x + 5 * y),64):int64`;;

let keccak_state = new_definition
 `keccak_state (a:num->num->int64) =
    word(nsum (0..24) (\i. val(a (i MOD 5) (i DIV 5)) * 2 EXP (64 * i))):
    1600 word`;;

let keccak_rounds = define
 `keccak_rounds 0 a = a /\
  keccak_rounds (SUC n) a = keccak_rnd n (keccak_rounds n a)`;;

let keccak_f1600 = new_definition
 `keccak_f1600 s = keccak_state (keccak_rounds 24 (keccak_lanes s))`;;

(* ------------------------------------------------------------------------- *)
(* The sponge construction over bytes, with rate r bytes, r = 200 - c / 8.   *)
(* The padding (domain-separation bits followed by pad10*1) of a message of  *)
(* length len, as bytes, when the first padding byte is d. The output is an  *)
(* infinite byte stream; finite outputs are its initial segments.            *)
(* ------------------------------------------------------------------------- *)

let keccak_pad = new_definition
 `keccak_pad r d len =
    if len MOD r = r - 1 then [word(d + 128):byte]
    else CONS (word d) (APPEND (REPLICATE (r - len MOD r - 2) (word 0))
                               [word 128])`;;

let keccak_absorb = define
 `keccak_absorb r p 0 = (word 0:1600 word) /\
  keccak_absorb r p (SUC j) =
    keccak_f1600
     (word_xor (keccak_absorb r p j)
               (word((p DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r))))`;;

let keccak_squeeze = define
 `keccak_squeeze 0 s = s /\
  keccak_squeeze (SUC t) s = keccak_f1600 (keccak_squeeze t s)`;;

let keccak_sponge = new_definition
 `keccak_sponge c d (m:byte list) =
    let r = (1600 - c) DIV 8 in
    let p = APPEND m (keccak_pad r d (LENGTH m)) in
    let s = keccak_absorb r (num_of_bytelist p) (LENGTH p DIV r) in
    \i. word_subword (keccak_squeeze (i DIV r) s) (8 * (i MOD r),8):byte`;;

(* ------------------------------------------------------------------------- *)
(* The four SHA-3 functions. SHAKE128 and SHAKE256 are infinite streams;     *)
(* SHAKE128(M,8 * n) in FIPS 202 notation is list_of_seq (shake128 M) n.     *)
(* ------------------------------------------------------------------------- *)

let sha3_256 = new_definition
 `sha3_256 m = list_of_seq (keccak_sponge 512 0x06 m) 32`;;

let sha3_512 = new_definition
 `sha3_512 m = list_of_seq (keccak_sponge 1024 0x06 m) 64`;;

let shake128 = new_definition
 `shake128 m = keccak_sponge 256 0x1F m`;;

let shake256 = new_definition
 `shake256 m = keccak_sponge 512 0x1F m`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties: lanes and states correspond, and each step mapping (so  *)
(* the permutation) only depends on the lanes with 0 <= x,y < 5.             *)
(* ------------------------------------------------------------------------- *)

let NSUM_DIGITS_25 = prove
 (`!b:num->num.
        (!i. b i < 2 EXP 64)
        ==> nsum (0..24) (\i. b i * 2 EXP (64 * i)) < 2 EXP 1600 /\
            !j. j < 25
                ==> (nsum (0..24) (\i. b i * 2 EXP (64 * i)) DIV
                     2 EXP (64 * j)) MOD 2 EXP 64 = b j`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (64 * i) = (2 EXP 64) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  SUBGOAL_THEN `0..24 = {i | i < 25}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`2 EXP 64`; `b:num->num`; `25`] DIGITSUM_BOUND) THEN
    ASM_REWRITE_TAC[EXP_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_DIV_MOD o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]);;

let KECCAK_LANES_STATE = prove
 (`!a x y. x < 5 /\ y < 5 ==> keccak_lanes (keccak_state a) x y = a x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\i. val((a:num->num->int64) (i MOD 5) (i DIV 5))`
               NSUM_DIGITS_25) THEN
  REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
               (INST_TYPE [`:64`,`:N`] VAL_BOUND)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x + 5 * y`)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x + 5 * y) MOD 5 = x /\ (x + 5 * y) DIV 5 = y`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[keccak_lanes; keccak_state; word_subword; VAL_WORD;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_VAL]);;

let KECCAK_STATE_LANES = prove
 (`!s. keccak_state (keccak_lanes s) = s`,
  GEN_TAC THEN REWRITE_TAC[keccak_state; keccak_lanes] THEN
  SUBGOAL_THEN `!i. i MOD 5 + 5 * i DIV 5 = i` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MP_TAC(SPECL [`i:num`; `5`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_64; ARITH_RULE `MIN 64 64 = 64`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (64 * i) = (2 EXP 64) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  SUBGOAL_THEN `0..24 = {i | i < 25}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIGITSUM_WORKS THEN
  MP_TAC(ISPEC `s:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; EXP_EXP] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_STATE_EQ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> keccak_state a = keccak_state b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_state] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i MOD 5`; `i DIV 5`]) THEN
  SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH_EQ] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let KECCAK_STEP_LOCAL_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[keccak_theta; keccak_rho; keccak_pi; keccak_chi;
              keccak_iota] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_EQ; ARITH_RULE
   `0 < 5 /\ 1 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5`];;

let KECCAK_THETA_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_theta a x y = keccak_theta b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_RHO_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_rho a x y = keccak_rho b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_PI_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_pi a x y = keccak_pi b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_CHI_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_chi a x y = keccak_chi b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_IOTA_LOCAL = prove
 (`!i a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
           ==> !x y. x < 5 /\ y < 5
                     ==> keccak_iota i a x y = keccak_iota i b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_RND_LOCAL = prove
 (`!i a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
           ==> !x y. x < 5 /\ y < 5
                     ==> keccak_rnd i a x y = keccak_rnd i b x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[keccak_rnd] THEN
  MATCH_MP_TAC KECCAK_IOTA_LOCAL THEN MATCH_MP_TAC KECCAK_CHI_LOCAL THEN
  MATCH_MP_TAC KECCAK_PI_LOCAL THEN MATCH_MP_TAC KECCAK_RHO_LOCAL THEN
  MATCH_MP_TAC KECCAK_THETA_LOCAL THEN ASM_REWRITE_TAC[]);;

let KECCAK_F1600_ROUND_WORDS = prove
 (`!s n. keccak_state (keccak_rounds (SUC n) (keccak_lanes s)) =
         keccak_state (keccak_rnd n
           (keccak_lanes (keccak_state (keccak_rounds n (keccak_lanes s)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_rounds] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN MATCH_MP_TAC KECCAK_RND_LOCAL THEN
  SIMP_TAC[KECCAK_LANES_STATE]);;

(* ------------------------------------------------------------------------- *)
(* The rho offsets come from FIPS 202 Algorithm 2: starting at (x,y) = (1,0) *)
(* and stepping (x,y) -> (y,2x+3y mod 5), the t-th lane visited (t < 24) is  *)
(* rotated by (t+1)(t+2)/2; lane (0,0) is not rotated.                       *)
(* ------------------------------------------------------------------------- *)

let keccak_rho_pos = define
 `keccak_rho_pos 0 = (1,0) /\
  keccak_rho_pos (SUC t) =
    (SND(keccak_rho_pos t),
     (2 * FST(keccak_rho_pos t) + 3 * SND(keccak_rho_pos t)) MOD 5)`;;

let KECCAK_RHO_OFFSET_ALGORITHM = prove
 (`keccak_rho_offset 0 0 = 0 /\
   !t. t < 24
       ==> keccak_rho_offset (FST(keccak_rho_pos t)) (SND(keccak_rho_pos t)) =
           (((t + 1) * (t + 2)) DIV 2) MOD 64`,
  let posconv =
    let th0,th1 = CONJ_PAIR keccak_rho_pos in
    let cache = ref [0,th0] in
    let rec get n =
      try assoc n (!cache) with Failure _ ->
      let thp = get (n - 1) in
      let tm = mk_comb(`keccak_rho_pos`,mk_small_numeral n) in
      let th = (RAND_CONV num_CONV THENC REWR_CONV th1 THENC
                PURE_REWRITE_CONV[thp] THENC REWRITE_CONV[] THENC
                NUM_REDUCE_CONV) tm in
      cache := (n,th)::(!cache); th in
    fun tm -> match tm with
        Comb(Const("keccak_rho_pos",_),n) when is_numeral n ->
          get (Num.int_of_num(dest_numeral n))
      | _ -> failwith "posconv" in
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_rho_offset] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV posconv) THEN
    REWRITE_TAC[keccak_rho_offset] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
