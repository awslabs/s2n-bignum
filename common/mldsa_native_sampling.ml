(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the samplers of mldsa-native's portable C   *)
(* implementation (poly.c and poly_kl.c), in the style of                    *)
(* common/mldsa_native_poly.ml: the rejection sampling of coefficients mod q *)
(* (mld_rej_uniform_c, mld_poly_uniform_4x, mld_poly_uniform) and in         *)
(* [-eta,eta] (mld_rej_eta_c, mld_poly_uniform_eta_4x), and the sampling of  *)
(* the polynomials of y (mld_poly_uniform_gamma1_4x,                         *)
(* mld_poly_uniform_gamma1).                                                 *)
(*                                                                           *)
(* A buffer is a function b:num->byte, byte j being b j; the output of SHAKE *)
(* is such a function for the infinite stream of its bytes. The rejection    *)
(* samplers turn the buffer into a sequence of candidates (groups of 3 bytes *)
(* for mld_rej_uniform_c, nibbles for mld_rej_eta_c), keep those accepted,   *)
(* in order, and store them after the coefficients already sampled until     *)
(* there are 256; here the accepted values from the first n candidates are a *)
(* list, of which the C functions store an initial segment. The callers      *)
(* sample a whole polynomial from the SHAKE output: a few blocks at first,   *)
(* then one block at a time until each polynomial has 256 coefficients,      *)
(* which only happens if the stream has 256 acceptable candidates; the       *)
(* theorems about them assume that it does (the _terminates predicates).     *)
(*                                                                           *)
(* The C code of mld_rej_eta_c declassifies (MLD_CT_TESTING_DECLASSIFY)      *)
(* whether each nibble that it examines is accepted: mld_rej_eta_declass and *)
(* mld_poly_uniform_eta_declass give exactly those, in order, as the lists   *)
(* of booleans of which the events of the code may be functions.             *)
(* ========================================================================= *)

needs "common/mldsa_native_fips202.ml";;
needs "common/mldsa_native_packing.ml";;

(* ------------------------------------------------------------------------- *)
(* The 4-way SHAKE functions (the mld_xof128_x4_ and mld_xof256_x4_ ones)    *)
(* absorb each message M of inlen bytes in one go                            *)
(* (mld_keccak_absorb_once_x4): they absorb the full blocks of rate r and    *)
(* XOR the last, padded with the domain separation byte p, into the state,   *)
(* which mldsa_shake128x4_absorb_once and mldsa_shake256x4_absorb_once leave *)
(* as below, and squeeze whole blocks, permuting the state before each. Byte *)
(* j of the output is therefore byte j of the stream that                    *)
(* mld_keccak_squeeze_byte gives from that state with the current block used *)
(* up (position r), as for mld_shake256_byte.                                *)
(* ------------------------------------------------------------------------- *)

let mld_keccak_absorb_once = new_definition
 `mld_keccak_absorb_once r p inlen M =
    let P = M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad r p inlen) in
    word_xor (keccak_absorb r P (inlen DIV r))
             (word(P DIV 2 EXP (8 * r * inlen DIV r) MOD 2 EXP (8 * r)))
    :1600 word`;;

let mld_shake128_stream = new_definition
 `mld_shake128_stream inlen M =
    mld_keccak_squeeze_byte 168 (mld_keccak_absorb_once 168 0x1F inlen M) 168`;;

let mld_shake256_stream = new_definition
 `mld_shake256_stream inlen M =
    mld_keccak_squeeze_byte 136 (mld_keccak_absorb_once 136 0x1F inlen M) 136`;;

(* ------------------------------------------------------------------------- *)
(* mld_rej_uniform_c (poly.c): candidate k is the 23-bit number formed by    *)
(* bytes 3 * k, 3 * k + 1 and 3 * k + 2, as the C code computes it, accepted *)
(* if it is less than q. From offset coefficients, with target 256 in all    *)
(* calls, the function stores the accepted values of the buflen DIV 3 groups *)
(* that fit below target, at offset, offset + 1, ..., and returns their      *)
(* number plus offset; it reads mld_rej_uniform_groups groups.               *)
(* ------------------------------------------------------------------------- *)

let mld_rej_uniform_cand = new_definition
 `mld_rej_uniform_cand (b:num->byte) k =
    word_and
     (word_or (word_or (word_zx(b(3 * k)))
                       (word_shl (word_zx(b(3 * k + 1))) 8))
              (word_shl (word_zx(b(3 * k + 2))) 16))
     (word 8388607):int32`;;

let mld_rej_uniform_list = new_definition
 `mld_rej_uniform_list (b:num->byte) n =
    FILTER (\t:int32. val t < 8380417)
           (list_of_seq (mld_rej_uniform_cand b) n)`;;

let mld_rej_uniform_ctr = new_definition
 `mld_rej_uniform_ctr target offset (b:num->byte) buflen =
    offset +
    MIN (target - offset) (LENGTH(mld_rej_uniform_list b (buflen DIV 3)))`;;

let mld_rej_uniform_groups = new_definition
 `mld_rej_uniform_groups target offset (b:num->byte) buflen =
    minimal g. g = buflen DIV 3 \/
               target <= offset + LENGTH(mld_rej_uniform_list b g)`;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_uniform and mld_poly_uniform_4x (poly.c) sample a polynomial     *)
(* from the SHAKE128 output s of a seed of 34 bytes: they first squeeze      *)
(* MLD_POLY_UNIFORM_NBLOCKS = 5 blocks of 168 bytes, i.e. 280 groups, and    *)
(* then one block, 56 groups, at a time while a polynomial has fewer than    *)
(* 256 coefficients, which it gets in the end if s has 256 acceptable groups *)
(* (mld_rej_uniform_terminates). The polynomial is then the first 256        *)
(* accepted values, whatever the number of blocks beyond that (as in         *)
(* mld_poly_uniform_4x, which squeezes until all four are complete).         *)
(* ------------------------------------------------------------------------- *)

let mld_rej_uniform_terminates = new_definition
 `mld_rej_uniform_terminates (s:num->byte) <=>
    ?n. 256 <= LENGTH(mld_rej_uniform_list s n)`;;

let mld_poly_uniform_nblocks = new_definition
 `mld_poly_uniform_nblocks (s:num->byte) =
    minimal k. 256 <= LENGTH(mld_rej_uniform_list s (280 + 56 * k))`;;

let mld_rej_uniform_poly = new_definition
 `mld_rej_uniform_poly (s:num->byte) i =
    EL i (mld_rej_uniform_list s (280 + 56 * mld_poly_uniform_nblocks s))`;;

let mld_poly_uniform = new_definition
 `mld_poly_uniform seed = mld_rej_uniform_poly (mld_shake128_stream 34 seed)`;;

(* ------------------------------------------------------------------------- *)
(* mld_rej_eta_c (poly_kl.c): candidate k is nibble k of the buffer, the low *)
(* half of byte k DIV 2 for k even (t0 in the C code) and the high half for  *)
(* k odd (t1). For eta = 2 a nibble t < 15 is accepted, giving 2 - t mod 5,  *)
(* with t mod 5 computed as t - ((205 * t) >> 10) * 5; for eta = 4 one with  *)
(* t < 9, giving 4 - t. The function reads the buffer byte by byte, while    *)
(* there are fewer than target coefficients: it reads mld_rej_eta_bytes      *)
(* bytes, and declassifies whether each of their two nibbles is accepted.    *)
(* ------------------------------------------------------------------------- *)

let mld_rej_eta_nibble = new_definition
 `mld_rej_eta_nibble (b:num->byte) k =
    if EVEN k then word_and (word_zx(b(k DIV 2))) (word 15)
    else word_ushr (word_zx(b(k DIV 2))) 4:int32`;;

let mld_rej_eta_valid = new_definition
 `mld_rej_eta_valid eta (t:int32) <=> val t < (if eta = 2 then 15 else 9)`;;

let mld_rej_eta_coeff = new_definition
 `mld_rej_eta_coeff eta (t:int32) =
    if eta = 2
    then word_sub (word 2)
          (word_sub t (word_mul (word_ushr (word_mul (word 205) t) 10)
                                (word 5)))
    else word_sub (word 4) t:int32`;;

let mld_rej_eta_list = new_definition
 `mld_rej_eta_list eta (b:num->byte) n =
    MAP (mld_rej_eta_coeff eta)
        (FILTER (mld_rej_eta_valid eta)
                (list_of_seq (mld_rej_eta_nibble b) n))`;;

let mld_rej_eta_ctr = new_definition
 `mld_rej_eta_ctr eta target offset (b:num->byte) buflen =
    offset +
    MIN (target - offset) (LENGTH(mld_rej_eta_list eta b (2 * buflen)))`;;

let mld_rej_eta_bytes = new_definition
 `mld_rej_eta_bytes eta target offset (b:num->byte) buflen =
    minimal m. m = buflen \/
               target <= offset + LENGTH(mld_rej_eta_list eta b (2 * m))`;;

let mld_rej_eta_declass = new_definition
 `mld_rej_eta_declass eta target offset (b:num->byte) buflen =
    list_of_seq (\k. mld_rej_eta_valid eta (mld_rej_eta_nibble b k))
                (2 * mld_rej_eta_bytes eta target offset b buflen)`;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_uniform_eta_4x (poly_kl.c) samples a polynomial from the         *)
(* SHAKE256 output s of the seed extended with the nonce and a zero byte: it *)
(* squeezes MLD_POLY_UNIFORM_ETA_NBLOCKS blocks of 136 bytes first (1 for    *)
(* eta = 2, 2 for eta = 4), then one at a time, as for mld_poly_uniform. The *)
(* calls of mld_rej_eta_c for the polynomial read the first bytes of s until *)
(* it has 256 coefficients, and declassify whether their nibbles are         *)
(* accepted: mld_poly_uniform_eta_declass.                                   *)
(* ------------------------------------------------------------------------- *)

let mld_rej_eta_terminates = new_definition
 `mld_rej_eta_terminates eta (s:num->byte) <=>
    ?n. 256 <= LENGTH(mld_rej_eta_list eta s n)`;;

let mld_poly_uniform_eta_nblocks = new_definition
 `mld_poly_uniform_eta_nblocks eta (s:num->byte) =
    minimal k. 256 <= LENGTH(mld_rej_eta_list eta s
                              (2 * 136 * ((if eta = 2 then 1 else 2) + k)))`;;

let mld_rej_eta_poly = new_definition
 `mld_rej_eta_poly eta (s:num->byte) i =
    EL i (mld_rej_eta_list eta s
           (2 * 136 * ((if eta = 2 then 1 else 2) +
                       mld_poly_uniform_eta_nblocks eta s)))`;;

let mld_poly_uniform_eta_declass = new_definition
 `mld_poly_uniform_eta_declass eta (s:num->byte) =
    list_of_seq (\k. mld_rej_eta_valid eta (mld_rej_eta_nibble s k))
     (2 * (minimal m. 256 <= LENGTH(mld_rej_eta_list eta s (2 * m))))`;;

let mld_poly_uniform_eta = new_definition
 `mld_poly_uniform_eta eta seed (nonce:byte) =
    mld_rej_eta_poly eta
     (mld_shake256_stream 66 (seed + 2 EXP 512 * val nonce))`;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_uniform_gamma1_4x and mld_poly_uniform_gamma1 (poly_kl.c) unpack *)
(* the polynomial from the SHAKE256 output of the seed extended with the     *)
(* 16-bit nonce, of which they squeeze MLD_POLY_UNIFORM_GAMMA1_NBLOCKS = 5   *)
(* blocks (680 bytes); mld_polyz_unpack reads the first 576 bytes of them    *)
(* for gamma1 = 2^17 and the first 640 for gamma1 = 2^19.                    *)
(* ------------------------------------------------------------------------- *)

let mld_poly_uniform_gamma1_17 = new_definition
 `mld_poly_uniform_gamma1_17 seed (nonce:int16) =
    mld_polyz_unpack_17
     (mld_shake256_stream 66 (seed + 2 EXP 512 * val nonce))`;;

let mld_poly_uniform_gamma1_19 = new_definition
 `mld_poly_uniform_gamma1_19 seed (nonce:int16) =
    mld_polyz_unpack_19
     (mld_shake256_stream 66 (seed + 2 EXP 512 * val nonce))`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the lists of accepted values: a list of the first m + n      *)
(* candidates is that of the first m followed by that of the next n, and the *)
(* values already accepted stay where they are as more candidates are read.  *)
(* ------------------------------------------------------------------------- *)

let MLD_LIST_OF_SEQ_ADD = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\k. f(m + k)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let MLD_REJ_ETA_NIBBLE_SHIFT = prove
 (`!(b:num->byte) c k.
        mld_rej_eta_nibble b (2 * c + k) = mld_rej_eta_nibble (\j. b(c + j)) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_nibble; EVEN_ADD; EVEN_MULT;
    ARITH_EVEN] THEN
  SUBGOAL_THEN `(2 * c + k) DIV 2 = c + k DIV 2` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[]]);;

let MLD_REJ_ETA_LIST_ADD = prove
 (`!eta (b:num->byte) c n.
        mld_rej_eta_list eta b (2 * c + n) =
        APPEND (mld_rej_eta_list eta b (2 * c))
               (mld_rej_eta_list eta (\j. b(c + j)) n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_rej_eta_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              MAP_APPEND; MLD_REJ_ETA_NIBBLE_SHIFT; ETA_AX]);;

let MLD_REJ_ETA_LIST_SUC = prove
 (`!eta (b:num->byte) n.
     mld_rej_eta_list eta b (n + 1) =
     APPEND (mld_rej_eta_list eta b n)
      (if mld_rej_eta_valid eta (mld_rej_eta_nibble b n)
       then [mld_rej_eta_coeff eta (mld_rej_eta_nibble b n)] else [])`,
  REWRITE_TAC[mld_rej_eta_list; GSYM ADD1; list_of_seq; FILTER_APPEND;
              MAP_APPEND; FILTER] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MAP]);;

let LENGTH_MLD_REJ_ETA_LIST = prove
 (`!eta (b:num->byte) n.
     LENGTH(mld_rej_eta_list eta b n) =
     LENGTH(FILTER (\x. x)
       (list_of_seq (\k. mld_rej_eta_valid eta (mld_rej_eta_nibble b k)) n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mld_rej_eta_list; list_of_seq; FILTER; MAP; LENGTH] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_rej_eta_list; LENGTH_MAP]) THEN
  ASM_REWRITE_TAC[FILTER_APPEND; MAP_APPEND; LENGTH_APPEND; LENGTH_MAP;
                  FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let EL_MLD_REJ_ETA_LIST_PREFIX = prove
 (`!eta (b:num->byte) m n j.
     m <= n /\ j < LENGTH(mld_rej_eta_list eta b m)
     ==> EL j (mld_rej_eta_list eta b n) = EL j (mld_rej_eta_list eta b m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[mld_rej_eta_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              MAP_APPEND; EL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_rej_eta_list]) THEN ASM_REWRITE_TAC[]);;

let LENGTH_MLD_REJ_ETA_LIST_MONO = prove
 (`!eta (b:num->byte) m n.
     m <= n ==> LENGTH(mld_rej_eta_list eta b m) <=
                LENGTH(mld_rej_eta_list eta b n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[mld_rej_eta_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              MAP_APPEND; LENGTH_APPEND; LE_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The number of bytes that mld_rej_eta_c reads (the minimal m), and the     *)
(* values that it declassifies.                                              *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_ETA_BYTES = prove
 (`!eta target offset (b:num->byte) buflen M.
     mld_rej_eta_bytes eta target offset b buflen = M
     ==> M <= buflen /\
         (M = buflen \/
          target <= offset + LENGTH(mld_rej_eta_list eta b (2 * M))) /\
         (!m. m < M
              ==> m < buflen /\
                  offset + LENGTH(mld_rej_eta_list eta b (2 * m)) < target)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_bytes] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC
   `\m. m = buflen \/
        target <= offset + LENGTH(mld_rej_eta_list eta (b:num->byte) (2 * m))`
   MINIMAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [EXISTS_TAC `buflen:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`minimal m. m = buflen \/
                       target <= offset +
                       LENGTH(mld_rej_eta_list eta (b:num->byte) (2 * m))`,
           `N:num`) THEN
  GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `N <= buflen` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `buflen:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m < N` THEN UNDISCH_TAC `N <= buflen` THEN ARITH_TAC);;

let MLD_REJ_ETA_BYTES_0 = prove
 (`!eta target offset (b:num->byte) buflen.
     target <= offset ==> mld_rej_eta_bytes eta target offset b buflen = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eta:num`; `target:num`; `offset:num`; `b:num->byte`;
                `buflen:num`;
                `mld_rej_eta_bytes eta target offset (b:num->byte) buflen`]
         MLD_REJ_ETA_BYTES) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_eta_bytes eta target offset (b:num->byte) buflen`,
           `M:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `M = 0 <=> ~(0 < M)`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; mld_rej_eta_list; list_of_seq; FILTER;
                  MAP; LENGTH] THEN
  ASM_ARITH_TAC);;

let MLD_REJ_ETA_BYTES_POS = prove
 (`!eta target offset (b:num->byte) buflen.
     0 < buflen /\ offset < target
     ==> 0 < mld_rej_eta_bytes eta target offset b buflen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eta:num`; `target:num`; `offset:num`; `b:num->byte`;
                `buflen:num`;
                `mld_rej_eta_bytes eta target offset (b:num->byte) buflen`]
         MLD_REJ_ETA_BYTES) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_eta_bytes eta target offset (b:num->byte) buflen`,
           `M:num`) THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `0 < M <=> ~(M = 0)`] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; mld_rej_eta_list; list_of_seq; FILTER;
                  MAP; LENGTH] THEN
  ASM_ARITH_TAC);;

let MLD_REJ_ETA_BYTES_NEXT = prove
 (`!eta target offset (b:num->byte) buflen M i.
     mld_rej_eta_bytes eta target offset b buflen = M /\ i < M
     ==> (i + 1 < M <=>
          i + 1 < buflen /\
          offset + LENGTH(mld_rej_eta_list eta b (2 * (i + 1))) < target)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o
             MATCH_MP MLD_REJ_ETA_BYTES) THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `M = i + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  ASM_ARITH_TAC);;

let MLD_REJ_ETA_CTR = prove
 (`!eta target offset (b:num->byte) buflen.
     mld_rej_eta_ctr eta target offset b buflen =
     offset +
     MIN (target - offset)
      (LENGTH(mld_rej_eta_list eta b
               (2 * mld_rej_eta_bytes eta target offset b buflen)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_ctr; EQ_ADD_LCANCEL] THEN
  MP_TAC(SPECL [`eta:num`; `target:num`; `offset:num`; `b:num->byte`;
                `buflen:num`;
                `mld_rej_eta_bytes eta target offset (b:num->byte) buflen`]
         MLD_REJ_ETA_BYTES) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_eta_bytes eta target offset (b:num->byte) buflen`,
           `M:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`eta:num`; `b:num->byte`; `2 * M`; `2 * buflen`]
         LENGTH_MLD_REJ_ETA_LIST_MONO) THEN
  ANTS_TAC THENL [UNDISCH_TAC `M <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `target <= offset + LENGTH(mld_rej_eta_list eta b (2 * M))` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two nibbles of byte i, as numbers, and the list after it.             *)
(* ------------------------------------------------------------------------- *)

let MLD_BYTE_NIBBLES_SMALL = prove
 (`!n. n < 256
       ==> n MOD 4294967296 = n /\ n MOD 16 MOD 4294967296 = n MOD 16 /\
           (n DIV 16) MOD 4294967296 = n DIV 16`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`n:num`; `16`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`n:num`; `16`] DIV_LE) THEN ASM_ARITH_TAC);;

let MLD_REJ_ETA_NIBBLE_BYTE = prove
 (`!(b:num->byte) i.
        mld_rej_eta_nibble b (2 * i) = word(val(b i) MOD 16) /\
        mld_rej_eta_nibble b (2 * i + 1) = word(val(b i) DIV 16)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_rej_eta_nibble; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[ARITH_RULE `(2 * i) DIV 2 = i /\ (2 * i + 1) DIV 2 = i`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_8; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `15 = 2 EXP 4 - 1`; VAL_WORD_AND_MASK_WORD;
              VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MLD_BYTE_NIBBLES_SMALL]);;

let MLD_REJ_ETA_VALID_BYTE = prove
 (`!eta (b:num->byte) i.
        (mld_rej_eta_valid eta (mld_rej_eta_nibble b (2 * i)) <=>
         val(b i) MOD 16 < (if eta = 2 then 15 else 9)) /\
        (mld_rej_eta_valid eta (mld_rej_eta_nibble b (2 * i + 1)) <=>
         val(b i) DIV 16 < (if eta = 2 then 15 else 9))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLD_REJ_ETA_NIBBLE_BYTE; mld_rej_eta_valid] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MLD_BYTE_NIBBLES_SMALL]);;

let MLD_REJ_ETA_LIST_BYTE = prove
 (`!eta (b:num->byte) i.
     mld_rej_eta_list eta b (2 * (i + 1)) =
     APPEND (mld_rej_eta_list eta b (2 * i))
      (APPEND
        (if val(b i) MOD 16 < (if eta = 2 then 15 else 9)
         then [mld_rej_eta_coeff eta (word(val(b i) MOD 16))] else [])
        (if val(b i) DIV 16 < (if eta = 2 then 15 else 9)
         then [mld_rej_eta_coeff eta (word(val(b i) DIV 16))] else []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`] THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_SUC; MLD_REJ_ETA_NIBBLE_BYTE;
              GSYM MLD_REJ_ETA_VALID_BYTE; APPEND_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The same lemmas for mld_rej_uniform_c, with groups of 3 bytes.            *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_UNIFORM_CAND_SHIFT = prove
 (`!(b:num->byte) c k.
        mld_rej_uniform_cand b (c + k) =
        mld_rej_uniform_cand (\j. b(3 * c + j)) k`,
  REWRITE_TAC[mld_rej_uniform_cand; LEFT_ADD_DISTRIB; ADD_ASSOC]);;

let MLD_REJ_UNIFORM_LIST_ADD = prove
 (`!(b:num->byte) c n.
        mld_rej_uniform_list b (c + n) =
        APPEND (mld_rej_uniform_list b c)
               (mld_rej_uniform_list (\j. b(3 * c + j)) n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_rej_uniform_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              MLD_REJ_UNIFORM_CAND_SHIFT; ETA_AX]);;

let MLD_REJ_UNIFORM_LIST_SUC = prove
 (`!(b:num->byte) n.
     mld_rej_uniform_list b (n + 1) =
     APPEND (mld_rej_uniform_list b n)
      (if val(mld_rej_uniform_cand b n) < 8380417
       then [mld_rej_uniform_cand b n] else [])`,
  REWRITE_TAC[mld_rej_uniform_list; GSYM ADD1; list_of_seq; FILTER_APPEND;
              FILTER]);;

let EL_MLD_REJ_UNIFORM_LIST_PREFIX = prove
 (`!(b:num->byte) m n j.
     m <= n /\ j < LENGTH(mld_rej_uniform_list b m)
     ==> EL j (mld_rej_uniform_list b n) = EL j (mld_rej_uniform_list b m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[mld_rej_uniform_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              EL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_rej_uniform_list]) THEN ASM_REWRITE_TAC[]);;

let LENGTH_MLD_REJ_UNIFORM_LIST_MONO = prove
 (`!(b:num->byte) m n.
     m <= n ==> LENGTH(mld_rej_uniform_list b m) <=
                LENGTH(mld_rej_uniform_list b n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[mld_rej_uniform_list; MLD_LIST_OF_SEQ_ADD; FILTER_APPEND;
              LENGTH_APPEND; LE_ADD]);;

let MLD_REJ_UNIFORM_GROUPS = prove
 (`!target offset (b:num->byte) buflen G.
     mld_rej_uniform_groups target offset b buflen = G
     ==> G <= buflen DIV 3 /\
         (G = buflen DIV 3 \/
          target <= offset + LENGTH(mld_rej_uniform_list b G)) /\
         (!m. m < G
              ==> m < buflen DIV 3 /\
                  offset + LENGTH(mld_rej_uniform_list b m) < target)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_groups] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC
   `\m. m = buflen DIV 3 \/
        target <= offset + LENGTH(mld_rej_uniform_list (b:num->byte) m)`
   MINIMAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [EXISTS_TAC `buflen DIV 3` THEN REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`minimal m. m = buflen DIV 3 \/
                       target <= offset +
                       LENGTH(mld_rej_uniform_list (b:num->byte) m)`,
           `N:num`) THEN
  GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `N <= buflen DIV 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `buflen DIV 3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m < N` THEN UNDISCH_TAC `N <= buflen DIV 3` THEN ARITH_TAC);;

let MLD_REJ_UNIFORM_GROUPS_0 = prove
 (`!target offset (b:num->byte) buflen.
     target <= offset ==> mld_rej_uniform_groups target offset b buflen = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`target:num`; `offset:num`; `b:num->byte`; `buflen:num`;
                `mld_rej_uniform_groups target offset (b:num->byte) buflen`]
         MLD_REJ_UNIFORM_GROUPS) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_uniform_groups target offset (b:num->byte) buflen`,
           `G:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `G = 0 <=> ~(0 < G)`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH] THEN
  ASM_ARITH_TAC);;

let MLD_REJ_UNIFORM_GROUPS_POS = prove
 (`!target offset (b:num->byte) buflen.
     3 <= buflen /\ offset < target
     ==> 0 < mld_rej_uniform_groups target offset b buflen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`target:num`; `offset:num`; `b:num->byte`; `buflen:num`;
                `mld_rej_uniform_groups target offset (b:num->byte) buflen`]
         MLD_REJ_UNIFORM_GROUPS) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_uniform_groups target offset (b:num->byte) buflen`,
           `G:num`) THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `0 < G <=> ~(G = 0)`] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH] THEN
  SUBGOAL_THEN `~(0 = buflen DIV 3)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `~(0 = n) <=> 1 <= n`] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_EQ; MULT_CLAUSES];
    ASM_ARITH_TAC]);;

let MLD_REJ_UNIFORM_GROUPS_NEXT = prove
 (`!target offset (b:num->byte) buflen G i.
     mld_rej_uniform_groups target offset b buflen = G /\ i < G
     ==> (i + 1 < G <=>
          i + 1 < buflen DIV 3 /\
          offset + LENGTH(mld_rej_uniform_list b (i + 1)) < target)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o
             MATCH_MP MLD_REJ_UNIFORM_GROUPS) THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `G = i + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  ASM_ARITH_TAC);;

let MLD_REJ_UNIFORM_CTR = prove
 (`!target offset (b:num->byte) buflen.
     mld_rej_uniform_ctr target offset b buflen =
     offset +
     MIN (target - offset)
      (LENGTH(mld_rej_uniform_list b
               (mld_rej_uniform_groups target offset b buflen)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_ctr; EQ_ADD_LCANCEL] THEN
  MP_TAC(SPECL [`target:num`; `offset:num`; `b:num->byte`; `buflen:num`;
                `mld_rej_uniform_groups target offset (b:num->byte) buflen`]
         MLD_REJ_UNIFORM_GROUPS) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC(`mld_rej_uniform_groups target offset (b:num->byte) buflen`,
           `G:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`b:num->byte`; `G:num`; `buflen DIV 3`]
         LENGTH_MLD_REJ_UNIFORM_LIST_MONO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `target <= offset + LENGTH(mld_rej_uniform_list b G)` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The output of mldsa_shake128x4_squeezeblocks and                          *)
(* mldsa_shake256x4_squeezeblocks, the rate parts of the states after the    *)
(* absorbed state, block i being that of keccak_squeeze (i + 1), as bytes of *)
(* the stream that mld_keccak_squeeze_byte gives from the absorbed state.    *)
(* ------------------------------------------------------------------------- *)

let MLD_NSUM_BLOCKS_BOUND = prove
 (`!(B:num->num) r n.
        (!i. i < n ==> B i < 2 EXP (8 * r))
        ==> nsum {i | i < n} (\i. 2 EXP (8 * r * i) * B i) <
            2 EXP (8 * r * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; MULT_CLAUSES; EXP; ARITH] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LT_SUC_LE; LE_REFL; LT_IMP_LE; LT];
                  ALL_TAC] THEN
  SUBGOAL_THEN `(B:num->num) n < 2 EXP (8 * r)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * (r + r * n) = 8 * r * n + 8 * r`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP (8 * r * n)`,`p:num`) THEN
  SPEC_TAC(`2 EXP (8 * r)`,`q:num`) THEN
  SPEC_TAC(`nsum {i | i < n} (\i. 2 EXP (8 * r * i) * (B:num->num) i)`,
           `a:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p + p * B(n:num)` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `p + p * b = p * (b + 1)`] THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC);;

let MLD_NSUM_BLOCKS_DIGIT = prove
 (`!(B:num->num) r n j.
        0 < r /\ (!i. i < n ==> B i < 2 EXP (8 * r)) /\ j < r * n
        ==> (nsum {i | i < n} (\i. 2 EXP (8 * r * i) * B i) DIV
             2 EXP (8 * j)) MOD 256 =
            (B (j DIV r) DIV 2 EXP (8 * (j MOD r))) MOD 256`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LT]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT] THEN
  SUBGOAL_THEN `!i. i < n ==> (B:num->num) i < 2 EXP (8 * r)` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `i < n` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_NSUM_BLOCKS_BOUND
   (ASSUME `!i. i < n ==> (B:num->num) i < 2 EXP (8 * r)`)) THEN
  ASM_CASES_TAC `j < r * n` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "nsum"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SPEC_TAC(`nsum {i | i < n} (\i. 2 EXP (8 * r * i) * (B:num->num) i)`,
             `a:num`) THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (8 * r * n) = 2 EXP (8 * j) * 256 * 2 EXP (8 * r * n - 8 * j - 8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `j < r * n` THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  SPEC_TAC(`nsum {i | i < n} (\i. 2 EXP (8 * r * i) * (B:num->num) i)`,
           `a:num`) THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j DIV r = n /\ j MOD r = j - r * n`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ; MATCH_MP_TAC MOD_UNIQ] THENL
     [EXISTS_TAC `j - r * n`; EXISTS_TAC `n:num`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; MULT_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `8 * j = 8 * r * n + 8 * (j - r * n)` SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]);;

let MLD_DIGIT_MOD = prove
 (`!x p r. p < r
           ==> ((x MOD 2 EXP (8 * r)) DIV 2 EXP (8 * p)) MOD 256 =
               (x DIV 2 EXP (8 * p)) MOD 256`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `2 EXP (8 * r) = (2 EXP (8 * p) * 256) * 2 EXP (8 * r - 8 * p - 8)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `p < r` THEN ARITH_TAC;
    REWRITE_TAC[MOD_MOD]]);;

let MLD_SQUEEZE_BLOCKS_BYTE = prove
 (`!r (S:1600 word) n j.
        0 < r /\ j < r * n
        ==> word((nsum {i | i < n}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * r)) DIV
                  2 EXP (8 * j)) MOD 256):byte =
            mld_keccak_squeeze_byte r S r j`,
  REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(ISPECL
   [`\i. val(keccak_squeeze (i + 1) (S:1600 word)) MOD 2 EXP (8 * r)`;
    `r:num`; `n:num`; `j:num`] MLD_NSUM_BLOCKS_DIGIT)) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(r + j) DIV r = j DIV r + 1 /\ (r + j) MOD r = j MOD r`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j MOD r`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j DIV r + 1`] THEN
    MP_TAC(SPECL [`j:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[LE_1; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(keccak_squeeze (j DIV r + 1) (S:1600 word))`;
                `j MOD r`; `r:num`] MLD_DIGIT_MOD) THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let MLD_KECCAK_SQUEEZE_ADD = prove
 (`!m n (S:1600 word).
        keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let MLD_KECCAK_SQUEEZE_BYTE_SHIFT = prove
 (`!r (S:1600 word) m j.
        0 < r
        ==> mld_keccak_squeeze_byte r (keccak_squeeze m S) r j =
            mld_keccak_squeeze_byte r S r (r * m + j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLD_KECCAK_SQUEEZE_ADD] THEN
  SUBGOAL_THEN `r + r * m + j = (r + j) + m * r` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `0 < r ==> ~(r = 0)`]);;

let MLD_KECCAK_ABSORB_ONCE = prove
 (`!r p inlen M.
        mld_keccak_absorb_once r p inlen M =
        word_xor
         (keccak_absorb r
           (M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad r p inlen))
           (inlen DIV r))
         (word((M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad r p inlen))
               DIV 2 EXP (8 * r * inlen DIV r) MOD 2 EXP (8 * r)))`,
  REWRITE_TAC[mld_keccak_absorb_once] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* When the stream s has 256 acceptable groups, the polynomial is the first  *)
(* 256 accepted values of any number of blocks with at least 256.            *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_UNIFORM_TERMINATES = prove
 (`!s:num->byte.
        mld_rej_uniform_terminates s
        ==> 256 <= LENGTH(mld_rej_uniform_list s
                           (280 + 56 * mld_poly_uniform_nblocks s)) /\
            (!k. 256 <= LENGTH(mld_rej_uniform_list s (280 + 56 * k))
                 ==> mld_poly_uniform_nblocks s <= k)`,
  GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_terminates] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPEC `\k. 256 <= LENGTH(mld_rej_uniform_list (s:num->byte)
                                    (280 + 56 * k))` MINIMAL) THEN
  REWRITE_TAC[GSYM mld_poly_uniform_nblocks] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN
    TRANS_TAC LE_TRANS `LENGTH(mld_rej_uniform_list (s:num->byte) n)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LENGTH_MLD_REJ_UNIFORM_LIST_MONO THEN
    ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[NOT_LE]]);;

let MLD_REJ_UNIFORM_POLY_EQ = prove
 (`!(s:num->byte) k i.
        mld_rej_uniform_terminates s /\
        256 <= LENGTH(mld_rej_uniform_list s (280 + 56 * k)) /\ i < 256
        ==> EL i (mld_rej_uniform_list s (280 + 56 * k)) =
            mld_rej_uniform_poly s i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_rej_uniform_poly] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  MATCH_MP_TAC EL_MLD_REJ_UNIFORM_LIST_PREFIX THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> 280 + 56 * a <= 280 + 56 * b`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The steps of mld_poly_uniform_4x: the count after the first five blocks,  *)
(* and the count and the coefficients after one more block of 56 groups,     *)
(* from the count c = MIN 256 (LENGTH(mld_rej_uniform_list s t)) after t     *)
(* groups, the block being the bytes of s from 3 * t on.                     *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_UNIFORM_TERMINATES_MONO = prove
 (`!(s:num->byte) k.
        mld_rej_uniform_terminates s /\ mld_poly_uniform_nblocks s <= k
        ==> 256 <= LENGTH(mld_rej_uniform_list s (280 + 56 * k))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> 256 <= a ==> 256 <= b`) THEN
  MATCH_MP_TAC LENGTH_MLD_REJ_UNIFORM_LIST_MONO THEN
  UNDISCH_TAC `mld_poly_uniform_nblocks (s:num->byte) <= k` THEN ARITH_TAC);;

let MLD_REJ_UNIFORM_CTR_FIRST = prove
 (`!s:num->byte.
     mld_rej_uniform_ctr 256 0 s 840 =
     MIN 256 (LENGTH(mld_rej_uniform_list s 280))`,
  REWRITE_TAC[mld_rej_uniform_ctr; SUB_0; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN REWRITE_TAC[]);;

let MLD_REJ_UNIFORM_CTR_BLOCK = prove
 (`!(s:num->byte) t c.
        MIN 256 (LENGTH(mld_rej_uniform_list s t)) = c
        ==> mld_rej_uniform_ctr 256 c (\j. s(3 * t + j)) 168 =
            MIN 256 (LENGTH(mld_rej_uniform_list s (t + 56)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mld_rej_uniform_ctr; MLD_REJ_UNIFORM_LIST_ADD; LENGTH_APPEND] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN ARITH_TAC);;

let MLD_REJ_UNIFORM_EL_BLOCK = prove
 (`!(s:num->byte) t c k.
        MIN 256 (LENGTH(mld_rej_uniform_list s t)) = c /\
        k < MIN 256 (LENGTH(mld_rej_uniform_list s (t + 56)))
        ==> EL k (mld_rej_uniform_list s (t + 56)) =
            if k < c then EL k (mld_rej_uniform_list s t)
            else EL (k - c) (mld_rej_uniform_list (\j. s(3 * t + j)) 56)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_ADD; EL_APPEND; LENGTH_APPEND] THEN
  ASM_CASES_TAC `k < LENGTH(mld_rej_uniform_list (s:num->byte) t)` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (s:num->byte) t) < 256`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (s:num->byte) t)) =
                  LENGTH(mld_rej_uniform_list s t)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Initial segments and sublists of the lists of a sequence.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_SUB_LIST_LIST_OF_SEQ = prove
 (`!(f:num->A) m n.
        n <= m ==> SUB_LIST(0,n) (list_of_seq f m) = list_of_seq f n`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [SIMP_TAC[LE; SUB_LIST_CLAUSES; list_of_seq]; ALL_TAC] THEN
  REWRITE_TAC[LE] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LE_REFL];
    REWRITE_TAC[list_of_seq] THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LENGTH_LIST_OF_SEQ]]);;

let MLD_SUB_LIST_APPEND_SKIP = prove
 (`!(l1:A list) l2 m n.
        LENGTH l1 = m ==> SUB_LIST(m,n) (APPEND l1 l2) = SUB_LIST(0,n) l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; APPEND] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[SUB_LIST_CLAUSES]);;

let MLD_SUB_LIST_LIST_OF_SEQ_OFFSET = prove
 (`!(f:num->A) m n p.
        m + n <= p
        ==> SUB_LIST(m,n) (list_of_seq f p) = list_of_seq (\k. f(m + k)) n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MLD_LIST_OF_SEQ_ADD] THEN
  SIMP_TAC[MLD_SUB_LIST_APPEND_SKIP; LENGTH_LIST_OF_SEQ] THEN
  MATCH_MP_TAC MLD_SUB_LIST_LIST_OF_SEQ THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The steps of mld_poly_uniform_eta_4x for a stream s with 256 acceptable   *)
(* nibbles: the list D of the values that the calls of mld_rej_eta_c for it  *)
(* declassify (mld_poly_uniform_eta_declass) has the length 2 * M for the    *)
(* number M of bytes they read, and the counts before each call are the      *)
(* numbers of T in initial segments of D. The call on the bytes from t on,   *)
(* after count c, reads MIN L (M - t) of the L bytes of its buffer and       *)
(* declassifies the corresponding part of D, and its count and coefficients  *)
(* are those of the bytes up to t + L, as for mld_poly_uniform_4x.           *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_UNIFORM_ETA_DECLASS = prove
 (`!eta (s:num->byte).
     mld_rej_eta_terminates eta s
     ==> LENGTH(mld_poly_uniform_eta_declass eta s) =
         2 * (LENGTH(mld_poly_uniform_eta_declass eta s) DIV 2) /\
         256 <= LENGTH(mld_rej_eta_list eta s
                        (LENGTH(mld_poly_uniform_eta_declass eta s))) /\
         (!m. m < LENGTH(mld_poly_uniform_eta_declass eta s) DIV 2
              ==> LENGTH(mld_rej_eta_list eta s (2 * m)) < 256) /\
         (!n. n <= LENGTH(mld_poly_uniform_eta_declass eta s)
              ==> LENGTH(FILTER (\x. x)
                    (SUB_LIST(0,n) (mld_poly_uniform_eta_declass eta s))) =
                  LENGTH(mld_rej_eta_list eta s n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_terminates] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPEC `\m. 256 <= LENGTH(mld_rej_eta_list eta (s:num->byte)
                                    (2 * m))` MINIMAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN
    TRANS_TAC LE_TRANS `LENGTH(mld_rej_eta_list eta (s:num->byte) n)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LENGTH_MLD_REJ_ETA_LIST_MONO THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mld_poly_uniform_eta_declass; LENGTH_LIST_OF_SEQ] THEN
  ABBREV_TAC `M = minimal m. 256 <= LENGTH(mld_rej_eta_list eta
                                  (s:num->byte) (2 * m))` THEN
  STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(2 * M) DIV 2 = M`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[NOT_LE];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MLD_SUB_LIST_LIST_OF_SEQ; LENGTH_MLD_REJ_ETA_LIST]]);;

let MLD_POLY_UNIFORM_ETA_COUNT = prove
 (`!eta (s:num->byte) n.
     mld_rej_eta_terminates eta s
     ==> MIN 256 (LENGTH(FILTER (\x. x)
                   (SUB_LIST(0,n) (mld_poly_uniform_eta_declass eta s)))) =
         MIN 256 (LENGTH(mld_rej_eta_list eta s n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o
    MATCH_MP MLD_POLY_UNIFORM_ETA_DECLASS) THEN
  ABBREV_TAC `D = mld_poly_uniform_eta_declass eta (s:num->byte)` THEN
  ASM_CASES_TAC `n <= LENGTH(D:bool list)` THEN ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[SUB_LIST_REFL; LT_IMP_LE] THEN
  FIRST_ASSUM(MP_TAC o SPEC `LENGTH(D:bool list)` o check (is_forall o concl)
    o check (fun th -> free_in `n:num` (concl th) = false)) THEN
  REWRITE_TAC[LE_REFL] THEN
  SIMP_TAC[SUB_LIST_REFL; LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`eta:num`; `s:num->byte`; `LENGTH(D:bool list)`; `n:num`]
    LENGTH_MLD_REJ_ETA_LIST_MONO) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN
  UNDISCH_TAC `256 <= LENGTH(mld_rej_eta_list eta (s:num->byte)
                               (LENGTH(D:bool list)))` THEN
  ARITH_TAC);;

let MLD_REJ_ETA_LIST_BLOCK = prove
 (`!eta (s:num->byte) t L.
     mld_rej_eta_list eta s (2 * (t + L)) =
     APPEND (mld_rej_eta_list eta s (2 * t))
            (mld_rej_eta_list eta (\j. s(t + j)) (2 * L))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; MLD_REJ_ETA_LIST_ADD]);;

let MLD_POLY_UNIFORM_ETA_BYTES = prove
 (`!eta (s:num->byte) t c L.
     mld_rej_eta_terminates eta s /\
     MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * t))) = c
     ==> mld_rej_eta_bytes eta 256 c (\j. s(t + j)) L =
         MIN L (LENGTH(mld_poly_uniform_eta_declass eta s) DIV 2 - t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o
    MATCH_MP MLD_POLY_UNIFORM_ETA_DECLASS) (SUBST1_TAC o SYM)) THEN
  ABBREV_TAC `M = LENGTH(mld_poly_uniform_eta_declass eta (s:num->byte))
                  DIV 2` THEN
  SUBGOAL_THEN
   `!m. 256 <= LENGTH(mld_rej_eta_list eta (s:num->byte) (2 * m)) <=> M <= m`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      TRANS_TAC LE_TRANS `LENGTH(mld_rej_eta_list eta (s:num->byte)
                         (LENGTH(mld_poly_uniform_eta_declass eta s)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LENGTH_MLD_REJ_ETA_LIST_MONO THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `M <= t` THENL
   [SUBGOAL_THEN `M - t = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `MIN L 0 = 0`] THEN
    MATCH_MP_TAC MLD_REJ_ETA_BYTES_0 THEN
    REWRITE_TAC[ARITH_RULE `256 <= MIN 256 x <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  SUBGOAL_THEN `LENGTH(mld_rej_eta_list eta (s:num->byte) (2 * t)) < 256`
  ASSUME_TAC THENL [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `x < 256 ==> MIN 256 x = x`] THEN
  REWRITE_TAC[mld_rej_eta_bytes] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  REWRITE_TAC[GSYM LENGTH_APPEND; GSYM MLD_REJ_ETA_LIST_BLOCK] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK = prove
 (`!eta (s:num->byte) t c L.
     mld_rej_eta_terminates eta s /\
     MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * t))) = c
     ==> mld_rej_eta_declass eta 256 c (\j. s(t + j)) L =
         SUB_LIST(2 * t,
                  2 * MIN L (LENGTH(mld_poly_uniform_eta_declass eta s) DIV 2
                             - t))
                 (mld_poly_uniform_eta_declass eta s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_rej_eta_declass] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP MLD_POLY_UNIFORM_ETA_BYTES th]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_POLY_UNIFORM_ETA_DECLASS o
                CONJUNCT1) THEN
  ABBREV_TAC `D = mld_poly_uniform_eta_declass eta (s:num->byte)` THEN
  ASM_CASES_TAC `LENGTH(D:bool list) DIV 2 <= t` THENL
   [SUBGOAL_THEN `LENGTH(D:bool list) DIV 2 - t = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `MIN L 0 = 0`; MULT_CLAUSES; list_of_seq;
                SUB_LIST_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `D = list_of_seq (\k. mld_rej_eta_valid eta
                          (mld_rej_eta_nibble (s:num->byte) k))
                    (LENGTH(D:bool list))`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[mld_poly_uniform_eta_declass; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand)
     MLD_SUB_LIST_LIST_OF_SEQ_OFFSET (rand w))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MLD_REJ_ETA_NIBBLE_SHIFT]);;

let MLD_REJ_ETA_CTR_BLOCK = prove
 (`!eta (s:num->byte) t c L.
     MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * t))) = c
     ==> mld_rej_eta_ctr eta 256 c (\j. s(t + j)) L =
         MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * (t + L))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mld_rej_eta_ctr; MLD_REJ_ETA_LIST_BLOCK; LENGTH_APPEND] THEN
  ARITH_TAC);;

let MLD_REJ_ETA_EL_BLOCK = prove
 (`!eta (s:num->byte) t c L k.
     MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * t))) = c /\
     k < MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * (t + L))))
     ==> EL k (mld_rej_eta_list eta s (2 * (t + L))) =
         if k < c then EL k (mld_rej_eta_list eta s (2 * t))
         else EL (k - c) (mld_rej_eta_list eta (\j. s(t + j)) (2 * L))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_BLOCK; EL_APPEND; LENGTH_APPEND] THEN
  ASM_CASES_TAC `k < LENGTH(mld_rej_eta_list eta (s:num->byte) (2 * t))` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH(mld_rej_eta_list eta (s:num->byte) (2 * t)) < 256`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_eta_list eta (s:num->byte)
                                   (2 * t))) =
                  LENGTH(mld_rej_eta_list eta s (2 * t))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let MLD_REJ_ETA_CTR_FIRST = prove
 (`!eta (s:num->byte) L.
     mld_rej_eta_ctr eta 256 0 s L =
     MIN 256 (LENGTH(mld_rej_eta_list eta s (2 * L)))`,
  REWRITE_TAC[mld_rej_eta_ctr; SUB_0; ADD_CLAUSES]);;

let MLD_POLY_UNIFORM_ETA_DECLASS_FIRST = prove
 (`!eta (s:num->byte) L.
     mld_rej_eta_terminates eta s
     ==> mld_rej_eta_declass eta 256 0 s L =
         SUB_LIST(0,2 * MIN L (LENGTH(mld_poly_uniform_eta_declass eta s)
                              DIV 2))
                 (mld_poly_uniform_eta_declass eta s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eta:num`; `s:num->byte`; `0`; `0`; `L:num`]
    MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; ADD_CLAUSES; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[mld_rej_eta_list; list_of_seq; FILTER; MAP; LENGTH] THEN
  ARITH_TAC);;

let MLD_POLY_UNIFORM_ETA_DONE = prove
 (`!eta (s:num->byte) n.
     mld_rej_eta_terminates eta s /\
     LENGTH(mld_poly_uniform_eta_declass eta s) <= n
     ==> 256 <= LENGTH(FILTER (\x. x)
                 (SUB_LIST(0,n) (mld_poly_uniform_eta_declass eta s)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o
    MATCH_MP MLD_POLY_UNIFORM_ETA_DECLASS) ASSUME_TAC) THEN
  ASM_SIMP_TAC[SUB_LIST_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `LENGTH(mld_poly_uniform_eta_declass eta (s:num->byte))` o
   check (is_forall o concl) o
   check (fun th -> can (find_term ((=) `FILTER:(bool->bool)->bool list->
                                          bool list`)) (concl th))) THEN
  SIMP_TAC[LE_REFL; SUB_LIST_REFL] THEN ASM_ARITH_TAC);;

let MLD_REJ_ETA_TERMINATES = prove
 (`!eta (s:num->byte).
        mld_rej_eta_terminates eta s
        ==> 256 <= LENGTH(mld_rej_eta_list eta s
                           (2 * 136 * ((if eta = 2 then 1 else 2) +
                                       mld_poly_uniform_eta_nblocks eta s))) /\
            (!k. 256 <= LENGTH(mld_rej_eta_list eta s
                                (2 * 136 * ((if eta = 2 then 1 else 2) + k)))
                 ==> mld_poly_uniform_eta_nblocks eta s <= k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_terminates] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPEC `\k. 256 <= LENGTH(mld_rej_eta_list eta (s:num->byte)
                    (2 * 136 * ((if eta = 2 then 1 else 2) + k)))` MINIMAL) THEN
  REWRITE_TAC[GSYM mld_poly_uniform_eta_nblocks] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN
    TRANS_TAC LE_TRANS `LENGTH(mld_rej_eta_list eta (s:num->byte) n)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LENGTH_MLD_REJ_ETA_LIST_MONO THEN
    ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[NOT_LE]]);;

let MLD_REJ_ETA_POLY_EQ = prove
 (`!eta (s:num->byte) k i.
        mld_rej_eta_terminates eta s /\
        256 <= LENGTH(mld_rej_eta_list eta s
                       (2 * 136 * ((if eta = 2 then 1 else 2) + k))) /\
        i < 256
        ==> EL i (mld_rej_eta_list eta s
                   (2 * 136 * ((if eta = 2 then 1 else 2) + k))) =
            mld_rej_eta_poly eta s i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_rej_eta_poly] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_REJ_ETA_TERMINATES) THEN
  MATCH_MP_TAC EL_MLD_REJ_ETA_LIST_PREFIX THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> 2 * 136 * (c + a) <= 2 * 136 * (c + b)`)
  THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* mld_polyvec_matrix_expand (polyvec_lazy.c): entry (i,j) of the matrix of  *)
(* k rows of l polynomials is mld_poly_uniform of the seed rho || j || i of  *)
(* 34 bytes (as a number, mld_matrix_seed), and the matrix is one function   *)
(* for its 256 * k * l coefficients, entry (i,j) being polynomial l * i + j  *)
(* (common/mldsa_native_polyvec.ml). Sampling terminates if the SHAKE128     *)
(* output of each seed has 256 acceptable groups (mld_matrix_terminates).    *)
(* ------------------------------------------------------------------------- *)

let mld_matrix_seed = new_definition
 `mld_matrix_seed rho i j = rho + 2 EXP 256 * (j + 256 * i)`;;

let mld_polyvec_matrix_expand = new_definition
 `mld_polyvec_matrix_expand l rho =
    \n. mld_poly_uniform
         (mld_matrix_seed rho ((n DIV 256) DIV l) ((n DIV 256) MOD l))
         (n MOD 256)`;;

let mld_matrix_terminates = new_definition
 `mld_matrix_terminates k l rho <=>
    !i j. i < k /\ j < l
          ==> mld_rej_uniform_terminates
               (mld_shake128_stream 34 (mld_matrix_seed rho i j))`;;

let MLD_POLYVEC_MATRIX_EXPAND_COEFF = prove
 (`!l rho k c.
        c < 256
        ==> mld_polyvec_matrix_expand l rho (256 * k + c) =
            mld_poly_uniform (mld_matrix_seed rho (k DIV l) (k MOD l)) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec_matrix_expand] THEN
  SUBGOAL_THEN `(256 * k + c) DIV 256 = k /\ (256 * k + c) MOD 256 = c`
   (fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
               ADD_CLAUSES]);;
