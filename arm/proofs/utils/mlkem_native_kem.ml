(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of the ML-KEM functions of mlkem-native *)
(* in the gcc 12 -O2 image, such as mlkem768_dec: the lengths of the results *)
(* of the algorithms of FIPS 203 and the forms of its internal ML-KEM        *)
(* algorithms used in the proofs, copies of 32-byte values as two 128-bit    *)
(* words, the constant-time comparison of byte arrays 16 bytes at a time,    *)
(* and the conditional move of 32 bytes one byte at a time.                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/utils/mlkem_native_fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* The algorithms of FIPS 203: lengths, and the internal ML-KEM algorithms   *)
(* (FIPS 203 Algorithms 16, 17 and 18) with the hash functions unfolded.     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA3_256 = prove
 (`!m. LENGTH(sha3_256 m) = 32`,
  REWRITE_TAC[sha3_256; LENGTH_LIST_OF_SEQ]);;

let LENGTH_SHA3_512 = prove
 (`!m. LENGTH(sha3_512 m) = 64`,
  REWRITE_TAC[sha3_512; LENGTH_LIST_OF_SEQ]);;

let KPKE_KEYGEN_LENGTHS = prove
 (`!k eta1 eta2 du dv d.
        LENGTH(FST(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k + 32 /\
        LENGTH(SND(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k`,
  REWRITE_TAC[kpke_keygen; mlkem_g] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND; MLKEM_ENCODE_LENGTH; mlkem_slice;
              LENGTH_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let KPKE_ENCRYPT_LENGTH = prove
 (`!k eta1 eta2 du dv ek m r.
        LENGTH(kpke_encrypt (k,eta1,eta2,du,dv) ek m r) = 32 * (du * k + dv)`,
  REWRITE_TAC[kpke_encrypt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND; MLKEM_ENCODE_LENGTH] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `du * 256 * k = 8 * (32 * du * k) /\ dv * 256 = 8 * (32 * dv)`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

let KPKE_DECRYPT_LENGTH = prove
 (`!k eta1 eta2 du dv dk c.
        LENGTH(kpke_decrypt (k,eta1,eta2,du,dv) dk c) = 32`,
  REWRITE_TAC[kpke_decrypt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_SLICE_SLICE = prove
 (`!a n b m (l:byte list).
        a + n <= m
        ==> mlkem_slice a n (mlkem_slice b m l) = mlkem_slice (b + a) n l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_slice] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `a + i < m` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_LIST_OF_SEQ; ADD_ASSOC]]);;

let NUM_OF_BYTELIST_INJ = prove
 (`!l1 l2:byte list.
        LENGTH l1 = LENGTH l2
        ==> (num_of_bytelist l1 = num_of_bytelist l2 <=> l1 = l2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_KEYGEN_PAIR = prove
 (`!k eta1 eta2 du dv d z.
        mlkem_keygen (k,eta1,eta2,du,dv) d z =
        FST(kpke_keygen (k,eta1,eta2,du,dv) d),
        APPEND (SND(kpke_keygen (k,eta1,eta2,du,dv) d))
         (APPEND (FST(kpke_keygen (k,eta1,eta2,du,dv) d))
           (APPEND (mlkem_h(FST(kpke_keygen (k,eta1,eta2,du,dv) d))) z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_keygen; mlkem_keygen_internal] THEN
  SPEC_TAC(`kpke_keygen (k,eta1,eta2,du,dv) d`,`kk:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let MLKEM_ENCAPS_PAIR = prove
 (`!k eta1 eta2 du dv ek m.
        mlkem_encaps_internal (k,eta1,eta2,du,dv) ek m =
        mlkem_slice 0 32 (sha3_512 (APPEND m (sha3_256 ek))),
        kpke_encrypt (k,eta1,eta2,du,dv) ek m
         (mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek))))`,
  REWRITE_TAC[mlkem_encaps_internal; mlkem_g; mlkem_h] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLKEM_DECAPS_ALT = prove
 (`!k eta1 eta2 du dv dk c.
        mlkem_decaps_internal (k,eta1,eta2,du,dv) dk c =
        let m' = kpke_decrypt (k,eta1,eta2,du,dv)
                  (mlkem_slice 0 (384 * k) dk) c in
        let g = sha3_512 (APPEND m' (mlkem_slice (768 * k + 32) 32 dk)) in
        if kpke_encrypt (k,eta1,eta2,du,dv)
            (mlkem_slice (384 * k) (384 * k + 32) dk) m'
            (mlkem_slice 32 32 g) =
           c
        then mlkem_slice 0 32 g
        else list_of_seq
              (shake256 (APPEND (mlkem_slice (768 * k + 64) 32 dk) c))
                         32`,
  REWRITE_TAC[mlkem_decaps_internal; mlkem_g; mlkem_j] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Labels for the contracts of memset and memcpy, the GOT entries in the     *)
(* form used by the callees (when they are in the form used by the PLT       *)
(* stubs), offsets from the stack pointer, and copies of 32 bytes as two     *)
(* 128-bit words.                                                            *)
(* ------------------------------------------------------------------------- *)

let KEM_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let KEM_HAS_CONST c tm =
  can (find_term (fun t -> match t with Const(c',_) -> c' = c | _ -> false))
      tm;;

let KEM_LABELS_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_contract mf ea el ev`) (concl th)
    then LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_contract mc ea el ev`) (concl th)
    then LABEL_TAC "H_MEMCPY" (REWRITE_RULE[memcpy_contract] th)
    else NO_TAC);;

let KEM_GOT_TAC =
  let pat n = subst [mk_small_numeral n,`n:num`]
   `read (memory :> bytes64 (word_add (word pc) (word n):int64)) s =
    (g:int64)` in
  MAP_EVERY (fun n ->
    TRY(FIRST_ASSUM(fun th ->
      if can (term_match [] (pat n)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC)))
   [131064; 131048; 131024];;

let KEM_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEM_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

let KEM_HALVES_TAC a =
  FIRST_ASSUM(MP_TAC o MATCH_MP KEM_BYTES128_HALVES o check
   (can (term_match [] (subst [a,`a:int64`]
     `read (memory :> bytes(a,32)) s = n`)) o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KEM_JOIN_TAC a l s =
  MP_TAC(SPECL [a; mk_comb(`num_of_bytelist`,l);
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC l NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The constant-time comparison of two byte arrays: the 16 bytes at a time   *)
(* of the two arrays XORed together are ORed into one accumulator (and XORed *)
(* into another), which is zero if and only if the prefixes so far are       *)
(* equal.                                                                    *)
(* ------------------------------------------------------------------------- *)

let KEM_BYTES128 = prove
 (`!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 * k = 8 * 16 * k`; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_MOD; MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let KEM_MOD_STEP = prove
 (`!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * (k + 1) = 128 * k + 128`; EXP_ADD] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEXICOGRAPHIC_EQ o lhand o snd) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

let KEM_OR_STEP = prove
 (`!q:int128 a b.
        word_or
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456)))
         q = word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[VAL_EQ; CONJ_ACI; EQ_SYM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The conditional move of 32 bytes, one byte at a time with a mask from the *)
(* comparison: the bytes of a value from offset i, the extension of a prefix *)
(* by one byte, the addresses of the bytes as computed by the code, and its  *)
(* loop test.                                                                *)
(* ------------------------------------------------------------------------- *)

let KEM_SPLIT1 = prove
 (`!a l x s:armstate.
        read (memory :> bytes(a,l + 1)) s = x
        ==> read (memory :> bytes8 a) s = word(x MOD 256) /\
            read (memory :> bytes(word_add a (word 1),l)) s = x DIV 256`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `MIN (l + 1) 1 = 1`;
              ARITH_RULE `(l + 1) - 1 = l`] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1; WORD_VAL]);;

let KEM_MOD_BYTE = prove
 (`!x i. x MOD 2 EXP (8 * (i + 1)) =
         x MOD 2 EXP (8 * i) +
         2 EXP (8 * i) * ((x DIV 2 EXP (8 * i)) MOD 256)`,
  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let KEM_DIV_BYTE = prove
 (`!x i. x DIV 2 EXP (8 * (i + 1)) = (x DIV 2 EXP (8 * i)) DIV 256`,
  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; EXP_ADD; DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEM_VAL_BYTE = prove
 (`!n. n MOD 256 = val(word(n MOD 256):byte)`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let KEM_SS_ADDR = prove
 (`!ss:int64 i. word_add (word_sub ss (word 1)) (word (i + 1)) =
                word_add ss (word i)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let KEM_KP_ADDR = prove
 (`!sp:int64 a i.
        word_add (word_add sp (word a)) (word i) =
        word_add sp (word (a + (i + 1) + 18446744073709551615))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `a + (i + 1) + 18446744073709551615 =
                          1 * 18446744073709551616 + (a + i)`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let KEM_CMOV_TEST = prove
 (`!i. i < 32
       ==> (val(word_add (word (i + 1)) (word 18446744073709551584):int64) =
            0 <=> ~(i + 1 < 32))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(i + 1) MOD 18446744073709551616 = i + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(ARITH_RULE `~(x = 0) /\ x MOD n = x ==> ~(x MOD n = 0)`) THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `i + 1 = 32` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The random bytes written by randombytes, as the seeds d and z (64 bytes)  *)
(* or as the message m (32 bytes) of the algorithms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KEM_RANDOM_SPLIT = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,64)) s = n
        ==> read (memory :> bytes(a,32)) s =
            num_of_bytelist(bytelist_of_num 32 (n MOD 2 EXP 256)) /\
            read (memory :> bytes(word_add a (word 32),32)) s =
            num_of_bytelist(bytelist_of_num 32 (n DIV 2 EXP 256))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[ARITH_RULE `256 EXP 32 = 2 EXP (8 * 32)`;
              ARITH_RULE `2 EXP 256 = 2 EXP (8 * 32)`] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD; READ_BYTES_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`word_add a (word 32):int64`; `32`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let KEM_RANDOM_32 = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> num_of_bytelist(bytelist_of_num 32 n) = n`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  MP_TAC(ISPECL [`a:int64`; `32`; `read memory s`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
