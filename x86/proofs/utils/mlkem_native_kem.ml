(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of the ML-KEM functions of mlkem-native *)
(* in the gcc 12 -O2 image, such as mlkem768_enc_derand, as in               *)
(* arm/proofs/utils/mlkem_native_kem.ml: the lengths of the results of the   *)
(* algorithms of FIPS 203 and the forms of its internal ML-KEM algorithms    *)
(* used in the proofs, copies of 32-byte values as two 128-bit words, and    *)
(* the inline copies of byte arrays by REP MOVSQ. The frames are handled by  *)
(* the tactics of mlkem_native_indcpa.ml.                                    *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

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
(* Copies of 32 bytes as two 128-bit words: the halves of a value in memory, *)
(* and the value from its halves.                                            *)
(* ------------------------------------------------------------------------- *)

let KEM_BYTES128_HALVES = prove
 (`!a:int64 n s:x86state.
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
 (`!a:int64 n s:x86state.
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
                mk_var(s,`:x86state`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC l NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The inline memcpy of n bytes (a multiple of 8) from pk to sk + t, as gcc  *)
(* compiles it for a destination that is not known to be aligned: the first  *)
(* and the last 8 bytes, then by REP MOVSQ the n DIV 8 - 1 quadwords from    *)
(* the first multiple of 8 after the destination, sk + t + lo for lo = 8 -   *)
(* val(sk + t) MOD 8 (by MEMSET_ALIGN_ADDR), so that the parts of the first  *)
(* and last quadwords outside them are kept. The lemmas KEM_BYTES64_OF_NUM,  *)
(* KEM_BYTES_JOIN and KEM_MOVSQ_FACT are as in                               *)
(* mlkem_native_shake256x4_gcc12_O2.ml. KEM_MEMCPY_REGS_TAC gives lo and the *)
(* values of the registers for the REP MOVSQ, KEM_MOVSQ_STEP_TAC steps it,   *)
(* keeping the fact for the memory it writes, which the simulation does not, *)
(* and KEM_MEMCPY_TAC does the whole copy, leaving the fact for the n bytes  *)
(* at sk + t. For the safety proofs, KEM_UNLO_TAC expands lo in the events,  *)
(* and KEM_MEMCPY_DISCHARGE_TAC is DISCHARGE_SAFETY_PROPERTY_TAC with val(sk *)
(* + t) MOD 8 as a variable for the bounds of the accesses.                  *)
(* ------------------------------------------------------------------------- *)

let KEM_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 18446744073709551616)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let KEM_BYTES_JOIN = prove
 (`!a:int64 x k l s:x86state.
        read (memory :> bytes(a,k)) s = x MOD 2 EXP (8 * k) /\
        read (memory :> bytes(word_add a (word k),l)) s =
        (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)
        ==> read (memory :> bytes(a,k + l)) s = x MOD 2 EXP (8 * (k + l))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  MATCH_ACCEPT_TAC ADD_SYM);;

let KEM_MOVSQ_FACT = prove
 (`!df a b n x s s' t.
        read (memory :> bytes(b,8 * n)) s' =
        read (memory :> bytes(b,8 * n))
         (write (memory :> bytes(b,8 * n))
           (x86_qstringcopy df a b n x (read (memory :> bytes(b,8 * n)) s))
           t)
        ==> nonoverlapping (a,8 * n) (b,8 * n) /\
            read (memory :> bytes(a,8 * n)) s = x /\
            8 * n <= 2 EXP 64
            ==> read (memory :> bytes(b,8 * n)) s' = x`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[X86_QSTRINGCOPY_NONOVERLAPPING] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[REWRITE_RULE[valid_component]
    (VALID_COMPONENT_CONV `valid_component memory`)] THEN
  ASM_SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[READ_BYTES_BOUND]);;

let KEM_MEMCPY_ALIGN = prove
 (`!sk:int64 t lo.
        8 - val(word_add sk (word t)) MOD 8 = lo
        ==> word_and (word_add sk (word (t + 8))) (word 18446744073709551608) =
            word_add sk (word (t + lo))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `word_add sk (word t):int64` MEMSET_ALIGN_ADDR) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let KEM_MEMCPY_SRC = prove
 (`!pk sk:int64 t lo.
        word_sub pk (word_sub (word_add sk (word t))
                              (word_add sk (word (t + lo)))) =
        word_add pk (word lo)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let KEM_MEMCPY_ARITH = prove
 (`!q lo. 1 <= q /\ 8 * q < 2147483648 /\ 1 <= lo /\ lo <= 8
          ==> ((((18446744073709551616 - lo) MOD 4294967296 +
                 (8 * q) MOD 4294967296) MOD 4294967296 MOD
                18446744073709551616 MOD 4294967296) DIV 8) MOD
              18446744073709551616 = q - 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(18446744073709551616 - lo) MOD 4294967296 = 4294967296 - lo`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `4294967295` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(8 * q) MOD 4294967296 = 8 * q` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(4294967296 - lo + 8 * q) MOD 4294967296 = 8 * q - lo`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(8 * q - lo) MOD 18446744073709551616 MOD 4294967296 =
                8 * q - lo` SUBST1_TAC THENL
   [SUBGOAL_THEN `8 * q - lo < 4294967296` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `x < 4294967296 ==> x < 18446744073709551616`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(8 * q - lo) DIV 8 = q - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `8 - lo` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let KEM_MEMCPY_COUNT = prove
 (`!sk:int64 t lo n.
        1 <= lo /\ lo <= 8 /\ 8 <= n /\ n < 2147483648 /\ 8 divides n
        ==> (word_zx:int32->int64)
             (word_ushr ((word_zx:int64->int32) ((word_zx:int32->int64)
               (word_add ((word_zx:int64->int32)
                 (word_sub (word_add sk (word t))
                           (word_add sk (word (t + lo)))))
                (word n)))) 3) =
            word(n DIV 8 - 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_add sk (word t)) (word_add sk (word (t + lo))):int64 =
    word_neg(word lo)`] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD_ADD; VAL_WORD;
              VAL_WORD_NEG_CASES; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `lo MOD 18446744073709551616 = lo` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= lo ==> ~(lo = 0)`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(8 * q) DIV 8 = q`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) KEM_MEMCPY_ARITH o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let KEM_MEMCPY_JOIN = prove
 (`!a:int64 x n lo s:x86state.
        1 <= lo /\ lo <= 8 /\ 8 <= n /\
        read (memory :> bytes(a,lo)) s = x MOD 2 EXP (8 * lo) /\
        read (memory :> bytes(word_add a (word lo),n - 8)) s =
        (x DIV 2 EXP (8 * lo)) MOD 2 EXP (8 * (n - 8)) /\
        read (memory :> bytes(word_add a (word (n - 8 + lo)),8 - lo)) s =
        (x DIV 2 EXP (8 * (n - 8 + lo))) MOD 2 EXP (8 * (8 - lo))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `x:num`; `lo:num`; `n - 8`; `s:x86state`]
    KEM_BYTES_JOIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `x:num`; `lo + (n - 8)`; `8 - lo`; `s:x86state`]
    KEM_BYTES_JOIN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lo + (n - 8) = n - 8 + lo /\ (n - 8 + lo) + (8 - lo) = n`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let KEM_BYTES64_PREFIX = prove
 (`!a:int64 y k s:x86state.
        read (memory :> bytes64 a) s = word(y MOD 2 EXP 64) /\ k <= 8
        ==> read (memory :> bytes(a,k)) s = y MOD 2 EXP (8 * k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o AP_TERM `val:int64->num`)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `k:num`; `read memory s`] READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 8 ==> MIN 8 k = k`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 8 ==> MIN (8 * 8) (8 * k) = 8 * k`]);;

let KEM_BYTES64_SUFFIX = prove
 (`!a:int64 y k s:x86state.
        read (memory :> bytes64 a) s = word(y MOD 2 EXP 64) /\ k <= 8
        ==> read (memory :> bytes(word_add a (word k),8 - k)) s =
            (y DIV 2 EXP (8 * k)) MOD 2 EXP (8 * (8 - k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o AP_TERM `val:int64->num`)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM READ_BYTES_DIV] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 8 ==> 8 * k + 8 * (8 - k) = 64`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEM_MEMCPY_JOIN2 = prove
 (`!a:int64 x y z n lo s.
        1 <= lo /\ lo <= 8 /\ 8 <= n /\
        x DIV 2 EXP (8 * (n - 8)) = y /\
        (x DIV 2 EXP (8 * lo)) MOD 2 EXP (8 * (n - 8)) = z /\
        read (memory :> bytes(a,lo)) s = x MOD 2 EXP (8 * lo) /\
        read (memory :> bytes(word_add a (word lo),n - 8)) s = z /\
        read (memory :> bytes(word_add a (word (n - 8 + lo)),8 - lo)) s =
        (y DIV 2 EXP (8 * lo)) MOD 2 EXP (8 * (8 - lo))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC KEM_MEMCPY_JOIN THEN
  EXISTS_TAC `lo:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `y:num`)) THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * (n - 8) + 8 * lo = 8 * (n - 8 + lo)`]);;

let KEM_MOVSQ_RESULT n =
  let th = INST [mk_small_numeral n,`n:num`]
            (SPEC_ALL KEM_MOVSQ_FACT) in
  GEN_ALL(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let KEM_MOVSQ_STEP_TAC execth st n =
  let sname = "s" ^ string_of_int st in
  let sv = mk_var(sname,`:x86state`) in
  let is_qsc t = match strip_comb t with
                   Const("x86_qstringcopy",_),_ -> true | _ -> false in
  let lemma = KEM_MOVSQ_RESULT n in
  X86_VSTEPS_TAC execth [st] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(a,k)) s`) (lhand c) &&
       rand(lhand c) = sv && can (find_term is_qsc) (rand c)
    then MP_TAC(MATCH_MP lemma th) else NO_TAC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]; CONV_TAC NUM_REDUCE_CONV];
    DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC sname;;

let KEM_MEMCPY_REGS_TAC t n =
  let num = mk_small_numeral in
  let pf fmt = Printf.ksprintf parse_term fmt in
  ABBREV_TAC(pf "lo = 8 - val(word_add sk (word %d):int64) MOD 8" t) THEN
  SUBGOAL_THEN `1 <= lo /\ lo <= 8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lo" THEN
    MP_TAC(SPECL [pf "val(word_add sk (word %d):int64)" t; `8`]
           MOD_LT_EQ) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `lo:num`
    then ASSUME_TAC th THEN
         RULE_ASSUM_TAC(REWRITE_RULE[CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (MATCH_MP (SPECL [`sk:int64`; num t; `lo:num`] KEM_MEMCPY_ALIGN)
                    th)])
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KEM_MEMCPY_SRC]) THEN
  MP_TAC(SPECL [`sk:int64`; num t; `lo:num`; num n] KEM_MEMCPY_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let KEM_MEMCPY_TAC execth p r t n stk =
  let num = mk_small_numeral and n8 = n - 8 in
  let pf fmt = Printf.ksprintf parse_term fmt in
  let sv = mk_var("s" ^ string_of_int r,`:x86state`) in
  let side = ARITH_RULE(pf "0 + 8 <= %d /\\ %d + 8 <= %d" n n8 n) in
  let dst = pf "word_add sk (word %d):int64" t in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pf "read (memory :> bytes(pk,%d)) s = v" n))
           (concl th)
    then
      let v = rand(concl th) and s = rand(lhand(concl th)) in
      MP_TAC(SPECL [`pk:int64`; num n; v; `0`; s]
               KEM_BYTES64_OF_NUM) THEN
      MP_TAC(SPECL [`pk:int64`; num n; v; num n8; s]
               KEM_BYTES64_OF_NUM) THEN
      ASM_REWRITE_TAC[side] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
      MP_TAC(ISPEC (rand v) NUM_OF_BYTELIST_BOUND) THEN
      ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
      ABBREV_TAC(mk_eq(`x:num`,v)) THEN
      ABBREV_TAC(pf "y2 = x DIV 2 EXP (8 * %d)" n8) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  X86_STEPS_TAC execth (p--(r-2)) THEN KEM_MEMCPY_REGS_TAC t n THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pf "read (memory :> bytes64(%s)) s =
                                word(x MOD 2 EXP 64)" (string_of_term dst)))
           (concl th)
    then ASSUME_TAC(MATCH_MP KEM_BYTES64_PREFIX
           (CONJ th (ASSUME `lo <= 8`)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
             (pf "read (memory :> bytes64(word_add sk (word %d))) s =
                  word(y2 MOD 2 EXP 64)" (t + n8)))
           (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
           (MATCH_MP KEM_BYTES64_SUFFIX (CONJ th (ASSUME `lo <= 8`))))
    else NO_TAC) THEN
  ABBREV_TAC(pf "y3 = (x DIV 2 EXP (8 * lo)) MOD 2 EXP (8 * %d)" n8) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pf "read (memory :> bytes(pk,%d)) s = x" n))
           (concl th)
    then MP_TAC(SPECL [`pk:int64`; num n; `x:num`; `lo:num`; num n8;
                       rand(lhand(concl th))] READ_MEMORY_BYTES_SUB) THEN
         ASM_REWRITE_TAC[] THEN
         ANTS_TAC THENL [UNDISCH_TAC `lo <= 8` THEN ARITH_TAC; DISCH_TAC]
    else NO_TAC) THEN
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      pf "word_add sk (word (%d + lo)):int64,%d" t n8),r))
     ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC])
   [pf "word_add pk (word lo):int64,%d" n8;
    pf "word_add sk (word %d):int64,lo:num" t;
    pf "word_add sk (word (%d + lo)):int64,8 - lo" (t + n8);
    pf "pk:int64,%d" n; pf "sk:int64,%d" t; `coins:int64,64`;
    `word pc:int64,0x82a0`; stk] THEN
  X86_STEPS_TAC execth [r - 1] THEN
  KEM_MOVSQ_STEP_TAC execth r (n8 / 8) THEN
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`read:(x86state,num)component->x86state->num`,
     [pf "memory :> bytes(word_add sk (word %d),%d)" t n; sv]), `x:num`))
  ASSUME_TAC THENL
   [MP_TAC(SPECL [dst; `x:num`; `y2:num`; `y3:num`; num n; `lo:num`; sv]
                 KEM_MEMCPY_JOIN2) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[ARITH_RULE(pf "8 <= %d" n)] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let KEM_UNLO_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `lo:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let KEM_MEMCPY_DISCHARGE_TAC a =
  let md = mk_comb(mk_comb(`(MOD):num->num->num`,
                           mk_comb(`val:int64->num`,a)),`8`) in
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  MP_TAC(SPECL [mk_comb(`val:int64->num`,a); `8`] MOD_LT_EQ) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC(mk_eq(`md:num`,md)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(mk_eq(md,`md:num`))]) THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The decapsulation: the comparison of the ciphertexts, 16 bytes at a time  *)
(* with an OR accumulator, as for AArch64 (KEM_BYTES128, KEM_MOD_STEP and    *)
(* KEM_OR_STEP, with the operands of the OR in the order of POR), and the    *)
(* conditional move of 32 bytes, one byte at a time with a mask from the     *)
(* comparison (KEM_SPLIT1, KEM_MOD_BYTE, KEM_DIV_BYTE and KEM_VAL_BYTE). For *)
(* the legacy SSE moves, KEM_SUBWORD_JOIN_128 gives the XMM part of the      *)
(* values of YMM registers, and KEM_MOD256 puts the zero extensions of bytes *)
(* in a form for BITBLAST. For a memory operand at base + index, the address *)
(* is computed as word_add a (word(1 * n)) when the index register is word   *)
(* n, and KEM_INDEX_TAC and KEM_INDEX1_TAC restate the assumptions about the *)
(* 128-bit words at offsets 16 * i and the bytes at offsets i in that form.  *)
(* KEM_CMOV_TEST is the test of the loop of the conditional move.            *)
(* ------------------------------------------------------------------------- *)

let KEM_BYTES128 = prove
 (`!a l k n s:x86state.
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
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[VAL_EQ; CONJ_ACI; EQ_SYM_EQ]);;

let KEM_SPLIT1 = prove
 (`!a l x s:x86state.
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

let KEM_SUBWORD_JOIN_128 = prove
 (`!h:int128 l:int128.
    word_subword (word_join h l:int256) (0,128):int128 = l`,
  CONV_TAC WORD_BLAST);;

let KEM_MOD256 = prove
 (`!x:N word. word(val x MOD 256):M word = word_zx(word_zx x:byte)`,
  REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let KEM_INDEX_TAC =
  let pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes128 (word_add a (word n))) s = v`) c &&
       free_in `i:num` (lhand c)
    then GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [pth] th else th);;

let KEM_INDEX1_TAC =
  let ith = ARITH_RULE `i = 1 * i` in
  let conv t = if t = `i:num` then ith else failwith "KEM_INDEX1_TAC" in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes8 (word_add a (word n))) s = v`) c &&
       free_in `i:num` (lhand c)
    then CONV_RULE (LAND_CONV(ONCE_DEPTH_CONV conv)) th else th);;

let KEM_CMOV_TEST = prove
 (`!i. i < 32
       ==> (val(word_add (word i) (word 18446744073709551585):int64) = 0 <=>
            ~(i + 1 < 32))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> i < 18446744073709551616`]
  THEN ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i + 1 < 32 ==> i + 18446744073709551585 < 18446744073709551616`]
    THEN ARITH_TAC;
    SUBGOAL_THEN `i = 31` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;
