(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. This is the    *)
(* code for mlkem_poly_rej_uniform from mlkem-native's portable C            *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which absorbs the 34 bytes of the seed into a SHAKE128 state, squeezes    *)
(* three blocks of 168 bytes and samples the coefficients below 3329 from    *)
(* them with mlk_rej_uniform_c, and then squeezes one more block and samples *)
(* from it until there are 256, before zeroing the state and the buffer. It  *)
(* is verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),   *)
(* where it is at address 0x4d40, using the theorems for mlkem_shake128_init *)
(* at 0x2540, mlkem_shake128_absorb_once at 0x24d0,                          *)
(* mlkem_shake128_squeezeblocks at 0x24e4, mlkem_shake128_release at 0x2544  *)
(* and mlk_rej_uniform_c at 0x4a90 in the image and assuming the contract    *)
(* for memset in utils/mlkem_native_libc.ml. There is no constant-time and   *)
(* memory safety proof yet (see mlkem_native/README.md).                     *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native_shake128_init_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128_squeezeblocks_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128_release_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_rej_uniform_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image, and the PLT stub for memset:

    4d40: sub     sp, sp, #0x330
    4d44: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    4d48: ldr     x2, [x2, #4088]
    4d4c: stp     x19, x20, [sp]
    4d50: mov     x19, x1
    4d54: add     x20, sp, #0x4f
    4d58: stp     x21, x22, [sp, #16]
    4d5c: and     x20, x20, #0xffffffffffffffe0
    4d60: add     x22, x20, #0x200
    4d64: str     x30, [sp, #32]
    4d68: mov     x21, x0
    4d6c: mov     x0, x22
    4d70: ldr     x1, [x2]
    4d74: str     x1, [sp, #808]
    4d78: mov     x1, #0x0
    4d7c: bl      2540 <mlkem_shake128_init>
    4d80: mov     x1, x19
    4d84: mov     x0, x22
    4d88: mov     x2, #0x22
    4d8c: bl      24d0 <mlkem_shake128_absorb_once>
    4d90: mov     x2, x22
    4d94: mov     x0, x20
    4d98: mov     x1, #0x3
    4d9c: bl      24e4 <mlkem_shake128_squeezeblocks>
    4da0: mov     x2, x20
    4da4: mov     x0, x21
    4da8: mov     w3, #0x1f8
    4dac: mov     w1, #0x0
    4db0: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4db4: cmp     w0, #0xff
    4db8: b.hi    4df0 <mlkem_poly_rej_uniform+0xb0>
    4dbc: mov     w19, w0
    4dc0: mov     x2, x22
    4dc4: mov     x0, x20
    4dc8: mov     x1, #0x1
    4dcc: bl      24e4 <mlkem_shake128_squeezeblocks>
    4dd0: mov     w1, w19
    4dd4: mov     x2, x20
    4dd8: mov     x0, x21
    4ddc: mov     w3, #0xa8
    4de0: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4de4: mov     w19, w0
    4de8: cmp     w0, #0xff
    4dec: b.ls    4dc0 <mlkem_poly_rej_uniform+0x80>
    4df0: mov     x0, x22
    4df4: bl      2544 <mlkem_shake128_release>
    4df8: mov     x0, x20
    4dfc: mov     x2, #0x1f8
    4e00: mov     w1, #0x0
    4e04: bl      840 <memset@plt>
    4e08: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    4e0c: ldr     x0, [x0, #4088]
    4e10: ldr     x2, [sp, #808]
    4e14: ldr     x1, [x0]
    4e18: subs    x2, x2, x1
    4e1c: mov     x1, #0x0
    4e20: b.ne    4e38 <mlkem_poly_rej_uniform+0xf8>
    4e24: ldp     x19, x20, [sp]
    4e28: ldp     x21, x22, [sp, #16]
    4e2c: ldr     x30, [sp, #32]
    4e30: add     sp, sp, #0x330
    4e34: ret
    4e38: bl      830 <__stack_chk_fail@plt>

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x4d40,0x4e3c; 0x840,0x850];;


(* ------------------------------------------------------------------------- *)
(* The bytes of SHAKE128 in blocks of 168, the rate, in terms of the         *)
(* absorbed state, as for mlkem_shake256 and mlkem_shake256x4.               *)
(* ------------------------------------------------------------------------- *)

let REJ_SPONGE = prove
 (`!(m:byte list) k n.
        n <= 168
        ==> num_of_bytelist(list_of_seq (\j. shake128 m (168 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 168
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                     (LENGTH m DIV 168))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 168 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                         2 EXP (8 * 168))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake128] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let REJ_XOF_BLOCKS = prove
 (`!(f:num->byte) n.
        num_of_bytelist(list_of_seq f (168 * n)) =
        nsum {i | i < n}
         (\i. 2 EXP (8 * 168 * i) *
              num_of_bytelist(list_of_seq (\j. f(168 * i + j)) 168))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; num_of_bytelist;
                NSUM_CLAUSES_NUMSEG_LT];
    ASM_REWRITE_TAC[ARITH_RULE `168 * SUC n = 168 * n + 168`;
                    NUM_OF_BYTELIST_LIST_OF_SEQ_ADD;
                    NSUM_CLAUSES_NUMSEG_LT]]);;

let REJ_SHAKE128_BLOCKS = prove
 (`!(m:byte list) b.
        num_of_bytelist(list_of_seq (shake128 m) (168 * b)) =
        nsum {i | i < b}
         (\i. 2 EXP (8 * 168 * i) *
              val(keccak_squeeze (i + 1)
                   (word_xor
                     (keccak_absorb 168
                       (num_of_bytelist m +
                        2 EXP (8 * LENGTH m) *
                        num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                       (LENGTH m DIV 168))
                     (word((num_of_bytelist m +
                            2 EXP (8 * LENGTH m) *
                            num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                           DIV 2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                           2 EXP (8 * 168))))) MOD 2 EXP (8 * 168))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_XOF_BLOCKS] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC REJ_SPONGE THEN
  REWRITE_TAC[LE_REFL]);;

let KECCAK_SQUEEZE_ADD = prove
 (`!m n (S:1600 word).
        keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let REJ_NSUM_1 = prove
 (`!f. nsum {j | j < 1} f = f 0`,
  REWRITE_TAC[num_CONV `1`; NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The 12-bit fields of the first 504 + 168 * j bytes, those of three blocks *)
(* and j more, and the samples from them as in the specification of          *)
(* mlk_rej_uniform_c, with REJ_SAMPLE as there.                              *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_OF_NUM_ADD = prove
 (`!m n x. wordlist_of_num (m + n) x:(N word)list =
           APPEND (wordlist_of_num m x)
                  (wordlist_of_num n (x DIV 2 EXP (dimindex(:N) * m)))`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; wordlist_of_num; APPEND; MULT_CLAUSES; EXP;
              DIV_1] THEN
  ASM_REWRITE_TAC[CONS_11; DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `d + d * m = d * SUC m`]);;

let REJ_WORDLIST_APPEND = prove
 (`!(f:num->byte) m n.
        8 * m = 12 * n
        ==> wordlist_of_num (n + 112)
             (num_of_bytelist(list_of_seq f (m + 168))):(12 word)list =
            APPEND (wordlist_of_num n (num_of_bytelist(list_of_seq f m)))
                   (wordlist_of_num 112
                     (num_of_bytelist(list_of_seq (\i. f(m + i)) 168)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; REJ_WORDLIST_OF_NUM_ADD] THEN
  REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) m` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM(NUM_REDUCE_CONV `2 EXP 8`);
              GSYM EXP_MULT] THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (f:num->byte) m)`,`x:num`) THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (\i. (f:num->byte)(m + i)) 168)`,
           `y:num`) THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [GSYM WORDLIST_OF_NUM_MOD] THEN
    REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

let REJ_FIELDS_SUC = prove
 (`!(f:num->byte) j.
        wordlist_of_num (336 + 112 * (j + 1))
         (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))):(12 word)list =
        APPEND
         (wordlist_of_num (336 + 112 * j)
           (num_of_bytelist(list_of_seq f (504 + 168 * j))))
         (wordlist_of_num 112
           (num_of_bytelist(list_of_seq (\i. f((504 + 168 * j) + i)) 168)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `504 + 168 * (j + 1) = (504 + 168 * j) + 168`;
              ARITH_RULE `336 + 112 * (j + 1) = (336 + 112 * j) + 112`] THEN
  MATCH_MP_TAC REJ_WORDLIST_APPEND THEN ARITH_TAC);;

let REJ_FIELDS_PREFIX = prove
 (`!(f:num->byte) j k.
        j <= k
        ==> ?t. wordlist_of_num (336 + 112 * k)
                 (num_of_bytelist(list_of_seq f (504 + 168 * k))):
                (12 word)list =
                APPEND (wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j)))) t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[]:(12 word)list` THEN REWRITE_TAC[APPEND_NIL];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[LE] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `[]:(12 word)list` THEN
      REWRITE_TAC[APPEND_NIL];
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:(12 word)list`) THEN
      REWRITE_TAC[ADD1; REJ_FIELDS_SUC] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]]]);;

let REJ_COUNT_MONO = prove
 (`!(f:num->byte) j k.
        j <= k
        ==> LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <=
            LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist(list_of_seq f (504 + 168 * k)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
             MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX)) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD]);;

let REJ_SAMPLE_FINAL = prove
 (`!(f:num->byte) j k.
        j <= k /\
        256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                       (num_of_bytelist(list_of_seq f (504 + 168 * j)))))
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                (num_of_bytelist(list_of_seq f (504 + 168 * k))))) =
            SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                (num_of_bytelist(list_of_seq f (504 + 168 * j)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
    MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX))
   ASSUME_TAC) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

let REJ_SAMPLE_SUC = prove
 (`!(f:num->byte) j.
        LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                 (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <= 256
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
                (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
            APPEND
             (SUB_LIST(0,256)
               (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                  (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
             (SUB_LIST(0,256 -
                       LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
               (REJ_SAMPLE(wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Lists of 12-bit fields and of 16-bit samples in memory.                   *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_FROM_BYTES = prove
 (`!a m n x s:armstate.
        12 * n = 8 * m /\ read (memory :> bytes(a,m)) s = x
        ==> wordlist_from_memory(a,n) s = (wordlist_of_num n x:(12 word)list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory; DIMINDEX_12] THEN
  SUBGOAL_THEN `(12 * n + 7) DIV 8 = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `7` THEN ASM_ARITH_TAC);;

let REJ_BYTES16_OF_WORDLIST = prove
 (`!a n (l:int16 list) s:armstate.
        wordlist_from_memory(a,n) s = l
        ==> read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `2 * n`; `l:int16 list`; `s:armstate`]
         WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_WORDLIST_OF_BYTES16 = prove
 (`!a (l:int16 list) s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l
        ==> wordlist_from_memory(a,LENGTH l) s = l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(l:int16 list)`; `2 * LENGTH(l:int16 list)`;
                 `l:int16 list`; `s:armstate`]
                WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_BYTES16_APPEND_N = prove
 (`!a n (l1:int16 list) (l2:int16 list) s:armstate.
        LENGTH l1 = n /\
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l1 /\
        read (memory :> bytes(word_add a (word(2 * n)),2 * LENGTH l2)) s =
        num_of_wordlist l2
        ==> read (memory :> bytes(a,2 * (n + LENGTH l2))) s =
            num_of_wordlist(APPEND l1 l2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> concl th = `LENGTH(l1:int16 list) = n`)) THEN
  REWRITE_TAC[GSYM LENGTH_APPEND] THEN
  MATCH_MP_TAC READ_BYTES16_APPEND THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The comparison of the number of samples with 255, as 32-bit words.        *)
(* ------------------------------------------------------------------------- *)

let REJ_HI_LEMMA = prove
 (`!c. c < 2 EXP 32
       ==> ((&c - &255:int =
             &(val(word_sub (word_zx (word c:int64):int32) (word 255))) /\
             ~(val(word_sub (word_zx (word c:int64):int32) (word 255)) =
               0)) <=>
            255 < c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> ((a /\ c) <=> b)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The buffer for three blocks, followed by the state, is aligned to 32      *)
(* bytes within the stack frame, so its address depends on whether the stack *)
(* pointer is a multiple of 32 or just of 16.                                *)
(* ------------------------------------------------------------------------- *)

let REJ_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let REJ_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 335)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 320 else 304))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let REJ_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 335))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REJ_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let REJ_BUF = `word_add (stackpointer:int64)
                (word(if aligned 32 stackpointer then 320 else 304))`;;

let REJ_CTX = `word_add (stackpointer:int64)
                (word((if aligned 32 stackpointer then 320 else 304) + 512))`;;

let REJ_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let REJ_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE REJ_ADDRESS_CONV th else th);;

let REJ_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1072):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `304 <= (if aligned 32 (stackpointer:int64) then 320 else 304) /\
    (if aligned 32 (stackpointer:int64) then 320 else 304) <= 320`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--22);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_shake128x4_release. The seed is 34 bytes at seed, given as a list   *)
(* of bytes inp. The loop sampling from one more block at a time stops when  *)
(* there are 256 samples, so the theorem has the hypothesis that there are   *)
(* at least 256 samples, values below 3329, among the 12-bit fields of the   *)
(* first 504 + 168 * k bytes of shake128 of the seed for some k, and the     *)
(* result is the first 256 of those samples. The proof uses the minimal such *)
(* k, k0, as the number of iterations of the loop. The stack is the 816      *)
(* bytes of the function and the 256 used by mlkem_shake128_absorb_once      *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_RELEASE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The fields and samples, and the blocks and samples from them ***)

let rej_fields j =
  vsubst [j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rej_count j = mk_comb(`LENGTH:(16 word)list->num`,
                          mk_comb(`REJ_SAMPLE`,rej_fields j));;

let rej_block i =
  vsubst [i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rej_l1 i =
  mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_fields i));;

let rej_l2 i =
  mk_comb(`SUB_LIST(0,256 - ci):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_block i));;

(*** The facts at the intermediate points, with the saved registers ***)

let REJ_FRAME =
 `read SP s = word_add stackpointer (word 256) /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1064))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X20 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304)) /\
  read X21 s = entry /\
  read X22 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 320 else 304) + 512))`;;

let REJ_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,REJ_FRAME));;

let REJ_A1 = REJ_AT
 `\s. read X0 s =
      word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)))))) /\
      read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
        (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 inp) 504))))))) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504))))) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 320 else 304) + 512)),
              200)) s =
      val(keccak_squeeze 3 (S0:1600 word))`;;

let REJ_INV = REJ_AT
 `\i s. read X19 s =
        word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
        read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
          (wordlist_of_num (336 + 112 * i)
            (num_of_bytelist(list_of_seq (shake128 inp)
                               (504 + 168 * i)))))))) s =
        num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
          (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 320 else 304) + 512)),
                200)) s =
        val(keccak_squeeze (3 + i) (S0:1600 word))`;;

let REJ_A2 = REJ_AT
 `\s. read (memory :> bytes(entry,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))`;;

(*** The absorbed state as S0, and the minimal number k0 of blocks ***)

let REJ_ABSORBED =
 `word_xor
   (keccak_absorb 168
     (num_of_bytelist inp +
      2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34))
     (34 DIV 168))
   (word((num_of_bytelist inp +
          2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34)) DIV
         2 EXP (8 * 168 * 34 DIV 168) MOD 2 EXP (8 * 168))):1600 word`;;

let REJ_ABSORBED_TAC =
  let len = ASSUME `LENGTH(inp:byte list) = 34` in
  ABBREV_TAC(mk_eq(`S0:1600 word`,REJ_ABSORBED)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SPONGE)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SHAKE128_BLOCKS));;

let REJ_MINIMAL_TAC =
  let p = mk_abs(`n:num`,
           mk_comb(mk_comb(`(<=):num->num->bool`,`256`),
             mk_comb(`LENGTH:(16 word)list->num`,
               mk_comb(`REJ_SAMPLE`,rej_fields `n:num`)))) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** Calls of mlk_rej_uniform_c and their results ***)

let REJ_INPUT0_TAC s =
  SUBGOAL_THEN
   (subst [REJ_BUF,`buf:int64`; s,`s:armstate`]
     `wordlist_from_memory(buf,336) s =
      (wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`] (ISPECL
   [`336`; `num_of_bytelist(list_of_seq (shake128 inp) 504)`]
   LENGTH_WORDLIST_OF_NUM));;

let REJ_BLOCK_TAC s =
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJ_BUF,`112`); s]),
          rej_block `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) then
        MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rej_block `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJ_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      STRIP_ASSUME_TAC(REWRITE_RULE[GSYM REJ_SAMPLE]
        (CONV_RULE(TOP_DEPTH_CONV let_CONV) th))
    else NO_TAC);;

let REJ_COMBINE_TAC =
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),`ci:num`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`entry:int64`; `ci:num`; rej_l1 `i:num`; rej_l2 `i:num`;
                 `s11:armstate`] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (let th = MP (REWRITE_RULE[ASSUME(mk_eq(rej_count `i:num`,`ci:num`))]
                (ISPECL [`shake128 inp`; `i:num`] REJ_SAMPLE_SUC))
               (ASSUME `ci <= 256`) in
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
   MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND;
    ASSUME(mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),
                 `ci:num`))] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

(*** The counter and the tests of whether there are 256 samples ***)

let REJ_C0 =
  `LENGTH(REJ_SAMPLE(wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list))`
and REJ_CN = mk_comb(`MIN 256`,rej_count `i + 1`);;

let REJ_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let REJ_HI_TAC c =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `2 EXP 32`) (fun bth ->
    let th = MP (SPEC c REJ_HI_LEMMA) bth in
    RULE_ASSUM_TAC(fun th' ->
      if is_eq(concl th') && is_cond(rand(concl th'))
      then REWRITE_RULE[th] th' else th')) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    ALL_TAC];;

let REJ_MIN_TAC =
  FIRST_ASSUM(fun th ->
    if is_binary "<" (concl th) && rand(concl th) = `256` &&
       can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE"
                               with _ -> false)) (lhand(concl th))
    then REWRITE_TAC[MATCH_MP (ARITH_RULE `x < 256 ==> MIN 256 x = x`) th]
    else NO_TAC);;

let REJ_LS_TAC =
  SUBGOAL_THEN (mk_eq(mk_binop `(<):num->num->bool` `255` REJ_CN,
                      `~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] THEN EQ_TAC THENL
     [DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC];;

(*** The parts of the proof ***)

let REJ_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`entry:int64`; `seed:int64`; `inp:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1072 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

let REJ_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (3--8) THEN
  REJ_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (9--16) THEN
  REJ_NORMALIZE_TAC THEN
  LOCAL_INIT_TAC [`read X0 s`; `pc:num`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (18--21) THEN
  LOCAL_ABSORB_TAC [`read X0 s`; `read X1 s`; `34`;
                    `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`;
                    `read X30 s`] 22 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (23--26) THEN
  LOCAL_SQUEEZE_TAC [`read X0 s`; `3`; `read X2 s`; `S0:1600 word`;
                     `pc:num`; `read SP s`; `read X30 s`] 27 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (28--32) THEN
  REJ_INPUT0_TAC `s32:armstate` THEN
  LOCAL_REJ_TAC [`read X0 s`; `0`; `read X2 s`; `504`;
     `wordlist_of_num 336 (num_of_bytelist(list_of_seq (shake128 inp) 504)):
      (12 word)list`; `pc:num`; `read X30 s`] 33 THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(entry,n) s = l:int16 list`) o
    concl)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJ_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJ_FINAL_TAC =
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),`256`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),
                        `256`)
    then GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]
    else NO_TAC) THEN
  MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[];;


(*** The loop body, from 3 + i blocks to 3 + i + 1 ***)

let REJ_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  REJ_MIN_TAC THEN ENSURES_INIT_TAC "s0" THEN

  (*** Squeezing one more block from the state ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--4) THEN
  KECCAK_STATE_AT_TAC REJ_CTX THEN
  LOCAL_SQUEEZE_TAC [`read X0 s`; `1`; `read X2 s`;
                     `keccak_squeeze (3 + i) (S0:1600 word)`;
                     `pc:num`; `read SP s`; `read X30 s`] 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN

  (*** Sampling from it after the ci samples so far ***)

  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (6--10) THEN
  REJ_ARGS_32_TAC `ci:num` THEN REJ_BLOCK_TAC `s10:armstate` THEN
  LOCAL_REJ_TAC [`read X0 s`; `ci:num`; `read X2 s`; `168`;
                 rej_block `i:num`; `pc:num`; `read X30 s`] 11 THEN
  REJ_COMBINE_TAC THEN

  (*** The test of whether there are 256 samples now ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (12--14) THEN
  REJ_ARGS_32_TAC REJ_CN THEN REJ_HI_TAC REJ_CN THEN REJ_LS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[];;

(*** The loop, if one more block is needed, from the first sampling ***)

let REJ_LOOP_TAC =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` REJ_C0 `256`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),REJ_C0))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + 0x4dc0` `pc + 0x4df0` REJ_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, after not branching round the loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
    REJ_ARGS_32_TAC REJ_C0 THEN REJ_HI_TAC REJ_C0 THEN
    SUBGOAL_THEN (mk_neg(mk_binop `(<):num->num->bool` `255` REJ_C0))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [FIRST_ASSUM(fun th ->
        if is_binary "<" (concl th) && lhand(concl th) = REJ_C0
        then MP_TAC th THEN ARITH_TAC else NO_TAC);
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (3--3) THEN
    REJ_ARGS_32_TAC REJ_C0 THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REJ_MIN_TAC THEN ASM_REWRITE_TAC[];

    REJ_BODY_TAC;

    REJ_EXIT_TAC];;

(*** Branching round the loop when no more blocks are needed ***)

let REJ_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

(*** Releasing the state, zeroing the buffer, the stack guard, return ***)

let REJ_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  LOCAL_RELEASE_TAC [`read X0 s`; `pc:num`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (4--7) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC 7 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (13--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (14--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJ_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!entry seed (inp:byte list) k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH inp = 34 /\
        256 <= LENGTH(FILTER (\x. val x < 3329)
                       (MAP (word_zx:12 word->16 word)
                         (wordlist_of_num (336 + 112 * k)
                           (num_of_bytelist
                             (list_of_seq (shake128 inp)
                                          (504 + 168 * k)))))) /\
        nonoverlapping (entry,512) (word_sub stackpointer (word 1072),1072) /\
        ALLPAIRS nonoverlapping
         [(entry,512); (word_sub stackpointer (word 1072),1072)]
         [(seed,34); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x4d40) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [entry; seed] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(entry,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp) (504 + 168 * k)))))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(entry,512);
                memory :> bytes(word_sub stackpointer (word 1072),1072)])`,
  REJ_INTRO_TAC THEN REJ_SETUP_TAC THEN REJ_ABSORBED_TAC THEN
  REJ_MINIMAL_TAC THEN

  (*** The first three blocks and the samples from them ***)

  ENSURES_SEQUENCE_TAC `pc + 0x4df0` REJ_A2 THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x4db4` REJ_A1 THEN CONJ_TAC THENL
     [REJ_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL [REJ_NOLOOP_TAC; REJ_LOOP_TAC]];
    REJ_PART3_TAC]);;
