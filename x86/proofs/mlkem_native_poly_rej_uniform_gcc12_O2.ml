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
(* where it is at address 0x62f0, using the theorems for mlkem_shake128_init *)
(* at 0x3430, mlkem_shake128_absorb_once at 0x33c0,                          *)
(* mlkem_shake128_squeezeblocks at 0x33e0, mlkem_shake128_release at 0x3440  *)
(* and mlk_rej_uniform_c at 0x6040 in the image.                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_rej_uniform_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128_init_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128_absorb_once_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128_squeezeblocks_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128_release_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    62f0: push   rbp
    62f1: mov    rbp,rsp
    62f4: push   r14
    62f6: mov    r14,rdi
    62f9: push   r13
    62fb: push   r12
    62fd: push   rbx
    62fe: mov    rbx,rsi
    6301: and    rsp,0xffffffffffffffe0
    6305: sub    rsp,0x2e0
    630c: mov    r13,rsp
    630f: lea    r12,[rsp+0xe0]
    6317: mov    rdi,r13
    631a: call   3430 <mlkem_shake128_init>
    631f: mov    edx,0x22
    6324: mov    rsi,rbx
    6327: mov    rdi,r13
    632a: call   33c0 <mlkem_shake128_absorb_once>
    632f: mov    rdx,r13
    6332: mov    esi,0x3
    6337: mov    rdi,r12
    633a: call   33e0 <mlkem_shake128_squeezeblocks>
    633f: xor    esi,esi
    6341: mov    ecx,0x1f8
    6346: mov    rdx,r12
    6349: mov    rdi,r14
    634c: call   6040 <mlk_rej_uniform_c.constprop.0>
    6351: cmp    eax,0xff
    6356: ja     638b <mlkem_poly_rej_uniform+0x9b>
    6358: mov    ebx,eax
    635a: nop    WORD PTR [rax+rax*1+0x0]
    6360: mov    rdx,r13
    6363: mov    esi,0x1
    6368: mov    rdi,r12
    636b: call   33e0 <mlkem_shake128_squeezeblocks>
    6370: mov    esi,ebx
    6372: mov    ecx,0xa8
    6377: mov    rdx,r12
    637a: mov    rdi,r14
    637d: call   6040 <mlk_rej_uniform_c.constprop.0>
    6382: mov    ebx,eax
    6384: cmp    eax,0xff
    6389: jbe    6360 <mlkem_poly_rej_uniform+0x70>
    638b: mov    rdi,r13
    638e: call   3440 <mlkem_shake128_release>
    6393: xor    eax,eax
    6395: mov    rdi,r12
    6398: mov    ecx,0x3f
    639d: rep    stos QWORD PTR es:[rdi],rax
    63a0: lea    rsp,[rbp-0x20]
    63a4: pop    rbx
    63a5: pop    r12
    63a7: pop    r13
    63a9: pop    r14
    63ab: pop    rbp
    63ac: ret
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x62f0,0x63ad];;

(* ------------------------------------------------------------------------- *)
(* The bytes of SHAKE128 in blocks of 168, the rate, in terms of the         *)
(* absorbed state, as on AArch64.                                            *)
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
 (`!a m n x s:x86state.
        12 * n = 8 * m /\ read (memory :> bytes(a,m)) s = x
        ==> wordlist_from_memory(a,n) s = (wordlist_of_num n x:(12 word)list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory; DIMINDEX_12] THEN
  SUBGOAL_THEN `(12 * n + 7) DIV 8 = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `7` THEN ASM_ARITH_TAC);;

let REJ_BYTES16_OF_WORDLIST = prove
 (`!a n (l:int16 list) s:x86state.
        wordlist_from_memory(a,n) s = l
        ==> read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `2 * n`; `l:int16 list`; `s:x86state`]
         WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_WORDLIST_OF_BYTES16 = prove
 (`!a (l:int16 list) s:x86state.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l
        ==> wordlist_from_memory(a,LENGTH l) s = l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(l:int16 list)`; `2 * LENGTH(l:int16 list)`;
                 `l:int16 list`; `s:x86state`]
                WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_BYTES16_APPEND_N = prove
 (`!a n (l1:int16 list) (l2:int16 list) s:x86state.
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
(* The comparison of the number of samples with 255, as 32-bit words, for a  *)
(* branch on both CF and ZF (ja) or on either (jbe, setbe).                  *)
(* ------------------------------------------------------------------------- *)

let REJ_HI_LEMMA = prove
 (`!c. c < 2 EXP 32
       ==> ((&(val(word_zx (word c:int64):int32)) - &255:int =
             &(val(word_sub (word_zx (word c:int64):int32) (word 255))) /\
             ~(val(word_sub (word_zx (word c:int64):int32) (word 255)) =
               0) <=>
             255 < c) /\
           ((~(&(val(word_zx (word c:int64):int32)) - &255:int =
               &(val(word_sub (word_zx (word c:int64):int32) (word 255)))) \/
             val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0) <=>
            ~(255 < c)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT
   `(p /\ ~q <=> r) ==> (p /\ ~q <=> r) /\ (~p \/ q <=> ~r)`) THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> ((a /\ c) <=> b)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The state of 224 bytes and the buffer for three blocks after it are       *)
(* aligned to 32 bytes within the stack frame, by AND with -32 after the     *)
(* pushes, so the state is at stackpointer + (360 - k) for k =               *)
(* val(stackpointer + 1096) MOD 32, where stackpointer is the bottom of the  *)
(* 1136 bytes of the stack below the return address, as for mlkem_shake256.  *)
(* The addresses below it, for the calls, and that of the buffer are put in  *)
(* the same form by REJ_NORMALIZE_TAC.                                       *)
(* ------------------------------------------------------------------------- *)

let REJ_STATE_ADDRESS = prove
 (`!a:int64.
        word_sub (word_and (word_add a (word 1096))
                           (word 18446744073709551584))
                 (word 736) =
        word_add a (word(360 - val(word_add a (word 1096)) MOD 32))`,
  let lemma = prove
   (`!x:int64. word_and x (word 18446744073709551584) =
               word_sub x (word(val x MOD 32))`,
    GEN_TAC THEN
    SUBGOAL_THEN `val(x:int64) MOD 32 = val(word_and x (word 31):int64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
      REWRITE_TAC[WORD_VAL] THEN
      W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]) in
  GEN_TAC THEN REWRITE_TAC[lemma] THEN
  MP_TAC(SPECL [`val(word_add a (word 1096):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word 1096):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`360`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let REJ_CTX =
 `word_add (stackpointer:int64)
           (word(360 - val(word_add stackpointer (word 1096)) MOD 32))`;;

let REJ_BUF =
 `word_add (stackpointer:int64)
           (word(584 - val(word_add stackpointer (word 1096)) MOD 32))`;;

let REJ_NORMALIZE_TAC =
  let k = `val(word_add (stackpointer:int64) (word 1096)) MOD 32` in
  let kth = REWRITE_RULE[ARITH_EQ]
   (SPECL [`val(word_add (stackpointer:int64) (word 1096))`; `32`]
          MOD_LT_EQ) in
  let mk t = subst [k,`k:num`] t in
  let sub2 a = INST [mk_small_numeral a,`x:num`; `k:num`,`y:num`]
                    (INST_TYPE [`:64`,`:N`] WORD_SUB2) in
  let n t = mk_small_numeral t in
  let prv tm a b =
    prove(mk tm,
      MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN REPEAT STRIP_TAC THEN
      MP_TAC(sub2 a) THEN MP_TAC(sub2 b) THEN
      REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
      CONV_TAC WORD_RULE) in
  let sub_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a - d),`e:num`]
         `word_sub (word_add stackpointer (word (a - k))) (word d):int64 =
          word_add stackpointer (word (e - k))`) a (a - d)
  and add_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a + d),`e:num`]
         `word_add (word_add stackpointer (word (a - k))) (word d):int64 =
          word_add stackpointer (word (e - k))`) a (a + d)
  and wsub_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a - d),`e:num`]
         `word_sub (word (a - k)) (word d):int64 = word (e - k)`) a (a - d)
  and wadd_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a + d),`e:num`]
         `word_add (word (a - k)) (word d):int64 = word (e - k)`) a (a + d) in
  let arith = prove(mk `352 - k + 8 = 360 - k`,
    MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN ARITH_TAC) in
  let ths = [sub_lemma 360 8; sub_lemma 352 320; sub_lemma 352 288;
             add_lemma 352 8; add_lemma 360 224;
             wsub_lemma 360 8; wsub_lemma 352 320; wsub_lemma 352 288;
             wadd_lemma 352 8; wadd_lemma 360 224; arith] in
  RULE_ASSUM_TAC(REWRITE_RULE ths);;

let REJ_SETUP_TAC =
  SUBGOAL_THEN
   `val(word_add (stackpointer:int64) (word 1096)) MOD 32 < 32 /\
    329 <= 360 - val(word_add (stackpointer:int64) (word 1096)) MOD 32 /\
    360 - val(word_add (stackpointer:int64) (word 1096)) MOD 32 <= 360`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`val(word_add (stackpointer:int64) (word 1096))`; `32`]
      MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 34 bytes at seed, given as a list of bytes *)
(* inp. The loop sampling from one more block at a time stops when there are *)
(* 256 samples, so the theorem has the hypothesis that there are at least    *)
(* 256 samples, values below 3329, among the 12-bit fields of the first 504  *)
(* + 168 * k bytes of shake128 of the seed for some k, and the result is the *)
(* first 256 of those samples. The proof uses the minimal such k, k0, as the *)
(* number of iterations of the loop. The state is released and the buffer    *)
(* zeroed at the end with REP STOSQ, so the specification assumes that DF is *)
(* clear, as the ABI requires. The stack is the 1136 bytes below the return  *)
(* address, for the frame of the function, of at most 807 bytes, and the 328 *)
(* used by mlkem_shake128_absorb_once below it.                              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_RELEASE_TAC =
  X86_SUBROUTINE_SIM_TAC
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
 `read RSP s =
  word_add stackpointer
   (word(360 - val(word_add stackpointer (word 1096)) MOD 32)) /\
  read RBP s = word_add stackpointer (word 1128) /\
  read (memory :> bytes64 (word_add stackpointer (word 1096))) s =
  rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1104))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1112))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1120))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1128))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1136))) s =
  returnaddress /\
  read R12 s =
  word_add stackpointer
   (word(584 - val(word_add stackpointer (word 1096)) MOD 32)) /\
  read R13 s =
  word_add stackpointer
   (word(360 - val(word_add stackpointer (word 1096)) MOD 32)) /\
  read R14 s = entry /\
  (read DF s <=> false)`;;

let REJ_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,REJ_FRAME));;

let REJ_A1 = REJ_AT
 `\s. read RAX s =
      word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)))))) /\
      read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
        (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 inp) 504))))))) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504))))) /\
      read (memory :> bytes(word_add stackpointer
              (word(360 - val(word_add stackpointer (word 1096)) MOD 32)),
              200)) s =
      val(keccak_squeeze 3 (S0:1600 word))`;;

let REJ_INV = REJ_AT
 `\i s. read RBX s =
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
                (word(360 - val(word_add stackpointer (word 1096)) MOD 32)),
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
   (subst [REJ_BUF,`buf:int64`; s,`s:x86state`]
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
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->x86state->
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

let REJ_COMBINE_TAC sn =
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
                 sn] REJ_BYTES16_APPEND_N) THEN
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
   [`entry:int64`; `seed:int64`; `inp:byte list`; `k:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1136 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let REJ_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_STATE_ADDRESS]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (11--14) THEN
  REJ_NORMALIZE_TAC THEN
  LOCAL_INIT_TAC [`read RDI s`; `pc:num`; `read RSP s`;
                  `read (memory :> bytes64(read RSP s)) s`] 15 THEN
  REJ_NORMALIZE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (16--19) THEN
  REJ_NORMALIZE_TAC THEN
  LOCAL_ABSORB_TAC [`read RDI s`; `read RSI s`; `34`;
                    `num_of_bytelist(inp:byte list)`; `pc:num`;
                    `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
    20 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (21--24) THEN
  REJ_NORMALIZE_TAC THEN KECCAK_STATE_AT_TAC REJ_CTX THEN
  LOCAL_SQUEEZE_TAC [`read RDI s`; `3`; `read RDX s`; `S0:1600 word`;
                     `pc:num`; `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 25 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (26--30) THEN
  REJ_NORMALIZE_TAC THEN REJ_INPUT0_TAC `s30:x86state` THEN
  LOCAL_REJ_TAC [`read RDI s`; `0`; `read RDX s`; `504`;
     `wordlist_of_num 336 (num_of_bytelist(list_of_seq (shake128 inp) 504)):
      (12 word)list`; `pc:num`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`] 31 THEN
  REJ_NORMALIZE_TAC THEN REJ_POST_TAC THEN
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

  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--4) THEN
  REJ_NORMALIZE_TAC THEN KECCAK_STATE_AT_TAC REJ_CTX THEN
  LOCAL_SQUEEZE_TAC [`read RDI s`; `1`; `read RDX s`;
                     `keccak_squeeze (3 + i) (S0:1600 word)`;
                     `pc:num`; `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 5 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN

  (*** Sampling from it after the ci samples so far ***)

  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (6--10) THEN
  REJ_NORMALIZE_TAC THEN REJ_ARGS_32_TAC `ci:num` THEN
  REJ_BLOCK_TAC `s10:x86state` THEN
  LOCAL_REJ_TAC [`read RDI s`; `ci:num`; `read RDX s`; `168`;
                 rej_block `i:num`; `pc:num`; `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 11 THEN
  REJ_NORMALIZE_TAC THEN REJ_COMBINE_TAC `s11:x86state` THEN

  (*** The test of whether there are 256 samples now ***)

  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (12--14) THEN
  REJ_HI_TAC REJ_CN THEN REJ_ARGS_32_TAC REJ_CN THEN REJ_LS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[];;

(*** The loop, if one more block is needed, from the first sampling ***)

let REJ_LOOP_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  REJ_HI_TAC REJ_C0 THEN
  SUBGOAL_THEN (mk_neg(mk_binop `(<):num->num->bool` `255` REJ_C0))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = REJ_C0
      then MP_TAC th THEN ARITH_TAC else NO_TAC);
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (3--4) THEN
  REJ_ARGS_32_TAC REJ_C0;;

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
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + 0x6360` `pc + 0x638b` REJ_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, after not branching round the loop ***)

    REJ_LOOP_INIT_TAC THEN
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
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

(*** Releasing the state, zeroing the buffer and the return ***)

let REJ_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  REJ_NORMALIZE_TAC THEN
  LOCAL_RELEASE_TAC [`read RDI s`; `pc:num`; `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 3 THEN
  REJ_NORMALIZE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (4--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJ_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!entry seed (inp:byte list) k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH inp = 34 /\
        256 <= LENGTH(FILTER (\x. val x < 3329)
                       (MAP (word_zx:12 word->16 word)
                         (wordlist_of_num (336 + 112 * k)
                           (num_of_bytelist
                             (list_of_seq (shake128 inp)
                                          (504 + 168 * k)))))) /\
        nonoverlapping (entry,512) (word_sub stackpointer (word 1136),1144) /\
        ALLPAIRS nonoverlapping
         [(entry,512); (word_sub stackpointer (word 1136),1144)]
         [(seed,34); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x62f0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [entry; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(entry,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp) (504 + 168 * k)))))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(entry,512);
                memory :> bytes(word_sub stackpointer (word 1136),1136)])`,
  REJ_INTRO_TAC THEN REJ_SETUP_TAC THEN REJ_ABSORBED_TAC THEN
  REJ_MINIMAL_TAC THEN

  (*** The first three blocks and the samples from them ***)

  ENSURES_SEQUENCE_TAC `pc + 0x638b` REJ_A2 THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x6351` REJ_A1 THEN CONJ_TAC THENL
     [REJ_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL [REJ_NOLOOP_TAC; REJ_LOOP_TAC]];
    REJ_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on the seed, which is public, through the samples and the   *)
(* number of iterations of the loop, the least k for which there are 256     *)
(* samples, and the hypothesis about the samples is still needed for the     *)
(* loop to terminate. The events are given by a template with the parts      *)
(* before, in and after the loop, and the proof uses the combined theorems   *)
(* for the hash functions and mlk_rej_uniform_c, with the facts of the       *)
(* correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

(*** Constant-time and memory safety ***)

let PREJ_SAFE_TEMPLATE =
 `\(entry:int64) (seed:int64) (inp:byte list) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND (f_ev_p3 entry seed inp pc stackpointer returnaddress)
    (APPEND
      (if (minimal n.
             256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * n)
                     (num_of_bytelist
                       (list_of_seq (shake128 inp) (504 + 168 * n)))))) = 0
       then f_ev_skip entry seed inp pc stackpointer returnaddress
       else
        APPEND
         (f_ev_exit entry seed inp pc stackpointer returnaddress)
         (APPEND
           (ENUMERATEL
             (minimal n.
                256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * n)
                        (num_of_bytelist
                          (list_of_seq (shake128 inp) (504 + 168 * n))))))
             (\i. f_ev_loop entry seed inp pc stackpointer returnaddress i))
           (f_ev_enter entry seed inp pc stackpointer returnaddress)))
      (f_ev_p1 entry seed inp pc stackpointer returnaddress))
   :(uarch_event)list`;;

let PREJ_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_RELEASE" THEN
  CONCRETIZE_F_EVENTS_TAC PREJ_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REJ_INTRO_TAC THEN REJ_SETUP_TAC THEN REJ_ABSORBED_TAC THEN
  REJ_MINIMAL_TAC;;

let PREJ_ALLOWED =
  [`pc:num`; `entry:int64`; `seed:int64`; `inp:byte list`;
   `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `f_ev_loop:int64->int64->byte list->num->int64->int64->num->
              (uarch_event)list`];;

let PREJ_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref PREJ_ALLOWED); LABEL_TAC name safety_th]);;

let PREJ_SAFE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

let PREJ_SAFE_PART1_TAC =
  PREJ_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_STATE_ADDRESS]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (11--14) THEN
  REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_INIT"
   [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 15 THEN
  REJ_NORMALIZE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (16--19) THEN
  REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `34`;
    `num_of_bytelist(inp:byte list)`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 20 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (21--24) THEN
  REJ_NORMALIZE_TAC THEN KECCAK_STATE_AT_TAC REJ_CTX THEN
  PREJ_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read RDI s`; `3`; `read RDX s`; `S0:1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 25 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (26--30) THEN
  REJ_NORMALIZE_TAC THEN REJ_INPUT0_TAC `s30:x86state` THEN
  PREJ_SAFE_CALL_TAC "H_REJ"
   [`e:(uarch_event)list`; `read RDI s`; `0`; `read RDX s`; `504`;
    `wordlist_of_num 336 (num_of_bytelist(list_of_seq (shake128 inp) 504)):
     (12 word)list`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 31 THEN
  REJ_NORMALIZE_TAC THEN REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(entry,n) s = l:int16 list`) o
    concl)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ_SAFE_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  PREJ_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  REJ_MIN_TAC THEN PREJ_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--4) THEN
  REJ_NORMALIZE_TAC THEN KECCAK_STATE_AT_TAC REJ_CTX THEN
  PREJ_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read RDI s`; `1`; `read RDX s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 5 THEN
  REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (6--10) THEN
  REJ_NORMALIZE_TAC THEN REJ_ARGS_32_TAC `ci:num` THEN
  REJ_BLOCK_TAC `s10:x86state` THEN
  PREJ_SAFE_CALL_TAC "H_REJ"
   [`e:(uarch_event)list`; `read RDI s`; `ci:num`; `read RDX s`; `168`;
    rej_block `i:num`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 11 THEN
  REJ_NORMALIZE_TAC THEN REJ_COMBINE_TAC `s11:x86state` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (12--14) THEN
  REJ_HI_TAC REJ_CN THEN REJ_ARGS_32_TAC REJ_CN THEN REJ_LS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `ci:num`))) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ_SAFE_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
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
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + 0x6360` `pc + 0x638b`
    REJ_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    PREJ_SAFE_INIT_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
    REJ_HI_TAC REJ_C0 THEN
    SUBGOAL_THEN (mk_neg(mk_binop `(<):num->num->bool` `255` REJ_C0))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [FIRST_ASSUM(fun th ->
        if is_binary "<" (concl th) && lhand(concl th) = REJ_C0
        then MP_TAC th THEN ARITH_TAC else NO_TAC);
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (3--4) THEN
    REJ_ARGS_32_TAC REJ_C0 THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REJ_MIN_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    PREJ_SAFE_BODY_TAC;

    REWRITE_TAC[] THEN PREJ_SAFE_INIT_TAC THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PREJ_SAFE_PART3_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  PREJ_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (1--2) THEN
  REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_RELEASE"
   [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 3 THEN
  REJ_NORMALIZE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_EXEC (4--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e entry seed (inp:byte list) k pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ LENGTH inp = 34 /\
       256 <= LENGTH(FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word)
                        (wordlist_of_num (336 + 112 * k)
                          (num_of_bytelist
                            (list_of_seq (shake128 inp)
                                         (504 + 168 * k)))))) /\
       nonoverlapping (entry,512) (word_sub stackpointer (word 1136),1144) /\
       ALLPAIRS nonoverlapping
        [(entry,512); (word_sub stackpointer (word 1136),1144)]
        [(seed,34); (word pc,0x82a0)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x62f0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [entry; seed] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(seed,34)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events entry seed inp pc
                           (word_sub stackpointer (word 1136)) returnaddress /\
                    memaccess_inbounds e2
                     [seed,34; entry,512;
                      word_sub stackpointer (word 1136),1144;
                      word(pc + 0x80c0),192]
                     [entry,512; word_sub stackpointer (word 1136),1136]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(entry,512);
               memory :> bytes(word_sub stackpointer (word 1136),1136)])`,
  PREJ_SAFE_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x638b` REJ_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6351` REJ_A1 THEN CONJ_TAC THENL
     [PREJ_SAFE_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [PREJ_SAFE_NOLOOP_TAC; PREJ_SAFE_LOOP_TAC]];
    PREJ_SAFE_PART3_TAC]);;
