(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-1024 encapsulation key. This is the code   *)
(* for mlkem1024_check_pk from mlkem-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which decodes   *)
(* the vector of the key from its first 1536 bytes into a buffer on the      *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result in constant time with the key, and zeroes the buffers. It is       *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x1010, using the theorems for                     *)
(* mlkem1024_polyvec_frombytes at 0x17b0, mlkem1024_polyvec_reduce at 0x1940 *)
(* and mlkem1024_polyvec_tobytes at 0x1770 in the image and assuming the     *)
(* contract for memset in utils/mlkem_native_libc.ml. There is no            *)
(* constant-time and memory safety proof yet.                                *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native_polyvec_frombytes_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_reduce_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_tobytes_k4_gcc12_O2.ml";;

(*** The code in the image, and the PLT stub for memset:

    1010: sub     sp, sp, #0xe40
    1014: mov     x1, x0
    1018: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    101c: ldr     x2, [x2, #4088]
    1020: stp     x19, x20, [sp]
    1024: add     x20, sp, #0x3f
    1028: and     x20, x20, #0xffffffffffffffe0
    102c: stp     x21, x30, [sp, #16]
    1030: mov     x19, x0
    1034: mov     x0, x20
    1038: ldr     x3, [x2]
    103c: str     x3, [sp, #3640]
    1040: mov     x3, #0x0
    1044: add     x21, x20, #0x800
    1048: bl      17b0 <mlkem1024_polyvec_frombytes>
    104c: mov     x0, x20
    1050: bl      1940 <mlkem1024_polyvec_reduce>
    1054: mov     x0, x21
    1058: mov     x1, x20
    105c: bl      1770 <mlkem1024_polyvec_tobytes>
    1060: movi    v2.4s, #0x0
    1064: mov     x0, x19
    1068: mov     x2, x21
    106c: add     x1, x20, #0xe00
    1070: mov     v3.16b, v2.16b
    1074: nop
    1078: ldr     q0, [x0], #16
    107c: ldr     q1, [x2], #16
    1080: eor     v0.16b, v0.16b, v1.16b
    1084: orr     v3.16b, v3.16b, v0.16b
    1088: eor     v2.16b, v2.16b, v0.16b
    108c: cmp     x1, x2
    1090: b.ne    1078 <mlkem1024_check_pk+0x68>
    1094: movi    v1.4s, #0x0
    1098: ext     v4.16b, v3.16b, v1.16b, #8
    109c: ext     v0.16b, v2.16b, v1.16b, #8
    10a0: orr     v3.16b, v4.16b, v3.16b
    10a4: eor     v2.16b, v0.16b, v2.16b
    10a8: ext     v4.16b, v3.16b, v1.16b, #4
    10ac: ext     v0.16b, v2.16b, v1.16b, #4
    10b0: orr     v4.16b, v4.16b, v3.16b
    10b4: eor     v0.16b, v0.16b, v2.16b
    10b8: ext     v3.16b, v4.16b, v1.16b, #2
    10bc: ext     v2.16b, v0.16b, v1.16b, #2
    10c0: orr     v3.16b, v3.16b, v4.16b
    10c4: eor     v2.16b, v2.16b, v0.16b
    10c8: ext     v0.16b, v3.16b, v1.16b, #1
    10cc: ext     v1.16b, v2.16b, v1.16b, #1
    10d0: orr     v0.16b, v0.16b, v3.16b
    10d4: eor     v1.16b, v1.16b, v2.16b
    10d8: umov    w0, v0.b[0]
    10dc: umov    w1, v1.b[0]
    10e0: neg     w0, w0
    10e4: eor     w0, w1, w0, asr #16
    10e8: cmp     w1, w0, uxtb
    10ec: mov     x2, #0x600
    10f0: mov     x0, x21
    10f4: mov     w1, #0x0
    10f8: mov     w19, #0xfffffffc
    10fc: csel    w19, wzr, w19, eq
    1100: bl      840 <memset@plt>
    1104: mov     x2, #0x800
    1108: mov     x0, x20
    110c: mov     w1, #0x0
    1110: bl      840 <memset@plt>
    1114: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    1118: ldr     x0, [x0, #4088]
    111c: ldr     x2, [sp, #3640]
    1120: ldr     x1, [x0]
    1124: subs    x2, x2, x1
    1128: mov     x1, #0x0
    112c: b.ne    1144 <mlkem1024_check_pk+0x134>
    1130: ldp     x21, x30, [sp, #16]
    1134: mov     w0, w19
    1138: ldp     x19, x20, [sp]
    113c: add     sp, sp, #0xe40
    1140: ret
    1144: bl      830 <__stack_chk_fail@plt>

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1010,0x1148; 0x840,0x850];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES16_LIST = prove
 (`!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let CHECKPK_IVAL_WORD = prove
 (`!f. f < 32768 ==> ival(word f:int16) = &f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 32768 ==> f < 65536`]);;

let CHECKPK_REDUCED = prove
 (`!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word f:int16) = &f` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECKPK_IVAL_WORD THEN UNDISCH_TAC `f < 2 EXP 12` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_REM]) THEN
  ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHECKPK_IVAL_WORD THEN
  MP_TAC(SPECL [`f:num`; `3329`] MOD_LT_EQ) THEN ARITH_TAC);;

let CHECKPK_LIST_PROPS = prove
 (`!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; VAL_WORD; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`(g:num->num) i`; `3329`] MOD_LT_EQ) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 3329 ==> x < 65536`] THEN ARITH_TAC);;

let CHECKPK_REENCODE = prove
 (`!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!x. word_zx(word(x MOD 3329):int16):12 word = word(x MOD 3329)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `x MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 65536`];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`; LENGTH_LIST_OF_SEQ]
     (ISPECL [`list_of_seq (\x. word((n DIV 2 EXP (12 * x)) MOD 2 EXP 12 MOD
                                     3329):12 word) l`; `i:num`]
             NUM_OF_WORDLIST_EL)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SPEC_TAC(`(n DIV 2 EXP (12 * i)) MOD 4096`,`d:num`) THEN GEN_TAC THEN
    MP_TAC(ARITH_RULE `d MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4096`] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`]
    (ISPECL [`l:num`; `n:num`]
      (INST_TYPE [`:12`,`:N`] NUM_OF_WORDLIST_OF_NUM_EQ_SELF))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th] THEN
                       ASSUME_TAC th) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_OF_NUM; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(ISPECL [`wordlist_of_num l n:(12 word)list`; `i:num`]
                EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time: the bytes of the key and of the       *)
(* encoding XORed together are ORed into one accumulator (and XORed into     *)
(* another), which is zero if and only if the prefixes so far are equal. The *)
(* loop test compares the pointers.                                          *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES128 = prove
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

let CHECKPK_MOD_STEP = prove
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

let CHECKPK_OR_STEP = prove
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

let CHECKPK4_TEST = prove
 (`!sp:int64 b i.
        b <= 80 /\ i < 96
        ==> (val(word_sub (word_add sp (word(b + 3584)))
                          (word_add (word_add sp (word((b + 2048) + 16 * i)))
                                    (word 16))) = 0 <=>
             ~(i + 1 < 96))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_sub (word_add a x) (word_add a y):int64 =
                         word_sub x y`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `b + 3584 < 2 EXP 64 /\ ((b + 2048) + 16 * i) + 16 < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* address depends on whether the stack pointer is a multiple of 32 or just  *)
(* of 16. The proof uses a variable boff for the offset of the first one.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_ALIGNED_16_32 = prove
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

let CHECKPK4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 95)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 64 else 80))`,
  REWRITE_TAC[CHECKPK_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let CHECKPK_BUFFER_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `word_and (word_add stackpointer (word n))
                                    (word m):int64`) (lhs(concl th))
    then SUBST_ALL_TAC th else NO_TAC);;

let CHECKPK_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_shake128x4_release. The first 1536 bytes of the key at pk are a     *)
(* number n, and the result is 0 if all the 1024 12-bit fields of n are      *)
(* below 3329, which is the modulus check of FIPS 203, and -4 otherwise. The *)
(* loop of the comparison has an invariant stating the value of the          *)
(* accumulator in terms of the prefixes of the key and of the encoding. The  *)
(* stack is the 3648 bytes of the function and the 32 used by the callees    *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the offset of the buffers as boff ***)

let CHECKPK4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `n:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3680 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3680):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK4_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `64 <= (if aligned 32 (stackpointer:int64) then 64 else 80) /\
    (if aligned 32 (stackpointer:int64) then 64 else 80) <= 80`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`if aligned 32 (stackpointer:int64) then 64 else 80`,
           `boff:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

(*** The facts in the loop, with the saved registers and the stack guard ***)

let CHECKPK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              1024`;;

let CHECKPK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                1024))`;;

let CHECKPK4_FRAME = vsubst [CHECKPK_M,`M:num`]
 `read SP s = word_add stackpointer (word 32) /\
  read (memory :> bytes64 (word_add stackpointer (word 32))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 40))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 48))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 56))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 3672))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X20 s = word_add stackpointer (word boff) /\
  read X21 s = word_add stackpointer (word(boff + 2048)) /\
  read (memory :> bytes(pk,1536)) s = n /\
  read (memory :> bytes(word_add stackpointer (word(boff + 2048)),1536)) s =
  M`;;

let CHECKPK4_INV = vsubst [CHECKPK_M,`M:num`]
 `\i s. read X0 s = word_add pk (word(16 * i)) /\
        read X2 s = word_add stackpointer (word((boff + 2048) + 16 * i)) /\
        read X1 s = word_add stackpointer (word(boff + 3584)) /\
        (read Q3 s = word 0 <=>
         n MOD 2 EXP (128 * i) = M MOD 2 EXP (128 * i))`;;

let CHECKPK4_INV_FRAME =
  let vs,bod = strip_abs CHECKPK4_INV in
  list_mk_abs(vs,mk_conj(bod,CHECKPK4_FRAME));;

(*** Decoding, reducing and encoding the vector, up to the loop ***)

let CHECKPK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add stackpointer (word boff),2048)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 1024)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2048 = 2 * 1024`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHECKPK4_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (4--7) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (8--15) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`; `pc:num`;
                       `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (17--18) THEN
  LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 19 THEN
  CHECKPK_LIST_TAC `s19:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (20--22) THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`; CHECKPK_L; `pc:num`;
                     `read SP s`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (24--29) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[];;

(*** The loop body, comparing 16 more bytes ***)

let CHECKPK_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 96 ==> 16 * i + 16 <= 1536`)
               (ASSUME `i < 96`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1536`) && vv = v ->
          let lth = SPECL [a; `1536`; `i:num`; v; s] CHECKPK_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let CHECKPK4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  CHECKPK_CHUNK_TAC `pk:int64` `n:num` THEN
  CHECKPK_CHUNK_TAC `word_add stackpointer (word(boff + 2048)):int64`
                    `mm:num` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`; `boff:num`; `i:num`] CHECKPK4_TEST)
       (CONJ (ASSUME `boff <= 80`) (ASSUME `i < 96`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[CHECKPK_OR_STEP; CHECKPK_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]];;

(*** The final result from the accumulators, the zeroing, the return ***)

let CHECKPK_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `1536`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECKPK4_DONE_TAC =
  SUBGOAL_THEN
   `(q3:int128 = word 0) <=>
    !i. i < 1024 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECKPK_BOUND `pk:int64` `s0:armstate`) THEN
    MP_TAC(CHECKPK_BOUND `word_add stackpointer (word(boff + 2048)):int64`
                         `s0:armstate`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 1536 = 128 * 96`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECKPK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECKPK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 1024 = 128 * 96`];
    ALL_TAC];;

let CHECKPK4_EXIT_TAC =
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN CHECKPK4_DONE_TAC THEN

  (*** The comparison of the hashes and the zeroing of the buffers ***)

  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--21) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (22--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC 28 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (34--37) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC 37 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 42 THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (43--43) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_EXEC (44--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!pk n guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (pk,1536) (word pc,0x6480) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 3680),3680)]
         [(pk,1536); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1010) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1536)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 1024
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 0 else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 3680),3680)])`,
  CHECKPK4_INTRO_TAC THEN
  ENSURES_WHILE_UP2_TAC `96` `pc + 0x1078` `pc + 0x1094`
   CHECKPK4_INV_FRAME THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CHECKPK4_PART1_TAC; CHECKPK4_BODY_TAC; CHECKPK4_EXIT_TAC]);;
