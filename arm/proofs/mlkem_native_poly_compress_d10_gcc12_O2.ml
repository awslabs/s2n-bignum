(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 10 bits per coefficient.                   *)
(* This is the code for mlkem_poly_compress_d10 from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), with a stack protector. It is verified in the    *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x1cd0, with the address of the stack guard in the global offset  *)
(* table at 0x1fff8.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    1cd0: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    1cd4: ldr     x3, [x3, #4088]
    1cd8: str     x30, [sp, #-32]!
    1cdc: mov     x8, #0xbc00
    1ce0: mov     x6, x1
    1ce4: add     x12, sp, #0x10
    1ce8: mov     x2, x0
    1cec: movk    x8, #0x9d7d, lsl #16
    1cf0: ldr     x0, [x3]
    1cf4: str     x0, [sp, #24]
    1cf8: mov     x0, #0x0
    1cfc: mov     x7, #0x100000000
    1d00: mov     w3, #0x4
    1d04: nop
    1d08: sub     w1, w3, #0x4
    1d0c: mov     x4, x12
    1d10: ldrsh   x0, [x6, w1, uxtw #1]
    1d14: add     w1, w1, #0x1
    1d18: madd    x0, x0, x8, x7
    1d1c: ubfx    x0, x0, #33, #10
    1d20: strh    w0, [x4], #2
    1d24: cmp     w3, w1
    1d28: b.ne    1d10 <mlkem_poly_compress_d10+0x40>
    1d2c: ldrh    w4, [sp, #18]
    1d30: add     w3, w3, #0x4
    1d34: ldrh    w1, [sp, #20]
    1d38: add     x2, x2, #0x5
    1d3c: ldrh    w0, [sp, #22]
    1d40: ldrh    w5, [sp, #16]
    1d44: lsl     w9, w4, #2
    1d48: lsl     w11, w1, #4
    1d4c: sturb   w5, [x2, #-5]
    1d50: lsl     w10, w0, #6
    1d54: orr     w4, w11, w4, lsr #6
    1d58: orr     w1, w10, w1, lsr #4
    1d5c: lsr     w0, w0, #2
    1d60: orr     w5, w9, w5, lsr #8
    1d64: sturb   w5, [x2, #-4]
    1d68: sturb   w4, [x2, #-3]
    1d6c: sturb   w1, [x2, #-2]
    1d70: sturb   w0, [x2, #-1]
    1d74: cmp     w3, #0x104
    1d78: b.ne    1d08 <mlkem_poly_compress_d10+0x38>
    1d7c: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    1d80: ldr     x0, [x0, #4088]
    1d84: ldr     x2, [sp, #24]
    1d88: ldr     x1, [x0]
    1d8c: subs    x2, x2, x1
    1d90: mov     x1, #0x0
    1d94: b.ne    1da0 <mlkem_poly_compress_d10+0xd0>
    1d98: ldr     x30, [sp], #32
    1d9c: ret
    1da0: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1cd0,0x1da4];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 10 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_ARITH = prove
 (`!v. v < 3329
       ==> (4294967296 + v * 2642263040) DIV 8589934592 =
           (2048 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2048 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(2048 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(2048 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 2642263040) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let WORD_SX_SMALL_64 = prove
 (`!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let COMPRESS_D10_FIELD = prove
 (`!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (4294967296 + val (word_sx y:int64) * 2642263040):int64)
                 (33,10):10 word) =
            ((2048 * val y + 3329) DIV 6658) MOD 1024`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL_64; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> 4294967296 + y * 2642263040 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D10_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of four 10-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5 = prove
 (`!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 256 = n DIV 4294967296`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 40` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16777216`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let VAL_JOIN_10X4 = prove
 (`!(u0:10 word) (u1:10 word) (u2:10 word) (u3:10 word).
     val(word_join u3 (word_join u2 (word_join u1 u0:20 word):30 word):
         40 word) =
     val u0 + 1024 * val u1 + 1048576 * val u2 + 1073741824 * val u3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:10 word`; `u1:10 word`; `u2:10 word`; `u3:10 word`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1024 * val(u1:10 word) + val(u0:10 word) < 1048576`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1073741824`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1073741824 * val(u3:10 word) +
                1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1099511627776`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ARITH_TAC]);;

(*** The stored bytes as parts of the 40-bit join of the four fields ***)

let d10_indices = map (fun k ->
  if k = 0 then `4 * i` else
  mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k)) (0--4);;

let d10_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (4294967296 + val (word_sx ((x:num->int16) j):int64) * 2642263040):
    int64`) (butlast d10_indices);;

let d10_join =
  vsubst (zip d10_xatoms [`w0:int64`; `w1:int64`; `w2:int64`; `w3:int64`])
  `word_join (word_subword (w3:int64) (33,10):10 word)
    (word_join (word_subword (w2:int64) (33,10):10 word)
      (word_join (word_subword (w1:int64) (33,10):10 word)
                 (word_subword (w0:int64) (33,10):10 word):20 word):30 word):
    40 word`;;

let D10_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (5 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `5 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d10_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d10_xatoms in
    let eq = subst (zip gvs d10_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip d10_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "D10_PACK_TAC");;

(* ------------------------------------------------------------------------- *)
(* The loops. The inner one, unrolled in the simulation, computes four       *)
(* 10-bit values into a temporary array on the stack; X1 is the index of the *)
(* coefficient, which is tidied up before it is used as a register offset.   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_INDEX_TAC k =
  let jt = el k d10_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X1 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC]
    else failwith "COMPRESS_D10_INDEX_TAC");;

let COMPRESS_D10_UXTW_TAC k =
  let jt = el k d10_indices in
  let zt = mk_comb(`word_zx:int32->int64`,
                   mk_comb(`word_zx:int64->int32`,
                           mk_comb(`word:num->int64`,jt))) in
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,zt),jt)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REWRITE_TAC[];
    ALL_TAC];;

let COMPRESS_D10_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
  COMPRESS_D10_INDEX_TAC 0 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--2) THEN
  MAP_EVERY (fun k ->
    COMPRESS_D10_UXTW_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     ((3 + 7 * k)--(4 + 7 * k)) THEN
    COMPRESS_D10_INDEX_TAC (k + 1) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     ((5 + 7 * k)--(8 + 7 * k)) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     ((9 + 7 * k)--(9 + 7 * k))) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (31--48);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 10 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 1024 * x / 3329, rounding up on ties, modulo 1024, i.e.                   *)
(* ((2048 * x + 3329) DIV 6658) MOD 1024, and as for mlkem_encode 10 the     *)
(* 10-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329). The stack guard is handled  *)
(* as for mlkem_poly_compress_d4.                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,320); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,320); (word_sub stackpointer (word 32),32)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1cd0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** The outer loop, over groups of 4 coefficients ***)

  ENSURES_WHILE_UP_TAC `64` `pc + 0x1d08` `pc + 0x1d74`
   `\i s. read X2 s = word_add r (word(5 * i)) /\
          read X3 s = word(4 * i + 4) /\
          read X6 s = a /\
          read X7 s = word 4294967296 /\
          read X8 s = word 2642263040 /\
          read X12 s = word_add stackpointer (word 16) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 4 * i}
                (\j. ((2048 * val(x j) + 3329) DIV 6658) MOD 1024 *
                     2 EXP (10 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for four coefficients and five bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 64` THEN ARITH_TAC; DISCH_TAC])
     (butlast d10_indices) THEN
    COMPRESS_D10_BODY_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `4 * (i + 1) + 4 = (4 * i + 4) + 4`] THEN
      WORD_SMALL_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** The new bytes as parts of the join of the 10-bit fields ***)

    MAP_EVERY D10_PACK_TAC (0--4) THEN
    REWRITE_TAC[ARITH_RULE
     `5 * (i + 1) = ((((5 * i + 1) + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(5 * i + 1) + 1 = 5 * i + 2`;
                ARITH_RULE `(5 * i + 2) + 1 = 5 * i + 3`;
                ARITH_RULE `(5 * i + 3) + 1 = 5 * i + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INST_TYPE [`:40`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1] THEN
    MP_TAC(SPEC (mk_comb(`val:40 word->num`,d10_join)) BYTES_OF_NUM_5) THEN
    MP_TAC(ISPEC d10_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_10X4] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D10_FIELD) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) (butlast d10_indices) THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; NSUM_LT_ADD] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUM_RING;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit, the check of the stack guard and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,320; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,320; word_sub stackpointer (word 32),32]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x1cd0) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 32)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,320; word_sub stackpointer (word 32),32;
                      word(pc + 0x1fff8),8; guard,8]
                     [r,320; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,320);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a r guard pc stackpointer returnaddress i))
          (f_ev_prol a r guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + 0x1d08` `pc + 0x1d7c`
    `\i s. read X2 s = word_add r (word(5 * i)) /\
           read X3 s = word(4 * i + 4) /\
           read X6 s = a /\
           read X12 s = word_add stackpointer (word 16) /\
           read SP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 24))) s =
           canary /\
           read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
           guard /\
           read (memory :> bytes64 guard) s = canary` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  COMPRESS_D10_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (49--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub
           (word_zx (word_zx (word_add (word_zx (word (4 * i + 4):int64):int32)
                                       (word 4)):int64):int32)
           (word 260):int32) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 4 * i + 4 < 18446744073709551616 /\
                 4 * i + 4 < 4294967296 /\
                 (4 * i + 4) + 4 < 4294967296 /\
                 (4 * i + 4) + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) + 4 = (4 * i + 4) + 4`] THEN
    WORD_SMALL_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
