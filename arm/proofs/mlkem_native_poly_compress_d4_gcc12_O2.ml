(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient.                    *)
(* This is the code for mlkem_poly_compress_d4 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), with a stack protector. It is verified in the    *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x1bf0, with the address of the stack guard in the global offset  *)
(* table at 0x1fff8.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    1bf0: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    1bf4: ldr     x2, [x2, #4088]
    1bf8: str     x30, [sp, #-32]!
    1bfc: mov     x10, x1
    1c00: mov     w12, #0xafb0
    1c04: ldr     x1, [x2]
    1c08: str     x1, [sp, #24]
    1c0c: mov     x1, #0x0
    1c10: add     x13, sp, #0x10
    1c14: movk    w12, #0x13, lsl #16
    1c18: mov     w11, #0x8000000
    1c1c: nop
    1c20: sub     w3, w1, #0x1
    1c24: mov     x2, #0x1
    1c28: str     xzr, [sp, #16]
    1c2c: nop
    1c30: add     w4, w3, w2
    1c34: add     x5, x13, x2
    1c38: add     x2, x2, #0x1
    1c3c: ldrsh   w4, [x10, x4, lsl #1]
    1c40: madd    w4, w4, w12, w11
    1c44: lsr     w4, w4, #28
    1c48: sturb   w4, [x5, #-1]
    1c4c: cmp     x2, #0x9
    1c50: b.ne    1c30 <mlkem_poly_compress_d4+0x40>
    1c54: ldrb    w9, [sp, #16]
    1c58: add     w1, w1, #0x8
    1c5c: ldrb    w8, [sp, #18]
    1c60: add     x0, x0, #0x4
    1c64: ldrb    w7, [sp, #20]
    1c68: ldrb    w6, [sp, #22]
    1c6c: ldrb    w5, [sp, #17]
    1c70: ldrb    w4, [sp, #19]
    1c74: ldrb    w3, [sp, #21]
    1c78: ldrb    w2, [sp, #23]
    1c7c: orr     w5, w9, w5, lsl #4
    1c80: orr     w4, w8, w4, lsl #4
    1c84: sturb   w5, [x0, #-4]
    1c88: orr     w3, w7, w3, lsl #4
    1c8c: sturb   w4, [x0, #-3]
    1c90: orr     w2, w6, w2, lsl #4
    1c94: sturb   w3, [x0, #-2]
    1c98: sturb   w2, [x0, #-1]
    1c9c: cmp     w1, #0x100
    1ca0: b.ne    1c20 <mlkem_poly_compress_d4+0x30>
    1ca4: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    1ca8: ldr     x0, [x0, #4088]
    1cac: ldr     x2, [sp, #24]
    1cb0: ldr     x1, [x0]
    1cb4: subs    x2, x2, x1
    1cb8: mov     x1, #0x0
    1cbc: b.ne    1cc8 <mlkem_poly_compress_d4+0xd8>
    1cc0: ldr     x30, [sp], #32
    1cc4: ret
    1cc8: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1bf0,0x1ccc];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed, and the packing  *)
(* of two such values into a byte.                                           *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_ARITH = prove
 (`!v. v < 3329
       ==> (134217728 + v * 1290160) DIV 268435456 =
           (32 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`32 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(32 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(32 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `32 * v + 3329 = q * 6658 + r` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(134217728 + v * 1290160) - q * 268435456` THEN
  ASM_ARITH_TAC);;

let COMPRESS_D4_NIBBLE = prove
 (`!y:int16.
        val y < 3329
        ==> word_ushr
             (word_zx (word_zx
               (word (134217728 +
                      val (word_zx (word_zx (word_sx y:int32):int64):int32) *
                      1290160):int32):int64):int32) 28 =
            word(((32 * val y + 3329) DIV 6658) MOD 16)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_32_64; MOD_MOD_REFL] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`] THEN
  SUBGOAL_THEN `((32 * val(y:int16) + 3329) DIV 6658) MOD 16 < 4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 16 ==> x < 4294967296`) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 268435456 * 16`; GSYM DIV_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D4_ARITH]);;

let COMPRESS_D4_BYTE = prove
 (`!a. a < 16 ==> !b. b < 16 ==>
     val(word_zx(word_zx(word_zx(word_or
      (word_zx(word_zx(word_zx(word_zx(word_zx(word_zx
        (word a:int32):int64):int32):byte):int32):int64):int32)
      (word_shl (word_zx(word_zx(word_zx(word_zx(word_zx(word_zx
        (word b:int32):int64):int32):byte):int32):int64):int32) 4))
      :int64):int32):byte) = a + 16 * b`,
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let COMPRESS_D4_BYTE_ALT =
  REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] COMPRESS_D4_BYTE;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the load with a shifted register offset.                    *)
(* ------------------------------------------------------------------------- *)

let compress_d4_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let COMPRESS_D4_INDEX_TAC k =
  let jt = el k compress_d4_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  let mt = mk_comb(`word_zx:int32->int64`,
            mk_comb(mk_comb(`word_add:int32->int32->int32`,
                            `word_zx(word(8 * i):int64):int32`),
                    mk_comb(`word:num->int32`,mk_small_numeral k))) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X4 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [TRANS_TAC EQ_TRANS mt THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN SPEC_TAC(`word(8 * i):int64`,`w:int64`) THEN
          GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
          WORD_SMALL_TAC];
        DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D4_INDEX_TAC");;

let COMPRESS_D4_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--4) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC [5 + 9 * k] THEN
    COMPRESS_D4_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC
     ((6 + 9 * k)--(13 + 9 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (77--94);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(*                                                                           *)
(* The code reads the address of the stack guard from the global offset      *)
(* table (GOT) at 0x1fff8 in the loaded image, which is outside the code and *)
(* read-only data covered by the image and so is part of the precondition,   *)
(* and checks before returning that the copy of the guard on the stack is    *)
(* still the same, which it is since neither the guard nor the GOT entry is  *)
(* written by the code.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1bf0) /\
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
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128);
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

  (*** The outer loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x1c20` `pc + 0x1c9c`
   `\i s. read X0 s = word_add r (word(4 * i)) /\
          read X1 s = word(8 * i) /\
          read X10 s = a /\
          read X11 s = word 134217728 /\
          read X12 s = word 1290160 /\
          read X13 s = word_add stackpointer (word 16) /\
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
           ==> read(memory :> bytes(r,4 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((32 * val(x j) + 3329) DIV 6658) MOD 16 *
                     2 EXP (4 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (2--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for eight coefficients and four bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC])
     compress_d4_indices THEN
    COMPRESS_D4_BODY_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN WORD_SMALL_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D4_NIBBLE) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])
     compress_d4_indices THEN

    (*** Split off the new bytes and the 4-bit values for them ***)

    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = (((4 * i + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(4 * i + 1) + 1 = 4 * i + 2`;
                ARITH_RULE `(4 * i + 2) + 1 = 4 * i + 3`] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[COMPRESS_D4_BYTE_ALT; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit, the check of the stack guard and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (2--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, since besides the arguments the events depend on  *)
(* the address of the stack guard, read from the GOT, which is also read.    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,128; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,128; word_sub stackpointer (word 32),32]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x1bf0) /\
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
                     [a,512; r,128; word_sub stackpointer (word 32),32;
                      word(pc + 0x1fff8),8; guard,8]
                     [r,128; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,128);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r guard pc stackpointer returnaddress i))
          (f_ev_prol a r guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x1c20` `pc + 0x1ca4`
    `\i s. read X0 s = word_add r (word(4 * i)) /\
           read X1 s = word(8 * i) /\
           read X10 s = a /\
           read X13 s = word_add stackpointer (word 16) /\
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (2--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  COMPRESS_D4_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (95--96) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub
           (word_zx (word_zx (word_add (word_zx (word (8 * i):int64):int32)
                                       (word 8)):int64):int32)
           (word 256):int32) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 8 * i < 18446744073709551616 /\ 8 * i < 4294967296 /\
                 8 * i + 8 < 4294967296 /\
                 8 * i + 8 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN WORD_SMALL_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
