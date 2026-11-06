(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial. This is the code for     *)
(* mlkem_poly_frommsg from mlkem-native's portable C implementation          *)
(* compiled by gcc 12 with -O2 as one translation unit (see                  *)
(* mlkem_native/README.md), which is the same as in the separate -O2         *)
(* build. It is verified in the whole image (see libmlkem.ml).               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_frommsg:
       +0x0: mov     x6, x0
       +0x4: mov     x5, x1
       +0x8: mov     x3, #0x0
       +0xc: mov     w8, #0x1
      +0x10: mov     w7, #0x681
      +0x14: nop
      +0x18: lsl     w4, w3, #3
      +0x1c: mov     w1, #0x0
      +0x20: lsl     w0, w8, w1
      +0x24: ldrb    w2, [x5, x3]
      +0x28: and     w0, w0, #0xff
      +0x2c: and     w0, w0, w2
      +0x30: neg     w0, w0
      +0x34: add     w2, w1, w4
      +0x38: and     w0, w7, w0, asr #16
      +0x3c: add     w1, w1, #0x1
      +0x40: strh    w0, [x6, x2, lsl #1]
      +0x44: cmp     w1, #0x8
      +0x48: b.ne    <mlkem_poly_frommsg+0x20>
      +0x4c: add     x3, x3, #0x1
      +0x50: cmp     x3, #0x20
      +0x54: b.ne    <mlkem_poly_frommsg+0x18>
      +0x58: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem_poly_frommsg"];;

(* ------------------------------------------------------------------------- *)
(* The bits of a byte of an array given as a number.                         *)
(* ------------------------------------------------------------------------- *)

let BYTE_BIT_STMT =
  `!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`;;

let BYTE_BIT = assume_spec BYTE_BIT_STMT;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the store with a shifted register offset.                   *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X2 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "FROMMSG_INDEX_TAC");;

let FROMMSG_BODY_TAC =
  SUBGOAL_THEN `word_zx (word_shl (word_zx (word i:int64):int32) 3):int64 =
                word(8 * i)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_EXEC
     ((3 + 11 * k)--(8 + 11 * k)) THEN
    FROMMSG_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_EXEC
     ((9 + 11 * k)--(13 + 11 * k))) (0--7);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 1 in common/fips203.ml, the    *)
(* result for a bit y is the integer closest to 3329 * y / 2, rounding up on *)
(* ties, i.e. (3329 * y + 1) DIV 2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem_poly_frommsg) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_frommsg_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 32]", "true")],
   "void",
   [("a", "32", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frommsg_signature
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem_poly_frommsg) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,32; r,512] [r,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
