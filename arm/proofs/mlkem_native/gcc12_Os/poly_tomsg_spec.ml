(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message. This is the code for     *)
(* mlkem_poly_tomsg from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -Os (see mlkem_native/README.md). It is verified in the    *)
(* whole image (see libmlkem.ml).                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomsg:
       +0x0: mov     w5, #0xafb8
       +0x4: mov     x3, #0x0
       +0x8: movk    w5, #0x13, lsl #16
       +0xc: mov     w6, #0x40000000
      +0x10: lsl     w8, w3, #3
      +0x14: mov     w4, #0x0
      +0x18: strb    wzr, [x0, x3]
      +0x1c: add     w2, w8, w4
      +0x20: ldrb    w7, [x0, x3]
      +0x24: ldrsh   w2, [x1, x2, lsl #1]
      +0x28: madd    w2, w2, w5, w6
      +0x2c: lsr     w2, w2, #31
      +0x30: lsl     w2, w2, w4
      +0x34: add     w4, w4, #0x1
      +0x38: orr     w2, w2, w7
      +0x3c: strb    w2, [x0, x3]
      +0x40: cmp     w4, #0x8
      +0x44: b.ne    <mlkem_poly_tomsg+0x1c>
      +0x48: add     x3, x3, #0x1
      +0x4c: cmp     x3, #0x20
      +0x50: b.ne    <mlkem_poly_tomsg+0x10>
      +0x54: ret     
 ***)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_tomsg"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH_STMT =
  `!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`;;

let COMPRESS_D1_ARITH = assume_spec COMPRESS_D1_ARITH_STMT;;

let TOMSG_BIT_STMT =
  `!y:int16.
        val y < 3329
        ==> word_ushr
             (word_zx (word_zx
               (word (1073741824 +
                      val (word_zx (word_zx (word_sx y:int32):int64):int32) *
                      1290168):int32):int64):int32) 31 =
            word(((4 * val y + 3329) DIV 6658) MOD 2)`;;

let TOMSG_BIT = assume_spec TOMSG_BIT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Splitting off the bits for one byte from the number for the message.      *)
(* ------------------------------------------------------------------------- *)

let NSUM_BYTE_STMT =
  `!f m. nsum {k | k < 8} (\k. f(m + k) * 2 EXP (m + k)) =
         2 EXP m * nsum {k | k < 8} (\k. f(m + k) * 2 EXP k)`;;

let NSUM_BYTE = assume_spec NSUM_BYTE_STMT;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the load with a shifted register offset.                    *)
(* ------------------------------------------------------------------------- *)

let tomsg_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let TOMSG_INDEX_TAC k =
  let jt = el k tomsg_indices in
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
    else failwith "TOMSG_INDEX_TAC");;

(*** The 92 steps of an iteration of the outer loop, up to its test: the
 *** clearing of the byte, eight iterations of the inner loop of 11
 *** instructions each, and the update of the byte index ***)

let TOMSG_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC (1--1) THEN
  SUBGOAL_THEN `word_zx (word_shl (word_zx (word i:int64):int32) 3):int64 =
                word(8 * i)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC (2--3) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC
     ((4 + 11 * k)--(4 + 11 * k)) THEN
    TOMSG_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC
     ((5 + 11 * k)--(14 + 11 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC (92--92);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 1 in common/fips203/fips203.ml,  *)
(* the bit for a coefficient x in [0,3329) is the integer closest to 2 * x / *)
(* 3329, rounding up on ties, modulo 2, i.e. ((4 * x + 3329) DIV 6658) MOD   *)
(* 2, and as for mlkem_encode 1 the bits are put together little-endian.     *)
(* Like the C code, this relies on the coefficients being in [0,3329).       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,32)) [(word pc,libmlkem_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_tomsg) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_tomsg_signature =
  ([("r", "uint8_t[static 32]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("r", "32", 1)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_tomsg_signature
    MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,32)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem_poly_tomsg) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,512; r,32] [r,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
