(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction of polynomials, coefficientwise with wraparound. This is the  *)
(* code for mlkem_poly_sub from mlkem-native's portable C implementation     *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which the     *)
(* compiler has vectorized and unrolled completely, after a check that the   *)
(* two arrays do not overlap. It is verified in the whole image (see         *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image. If the arrays overlap, a scalar loop does the
 *** subtractions one at a time; otherwise the code from +0x3c does them on
 *** 16 pairs of Q registers, the pattern of +0x3c to +0x60 continuing
 *** with the offsets increased by 32 each time:

    mlkem_poly_sub:
       +0x0: add     x8, x1, #0x200
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_sub+0x3c>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    <mlkem_poly_sub+0x3c>
      +0x18: mov     x8, xzr
      +0x1c: ldrh    w9, [x0, x8]
      +0x20: ldrh    w10, [x1, x8]
      +0x24: sub     w9, w9, w10
      +0x28: strh    w9, [x0, x8]
      +0x2c: add     x8, x8, #0x2
      +0x30: cmp     x8, #0x200
      +0x34: b.ne    <mlkem_poly_sub+0x1c>
      +0x38: ret
      +0x3c: ldp     q0, q1, [x0]
      +0x40: ldp     q2, q3, [x1]
      +0x44: sub     v0.8h, v0.8h, v2.8h
      +0x48: ldp     q4, q2, [x0, #32]
      +0x4c: sub     v1.8h, v1.8h, v3.8h
      +0x50: stp     q0, q1, [x0]
      +0x54: ldp     q3, q5, [x1, #32]
      +0x58: sub     v1.8h, v4.8h, v3.8h
      +0x5c: ldp     q0, q3, [x0, #64]
      +0x60: sub     v2.8h, v2.8h, v5.8h
      ...
     +0x16c: ldp     q4, q5, [x1, #480]
     +0x170: sub     v0.8h, v1.8h, v4.8h
     +0x174: sub     v1.8h, v2.8h, v5.8h
     +0x178: stp     q0, q1, [x0, #480]
     +0x17c: ret
 ***)

let MLKEM_NATIVE_POLY_SUB_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_sub"];;

(* ------------------------------------------------------------------------- *)
(* The check for overlap. For arrays r and b of 512 bytes, the code takes    *)
(* the vectorized path if b + 512 <= r or r + 512 <= b, computed modulo      *)
(* 2^64. When the arrays do not overlap, one of these holds: if neither did, *)
(* the start of one array would be within the other, also when an array      *)
(* wraps around the end of the address space.                                *)
(* ------------------------------------------------------------------------- *)

let MOD_2N_CASES_STMT =
  `!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`;;

let MOD_2N_CASES = assume_spec MOD_2N_CASES_STMT;;

let ALIAS_CHECK_512_STMT =
  `!r b:int64.
        nonoverlapping (r,512) (b,512)
        ==> ~(val r <= val (word_add b (word 512)) /\
              ~(val (word_sub (word_add b (word 512)) r) = 0)) \/
            ~(val b <= val (word_add r (word 512)) /\
              ~(val (word_sub (word_add r (word 512)) b) = 0))`;;

let ALIAS_CHECK_512 = assume_spec ALIAS_CHECK_512_STMT;;

(*** The two conditions, and using one of them in a case of the proof ***)

let ALIAS_CHECK_1 =
 `~(val (r:int64) <= val (word_add b (word 512):int64) /\
    ~(val (word_sub (word_add b (word 512)) r:int64) = 0))`
and ALIAS_CHECK_2 =
 `~(val (b:int64) <= val (word_add r (word 512):int64) /\
    ~(val (word_sub (word_add r (word 512)) b:int64) = 0))`;;

let USE_CASE_TAC c =
  FIRST_X_ASSUM(fun th ->
    if concl th = c then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (b,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_sub) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_sub (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_sub_signature =
  ([("r", "int16_t[static 256]", "false");
    ("b", "int16_t[static 256]", "true")],
   "void",
   [("r", "256", 2); ("b", "256", 2)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_sub_signature
    MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_SUB_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r b pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; b,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_sub) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc returnaddress /\
                         memaccess_inbounds e2 [r,512; b,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
