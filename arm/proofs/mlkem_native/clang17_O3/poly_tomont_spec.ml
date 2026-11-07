(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which the compiler has vectorized, 16            *)
(* coefficients at a time. Unlike the gcc 12 -O2 code, it makes its vectors  *)
(* of constants with MOV, DUP and MVNI instead of loading them from the      *)
(* read-only data. It is verified in the whole image (see libmlkem.ml).      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomont:
       +0x0: mov     w9, #0x549
       +0x4: mov     w10, #0x50490000
       +0x8: mov     x8, xzr
       +0xc: mvni    v2.4s, #0xd, lsl #8
      +0x10: dup     v0.8h, w9
      +0x14: dup     v1.4s, w10
      +0x18: add     x9, x0, x8
      +0x1c: add     x8, x8, #0x20
      +0x20: cmp     x8, #0x200
      +0x24: ldp     q3, q4, [x9]
      +0x28: sxtl    v5.4s, v3.4h
      +0x2c: sxtl2   v6.4s, v3.8h
      +0x30: sxtl    v7.4s, v4.4h
      +0x34: mul     v5.4s, v5.4s, v1.4s
      +0x38: mul     v7.4s, v7.4s, v1.4s
      +0x3c: sxtl2   v16.4s, v4.8h
      +0x40: mul     v6.4s, v6.4s, v1.4s
      +0x44: mul     v16.4s, v16.4s, v1.4s
      +0x48: sshr    v5.4s, v5.4s, #16
      +0x4c: sshr    v7.4s, v7.4s, #16
      +0x50: smull2  v17.4s, v3.8h, v0.8h
      +0x54: sshr    v6.4s, v6.4s, #16
      +0x58: smull   v3.4s, v3.4h, v0.4h
      +0x5c: smull2  v18.4s, v4.8h, v0.8h
      +0x60: smull   v4.4s, v4.4h, v0.4h
      +0x64: mul     v5.4s, v5.4s, v2.4s
      +0x68: mul     v7.4s, v7.4s, v2.4s
      +0x6c: sshr    v16.4s, v16.4s, #16
      +0x70: mul     v6.4s, v6.4s, v2.4s
      +0x74: mul     v16.4s, v16.4s, v2.4s
      +0x78: addhn   v3.4h, v5.4s, v3.4s
      +0x7c: addhn   v4.4h, v7.4s, v4.4s
      +0x80: addhn2  v3.8h, v6.4s, v17.4s
      +0x84: addhn2  v4.8h, v16.4s, v18.4s
      +0x88: stp     q3, q4, [x9]
      +0x8c: b.ne    <mlkem_poly_tomont+0x18>
      +0x90: ret
 ***)

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Splitting off the 16 coefficients handled by one iteration of the loop.   *)
(* ------------------------------------------------------------------------- *)

let CHUNK16_INPUT_SPLIT_STMT =
  `!P i. i < 16
         ==> ((!j. 16 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 16 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 16 ==> P(16 * i + k)))`;;

let CHUNK16_INPUT_SPLIT = assume_spec CHUNK16_INPUT_SPLIT_STMT;;

let CHUNK16_OUTPUT_SPLIT_STMT =
  `!P i. (!j. j < 16 * (i + 1) ==> P j) <=>
         (!j. j < 16 * i ==> P j) /\ (!k. k < 16 ==> P(16 * i + k))`;;

let CHUNK16_OUTPUT_SPLIT = assume_spec CHUNK16_OUTPUT_SPLIT_STMT;;

let CHUNK16_ADDR_STMT =
  `!a i k. word_add a (word(2 * (16 * i + k))):int64 =
           word_add (word_add a (word(32 * i))) (word(2 * k))`;;

let CHUNK16_ADDR = assume_spec CHUNK16_ADDR_STMT;;

(*** Addresses word_add (word_add a (word(32 * i + 16))) (word k) and the
 *** like, as the simulation leaves them, in the form
 *** word_add a (word(32 * i + k')) of the specification
 ***)

let ADDR_NORM_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane. The code computes the Montgomery         *)
(* reduction of x * 1353, but with the low half of the quotient computed     *)
(* from x directly, as the high half of x * (20553 * 2^16) for               *)
(* 20553 = 1353 * 62209 mod 2^16 (62209 being 3329^-1 mod 2^16). This is     *)
(* the same as montred_neon.                                                 *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CLANG17_O3_FACTOR_STMT =
  `!x:int16.
     word_ishr (word_mul (word_sx x) (word 1346961408)) 16:int32 =
     word_sx (word_mul (word_subword (word_mul (word_sx x) (word 1353):int32)
                                     (0,16))
                       (word 62209):int16)`;;

let TOMONT_CLANG17_O3_FACTOR = assume_spec TOMONT_CLANG17_O3_FACTOR_STMT;;

let TOMONT_CLANG17_O3_MONTRED_STMT =
  `!x:int16.
     word_subword
      (word_add
        (word_mul
          (word_ishr (word_mul (word_shl (word_sx x:int32) 0)
                               (word 1346961408)) 16)
          (word 4294963967))
        (word_mul (word_sx x) (word 1353)):int32) (16,16):int16 =
     montred_neon(word_mul (word_sx x) (word 1353))`;;

let TOMONT_CLANG17_O3_MONTRED = assume_spec TOMONT_CLANG17_O3_MONTRED_STMT;;

let TOMONT_LANE_STMT =
  `!x:int16.
     (ival(montred_neon(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_neon(word_mul (word_sx x) (word 1353)))) <= &3328`;;

let TOMONT_LANE = assume_spec TOMONT_LANE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_tomont) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomont) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
