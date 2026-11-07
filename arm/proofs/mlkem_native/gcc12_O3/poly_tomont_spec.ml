(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form. This is the     *)
(* code for mlkem_poly_tomont from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md), which the       *)
(* compiler has vectorized. It is verified in the whole image (see           *)
(* libmlkem.ml). The loop is the same as with -O2, but the vector of 0xf2ff  *)
(* is made with MVNI instead of MOVI, and the two vectors of constants       *)
(* loaded from the read-only data are not next to each other: that of        *)
(* 3329^-1 mod 2^16, which other functions share, is at the start of the     *)
(* block mlkem_poly_tomont_consts, and that of 1353 at its end. So the       *)
(* theorem of constant time and memory safety has that block of              *)
(* mlkem_poly_tomont_consts_size bytes as a read-only region, where with -O2 *)
(* it has the 32 bytes of the two vectors.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomont:
       +0x0: adrp    x2, <page>
       +0x4: adrp    x1, <page>
       +0x8: mvni    v3.8h, #0xd, lsl #8
       +0xc: ldr     q5, [x2, #2336]
      +0x10: ldr     q4, [x1, #2400]
      +0x14: add     x1, x0, #0x200
      +0x18: ldr     q0, [x0]
      +0x1c: smull   v1.4s, v0.4h, v4.4h
      +0x20: smull2  v0.4s, v0.8h, v4.8h
      +0x24: uzp1    v2.8h, v1.8h, v0.8h
      +0x28: mul     v2.8h, v2.8h, v5.8h
      +0x2c: smlal   v1.4s, v2.4h, v3.4h
      +0x30: smlal2  v0.4s, v2.8h, v3.8h
      +0x34: uzp2    v1.8h, v1.8h, v0.8h
      +0x38: str     q1, [x0], #16
      +0x3c: cmp     x1, x0
      +0x40: b.ne    <mlkem_poly_tomont+0x18>
      +0x44: ret
 ***)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_tomont"];;

(*** The vectors of 3329^-1 mod 2^16 and of 1353 = 2^32 mod 3329 ***)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem_poly_tomont_const1"; layout "mlkem_poly_tomont_const2"];;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane.                                          *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE_STMT =
  `!x:int16.
     (ival(montred_neon(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_neon(word_mul (word_sx x) (word 1353)))) <= &3328`;;

let TOMONT_LANE = assume_spec TOMONT_LANE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
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

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the block of the ***)
(*** vectors of constants is a read-only object.                         ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_tomont_consts):int64`,
                       `mlkem_poly_tomont_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomont) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2
                         [a,512;
                          word (pc + mlkem_poly_tomont_consts),
                          mlkem_poly_tomont_consts_size] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
