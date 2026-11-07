(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial. This is the code for     *)
(* mlkem_poly_frommsg from mlkem-native's portable C implementation compiled *)
(* by gcc 12 with -O3 (see mlkem_native/README.md), where the inner loop     *)
(* over the bits of a byte is unrolled. It is verified in the whole image    *)
(* (see libmlkem.ml).                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image, where the pattern of +0x30 to +0x4c is repeated
 *** for the other bits, with the masks in w11, w10, w9, w8, w7, w6 and w5
 *** and the stores at offsets 2 to 12 from x2, the last one after x2 is
 *** advanced:

    mlkem_poly_frommsg:
       +0x0: mov     x2, x0
       +0x4: mov     x3, x1
       +0x8: add     x13, x0, #0x200
       +0xc: mov     w12, #0x1
      +0x10: mov     w4, #0x681
      +0x14: mov     w11, #0x2
      +0x18: mov     w10, #0x4
      +0x1c: mov     w9, #0x8
      +0x20: mov     w8, #0x10
      +0x24: mov     w7, #0x20
      +0x28: mov     w6, #0x40
      +0x2c: mov     w5, #0xffffff80
      +0x30: mov     w0, w12
      +0x34: ldrb    w1, [x3]
      +0x38: and     w0, w0, #0xff
      +0x3c: and     w0, w0, w1
      +0x40: neg     w0, w0
      +0x44: and     w1, w4, w0, asr #16
      +0x48: mov     w0, w11
      +0x4c: strh    w1, [x2]
      ...
      +0xf8: ldrb    w1, [x3], #1
      +0xfc: and     w0, w0, #0xff
     +0x100: and     w0, w0, w1
     +0x104: neg     w0, w0
     +0x108: and     w0, w4, w0, asr #16
     +0x10c: add     x2, x2, #0x10
     +0x110: sturh   w0, [x2, #-2]
     +0x114: cmp     x13, x2
     +0x118: b.ne    <mlkem_poly_frommsg+0x30>
     +0x11c: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
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
(* Correctness proof. As for mlkem_decompress 1 in common/fips203.ml, the    *)
(* result for a bit y is the integer closest to 3329 * y / 2, rounding up on *)
(* ties, i.e. (3329 * y + 1) DIV 2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_frommsg) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
