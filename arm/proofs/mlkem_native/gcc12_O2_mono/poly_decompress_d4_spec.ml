(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 4 bits per coefficient. This is the    *)
(* code for mlk_poly_decompress_d4_c from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), which is the same as mlkem_poly_decompress_d4    *)
(* of the separate -O2 build. It is verified in the whole image (see         *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_decompress_d4_c:
       +0x0: add     x4, x0, #0x200
       +0x4: mov     w3, #0xd01
       +0x8: nop
       +0xc: ldrb    w2, [x1]
      +0x10: add     x0, x0, #0x4
      +0x14: and     w2, w2, #0xf
      +0x18: mul     w2, w2, w3
      +0x1c: add     w2, w2, #0x8
      +0x20: lsr     w2, w2, #4
      +0x24: sturh   w2, [x0, #-4]
      +0x28: ldrb    w2, [x1], #1
      +0x2c: lsr     w2, w2, #4
      +0x30: mul     w2, w2, w3
      +0x34: add     w2, w2, #0x8
      +0x38: lsr     w2, w2, #4
      +0x3c: sturh   w2, [x0, #-2]
      +0x40: cmp     x4, x0
      +0x44: b.ne    <mlk_poly_decompress_d4_c+0xc>
      +0x48: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_decompress_d4_c"];;

(* ------------------------------------------------------------------------- *)
(* The two 4-bit fields of a byte of an array given as a number.             *)
(* ------------------------------------------------------------------------- *)

let BYTE_NIBBLES_STMT =
  `(!n k. (n DIV 2 EXP k) MOD 2 EXP 4 = ((n DIV 2 EXP k) MOD 256) MOD 16) /\
   (!n k. (n DIV 2 EXP (k + 4)) MOD 2 EXP 4 =
          ((n DIV 2 EXP k) MOD 256) DIV 16)`;;

let BYTE_NIBBLES = assume_spec BYTE_NIBBLES_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 4 in common/fips203.ml, the    *)
(* result for a 4-bit field y is the integer closest to 3329 * y / 16,       *)
(* rounding up on ties, i.e. (3329 * y + 8) DIV 16.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_decompress_d4_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8)
                               DIV 16))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d4_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 128]", "true")],
   "void",
   [("a", "128", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d4_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_decompress_d4_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
