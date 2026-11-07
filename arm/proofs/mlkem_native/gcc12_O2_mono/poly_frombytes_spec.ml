(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 12-bit coefficients from bytes, without reduction. This is   *)
(* the code for mlk_poly_frombytes_c from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), which is the same as mlkem_poly_frombytes of     *)
(* the separate -O2 build. It is verified in the whole image (see            *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_frombytes_c:
       +0x0: add     x6, x1, #0x180
       +0x4: nop
       +0x8: ldrb    w2, [x1, #1]
       +0xc: add     x0, x0, #0x4
      +0x10: ldrb    w4, [x1, #2]
      +0x14: ldrb    w5, [x1], #3
      +0x18: ubfiz   w3, w2, #8, #4
      +0x1c: lsl     w4, w4, #4
      +0x20: orr     w3, w3, w5
      +0x24: orr     w2, w4, w2, lsr #4
      +0x28: sturh   w3, [x0, #-4]
      +0x2c: sturh   w2, [x0, #-2]
      +0x30: cmp     x6, x1
      +0x34: b.ne    <mlk_poly_frombytes_c+0x8>
      +0x38: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_frombytes_c"];;

(* ------------------------------------------------------------------------- *)
(* The two coefficients from three bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let FROMBYTES_LANES_STMT =
  `!n i.
     word_zx(word_join
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (0,4):4 word)
              (word((n DIV 2 EXP (24 * i)) MOD 256):byte):12 word):int16 =
     word((n DIV 2 EXP (24 * i)) MOD 4096) /\
     word_zx(word_join
              (word((n DIV 2 EXP (24 * i + 16)) MOD 256):byte)
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (4,4):4 word):12 word):int16 =
     word((n DIV 2 EXP (24 * i + 12)) MOD 4096)`;;

let FROMBYTES_LANES = assume_spec FROMBYTES_LANES_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_frombytes_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_frombytes_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 384]", "true")],
   "void",
   [("a", "384", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frombytes_signature
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_frombytes_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_poly_reduce.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a n pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_frombytes_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,384)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT;;
