(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has vectorized using SSE2.                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/layout.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_tomont","mlkem_poly_tomont"]);;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun _ ->
          "mlkem_native_poly_tomont_gcc12_O2_data")
        "x86/mlkem_native/gcc12_O2/poly_tomont.o";;
 ****)

let mlkem_native_poly_tomont_gcc12_O2_mc,
    mlkem_native_poly_tomont_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlkem_native_poly_tomont_gcc12_O2_constants" ->
          "mlkem_native_poly_tomont_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_tomont_gcc12_O2_mc"
    "x86/mlkem_native/gcc12_O2/poly_tomont.o"
(fun b ADDR -> [b[
  0x66; 0x0f; 0x6f; 0x2d];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(-4)); b[
                           (* MOVDQA (%_% xmm5) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + &8)))))) *)
  0x66; 0x0f; 0x6f; 0x35];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(12)); b[
                           (* MOVDQA (%_% xmm6) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + -- &0)))))) *)
  0x48; 0x8d; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rax) (%% (rdi,512)) *)
  0x66; 0x0f; 0x6f; 0x25];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(28)); b[
                           (* MOVDQA (%_% xmm4) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + -- &1)))))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x6f; 0x1f;  (* MOVDQA (%_% xmm3) (Memop Word128 (%% (rdi,0))) *)
  0x66; 0x0f; 0x6f; 0xc5;  (* MOVDQA (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0xe5; 0x07;  (* PMULHW (%_% xmm0) (Memop Word128 (%% (rdi,0))) *)
  0x48; 0x83; 0xc7; 0x10;  (* ADD (% rdi) (Imm8 (word 16)) *)
  0x66; 0x0f; 0xd5; 0xdd;  (* PMULLW (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xfb;  (* MOVDQA (%_% xmm7) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xd8;  (* PUNPCKHWD (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xf8;  (* PUNPCKLWD (%_% xmm7) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc7;  (* MOVDQA (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0x6f; 0xcf;  (* MOVDQA (%_% xmm1) (%_% xmm7) *)
  0x66; 0x0f; 0x61; 0xc3;  (* PUNPCKLWD (%_% xmm0) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xcb;  (* PUNPCKHWD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0xd5; 0xc6;  (* PMULLW (%_% xmm0) (%_% xmm6) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0xe5; 0xcc;  (* PMULHW (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xd5; 0xd4;  (* PMULLW (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xc2;  (* MOVDQA (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xca;  (* MOVDQA (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0xfe; 0xc7;  (* PADDD (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xcb;  (* PADDD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x72; 0xe1; 0x10;
                           (* PSRAD (%_% xmm1) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x72; 0xe0; 0x10;
                           (* PSRAD (%_% xmm0) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0x69; 0xca;  (* PUNPCKHWD (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x0f; 0x29; 0x47; 0xf0;  (* MOVAPS (Memop Word128 (%%
                                     (rdi,18446744073709551600))) (%_% xmm0) *)
  0x48; 0x39; 0xf8;        (* CMP (% rax) (% rdi) *)
  0x0f; 0x85; 0x61; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967137)) *)
  0xc3                     (* RET *)
]]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_tomont_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The vectors of constants in the read-only data.                           *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CONSTANTS_LOADED_STMT =
  `!c s. bytes_loaded s (word c) mlkem_native_poly_tomont_gcc12_O2_data
         ==> read(memory :> bytes128(word c)) s =
             word 0x05490549054905490549054905490549 /\
             read(memory :> bytes128(word(c + 16))) s =
             word 0xf301f301f301f301f301f301f301f301 /\
             read(memory :> bytes128(word(c + 32))) s =
             word 0xf2fff2fff2fff2fff2fff2fff2fff2ff`;;

let TOMONT_CONSTANTS_LOADED =
  assume_spec TOMONT_CONSTANTS_LOADED_STMT;;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane. The compiler forms the 32-bit products   *)
(* from the 16-bit high and low halves given by PMULHW and PMULLW, which it  *)
(* interleaves and later de-interleaves with PUNPCKLWD and PUNPCKHWD.        *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE_FORM_STMT =
  `!x:int16.
     word_subword
      (word_ishr
        (word_add
          (word_join
            (word_subword
              (word_mul (word_sx (word_mul (word_mul x (word 1353))
                                           (word 62209)):int32)
                        (word 4294963967))
              (16,16):int16)
            (word_mul (word_mul (word_mul x (word 1353)) (word 62209))
                      (word 62207)):int32)
          (word_join
            (word_subword (word_mul (word 1353) (word_sx x:int32))
                          (16,16):int16)
            (word_mul x (word 1353)):int32))
        16)
      (0,16):int16 =
     montred_x86 (word_mul (word_sx x) (word 1353))`;;

let TOMONT_LANE_FORM =
  assume_spec TOMONT_LANE_FORM_STMT;;

let TOMONT_LANE_STMT =
  `!x:int16.
     (ival(montred_x86(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_x86(word_mul (word_sx x) (word 1353)))) <= &3328`;;

let TOMONT_LANE =
  assume_spec TOMONT_LANE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT_STMT =
  `!a consts x pc.
    aligned 16 a /\ aligned 16 (word consts:int64) /\
    riprel32_within_bounds consts (pc + 8) /\
    riprel32_within_bounds (consts + 16) (pc + 16) /\
    riprel32_within_bounds (consts + 32) (pc + 31) /\
    ALL (nonoverlapping (a,512)) [(word pc,poly_tomont_size); (word consts,48)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read RIP s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + poly_tomont_ret) /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!a consts x pc stackpointer returnaddress.
    aligned 16 a /\ aligned 16 (word consts:int64) /\
    riprel32_within_bounds consts (pc + 8) /\
    riprel32_within_bounds (consts + 16) (pc + 16) /\
    riprel32_within_bounds (consts + 32) (pc + 31) /\
    ALL (nonoverlapping (a,512))
        [(word pc,poly_tomont_size); (word consts,48); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the vectors of ***)
(*** constants are a read-only object.                                 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word consts:int64`,`48`]
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SAFE_STMT =
  `exists f_events.
       forall e a consts pc.
           aligned 16 a /\ aligned 16 (word consts:int64) /\
           riprel32_within_bounds consts (pc + 8) /\
           riprel32_within_bounds (consts + 16) (pc + 16) /\
           riprel32_within_bounds (consts + 32) (pc + 31) /\
           ALL (nonoverlapping (a,512)) [word pc,poly_tomont_size; word consts,48]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_tomont_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a consts pc /\
                         memaccess_inbounds e2
                          [a,512; word consts,48] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SAFE_STMT;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a consts pc stackpointer returnaddress.
           aligned 16 a /\ aligned 16 (word consts:int64) /\
           riprel32_within_bounds consts (pc + 8) /\
           riprel32_within_bounds (consts + 16) (pc + 16) /\
           riprel32_within_bounds (consts + 32) (pc + 31) /\
           ALL (nonoverlapping (a,512))
               [word pc,poly_tomont_size; word consts,48; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a consts pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; word consts,48; stackpointer,8] [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, with the vectors of constants (see      *)
(* libmlkem.ml).                                                             *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_tomont_gcc12_O2_mc
    (layout "mlkem_poly_tomont") [layout "mlkem_poly_tomont_consts"];;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CONSTANTS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE
    (hd mlkem_native_poly_tomont_gcc12_O2_data) (layout "mlkem_poly_tomont_consts");;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    aligned 16 a /\
    ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_tomont) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           aligned 16 a /\
           ALL (nonoverlapping (a,512)) [word pc,libmlkem_size; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_tomont) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; word (pc + mlkem_poly_tomont_consts),48;
                           stackpointer,8] [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
