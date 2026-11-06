(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has vectorized. It reads its own vectors of constants  *)
(* from the read-only data.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_tomont","mlkem_poly_tomont"]);;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun _ ->
          "mlkem_native_poly_tomont_gcc12_O2_data")
        "arm/mlkem_native/gcc12_O2/poly_tomont.o";;
 ****)

let mlkem_native_poly_tomont_gcc12_O2_mc,
    mlkem_native_poly_tomont_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1"
      | "mlkem_native_poly_tomont_gcc12_O2_constants" ->
          "mlkem_native_poly_tomont_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_tomont_gcc12_O2_mc"
    "arm/mlkem_native/gcc12_O2/poly_tomont.o"
(fun w BL ADR ADRP ADD_rri64 LDR_Q_rri -> [
  ADRP (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),16,0,2);
  ADRP (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),0,4,1);
  w 0x6f00a5a3;         (* arm_MOVI Q3 (word 17509981057347220223) *)
  LDR_Q_rri (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),16,5,2);
  LDR_Q_rri (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),0,4,1);
  w 0x91080001;         (* arm_ADD X1 X0 (rvalue (word 512)) *)
  w 0x3dc00000;         (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  w 0x0e64c001;         (* arm_SMULL_VEC Q1 Q0 Q4 16 *)
  w 0x4e64c000;         (* arm_SMULL2_VEC Q0 Q0 Q4 16 *)
  w 0x4e401822;         (* arm_UZP1 Q2 Q1 Q0 16 *)
  w 0x4e659c42;         (* arm_MUL_VEC Q2 Q2 Q5 16 128 *)
  w 0x0e638041;         (* arm_SMLAL_VEC Q1 Q2 Q3 16 *)
  w 0x4e638040;         (* arm_SMLAL2_VEC Q0 Q2 Q3 16 *)
  w 0x4e405821;         (* arm_UZP2 Q1 Q1 Q0 16 *)
  w 0x3c810401;         (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  w 0xeb00003f;         (* arm_CMP X1 X0 *)
  w 0x54fffec1;         (* arm_BNE (word 2097112) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_tomont_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The vectors of constants in the read-only data.                           *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CONSTANTS_LOADED_STMT =
  `!c s. bytes_loaded s (word c) mlkem_native_poly_tomont_gcc12_O2_data
         ==> read(memory :> bytes128(word c)) s =
             word 0x05490549054905490549054905490549 /\
             read(memory :> bytes128(word(c + 16))) s =
             word 0xf301f301f301f301f301f301f301f301`;;

let TOMONT_CONSTANTS_LOADED = assume_spec TOMONT_CONSTANTS_LOADED_STMT;;

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

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT_STMT =
  `!a consts x pc.
    adrp_within_bounds (word(consts + 16)) (word pc) /\
    adrp_within_bounds (word consts) (word(pc + 4)) /\
    aligned 16 (word consts:int64) /\
    ALL (nonoverlapping (a,512)) [(word pc,poly_tomont_size); (word consts,32)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read PC s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + poly_tomont_ret) /\
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
  `!a consts x pc returnaddress.
    adrp_within_bounds (word(consts + 16)) (word pc) /\
    adrp_within_bounds (word consts) (word(pc + 4)) /\
    aligned 16 (word consts:int64) /\
    ALL (nonoverlapping (a,512)) [(word pc,poly_tomont_size); (word consts,32)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
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

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the vectors of ***)
(*** constants are a read-only object.                                 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word consts:int64`,`32`]
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a consts pc returnaddress.
           adrp_within_bounds (word (consts + 16)) (word pc) /\
           adrp_within_bounds (word consts) (word (pc + 4)) /\
           aligned 16 (word consts:int64) /\
           ALL (nonoverlapping (a,512)) [word pc,72; word consts,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read PC s = word pc /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a consts pc returnaddress /\
                        memaccess_inbounds e2
                         [a,512; word consts,32] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, with the constants (see                 *)
(* libmlkem.ml).                                                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_tomont_gcc12_O2_mc
    (layout "mlkem_poly_tomont") [layout "mlkem_poly_tomont_consts"];;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CONSTANTS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE
    (hd mlkem_native_poly_tomont_gcc12_O2_data)
     (layout "mlkem_poly_tomont_consts");;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O2_mc /\
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
                          word (pc + mlkem_poly_tomont_consts),32] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
