(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks to a byte array.      *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_tobytes","mlkem_poly_tobytes"]);;

(**** print_literal_from_elf
        "arm/mlkem_native/gcc12_O2/poly_tobytes.o";;
 ****)

let mlkem_native_poly_tobytes_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_tobytes_gcc12_O2_mc"
  "arm/mlkem_native/gcc12_O2/poly_tobytes.o"
[
  0x91060004;       (* arm_ADD X4 X0 (rvalue (word 384)) *)
  0xd503201f;       (* arm_NOP *)
  0x79c00022;       (* arm_LDRSH W2 X1 (Immediate_Offset (word 0)) *)
  0x91000c00;       (* arm_ADD X0 X0 (rvalue (word 3)) *)
  0x79400423;       (* arm_LDRH W3 X1 (Immediate_Offset (word 2)) *)
  0x91001021;       (* arm_ADD X1 X1 (rvalue (word 4)) *)
  0x381fd002;       (* arm_STRB W2 X0
                       (Immediate_Offset (word 18446744073709551613)) *)
  0xd3483c42;       (* arm_UBFM X2 X2 8 15 *)
  0x2a031042;       (* arm_ORR W2 W2 (Shiftedreg W3 LSL 4) *)
  0x53047c63;       (* arm_LSR W3 W3 4 *)
  0x381fe002;       (* arm_STRB W2 X0
                       (Immediate_Offset (word 18446744073709551614)) *)
  0x381ff003;       (* arm_STRB W3 X0
                       (Immediate_Offset (word 18446744073709551615)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54fffea1;       (* arm_BNE (word 2097108) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_tobytes_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(*                                                                           *)
(* Unlike the hand-written kernel mlkem_tobytes, the C code relies on the    *)
(* coefficients being < 2^12, as stated in its contract (in fact requiring   *)
(* them to be < 3329), so this is an additional assumption here.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT_STMT =
  `!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,poly_tobytes_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + poly_tobytes_ret) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,poly_tobytes_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_tobytes ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tobytes" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,60; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_tobytes_gcc12_O2_mc
    (layout "mlkem_poly_tobytes") [];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,384)) [(word pc,libmlkem_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_tobytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_poly_reduce. The loop body is simulated in both cases of the        *)
(* hypothesis on the list, and in the second its events are those already    *)
(* given for the first, so they are matched directly rather than by          *)
(* instantiation.                                                            *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_FULL_DISCHARGE_AGAIN_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then
      CONJ_TAC THENL
       [FULL_UNIFY_F_EVENTS_TAC ORELSE
        (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[ENUMERATEL_ADD1; APPEND; APPEND_NIL;
                     GSYM APPEND_ASSOC] THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
        ALL_TAC]
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let TOBYTES_FULL_TEST_TAC =
  SUBGOAL_THEN
   `~(val(word_sub (word_add r (word 384))
                   (word_add (word_add r (word (3 * i))) (word 3)):int64) =
      0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,poly_tobytes_size; a,512]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
