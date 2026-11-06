(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks to a byte array.      *)
(* This is the code for mlk_poly_tobytes_c from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), which is the same as mlkem_poly_tobytes of the   *)
(* separate -O2 build except for a NOP before the loop there. It is          *)
(* verified in the whole image (see libmlkem.ml), with the proof for the     *)
(* separate -O2 build adapted to the image.                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_tobytes_c:
       +0x0: add     x4, x0, #0x180
       +0x4: ldrsh   w2, [x1]
       +0x8: add     x0, x0, #0x3
       +0xc: ldrh    w3, [x1, #2]
      +0x10: add     x1, x1, #0x4
      +0x14: sturb   w2, [x0, #-3]
      +0x18: ubfx    x2, x2, #8, #8
      +0x1c: orr     w2, w2, w3, lsl #4
      +0x20: lsr     w3, w3, #4
      +0x24: sturb   w2, [x0, #-2]
      +0x28: sturb   w3, [x0, #-1]
      +0x2c: cmp     x4, x0
      +0x30: b.ne    <mlk_poly_tobytes_c+0x4>
      +0x34: ret
 ***)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_tobytes_c"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(*                                                                           *)
(* Unlike the hand-written kernel mlkem_tobytes, the C code relies on the    *)
(* coefficients being < 2^12, as stated in its contract (in fact requiring   *)
(* them to be < 3329), so this is an additional assumption here.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_CORRECT_STMT =
  `!r a (l:int16 list) pc.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,384)) [(word pc,libmlkem_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_tobytes_c) /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + mlk_poly_tobytes_c_ret) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,384)) [(word pc,libmlkem_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_tobytes_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_tobytes ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tobytes" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_tobytes_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)


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

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_tobytes_c) /\
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
               (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT;;
