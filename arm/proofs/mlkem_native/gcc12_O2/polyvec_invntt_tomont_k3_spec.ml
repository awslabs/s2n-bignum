(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform of a vector of 3 polynomials, with     *)
(* conversion to Montgomery form. This is the code for                       *)
(* mlkem768_polyvec_invntt_tomont from mlkem-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_invntt_tomont for each of the polynomials, the     *)
(* last time as a tail call. It is verified in the whole image (see          *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_poly_invntt_tomont in the image.                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem768_polyvec_invntt_tomont:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: bl      <mlkem_poly_invntt_tomont>
       +0xc: add     x0, x19, #0x200
      +0x10: bl      <mlkem_poly_invntt_tomont>
      +0x14: add     x0, x19, #0x400
      +0x18: ldp     x19, x30, [sp], #16
      +0x1c: b       <mlkem_poly_invntt_tomont>
 ***)

let MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem768_polyvec_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,1536) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
          [(a,1536); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem768_polyvec_invntt_tomont) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 3
                      ==> !i. i < 256
                              ==> let zi =
                                    read(memory :> bytes16
                                     (word_add a (word(512 * j + 2 * i)))) s
                                  in (ival zi ==
                                      inverse_ntt (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival zi) <= &26624)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1536);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_invntt_tomont_k3_signature =
  ([("a", "int16_t[static 768]", "false")],
   "void",
   [("a", "768", 2)],
   [("a", "768", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_invntt_tomont_const1):int64`,`32`;
                       `word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_polyvec_invntt_tomont_k3_signature
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_EXEC;;

let LOCAL_INVNTT_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,1536) (word_sub stackpointer (word 32),32) /\
           ALLPAIRS nonoverlapping
           [a,1536; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem768_polyvec_invntt_tomont) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,1536; word_sub stackpointer (word 32),32;
                          word (pc + mlkem_poly_invntt_tomont_consts),32;
                          word (pc + rodata_mlk_zetas),256]
                         [a,1536; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,1536);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
