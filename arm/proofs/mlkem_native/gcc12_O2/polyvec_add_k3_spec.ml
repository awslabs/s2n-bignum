(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of vectors of 3 polynomials, coefficientwise with wraparound.    *)
(* This is the code for mlkem768_polyvec_add from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_add for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see                       *)
(* libmlkem.ml), using the theorems for mlkem_poly_add                       *)
(* in the image.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_add_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem768_polyvec_add:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: str     x30, [sp, #16]
      +0x10: bl      <mlkem_poly_add>
      +0x14: add     x1, x20, #0x200
      +0x18: add     x0, x19, #0x200
      +0x1c: bl      <mlkem_poly_add>
      +0x20: ldr     x30, [sp, #16]
      +0x24: add     x1, x20, #0x400
      +0x28: add     x0, x19, #0x400
      +0x2c: ldp     x19, x20, [sp], #32
      +0x30: b       <mlkem_poly_add>
 ***)

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem768_polyvec_add"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1536); (b,1536); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1536); (b,1536); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem768_polyvec_add) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 768
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 768
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1536);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_add_k3_signature =
  ([("r", "int16_t[static 768]", "false");
    ("b", "int16_t[static 768]", "true")],
   "void",
   [("r", "768", 2); ("b", "768", 2)],
   [("r", "768", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_add_k3_signature
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC;;

let LOCAL_ADD_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `b:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r b pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,1536; b,1536; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,1536; b,1536; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem768_polyvec_add) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events b r pc (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [r,1536; b,1536; word_sub stackpointer (word 32),32]
                         [r,1536; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,1536);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
