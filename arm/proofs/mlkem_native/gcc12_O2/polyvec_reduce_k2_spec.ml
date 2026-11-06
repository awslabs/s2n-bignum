(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Barrett reduction of a vector of 2 polynomials. This is the code for      *)
(* mlkem512_polyvec_reduce from mlkem-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which calls     *)
(* mlkem_poly_reduce for each of the polynomials, the last time as a tail    *)
(* call. It is verified in the whole image (see                              *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_poly_reduce in the image.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_reduce:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: bl      <mlkem_poly_reduce>
       +0xc: add     x0, x19, #0x200
      +0x10: ldp     x19, x30, [sp], #16
      +0x14: b       <mlkem_poly_reduce>
 ***)

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem512_polyvec_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,1024) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
          [(a,1024); (word_sub stackpointer (word 16),16)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem512_polyvec_reduce) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 512
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_reduce_k2_signature =
  ([("a", "int16_t[static 512]", "false")],
   "void",
   [("a", "512", 2)],
   [("a", "512", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_reduce_k2_signature
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_EXEC;;

let LOCAL_REDUCE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,1024) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
           [a,1024; word_sub stackpointer (word 16),16]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem512_polyvec_reduce) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 16))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,1024; word_sub stackpointer (word 16),16]
                         [a,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (a,1024);
                 memory :> bytes (word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_poly_reduce, for mlkem512_check_pk, whose result the             *)
(* encapsulation branches on.                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FULL_TAC ilist n =
  REMOVE_THEN "H_POLY" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_POLY" safety_th]);;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,1024) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
          [(a,1024); (word_sub stackpointer (word 16),16)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem512_polyvec_reduce) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 512
                       ==> read(memory :> bytes16
                            (word_add a (word(2 * i)))) s =
                           x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 512
                       ==> ival(read(memory :> bytes16
                                  (word_add a (word(2 * i)))) s) =
                           ival(x i) rem &3329) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 =
                     f_events a pc (word_sub stackpointer (word 16))
                     returnaddress /\
                     memaccess_inbounds e2
                     [a,1024; word_sub stackpointer (word 16),16]
                     [a,1024; word_sub stackpointer (word 16),16]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
