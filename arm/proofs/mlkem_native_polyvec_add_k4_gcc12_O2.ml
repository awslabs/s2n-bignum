(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of vectors of 4 polynomials, coefficientwise with wraparound.    *)
(* This is the code for mlkem1024_polyvec_add from mlkem-native's portable C *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_add for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see                       *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x1970, using  *)
(* the theorems for mlkem_poly_add at 0x41e0 in the image.                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_add_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    1970: stp     x19, x20, [sp, #-32]!
    1974: mov     x20, x1
    1978: mov     x19, #0x0
    197c: stp     x21, x30, [sp, #16]
    1980: mov     x21, x0
    1984: add     x1, x20, x19
    1988: add     x0, x21, x19
    198c: add     x19, x19, #0x200
    1990: bl      41e0 <mlkem_poly_add>
    1994: cmp     x19, #0x800
    1998: b.ne    1984 <mlkem1024_polyvec_add+0x14>
    199c: ldp     x21, x30, [sp, #16]
    19a0: ldp     x19, x20, [sp], #32
    19a4: ret
 ***)

let MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1970,0x19a8];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,2048); (b,2048); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,2048); (b,2048); (word_sub stackpointer (word 32),32)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1970) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,2048);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_ADD_TAC [`read X0 s`; `read X1 s`; `x:num->int16`; `y:num->int16`;
                 `pc:num`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (11--16) THEN
  LOCAL_ADD_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(256 + i)`;
                 `\i. (y:num->int16)(256 + i)`; `pc:num`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (18--23) THEN
  LOCAL_ADD_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(512 + i)`;
                 `\i. (y:num->int16)(512 + i)`; `pc:num`; `read X30 s`] 24 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (25--30) THEN
  LOCAL_ADD_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(768 + i)`;
                 `\i. (y:num->int16)(768 + i)`; `pc:num`; `read X30 s`] 31 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (32--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 4 THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_add_k4_signature =
  ([("r", "int16_t[static 1024]", "false");
    ("b", "int16_t[static 1024]", "true")],
   "void",
   [("r", "1024", 2); ("b", "1024", 2)],
   [("r", "1024", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_add_k4_signature
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC;;

let LOCAL_ADD_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `b:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r b pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,2048; b,2048; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,2048; b,2048; word_sub stackpointer (word 32),32]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x1970) /\
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
                         [r,2048; b,2048; word_sub stackpointer (word 32),32]
                         [r,2048; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,2048);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ADD" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (11--16) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 17 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (18--23) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 24 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (25--30) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 31 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_EXEC (32--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
