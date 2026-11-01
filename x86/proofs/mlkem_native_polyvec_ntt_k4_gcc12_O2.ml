(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 4 polynomials.          *)
(* This is the code for mlkem1024_polyvec_ntt from mlkem-native's portable C *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_ntt for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see                       *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2040, using  *)
(* the theorems for mlkem_poly_ntt at 0x5780 in the image.                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_ntt_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2040: push   rbx
    2041: mov    rbx,rdi
    2044: call   5780 <mlkem_poly_ntt>
    2049: lea    rdi,[rbx+0x200]
    2050: call   5780 <mlkem_poly_ntt>
    2055: lea    rdi,[rbx+0x400]
    205c: call   5780 <mlkem_poly_ntt>
    2061: lea    rdi,[rbx+0x600]
    2068: pop    rbx
    2069: jmp    5780 <mlkem_poly_ntt>
 ***)

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2040,0x206e];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_NTT_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (a,2048) (word pc,0x82a0) /\
        ALL (nonoverlapping (word_sub stackpointer (word 68),76))
            [(word pc,0x82a0); (a,2048)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2040) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 4 /\
                      (!i. i < 256 ==> abs(ival(x(256 * j + i))) <= &8191)
                      ==> !i. i < 256
                              ==> let zi =
                                    read(memory :> bytes16
                                     (word_add a (word(512 * j + 2 * i)))) s
                                  in (ival zi ==
                                      forward_ntt (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival zi) <= &23594)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,2048);
                memory :> bytes(word_sub stackpointer (word 68),68)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 68 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (1--3) THEN
  LOCAL_NTT_TAC [`read RDI s`; `x:num->int16`; `pc:num`; `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (5--6) THEN
  LOCAL_NTT_TAC [`read RDI s`; `\i. (x:num->int16)(256 + i)`; `pc:num`;
                 `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (8--9) THEN
  LOCAL_NTT_TAC [`read RDI s`; `\i. (x:num->int16)(512 + i)`; `pc:num`;
                 `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (11--13) THEN
  LOCAL_NTT_TAC [`read RDI s`; `\i. (x:num->int16)(768 + i)`; `pc:num`;
                 `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_NTT_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (a,2048) (word pc,0x82a0) /\
           ALL (nonoverlapping (word_sub stackpointer (word 68),76))
               [(word pc,0x82a0); (a,2048)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2040) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 68))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,2048; word (pc + 0x81a0),256;
                           word_sub stackpointer (word 68),76]
                          [a,2048; word_sub stackpointer (word 68),68]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(a,2048);
                  memory :> bytes(word_sub stackpointer (word 68),68)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 68 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (1--3) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (5--6) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (8--9) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_EXEC (11--13) THEN
  LOCAL_NTT_SAFETY_TAC "H_NTT" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
