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
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x7720, using  *)
(* the theorems for mlkem_poly_add at 0x56b0 in the image.                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_add_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    7720: push   rbp
    7721: mov    rbp,rsi
    7724: push   rbx
    7725: mov    rbx,rdi
    7728: sub    rsp,0x8
    772c: call   56b0 <mlkem_poly_add>
    7731: lea    rsi,[rbp+0x200]
    7738: lea    rdi,[rbx+0x200]
    773f: call   56b0 <mlkem_poly_add>
    7744: add    rsp,0x8
    7748: lea    rsi,[rbp+0x400]
    774f: lea    rdi,[rbx+0x400]
    7756: pop    rbx
    7757: pop    rbp
    7758: jmp    56b0 <mlkem_poly_add>
 ***)

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x7720,0x775d];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r b x y pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
        ALL (nonoverlapping (r,1536)) [(word pc,0x82a0); (b,1536)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (b,1536); (r,1536)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x7720) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 768
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 768
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1536);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ALIGNED_OFFSETS_TAC `r:int64` 16 [512; 1024] THEN
  ALIGNED_OFFSETS_TAC `b:int64` 16 [512; 1024] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 3 THEN POLYVEC_SPLIT_TAC 3 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (1--6) THEN
  LOCAL_ADD_TAC [`read RDI s`; `read RSI s`; `x:num->int16`; `y:num->int16`;
                 `pc:num`; `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_ADD_TAC [`read RDI s`; `read RSI s`; `\i. (x:num->int16)(256 + i)`;
                 `\i. (y:num->int16)(256 + i)`; `pc:num`; `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (12--17) THEN
  LOCAL_ADD_TAC [`read RDI s`; `read RSI s`; `\i. (x:num->int16)(512 + i)`;
                 `\i. (y:num->int16)(512 + i)`; `pc:num`; `read RSP s`;
                 `read (memory :> bytes64(read RSP s)) s`] 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 3 THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_ADD_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `b:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
           ALL (nonoverlapping (r,1536)) [(word pc,0x82a0); (b,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (b,1536); (r,1536)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x7720) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r b pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [b,1536; r,1536; word_sub stackpointer (word 32),40]
                          [r,1536; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1536);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `b:int64`;
                       `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ALIGNED_OFFSETS_TAC `r:int64` 16 [512; 1024] THEN
  ALIGNED_OFFSETS_TAC `b:int64` 16 [512; 1024] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (1--6) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_EXEC (12--17) THEN
  LOCAL_ADD_SAFETY_TAC "H_ADD" 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
