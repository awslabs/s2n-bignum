(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 2 polynomials from bytes, 12 bits per            *)
(* coefficient.                                                              *)
(* This is the code for mlkem512_polyvec_frombytes from mlkem-native's       *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_frombytes for each of the *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x5ae0, using the theorems for mlkem_poly_frombytes at 0x31c0 in the      *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_frombytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5ae0: push   rbp
    5ae1: mov    rbp,rsi
    5ae4: push   rbx
    5ae5: mov    rbx,rdi
    5ae8: sub    rsp,0x8
    5aec: call   31c0 <mlkem_poly_frombytes>
    5af1: add    rsp,0x8
    5af5: lea    rsi,[rbp+0x180]
    5afc: lea    rdi,[rbx+0x200]
    5b03: pop    rbx
    5b04: pop    rbp
    5b05: jmp    31c0 <mlkem_poly_frombytes>
 ***)

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5ae0,0x5b0a];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_FROMBYTES_SPLIT = prove
 (`!a n s j.
        read (memory :> bytes(a,768)) s = n /\ j < 2
        ==> read (memory :> bytes(word_add a (word(384 * j)),384)) s =
            (n DIV 2 EXP (3072 * j)) MOD 2 EXP 3072`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `3072 * j = 8 * 384 * j`;
              ARITH_RULE `3072 = 8 * 384`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_FROMBYTES_FIELD = prove
 (`!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD 2 EXP 12 =
            (n DIV 2 EXP (k + 12 * i)) MOD 2 EXP 12`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 3072 (12 * i + 12) = 12 * i + 12`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,1024)) [(word pc,0x82a0); (a,768)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (a,768); (r,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x5ae0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,768)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,768)) s = n`)
           (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_FROMBYTES_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `2`)))))) [0;1]
    else failwith "") THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (1--6) THEN
  LOCAL_FROMBYTES_TAC [`read RDI s`; `read RSI s`;
                       `(n DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`;
                       `read RSP s`;
                       `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (8--13) THEN
  LOCAL_FROMBYTES_TAC [`read RDI s`; `read RSI s`;
                       `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`;
                       `read RSP s`;
                       `read (memory :> bytes64(read RSP s)) s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 2 THEN REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[POLYVEC_FROMBYTES_FIELD; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_FROMBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1024)) [(word pc,0x82a0); (a,768)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (a,768); (r,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x5ae0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,768; r,1024; word_sub stackpointer (word 32),40]
                          [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1024);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`;
                       `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (1--6) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (8--13) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_poly_frombytes, for mlkem512_check_pk, whose result the          *)
(* encapsulation branches on.                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FULL_TAC ilist n =
  REMOVE_THEN "H_POLY" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_POLY" safety_th]);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  time prove
 (`exists f_events.
       forall e r a n pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1024)) [(word pc,0x82a0); (a,768)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (a,768); (r,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x5ae0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,768)) s = n /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 512
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,768; r,1024; word_sub stackpointer (word 32),40]
                          [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1024);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,768)) s = n`)
           (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_FROMBYTES_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `2`)))))) [0;1]
    else failwith "") THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (1--6) THEN
  LOCAL_FULL_TAC [`read RDI s`; `read RSI s`;
                  `(n DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`;
                  `read RSP s`;
                  `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC (8--13) THEN
  LOCAL_FULL_TAC [`read RDI s`; `read RSI s`;
                  `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`;
                  `read RSP s`;
                  `read (memory :> bytes64(read RSP s)) s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  POLYVEC_JOIN_TAC 2 THEN REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[POLYVEC_FROMBYTES_FIELD; ADD_CLAUSES]);;
