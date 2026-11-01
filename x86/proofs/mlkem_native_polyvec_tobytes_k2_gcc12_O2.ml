(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a vector of 2 polynomials into bytes, 12 bits per coefficient. *)
(* This is the code for mlkem512_polyvec_tobytes from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_tobytes for each of the   *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x5ab0, using the theorems for mlkem_poly_tobytes at 0x3180 in the image. *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_tobytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5ab0: push   rbp
    5ab1: mov    rbp,rsi
    5ab4: push   rbx
    5ab5: mov    rbx,rdi
    5ab8: sub    rsp,0x8
    5abc: call   3180 <mlkem_poly_tobytes>
    5ac1: add    rsp,0x8
    5ac5: lea    rsi,[rbp+0x200]
    5acc: lea    rdi,[rbx+0x180]
    5ad3: pop    rbx
    5ad4: pop    rbp
    5ad5: jmp    3180 <mlkem_poly_tobytes>
 ***)

let MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5ab0,0x5ada];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ALL_SUB_LIST = prove
 (`!P (l:A list) m n. ALL P l ==> ALL P (SUB_LIST(m,n) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; ALL] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; ALL]);;

let POLYVEC_TOBYTES_SPLIT = prove
 (`!a (l:int16 list) s j.
        read (memory :> bytes(a,1024)) s = num_of_wordlist l /\ j < 2
        ==> read (memory :> bytes(word_add a (word(512 * j)),512)) s =
            num_of_wordlist (SUB_LIST(256 * j,256) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_16] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `16 * 256 * j = 8 * 512 * j`;
              ARITH_RULE `16 * 256 = 8 * 512`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_TOBYTES_JOIN = prove
 (`!r (l:int16 list) s.
        LENGTH l = 512 /\
        (!j. j < 2
             ==> read (memory :> bytes(word_add r (word(384 * j)),384)) s =
                 num_of_wordlist
                  (MAP word_zx (SUB_LIST(256 * j,256) l):(12 word)list))
        ==> read (memory :> bytes(r,768)) s =
            num_of_wordlist (MAP word_zx l:(12 word)list)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `l:int16 list =
    APPEND (SUB_LIST(0,256) l) (SUB_LIST(256,256) l)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM SUB_LIST_LENGTH] THEN
    ASM_REWRITE_TAC[ARITH_RULE `512 = 256 + 256`; SUB_LIST_SPLIT] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
              LENGTH_SUB_LIST] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[ARITH_RULE `768 = 384 + 384`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_TOBYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,768)) [(word pc,0x82a0); (a,1024)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (a,1024); (r,768)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x5ab0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,1024)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 512 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,768)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,1024)) s = n`)
           (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_TOBYTES_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `2`)))))) [0;1]
    else failwith "") THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC (1--6) THEN
  LOCAL_TOBYTES_TAC [`read RDI s`; `read RSI s`;
                     `SUB_LIST(0,256) (l:int16 list)`; `pc:num`; `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC (8--13) THEN
  LOCAL_TOBYTES_TAC [`read RDI s`; `read RSI s`;
                     `SUB_LIST(256,256) (l:int16 list)`; `pc:num`;
                     `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC POLYVEC_TOBYTES_JOIN THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST; ALL_SUB_LIST; MIN; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_TOBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,768)) [(word pc,0x82a0); (a,1024)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (a,1024); (r,768)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x5ab0) /\
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
                          [a,1024; r,768; word_sub stackpointer (word 32),40]
                          [r,768; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,768);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_TOBYTES" THEN
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
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC (1--6) THEN
  LOCAL_TOBYTES_SAFETY_TAC "H_TOBYTES" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_EXEC (8--13) THEN
  LOCAL_TOBYTES_SAFETY_TAC "H_TOBYTES" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
