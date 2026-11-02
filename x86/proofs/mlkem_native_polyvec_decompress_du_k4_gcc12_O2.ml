(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a vector of 4 polynomials from 11 bits per coefficient.  *)
(* This is the code for mlkem1024_polyvec_decompress_du from mlkem-native's  *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_decompress_d11 for each   *)
(* of the polynomials, in a loop. It is verified in the whole image (see     *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x1f80, using  *)
(* the theorems for mlkem_poly_decompress_d11 at 0x2fe0 in the image.        *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_decompress_d11_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    1f80: push   r12
    1f82: lea    r12,[rsi+0x580]
    1f89: push   rbp
    1f8a: mov    rbp,rdi
    1f8d: push   rbx
    1f8e: mov    rbx,rsi
    1f91: mov    rsi,rbx
    1f94: mov    rdi,rbp
    1f97: add    rbx,0x160
    1f9e: add    rbp,0x200
    1fa5: call   2fe0 <mlkem_poly_decompress_d11>
    1faa: cmp    rbx,r12
    1fad: jne    1f91 <mlkem1024_polyvec_decompress_du+0x11>
    1faf: pop    rbx
    1fb0: pop    rbp
    1fb1: pop    r12
    1fb3: ret
 ***)

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1f80,0x1fb4];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_DECOMPRESS_DU_SPLIT = prove
 (`!a n s j.
        read (memory :> bytes(a,1408)) s = n /\ j < 4
        ==> read (memory :> bytes(word_add a (word(352 * j)),352)) s =
            (n DIV 2 EXP (2816 * j)) MOD 2 EXP 2816`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `2816 * j = 8 * 352 * j`;
              ARITH_RULE `2816 = 8 * 352`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_DECOMPRESS_DU_FIELD = prove
 (`!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2816 DIV 2 EXP (11 * i)) MOD 2 EXP 11 =
            (n DIV 2 EXP (k + 11 * i)) MOD 2 EXP 11`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 2816 (11 * i + 11) = 11 * i + 11`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DECOMPRESS_D11_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 r /\
        ALL (nonoverlapping (r,2048)) [(word pc,0x82a0); (a,1408)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),72))
            [(word pc,0x82a0); (a,1408); (r,2048)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x1f80) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,1408)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,2048);
                memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ALIGNED_OFFSETS_TAC `r:int64` 16 [512; 1024; 1536] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,1408)) s = n`)
           (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_DECOMPRESS_DU_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `4`)))))) [0;1;2;3]
    else failwith "") THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (1--11) THEN
  LOCAL_DECOMPRESS_D11_TAC [`read RDI s`; `read RSI s`;
                            `(n DIV 2 EXP 0) MOD 2 EXP 2816`; `pc:num`;
                            `read RSP s`;
                            `read (memory :> bytes64(read RSP s)) s`] 12 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (13--14) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (15--19) THEN
  LOCAL_DECOMPRESS_D11_TAC [`read RDI s`; `read RSI s`;
                            `(n DIV 2 EXP 2816) MOD 2 EXP 2816`; `pc:num`;
                            `read RSP s`;
                            `read (memory :> bytes64(read RSP s)) s`] 20 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (21--22) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (23--27) THEN
  LOCAL_DECOMPRESS_D11_TAC [`read RDI s`; `read RSI s`;
                            `(n DIV 2 EXP 5632) MOD 2 EXP 2816`; `pc:num`;
                            `read RSP s`;
                            `read (memory :> bytes64(read RSP s)) s`] 28 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (29--30) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (31--35) THEN
  LOCAL_DECOMPRESS_D11_TAC [`read RDI s`; `read RSI s`;
                            `(n DIV 2 EXP 8448) MOD 2 EXP 2816`; `pc:num`;
                            `read RSP s`;
                            `read (memory :> bytes64(read RSP s)) s`] 36 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (37--38) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (39--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 4 THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[POLYVEC_DECOMPRESS_DU_FIELD; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_DECOMPRESS_D11_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 r /\
           ALL (nonoverlapping (r,2048)) [(word pc,0x82a0); (a,1408)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 64),72))
               [(word pc,0x82a0); (a,1408); (r,2048)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x1f80) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 64))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1408; r,2048; word (pc + 0x8050),16;
                           word (pc + 0x8060),16;
                           word_sub stackpointer (word 64),72]
                          [r,2048; word_sub stackpointer (word 64),64]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,2048);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_D11" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`;
                       `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ALIGNED_OFFSETS_TAC `r:int64` 16 [512; 1024; 1536] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (1--11) THEN
  LOCAL_DECOMPRESS_D11_SAFETY_TAC "H_DECOMPRESS_D11" 12 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (13--14) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (15--19) THEN
  LOCAL_DECOMPRESS_D11_SAFETY_TAC "H_DECOMPRESS_D11" 20 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (21--22) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (23--27) THEN
  LOCAL_DECOMPRESS_D11_SAFETY_TAC "H_DECOMPRESS_D11" 28 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (29--30) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (31--35) THEN
  LOCAL_DECOMPRESS_D11_SAFETY_TAC "H_DECOMPRESS_D11" 36 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (37--38) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_EXEC
   (39--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
