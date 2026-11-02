(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 3 polynomials to 10 bits per coefficient.      *)
(* This is the code for mlkem768_polyvec_compress_du from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d10 for each of  *)
(* the polynomials, the last time as a tail call. It is verified in the      *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x7470, using the theorems for mlkem_poly_compress_d10 at 0x2660  *)
(* in the image.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_compress_d10_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    7470: push   rbp
    7471: mov    rbp,rsi
    7474: push   rbx
    7475: mov    rbx,rdi
    7478: sub    rsp,0x8
    747c: call   2660 <mlkem_poly_compress_d10>
    7481: lea    rsi,[rbp+0x200]
    7488: lea    rdi,[rbx+0x140]
    748f: call   2660 <mlkem_poly_compress_d10>
    7494: add    rsp,0x8
    7498: lea    rsi,[rbp+0x400]
    749f: lea    rdi,[rbx+0x280]
    74a6: pop    rbx
    74a7: pop    rbp
    74a8: jmp    2660 <mlkem_poly_compress_d10>
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x7470,0x74ad];;

(* ------------------------------------------------------------------------- *)
(* The output for the vector from those for the polynomials.                 *)
(* ------------------------------------------------------------------------- *)

let NSUM_SHIFT_EXP = prove
 (`!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM NSUM_LMUL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let POLYVEC_COMPRESS_DU_JOIN = prove
 (`!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 640),320)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,960)) s =
         nsum {i | i < 768} (\i. g i * 2 EXP (10 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `960 = 320 + 320 + 320`;
              ARITH_RULE `768 = 256 + 256 + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[NSUM_SHIFT_EXP] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `5120 = 2560 + 2560`; EXP_ADD] THEN
  SPEC_TAC(`2 EXP 2560`,`e:num`) THEN CONV_TAC NUM_RING);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_COMPRESS_D10_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,960)) [(word pc,0x82a0); (a,1536)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),80))
            [(word pc,0x82a0); (a,1536); (r,960)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x7470) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 768 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,960)) s =
                       nsum {i | i < 768}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,960);
                memory :> bytes(word_sub stackpointer (word 72),72)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 72 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 3 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (1--6) THEN
  LOCAL_COMPRESS_D10_TAC [`read RDI s`; `read RSI s`; `x:num->int16`; `pc:num`;
                          `read RSP s`;
                          `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_COMPRESS_D10_TAC [`read RDI s`; `read RSI s`;
                          `\i. (x:num->int16)(256 + i)`; `pc:num`;
                          `read RSP s`;
                          `read (memory :> bytes64(read RSP s)) s`] 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (12--17) THEN
  LOCAL_COMPRESS_D10_TAC [`read RDI s`; `read RSI s`;
                          `\i. (x:num->int16)(512 + i)`; `pc:num`;
                          `read RSP s`;
                          `read (memory :> bytes64(read RSP s)) s`] 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN POLYVEC_SPLIT_TAC 3 THEN
  MATCH_MP_TAC(BETA_RULE(SPEC
   `\i. ((2048 * val((x:num->int16) i) + 3329) DIV 6658) MOD 1024`
   (SPECL [`r:int64`; `s18:x86state`] POLYVEC_COMPRESS_DU_JOIN))) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_COMPRESS_D10_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,960)) [(word pc,0x82a0); (a,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 72),80))
               [(word pc,0x82a0); (a,1536); (r,960)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x7470) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 72))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1536; r,960; word_sub stackpointer (word 72),80]
                          [r,960; word_sub stackpointer (word 72),72]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,960);
                  memory :> bytes(word_sub stackpointer (word 72),72)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_D10" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`;
                       `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 72 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (1--6) THEN
  LOCAL_COMPRESS_D10_SAFETY_TAC "H_COMPRESS_D10" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (8--10) THEN
  LOCAL_COMPRESS_D10_SAFETY_TAC "H_COMPRESS_D10" 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC (12--17) THEN
  LOCAL_COMPRESS_D10_SAFETY_TAC "H_COMPRESS_D10" 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
