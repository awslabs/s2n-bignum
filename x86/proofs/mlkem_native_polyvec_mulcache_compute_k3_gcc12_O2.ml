(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache of a vector of 3 polynomials.     *)
(* This is the code for mlkem768_polyvec_mulcache_compute from               *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md), which calls mlkem_poly_mulcache_compute for each *)
(* of the polynomials, the last time as a tail call. It is verified in the   *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x76b0, using the theorems for mlkem_poly_mulcache_compute at     *)
(* 0x5710 in the image.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_mulcache_compute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    76b0: push   rbp
    76b1: mov    rbp,rsi
    76b4: push   rbx
    76b5: mov    rbx,rdi
    76b8: sub    rsp,0x8
    76bc: call   5710 <mlkem_poly_mulcache_compute>
    76c1: lea    rsi,[rbp+0x200]
    76c8: lea    rdi,[rbx+0x100]
    76cf: call   5710 <mlkem_poly_mulcache_compute>
    76d4: add    rsp,0x8
    76d8: lea    rsi,[rbp+0x400]
    76df: lea    rdi,[rbx+0x200]
    76e6: pop    rbx
    76e7: pop    rbp
    76e8: jmp    5710 <mlkem_poly_mulcache_compute>
 ***)

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x76b0,0x76ed];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MULCACHE_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!dst src x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (dst,768)) [(word pc,0x82a0); (src,1536)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (src,1536); (dst,768)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x76b0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [dst; src] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add src (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 3
                      ==> !i. i < 128
                              ==> let z_i =
                                    read(memory :> bytes16
                                     (word_add dst (word(256 * j + 2 * i)))) s
                                  in (ival z_i ==
                                      mulcache (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival z_i) <= &3328)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(dst,768);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 3 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (1--6) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`; `x:num->int16`; `pc:num`;
                      `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (8--10) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`;
                      `\i. (x:num->int16)(256 + i)`; `pc:num`; `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (12--17) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`;
                      `\i. (x:num->int16)(512 + i)`; `pc:num`; `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_MULCACHE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `dst:int64`; `src:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (dst,768)) [(word pc,0x82a0); (src,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (src,1536); (dst,768)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x76b0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events dst src pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [src,1536; dst,768; word (pc + 0x81a0),256;
                           word_sub stackpointer (word 32),40]
                          [dst,768; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(dst,768);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `dst:int64`; `src:int64`;
                       `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (1--6) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (8--10) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 11 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (12--17) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 18 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
