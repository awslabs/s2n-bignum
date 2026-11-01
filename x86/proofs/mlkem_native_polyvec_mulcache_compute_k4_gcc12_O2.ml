(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache of a vector of 4 polynomials.     *)
(* This is the code for mlkem1024_polyvec_mulcache_compute from              *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md), which calls mlkem_poly_mulcache_compute for each *)
(* of the polynomials, in a loop. It is verified in the whole image (see     *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2190, using  *)
(* the theorems for mlkem_poly_mulcache_compute at 0x5710 in the image.      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_mulcache_compute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2190: push   r12
    2192: lea    r12,[rdi+0x400]
    2199: push   rbp
    219a: mov    rbp,rsi
    219d: push   rbx
    219e: mov    rbx,rdi
    21a1: mov    rsi,rbp
    21a4: mov    rdi,rbx
    21a7: add    rbx,0x100
    21ae: add    rbp,0x200
    21b5: call   5710 <mlkem_poly_mulcache_compute>
    21ba: cmp    rbx,r12
    21bd: jne    21a1 <mlkem1024_polyvec_mulcache_compute+0x11>
    21bf: pop    rbx
    21c0: pop    rbp
    21c1: pop    r12
    21c3: ret
 ***)

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2190,0x21c4];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MULCACHE_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!dst src x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (dst,1024)) [(word pc,0x82a0); (src,2048)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (src,2048); (dst,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2190) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [dst; src] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add src (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 4
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
               [memory :> bytes(dst,1024);
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
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (1--11) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`; `x:num->int16`; `pc:num`;
                      `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 12 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (13--14) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (15--19) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`;
                      `\i. (x:num->int16)(256 + i)`; `pc:num`; `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 20 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (21--22) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (23--27) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`;
                      `\i. (x:num->int16)(512 + i)`; `pc:num`; `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 28 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (29--30) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (31--35) THEN
  LOCAL_MULCACHE_TAC [`read RDI s`; `read RSI s`;
                      `\i. (x:num->int16)(768 + i)`; `pc:num`; `read RSP s`;
                      `read (memory :> bytes64(read RSP s)) s`] 36 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (37--38) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (39--42) THEN
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
       MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `dst:int64`; `src:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (dst,1024)) [(word pc,0x82a0); (src,2048)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,0x82a0); (src,2048); (dst,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2190) /\
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
                          [src,2048; dst,1024; word (pc + 0x81a0),256;
                           word_sub stackpointer (word 32),40]
                          [dst,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(dst,1024);
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
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (1--11) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 12 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (13--14) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (15--19) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 20 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (21--22) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (23--27) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 28 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (29--30) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (31--35) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 36 THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (37--38) THEN
  PTR_DECIDE_RIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_EXEC
   (39--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
