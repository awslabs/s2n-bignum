(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache for a vector of 3 polynomials.    *)
(* This is the code for mlkem768_polyvec_mulcache_compute from               *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md), which calls mlkem_poly_mulcache_compute     *)
(* for each of the polynomials, the last time as a tail call. It is          *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x5ff0, using the theorems for                     *)
(* mlkem_poly_mulcache_compute at 0x4240 in the image.                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_mulcache_compute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5ff0: stp     x19, x20, [sp, #-32]!
    5ff4: mov     x19, x0
    5ff8: mov     x20, x1
    5ffc: str     x30, [sp, #16]
    6000: bl      4240 <mlkem_poly_mulcache_compute>
    6004: add     x1, x20, #0x200
    6008: add     x0, x19, #0x100
    600c: bl      4240 <mlkem_poly_mulcache_compute>
    6010: ldr     x30, [sp, #16]
    6014: add     x1, x20, #0x400
    6018: add     x0, x19, #0x200
    601c: ldp     x19, x20, [sp], #32
    6020: b       4240 <mlkem_poly_mulcache_compute>
 ***)

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5ff0,0x6024];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!dst src x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(dst,768); (src,1536); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(dst,768); (src,1536); (word_sub stackpointer (word 32),32)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5ff0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add src (word(2 * i))))
                            s = x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 3
                      ==> !i. i < 128
                              ==> let z_i =
                                    read(memory :> bytes16
                                     (word_add dst (word(256 * j + 2 * i)))) s
                                  in (ival z_i ==
                                      mulcache (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival z_i) <= &3328)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(dst,768);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (1--5) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `x:num->int16`; `pc:num`;
                      `read X30 s`] 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (7--9) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(256 + i)`;
                      `pc:num`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (11--15) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(512 + i)`;
                      `pc:num`; `read X30 s`] 16 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_mulcache_compute_k3_signature =
  ([("x", "int16_t[static 384]", "false");
    ("a", "int16_t[static 768]", "true")],
   "void",
   [("a", "768", 2)],
   [("x", "384", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + 0x6380):int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_polyvec_mulcache_compute_k3_signature
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC;;

let LOCAL_MULCACHE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `dst:int64`; `src:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [dst,768; src,1536; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [dst,768; src,1536; word_sub stackpointer (word 32),32]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x5ff0) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events src dst pc
                         (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [src,1536; dst,768;
                          word_sub stackpointer (word 32),32;
                          word (pc + 0x6380),256]
                         [dst,768; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (dst,768);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (1--5) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (7--9) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_EXEC
   (11--15) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 16 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
