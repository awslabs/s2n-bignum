(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache for a vector of 4 polynomials.    *)
(* This is the code for mlkem1024_polyvec_mulcache_compute from mlkem-       *)
(* native's portable C implementation compiled by gcc 12 with -O3 (see       *)
(* mlkem_native/README.md), which calls mlkem_poly_mulcache_compute for each *)
(* of the polynomials, in a loop. It is verified in the whole image (see     *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_poly_mulcache_compute in the image.                                 *)
(* The code is the same as with -O2, but the stack frame is 48 bytes rather *)
(* than 32, since mlkem_poly_mulcache_compute saves D8 on the stack at -O3,  *)
(* and the theorem of constant time and memory safety has the block of       *)
(* constants that mlkem_poly_mulcache_compute reads as a read-only region    *)
(* rather than the zetas.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/poly_mulcache_compute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_mulcache_compute:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: stp     x21, x30, [sp, #16]
      +0x10: add     x21, x0, #0x400
      +0x14: mov     x1, x20
      +0x18: mov     x0, x19
      +0x1c: add     x19, x19, #0x100
      +0x20: bl      <mlkem_poly_mulcache_compute>
      +0x24: add     x20, x20, #0x200
      +0x28: cmp     x19, x21
      +0x2c: b.ne    <mlkem1024_polyvec_mulcache_compute+0x14>
      +0x30: ldp     x21, x30, [sp, #16]
      +0x34: ldp     x19, x20, [sp], #32
      +0x38: ret
 ***)

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem1024_polyvec_mulcache_compute"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!dst src x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(dst,1024); (src,2048); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
          [(dst,1024); (src,2048); (word_sub stackpointer (word 48),48)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_mulcache_compute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add src (word(2 * i))))
                            s = x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 4
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
               [memory :> bytes(dst,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (1--9) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `x:num->int16`; `pc:num`;
                      `read SP s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (13--17) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(256 + i)`;
                      `pc:num`; `read SP s`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (21--25) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(512 + i)`;
                      `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (29--33) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (x:num->int16)(768 + i)`;
                      `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN POLYVEC_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_mulcache_compute_k4_signature =
  ([("x", "int16_t[static 512]", "false");
    ("a", "int16_t[static 1024]", "true")],
   "void",
   [("a", "1024", 2)],
   [("x", "512", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_mulcache_compute_consts):int64`,
                       `mlkem_poly_mulcache_compute_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_polyvec_mulcache_compute_k4_signature
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC;;

let LOCAL_MULCACHE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read SP s`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `dst:int64`; `src:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [dst,1024; src,2048; word_sub stackpointer (word 48),48] /\
           ALLPAIRS nonoverlapping
           [dst,1024; src,2048; word_sub stackpointer (word 48),48]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s =
                      word (pc + mlkem1024_polyvec_mulcache_compute) /\
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
                         (word_sub stackpointer (word 48))
                         returnaddress /\
                         memaccess_inbounds e2
                         [src,2048; dst,1024;
                          word_sub stackpointer (word 48),48;
                          word (pc + mlkem_poly_mulcache_compute_consts),
                          mlkem_poly_mulcache_compute_consts_size]
                         [dst,1024; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (dst,1024);
                 memory :> bytes (word_sub stackpointer (word 48),48)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE
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
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (1--9) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (13--17) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (21--25) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (29--33) THEN
  LOCAL_MULCACHE_SAFETY_TAC "H_MULCACHE" 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_EXEC
   (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
