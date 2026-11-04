(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a vector of 2 polynomials from 10 bits per coefficient.  *)
(* This is the code for mlkem512_polyvec_decompress_du from mlkem-native's   *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_decompress_d10 for each   *)
(* of the polynomials, the last time as a tail call. It is verified in the   *)
(* whole image (see libmlkem.ml), using the theorems                         *)
(* for mlkem_poly_decompress_d10 in the image.                               *)
(*                                                                           *)
(* Unlike at -O2, mlkem_poly_decompress_d10 loads no constants, so the       *)
(* safety theorem has no read-only region for them.                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/poly_decompress_d10.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_decompress_du:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: str     x30, [sp, #16]
      +0x10: bl      <mlkem_poly_decompress_d10>
      +0x14: ldr     x30, [sp, #16]
      +0x18: add     x1, x20, #0x140
      +0x1c: add     x0, x19, #0x200
      +0x20: ldp     x19, x20, [sp], #32
      +0x24: b       <mlkem_poly_decompress_d10>
 ***)

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem512_polyvec_decompress_du"];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_DECOMPRESS_DU_SPLIT = prove
 (`!a n s j.
        read (memory :> bytes(a,640)) s = n /\ j < 2
        ==> read (memory :> bytes(word_add a (word(320 * j)),320)) s =
            (n DIV 2 EXP (2560 * j)) MOD 2 EXP 2560`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `2560 * j = 8 * 320 * j`;
              ARITH_RULE `2560 = 8 * 320`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_DECOMPRESS_DU_FIELD = prove
 (`!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2560 DIV 2 EXP (10 * i)) MOD 2 EXP 10 =
            (n DIV 2 EXP (k + 10 * i)) MOD 2 EXP 10`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 2560 (10 * i + 10) = 10 * i + 10`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DECOMPRESS_D10_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1024); (a,640); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1024); (a,640); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem512_polyvec_decompress_du) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,640)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,640)) s = n`) (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_DECOMPRESS_DU_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `2`)))))) [0;1]
    else failwith "") THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC (1--5) THEN
  LOCAL_DECOMPRESS_D10_TAC [`read X0 s`; `read X1 s`;
                            `(n DIV 2 EXP 0) MOD 2 EXP 2560`; `pc:num`;
                            `read X30 s`] 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC
   (7--11) THEN
  LOCAL_DECOMPRESS_D10_TAC [`read X0 s`; `read X1 s`;
                            `(n DIV 2 EXP 2560) MOD 2 EXP 2560`; `pc:num`;
                            `read X30 s`] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 2 THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[POLYVEC_DECOMPRESS_DU_FIELD; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_decompress_du_k2_signature =
  ([("r", "int16_t[static 512]", "false");
    ("a", "uint8_t[static 640]", "true")],
   "void",
   [("a", "640", 1)],
   [("r", "512", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_decompress_du_k2_signature
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC;;

let LOCAL_DECOMPRESS_D10_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,1024; a,640; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,1024; a,640; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem512_polyvec_decompress_du) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a r pc (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,640; r,1024; word_sub stackpointer (word 32),32]
                         [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,1024);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_D10" THEN
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
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC (1--5) THEN
  LOCAL_DECOMPRESS_D10_SAFETY_TAC "H_DECOMPRESS_D10" 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_EXEC
   (7--11) THEN
  LOCAL_DECOMPRESS_D10_SAFETY_TAC "H_DECOMPRESS_D10" 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
