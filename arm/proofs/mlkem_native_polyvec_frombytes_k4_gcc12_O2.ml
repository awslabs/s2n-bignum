(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 4 polynomials from bytes, 12 bits per            *)
(* coefficient. This is the code for mlkem1024_polyvec_frombytes from        *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md), which calls mlkem_poly_frombytes for each of the *)
(* polynomials, in a loop. It is verified in the whole image (see            *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x17b0, using  *)
(* the theorems for mlkem_poly_frombytes at 0x22a0 in the image.             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_frombytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    17b0: stp     x19, x20, [sp, #-32]!
    17b4: mov     x19, x1
    17b8: mov     x20, x0
    17bc: stp     x21, x30, [sp, #16]
    17c0: add     x21, x1, #0x600
    17c4: mov     x1, x19
    17c8: mov     x0, x20
    17cc: add     x19, x19, #0x180
    17d0: bl      22a0 <mlkem_poly_frombytes>
    17d4: add     x20, x20, #0x200
    17d8: cmp     x19, x21
    17dc: b.ne    17c4 <mlkem1024_polyvec_frombytes+0x14>
    17e0: ldp     x21, x30, [sp, #16]
    17e4: ldp     x19, x20, [sp], #32
    17e8: ret
 ***)

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x17b0,0x17ec];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_FROMBYTES_SPLIT = prove
 (`!a n s j.
        read (memory :> bytes(a,1536)) s = n /\ j < 4
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
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,2048); (a,1536); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,2048); (a,1536); (word_sub stackpointer (word 32),32)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x17b0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,1536)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,2048);
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
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,1536)) s = n`) (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_FROMBYTES_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `4`)))))) [0;1;2;3]
    else failwith "") THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (13--17) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (21--25) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 6144) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (29--33) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 9216) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLYVEC_JOIN_TAC 4 THEN REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[POLYVEC_FROMBYTES_FIELD; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_frombytes_k4_signature =
  ([("r", "int16_t[static 1024]", "false");
    ("a", "uint8_t[static 1536]", "true")],
   "void",
   [("a", "1536", 1)],
   [("r", "1024", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_frombytes_k4_signature
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC;;

let LOCAL_FROMBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,2048; a,1536; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,2048; a,1536; word_sub stackpointer (word 32),32]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x17b0) /\
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
                         [a,1536; r,2048; word_sub stackpointer (word 32),32]
                         [r,2048; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,2048);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
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
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (1--9) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (11--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (13--17) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (19--20) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (21--25) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (27--28) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (29--33) THEN
  LOCAL_FROMBYTES_SAFETY_TAC "H_FROMBYTES" 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (35--36) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_EXEC (37--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
