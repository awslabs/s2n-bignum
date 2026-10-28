(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a vector of 3 polynomials into bytes, 12 bits per coefficient. *)
(* This is the code for mlkem768_polyvec_tobytes from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_tobytes for each of the   *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x5e90, using the theorems for mlkem_poly_tobytes at 0x2260 in the image. *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_tobytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5e90: stp     x19, x20, [sp, #-32]!
    5e94: mov     x19, x0
    5e98: mov     x20, x1
    5e9c: str     x30, [sp, #16]
    5ea0: bl      2260 <mlkem_poly_tobytes>
    5ea4: add     x1, x20, #0x200
    5ea8: add     x0, x19, #0x180
    5eac: bl      2260 <mlkem_poly_tobytes>
    5eb0: ldr     x30, [sp, #16]
    5eb4: add     x1, x20, #0x400
    5eb8: add     x0, x19, #0x300
    5ebc: ldp     x19, x20, [sp], #32
    5ec0: b       2260 <mlkem_poly_tobytes>
 ***)

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5e90,0x5ec4];;

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
        read (memory :> bytes(a,1536)) s = num_of_wordlist l /\ j < 3
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
        LENGTH l = 768 /\
        (!j. j < 3
             ==> read (memory :> bytes(word_add r (word(384 * j)),384)) s =
                 num_of_wordlist
                  (MAP word_zx (SUB_LIST(256 * j,256) l):(12 word)list))
        ==> read (memory :> bytes(r,1152)) s =
            num_of_wordlist (MAP word_zx l:(12 word)list)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `l:int16 list =
    APPEND (SUB_LIST(0,256) l)
           (APPEND (SUB_LIST(256,256) l) (SUB_LIST(512,256) l))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM SUB_LIST_LENGTH] THEN
    ASM_REWRITE_TAC[ARITH_RULE `768 = 256 + 256 + 256`; SUB_LIST_SPLIT] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
              LENGTH_SUB_LIST] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[ARITH_RULE `1152 = 384 + 384 + 384`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1152); (a,1536); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1152); (a,1536); (word_sub stackpointer (word 32),32)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5e90) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,1536)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 768 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,1152)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1152);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
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
    if can (term_match [] `read (memory :> bytes(a,1536)) s = n`) (concl th)
    then MAP_EVERY (fun j ->
      ASSUME_TAC(CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP POLYVEC_TOBYTES_SPLIT
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral j) `3`)))))) [0;1;2]
    else failwith "") THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC (1--5) THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`;
                     `SUB_LIST(0,256) (l:int16 list)`;
                     `pc:num`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC (7--9) THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`;
                     `SUB_LIST(256,256) (l:int16 list)`;
                     `pc:num`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC (11--15) THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`;
                     `SUB_LIST(512,256) (l:int16 list)`;
                     `pc:num`; `read X30 s`] 16 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC POLYVEC_TOBYTES_JOIN THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST; ALL_SUB_LIST; MIN; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_tobytes_k3_signature =
  ([("r", "uint8_t[static 1152]", "false");
    ("a", "int16_t[static 768]", "true")],
   "void",
   [("a", "768", 2)],
   [("r", "1152", 1)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_tobytes_k3_signature
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC;;

let LOCAL_TOBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,1152; a,1536; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,1152; a,1536; word_sub stackpointer (word 32),32]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x5e90) /\
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
                         [a,1536; r,1152; word_sub stackpointer (word 32),32]
                         [r,1152; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,1152);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_TOBYTES" THEN
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
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC
   (1--5) THEN
  LOCAL_TOBYTES_SAFETY_TAC "H_TOBYTES" 6 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC
   (7--9) THEN
  LOCAL_TOBYTES_SAFETY_TAC "H_TOBYTES" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC
   (11--15) THEN
  LOCAL_TOBYTES_SAFETY_TAC "H_TOBYTES" 16 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
