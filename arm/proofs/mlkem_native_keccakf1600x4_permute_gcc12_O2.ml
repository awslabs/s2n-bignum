(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation of four consecutive states.                      *)
(* This is the code for mlkem_keccakf1600x4_permute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_keccakf1600_permute for each   *)
(* of the four states, the last time as a tail call. It is verified in the   *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x33a0, using the theorems for mlkem_keccakf1600_permute at       *)
(* 0x2dd0 in the image. The specification is the same as for                 *)
(* sha3_keccak4_f1600, except that the table of round constants is not an    *)
(* argument, since it is part of the image.                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccakf1600_permute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    33a0: stp     x19, x30, [sp, #-16]!
    33a4: mov     x19, x0
    33a8: bl      2dd0 <mlkem_keccakf1600_permute>
    33ac: add     x0, x19, #0xc8
    33b0: bl      2dd0 <mlkem_keccakf1600_permute>
    33b4: add     x0, x19, #0x190
    33b8: bl      2dd0 <mlkem_keccakf1600_permute>
    33bc: add     x0, x19, #0x258
    33c0: ldp     x19, x30, [sp], #16
    33c4: b       2dd0 <mlkem_keccakf1600_permute>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x33a0,0x33c8];;

(* ------------------------------------------------------------------------- *)
(* The four calls of mlkem_keccakf1600_permute, keeping the states in memory *)
(* as numbers so that they are carried through the steps.                    *)
(* ------------------------------------------------------------------------- *)

let WORDLIST_FROM_MEMORY_25 = prove
 (`!a s (l:int64 list).
        wordlist_from_memory(a,25) s = l <=>
        LENGTH l = 25 /\ read (memory :> bytes(a,200)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_EQ_ALT THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;

let LOCAL_KECCAK_TAC =
  let tac = ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) in
  fun atm n ->
    tac [`read X0 s`; atm; `pc:num`; `read SP s`; `read X30 s`] n THENL
     [REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check
       (can (term_match [] `wordlist_from_memory(a,25) s:int64 list = l`) o
        concl)) THEN
      REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a A1 A2 A3 A4 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x33a0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s = A4)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s =
                  keccak 24 A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s =
                  keccak 24 A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s =
                  keccak 24 A4)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 208),208)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `A1:int64 list`; `A2:int64 list`; `A3:int64 list`;
    `A4:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 208 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_TAC `A1:int64 list` 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_TAC `A2:int64 list` 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_TAC `A3:int64 list` 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_TAC `A4:int64 list` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_keccakf1600x4_permute_signature =
  ([("a", "uint64_t[static 100]", "false")],
   "void",
   [("a", "100", 8)],
   [("a", "100", 8)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + 0x62b0):int64`,`192`]
    ~keep_maychanges:true
    mlkem_native_keccakf1600x4_permute_signature
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC;;

let LOCAL_KECCAK_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 208),208]
           [word pc,0x6480]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x33a0) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,800; word_sub stackpointer (word 208),208;
                          word (pc + 0x62b0),192]
                         [a,800; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,800);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_KECCAK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 7 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same for the four states as 1600-bit words, read by wbytes, with the  *)
(* permutation keccak_f1600 of common/fips202.ml, as for                     *)
(* mlkem_keccakf1600_permute.                                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600
  = prove
 (`!a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,0x6480)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x33a0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  keccak_f1600 S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  keccak_f1600 S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  keccak_f1600 S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 208),208)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`a:int64`; `wordlist_of_num 25 (val(S0:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (MESON[ENSURES_PREPOSTCONDITION_THM]
   `ensures step P Q C
    ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
        ==> ensures step P' Q' C`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;
