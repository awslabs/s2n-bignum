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
(* address 0x4740, using the theorems for mlkem_keccakf1600_permute at       *)
(* 0x3e70 in the image. The specification is the same as for                 *)
(* sha3_keccak4_f1600, except that the table of round constants is not an    *)
(* argument, since it is part of the image.                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccakf1600_permute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    4740: push   rbx
    4741: mov    rbx,rdi
    4744: call   3e70 <mlkem_keccakf1600_permute>
    4749: lea    rdi,[rbx+0xc8]
    4750: call   3e70 <mlkem_keccakf1600_permute>
    4755: lea    rdi,[rbx+0x190]
    475c: call   3e70 <mlkem_keccakf1600_permute>
    4761: lea    rdi,[rbx+0x258]
    4768: pop    rbx
    4769: jmp    3e70 <mlkem_keccakf1600_permute>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x4740,0x476e];;

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
  let tac = X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) in
  fun atm n ->
    tac [`read RDI s`; atm; `pc:num`; `read RSP s`;
         `read (memory :> bytes64(read RSP s)) s`] n THENL
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
        aligned 16 (word pc:int64) /\
        nonoverlapping (a,800) (word pc,0x82a0) /\
        ALL (nonoverlapping (word_sub stackpointer (word 272),280))
            [(word pc,0x82a0); (a,800)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x4740) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s = A4)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(a,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s =
                  keccak 24 A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s =
                  keccak 24 A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s =
                  keccak 24 A4)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `A1:int64 list`; `A2:int64 list`; `A3:int64 list`;
    `A4:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_TAC `A1:int64 list` 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_TAC `A2:int64 list` 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_TAC `A3:int64 list` 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_TAC `A4:int64 list` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_KECCAK_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (a,800) (word pc,0x82a0) /\
           ALL (nonoverlapping (word_sub stackpointer (word 272),280))
               [(word pc,0x82a0); (a,800)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x4740) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 272))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,800; word (pc + 0x80c0),192;
                           word_sub stackpointer (word 272),280]
                          [a,800; word_sub stackpointer (word 272),272]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(a,800);
                  memory :> bytes(word_sub stackpointer (word 272),272)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_KECCAK" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 4 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 7 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_SAFETY_TAC "H_KECCAK" 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
