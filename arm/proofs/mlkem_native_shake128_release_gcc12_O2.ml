(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Release of a SHAKE128 context. This is the code for                       *)
(* mlkem_shake128_release from mlkem-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which zeroes    *)
(* the context of 224 bytes, the 200 bytes of the state padded to a multiple *)
(* of 32. It is verified in the whole image (see                             *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2544.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2544: movi    v0.4s, #0x0
    2548: stp     q0, q0, [x0]
    254c: stp     q0, q0, [x0, #32]
    2550: stp     q0, q0, [x0, #64]
    2554: stp     q0, q0, [x0, #96]
    2558: stp     q0, q0, [x0, #128]
    255c: stp     q0, q0, [x0, #160]
    2560: stp     q0, q0, [x0, #192]
    2564: ret
 ***)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2544,0x2568];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!st pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        nonoverlapping (st,224) (word pc,0x6480)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2544) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(st,224)) s = 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(st,224)])`,
  let zl = mk_list(replicate `word 0:int64` 28,`:int64`) in
  let zth = prove
   (mk_eq(`0`,mk_comb(`num_of_wordlist:int64 list->num`,zl)),
    REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC) in
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes128 a) s = word 0`) (concl th)
    then CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                   ONCE_DEPTH_CONV WORD_REDUCE_CONV) th
    else th) THEN
  GEN_REWRITE_TAC RAND_CONV [zth] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e st pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           nonoverlapping (st,224) (word pc,0x6480)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2544) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events st pc returnaddress /\
                         memaccess_inbounds e2 [st,224] [st,224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,224)])`,
  PROVE_SAFETY_SPEC_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC);;
