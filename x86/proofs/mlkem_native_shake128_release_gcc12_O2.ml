(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing a SHAKE128 context.                                               *)
(* This is the code for mlkem_shake128_release from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x3440. This   *)
(* zeroes the context of 224 bytes, the 200 bytes of the state padded to a   *)
(* multiple of 32, in the way that gcc inlines a memset of memory whose      *)
(* alignment is not known: it stores zero quadwords at both ends and then    *)
(* clears the quadwords in between from the first multiple of 8 above the    *)
(* start with REP STOSQ. So the specifications assume that the direction     *)
(* flag DF is clear, as the ABI requires on entry.                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3440: mov    QWORD PTR [rdi],0x0
    3447: mov    rdx,rdi
    344a: lea    rdi,[rdi+0x8]
    344e: xor    eax,eax
    3450: mov    QWORD PTR [rdi+0xd0],0x0
    345b: mov    rcx,rdx
    345e: and    rdi,0xfffffffffffffff8
    3462: sub    rcx,rdi
    3465: add    ecx,0xe0
    346b: shr    ecx,0x3
    346e: rep    stos QWORD PTR es:[rdi],rax
    3471: ret
 ***)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3440,0x3472];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The bytes at the ends and those cleared by REP STOSQ,  *)
(* at an offset of 1 to 8 bytes that depends on the alignment of st, are put *)
(* together by MEMSET_PREP_TAC, MEMSET_STEP_TAC and MEMSET_DONE_TAC.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_CORRECT = prove
 (`!st pc.
    aligned 16 (word pc:int64) /\
    nonoverlapping (st,224) (word pc,0x82a0)
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x3440) /\
           C_ARGUMENTS [st] s /\
           (read DF s <=> false))
      (\s. read RIP s = word (pc + 0x3471) /\
           read (memory :> bytes(st,224)) s = 0)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(st,224)])`,
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC (1--10) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC 11 THEN
  MEMSET_DONE_TAC `st:int64` 224 "s11" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!st pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (st,224)) [(word pc,0x82a0); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x3440) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [st] s /\
           (read DF s <=> false))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read (memory :> bytes(st,224)) s = 0)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(st,224)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC
    MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SAFE = time prove
 (`exists f_events.
       forall e st pc.
           aligned 16 (word pc:int64) /\
           nonoverlapping (st,224) (word pc,0x82a0)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3440) /\
                    C_ARGUMENTS [st] s /\
                    (read DF s <=> false) /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x3471) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events st pc /\
                         memaccess_inbounds e2 [st,224] [st,224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,224)])`,
  META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC (1--10) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC 11 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e st pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (st,224)) [word pc,0x82a0; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3440) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    (read DF s <=> false) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events st pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [st,224; stackpointer,8] [st,224]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,224)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC
    MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
