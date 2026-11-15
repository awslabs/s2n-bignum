(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing a context of four SHAKE128 states. This is the code for           *)
(* mlkem_shake128x4_release from mlkem-native's portable C implementation    *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml). This zeroes the 800 bytes of the    *)
(* context in the way that gcc inlines a memset of memory whose alignment is *)
(* not known: it stores zero quadwords at both ends and then clears the      *)
(* quadwords in between from the first multiple of 8 above the start with    *)
(* REP STOSQ. So the specifications assume that the direction flag DF is     *)
(* clear, as the ABI requires on entry.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_release:
       +0x0: mov    QWORD PTR [rdi],0x0
       +0x7: mov    rdx,rdi
       +0xa: lea    rdi,[rdi+0x8]
       +0xe: xor    eax,eax
      +0x10: mov    QWORD PTR [rdi+0x310],0x0
      +0x1b: mov    rcx,rdx
      +0x1e: and    rdi,0xfffffffffffffff8
      +0x22: sub    rcx,rdi
      +0x25: add    ecx,0x320
      +0x2b: shr    ecx,0x3
      +0x2e: rep    stos QWORD PTR es:[rdi],rax
      +0x31: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_shake128x4_release"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The bytes at the ends and those cleared by REP STOSQ,  *)
(* at an offset of 1 to 8 bytes that depends on the alignment of st, are put *)
(* together by MEMSET_PREP_TAC, MEMSET_STEP_TAC and MEMSET_DONE_TAC.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_CORRECT_STMT =
  `!st pc.
    aligned 16 (word pc:int64) /\
    nonoverlapping (st,800) (word pc,libmlkem_size)
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_shake128x4_release) /\
           C_ARGUMENTS [st] s /\
           (read DF s <=> false))
      (\s. read RIP s = word (pc + mlkem_shake128x4_release_ret) /\
           read (memory :> bytes(st,800)) s = 0)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(st,800)])`;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (st,800)) [(word pc,libmlkem_size); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_shake128x4_release) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [st] s /\
           (read DF s <=> false))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read (memory :> bytes(st,800)) s = 0)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(st,800)])`;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e st pc.
           aligned 16 (word pc:int64) /\
           nonoverlapping (st,800) (word pc,libmlkem_size)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_shake128x4_release) /\
                    C_ARGUMENTS [st] s /\
                    (read DF s <=> false) /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_shake128x4_release_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events st pc /\
                         memaccess_inbounds e2 [st,800] [st,800]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,800)])`;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e st pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (st,800)) [word pc,libmlkem_size; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_shake128x4_release) /\
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
                          [st,800; stackpointer,8] [st,800]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,800)])`;;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
