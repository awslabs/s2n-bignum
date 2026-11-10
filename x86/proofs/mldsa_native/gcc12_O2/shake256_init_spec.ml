(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a SHAKE256 context: the statement. This is the code for *)
(* mldsa_shake256_init (mld_shake256_init in fips202.c) from mldsa-native's  *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which sets the Keccak state, the first 200 bytes *)
(* of the context, and the position, the 32-bit word after it, to zero. The  *)
(* zeroing of the state is a memset that gcc inlines with REP STOSQ, so the  *)
(* direction flag must be clear, as the ABI requires on entry. It is also    *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256_init:
       +0x0  mov     QWORD PTR [rdi], 0x0
       +0x7  mov     rdx, rdi
       +0xa  lea     rdi, [rdi+0x8]
       +0xe  xor     eax, eax
      +0x10  mov     QWORD PTR [rdi+0xb8], 0x0
      +0x1b  mov     rcx, rdx
      +0x1e  and     rdi, 0xfffffffffffffff8
      +0x22  sub     rcx, rdi
      +0x25  add     ecx, 0xc8
      +0x2b  shr     ecx, 0x3
      +0x2e  rep stos QWORD PTR es:[rdi], rax
      +0x31  mov     DWORD PTR [rdx+0xc8], 0x0
     ret:
      +0x3b  ret
 ***)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256_init"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (ctx,204))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_init) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  (read DF s <=> false))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s = word 0)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the address of the context only, with all        *)
(* accesses within the context and the slot of the return address, and the   *)
(* writes within the context.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e ctx pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (ctx,204))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_init) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word 0 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [ctx,204; stackpointer,8] [ctx,204]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ctx pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (ctx,204))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_init) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [ctx,204; stackpointer,8] [ctx,204]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
