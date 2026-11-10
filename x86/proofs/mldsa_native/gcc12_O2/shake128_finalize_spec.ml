(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finalizing the absorbing into a SHAKE128 context: the statement. This is  *)
(* the code for mldsa_shake128_finalize (mld_shake128_finalize in fips202.c, *)
(* with keccak_finalize inlined) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which XORs the domain separation byte 0x1F at the position and the byte   *)
(* 0x80 at the end 167 of the block into the state, by two calls of          *)
(* mldsa_keccakf1600_xor_bytes with the bytes on its stack, and sets the     *)
(* position to the rate 168. It is verified in the whole image (see          *)
(* libmldsa.ml) against mld_keccak_finalize of                               *)
(* common/mldsa_native_fips202.ml, for a position up to the rate, as the C   *)
(* code requires. Unlike the AArch64 code, it has no stack guard (see        *)
(* mldsa_native/README.md). It is also shown to be constant time and memory  *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128_finalize:
       +0x0  push    rbx
       +0x1  mov     ecx, 0x1
       +0x6  mov     rbx, rdi
       +0x9  sub     rsp, 0x10
       +0xd  mov     edx, DWORD PTR [rdi+0xc8]
      +0x13  lea     rsi, [rsp+0xf]
      +0x18  mov     BYTE PTR [rsp+0xf], 0x1f
      +0x1d  mov     BYTE PTR [rsp+0xe], 0x80
      +0x22  call    mldsa_keccakf1600_xor_bytes
     after_mldsa_keccakf1600_xor_bytes_1:
      +0x27  lea     rsi, [rsp+0xe]
      +0x2c  mov     rdi, rbx
      +0x2f  mov     ecx, 0x1
      +0x34  mov     edx, 0xa7
      +0x39  call    mldsa_keccakf1600_xor_bytes
     after_mldsa_keccakf1600_xor_bytes_2:
      +0x3e  mov     DWORD PTR [rbx+0xc8], 0xa8
      +0x48  add     rsp, 0x10
      +0x4c  pop     rbx
     ret:
      +0x4d  ret
 ***)

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128_finalize"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves RBX below the return address and          *)
(* allocates 16 bytes below it for the two bytes, and each call of           *)
(* mldsa_keccakf1600_xor_bytes puts its return address below that.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        ALL (nonoverlapping (ctx,204))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(ctx,204); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_finalize) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s =
                  mld_keccak_finalize 168 0x1F S pos /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word 168)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the position only, with all    *)
(* accesses within the context, the stack frame and the slot of the return   *)
(* address, and the writes within the context and the frame.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        ALL (nonoverlapping (ctx,204))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(ctx,204); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_finalize) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s =
                  mld_keccak_finalize 168 0x1F S pos /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word 168 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pos pc
                                 (word_sub stackpointer (word 32))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,204; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [ctx,204; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ctx pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        ALL (nonoverlapping (ctx,204))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(ctx,204); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_finalize) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pos pc
                                 (word_sub stackpointer (word 32))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,204; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [ctx,204; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
