(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a SHAKE128 context: the statement. This is the   *)
(* code for mldsa_shake128_absorb (mld_shake128_absorb in fips202.c, with    *)
(* keccak_absorb inlined) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which XORs the  *)
(* message into the state from the position on, with                         *)
(* mldsa_keccakf1600_xor_bytes, permuting it with mldsa_keccakf1600_permute  *)
(* after each full block of 168 bytes, and stores the new position. It is    *)
(* verified in the whole image (see libmldsa.ml) against mld_keccak_absorb   *)
(* of common/mldsa_native_fips202.ml, for a position up to the rate, as the  *)
(* C code requires. The stack is the 56 bytes of the function, the return    *)
(* address of the calls and the 256 bytes used by the permutation below      *)
(* them. It is also shown to be constant time and memory safe.               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128_absorb:
       +0x0  push    r13
       +0x2  mov     ecx, 0xa8
       +0x7  mov     r13, rdi
       +0xa  push    r12
       +0xc  push    rbp
       +0xd  mov     rbp, rsi
      +0x10  push    rbx
      +0x11  mov     rbx, rdx
      +0x14  sub     rsp, 0x18
      +0x18  mov     edx, DWORD PTR [rdi+0xc8]
      +0x1e  sub     ecx, edx
      +0x20  mov     r12d, ecx
      +0x23  cmp     rbx, r12
      +0x26  jb      join1
      +0x28  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x30  mov     rsi, rbp
      +0x33  mov     rdi, r13
      +0x36  sub     rbx, r12
      +0x39  add     rbp, r12
      +0x3c  call    mldsa_keccakf1600_xor_bytes
     after_mldsa_keccakf1600_xor_bytes_1:
      +0x41  mov     rdi, r13
      +0x44  mov     r12d, 0xa8
      +0x4a  call    mldsa_keccakf1600_permute
     after_mldsa_keccakf1600_permute:
      +0x4f  xor     edx, edx
      +0x51  mov     ecx, 0xa8
     loop1_test:
      +0x56  cmp     rbx, 0xa7
     loop1_back:
      +0x5d  ja      loop1
     join1: loop1_exit:
      +0x5f  mov     ecx, ebx
      +0x61  mov     rsi, rbp
      +0x64  mov     rdi, r13
      +0x67  mov     DWORD PTR [rsp+0xc], edx
      +0x6b  call    mldsa_keccakf1600_xor_bytes
     after_mldsa_keccakf1600_xor_bytes_2:
      +0x70  mov     edx, DWORD PTR [rsp+0xc]
      +0x74  add     edx, ebx
      +0x76  mov     DWORD PTR [r13+0xc8], edx
      +0x7d  add     rsp, 0x18
      +0x81  pop     rbx
      +0x82  pop     rbp
      +0x83  pop     r12
      +0x85  pop     r13
     ret:
      +0x87  ret
 ***)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128_absorb"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx src inlen (S:1600 word) pos M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (src,inlen); (word_sub stackpointer (word 320),320)] /\
        nonoverlapping (ctx,204) (stackpointer,8) /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_absorb) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx; src; word inlen] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read (memory :> bytes(src,inlen)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_absorb 168 S pos inlen M) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_absorb 168 S pos inlen M)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the length and the position only  *)
(* (which give the number of blocks), with all accesses within the context,  *)
(* the message, the stack, the slot of the return address and the round      *)
(* constants of the permutation, and the writes within the context and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e ctx src inlen (S:1600 word) pos M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (src,inlen); (word_sub stackpointer (word 320),320)] /\
        nonoverlapping (ctx,204) (stackpointer,8) /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_absorb) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx; src; word inlen] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read (memory :> bytes(src,inlen)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_absorb 168 S pos inlen M) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_absorb 168 S pos inlen M)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx src inlen pos pc
                                 (word_sub stackpointer (word 320))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,204; src,inlen;
                       word_sub stackpointer (word 320),320; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; word_sub stackpointer (word 320),320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ctx src inlen pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (src,inlen); (word_sub stackpointer (word 320),320)] /\
        nonoverlapping (ctx,204) (stackpointer,8) /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake128_absorb) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [ctx; src; word inlen] s /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx src inlen pos pc
                                 (word_sub stackpointer (word 320))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,204; src,inlen;
                       word_sub stackpointer (word 320),320; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; word_sub stackpointer (word 320),320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
