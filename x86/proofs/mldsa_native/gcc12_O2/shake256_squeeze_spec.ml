(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE256 context: the statement. This is the code  *)
(* for mldsa_shake256_squeeze (mld_shake256_squeeze in fips202.c, with       *)
(* keccak_squeeze inlined) from mldsa-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which copies    *)
(* the bytes of the state from the position on with                          *)
(* mldsa_keccakf1600_extract_bytes, permuting it with                        *)
(* mldsa_keccakf1600_permute whenever the position reaches the rate 136 and  *)
(* more bytes are wanted, and stores the new position. It is verified in the *)
(* whole image (see libmldsa.ml) against mld_keccak_squeeze_byte and         *)
(* mld_keccak_squeeze_state of common/mldsa_native_fips202.ml, for a         *)
(* position up to the rate, as the C code requires. The stack is the 56      *)
(* bytes of the function, the return address of the calls and the 256 bytes  *)
(* used by the permutation below them. It is also shown to be constant time  *)
(* and memory safe.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256_squeeze:
       +0x0  push    r15
       +0x2  push    r14
       +0x4  push    r13
       +0x6  mov     r13, rdx
       +0x9  push    r12
       +0xb  push    rbp
       +0xc  push    rbx
       +0xd  sub     rsp, 0x8
      +0x11  mov     r12d, DWORD PTR [rdx+0xc8]
      +0x18  test    rsi, rsi
      +0x1b  je      join5
      +0x1d  mov     r14, rdi
      +0x20  mov     rbx, rsi
      +0x23  xor     r15d, r15d
      +0x26  jmp     join4
      +0x28  nop     DWORD PTR [rax+rax*1+0x0]
     join1:
      +0x30  mov     ecx, 0x88
      +0x35  mov     edx, r12d
      +0x38  sub     ecx, r12d
      +0x3b  mov     ebp, ecx
     join2:
      +0x3d  mov     r12d, 0x88
      +0x43  cmp     rbx, rbp
      +0x46  jae     join3
      +0x48  mov     ecx, ebx
      +0x4a  lea     r12d, [rdx+rbx*1]
      +0x4e  mov     rbp, rbx
     join3:
      +0x51  lea     rsi, [r14+r15*1]
      +0x55  mov     rdi, r13
      +0x58  add     r15, rbp
      +0x5b  call    mldsa_keccakf1600_extract_bytes
     after_mldsa_keccakf1600_extract_bytes:
      +0x60  sub     rbx, rbp
      +0x63  je      join5
     join4:
      +0x65  cmp     r12d, 0x88
      +0x6c  jne     join1
      +0x6e  mov     rdi, r13
      +0x71  mov     ebp, 0x88
      +0x76  call    mldsa_keccakf1600_permute
     after_mldsa_keccakf1600_permute:
      +0x7b  mov     ecx, 0x88
      +0x80  xor     edx, edx
      +0x82  jmp     join2
      +0x84  nop     DWORD PTR [rax+0x0]
     join5:
      +0x88  mov     DWORD PTR [r13+0xc8], r12d
      +0x8f  add     rsp, 0x8
      +0x93  pop     rbx
      +0x94  pop     rbp
      +0x95  pop     r12
      +0x97  pop     r13
      +0x99  pop     r14
      +0x9b  pop     r15
     ret:
      +0x9d  ret
 ***)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256_squeeze"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 136 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)] /\
        ALLPAIRS nonoverlapping [(ctx,204); (out,outlen)] [(stackpointer,8)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_squeeze) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 136 S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state 136 S pos outlen) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_squeeze_state 136 S pos outlen)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the length and the position only  *)
(* (which give the number of blocks), with all accesses within the output,   *)
(* the context, the stack, the slot of the return address and the round      *)
(* constants of the permutation, and the writes within the context, the      *)
(* output and the stack.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 136 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)] /\
        ALLPAIRS nonoverlapping [(ctx,204); (out,outlen)] [(stackpointer,8)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_squeeze) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 136 S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state 136 S pos outlen) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_squeeze_state 136 S pos outlen)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos pc
                                 (word_sub stackpointer (word 320))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,204;
                       word_sub stackpointer (word 320),320; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; out,outlen;
                       word_sub stackpointer (word 320),320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen ctx pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        pos <= 136 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)] /\
        ALLPAIRS nonoverlapping [(ctx,204); (out,outlen)] [(stackpointer,8)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 320),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256_squeeze) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos pc
                                 (word_sub stackpointer (word 320))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,204;
                       word_sub stackpointer (word 320),320; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; out,outlen;
                       word_sub stackpointer (word 320),320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
