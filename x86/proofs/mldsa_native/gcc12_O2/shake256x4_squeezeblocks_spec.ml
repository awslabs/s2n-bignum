(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four SHAKE256 states: the statement. This is  *)
(* the code for mldsa_shake256x4_squeezeblocks from mldsa-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which for each of nblocks blocks permutes the    *)
(* four states with mldsa_keccakf1600x4_permute and then extracts the first  *)
(* 136 bytes of each with mldsa_keccakf1600x4_extract_bytes, passing its     *)
(* seventh argument on the stack. It is verified in the whole image (see     *)
(* libmldsa.ml), using the theorems for those functions. It is also shown to *)
(* be constant time and memory safe.                                         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_extract_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_squeezeblocks:
       +0x0  test    r8, r8
       +0x3  je      join1
       +0x9  push    r15
       +0xb  mov     r15, r9
       +0xe  push    r14
      +0x10  mov     r14, r8
      +0x13  push    r13
      +0x15  mov     r13, rdi
      +0x18  push    r12
      +0x1a  mov     r12, rsi
      +0x1d  push    rbp
      +0x1e  mov     rbp, rdx
      +0x21  push    rbx
      +0x22  mov     rbx, rcx
      +0x25  sub     rsp, 0x8
      +0x29  nop     DWORD PTR [rax+0x0]
     loop1:
      +0x30  mov     rdi, r15
      +0x33  call    mldsa_keccakf1600x4_permute
     after_mldsa_keccakf1600x4_permute:
      +0x38  sub     rsp, 0x8
      +0x3c  mov     rdx, r12
      +0x3f  mov     r8, rbx
      +0x42  push    0x88
      +0x47  mov     rcx, rbp
      +0x4a  mov     rsi, r13
      +0x4d  xor     r9d, r9d
      +0x50  mov     rdi, r15
      +0x53  add     r13, 0x88
      +0x5a  add     r12, 0x88
      +0x61  add     rbp, 0x88
      +0x68  add     rbx, 0x88
      +0x6f  call    mldsa_keccakf1600x4_extract_bytes
     after_mldsa_keccakf1600x4_extract_bytes:
      +0x74  pop     rax
      +0x75  pop     rdx
     loop1_test:
      +0x76  sub     r14, 0x1
     loop1_back:
      +0x7a  jne     loop1
     loop1_exit:
      +0x7c  add     rsp, 0x8
      +0x80  pop     rbx
      +0x81  pop     rbp
      +0x82  pop     r12
      +0x84  pop     r13
      +0x86  pop     r14
      +0x88  pop     r15
     ret1:
      +0x8a  ret
      +0x8b  nop     DWORD PTR [rax+rax*1+0x0]
     join1: ret2:
      +0x90  ret
 ***)

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256x4_squeezeblocks"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(out0,136 * nblocks); (out1,136 * nblocks); (out2,136 * nblocks);
          (out3,136 * nblocks); (st,800);
          (word_sub stackpointer (word 336),336)] /\
        ALLPAIRS nonoverlapping
         [(out0,136 * nblocks); (out1,136 * nblocks); (out2,136 * nblocks);
          (out3,136 * nblocks); (st,800)]
         [(stackpointer,8)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(out0,136 * nblocks); (out1,136 * nblocks); (out2,136 * nblocks);
          (out3,136 * nblocks); (st,800);
          (word_sub stackpointer (word 336),336)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_squeezeblocks) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out0,136 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 136 * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 136)) /\
                  read (memory :> bytes(out1,136 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 136 * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 136)) /\
                  read (memory :> bytes(out2,136 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 136 * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 136)) /\
                  read (memory :> bytes(out3,136 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 136 * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 136)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out0,136 * nblocks);
                memory :> bytes(out1,136 * nblocks);
                memory :> bytes(out2,136 * nblocks);
                memory :> bytes(out3,136 * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, and constant time  *)
(* and memory safety alone.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
       PAIRWISE nonoverlapping
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800; word_sub stackpointer (word 336),336] /\
       ALLPAIRS nonoverlapping
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800]
        [stackpointer,8] /\
       ALL (nonoverlapping (word pc,libmldsa_size))
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800; word_sub stackpointer (word 336),336]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                 read RIP s = word (pc + mldsa_shake256x4_squeezeblocks) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out0,136 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 136 * i) *
                       val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 136)) /\
                 read (memory :> bytes(out1,136 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 136 * i) *
                       val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 136)) /\
                 read (memory :> bytes(out2,136 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 136 * i) *
                       val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 136)) /\
                 read (memory :> bytes(out3,136 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 136 * i) *
                       val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 136)) /\
                 read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 keccak_squeeze nblocks S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 keccak_squeeze nblocks S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 keccak_squeeze nblocks S3 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,136 * nblocks; out1,136 * nblocks;
                      out2,136 * nblocks; out3,136 * nblocks; st,800;
                      word_sub stackpointer (word 336),336; stackpointer,8;
                      word(pc + rodata_mld_KeccakF_RoundConstants),192]
                     [out0,136 * nblocks; out1,136 * nblocks;
                      out2,136 * nblocks; out3,136 * nblocks; st,800;
                      word_sub stackpointer (word 336),336]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out0,136 * nblocks);
               memory :> bytes(out1,136 * nblocks);
               memory :> bytes(out2,136 * nblocks);
               memory :> bytes(out3,136 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
       PAIRWISE nonoverlapping
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800; word_sub stackpointer (word 336),336] /\
       ALLPAIRS nonoverlapping
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800]
        [stackpointer,8] /\
       ALL (nonoverlapping (word pc,libmldsa_size))
        [out0,136 * nblocks; out1,136 * nblocks; out2,136 * nblocks;
         out3,136 * nblocks; st,800; word_sub stackpointer (word 336),336]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                 read RIP s = word (pc + mldsa_shake256x4_squeezeblocks) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,136 * nblocks; out1,136 * nblocks;
                      out2,136 * nblocks; out3,136 * nblocks; st,800;
                      word_sub stackpointer (word 336),336; stackpointer,8;
                      word(pc + rodata_mld_KeccakF_RoundConstants),192]
                     [out0,136 * nblocks; out1,136 * nblocks;
                      out2,136 * nblocks; out3,136 * nblocks; st,800;
                      word_sub stackpointer (word 336),336]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out0,136 * nblocks);
               memory :> bytes(out1,136 * nblocks);
               memory :> bytes(out2,136 * nblocks);
               memory :> bytes(out3,136 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
