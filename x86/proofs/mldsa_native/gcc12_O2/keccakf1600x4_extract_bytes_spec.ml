(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from four Keccak states. This is the code for         *)
(* mldsa_keccakf1600x4_extract_bytes from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa_keccakf1600_extract_bytes for each of the states, the   *)
(* last time as a tail call. It is verified in the whole image (see          *)
(* libmldsa.ml), using the theorems for mldsa_keccakf1600_extract_bytes in   *)
(* the image. It is also shown to be constant time and memory safe.          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600x4_extract_bytes:
       +0x0  push    r15
       +0x2  mov     r15, rdx
       +0x5  mov     edx, r9d
       +0x8  push    r14
       +0xa  mov     r14, rcx
       +0xd  push    r13
       +0xf  mov     r13, r8
      +0x12  push    r12
      +0x14  push    rbp
      +0x15  mov     ebp, r9d
      +0x18  push    rbx
      +0x19  mov     rbx, rdi
      +0x1c  sub     rsp, 0x8
      +0x20  mov     r12d, DWORD PTR [rsp+0x40]
      +0x25  mov     ecx, r12d
      +0x28  call    mldsa_keccakf1600_extract_bytes
     after_mldsa_keccakf1600_extract_bytes_1:
      +0x2d  mov     ecx, r12d
      +0x30  mov     edx, ebp
      +0x32  mov     rsi, r15
      +0x35  lea     rdi, [rbx+0xc8]
      +0x3c  call    mldsa_keccakf1600_extract_bytes
     after_mldsa_keccakf1600_extract_bytes_2:
      +0x41  mov     ecx, r12d
      +0x44  mov     edx, ebp
      +0x46  mov     rsi, r14
      +0x49  lea     rdi, [rbx+0x190]
      +0x50  call    mldsa_keccakf1600_extract_bytes
     after_mldsa_keccakf1600_extract_bytes_3:
      +0x55  add     rsp, 0x8
      +0x59  mov     ecx, r12d
      +0x5c  mov     edx, ebp
      +0x5e  lea     rdi, [rbx+0x258]
      +0x65  mov     rsi, r13
      +0x68  pop     rbx
      +0x69  pop     rbp
      +0x6a  pop     r12
      +0x6c  pop     r13
      +0x6e  pop     r14
      +0x70  pop     r15
      +0x72  jmp     mldsa_keccakf1600_extract_bytes
 ***)

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600x4_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seventh argument, len, is passed on the stack, above the *)
(* return address, and only the low 32 bits of its slot are read. The        *)
(* function saves six registers below the return address and allocates 8     *)
(* bytes below them, and each call of mldsa_keccakf1600_extract_bytes but    *)
(* the last, which is a tail call, puts its return address below that.       *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT
 =
 `!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (a,800)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len)]
         [(stackpointer,8); (word_add stackpointer (word 8),4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                  read (memory :> bytes32(word_add stackpointer (word 8))) s =
                  word len /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT
  ;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the offset and the length only,   *)
(* with all accesses within the states, the outputs, the stack frame and the *)
(* slots of the return address and of len, and the writes within the outputs *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (a,800)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len)]
         [(stackpointer,8); (word_add stackpointer (word 8),4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                  read (memory :> bytes32(word_add stackpointer (word 8))) s =
                  word len /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a d0 d1 d2 d3 off len pc
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,800; d0,len; d1,len; d2,len; d3,len;
                       word_sub stackpointer (word 64),64; stackpointer,8;
                       word_add stackpointer (word 8),4]
                      [d0,len; d1,len; d2,len; d3,len;
                       word_sub stackpointer (word 64),64]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a d0 d1 d2 d3 off len pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (a,800)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len)]
         [(stackpointer,8); (word_add stackpointer (word 8),4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                  read (memory :> bytes32(word_add stackpointer (word 8))) s =
                  word len /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a d0 d1 d2 d3 off len pc
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,800; d0,len; d1,len; d2,len; d3,len;
                       word_sub stackpointer (word 64),64; stackpointer,8;
                       word_add stackpointer (word 8),4]
                      [d0,len; d1,len; d2,len; d3,len;
                       word_sub stackpointer (word 64),64]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
