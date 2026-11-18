(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-256. This is the code for mlkem_sha3_256 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, extracts the 32 bytes of the hash with *)
(* mlk_keccak_squeeze_once, and then zeroes the state with memset from the C *)
(* library, called through the PLT of the image. It is verified in the whole *)
(* image (see libmlkem.ml), using the theorems for mlk_keccak_absorb_once    *)
(* and mlk_keccak_squeeze_once in the image and assuming the contracts for   *)
(* memset in utils/mlkem_native_libc.ml. The result is sha3_256 of           *)
(* common/fips202/fips202.ml.                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeeze_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem_sha3_256:
       +0x0: stp     x19, x20, [sp, #-240]!
       +0x4: mov     x20, x0
       +0x8: mov     w4, #0x6
       +0xc: adrp    x0, <page>
      +0x10: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x14: str     x30, [sp, #16]
      +0x18: add     x19, sp, #0x20
      +0x1c: ldr     x3, [x0]
      +0x20: str     x3, [sp, #232]
      +0x24: mov     x3, #0x0
      +0x28: mov     x0, x19
      +0x2c: mov     x3, x2
      +0x30: mov     x2, x1
      +0x34: mov     w1, #0x88
      +0x38: bl      <mlk_keccak_absorb_once>
      +0x3c: mov     w3, #0x88
      +0x40: mov     x2, x19
      +0x44: mov     x0, x20
      +0x48: mov     x1, #0x20
      +0x4c: bl      <mlk_keccak_squeeze_once>
      +0x50: mov     x0, x19
      +0x54: mov     x2, #0xc8
      +0x58: mov     w1, #0x0
      +0x5c: bl      <memset@plt>
      +0x60: adrp    x0, <page>
      +0x64: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x68: ldr     x2, [sp, #232]
      +0x6c: ldr     x1, [x0]
      +0x70: subs    x2, x2, x1
      +0x74: mov     x1, #0x0
      +0x78: b.eq    <mlkem_sha3_256+0x80>
      +0x7c: bl      <__stack_chk_fail@plt>
      +0x80: ldr     x30, [sp, #16]
      +0x84: ldp     x19, x20, [sp], #240
      +0x88: ret

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_sha3_256"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_256 in common/fips202/fips202.ml.  *)
(* The address of the stack guard is read from the GOT, as for               *)
(* mlkem_poly_compress_d4, and the contract for memset is that at the        *)
(* address mf in its GOT entry, with its code and data in the region         *)
(* (ea,el), which must not overlap the output or the stack. The stack is the *)
(* 240 bytes of the function and the 304 used by mlk_keccak_absorb_once      *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out m (inp:byte list) guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,32); (m,LENGTH inp); (word_sub stackpointer (word 544),544)] /\
        ALLPAIRS nonoverlapping
         [(out,32); (word_sub stackpointer (word 544),544)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_sha3_256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,32)) s =
                  num_of_bytelist(sha3_256 inp))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,32);
                memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_poly_compress_d4, it  *)
(* is stated directly, since the events depend on the address of the stack   *)
(* guard, read from the GOT, and on the address of memset, as well as on the *)
(* events of memset given by its contract.                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 544),544] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 544),544]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard mf pc
                           (word_sub stackpointer (word 544)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 544),544;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 544),544]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once and mlk_keccak_squeeze_once and assuming the    *)
(* combined contract for memset in utils/mlkem_native_libc_full.ml, for the  *)
(* hash check of the decapsulation key, whose result the decapsulation       *)
(* branches on.                                                              *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
     forall e out m (inp:byte list) inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 544),544] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 544),544]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,32)) s =
                 num_of_bytelist(sha3_256 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard mf pc
                           (word_sub stackpointer (word 544)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 544),544;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 544),544]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
