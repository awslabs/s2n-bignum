(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash check of an ML-KEM-1024 decapsulation key. This is the code for  *)
(* mlkem1024_check_sk from mlkem-native's portable C implementation          *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), which computes  *)
(* the SHA3-256 hash of the encapsulation key in the decapsulation key into  *)
(* a buffer on the stack, compares it with the hash stored in the            *)
(* decapsulation key by calling mlk_ct_memcmp_1, and zeroes the buffer by    *)
(* calling mlk_zeroize_2. It is verified in the whole image (see             *)
(* libmlkem.ml), using the theorems for mlkem_sha3_256, mlk_ct_memcmp_1 and  *)
(* mlk_zeroize_2 in the image, and assuming the contracts for memset in      *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_1_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_2_spec.ml";;

(*** The code in the image, with the labels of layout.ml:

     +0x0  stp     x19, x20, [sp, #-96]!
     +0x4  mov     x20, x0
     +0x8  mov     x2, #0x620
  adrp1:
     +0xc  adrp    x0, <page>
    +0x10  ldr     x0, [x0, #4088]
                   // got_stack_chk_guard
    +0x14  str     x30, [sp, #16]
    +0x18  add     x19, sp, #0x3f
    +0x1c  and     x19, x19, #0xffffffffffffffe0
    +0x20  ldr     x1, [x0]
    +0x24  str     x1, [sp, #88]
    +0x28  mov     x1, #0x0
    +0x2c  add     x1, x20, #0x600
    +0x30  mov     x0, x19
    +0x34  bl      mlkem_sha3_256
  after_mlkem_sha3_256:
    +0x38  mov     x2, #0x20
    +0x3c  mov     x1, x19
    +0x40  add     x0, x20, #0xc20
    +0x44  bl      mlk_ct_memcmp_1
  after_mlk_ct_memcmp_1:
    +0x48  tst     w0, #0xff
    +0x4c  mov     x1, x2
    +0x50  mov     x0, x19
    +0x54  mov     w20, #0xfffffffb
    +0x58  csel    w20, wzr, w20, eq
    +0x5c  bl      mlk_zeroize_2
  after_mlk_zeroize_2: adrp2:
    +0x60  adrp    x0, <page>
    +0x64  ldr     x0, [x0, #4088]
                   // got_stack_chk_guard
    +0x68  ldr     x2, [sp, #88]
    +0x6c  ldr     x1, [x0]
    +0x70  subs    x2, x2, x1
    +0x74  mov     x1, #0x0
    +0x78  b.eq    join1                          -+
    +0x7c  bl      stack_chk_fail                  |
  join1: after_stack_chk_fail:                     |
    +0x80  ldr     x30, [sp, #16]                 <+
    +0x84  mov     w0, w20
    +0x88  ldp     x19, x20, [sp], #96
  ret:
    +0x8c  ret
 ***)

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem1024_check_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset, as for               *)
(* mlk_zeroize_2 and mlkem_sha3_256. The decapsulation key of 3168 bytes at  *)
(* sk contains the encapsulation key of 1568 bytes at offset 1536, given as  *)
(* a list of bytes ek, and its hash h at offset 3104, as a number. The       *)
(* result is 0 if h is the SHA3-256 hash of ek, as in                        *)
(* common/fips202/fips202.ml, and -5 otherwise. The stack is the 96 bytes    *)
(* of the function and the 544 used by mlkem_sha3_256 below them.            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!sk (ek:byte list) h guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1568 /\
        nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 640),640)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem1024_check_sk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(word_add sk (word 1536),1568)) s =
                  num_of_bytelist ek /\
                  read (memory :> bytes(word_add sk (word 3104),32)) s = h)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if h = num_of_bytelist(sha3_256 ek) then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on the address   *)
(* of the stack guard, read from the GOT, and on the address of memset, as   *)
(* well as on the events of memset given by its contract. They do not        *)
(* depend on the keys.                                                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
     forall e sk guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
       ALLPAIRS nonoverlapping
        [word_sub stackpointer (word 640),640]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem1024_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk guard mf pc
                           (word_sub stackpointer (word 640)) returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 1536),1568;
                      word_add sk (word 3104),32;
                      word_sub stackpointer (word 640),640;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 640),640]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using the    *)
(* combined theorem for mlkem_sha3_256, for the decapsulation, which         *)
(* branches on the result.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
     forall e sk (ek:byte list) h guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH ek = 1568 /\
       nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
       ALLPAIRS nonoverlapping
        [word_sub stackpointer (word 640),640]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem1024_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read (memory :> bytes(word_add sk (word 1536),1568)) s =
                 num_of_bytelist ek /\
                 read (memory :> bytes(word_add sk (word 3104),32)) s = h /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s =
                 (if h = num_of_bytelist(sha3_256 ek) then word 0
                  else word 0xfffffffb) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk guard mf pc
                           (word_sub stackpointer (word 640)) returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 1536),1568;
                      word_add sk (word 3104),32;
                      word_sub stackpointer (word 640),640;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 640),640]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
