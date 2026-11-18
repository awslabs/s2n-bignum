(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-512 encapsulation key. This is the code    *)
(* for mlkem512_check_pk from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), which decodes   *)
(* the vector of the key from its first 768 bytes into a buffer on the       *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result with the key by calling mlk_ct_memcmp_2, and zeroes the buffers    *)
(* by calling mlk_zeroize_5. It is verified in the whole image (see          *)
(* libmlkem.ml), using the theorems for mlkem512_polyvec_frombytes,          *)
(* mlkem512_polyvec_reduce, mlkem512_polyvec_tobytes, mlk_ct_memcmp_2 and    *)
(* mlk_zeroize_5 in the image, and assuming the contracts for memset in      *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_frombytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_reduce_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_tobytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_5_spec.ml";;

(*** The code in the image, with the labels of layout.ml:

     +0x0  sub     sp, sp, #0x740
     +0x4  stp     x19, x20, [sp]
     +0x8  mov     x20, x0
     +0xc  add     x19, sp, #0x3f
  adrp1:
    +0x10  adrp    x0, <page>
    +0x14  ldr     x0, [x0, #4088]
                   // got_stack_chk_guard
    +0x18  stp     x21, x30, [sp, #16]
    +0x1c  and     x19, x19, #0xffffffffffffffe0
    +0x20  ldr     x1, [x0]
    +0x24  str     x1, [sp, #1848]
    +0x28  mov     x1, #0x0
    +0x2c  mov     x0, x19
    +0x30  mov     x1, x20
    +0x34  bl      mlkem512_polyvec_frombytes
  after_mlkem512_polyvec_frombytes:
    +0x38  add     x21, x19, #0x400
    +0x3c  mov     x0, x19
    +0x40  bl      mlkem512_polyvec_reduce
  after_mlkem512_polyvec_reduce:
    +0x44  mov     x1, x19
    +0x48  mov     x0, x21
    +0x4c  bl      mlkem512_polyvec_tobytes
  after_mlkem512_polyvec_tobytes:
    +0x50  mov     x2, #0x300
    +0x54  mov     x1, x21
    +0x58  mov     x0, x20
    +0x5c  bl      mlk_ct_memcmp_2
  after_mlk_ct_memcmp_2:
    +0x60  tst     w0, #0xff
    +0x64  mov     x1, x2
    +0x68  mov     x0, x21
    +0x6c  mov     w20, #0xfffffffc
    +0x70  csel    w20, wzr, w20, eq
    +0x74  bl      mlk_zeroize_5
  after_mlk_zeroize_5_1:
    +0x78  mov     x0, x19
    +0x7c  mov     x1, #0x400
    +0x80  bl      mlk_zeroize_5
  after_mlk_zeroize_5_2: adrp2:
    +0x84  adrp    x0, <page>
    +0x88  ldr     x0, [x0, #4088]
                   // got_stack_chk_guard
    +0x8c  ldr     x2, [sp, #1848]
    +0x90  ldr     x1, [x0]
    +0x94  subs    x2, x2, x1
    +0x98  mov     x1, #0x0
    +0x9c  b.eq    join1                          -+
    +0xa0  bl      stack_chk_fail                  |
  join1: after_stack_chk_fail:                     |
    +0xa4  ldp     x21, x30, [sp, #16]            <+
    +0xa8  mov     w0, w20
    +0xac  ldp     x19, x20, [sp]
    +0xb0  add     sp, sp, #0x740
  ret:
    +0xb4  ret
 ***)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem512_check_pk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset, as for               *)
(* mlk_zeroize_5. The first 768 bytes of the key at pk are a number n, and   *)
(* the result is 0 if all their 12-bit fields are below 3329, which is the   *)
(* modulus check of FIPS 203, and -4 otherwise. The stack is the 1856 bytes  *)
(* of the function and the 32 used by the callees below them.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (pk,768) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 1888),1888)]
         [(pk,768); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem512_check_pk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,768)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 512
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 0 else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 1888),1888)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;
(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the address of the key,    *)
(* the stack and the image: the comparison is in constant time and the       *)
(* result is selected without a branch.                                      *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 1888),1888)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 1888))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 1888),1888;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 1888),1888]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 1888),1888)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for          *)
(* mlkem512_enc_derand, which branches on the result.                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk n guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 1888),1888)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,768)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if !i. i < 512
                            ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                     then word 0 else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 1888))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 1888),1888;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 1888),1888]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 1888),1888)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
