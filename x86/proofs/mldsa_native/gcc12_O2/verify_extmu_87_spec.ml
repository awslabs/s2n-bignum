(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with external mu: the statement. This is the code   *)
(* for mldsa87_verify_extmu (mld_sign_verify_extmu in sign.c, an external    *)
(* API function) from mldsa-native's portable C implementation compiled by   *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which verifies with the     *)
(* given mu by a call of mldsa87_verify_internal with mlen = 64, pre = NULL, *)
(* prelen = 0 and ext = 1, its seventh argument, which it pushes on the      *)
(* stack. It is verified in the whole image (see libmldsa.ml), using the     *)
(* theorem for the callee and the contract memset_full_contract of           *)
(* utils/mldsa_native_libc.ml for the memset that the callee calls, and      *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_verify_extmu:
       +0x0  sub     rsp, 0x10
       +0x4  mov     r9, rdx
       +0x7  xor     r8d, r8d
       +0xa  xor     ecx, ecx
       +0xc  push    0x1
       +0xe  mov     edx, 0x40
      +0x13  call    mldsa87_verify_internal
     after_mldsa87_verify_internal:
      +0x18  add     rsp, 0x18
     ret:
      +0x1c  ret
 ***)

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_verify_extmu"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (4627 bytes), mu, MU, the 64 bytes at mu, and the public key pkb at pk    *)
(* (2592 bytes): the result is 0 if the signature is accepted for mu, and -6 *)
(* if not. The stack is the 32 bytes of the function, with ext and the       *)
(* return address of the call, and those of mldsa87_verify_internal below    *)
(* them: 74381 bytes below the return address in all. The GOT entry of       *)
(* memset and the region (ea,el) that memset may read are apart from the     *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig mu pk sigb pkb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74381),74381))
              [(sig,4627); (mu,64); (pk,2592); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb MU
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74381),74381)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the signature, mu and the public  *)
(* key, all public, the address of memset and the stack, with all accesses   *)
(* within the arguments, the stack, the return address, the GOT entry of     *)
(* memset, the region (ea,el) that memset may read and the constants of the  *)
(* callees, and the writes within the stack.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig mu pk sigb pkb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74381),74381))
              [(sig,4627); (mu,64); (pk,2592); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb MU
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig mu pk sigb pkb MU mf pc
                            (word_sub stackpointer (word 74381))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; mu,64; pk,2592;
                         word_sub stackpointer (word 74381),74381;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [word_sub stackpointer (word 74381),74381]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74381),74381)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig mu pk sigb pkb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74381),74381))
              [(sig,4627); (mu,64); (pk,2592); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig mu pk sigb pkb MU mf pc
                            (word_sub stackpointer (word 74381))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; mu,64; pk,2592;
                         word_sub stackpointer (word 74381),74381;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [word_sub stackpointer (word 74381),74381]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74381),74381)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
