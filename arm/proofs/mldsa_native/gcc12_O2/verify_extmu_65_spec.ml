(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with external mu: the statement. This is the code   *)
(* for mldsa65_verify_extmu (mld_sign_verify_extmu in sign.c, an external    *)
(* API function) from mldsa-native's portable C implementation compiled by   *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which verifies with the     *)
(* given mu by a tail call of mldsa65_verify_internal. It is verified in the *)
(* whole image (see libmldsa.ml), using the theorems for the callees and the *)
(* contracts memset_ret_full_contract of the C library functions, and shown  *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/verify_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_verify_extmu:
       +0x0: mov     x5, x2
       +0x4: mov     w6, #0x1
       +0x8: mov     x4, #0x0
       +0xc: mov     x3, #0x0
      +0x10: mov     x2, #0x40
      +0x14: b       <mldsa65_verify_internal>
 ***)

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_verify_extmu"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (3309 bytes), mu, MU, the 64 bytes at mu, and the   *)
(* public key pkb at pk (1952 bytes): the result is 0 if the signature is    *)
(* accepted for mu, and -6 if not. The stack is the 0 bytes of the function  *)
(* and those of the callees below them.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !sig mu pk sigb pkb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (mu,64); (pk,1952); (word pc,libmldsa_size);
               (word(pc + got_stack_chk_guard),8); (guard,8);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb MU
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the signature, mu and the public  *)
(* key, all public, with all accesses within the arguments, the stack, the   *)
(* GOT entries and the stack guard, the region (ea,el) that the C library    *)
(* functions may read and the constants of the callees, and the writes       *)
(* within the outputs and the stack.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig mu pk sigb pkb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (mu,64); (pk,1952); (word pc,libmldsa_size);
               (word(pc + got_stack_chk_guard),8); (guard,8);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb MU
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig mu pk sigb pkb MU guard mf pc
                            (word_sub stackpointer (word 45280))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; mu,64; pk,1952;
                         word_sub stackpointer (word 45280),45280;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 45280),45280]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig mu pk sigb pkb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5
           (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (mu,64); (pk,1952); (word pc,libmldsa_size);
               (word(pc + got_stack_chk_guard),8); (guard,8);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig mu pk sigb pkb MU guard mf pc
                            (word_sub stackpointer (word 45280))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; mu,64; pk,1952;
                         word_sub stackpointer (word 45280),45280;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 45280),45280]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
