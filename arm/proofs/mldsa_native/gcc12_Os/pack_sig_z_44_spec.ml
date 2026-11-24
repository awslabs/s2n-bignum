(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing polynomial i of z into a signature: the statement. This is the    *)
(* code for mldsa44_pack_sig_z (mld_pack_sig_z in packing.c) from            *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mldsa_native/README.md), a tail call of mldsa44_polyz_pack at offset *)
(* 32 + 576 * i of the signature. It is verified in the whole image (see     *)
(* libmldsa.ml), using the theorems for mldsa44_polyz_pack, and shown to be  *)
(* constant time and memory safe. As mldsa44_polyz_pack, it has a stack      *)
(* frame, uses the stack guard and calls memset (through mld_zeroize), so    *)
(* its statements carry the contract memset_full_contract of                 *)
(* utils/mlkem_native_libc_full.ml and the address of the stack guard in the *)
(* global offset table.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyz_pack_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pack_sig_z:
       +0x0: mov     w3, #0x240
       +0x4: mul     w2, w2, w3
       +0x8: add     x2, x2, #0x20
       +0xc: add     x0, x0, x2
      +0x10: b       <mldsa44_polyz_pack>
 ***)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_pack_sig_z"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For i < 4, the polynomial x at zi is packed into the 576     *)
(* bytes at offset 32 + 576 * i of the signature at sig, which may not       *)
(* overlap it, as mld_polyz_pack_17 of common/mldsa_native_packing.ml. The   *)
(* stack frame includes that of mld_zeroize; the memory (ea,el) that memset  *)
(* reads and keeps must not overlap the output or the stack frame.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig zi x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          i < 4 /\ aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)]
           [(zi,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_z) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; zi; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read(memory :> bytes32(word_add zi (word(4 * j))))
                               s = x j))
               (\s. read PC s = returnaddress /\
                    (!j. j < 576
                         ==> read(memory :> bytes8
                               (word_add sig (word(32 + 576 * i + j)))) s =
                             mld_polyz_pack_17 x j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame, the GOT entries of the stack guard   *)
(* and of memset, the guard and (ea,el), and the writes within the output    *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig zi x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          i < 4 /\ aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)]
           [(zi,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_z) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; zi; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read(memory :> bytes32(word_add zi (word(4 * j))))
                               s = x j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!j. j < 576
                         ==> read(memory :> bytes8
                               (word_add sig (word(32 + 576 * i + j)))) s =
                             mld_polyz_pack_17 x j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig zi i guard mf pc
                              (word_sub stackpointer (word 64))
                              returnaddress /\
                       memaccess_inbounds e2
                        [zi,1024; word_add sig (word(32 + 576 * i)),576;
                         word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word(32 + 576 * i)),576;
                         word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig zi i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          i < 4 /\ aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word(32 + 576 * i)),576);
            (word_sub stackpointer (word 64),64)]
           [(zi,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_z) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; zi; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig zi i guard mf pc
                              (word_sub stackpointer (word 64))
                              returnaddress /\
                       memaccess_inbounds e2
                        [zi,1024; word_add sig (word(32 + 576 * i)),576;
                         word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word(32 + 576 * i)),576;
                         word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
