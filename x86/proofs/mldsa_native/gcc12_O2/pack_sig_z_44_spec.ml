(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing polynomial i of z into a signature: the statement. This is the    *)
(* code for mldsa44_pack_sig_z (mld_pack_sig_z in packing.c) from            *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md), a tail call of mldsa44_polyz_pack at offset *)
(* 32 + 576 * i of the signature. It is verified in the whole image (see     *)
(* libmldsa.ml), using the theorems for mldsa44_polyz_pack, and shown to be  *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyz_pack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pack_sig_z:
       +0x0  lea     eax, [rdx+rdx*8]
       +0x3  shl     eax, 0x6
       +0x6  lea     rdi, [rax+rdi*1+0x20]
       +0xb  jmp     mldsa44_polyz_pack
 ***)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_pack_sig_z"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For i < 4, the polynomial x at zi is packed into the 576     *)
(* bytes at offset 32 + 576 * i of the signature at sig, which may not       *)
(* overlap it, as mld_polyz_pack_17 of common/mldsa_native_packing.ml. The   *)
(* tail call of mldsa44_polyz_pack saves R13, R12, RBP and RBX, which that   *)
(* function uses, in the 32 bytes below the return address.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig zi x i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (word_add sig (word(32 + 576 * i)),576))
            [(word pc,libmldsa_size); (zi,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (zi,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_pack_sig_z) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; zi; word i] s /\
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add zi (word(4 * j))))
                             s = x j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 576
                      ==> read(memory :> bytes8
                            (word_add sig (word(32 + 576 * i + j)))) s =
                          mld_polyz_pack_17 x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig zi x i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (word_add sig (word(32 + 576 * i)),576))
            [(word pc,libmldsa_size); (zi,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (zi,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_pack_sig_z) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; zi; word i] s /\
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add zi (word(4 * j))))
                             s = x j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 576
                       ==> read(memory :> bytes8
                             (word_add sig (word(32 + 576 * i + j)))) s =
                           mld_polyz_pack_17 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig zi i pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [zi,1024; word_add sig (word(32 + 576 * i)),576;
                        word_sub stackpointer (word 32),32; stackpointer,8]
                       [word_add sig (word(32 + 576 * i)),576;
                        word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig zi i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (word_add sig (word(32 + 576 * i)),576))
            [(word pc,libmldsa_size); (zi,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (zi,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_pack_sig_z) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; zi; word i] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig zi i pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [zi,1024; word_add sig (word(32 + 576 * i)),576;
                        word_sub stackpointer (word 32),32; stackpointer,8]
                       [word_add sig (word(32 + 576 * i)),576;
                        word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word(32 + 576 * i)),576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
