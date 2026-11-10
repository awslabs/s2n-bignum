(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking polynomial i of t1 from a public key: the statement. This is    *)
(* the code for mldsa44_unpack_pk_t1 (mld_unpack_pk_t1 in packing.c) from    *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md), a tail call of mldsa_polyt1_unpack at       *)
(* offset 32 + 320 * i of the public key. It is verified in the whole image  *)
(* (see libmldsa.ml), using the theorems for mldsa_polyt1_unpack, and shown  *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyt1_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_unpack_pk_t1:
       +0x0  lea     eax, [rdx+rdx*4]
       +0x3  shl     eax, 0x6
       +0x6  lea     rsi, [rax+rsi*1+0x20]
       +0xb  jmp     mldsa_polyt1_unpack
 ***)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_unpack_pk_t1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For i < 4, the 320 bytes b at offset 32 + 320 * i of the     *)
(* public key at pk are unpacked into the polynomial at t1, which may not    *)
(* overlap them, as mld_polyt1_unpack of common/mldsa_native_packing.ml.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!t1 pk b i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (t1,1024))
            [(word pc,libmldsa_size); (word_add pk (word(32 + 320 * i)),320);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_pk_t1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t1; pk; word i] s /\
                  (!j. j < 320
                       ==> read(memory :> bytes8
                             (word_add pk (word(32 + 320 * i + j)))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 256
                      ==> read(memory :> bytes32(word_add t1 (word(4 * j))))
                            s = mld_polyt1_unpack b j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t1,1024)])`;;

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e t1 pk b i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (t1,1024))
            [(word pc,libmldsa_size); (word_add pk (word(32 + 320 * i)),320);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_pk_t1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t1; pk; word i] s /\
                  (!j. j < 320
                       ==> read(memory :> bytes8
                             (word_add pk (word(32 + 320 * i + j)))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add t1 (word(4 * j))))
                             s = mld_polyt1_unpack b j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t1 pk i pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [word_add pk (word(32 + 320 * i)),320; t1,1024;
                        stackpointer,8]
                       [t1,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t1,1024)])`;;

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e t1 pk i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\
        ALL (nonoverlapping (t1,1024))
            [(word pc,libmldsa_size); (word_add pk (word(32 + 320 * i)),320);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_pk_t1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t1; pk; word i] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t1 pk i pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [word_add pk (word(32 + 320 * i)),320; t1,1024;
                        stackpointer,8]
                       [t1,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t1,1024)])`;;

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
