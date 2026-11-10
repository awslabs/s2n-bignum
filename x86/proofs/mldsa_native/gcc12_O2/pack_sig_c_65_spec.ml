(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying the challenge seed c~ of 48 bytes to the start of a signature:    *)
(* the statement. This is the code for mldsa65_pack_sig_c (mld_pack_sig_c    *)
(* in packing.c) from mldsa-native's portable C implementation compiled by   *)
(* gcc 12 with -O2 (see mldsa_native/README.md), in which the call of        *)
(* memcpy is inlined. It is verified in the whole image (see libmldsa.ml),   *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_pack_sig_c:
       +0x0  movdqu  xmm0, XMMWORD PTR [rsi]
       +0x4  movups  XMMWORD PTR [rdi], xmm0
       +0x7  movdqu  xmm1, XMMWORD PTR [rsi+0x10]
       +0xc  movups  XMMWORD PTR [rdi+0x10], xmm1
      +0x10  movdqu  xmm2, XMMWORD PTR [rsi+0x20]
      +0x15  movups  XMMWORD PTR [rdi+0x20], xmm2
     ret:
      +0x19  ret
 ***)

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_pack_sig_c"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 48 bytes b at c, which may not overlap the first 48      *)
(* bytes of the signature at sig, are copied there.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig c b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,48))
            [(word pc,libmldsa_size); (c,48); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_c) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  (!j. j < 48
                       ==> read(memory :> bytes8(word_add c (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 48
                      ==> read(memory :> bytes8(word_add sig (word j))) s =
                          b j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,48)])`;;

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig c b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,48))
            [(word pc,libmldsa_size); (c,48); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_c) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  (!j. j < 48
                       ==> read(memory :> bytes8(word_add c (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 48
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           b j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig c pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [c,48; sig,48; stackpointer,8] [sig,48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,48)])`;;

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig c pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,48))
            [(word pc,libmldsa_size); (c,48); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_c) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig c pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [c,48; sig,48; stackpointer,8] [sig,48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,48)])`;;

let MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
