(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-2,2] from nibbles: the statement. *)
(* This is the code for mld_rej_eta_c44 (mld_rej_eta_c in poly_kl.c with     *)
(* MLDSA_ETA = 2, for ML-DSA-44) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which the compiler has specialized to the target 256 and the buffer       *)
(* length 136 of all its calls. It is verified in the whole image (see       *)
(* libmldsa.ml) against mld_rej_eta_list and mld_rej_eta_ctr of              *)
(* common/mldsa_native_sampling.ml. It is also shown to be constant time     *)
(* and memory safe, with the events depending on the buffer only through     *)
(* the acceptance of the nibbles that the C code declassifies.               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_rej_eta_c44:
       +0x0: mov     x6, x0
       +0x4: mov     w0, w1
       +0x8: mov     x5, #0x0
       +0xc: mov     w9, #0x87
      +0x10: mov     w7, #0xcd
      +0x14: mov     w8, #0x2
      +0x18: cmp     w0, #0xff
      +0x1c: ccmp    w5, w9, #0x2, ls
      +0x20: b.ls    <mld_rej_eta_c44+0x28>
      +0x24: ret
      +0x28: ldrb    w1, [x2, x5]
      +0x2c: and     w3, w1, #0xf
      +0x30: lsr     w1, w1, #4
      +0x34: cmp     w3, #0xf
      +0x38: b.eq    <mld_rej_eta_c44+0x58>
      +0x3c: mul     w4, w3, w7
      +0x40: lsr     w4, w4, #10
      +0x44: add     w4, w4, w4, lsl #2
      +0x48: sub     w3, w3, w4
      +0x4c: sub     w3, w8, w3
      +0x50: str     w3, [x6, w0, uxtw #2]
      +0x54: add     w0, w0, #0x1
      +0x58: cmp     w0, #0xff
      +0x5c: ccmp    w1, #0xe, #0x2, ls
      +0x60: b.hi    <mld_rej_eta_c44+0x80>
      +0x64: mul     w3, w1, w7
      +0x68: lsr     w3, w3, #10
      +0x6c: add     w3, w3, w3, lsl #2
      +0x70: sub     w1, w1, w3
      +0x74: sub     w1, w8, w1
      +0x78: str     w1, [x6, w0, uxtw #2]
      +0x7c: add     w0, w0, #0x1
      +0x80: add     x5, x5, #0x1
      +0x84: b       <mld_rej_eta_c44+0x18>
 ***)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_rej_eta_c44"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of 136 bytes at buf and stores the accepted     *)
(* values of its nibbles that fit below 256, from coefficient offset on,     *)
(* returning the new number of coefficients.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_eta_c44) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_eta_ctr 2 256 offset b 136) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 2 256 offset b 136
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset) (mld_rej_eta_list 2 b (2 * 136))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset and the list of whether    *)
(* each nibble that the C code examines is accepted (the values t_valid that *)
(* it declassifies), mld_rej_eta_declass, with all accesses within the       *)
(* buffer and the writes within the coefficients from offset on.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_eta_c44) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_eta_ctr 2 256 offset b 136) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 2 256 offset b 136
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_eta_list 2 b (2 * 136))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf
                            (mld_rej_eta_declass 2 256 offset b 136)
                            pc returnaddress /\
                     memaccess_inbounds e2 [buf,136]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer only through the declassified validity of its nibbles, as above.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_eta_c44) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf
                            (mld_rej_eta_declass 2 256 offset b 136)
                            pc returnaddress /\
                     memaccess_inbounds e2 [buf,136]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
