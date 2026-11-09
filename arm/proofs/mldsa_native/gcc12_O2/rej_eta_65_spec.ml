(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-4,4] from nibbles: the statement. *)
(* This is the code for mld_rej_eta_c65 (mld_rej_eta_c in poly_kl.c with     *)
(* MLDSA_ETA = 4, for ML-DSA-65) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which the compiler has specialized to the target 256 of all its calls     *)
(* and, as buflen > 0 in all of them, does not test buflen before reading    *)
(* the first byte. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_rej_eta_list and mld_rej_eta_ctr of                           *)
(* common/mldsa_native_sampling.ml. It is also shown to be constant time     *)
(* and memory safe, with the events depending on the buffer only through     *)
(* the acceptance of the nibbles that the C code declassifies.               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_rej_eta_c65:
       +0x0: mov     x9, x0
       +0x4: mov     w0, w1
       +0x8: cmp     w1, #0xff
       +0xc: b.hi    <mld_rej_eta_c65+0x84>
      +0x10: mov     w10, #0x1
      +0x14: sub     w10, w10, w2
      +0x18: mov     w5, #0x4
      +0x1c: nop
      +0x20: ldrb    w4, [x2]
      +0x24: add     w6, w10, w2
      +0x28: add     x2, x2, #0x1
      +0x2c: and     w1, w4, #0xf
      +0x30: lsr     w4, w4, #4
      +0x34: sub     w7, w5, w1
      +0x38: sub     w8, w5, w4
      +0x3c: cmp     w1, #0x8
      +0x40: b.hi    <mld_rej_eta_c65+0x4c>
      +0x44: str     w7, [x9, w0, uxtw #2]
      +0x48: add     w0, w0, #0x1
      +0x4c: cmp     w0, #0xff
      +0x50: add     w7, w0, #0x1
      +0x54: cset    w1, ls
      +0x58: cmp     w1, #0x0
      +0x5c: ccmp    w4, #0x8, #0x2, ne
      +0x60: b.hi    <mld_rej_eta_c65+0x74>
      +0x64: cmp     w7, #0xff
      +0x68: str     w8, [x9, w0, uxtw #2]
      +0x6c: cset    w1, ls
      +0x70: mov     w0, w7
      +0x74: cmp     w6, w3
      +0x78: cset    w4, cc
      +0x7c: tst     w1, w4
      +0x80: b.ne    <mld_rej_eta_c65+0x20>
      +0x84: ret
 ***)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_rej_eta_c65"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of buflen bytes at buf, 0 < buflen <= 272, and  *)
(* stores the accepted values of its nibbles that fit below 256, from        *)
(* coefficient offset on, returning the new number of coefficients. The      *)
(* registers it may change are those that it does change: the callers rely   *)
(* on X3, the buffer length, being preserved, as gcc knows that it is.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_rej_eta_c65) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_eta_ctr 4 256 offset b buflen) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 4 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset) (mld_rej_eta_list 4 b (2 * buflen))))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset, buflen and the list of    *)
(* whether each nibble that the C code examines is accepted (the values      *)
(* t_valid that it declassifies), mld_rej_eta_declass, with all accesses     *)
(* within the buffer and the writes within the coefficients from offset on.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_rej_eta_c65) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_eta_ctr 4 256 offset b buflen) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 4 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_eta_list 4 b (2 * buflen))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen
                            (mld_rej_eta_declass 4 256 offset b buflen)
                            pc returnaddress /\
                     memaccess_inbounds e2 [buf,buflen]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer only through the declassified validity of its nibbles, as above.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_rej_eta_c65) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen
                            (mld_rej_eta_declass 4 256 offset b buflen)
                            pc returnaddress /\
                     memaccess_inbounds e2 [buf,buflen]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
