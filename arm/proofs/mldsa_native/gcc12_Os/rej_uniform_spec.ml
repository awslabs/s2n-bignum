(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients mod q from groups of 3 bytes: the      *)
(* statement. This is the code for mld_rej_uniform_c (poly.c) from           *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mldsa_native/README.md), which the compiler has specialized to the   *)
(* target 256 of all its calls. Before each group it tests the number of    *)
(* coefficients and then the room for a group in the buffer. It is verified  *)
(* in the whole image (see libmldsa.ml) against mld_rej_uniform_list and     *)
(* mld_rej_uniform_ctr of common/mldsa_native_sampling.ml. It is also shown  *)
(* to be constant time and memory safe, with the events depending on the     *)
(* buffer, which the callers fill with the SHAKE128 output of the public     *)
(* seed rho of the matrix.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_rej_uniform_c:
       +0x0: mov     x5, x0
       +0x4: mov     w0, w1
       +0x8: mov     w1, #0x3
       +0xc: sub     w1, w1, w2
      +0x10: cmp     w0, #0xff
      +0x14: b.hi    <mld_rej_uniform_c+0x24>
      +0x18: add     w4, w1, w2
      +0x1c: cmp     w3, w4
      +0x20: b.cs    <mld_rej_uniform_c+0x28>
      +0x24: ret
      +0x28: ldrb    w6, [x2, #2]
      +0x2c: add     x2, x2, #0x3
      +0x30: ldurb   w4, [x2, #-2]
      +0x34: ldurb   w7, [x2, #-3]
      +0x38: lsl     w6, w6, #16
      +0x3c: orr     w4, w6, w4, lsl #8
      +0x40: orr     w4, w4, w7
      +0x44: and     w4, w4, #0x7fffff
      +0x48: cmp     w4, #0x7fe, lsl #12
      +0x4c: b.hi    <mld_rej_uniform_c+0x18>
      +0x50: str     w4, [x5, w0, uxtw #2]
      +0x54: add     w0, w0, #0x1
      +0x58: b       <mld_rej_uniform_c+0x10>
 ***)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_rej_uniform_c"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of buflen bytes at buf, 3 <= buflen <= 840, and *)
(* stores the accepted values of its groups of 3 bytes that fit below 256,   *)
(* from coefficient offset on, returning the new number of coefficients. The *)
(* registers it may change are those that it does change: the callers rely   *)
(* on X3, the buffer length, being preserved, as gcc knows that it is.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_uniform_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_uniform_ctr 256 offset b buflen) /\
                  (!i. offset <= i /\
                       i < mld_rej_uniform_ctr 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_uniform_list b (buflen DIV 3))))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset, buflen and the contents b *)
(* of the buffer, which is public, with all accesses within the buffer and   *)
(* the writes within the coefficients from offset on.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_uniform_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(mld_rej_uniform_ctr 256 offset b buflen) /\
                  (!i. offset <= i /\
                       i < mld_rej_uniform_ctr 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_uniform_list b (buflen DIV 3))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen b pc returnaddress /\
                     memaccess_inbounds e2 [buf,buflen]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_rej_uniform_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen b pc returnaddress /\
                     memaccess_inbounds e2 [buf,buflen]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
