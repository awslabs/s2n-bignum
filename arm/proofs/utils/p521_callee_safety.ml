(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Safety of bignum_sqr_p521 and bignum_mul_p521 called as local            *)
(* subroutines, as in the P-521 point operations.                           *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/bignum_mul_p521.ml";;
needs "arm/proofs/bignum_sqr_p521.ml";;

(* BIGNUM_SQR_P521_SUBROUTINE_SAFE, but a slightly different maychange set *)
let LOCAL_SQR_P521_SUBR_SAFE =
  prove(`exists f_events.
         forall e z x pc stackpointer returnaddress.
            aligned 16 stackpointer /\
            nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),48) /\
            ALL (nonoverlapping (z,8 * 9))
              [word_sub stackpointer (word 48),48;
               word pc,LENGTH bignum_sqr_p521_mc] /\
            ALL (nonoverlapping (word_sub stackpointer (word 48),48))
              [word pc,LENGTH bignum_sqr_p521_mc; x,8 * 9]
            ==> ensures arm
                 (\s.
                      aligned_bytes_loaded s (word pc) bignum_sqr_p521_mc /\
                      read PC s = word pc /\
                      read SP s = stackpointer /\
                      read X30 s = returnaddress /\
                      C_ARGUMENTS [z; x] s /\
                      read events s = e)
                 (\s.
                      read PC s = returnaddress /\
                      (exists e2.
                           read events s = APPEND e2 e /\
                           e2 = f_events x z pc (word_sub stackpointer (word 48))
                           returnaddress /\
                           memaccess_inbounds e2
                           [x,72; z,72; word_sub stackpointer (word 48),48]
                           [z,72; word_sub stackpointer (word 48),48]))
                 (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                            X14; X15; X16; X17] ,,
                  MAYCHANGE MODIFIABLE_SIMD_REGS ,,
                  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                  MAYCHANGE [memory :> bignum(z,9);
                            memory :> bytes(word_sub stackpointer (word 48),48)])`,
    ARM_ADD_RETURN_STACK_TAC BIGNUM_SQR_P521_EXEC
      (let th = REWRITE_RULE [fst BIGNUM_SQR_P521_CORE_EXEC]
          BIGNUM_SQR_P521_SAFE in
        CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
      `[X19;X20;X21;X22;X23;X24]` 48 THEN
    DISCHARGE_SAFETY_PROPERTY_TAC);;

(* BIGNUM_MUL_P521_SUBROUTINE_SAFE, but a slightly different maychange set *)
let LOCAL_MUL_P521_SUBR_SAFE =
  prove(`exists f_events.
         forall e z x y pc stackpointer returnaddress.
             aligned 16 stackpointer /\
             nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_mc) /\
             ALL (nonoverlapping (word_sub stackpointer (word 144),144))
             [word pc,LENGTH bignum_mul_p521_mc; x,8 * 9; y,8 * 9; z,8 * 9]
             ==> ensures arm
                 (\s.
                      aligned_bytes_loaded s (word pc) bignum_mul_p521_mc /\
                      read PC s = word pc /\
                      read SP s = stackpointer /\
                      read X30 s = returnaddress /\
                      C_ARGUMENTS [z; x; y] s /\
                      read events s = e)
                 (\s.
                      read PC s = returnaddress /\
                      (exists e2.
                           read events s = APPEND e2 e /\
                           e2 = f_events x y z pc
                              (word_sub stackpointer (word 144))
                              returnaddress /\
                           memaccess_inbounds e2
                              [x,72; y,72; z,72;
                                word_sub stackpointer (word 144),144]
                              [z,72; word_sub stackpointer (word 144),144]))
                 (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                             X14; X15; X16; X17] ,,
                  MAYCHANGE MODIFIABLE_SIMD_REGS ,,
                  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                  MAYCHANGE [memory :> bignum(z,9);
                             memory :> bytes(word_sub stackpointer (word 144),144)])`,
    ARM_ADD_RETURN_STACK_TAC BIGNUM_MUL_P521_EXEC
      (let th = REWRITE_RULE [fst BIGNUM_MUL_P521_CORE_EXEC]
          BIGNUM_MUL_P521_SAFE in
        CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
      `[X19;X20;X21;X22;X23;X24;X25;X26]` 144 THEN
    DISCHARGE_SAFETY_PROPERTY_TAC);;
