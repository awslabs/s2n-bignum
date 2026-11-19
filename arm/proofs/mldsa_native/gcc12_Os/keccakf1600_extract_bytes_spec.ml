(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mldsa_keccakf1600_extract_bytes from mldsa-native's portable C            *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which copies len bytes of the 200-byte state starting at byte off. It is  *)
(* verified in the whole image (see libmldsa.ml).                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600_extract_bytes:
       +0x0: add     x2, x0, w2, uxtw
       +0x4: mov     x4, #0x0
       +0x8: cmp     w3, w4
       +0xc: b.hi    <mldsa_keccakf1600_extract_bytes+0x14>
      +0x10: ret
      +0x14: ldrb    w0, [x2, x4]
      +0x18: strb    w0, [x1, x4]
      +0x1c: add     x4, x4, #0x1
      +0x20: b       <mldsa_keccakf1600_extract_bytes+0x8>
 ***)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_keccakf1600_extract_bytes"];;

(*** The zero-extended arguments off and len, and the test of len ***)

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in common/fips202/fips202.ml, the state is a        *)
(* 1600-bit word S, and the bytes extracted are bytes off to off + len - 1   *)
(* of it, which as a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 *   *)
(* len).                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len)) [(word pc,libmldsa_size); (a,200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on off as well   *)
(* as len, so the theorem is stated directly rather than by mk_safety_spec.  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmldsa_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for callers  *)
(* whose events depend on the result, such as the rejection sampling in      *)
(* mldsa_poly_rej_uniform. Separate correctness and safety theorems are      *)
(* ensures statements whose postconditions might hold at different points of *)
(* an execution, so they cannot be combined after the fact; here the loop    *)
(* invariant of the correctness proof is used with the events of the safety  *)
(* proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmldsa_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
