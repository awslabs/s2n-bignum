(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The return codes of the API functions of mldsa-native (mldsa_native.h),   *)
(* as the contents of the return register x0 (the C type is int; the machine *)
(* code zero-extends the 32-bit value), and the code and the signature that  *)
(* the API functions return for each outcome of the FIPS 204 algorithms of   *)
(* common/fips204/fips204.ml. The theorems about the machine code state that *)
(* it returns what these functions give for the outcome of the model, for    *)
(* example that signing returns MLD_ERR_INVALID_ARG for a context of more    *)
(* than 255 bytes, where the model gives MLDSA_Sign_Error_BadContext.        *)
(* ========================================================================= *)

needs "common/fips204/fips204.ml";;

(* Success: 0 (the header has no name for it).                               *)

let MLD_OK = new_definition `MLD_OK = word 0:int64`;;

let MLD_ERR_FAIL =
  new_definition
   `MLD_ERR_FAIL = word_zx(word_neg(word 1):int32):int64`;;

let MLD_ERR_OUT_OF_MEMORY =
  new_definition
   `MLD_ERR_OUT_OF_MEMORY = word_zx(word_neg(word 2):int32):int64`;;

let MLD_ERR_RNG_FAIL =
  new_definition
   `MLD_ERR_RNG_FAIL = word_zx(word_neg(word 3):int32):int64`;;

let MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED =
  new_definition
   `MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED = word_zx(word_neg(word 4):int32):int64`;;

let MLD_ERR_SIGNING_PAUSED =
  new_definition
   `MLD_ERR_SIGNING_PAUSED = word_zx(word_neg(word 5):int32):int64`;;

let MLD_ERR_INVALID_SIGNATURE =
  new_definition
   `MLD_ERR_INVALID_SIGNATURE = word_zx(word_neg(word 6):int32):int64`;;

let MLD_ERR_INVALID_KEY =
  new_definition
   `MLD_ERR_INVALID_KEY = word_zx(word_neg(word 7):int32):int64`;;

let MLD_ERR_PCT_FAIL =
  new_definition
   `MLD_ERR_PCT_FAIL = word_zx(word_neg(word 8):int32):int64`;;

let MLD_ERR_INVALID_ARG =
  new_definition
   `MLD_ERR_INVALID_ARG = word_zx(word_neg(word 9):int32):int64`;;

let MLD_ERR_CONSTANTS =
 [MLD_OK; MLD_ERR_FAIL; MLD_ERR_OUT_OF_MEMORY; MLD_ERR_RNG_FAIL;
  MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED; MLD_ERR_SIGNING_PAUSED;
  MLD_ERR_INVALID_SIGNATURE; MLD_ERR_INVALID_KEY; MLD_ERR_PCT_FAIL;
  MLD_ERR_INVALID_ARG];;

(* ------------------------------------------------------------------------- *)
(* Signing: the return code and the signature buffer (as a number; the       *)
(* buffer is zero unless the code is MLD_OK) for the outcome of the model. A *)
(* context of more than 255 bytes (MLDSA_Sign_Error_BadContext) is           *)
(* MLD_ERR_INVALID_ARG, and exhausting the attempts, which the model with a  *)
(* bound (mldsa_sign p (SOME N)) gives as MLDSA_Sign_Error_OutOfAttempts,    *)
(* is MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED. The code MLD_ERR_RNG_FAIL has no      *)
(* counterpart in the model, which has the randomness as an argument.        *)
(* ------------------------------------------------------------------------- *)

let mld_sign_status = define
 `mld_sign_status (MLDSA_Sign_Success (sg:byte list)) =
    (MLD_OK,num_of_bytelist sg) /\
  mld_sign_status MLDSA_Sign_Error_BadContext = (MLD_ERR_INVALID_ARG,0) /\
  mld_sign_status MLDSA_Sign_Error_OutOfAttempts =
    (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED,0)`;;

(* ------------------------------------------------------------------------- *)
(* Verification: MLD_OK for a valid signature, MLD_ERR_INVALID_SIGNATURE for *)
(* an invalid one, and MLD_ERR_INVALID_ARG for a context that is too long.   *)
(* ------------------------------------------------------------------------- *)

let mld_verify_status = define
 `mld_verify_status MLDSA_Verify_Success = MLD_OK /\
  mld_verify_status MLDSA_Verify_Error_InvalidSignature =
    MLD_ERR_INVALID_SIGNATURE /\
  mld_verify_status MLDSA_Verify_Error_BadContext = MLD_ERR_INVALID_ARG`;;

(* The code for a boolean result, as the machine code computes it from the   *)
(* result of the check of the signature.                                     *)

let MLD_VERIFY_STATUS_OF_BOOL = prove
 (`!b. mld_verify_status (mldsa_verify_of_bool b) =
       if b then MLD_OK else MLD_ERR_INVALID_SIGNATURE`,
  GEN_TAC THEN REWRITE_TAC[mldsa_verify_of_bool] THEN COND_CASES_TAC THEN
  REWRITE_TAC[mld_verify_status]);;

(* ------------------------------------------------------------------------- *)
(* The number of signing attempts, MLD_MAX_KAPPA / l = (65535 - l) DIV l for *)
(* l polynomials in the vector y, after which signing returns                *)
(* MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED (16382, 13106 and 9361 for ML-DSA-44, -65 *)
(* and -87). mldsa_sign takes it as SOME N, as its bound.                    *)
(* ------------------------------------------------------------------------- *)

let mld_max_signing_attempts =
  new_definition `mld_max_signing_attempts l = (65535 - l) DIV l`;;

let MLD_MAX_SIGNING_ATTEMPTS_CLAUSES = prove
 (`mld_max_signing_attempts 4 = 16382 /\
   mld_max_signing_attempts 5 = 13106 /\
   mld_max_signing_attempts 7 = 9361`,
  REWRITE_TAC[mld_max_signing_attempts] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The codes as the numerals of the 64-bit words, to relate the theorems     *)
(* stated with the names above to those about the machine code.              *)

let MLD_ERR_LITERALS = prove
 (`MLD_OK = word 0 /\
   MLD_ERR_FAIL = word 4294967295 /\
   MLD_ERR_OUT_OF_MEMORY = word 4294967294 /\
   MLD_ERR_RNG_FAIL = word 4294967293 /\
   MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED = word 4294967292 /\
   MLD_ERR_SIGNING_PAUSED = word 4294967291 /\
   MLD_ERR_INVALID_SIGNATURE = word 4294967290 /\
   MLD_ERR_INVALID_KEY = word 4294967289 /\
   MLD_ERR_PCT_FAIL = word 4294967288 /\
   MLD_ERR_INVALID_ARG = word 4294967287`,
  REWRITE_TAC MLD_ERR_CONSTANTS THEN CONV_TAC WORD_REDUCE_CONV);;
