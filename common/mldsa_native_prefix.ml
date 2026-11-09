(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the domain separation prefix of             *)
(* mldsa-native's signing and verification, the function                     *)
(* mld_prepare_domain_separation_prefix of sign.c with                       *)
(* mld_validate_hash_length and mld_get_hash_oid: for pure ML-DSA            *)
(* (hashalg = MLD_PREHASH_NONE = 0) it is 0 || |ctx| || ctx, and for         *)
(* HashML-DSA 1 || |ctx| || ctx || OID || ph, where OID is the DER encoding  *)
(* of the object identifier of the pre-hash function and ph the pre-hash.    *)
(* The function returns the length of the prefix, or 0 if the context is     *)
(* longer than 255 bytes or, for HashML-DSA, if hashalg is not one of the    *)
(* MLD_PREHASH_* constants 1 to 12 of sign.h or ph does not have the length  *)
(* of the output of that hash function.                                      *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The pre-hash functions MLD_PREHASH_SHA2_224, MLD_PREHASH_SHA2_256,        *)
(* MLD_PREHASH_SHA2_384, MLD_PREHASH_SHA2_512, MLD_PREHASH_SHA2_512_224,     *)
(* MLD_PREHASH_SHA2_512_256, MLD_PREHASH_SHA3_224, MLD_PREHASH_SHA3_256,     *)
(* MLD_PREHASH_SHA3_384, MLD_PREHASH_SHA3_512, MLD_PREHASH_SHAKE_128 and     *)
(* MLD_PREHASH_SHAKE_256 are 1 to 12. The length of their output, as         *)
(* mld_validate_hash_length checks it (0 for other values of hashalg), and   *)
(* the check itself, mld_validate_hash_length hashalg len = 0.               *)
(* ------------------------------------------------------------------------- *)

let mld_prehash_length = new_definition
 `mld_prehash_length hashalg =
    if hashalg = 1 then 28 else if hashalg = 2 then 32 else
    if hashalg = 3 then 48 else if hashalg = 4 then 64 else
    if hashalg = 5 then 28 else if hashalg = 6 then 32 else
    if hashalg = 7 then 28 else if hashalg = 8 then 32 else
    if hashalg = 9 then 48 else if hashalg = 10 then 64 else
    if hashalg = 11 then 32 else if hashalg = 12 then 64 else 0`;;

let mld_prehash_valid = new_definition
 `mld_prehash_valid hashalg len <=>
    1 <= hashalg /\ hashalg <= 12 /\ len = mld_prehash_length hashalg`;;

(* ------------------------------------------------------------------------- *)
(* The 11 bytes of the OID of the pre-hash function, from the table oid_map  *)
(* of mld_get_hash_oid: 06 09 (an OID of 9 bytes) and the encoding of        *)
(* 2.16.840.1.101.3.4.2.k, with k = 4, 1, 2, 3, 5, 6, ..., 12 for hashalg =  *)
(* 1, ..., 12.                                                               *)
(* ------------------------------------------------------------------------- *)

let mld_prehash_oid = new_definition
 `mld_prehash_oid hashalg =
    [word 0x06; word 0x09; word 0x60; word 0x86; word 0x48; word 0x01;
     word 0x65; word 0x03; word 0x04; word 0x02;
     word(if hashalg = 1 then 0x04 else if hashalg = 2 then 0x01 else
          if hashalg = 3 then 0x02 else if hashalg = 4 then 0x03 else
          if hashalg = 5 then 0x05 else if hashalg = 6 then 0x06 else
          if hashalg = 7 then 0x07 else if hashalg = 8 then 0x08 else
          if hashalg = 9 then 0x09 else if hashalg = 10 then 0x0A else
          if hashalg = 11 then 0x0B else 0x0C)]:byte list`;;

(* ------------------------------------------------------------------------- *)
(* The prefix for the context ctx and the pre-hash ph (ignored for pure      *)
(* ML-DSA), and the value that mld_prepare_domain_separation_prefix returns  *)
(* for the lengths ctxlen of ctx and phlen of ph: the length of the prefix,  *)
(* or 0 for the errors.                                                      *)
(* ------------------------------------------------------------------------- *)

let mld_domain_separation_prefix = new_definition
 `mld_domain_separation_prefix hashalg (ctx:byte list) (ph:byte list) =
    if hashalg = 0 then CONS (word 0) (CONS (word(LENGTH ctx)) ctx)
    else CONS (word 1)
          (CONS (word(LENGTH ctx))
            (APPEND ctx (APPEND (mld_prehash_oid hashalg) ph)))`;;

let mld_domain_separation_prefix_length = new_definition
 `mld_domain_separation_prefix_length hashalg ctxlen phlen =
    if 255 < ctxlen then 0
    else if hashalg = 0 then 2 + ctxlen
    else if mld_prehash_valid hashalg phlen then 2 + ctxlen + 11 + phlen
    else 0`;;

(* ------------------------------------------------------------------------- *)
(* The returned length is that of the prefix when it is not 0.               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLD_DOMAIN_SEPARATION_PREFIX = prove
 (`!hashalg ctx ph.
        ~(mld_domain_separation_prefix_length hashalg (LENGTH ctx)
           (LENGTH ph) = 0)
        ==> LENGTH(mld_domain_separation_prefix hashalg ctx ph) =
            mld_domain_separation_prefix_length hashalg (LENGTH ctx)
             (LENGTH ph)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length;
              mld_domain_separation_prefix] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; mld_prehash_oid] THEN ARITH_TAC);;
