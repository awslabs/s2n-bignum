(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa44_signature_internal,                      *)
(* mldsa65_signature_internal and mldsa87_signature_internal of the build    *)
(* with MLD_CONFIG_REDUCE_RAM (gcc12_O2_reduced_ram), in addition to those   *)
(* of utils/mldsa_native_signing.ml. In this build the code keeps neither    *)
(* s1, s2 and t0 in the NTT domain nor y: each attempt unpacks polynomial i  *)
(* of s1, s2 or t0 from the secret key (mld_polyeta_unpack,                  *)
(* mld_polyt0_unpack) and transforms it (mld_poly_ntt) when it needs it, and *)
(* samples polynomial i of y again (mld_poly_uniform_gamma1) from rho'' and  *)
(* kappa + i. These lemmas turn the results of these calls, polynomial by    *)
(* polynomial, into the polynomials of the vectors of the C model            *)
(* (common/mldsa_native_sign.ml: mld_polyvec_map mld_poly_ntt of the         *)
(* unpacked vectors, and mld_sign_y), for the coefficients below 256 that    *)
(* the callees read. kappa is a 16-bit word on the stack, which the code     *)
(* copies into the structure of y (struct mld_yvec_lazy) and tests against   *)
(* its bound with a 16-bit CMP.                                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes of the secret key (of len bytes) from offset off, as the        *)
(* unpacking of a polynomial reads them (the n bytes at sk + off).           *)
(* ------------------------------------------------------------------------- *)

let SIGN_SK_SLICE = prove
 (`!(sk:int64) (skb:num->byte) len off n (s:x86state).
        (!j. j < len
             ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
        off + n <= len
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add sk (word(off + j)))) s =
                    skb(off + j)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Polynomial i of a vector unpacked from the bytes at off (P bytes per      *)
(* polynomial), and its NTT, as polynomials of the vectors of the model.     *)
(* ------------------------------------------------------------------------- *)

let SIGN_UNPACK_POLY_OF = prove
 (`!(f:(num->byte)->num->int32) P off i (skb:num->byte) (B:int64) d
    (s:x86state).
     (!k. k < 256
          ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
              f (\j. skb((off + P * i) + j)) k)
     ==> (!k. k < 256
              ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                  mld_poly_of (mld_polyvec_unpack P f (\j. skb(off + j))) i
                   k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mld_poly_of; MLD_POLYVEC_UNPACK_COEFF] THEN
  REWRITE_TAC[ADD_ASSOC]);;

let SIGN_NTT_POLY_OF = prove
 (`!(x:num->int32) i (B:int64) d (s:x86state).
     (!k. k < 256
          ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
              mld_poly_ntt (mld_poly_of x i) k)
     ==> (!k. k < 256
              ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                  mld_poly_of (mld_polyvec_map mld_poly_ntt x) i k)`,
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP]);;

(* ------------------------------------------------------------------------- *)
(* The nonce kappa + i of polynomial i of y, as the code computes it from    *)
(* kappa, a 16-bit word in memory, and the 64-bit counter i, and the         *)
(* polynomial that mld_poly_uniform_gamma1 samples with it, polynomial i of  *)
(* mld_sign_y.                                                               *)
(* ------------------------------------------------------------------------- *)

let SIGN_POW2_MOD_TAC =
  REWRITE_TAC[ARITH_RULE `65536 = 2 EXP 16`;
              ARITH_RULE `4294967296 = 2 EXP 32`;
              ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV;;

let SIGN_NONCE16 = prove
 (`!k i. (word_zx:int64->int16) ((word_zx:int32->int64) ((word_zx:int16->int32)
          (word (val ((word_zx:int32->int64)
            (word_add ((word_zx:int64->int32) ((word_zx:int32->int64)
                         ((word_zx:int16->int32) (word k))))
                      ((word_zx:int64->int32) (word i)))) MOD 65536)))) =
         word(k + i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
              DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  SIGN_POW2_MOD_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  SIGN_POW2_MOD_TAC);;

let SIGN_GAMMA_POLY_OF = prove
 (`!(g:num->int16->num->int32) rhop kappa i (B:int64) d (s:x86state).
     (!k. k < 256
          ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
              g rhop (word(kappa + i)) k)
     ==> (!k. k < 256
              ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                  mld_poly_of (mld_sign_y g rhop kappa) i k)`,
  SIMP_TAC[mld_sign_y; MLD_POLY_OF_POLYVEC]);;

(* ------------------------------------------------------------------------- *)
(* kappa, a 16-bit word on the stack: its copy into the structure of y (a    *)
(* zero-extended load and a 16-bit store) and its test against the bound,    *)
(* as CMP of the low 16 bits leaves it.                                      *)
(* ------------------------------------------------------------------------- *)

let SIGN_WORD16_OF_ZX = prove
 (`!x:int16. (word (val ((word_zx:int32->int64) ((word_zx:int16->int32) x))
                     MOD 65536):int16) = x`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ZX_GEN;
                           DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  SIGN_POW2_MOD_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SIGN_VAL_WORD_SUB_EQ_0_16 = prove
 (`!a b. a < 2 EXP 16 /\ b < 2 EXP 16
         ==> (val(word_sub (word a) (word b):int16) = 0 <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_16; MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Tactics: after the call that unpacks polynomial i with the function       *)
(* unpack of the model, put its result in the form of the model              *)
(* (SIGN_UNPACK_POLY_OF_TAC unpack), likewise after its NTT                  *)
(* (SIGN_NTT_POLY_OF_TAC) and after the sampling of polynomial i of y with   *)
(* the function g1 (SIGN_GAMMA_POLY_OF_TAC g1).                              *)
(* ------------------------------------------------------------------------- *)

let SIGN_UNPACK_POLY_OF_TAC unpack =
  let pat = subst [unpack,`f:(num->byte)->num->int32`]
   `!k. k < 256
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
            (f:(num->byte)->num->int32) (b:num->byte) k` in
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SIGN_UNPACK_POLY_OF o
    check (fun th -> can (term_match [] pat) (concl th)));;

let SIGN_NTT_POLY_OF_TAC =
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SIGN_NTT_POLY_OF o
    check (fun th -> can (term_match []
     `!k. k < 256
          ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
              mld_poly_ntt (mld_poly_of x i) k`) (concl th)));;

let SIGN_GAMMA_POLY_OF_TAC g1 =
  let pat = subst [g1,`g:num->int16->num->int32`]
   `!k. k < 256
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
            (g:num->int16->num->int32) (rhop:num) (word(kappa + i)) k` in
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_NONCE16]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SIGN_GAMMA_POLY_OF o
    check (fun th -> can (term_match [] pat) (concl th)));;
