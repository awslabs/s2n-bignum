(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The signature codec of the generated specification: sigEncode and         *)
(* sigDecode (hints.ml) need BitPack and BitUnpack of one polynomial z,      *)
(* which encode.ml proves (PACK_BITPACK_*, PACK_BITUNPACK_*: the             *)
(* statements of ENC_BITPACK_*, ENC_BITUNPACK_* checked against the          *)
(* hypotheses hints_bitpack_hyp and hints_bitunpack_hyp of hints.ml).        *)
(* This file discharges those hypotheses: EQ_SIGENCODE_FINAL_P and           *)
(* EQ_SIGDECODE_FINAL_P (P = MLDSA44, MLDSA65, MLDSA87), and the same        *)
(* hypothesis of the Sign callables 0 of callables.ml.                       *)
(*                                                                           *)
(* Load after base.ml and common.ml.                                   *)
(* ========================================================================= *)
needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/ball.ml";;
needs "common/fips204/generated/core/hints.ml";;
needs "common/fips204/generated/core/encode.ml";;
needs "common/fips204/generated/core/callables.ml";;

let PACK_BITPACK_131071 = ENC_BITPACK_131071;;
let PACK_BITPACK_524287 = ENC_BITPACK_524287;;
let PACK_BITUNPACK_131071 = ENC_BITUNPACK_131071;;
let PACK_BITUNPACK_524287 = ENC_BITUNPACK_524287;;

(* Fail at load time if the forms ever drift from hints.ml.                  *)
List.iter (fun (th,h) ->
  if not (aconv (concl th) h) then failwith "sigcodec.ml: statement mismatch")
 [PACK_BITPACK_131071, hints_bitpack_hyp (131072,18);
  PACK_BITPACK_524287, hints_bitpack_hyp (524288,20);
  PACK_BITUNPACK_131071, hints_bitunpack_hyp (131072,18);
  PACK_BITUNPACK_524287, hints_bitunpack_hyp (524288,20)];;

let EQ_SIGENCODE_FINAL_MLDSA44 = MP EQ_SIGENCODE_MLDSA44 PACK_BITPACK_131071;;
let EQ_SIGENCODE_FINAL_MLDSA65 = MP EQ_SIGENCODE_MLDSA65 PACK_BITPACK_524287;;
let EQ_SIGENCODE_FINAL_MLDSA87 = MP EQ_SIGENCODE_MLDSA87 PACK_BITPACK_524287;;
let EQ_SIGDECODE_FINAL_MLDSA44 = MP EQ_SIGDECODE_MLDSA44 PACK_BITUNPACK_131071;;
let EQ_SIGDECODE_FINAL_MLDSA65 = MP EQ_SIGDECODE_MLDSA65 PACK_BITUNPACK_524287;;
let EQ_SIGDECODE_FINAL_MLDSA87 = MP EQ_SIGDECODE_MLDSA87 PACK_BITUNPACK_524287;;

(* The Sign callables 0 (sigEncode) of callables.ml carry the same BitPack   *)
(* hypothesis; discharge it.                                                 *)

let EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA44 =
  MP EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA44 PACK_BITPACK_131071;;
let EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA65 =
  MP EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA65 PACK_BITPACK_524287;;
let EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA87 =
  MP EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA87 PACK_BITPACK_524287;;
let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA44 =
  MP EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA44 PACK_BITPACK_131071;;
let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA65 =
  MP EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA65 PACK_BITPACK_524287;;
let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA87 =
  MP EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA87 PACK_BITPACK_524287;;

List.iter (fun th -> if not(hyp th = []) || (is_imp(snd(strip_forall(concl th))) && false)
                     then failwith "hints_final: stray hypothesis")
 [EQ_SIGENCODE_FINAL_MLDSA44; EQ_SIGENCODE_FINAL_MLDSA65;
  EQ_SIGENCODE_FINAL_MLDSA87; EQ_SIGDECODE_FINAL_MLDSA44;
  EQ_SIGDECODE_FINAL_MLDSA65; EQ_SIGDECODE_FINAL_MLDSA87;
  EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA44;
  EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA65;
  EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA87;
  EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA44;
  EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA65;
  EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA87];;
