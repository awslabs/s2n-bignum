(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The equivalence lemmas for K-PKE and ML-KEM without sample_ok premises.   *)
(*                                                                           *)
(* Each `*_EQUIV` lemma of kpke.ml and mlkem.ml assumes, for all matrix      *)
(* positions (i,j), that sample_ok holds for the 34-byte seed               *)
(*   APPEND rho [word j; word i]                                             *)
(* where rho is either `FST (mlkem_g ...)` (key generation) or              *)
(* `mlkem_slice a 32 y` (encryption, decapsulation).  Both are 32 bytes     *)
(* long, so SAMPLE_OK_ALL discharges the premise.                            *)
(* ========================================================================= *)

(* Drop the sample_ok premises of a conditional lemma.  The remaining       *)
(* premises are unchanged, so the result is exactly the FINAL statement.    *)

let FINAL_DROP_SAMPLE_OK th =
  let th1 = PURE_REWRITE_RULE
    [SAMPLE_OK_SLICE; SAMPLE_OK_G] th in
  let th2 = REWRITE_RULE[] th1 in
  th2;;

(* Prove a FINAL statement from the matching conditional lemma. *)

let FINAL_TAC th =
  let th' = FINAL_DROP_SAMPLE_OK th in
  ACCEPT_TAC th' ORELSE (MP_TAC th' THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.                                                                    *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_512_FINAL = prove
 (KPKE_KEYGEN_512_FINAL_STMT, FINAL_TAC KPKE_KEYGEN_512_EQUIV);;

let KPKE_ENCRYPT_512_FINAL = prove
 (KPKE_ENCRYPT_512_FINAL_STMT, FINAL_TAC KPKE_ENCRYPT_512_EQUIV);;

let KPKE_KEYGEN_768_FINAL = prove
 (KPKE_KEYGEN_768_FINAL_STMT, FINAL_TAC KPKE_KEYGEN_768_EQUIV);;

let KPKE_ENCRYPT_768_FINAL = prove
 (KPKE_ENCRYPT_768_FINAL_STMT, FINAL_TAC KPKE_ENCRYPT_768_EQUIV);;

let KPKE_KEYGEN_1024_FINAL = prove
 (KPKE_KEYGEN_1024_FINAL_STMT, FINAL_TAC KPKE_KEYGEN_1024_EQUIV);;

let KPKE_ENCRYPT_1024_FINAL = prove
 (KPKE_ENCRYPT_1024_FINAL_STMT, FINAL_TAC KPKE_ENCRYPT_1024_EQUIV);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM, internal algorithms.                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KEYGEN_INTERNAL_512_FINAL = prove
 (MLKEM_KEYGEN_INTERNAL_512_FINAL_STMT,
  FINAL_TAC MLKEM_KEYGEN_INTERNAL_512_EQUIV);;

let MLKEM_ENCAPS_INTERNAL_512_FINAL = prove
 (MLKEM_ENCAPS_INTERNAL_512_FINAL_STMT,
  FINAL_TAC MLKEM_ENCAPS_INTERNAL_512_EQUIV);;

let MLKEM_DECAPS_INTERNAL_512_FINAL = prove
 (MLKEM_DECAPS_INTERNAL_512_FINAL_STMT,
  FINAL_TAC MLKEM_DECAPS_INTERNAL_512_EQUIV);;

let MLKEM_KEYGEN_INTERNAL_768_FINAL = prove
 (MLKEM_KEYGEN_INTERNAL_768_FINAL_STMT,
  FINAL_TAC MLKEM_KEYGEN_INTERNAL_768_EQUIV);;

let MLKEM_ENCAPS_INTERNAL_768_FINAL = prove
 (MLKEM_ENCAPS_INTERNAL_768_FINAL_STMT,
  FINAL_TAC MLKEM_ENCAPS_INTERNAL_768_EQUIV);;

let MLKEM_DECAPS_INTERNAL_768_FINAL = prove
 (MLKEM_DECAPS_INTERNAL_768_FINAL_STMT,
  FINAL_TAC MLKEM_DECAPS_INTERNAL_768_EQUIV);;

let MLKEM_KEYGEN_INTERNAL_1024_FINAL = prove
 (MLKEM_KEYGEN_INTERNAL_1024_FINAL_STMT,
  FINAL_TAC MLKEM_KEYGEN_INTERNAL_1024_EQUIV);;

let MLKEM_ENCAPS_INTERNAL_1024_FINAL = prove
 (MLKEM_ENCAPS_INTERNAL_1024_FINAL_STMT,
  FINAL_TAC MLKEM_ENCAPS_INTERNAL_1024_EQUIV);;

let MLKEM_DECAPS_INTERNAL_1024_FINAL = prove
 (MLKEM_DECAPS_INTERNAL_1024_FINAL_STMT,
  FINAL_TAC MLKEM_DECAPS_INTERNAL_1024_EQUIV);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM, external algorithms.                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KEYGEN_512_FINAL = prove
 (MLKEM_KEYGEN_512_FINAL_STMT, FINAL_TAC MLKEM_KEYGEN_512_EQUIV);;

let MLKEM_ENCAPS_512_FINAL = prove
 (MLKEM_ENCAPS_512_FINAL_STMT, FINAL_TAC MLKEM_ENCAPS_512_EQUIV);;

let MLKEM_DECAPS_512_FINAL = prove
 (MLKEM_DECAPS_512_FINAL_STMT, FINAL_TAC MLKEM_DECAPS_512_EQUIV);;

let MLKEM_KEYGEN_768_FINAL = prove
 (MLKEM_KEYGEN_768_FINAL_STMT, FINAL_TAC MLKEM_KEYGEN_768_EQUIV);;

let MLKEM_ENCAPS_768_FINAL = prove
 (MLKEM_ENCAPS_768_FINAL_STMT, FINAL_TAC MLKEM_ENCAPS_768_EQUIV);;

let MLKEM_DECAPS_768_FINAL = prove
 (MLKEM_DECAPS_768_FINAL_STMT, FINAL_TAC MLKEM_DECAPS_768_EQUIV);;

let MLKEM_KEYGEN_1024_FINAL = prove
 (MLKEM_KEYGEN_1024_FINAL_STMT, FINAL_TAC MLKEM_KEYGEN_1024_EQUIV);;

let MLKEM_ENCAPS_1024_FINAL = prove
 (MLKEM_ENCAPS_1024_FINAL_STMT, FINAL_TAC MLKEM_ENCAPS_1024_EQUIV);;

let MLKEM_DECAPS_1024_FINAL = prove
 (MLKEM_DECAPS_1024_FINAL_STMT, FINAL_TAC MLKEM_DECAPS_1024_EQUIV);;

(* ------------------------------------------------------------------------- *)
(* Encaps and Decaps in both directions.                                     *)
(*                                                                           *)
(* The generated Encaps and Decaps do not run the input check; the handwritten *)
(* mlkem_encaps_checked and mlkem_decaps_checked are `if check then SOME _ else NONE`. The   *)
(* statements compose the generated function with the generated check:       *)
(* _AGREE: when the check passes, the generated function returns a result    *)
(* exactly when the handwritten one returns SOME of it. _REJECT: when the    *)
(* check fails, the handwritten function returns NONE. Both follow from the  *)
(* one-way lemmas above (which assume SOME) and the equations for the checks.*)
(* ------------------------------------------------------------------------- *)

let FINAL_INJ_RESULT = injectivity "native_result";;
let FINAL_INJ_BOTTOM = injectivity "native_bottom";;
let FINAL_INJ_OPTION = injectivity "option";;

(* Turn a premise `check ... = Value T` or `= Value F` into the handwritten  *)
(* check or its negation.                                                    *)

let FINAL_CHECK_TAC chk =
  RULE_ASSUM_TAC (REWRITE_RULE[chk; FINAL_INJ_RESULT; EQ_CLAUSES]);;

let final_encaps_agree stmt chk fin p = prove
 (stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FINAL_CHECK_TAC chk THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC (SPECL [`ent:num->(byte list)option`; `ek:byte list`;
                   `m:byte list`;
                   parse_term ("mlkem_encaps_internal " ^ p ^ " ek m")] fin) THEN
    ASM_REWRITE_TAC[mlkem_encaps_checked; FINAL_INJ_RESULT; FINAL_INJ_BOTTOM;
                    FINAL_INJ_OPTION] THEN
    MESON_TAC[];
    DISCH_TAC THEN MP_TAC (SPEC_ALL fin) THEN ASM_REWRITE_TAC[]]);;

let final_encaps_reject stmt chk p = prove
 (stmt,
  REPEAT STRIP_TAC THEN FINAL_CHECK_TAC chk THEN
  ASM_REWRITE_TAC[mlkem_encaps_checked]);;

let final_decaps_agree stmt chk fin p = prove
 (stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FINAL_CHECK_TAC chk THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC (SPECL [`dk:byte list`; `c:byte list`;
                   parse_term ("mlkem_decaps_internal " ^ p ^ " dk c")] fin) THEN
    ASM_REWRITE_TAC[mlkem_decaps_checked; FINAL_INJ_RESULT; FINAL_INJ_OPTION] THEN
    MESON_TAC[];
    DISCH_TAC THEN MP_TAC (SPEC_ALL fin) THEN ASM_REWRITE_TAC[]]);;

let final_decaps_reject stmt chk p = prove
 (stmt,
  REPEAT STRIP_TAC THEN FINAL_CHECK_TAC chk THEN
  ASM_REWRITE_TAC[mlkem_decaps_checked]);;

let MLKEM_ENCAPS_512_AGREE = final_encaps_agree MLKEM_ENCAPS_512_AGREE_STMT
  MLKEM_EK_CHECK_512_EQUIV MLKEM_ENCAPS_512_FINAL "mlkem512";;
let MLKEM_ENCAPS_512_REJECT = final_encaps_reject MLKEM_ENCAPS_512_REJECT_STMT
  MLKEM_EK_CHECK_512_EQUIV "mlkem512";;
let MLKEM_DECAPS_512_AGREE = final_decaps_agree MLKEM_DECAPS_512_AGREE_STMT
  MLKEM_DECAPS_CHECK_512_EQUIV MLKEM_DECAPS_512_FINAL "mlkem512";;
let MLKEM_DECAPS_512_REJECT = final_decaps_reject MLKEM_DECAPS_512_REJECT_STMT
  MLKEM_DECAPS_CHECK_512_EQUIV "mlkem512";;

let MLKEM_ENCAPS_768_AGREE = final_encaps_agree MLKEM_ENCAPS_768_AGREE_STMT
  MLKEM_EK_CHECK_768_EQUIV MLKEM_ENCAPS_768_FINAL "mlkem768";;
let MLKEM_ENCAPS_768_REJECT = final_encaps_reject MLKEM_ENCAPS_768_REJECT_STMT
  MLKEM_EK_CHECK_768_EQUIV "mlkem768";;
let MLKEM_DECAPS_768_AGREE = final_decaps_agree MLKEM_DECAPS_768_AGREE_STMT
  MLKEM_DECAPS_CHECK_768_EQUIV MLKEM_DECAPS_768_FINAL "mlkem768";;
let MLKEM_DECAPS_768_REJECT = final_decaps_reject MLKEM_DECAPS_768_REJECT_STMT
  MLKEM_DECAPS_CHECK_768_EQUIV "mlkem768";;

let MLKEM_ENCAPS_1024_AGREE = final_encaps_agree MLKEM_ENCAPS_1024_AGREE_STMT
  MLKEM_EK_CHECK_1024_EQUIV MLKEM_ENCAPS_1024_FINAL "mlkem1024";;
let MLKEM_ENCAPS_1024_REJECT = final_encaps_reject MLKEM_ENCAPS_1024_REJECT_STMT
  MLKEM_EK_CHECK_1024_EQUIV "mlkem1024";;
let MLKEM_DECAPS_1024_AGREE = final_decaps_agree MLKEM_DECAPS_1024_AGREE_STMT
  MLKEM_DECAPS_CHECK_1024_EQUIV MLKEM_DECAPS_1024_FINAL "mlkem1024";;
let MLKEM_DECAPS_1024_REJECT = final_decaps_reject MLKEM_DECAPS_1024_REJECT_STMT
  MLKEM_DECAPS_CHECK_1024_EQUIV "mlkem1024";;
