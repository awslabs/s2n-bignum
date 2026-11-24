(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_rej_uniform_alt_VARIABLE_TIME (see     *)
(* rej_uniform_alt_variable_time_spec.ml). The standalone proof of         *)
(* arm/proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml runs here, in the job *)
(* of this file, so that it runs once: it proves the correctness theorem   *)
(* and the lemmas. The events of the rejection sampling and the theorem    *)
(* with the result and the events are proved after it by                   *)
(* arm/proofs/utils/mlkem_native2_rej_full.ml.                             *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/rej_uniform_alt_variable_time_spec.ml";;

loadt "arm/proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml";;
loadt "arm/proofs/utils/mlkem_native2_rej_full.ml";;
