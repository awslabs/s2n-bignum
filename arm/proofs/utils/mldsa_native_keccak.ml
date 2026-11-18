(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's Keccak code that do not depend on *)
(* the build, copied from utils/mlkem_native.ml (which is not loaded, see    *)
(* utils/mldsa_native.ml).                                                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native.ml";;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:armstate.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;
