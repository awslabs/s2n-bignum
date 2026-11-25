(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressAllTags<SnappyDecompressionValidator> (gcc12_O2): the segment   *)
(* from the cut point T (one tag of the slow path) with the window in        *)
(* scratch_ (S), restricted to the tag class C2: an antecedent on the        *)
(* tag byte EL 0 rest (dat_class_conds). The proof of the function           *)
(* combines the classes.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/dat_validator_lib.ml";;

let SNAPPY_DAT_VALIDATOR_T_S_C2_STMT = dat_class_stmt (dat_class_pre "S") dat_class_nexts "C2";;

let SNAPPY_DAT_VALIDATOR_T_S_C2 = assume_spec SNAPPY_DAT_VALIDATOR_T_S_C2_STMT;;
