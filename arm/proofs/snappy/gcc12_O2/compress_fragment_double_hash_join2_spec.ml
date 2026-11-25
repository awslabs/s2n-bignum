(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from join2, emit_remainder (phase *)
(* 5): EmitLiteral of the rest of the input, with memcpy through the PLT,    *)
(* and the return with the output of the model. Two statements: with the     *)
(* correctness contract of memcpy (the output), and with the contract with   *)
(* memory safety (the output and the events in bounds).                      *)
(* (see compress_fragment_double_hash_model_spec.ml).                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let snappy_cf2_join2_stmt contract post =
  parse_term
   ("!" ^ snappy_cf2_vars ^ " st. " ^ snappy_cf2_hyps ^ " /\\
     " ^ contract ^ " (imp \"memcpy\") ea el ev /\\
     snappy_cf2_reach src st
     ==> ensures arm
          (\\s. snappy_cf2_at " ^ snappy_cf2_args ^ "
                CompressFragmentDoubleHash_join2 st s)
          (\\s. " ^ post ^ ")
          (" ^ snappy_cf2_frame ^ ")");;

let SNAPPY_CF2_GCC12_O2_JOIN2_STMT =
  snappy_cf2_join2_stmt "memcpy_contract"
   "snappy_cf2_post src op stackpointer returnaddress x19 x20 x21 x29 s";;

let SNAPPY_CF2_GCC12_O2_JOIN2_SAFE_STMT =
  snappy_cf2_join2_stmt "memcpy_correct_safe_contract"
   "snappy_cf2_post_safe src inp op table table2 ts pc stackpointer
      returnaddress x19 x20 x21 x29 ea el e s";;

let SNAPPY_CF2_GCC12_O2_JOIN2 = assume_spec SNAPPY_CF2_GCC12_O2_JOIN2_STMT;;
let SNAPPY_CF2_GCC12_O2_JOIN2_SAFE =
  assume_spec SNAPPY_CF2_GCC12_O2_JOIN2_SAFE_STMT;;
