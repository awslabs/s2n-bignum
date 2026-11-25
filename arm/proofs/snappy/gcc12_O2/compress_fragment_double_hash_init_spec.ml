(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The start of CompressFragmentDoubleHash: the prologue and the setup of    *)
(* the constants, up to the point of the model's initial state (loop1 for    *)
(* 15 bytes or more, join2 for less), with the empty output and the zeroed   *)
(* tables (see compress_fragment_double_hash_model_spec.ml).                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let snappy_cf2_entry_pre =
 "aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
  read PC s = word(pc + CompressFragmentDoubleHash) /\\
  read SP s = stackpointer /\\
  read X30 s = returnaddress /\\
  C_ARGUMENTS [inp; word(LENGTH src); op; table; word ts; table2] s /\\
  read (memory :> bytes(inp,LENGTH src)) s = num_of_bytelist src /\\
  read (memory :> bytes(table,2 * ts)) s = 0 /\\
  read (memory :> bytes(table2,2 * ts)) s = 0 /\\
  read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SNAPPY_CF2_GCC12_O2_INIT_STMT = parse_term
 ("!" ^ snappy_cf2_vars ^ ". " ^ snappy_cf2_hyps ^ "
     ==> ensures arm
          (\\s. " ^ snappy_cf2_entry_pre ^ " /\\
               read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\
               read X29 s = x29 /\\ read events s = e)
          (\\s. ?pt st. (snappy_cf2_reach src st /\\ snappy_cf2_point pt) /\\
                       snappy_cf2_at " ^ snappy_cf2_args ^ " pt st s)
          (" ^ snappy_cf2_frame ^ ")");;

let SNAPPY_CF2_GCC12_O2_INIT = assume_spec SNAPPY_CF2_GCC12_O2_INIT_STMT;;
