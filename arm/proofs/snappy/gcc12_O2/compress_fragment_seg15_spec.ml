(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment (gcc12_O2): the statements of the entry, of the segment  *)
(* from loop1 (phase 1) and of the segment from join4 (phase 5,              *)
(* emit_remainder) to the return. They are proved in                         *)
(* compress_fragment_seg15_proof.ml, a job of its own in the link; the proof *)
(* of CompressFragment uses them as contracts (common/relative.ml).          *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_lib.ml";;

let SNAPPY_CF1_ENTRY_STMT = parse_term
  ("!pc src (inp:byte list) op table stackpointer x19 x29 returnaddress rw ea el ev imp
      (e:uarch_event list).
     " ^ snappy_cf1_hyps_str ^ "
     ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
               read PC s = word(pc + CompressFragment) /\\
               read SP s = stackpointer /\\
               read X30 s = returnaddress /\\
               C_ARGUMENTS [src; word(LENGTH inp); op;
                            table; word(snappy_table_size (LENGTH inp))] s /\\
               read (memory :> bytes(word(pc + libsnappy_rw),
                                     libsnappy_rw_size)) s = rw /\\
               read (memory :> bytes(ea,el)) s = ev /\\
               read (memory :> bytelist(src,LENGTH inp)) s = inp /\\
               read (memory :> bytes(table,
                       2 * snappy_table_size (LENGTH inp))) s = 0 /\\
               read events s = e /\\
               read X19 s = x19 /\\ read X29 s = x29)
          (\\s. ?n. snappy_cf1_cut pc src inp op table stackpointer x19 x29
                       returnaddress rw ea el ev e n s)
          (" ^ snappy_cf1_frame_str ^ ")");;

let SNAPPY_CF1_ENTRY = assume_spec SNAPPY_CF1_ENTRY_STMT;;
let SNAPPY_CF1_SEG1 = assume_spec SNAPPY_CF1_SEG1_STMT;;
let SNAPPY_CF1_SEG5 = assume_spec SNAPPY_CF1_SEG5_STMT;;
let SNAPPY_CF1_SEG5_SAFE = assume_spec SNAPPY_CF1_SEG5_SAFE_STMT;;
