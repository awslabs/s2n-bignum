(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A check that every word of the executable sections of the image (.init,   *)
(* .plt, .text and .fini) decodes to an instruction of the AArch64 model,    *)
(* by making the decoding theorems for all of them. The proofs only decode   *)
(* the code that they simulate; this shows that none of them can fail for   *)
(* want of an instruction.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;

let SNAPPY_LIBSNAPPY_GCC12_O2_ALL_CODE_EXEC =
  let sections = ["libsnappy_init"; "libsnappy_plt"; "libsnappy_text";
                  "libsnappy_fini"] in
  let ranges = map layout_range sections in
  let th = time (ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc) ranges in
  let n = itlist (fun (lo,hi) acc ->
    itlist (fun k acc ->
      match (snd th).(k) with
        Some _ -> acc + 1
      | None -> failwith ("no decoding theorem at " ^ string_of_int k))
      (map (fun i -> lo + 4 * i) (0--((hi - lo) / 4 - 1))) acc) ranges 0 in
  Printf.printf "image_decodes: all %d words of %s decode\n%!" n
    (String.concat ", " sections);
  th;;
