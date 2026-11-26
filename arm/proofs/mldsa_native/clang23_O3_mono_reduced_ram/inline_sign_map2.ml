(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The straight-line poly_shiftl and poly_sub of inline_sign_map.ml for the  *)
(* frames of mldsa65_verify_internal and mldsa87_verify_internal: the same   *)
(* statements and proofs with the offsets of the polynomials as parameters.  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;

(*** poly_shiftl in place at F + off ***)

let INLINE_SHIFTL_STMT_AT mc start stop off (mods:string list) =
  INLINE_MAP_STMT mc start stop ["x",off] off "mld_poly_shiftl x i" off 1024
   mods "" (Printf.sprintf "read X0 s = word_add fp (word %d) /\\" off);;

(*** poly_sub at F + yoff of the polynomial at F + xoff, with -q at F + coff ***)
(*** in each lane, reading the stack from F + coff to the end of y          ***)

let INLINE_SUB_STMT_AT mc start stop xoff yoff coff (mods:string list) =
  INLINE_MAP_STMT mc start stop ["x",xoff; "y",yoff] yoff "mld_poly_sub y x i"
   coff (yoff + 1024 - coff) mods
   (Printf.sprintf
     "read (memory :> bytes128 (word_add fp (word %d))) s =
        word 0xff801fffff801fffff801fffff801fff /\\" coff)
   "read X8 s = word 0 /\\
    read Q4 s = word 0x00400000004000000040000000400000 /\\
    read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\";;

(*** The instances in mldsa65_verify_internal (shiftl 151 instructions, ***)
(*** sub 238)                                                            ***)

let INLINE_SHIFTL65_START = "mldsa65_verify_internal_loop8_exit";;

let INLINE_SHIFTL65_STOP =
  string_of_int (layout "mldsa65_verify_internal_after_mldsa_poly_ntt_7" - 4);;

let INLINE_SHIFTL65_TERM =
  INLINE_SHIFTL_STMT_AT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   INLINE_SHIFTL65_START INLINE_SHIFTL65_STOP 352 ("X0"::INLINE_MAP_QMODS);;

let INLINE_SHIFTL65 () =
  INLINE_MAP_PROVE INLINE_SHIFTL65_TERM
   (INLINE_LOOP_EXEC INLINE_SHIFTL65_START INLINE_SHIFTL65_STOP)
   ["x",352] 151 [mld_poly_shiftl] [INLINE_SHL13_LANE];;

let INLINE_SUB65_TERM =
  INLINE_SUB_STMT_AT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   "mldsa65_verify_internal_loop9_exit" "mldsa65_verify_internal_loop10"
   352 1376 304 ("X8"::INLINE_MAP_QMODS);;

let INLINE_SUB65 () =
  INLINE_MAP_PROVE INLINE_SUB65_TERM
   (INLINE_LOOP_EXEC "mldsa65_verify_internal_loop9_exit"
                     "mldsa65_verify_internal_loop10")
   ["x",352; "y",1376] 238 [mld_poly_sub] [];;

(*** The instances in mldsa87_verify_internal (the same offsets; shiftl 151 ***)
(*** instructions, sub 238)                                                ***)

let INLINE_SHIFTL87_START = "mldsa87_verify_internal_loop10_exit";;

let INLINE_SHIFTL87_STOP =
  string_of_int (layout "mldsa87_verify_internal_after_mldsa_poly_ntt_9" - 4);;

let INLINE_SHIFTL87_TERM =
  INLINE_SHIFTL_STMT_AT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   INLINE_SHIFTL87_START INLINE_SHIFTL87_STOP 352 ("X0"::INLINE_MAP_QMODS);;

let INLINE_SHIFTL87 () =
  INLINE_MAP_PROVE INLINE_SHIFTL87_TERM
   (INLINE_LOOP_EXEC INLINE_SHIFTL87_START INLINE_SHIFTL87_STOP)
   ["x",352] 151 [mld_poly_shiftl] [INLINE_SHL13_LANE];;

let INLINE_SUB87_TERM =
  INLINE_SUB_STMT_AT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   "mldsa87_verify_internal_loop11_exit" "mldsa87_verify_internal_loop12"
   352 1376 304 ("X8"::INLINE_MAP_QMODS);;

let INLINE_SUB87 () =
  INLINE_MAP_PROVE INLINE_SUB87_TERM
   (INLINE_LOOP_EXEC "mldsa87_verify_internal_loop11_exit"
                     "mldsa87_verify_internal_loop12")
   ["x",352; "y",1376] 238 [mld_poly_sub] [];;
