(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mldsa-native's libmldsa.so compiled by     *)
(* gcc 12 with -O2 (see mldsa_native/README.md), as one image, and the       *)
(* versions for it of the rules in utils/mlkem_native_image.ml that transfer *)
(* the results for the individual functions to the same code in the image.   *)
(* Those rules do not depend on the library, only on the image. All the      *)
(* theorems about the image assume that it is loaded at an address pc that   *)
(* is a multiple of 4096, as the dynamic loader does, and that it does not   *)
(* wrap around the end of the address space, i.e.                            *)
(* pc + libmldsa_size <= 2 EXP 64. A function f in it is then at pc + f,     *)
(* with the names for the addresses and sizes in the binary that are listed  *)
(* in layout.ml.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native_image.ml";;

let mldsa_native_libmldsa_gcc12_O2_mc = define_from_elf
  "mldsa_native_libmldsa_gcc12_O2_mc"
  "arm/mldsa_native/gcc12_O2/libmldsa.o";;

let LENGTH_MLDSA_NATIVE_LIBMLDSA_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mldsa_native_libmldsa_gcc12_O2_mc);;

(* The image has the size given in the layout file.                          *)

let () =
  if dest_small_numeral(rhs(concl LENGTH_MLDSA_NATIVE_LIBMLDSA_GCC12_O2_MC)) <>
     layout "libmldsa_size"
  then failwith "The size of the image is not libmldsa_size";;

(* ------------------------------------------------------------------------- *)
(* The rules of utils/mlkem_native_image.ml for this image.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_IMAGE_CODE_RULE =
  MLKEM_NATIVE_IMAGE_CODE_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc;;

let MLDSA_NATIVE_IMAGE_DATA_RULE =
  MLKEM_NATIVE_IMAGE_DATA_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc;;

let MLDSA_NATIVE_IMAGE_CONST_RULE =
  MLKEM_NATIVE_IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc;;
