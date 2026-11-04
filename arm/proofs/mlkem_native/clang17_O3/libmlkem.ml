(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mlkem-native's libmlkem.so compiled by     *)
(* clang 17 with -O3 (see mlkem_native/README.md), as one image, and the     *)
(* versions for it of the rules in utils/mlkem_native_image.ml that transfer *)
(* the results for the individual functions to the same code in the image.   *)
(* All the theorems about the image assume that it is loaded at an address   *)
(* pc that is a multiple of 4096, as the dynamic loader does, and that it    *)
(* does not wrap around the end of the address space, i.e.                   *)
(* pc + libmlkem_size <= 2 EXP 64. A function f in it is then at pc + f,     *)
(* with the names for the addresses and sizes in the binary that are listed  *)
(* in layout.ml.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/layout.ml";;
needs "arm/proofs/utils/mlkem_native_image.ml";;

let mlkem_native_libmlkem_clang17_O3_mc = define_from_elf
  "mlkem_native_libmlkem_clang17_O3_mc"
  "arm/mlkem_native/clang17_O3/libmlkem.o";;

let LENGTH_MLKEM_NATIVE_LIBMLKEM_CLANG17_O3_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native_libmlkem_clang17_O3_mc);;

(* The image has the size given in the layout file.                          *)

let () =
  if dest_small_numeral
       (rhs(concl LENGTH_MLKEM_NATIVE_LIBMLKEM_CLANG17_O3_MC)) <>
     layout "libmlkem_size"
  then failwith "The size of the image is not libmlkem_size";;

(* ------------------------------------------------------------------------- *)
(* The rules of utils/mlkem_native_image.ml for this image.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_CODE_RULE =
  MLKEM_NATIVE_IMAGE_CODE_RULE_FOR mlkem_native_libmlkem_clang17_O3_mc;;

let MLKEM_NATIVE_IMAGE_DATA_RULE =
  MLKEM_NATIVE_IMAGE_DATA_RULE_FOR mlkem_native_libmlkem_clang17_O3_mc;;

let MLKEM_NATIVE_IMAGE_CONST_RULE =
  MLKEM_NATIVE_IMAGE_CONST_RULE_FOR mlkem_native_libmlkem_clang17_O3_mc;;
