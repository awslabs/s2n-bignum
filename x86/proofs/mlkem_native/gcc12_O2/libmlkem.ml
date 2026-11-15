(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mlkem-native's libmlkem.so for x86-64      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), as one image,   *)
(* and the versions for it of the rules in utils/mlkem_native_image.ml       *)
(* that transfer the results for the individual functions to the same code   *)
(* in the image. The code refers to other code and data in the image only    *)
(* by displacements from the instruction pointer, so the image works in the  *)
(* same way wherever it is loaded, at an address pc, and a function f in it  *)
(* is then at pc + f, with the names for the addresses and sizes in the      *)
(* binary that are listed in layout.ml. The theorems about the image only    *)
(* assume that pc is a multiple of 16, since the vectors of constants read   *)
(* by SSE instructions must be aligned. (The dynamic loader puts it at a     *)
(* multiple of 4096.)                                                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "x86/proofs/utils/mlkem_native_image.ml";;

let mlkem_native_libmlkem_gcc12_O2_mc = define_from_elf
  "mlkem_native_libmlkem_gcc12_O2_mc"
  "x86/mlkem_native/gcc12_O2/libmlkem.o";;

let LENGTH_MLKEM_NATIVE_LIBMLKEM_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native_libmlkem_gcc12_O2_mc);;

(* The image has the size given in the layout file.                          *)

let () =
  if dest_small_numeral(rhs(concl LENGTH_MLKEM_NATIVE_LIBMLKEM_GCC12_O2_MC)) <>
     layout "libmlkem_size"
  then failwith "The size of the image is not libmlkem_size";;

(* ------------------------------------------------------------------------- *)
(* The rules of utils/mlkem_native_image.ml for this image.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_CODE_RULE =
  MLKEM_NATIVE_IMAGE_CODE_RULE_FOR mlkem_native_libmlkem_gcc12_O2_mc;;

let MLKEM_NATIVE_IMAGE_DATA_RULE =
  MLKEM_NATIVE_IMAGE_DATA_RULE_FOR mlkem_native_libmlkem_gcc12_O2_mc;;

let MLKEM_NATIVE_IMAGE_CONST_RULE =
  MLKEM_NATIVE_IMAGE_CONST_RULE_FOR mlkem_native_libmlkem_gcc12_O2_mc;;

let MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE =
  MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE_FOR mlkem_native_libmlkem_gcc12_O2_mc;;
