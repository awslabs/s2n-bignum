(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of snappy's libsnappy.so compiled by gcc 12   *)
(* with -O2 (see arm/snappy/README.md), as one image, from address 0 to the  *)
(* end of .rodata, and the rules of utils/loaded_image.ml for it. All the    *)
(* theorems about the image assume that it is loaded at an address pc that  *)
(* is a multiple of 4096, as the dynamic loader does, and that it does not   *)
(* wrap around the end of the address space, i.e.                            *)
(* pc + libsnappy_size <= 2 EXP 64. A function f in it is then at pc + f,    *)
(* with the names for the addresses and sizes in the binary that are listed  *)
(* in layout.ml. The relocated slots of the writable segment, at the same    *)
(* base pc, are snappy_libsnappy_gcc12_O2_relocated pc imp (relocs.ml).      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/snappy/gcc12_O2/layout.ml";;
needs "arm/proofs/snappy/gcc12_O2/relocs.ml";;
needs "arm/proofs/utils/loaded_image.ml";;

let snappy_libsnappy_gcc12_O2_mc = define_from_elf
  "snappy_libsnappy_gcc12_O2_mc"
  "arm/snappy/gcc12_O2/libsnappy.o";;

let LENGTH_SNAPPY_LIBSNAPPY_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` snappy_libsnappy_gcc12_O2_mc);;

(* The image has the size given in the layout file.                          *)

let () =
  if dest_small_numeral(rhs(concl LENGTH_SNAPPY_LIBSNAPPY_GCC12_O2_MC)) <>
     layout "libsnappy_size"
  then failwith "The size of the image is not libsnappy_size";;

(* ------------------------------------------------------------------------- *)
(* The rules of utils/loaded_image.ml for this image.                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_IMAGE_CONST_RULE =
  IMAGE_CONST_RULE_FOR snappy_libsnappy_gcc12_O2_mc;;
