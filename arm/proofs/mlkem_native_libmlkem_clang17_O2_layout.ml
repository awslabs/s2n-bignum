(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The layout of mlkem-native's libmlkem.so compiled by clang 17 with -O2    *)
(* (see mlkem_native/README.md), for the functions of it that are            *)
(* transcribed in mlkem_native/*.S. See                                      *)
(* mlkem_native_libmlkem_gcc12_O2_layout.ml for the meaning of the names.    *)
(* This file is maintained by hand for now.                                  *)
(* ========================================================================= *)

needs "common/layout.ml";;

install_layout (layout_objects [
  "mlkem_poly_reduce", 0x7318, 0x050]);;

install_layout (layout_labels [
  "mlkem_poly_reduce",
   ["loop1",0x10; "loop1_test",0x44; "loop1_exit",0x4c; "ret",0x4c]]);;

install_layout (layout_copies [
  "poly_reduce",
   "mlkem_poly_reduce"]);;
