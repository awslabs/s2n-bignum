(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The image of the x86 mlkem_native2 functions, for the proofs about the    *)
(* ones that call others: the code of the objects listed in                  *)
(* MLKEM_ASM_IMAGE_OBJ in x86/mlkem_native/asm/image.mk, the API for the     *)
(* three parameter sets, the middle layer, and the leaves and Keccak         *)
(* permutations that they call, linked in that order at address 0 by         *)
(* x86/mlkem_native/asm/mlkem_native2_image.ld and followed by their         *)
(* read-only data (the rotation tables of sha3_keccak_f1600_alt2 and the     *)
(* constants block), as one byte list. The objects of this directory are     *)
(* "x86/mlkem_native/asm/mlkem512.o", "x86/mlkem_native/asm/mlkem768.o",     *)
(* "x86/mlkem_native/asm/mlkem1024.o", "x86/mlkem_native/asm/mlkem_gen_matrix.o", *)
(* "x86/mlkem_native/asm/mlkem_getnoise.o", "x86/mlkem_native/asm/mlkem_hash_g.o", *)
(* "x86/mlkem_native/asm/mlkem_hash_h.o" and                                 *)
(* "x86/mlkem_native/asm/mlkem_native2_constants.o".                         *)
(*                                                                           *)
(* The theorems about the image assume that it is loaded at an address pc. A *)
(* function or label f of the image is then at pc + f, with the names for    *)
(* its address, and for a function f also f_size for its size, taken from    *)
(* the symbol table of the linked file and installed as in common/layout.ml. *)
(* The theorems for the leaves and the Keccak permutations, about their own  *)
(* code, apply to the same code in the image, at pc + f, which               *)
(* X86_SUBROUTINE_SIM_TAC checks when it uses them.                          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native2_tools.ml";;

let mlkem_native2_image_mc,LENGTH_MLKEM_NATIVE2_IMAGE_MC =
  x86_image "mlkem_native2_image_mc"
    "x86/mlkem_native/asm/mlkem_native2_image.elf";;

(* ------------------------------------------------------------------------- *)
(* The decoding theorems for the simulation of the functions with the given  *)
(* names, as for an X86_MK_EXEC_RULE theorem.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_IMAGE_EXEC names =
  X86_MK_EXEC_RANGES_RULE mlkem_native2_image_mc (map layout_range names);;
