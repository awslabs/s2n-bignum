(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The image of the mlkem_native2 functions, for the proofs about the ones   *)
(* that call others (with BL): the code of the objects listed in             *)
(* MLKEM_NATIVE2_IMAGE_OBJ in arm/Makefile, the API for the three parameter  *)
(* sets, the middle layer, and the leaves and Keccak permutations that they  *)
(* call, linked in that order at address 0 by                                *)
(* arm/mlkem_native/asm/mlkem_native2_image.ld and followed by the constants *)
(* block, as one byte list.                                                  *)
(*                                                                           *)
(* The theorems about the image assume that it is loaded at an address pc    *)
(* (a multiple of 4096 when ADRP is used, i.e. for the API functions). A     *)
(* function or label f of the image is then at pc + f, with the names for    *)
(* its address, and for a function f also f_size for its size, taken from    *)
(* the symbol table of the linked file and installed as in common/layout.ml. *)
(* The theorems for the leaves and the Keccak permutations, about their own  *)
(* code, apply to the same code in the image, at pc + f, which               *)
(* ARM_SUBROUTINE_SIM_TAC checks when it uses them.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/layout.ml";;
needs "arm/proofs/utils/mlkem_native_image.ml";;

let mlkem_native2_image_mc = define_from_elf
  "mlkem_native2_image_mc" "arm/mlkem_native/asm/mlkem_native2_image.elf";;

let LENGTH_MLKEM_NATIVE2_IMAGE_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native2_image_mc);;

(* ------------------------------------------------------------------------- *)
(* The symbols of the section .text of an ELF64 file, as (name, value, size) *)
(* for the functions and other symbols with names, excluding the mapping     *)
(* symbols $x and $d of AArch64 and those of the assembler's numeric labels. *)
(* The labels inside the functions have names starting with L, which keeps   *)
(* them local to the object on Mach-O; that prefix is dropped where the name *)
(* without it is not another symbol's.                                       *)
(* ------------------------------------------------------------------------- *)

let load_elf64_text_symbols =
  let u16 bs a = get_int_le bs a 2 and u32 bs a = get_int_le bs a 4
  and u64 bs a = get_int_le bs a 8 in
  fun (filename:string) ->
    let file = load_file filename in
    if not (is_elf file) || get_int_list file 0x4 2 <> [2;1] then
      failwith "load_elf64_text_symbols: not a little-endian ELF64 file" else
    let shoff = u64 file 0x28 and shentsize = u16 file 0x3a
    and shnum = u16 file 0x3c and shstrndx = u16 file 0x3e in
    let header i = shoff + i * shentsize in
    let offset i = u64 file (header i + 0x18)
    and size i = u64 file (header i + 0x20)
    and typ i = u32 file (header i + 0x4)
    and link i = u32 file (header i + 0x28) in
    let name_of i = get_string file (offset shstrndx + u32 file (header i)) in
    let find p = let rec go i = if i >= shnum then failwith
                   "load_elf64_text_symbols: missing section"
                 else if p i then i else go (i + 1) in go 0 in
    let text = find (fun i -> name_of i = ".text")
    and symtab = find (fun i -> typ i = 2) in
    let strtab = link symtab in
    let unlocal n = String.sub n 1 (String.length n - 1) in
    let rec syms k acc =
      if k < 0 then acc else
      let e = offset symtab + 24 * k in
      let name = get_string file (offset strtab + u32 file e)
      and shndx = u16 file (e + 6) in
      let acc' =
        if shndx = text && name <> "" && String.get name 0 <> '$' &&
           not (String.contains name '.')
        then (name,u64 file (e + 8),u64 file (e + 16))::acc
        else acc in
      syms (k - 1) acc' in
    let l = syms (size symtab / 24 - 1) [] in
    let names = map (fun (n,_,_) -> n) l in
    map (fun (n,v,sz as sym) ->
           if String.length n > 1 && String.get n 0 = 'L' &&
              not (mem (unlocal n) names)
           then (unlocal n,v,sz) else sym) l;;

(* ------------------------------------------------------------------------- *)
(* The names of the image: f for the address of each function or label f,    *)
(* f_size for the size of a function, and mlkem_native2_image_size.          *)
(* ------------------------------------------------------------------------- *)

let mlkem_native2_image_symbols =
  load_elf64_text_symbols "arm/mlkem_native/asm/mlkem_native2_image.elf";;

install_layout
 (("mlkem_native2_image_size",
   dest_small_numeral(rhs(concl LENGTH_MLKEM_NATIVE2_IMAGE_MC))) ::
  List.concat
   (map (fun (name,value,size) ->
          if size = 0 then [name,value]
          else [name,value; name ^ "_size",size])
        mlkem_native2_image_symbols));;

(* ------------------------------------------------------------------------- *)
(* The decoding theorems for the simulation of the functions with the given  *)
(* names, for ARM_MK_EXEC_RANGES_RULE, as for an ARM_MK_EXEC_RULE theorem.   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_IMAGE_EXEC names =
  ARM_MK_EXEC_RANGES_RULE mlkem_native2_image_mc (map layout_range names);;
