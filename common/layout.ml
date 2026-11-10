(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Symbolic names for the addresses and sizes in a binary image.             *)
(*                                                                           *)
(* Proofs about the code of a whole binary (e.g. the mlkem-native image in   *)
(* arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml) refer to many addresses:    *)
(* the entry points of functions, points inside them where loops start or    *)
(* end, entries of the global offset table, constant tables and the size of  *)
(* the image. Rather than writing these as numerals in every proof, they     *)
(* are collected in a layout file for the binary, which installs them as     *)
(* names here, and the proofs use the names.                                 *)
(*                                                                           *)
(* A name can be used in two ways:                                           *)
(*                                                                           *)
(*  - In a HOL term, where it is replaced by its value as a numeral when the *)
(*    term is parsed, e.g. `read PC s = word(pc + mlkem768_dec)` is the same *)
(*    term as `read PC s = word(pc + 0x5c10)` if mlkem768_dec is 0x5c10. So  *)
(*    the names change nothing in the theorems, only in the proof scripts.   *)
(*                                                                           *)
(*  - In OCaml, as layout "mlkem768_dec", or layout_range "mlkem768_dec" for *)
(*    the pair of the address and the address after the end, using the size *)
(*    given by the name with "_size" appended.                               *)
(*                                                                           *)
(* HOL Light parses a quotation that is just one identifier as a variable,   *)
(* without trying any other parser, so a name on its own in a quotation      *)
(* needs a type, as in SPECL [`pc:num`; `got_memset:num`] WORD_ADD.          *)
(*                                                                           *)
(* Since the names are replaced wherever they occur as identifiers in terms  *)
(* parsed after they are installed, they cannot also be used as variables    *)
(* or constants. install_layout checks that none of them is the name of an   *)
(* existing constant, and new_definition of a constant with such a name      *)
(* fails, since its left-hand side would be a numeral.                       *)
(* ========================================================================= *)

let layout_table = (Hashtbl.create 1024 : (string,int) Hashtbl.t);;

let layout name =
  try Hashtbl.find layout_table name
  with Not_found -> failwith ("layout: unknown name " ^ name);;

let layout_range name = layout name,layout name + layout(name ^ "_size");;

let install_layout =
  let installed = ref false in
  let parser toks =
    match toks with
      Ident s :: rest when Hashtbl.mem layout_table s ->
        Varp(string_of_int(Hashtbl.find layout_table s),dpty),rest
    | _ -> raise Noparse in
  fun (bindings:(string*int)list) ->
    List.iter (fun (name,value) ->
        if can get_const_type name then
          failwith ("install_layout: " ^ name ^ " is a constant") else
        try let value' = Hashtbl.find layout_table name in
            if value' <> value then
              failwith ("install_layout: two values for " ^ name)
        with Not_found -> Hashtbl.add layout_table name value)
      bindings;
    if not !installed then
     (install_parser ("layout",parser); installed := true);;

(* ------------------------------------------------------------------------- *)
(* The bindings for the parts of a layout file, which list:                  *)
(*                                                                           *)
(*  - functions, as (name, address, size): names "f" and "f_size";           *)
(*                                                                           *)
(*  - data, as (name, address, size), likewise;                              *)
(*                                                                           *)
(*  - labels, as (function, [label, offset; ...]) with the offsets from the  *)
(*    start of the function: names "f_label" for the address in the image;   *)
(*                                                                           *)
(*  - separately transcribed copies of functions, as (copy, function), whose *)
(*    code starts at its own pc: names "copy_size" and "copy_label" for the  *)
(*    size and the offsets of the labels from the start of the function.     *)
(* ------------------------------------------------------------------------- *)

let layout_objects l =
  List.concat (map (fun (name,addr,size) -> [name,addr; name ^ "_size",size]) l);;

let layout_labels =
  let offsets = Hashtbl.create 128 in
  let labels l =
    List.concat (map (fun (f,ls) ->
        let a = layout f in
        Hashtbl.replace offsets f ls;
        map (fun (label,ofs) -> f ^ "_" ^ label,a + ofs) ls) l)
  and copies l =
    List.concat (map (fun (copy,f) ->
        (copy ^ "_size",layout(f ^ "_size")) ::
        map (fun (label,ofs) -> copy ^ "_" ^ label,ofs)
            (try Hashtbl.find offsets f with Not_found -> [])) l) in
  labels,copies;;

let layout_copies = snd layout_labels;;
let layout_labels = fst layout_labels;;
