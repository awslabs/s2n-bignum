(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*        Common memory-component inspection and MAYCHANGE coalescing.       *)
(* ========================================================================= *)

needs "common/relational.ml";;

(* Given `memory :> bytes (..)` or `memory :> bytesXX (..)`, return the
   address, byte size, and accessor name. The address type is determined by
   the backend's `memory` component. *)
let get_memory_read_info =
  let szs = [
    "bytes8",`1`;
    "bytes16",`2`;
    "bytes32",`4`;
    "bytes64",`8`;
    "bytes128",`16`;
    "bytes256",`32`
  ] in
  fun (t:term): (term * term * string) option ->
    if not (is_binary ":>" t) then None else
    let l,r = dest_binary ":>" t in
    let is_byte_memory_component =
      try
        let _,args = dest_type (type_of l) in
        let addr_ty,byte_ty = dest_fun_ty (last args) in
        can dest_word_ty addr_ty && byte_ty = `:byte`
      with Failure _ -> false in
    if not is_byte_memory_component then None else
    let c,args = strip_comb r in
    try
      let accessor:string = fst (dest_const c) in
      let bytewidth:term = assoc accessor szs in
      if List.length args <> 1 then failwith "get_memory_read_info" else
      Some (List.hd args, bytewidth, accessor)
    with Failure _ ->
      try
        let accessor:string = fst (dest_const c) in
        if accessor <> "bytes" || List.length args <> 1 then None else
        let a,sz = dest_pair (List.hd args) in
        Some (a,sz,"bytes")
      with Failure _ -> None;;

let get_base_ptr_and_ofs (t:term): term * term =
  try
    let baseptr,y = dest_binary "word_add" t in
    let wordc,ofs = dest_comb y in
    if name_of wordc <> "word" then failwith "not word" else
    baseptr,ofs
  with Failure _ -> t,mk_small_numeral 0;;

assert (get_base_ptr_and_ofs `x:int64` = (`x:int64`,`0`));;
assert (get_base_ptr_and_ofs `word_add x (word 32):int64` =
        (`x:int64`,`32`));;
assert (get_base_ptr_and_ofs `word_add x (word (8*4)):int64` =
        (`x:int64`,`8*4`));;
assert
 (get_base_ptr_and_ofs
    `word_add (word_add x (word 16)) (word 32):int64` =
  (`word_add x (word 16):int64`,`32`));;
assert (get_base_ptr_and_ofs `word_add x (word k):int64` =
        (`x:int64`,`k:num`));;
assert (get_base_ptr_and_ofs `word_add x (word k):int32` =
        (`x:int32`,`k:num`));;

(* Accept only a numerically reducible constant offset. If an address is not
   of the form `base + word constant`, return the complete address as its own
   base with offset zero, so it cannot be merged with another expression. *)
let get_base_ptr_and_constofs (t:term): term * int =
  let base,ofs = get_base_ptr_and_ofs t in
  if is_numeral ofs then base,dest_small_numeral ofs
  else
    try
      let ofs = rhs (concl (NUM_RED_CONV ofs)) in
      base,dest_small_numeral ofs
    with Failure _ -> t,0;;

assert
 (get_base_ptr_and_constofs `word_add x (word (8*4)):int64` =
  (`x:int64`,32));;

(* Flatten a sequence of MAYCHANGE lists, remove duplicate components, and
   merge overlapping or adjacent constant-size memory ranges that use the
   same memory component and syntactic base address. Symbolic-size ranges and
   addresses without a reducible constant offset are retained unchanged.

   For example, adjacent entries
     `memory :> bytes (a,4)`
     `memory :> bytes (word_add a (word 4),4)`
   are replaced by one `memory :> bytes64 a` entry.

   The collection, deduplication, sorting, and interval-merging algorithm is
   unchanged from the fixed-int64 implementation. The generic version carries
   the memory component as part of the merge key, reconstructs merged ranges
   at the pointer's word type, and recognizes bytes8 alongside the other named
   byte views.

   The 64- and 128-bit buckets preserve the grouping used for general-purpose
   and vector registers. Other component value types are grouped by type.
   Memory ranges retain the backend native address type; an eight-byte result
   is printed as `bytes64`, and other merged sizes use `bytes`. *)
let simplify_maychanges: term -> term =
  let maychange_const = `MAYCHANGE` and seq_const = `,,` in
  let word64ty = `:(64)word` and word128ty = `:(128)word` in
  let zero = `0` in

  fun (maychanges:term) ->
    let maychange_regs64 = ref [] and
        maychange_regs128 = ref [] and
        maychange_mems = ref [] and
        maychange_others = ref [] in
    let add_maychange (t:term): unit =
      match get_memory_read_info t with
      | Some (ptr,len,_) ->
          let memory_component = fst(dest_binary ":>" t) in
          maychange_mems :=
            !maychange_mems @ [(t,(memory_component,ptr,len))]
      | None ->
        let _,args = dest_type (type_of t) in
        let destty = last args in
        if destty = word64ty then begin
          if not (mem t !maychange_regs64) then
            maychange_regs64 := !maychange_regs64 @ [t]
        end else if destty = word128ty then begin
          if not (mem t !maychange_regs128) then
            maychange_regs128 := !maychange_regs128 @ [t]
        end else begin
          if not (mem t !maychange_others) then
            maychange_others := !maychange_others @ [t]
        end in

    let rec collect (t:term): unit =
      if is_binary ",," t then
        let lhs,rhs = dest_binary ",," t in
        let _,args = dest_comb lhs in
        List.iter add_maychange (dest_list args);
        collect rhs
      else
        let _,args = dest_comb t in
        List.iter add_maychange (dest_list args) in

    collect maychanges;

    let maychange_mems_merged = ref [] in
    let add_maychange_mem (memory_component,base_ptr,ofs,len): unit =
      let base_ptr =
        if ofs = 0 then base_ptr
        else
          let aty = dest_word_ty(type_of base_ptr) in
          let word_tm = inst [aty,`:A`] `word:num->A word`
          and word_add_tm =
            inst [aty,`:A`] `word_add:A word->A word->A word` in
          mk_comb(mk_comb(word_add_tm,base_ptr),
                  mk_comb(word_tm,mk_small_numeral ofs)) in
      let accessor =
        if len = 8 then
          mk_icomb
            (`bytes64:A word->((A word->byte),int64)component`,base_ptr)
        else mk_icomb(`bytes`,mk_pair(base_ptr,mk_small_numeral len)) in
      let final_term =
        list_mk_icomb ":>" [memory_component;accessor] in
      maychange_mems_merged := !maychange_mems_merged @ [final_term] in

    while length !maychange_mems <> 0 do
      let next_term,(memory_component,ptr,len) =
        List.hd !maychange_mems in
      if not (is_numeral len) then begin
        if not (mem next_term !maychange_mems_merged) then
          maychange_mems_merged := next_term::!maychange_mems_merged;
        maychange_mems := List.tl !maychange_mems
      end else
        let baseptr,_ = get_base_ptr_and_constofs ptr in
        let mems_of_interest,remaining = List.partition
          (fun _,(memory_component',ptr,len) ->
            memory_component = memory_component' &&
            baseptr = fst (get_base_ptr_and_constofs ptr) &&
            is_numeral len)
          !maychange_mems in
        maychange_mems := remaining;

        if List.length mems_of_interest = 1 then
          maychange_mems_merged :=
            fst (List.hd mems_of_interest)::!maychange_mems_merged
        else
          let ranges = map
            (fun (_,(_,t,len)) ->
              snd (get_base_ptr_and_constofs t),dest_small_numeral len)
            mems_of_interest in
          let ranges = mergesort (<) ranges in
          let rec merge_and_update ranges =
            match ranges with
            | [(ofs,len)] ->
                add_maychange_mem
                  (memory_component,baseptr,ofs,len)
            | (ofs1,len1)::(ofs2,len2)::t ->
              if ofs2 <= ofs1 + len1 then
                let len = max len1 (ofs2 + len2 - ofs1) in
                merge_and_update ((ofs1,len)::t)
              else begin
                add_maychange_mem
                  (memory_component,baseptr,ofs1,len1);
                merge_and_update ((ofs2,len2)::t)
              end
            | [] -> failwith "simplify_maychanges" in
          merge_and_update ranges
    done;

    let result = ref zero in
    let rec join_result (comps:term list): unit =
      match comps with
      | [] -> ()
      | first_comp::comps ->
        let fcty = type_of first_comp in
        let comps0,comps1 =
          List.partition (fun c -> type_of c = fcty) comps in
        let mterm =
          mk_icomb (maychange_const,mk_flist (first_comp::comps0)) in
        if !result = zero then result := mterm
        else result := mk_icomb(mk_icomb (seq_const,mterm),!result);
        join_result comps1 in
    join_result !maychange_regs64;
    join_result !maychange_regs128;
    join_result !maychange_others;
    List.iter (fun t -> join_result [t]) !maychange_mems_merged;
    !result;;

(* Simplify every MAYCHANGE relation in the assumptions. If coalescing changes
   a relation, prove the replacement from the original with
   MONOTONE_MAYCHANGE_TAC, assume it, and remove the original assumption.

   This is normally called automatically: ARM's EQUIV_STEP_TAC invokes it every
   50 lockstep instructions, and GEN_PROVE_SAFETY_SPEC_TAC invokes it after
   each 50-step chunk. prove_equiv_seq_composition uses the underlying term
   function directly. Proof authors may also call the tactic after many
   symbolic steps have fragmented a memory frame. The x86 equivalence driver
   does not currently invoke it automatically. *)
let SIMPLIFY_MAYCHANGES_TAC =
  W(fun (asl,w) ->
    let mcs = filter_map
      (fun (_,asm) ->
        if maychange_term (concl asm) then Some asm else None) asl in
    MAP_EVERY (fun asm ->
      let x,st2 = dest_comb (concl asm) in
      let mainterm,st1 = dest_comb x in
      let newterm = simplify_maychanges mainterm in
      let _ =
        Printf.printf
          "SIMPLIFY_MAYCHANGES_TAC: Simplifying `%s` to `%s`\n"
          (string_of_term (concl asm)) (string_of_term newterm) in
      if mainterm = newterm then ALL_TAC
      else
        (SUBGOAL_THEN (list_mk_comb (newterm,[st1;st2])) ASSUME_TAC THENL
         [POP_ASSUM_LIST (K ALL_TAC) THEN
          ASSUME_TAC asm THEN
          MONOTONE_MAYCHANGE_TAC;
          ALL_TAC] THEN
         UNDISCH_THEN (concl asm) (K ALL_TAC)))
      mcs);;
