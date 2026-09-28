(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generic fetch support for four-byte, little-endian instruction words.     *)
(*                                                                           *)
(* This file is loaded after a backend defines aligned code loading and its  *)
(* instruction decoder.                                                      *)
(* ========================================================================= *)

(* Fetch four little-endian bytes at the backend native-width address and
   pass the resulting int32 to the backend decoder. This fixes the instruction
   width and byte order, but not the address width or instruction semantics. *)
let decode32 = new_definition
 `decode32 decoder s pc inst <=>
  ?i:int32.
    aligned_bytes_loaded s pc (bytelist_of_num 4 (val i)) /\
    decoder i = SOME inst`;;

(* Connect list-oriented object-code traversal to `decode32`: consume one
   int32 from the front of an aligned byte list, decode it, and preserve
   aligned loading for the remainder at the native-width address `pc + 4`. *)
let DECODE32_CONS = prove
 (`!decoder s pc l i inst l'.
      aligned_bytes_loaded s (word pc) l ==>
      read_int32 l = SOME (i,l') ==>
      decoder i = SOME inst ==>
      decode32 decoder s (word pc) inst /\
      aligned_bytes_loaded s (word (pc + 4)) l'`,
  REWRITE_TAC[read_int32; read_word_eq_some;
              aligned_bytes_loaded_word] THEN
  REPLICATE_TAC 10 STRIP_TAC THEN
  POP_ASSUM_LIST(fun [h1;h2;h3;h4;h5;h6] ->
    let t1,t2 = CONJ_PAIR
      (REWRITE_RULE[GSYM WORD_ADD; h3; bytes_loaded_append; h4] h5) in
    let th1 = MATCH_MP DIVIDES_ADD
      (CONJ h6 (SPEC `4` DIVIDES_REFL)) in
    REWRITE_TAC[th1; h6; t2; h1; decode32;
                aligned_bytes_loaded_word] THEN
    EXISTS_TAC `i:int32` THEN
    REWRITE_TAC[h1; h2; VAL_WORD; DIMINDEX_32;
                ARITH_RULE `2 EXP 32 = 256 EXP 4`;
                BYTELIST_OF_NUM_MOD; SYM h3;
                BYTELIST_OF_NUM_OF_BYTELIST; t1]));;

let decode32_unique = prove
 (`!decoder s pc x y.
      decode32 decoder s pc x ==>
      decode32 decoder s pc y ==>
      x = y`,
  REWRITE_TAC[decode32] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST(fun [d2;l2; d1;l1] ->
    let t = REWRITE_RULE[LENGTH_BYTELIST_OF_NUM]
      (MATCH_MP (MATCH_MP aligned_bytes_loaded_unique l1) l2) in
    let t2 = REWRITE_RULE[NUM_OF_BYTELIST_OF_NUM; GSYM CONG;
      ARITH_RULE `256 EXP 4 = 2 EXP 32`; SYM DIMINDEX_32;
      GSYM WORD_EQ; WORD_VAL] (AP_TERM `num_of_bytelist` t) in
    ACCEPT_TAC(REWRITE_RULE[REWRITE_RULE[t2] d1; OPTION_INJ] d2)));;

let dest_cons4 =
  let assert_byte n = function
  | Comb(Const("word",_),a) -> dest_numeral a = num n
  | _ -> false in
  fun n t -> match t with
  | Comb(Comb(Const("CONS",_),a1),Comb(Comb(Const("CONS",_),a2),
      Comb(Comb(Const("CONS",_),a3),Comb(Comb(Const("CONS",_),a4),tm))))
      when 0 <= n && n <= 0xffffffff &&
           assert_byte (n land 0xff) a1 &&
           assert_byte ((n lsr 8) land 0xff) a2 &&
           assert_byte ((n lsr 16) land 0xff) a3 &&
           assert_byte ((n lsr 24) land 0xff) a4 ->
        tm
  | _ ->
      failwith ("dest_cons4: 4-byte instruction " ^ string_of_int n ^
                " does not match " ^ string_of_term t);;

let assert_word_list tm ls =
  if type_of tm = `:byte list` then
    let rec go = function
    | [],Const("NIL",_) -> ()
    | n::ns,tm -> go (ns,dest_cons4 n tm)
    | _ -> failwith "assert_word_list" in
    go (ls,tm)
  else
    failwith "assert_word_list";
  tm;;
