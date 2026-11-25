(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The table kLengthMinusOffset of snappy.cc in the gcc12_O2 image (rodata   *)
(* at pc + 0x7e00, 256 entries of 16 bits): the entry of a tag byte c is     *)
(* LengthMinusOffset(c), snappy_lmo c, the length of the tag (the low byte)  *)
(* minus the bits 8..10 of its offset (as a multiple of 256), or 255 for the *)
(* tags that the fast path does not take.                                    *)
(*                                                                           *)
(* SNAPPY_LMO_TABLE, the entries read from the image, takes about 40 s: it   *)
(* is stated here (assuming_proofs, common/relative.ml) and proved in the    *)
(* job length_minus_offset_lemmas_proof.ml, not while the link loads this    *)
(* file before its jobs. SNAPPY_LMO_TABLE_ZX is the same with the index as   *)
(* the code computes it, from the byte zero-extended to 64 bits. The proofs  *)
(* of DecompressBranchless<char*>, DecompressBranchless<size_t>,             *)
(* DecompressAllTags<SnappyDecompressionValidator> and                       *)
(* DecompressAllTags<SnappyArrayWriter> use these two.                       *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;

let snappy_lmo = new_definition
 `snappy_lmo (c:byte) : int =
    if val c MOD 4 = 3 then &255
    else if val c MOD 4 = 2 then &(val c DIV 4 + 1)
    else if val c MOD 4 = 1
    then &((val c DIV 4) MOD 8 + 4) - &256 * &((val c DIV 4) DIV 8)
    else if val c DIV 4 < 60 then &(val c DIV 4 + 1) - &256
    else &255`;;

let SNAPPY_READ_BYTES16_OF_BYTES64 = prove
 (`!(m:(S,N word->byte)component) a i s.
        i < 4
        ==> read (m :> bytes16 (word_add a (word (2 * i)))) s =
            word_subword (read (m :> bytes64 a) s) (16 * i,16)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes16; bytes64; READ_COMPONENT_COMPOSE; asword; through;
              read] THEN
  REWRITE_TAC[word_subword] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; REWRITE_RULE[ARITH_RULE `8 * 8 = 64`]
                    (ISPECL [`a:N word`; `8`] READ_BYTES_BOUND)] THEN
  REWRITE_TAC[ARITH_RULE `16 * i = 8 * (2 * i)`; READ_BYTES_DIV;
              ARITH_RULE `2 EXP 16 = 2 EXP (8 * 2)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 4 ==> MIN (8 - 2 * i) 2 = 2`]);;

(* The entry of the tag byte v, from the 64-bit constant of the image that   *)
(* contains it.                                                              *)

let snappy_lmo_entry v =
  let d0 = 32256 + 8 * (v / 4) and i = v mod 4 in
  let th64 = SNAPPY_IMAGE_CONST_RULE d0 64 in
  let n64 = dest_numeral(rand(rhs(rand(snd(strip_forall(concl th64)))))) in
  let n = Num.int_of_num(Num.mod_num
            (Num.quo_num n64 (Num.power_num (Num.num_of_int 2)
                                            (Num.num_of_int (16 * i))))
            (Num.num_of_int 65536)) in
  let tm = subst [mk_small_numeral (32256 + 2 * v),`d:num`;
                  mk_small_numeral n,`n:num`]
    `!s pc. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc
       ==> read (memory :> bytes16 (word_add (word pc) (word d))) s:int16 =
           word n` in
  prove(tm,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`;
       mk_comb(`word_add (word pc:int64)`,
               mk_comb(`word:num->int64`,mk_small_numeral d0));
       mk_small_numeral i; `s:armstate`] SNAPPY_READ_BYTES16_OF_BYTES64) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[th64; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_LMO_TABLE_STMT =
 `!s pc c.
     aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc
     ==> read (memory :> bytes16
                (word_add (word pc) (word (32256 + 2 * val(c:byte))))) s =
         iword(snappy_lmo c)`;;

let SNAPPY_LMO_TABLE_TAC : tactic = fun g ->
  let ths = map snappy_lmo_entry (0--255) in
  (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snappy_lmo] THEN
   MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
   CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(c:byte)`,`v:num`) THEN
   CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_SIMP_TAC ths THEN
   CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN CONV_TAC WORD_REDUCE_CONV) g;;

let SNAPPY_LMO_TABLE = assuming_proofs (fun () ->
  prove(SNAPPY_LMO_TABLE_STMT, SNAPPY_LMO_TABLE_TAC));;

let SNAPPY_LMO_TABLE_ZX = prove
 (`!s pc c.
     aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc
     ==> read (memory :> bytes16 (word_add (word pc)
               (word (32256 + 2 * val(word_zx (c:byte):int64))))) s =
         iword(snappy_lmo c)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `val(word_zx (c:byte):int64) = val c` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN
    ARITH_TAC;
    MATCH_ACCEPT_TAC SNAPPY_LMO_TABLE]);;
