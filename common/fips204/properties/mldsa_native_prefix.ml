(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa{44,65,87}_prepare_domain_separation_prefix  *)
(* (see common/mldsa_native_prefix.ml): the addresses of its two tables from *)
(* the ADRP and ADD instructions, the reading of the tables from the image,  *)
(* the decision of the branches on the arguments, the arithmetic of hashalg  *)
(* (an int, in W5), the pieces of the prefix in memory, and the events       *)
(* template.                                                                 *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/mldsa_native_prefix.ml";;

(* ------------------------------------------------------------------------- *)
(* The address in an image, relative to its start, that an ADRP at a and an  *)
(* ADD (immediate) at b compute, decoded from the instructions in the image  *)
(* image_mc (a theorem image_mc = [bytes]). The functions use it for two     *)
(* tables that have no names in the layout: the table of the jump on         *)
(* hashalg - 1 and the table oid_map of mld_get_hash_oid.                    *)
(* ------------------------------------------------------------------------- *)

let mld_prefix_adrp_add_target image_mc a b =
  let imagel = Array.of_list(dest_list(rhs(concl image_mc))) in
  let byte i = dest_small_numeral(rand(imagel.(i))) in
  let insn i = byte i lor (byte(i + 1) lsl 8) lor
               (byte(i + 2) lsl 16) lor (byte(i + 3) lsl 24) in
  let w = insn a and v = insn b in
  if w land 0x9f000000 <> 0x90000000
  then failwith "mld_prefix_adrp_add_target: not an ADRP" else
  if v land 0xff800000 <> 0x91000000
  then failwith "mld_prefix_adrp_add_target: not an ADD" else
  let imm = (((w lsr 5) land 0x7ffff) lsl 2) lor ((w lsr 29) land 3) in
  let imm = if imm land 0x100000 <> 0 then imm - 0x200000 else imm in
  (a land (lnot 0xfff)) + imm * 4096 +
  (((v lsr 10) land 0xfff) lsl (12 * ((v lsr 22) land 1)));;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_VAL_LEN_TAC b k a l adds val(word l) = l, for the length l of  *)
(* the buffer at a, which does not overlap the k bytes at b.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_VAL_LEN_TAC b k a l =
  SUBGOAL_THEN (subst [l,`l:num`] `val(word l:int64) = l`) ASSUME_TAC THENL
   [SUBGOAL_THEN
     (subst [k,`k:num`; l,`l:num`] `k + l <= 18446744073709551616`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
      MAP_EVERY EXISTS_TAC
       [mk_comb(`val:int64->num`,b); mk_comb(`val:int64->num`,a)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_SELECT_TAC rewrites each condition of a conditional in the     *)
(* goal (such as the cases of the events template) that is an assumption,    *)
(* or whose negation is, to T or F.                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

(* ------------------------------------------------------------------------- *)
(* hashalg - 1, computed in 32 bits (SUB w1, w5, #1) for hashalg != 0, and   *)
(* the condition HI after its comparison with 11, which the code uses to     *)
(* check that 1 <= hashalg <= 12 before the jump.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_WORD_SUB1 = prove
 (`!x:int32.
        ~(val x = 0)
        ==> word_zx (word_zx (word_sub x (word 1)):int64):int32 =
            word(val x - 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64; VAL_WORD_1] THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= val(x:int32) /\ val x - 1 < 4294967296 /\
                val x - 1 < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(x:int32) < 4294967296`; `~(val(x:int32) = 0)`] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let MLD_PREFIX_RANGE = prove
 (`!x:int32.
        ~(val x = 0)
        ==> ((&(val (word_zx (word_zx (word_sub x (word 1)):int64)
                       :int32)):int) - &11 =
             &(val (word_sub (word_zx (word_zx (word_sub x (word 1)):int64)
                               :int32) (word 11))) /\
             ~(val (word_sub (word_zx (word_zx (word_sub x (word 1)):int64)
                               :int32) (word 11)) = 0) <=>
             12 < val x)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[MLD_PREFIX_WORD_SUB1] THEN
  REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_SUB_EQ_0; VAL_WORD;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `(val(x:int32) - 1) MOD 4294967296 = val x - 1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `val(x:int32) < 4294967296` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[INT_ARITH `a - b:int = a + c - b <=> c = &0`] THEN
  CONV_TAC INT_REDUCE_CONV THEN RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN
  MAP_EVERY UNDISCH_TAC
   [`val(x:int32) < 4294967296`; `~(val(x:int32) = 0)`] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A 32-bit value zero-extended to 64 bits and truncated back (the loop      *)
(* compares hashalg in W5 with the 32-bit entries of oid_map).               *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_ZX_ZX = prove
 (`!y:int32. word_zx(word_zx y:int64):int32 = y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN] THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `y:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(y:int32) < 18446744073709551616` ASSUME_TAC THENL
   [UNDISCH_TAC `val(y:int32) < 4294967296` THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let MLD_PREFIX_ZX_WORD = prove
 (`(!n. word_zx(word n:int64):int32 = word n) /\
   (!n. word_zx(word n:int32):byte = word n) /\
   (!n. word_zx(word n:int64):byte = word n)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX_ZX_ADD1 = prove
 (`!i. i + 1 < 2 EXP 32
       ==> word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
           word(i + 1)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_PREFIX_ZX_WORD] THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `(i + 1) MOD 2 EXP 32 = i + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; REFL_TAC]);;

(*** A valid pre-hash has at most 64 bytes ***)

let MLD_PREFIX_PHLEN_LE = prove
 (`!h phlen. mld_prehash_valid h phlen ==> phlen <= 64`,
  REWRITE_TAC[mld_prehash_valid; mld_prehash_length] THEN
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ARITH_TAC);;

let MLD_PREFIX_NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let LENGTH_MLD_PREHASH_OID = prove
 (`!h. LENGTH(mld_prehash_oid h) = 11`,
  REWRITE_TAC[mld_prehash_oid; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX_OIDN = prove
 (`!h. num_of_bytelist(mld_prehash_oid h) =
       28430383651490054 +
       2 EXP 56 * (132099 + 16777216 * val(EL 10 (mld_prehash_oid h)))`,
  GEN_TAC THEN REWRITE_TAC[mld_prehash_oid] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_of_bytelist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> is_comb t && rator t = `val:byte->num` &&
                                is_cond(rand(rand t))) w in
    ABBREV_TAC(mk_eq(`x:num`,t))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The events template of the FULL proofs, by the cases of the code: the     *)
(* context too long, pure ML-DSA with an empty context or not, hashalg out   *)
(* of range, and for 1 <= hashalg <= 12 the part before the jump, then the   *)
(* jump and the check of the length of the pre-hash, one function for each   *)
(* hashalg (valid or not), and for a valid length the part to the loop over  *)
(* oid_map, its hashalg iterations, the last of them finding hashalg, and    *)
(* the rest, for an empty context or not. The functions for an empty context *)
(* do not have ctxlen as an argument.                                        *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_TEMPLATE =
  let a = "prefix ph phlen ctx ctxlen hashalg mc pc stackpointer returnaddress"
  and a0 = "prefix ph phlen ctx hashalg mc pc stackpointer returnaddress"
  and h = "val(word_zx hashalg:int32)" in
  let sel f =
    "(" ^ itlist (fun k s -> "if " ^ h ^ " = " ^ string_of_int k ^ " then " ^
                             f ^ string_of_int k ^ " " ^ a ^ " else " ^ s)
                 (1--11) (f ^ "12 " ^ a) ^ ")" in
  let tail c ar =
    "APPEND (f_ev_e" ^ c ^ " " ^ ar ^ ") " ^
    "(APPEND (ENUMERATEL (" ^ h ^ ") (\\i. if i + 1 < " ^ h ^
    " then f_ev_n" ^ c ^ " " ^ ar ^ " i else f_ev_f" ^ c ^ " " ^ ar ^
    " i)) (f_ev_c" ^ c ^ " " ^ ar ^ "))" in
  parse_term
   ("\\(prefix:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) " ^
    "(hashalg:int64) (mc:int64) (pc:num) (stackpointer:int64) " ^
    "(returnaddress:int64). " ^
    "if 255 < ctxlen then f_ev_big " ^ a ^
    " else if " ^ h ^ " = 0 then (if ctxlen = 0 then f_ev_p0 " ^ a0 ^
    " else f_ev_p1 " ^ a ^ ")" ^
    " else if 12 < " ^ h ^ " then f_ev_bad " ^ a ^
    " else APPEND (if mld_prehash_valid (" ^ h ^ ") phlen then " ^
    "APPEND (if ctxlen = 0 then " ^ tail "0" a0 ^ " else " ^ tail "1" a ^
    ") " ^ sel "f_ev_v" ^ " else " ^ sel "f_ev_b" ^ ") " ^
    "(f_ev_pre " ^ a ^ ") :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_RANGE_TAC rewrites the condition of the check 1 <= hashalg <=  *)
(* 12 to ~(12 < val(word_zx hashalg)), for hashalg != 0;                     *)
(* MLD_PREFIX_HCASES_TAC splits into the cases val(word_zx hashalg) = 1,     *)
(* ..., 12; MLD_PREFIX_HWORD_TAC k rewrites word_zx hashalg to word k in the *)
(* assumptions in case k; MLD_PREFIX_ADDR_NORM_RULE normalizes the addresses *)
(* in a theorem as the simulation does (NORMALIZE_RELATIVE_ADDRESS_CONV,     *)
(* twice).                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_RANGE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `word_zx (hashalg:int64):int32` MLD_PREFIX_RANGE)
       (ASSUME `~(val(word_zx (hashalg:int64):int32) = 0)`)]);;

let MLD_PREFIX_HCASES_TAC =
  SUBGOAL_THEN
   (list_mk_disj(map (fun k -> mk_eq(`val(word_zx (hashalg:int64):int32)`,
                                     mk_small_numeral k)) (1--12)))
   MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(val(word_zx (hashalg:int64):int32) = 0)`;
      `~(12 < val(word_zx (hashalg:int64):int32))`] THEN ARITH_TAC;
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)];;

let MLD_PREFIX_ADDR_NORM_RULE =
  CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
            ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV);;
