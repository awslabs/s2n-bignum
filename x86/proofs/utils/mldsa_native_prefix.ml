(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa{44,65,87}_prepare_domain_separation_prefix  *)
(* (see common/mldsa_native_prefix.ml) for x86-64, as for AArch64 (see       *)
(* arm/proofs/utils/mldsa_native_prefix.ml, whose tools these are, for the   *)
(* x86 model): the RIP-relative addresses of the two tables that the         *)
(* function reads, the reading of the tables from the image, the target of   *)
(* the jump through the table, the decision of the branches on the           *)
(* arguments, the arithmetic of hashalg (an int, in R9D), the pieces of the  *)
(* prefix in memory, and the events template.                                *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_prefix.ml";;

(* ------------------------------------------------------------------------- *)
(* Bytes in memory as the concatenation of two parts.                        *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_BYTES_COMBINE = prove
 (`!a m n (s:x86state).
        read (memory :> bytes(a,m + n)) s =
        read (memory :> bytes(a,m)) s +
        2 EXP (8 * m) * read (memory :> bytes(word_add a (word m),n)) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

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
(* goal (such as the cases of the events template) that is an assumption, or *)
(* whose negation is, to T or F.                                             *)
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
(* The carry flag of a comparison with a constant n, CMP x, n, as the        *)
(* simulation gives it.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_SUB_FLAG = prove
 (`!(x:N word) n.
        n < 2 EXP dimindex(:N)
        ==> (&(val x) - &n:int = &(val(word_sub x (word n))) <=> n <= val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
  REWRITE_TAC[INT_ARITH `a - b:int = a + c - b <=> c = &0`] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_BRANCH_TAC decides the condition c of the RIP after a          *)
(* conditional jump, read RIP s = if c then a else b, from the assumptions   *)
(* (with mld_prehash_valid expanded, only for this): the comparisons as      *)
(* equations or inequalities of numbers (VAL_WORD_SUB_EQ_0 for the zero      *)
(* flag, MLD_PREFIX_SUB_FLAG for the carry flag of a 32-bit comparison, and  *)
(* the values of the words), then arithmetic (MEMSAFE_ARITH_TAC, which keeps *)
(* the assumptions about values of words), and rewrites the assumptions (the *)
(* RIP and the events) with it; it does nothing if the simulation has        *)
(* already decided the jump.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_DECIDE_TAC =
  RULE_ASSUM_TAC
   (REWRITE_RULE[mld_prehash_valid; mld_prehash_length; ARITH]) THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SIMP_TAC[MLD_PREFIX_SUB_FLAG; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MEMSAFE_ARITH_TAC;;

let MLD_PREFIX_BRANCH_TAC =
  let is_rip_cond th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),r)
        -> is_cond r
    | _ -> false in
  W(fun (asl,w) ->
    if not(exists (fun (_,th) -> is_rip_cond th) asl) then ALL_TAC else
    FIRST_X_ASSUM(fun th ->
      if not(is_rip_cond th) then NO_TAC else
      let c = rand(rator(rator(rand(concl th)))) in
      let use cth =
        ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[cth]) in
      (SUBGOAL_THEN c use THENL [MLD_PREFIX_DECIDE_TAC; ALL_TAC]) ORELSE
      (SUBGOAL_THEN (mk_neg c) (use o EQF_INTRO) THENL
        [MLD_PREFIX_DECIDE_TAC; ALL_TAC])));;

(* ------------------------------------------------------------------------- *)
(* The first two bytes of the prefix, and the value of the byte that a MOV   *)
(* stores from a register holding a number below 256 (the simulation gives   *)
(* the low byte of word n as word(n MOD 256)).                               *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_BYTES2 = prove
 (`!a (s:x86state).
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8 (word_add a (word 1))) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; MLD_PREFIX_BYTES_COMBINE] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN ARITH_TAC);;

let MLD_PREFIX_VAL_BYTE = prove
 (`!n. n < 256
       ==> val(word_zx(word_zx(word n:int64):int32):byte) = n /\
           val(word_zx(word n:int64):byte) = n /\ val(word n:byte) = n /\
           val(word(n MOD 256):byte) = n`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n < 256` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_BOUND_TAC a adds the bound x < 2 EXP (8 * n) for the bytes x   *)
(* of length n read at a in the assumptions.                                 *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_READ_BYTES_BOUND = prove
 (`!a n (s:x86state) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let MLD_PREFIX_BOUND_TAC a =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,n)) s = x:num`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP MLD_PREFIX_READ_BYTES_BOUND th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reading the tables from the image. MLD_PREFIX_IMAGE_BYTES_RULE image_mc d *)
(* n is                                                                      *)
(*                                                                           *)
(*   |- !s pc. bytes_loaded s (word pc) image                                *)
(*             ==> read (memory :> bytes(word(pc + d),n)) s = v              *)
(*                                                                           *)
(* with v the value of the n bytes at d in the image (cf.                    *)
(* MLKEM_NATIVE_IMAGE_CONST_RULE of the x86 mlkem-native proofs, which gives *)
(* words). MLD_PREFIX_BYTES_SUB gives the bytes inside known bytes, and      *)
(* MLD_PREFIX_WBYTES_BYTES the word of some bytes.                           *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_IMAGE_BYTES_RULE image_mc =
  let rec take n l =
    if n = 0 then [] else
    match l with h::t -> h::take (n - 1) t | [] -> failwith "take" in
  let rec drop n l =
    if n = 0 then l else
    match l with _::t -> drop (n - 1) t | [] -> failwith "drop" in
  let imagel = dest_list(rhs(concl image_mc)) in
  let bl_tm = mk_comb(`bytes_loaded s (word pc)`,lhs(concl image_mc)) in
  fun d n ->
    let l = mk_list(take n (drop d imagel),`:byte`) in
    let th1 = UNDISCH(SPEC_ALL(BYTES_LOADED_SUBPROGRAM_RULE
                image_mc (REFL l) d)) in
    let th2 = REWRITE_RULE[bytes_loaded; READ_BYTELIST_EQ_BYTES] th1 in
    let th3 = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV LENGTH_CONV) THENC
                        RAND_CONV(REWRITE_CONV[num_of_bytelist] THENC
                                  DEPTH_CONV WORD_RED_CONV THENC
                                  NUM_REDUCE_CONV)) th2 in
    GENL [`s:x86state`; `pc:num`] (DISCH bl_tm th3);;

let MLD_PREFIX_BYTES_SUB = prove
 (`!a n i k v (s:x86state).
        read (memory :> bytes(a,n)) s = v /\ i + k <= n
        ==> read (memory :> bytes(word_add a (word i),k)) s =
            (v DIV 2 EXP (8 * i)) MOD 2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (n - i) k = k` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MIN] THEN UNDISCH_TAC `i + k <= n:num` THEN ARITH_TAC);;

let MLD_PREFIX_WBYTES_BYTES = prove
 (`!a (s:x86state).
        read (memory :> wbytes a) s:N word =
        word(read (memory :> bytes(a,dimindex(:N) DIV 8)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[GSYM VAL_READ_WBYTES; WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* MLD_PREFIX_TABLE_TAC th i k, for th as given by                           *)
(* MLD_PREFIX_IMAGE_BYTES_RULE for the n bytes at d and k = 1, 4 or 8, adds  *)
(* the value of the byte, 32-bit or 64-bit word at d + i in the state of the *)
(* assumption bytes_loaded s (word pc) ..., as                               *)
(*                                                                           *)
(*   read (memory :> bytesK (word_add (word(pc + d)) (word i))) s = word w   *)
(*                                                                           *)
(* (with word(pc + d) for i = 0), the form of the addresses in the           *)
(* simulation of a load from a table whose address is in a register.         *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_TABLE_TAC =
  let wty k = mk_finty(Num.num_of_int(8 * k)) in
  let wths =
    map (fun (k,bth,dth) ->
      let th = INST_TYPE [wty k,`:N`] MLD_PREFIX_WBYTES_BYTES in
      k,CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[GSYM bth; dth] th))
     [1,BYTES8_WBYTES,DIMINDEX_8; 4,BYTES32_WBYTES,DIMINDEX_32;
      8,BYTES64_WBYTES,DIMINDEX_64] in
  fun th i k ->
    FIRST_ASSUM(fun ath ->
      match concl ath with
        Comb(Comb(Comb(Const("bytes_loaded",_),sv),_),_) ->
          let th1 = MP (ISPECL [sv; `pc:num`] th) ath in
          let n = rand(rand(rand(rand(rator(lhand(concl th1)))))) in
          let ith = EQT_ELIM(NUM_REDUCE_CONV
                     (mk_binary "<=" (mk_binary "+" (mk_small_numeral i,
                                                     mk_small_numeral k),n))) in
          let th2 = MATCH_MP MLD_PREFIX_BYTES_SUB (CONJ th1 ith) in
          let th3 = CONV_RULE(RAND_CONV NUM_REDUCE_CONV) th2 in
          let th4 = AP_TERM (mk_const("word",[wty k,`:N`])) th3 in
          let th5 = REWRITE_RULE[GSYM(assoc k wths)] th4 in
          ASSUME_TAC(if i = 0 then REWRITE_RULE[WORD_ADD_0] th5 else th5)
      | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The addresses and the jump. The simulation gives the address that a       *)
(* RIP-relative LEA computes, from the end pc + a of the instruction and the *)
(* displacement b, as word(val(word(pc + a)) + b), which                     *)
(* MLD_PREFIX_RIPREL_CONV rewrites to word(pc + (a + b)). The jump through   *)
(* the table goes to the address of the table plus the sign extension of the *)
(* 32-bit offset, word_add (word a) (word(pc + b)) with a + b >= 2 EXP 64,   *)
(* which MLD_PREFIX_PC_CONV rewrites to word(pc + (a + b - 2 EXP 64)).       *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_RIPREL_CONV =
  let pth = prove
   (`word(val(word(pc + a):int64) + b):int64 = word(pc + (a + b))`,
    REWRITE_TAC[WORD_VAL_ADD_64; ADD_ASSOC]) in
  fun tm ->
    match tm with
      Comb(Const("word",_),Comb(Comb(Const("+",_),
        Comb(Const("val",_),Comb(Const("word",_),
          Comb(Comb(Const("+",_),Var("pc",_)),a)))),b))
      when is_numeral a && is_numeral b ->
        (REWR_CONV pth THENC RAND_CONV(RAND_CONV NUM_ADD_CONV)) tm
    | _ -> failwith "MLD_PREFIX_RIPREL_CONV";;

let MLD_PREFIX_PC_CONV =
  let p64 = num_of_string "18446744073709551616"
  and add_tm = `(+):num->num->num` in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_add",_),Comb(Const("word",_),a)),
           Comb((Const("word",_) as w),
                (Comb(Comb(Const("+",_),(Var("pc",_) as p)),b) as pb)))
      when is_numeral a && is_numeral b &&
           dest_numeral a +/ dest_numeral b >=/ p64 ->
        let c = mk_numeral(dest_numeral a +/ dest_numeral b -/ p64) in
        let rtm = mk_comb(w,mk_binop add_tm p c) in
        let eth = ARITH_RULE
         (mk_eq(mk_binop add_tm a pb,
                mk_binop add_tm (mk_binop add_tm p c) (mk_numeral p64))) in
        prove(mk_eq(tm,rtm),
          REWRITE_TAC[GSYM WORD_ADD; eth] THEN
          REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_REDUCE_CONV THEN
          REWRITE_TAC[WORD_ADD_0])
    | _ -> failwith "MLD_PREFIX_PC_CONV";;

(* ------------------------------------------------------------------------- *)
(* A 32-bit value zero-extended to 64 bits and truncated back (the loop      *)
(* compares hashalg in R9D with the 32-bit entries of oid_map, and hashalg   *)
(* is saved and reloaded as 32 bits around the copy of the context), and the *)
(* counter of the loop in EAX.                                               *)
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

(* ------------------------------------------------------------------------- *)
(* The offset 16 * j + 4 of the OID of entry j of oid_map, as computed by    *)
(* SHL rax, 4 and LEA rax, [rcx+rax*1+0x4] with RAX = j.                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_OID_OFFSET = prove
 (`!j. j < 12 ==> 1 * val(word_shl (word j:int64) 4) + 4 = 16 * j + 4`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `j < 2 EXP 64 /\ 2 EXP 4 * j < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `j < 12` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The low 7 bytes of a 64-bit word stored in memory (the code stores the    *)
(* OID with an 8-byte store and then a 4-byte store at offset 7).            *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_BYTES64_LOW7 = prove
 (`!a v (s:x86state).
        read (memory :> bytes64 a) s = word v /\ v < 2 EXP 64
        ==> read (memory :> bytes(a,7)) s = v MOD 2 EXP 56`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; MLD_PREFIX_WBYTES_BYTES; DIMINDEX_64] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(ONCE_DEPTH_CONV NUM_DIV_CONV))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,8)) s = v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    MP_TAC(ISPECL [`a:int64`; `8`; `s:x86state`;
                   `read (memory :> bytes(a,8)) s`]
      MLD_PREFIX_READ_BYTES_BOUND) THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `v < 2 EXP 64` THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `2 EXP 56 = 2 EXP (8 * 7)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** MLD_PREFIX_LOW7_TAC b adds the low 7 bytes of a numeral word stored ***)
(*** with an 8-byte store to an address involving b                      ***)

let MLD_PREFIX_LOW7_TAC b =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes64",_),a))),_)),
           Comb(Const("word",_),v))
      when is_numeral v && free_in b a ->
        let bth = EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (v,`2 EXP 64`))) in
        ASSUME_TAC(CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
                    (MATCH_MP MLD_PREFIX_BYTES64_LOW7 (CONJ th bth)))
    | _ -> NO_TAC);;

(*** A valid pre-hash has at most 64 bytes ***)

let MLD_PREFIX_PHLEN_LE = prove
 (`!h phlen. mld_prehash_valid h phlen ==> phlen <= 64`,
  REWRITE_TAC[mld_prehash_valid; mld_prehash_length] THEN
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prefix for HashML-DSA in memory, in the pieces that the code writes,  *)
(* with the addresses as in the simulation (where the code adds ctxlen as an *)
(* index with scale 1), and the OID as a number.                             *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_HASH_SPLIT = prove
 (`!a l n (s:x86state).
        read (memory :> bytes(a,2 + l + 11 + n)) s =
        read (memory :> bytes(a,2)) s +
        2 EXP 16 *
        (read (memory :> bytes(word_add a (word 2),l)) s +
         2 EXP (8 * l) *
         (read (memory :> bytes(word_add a (word (1 * l + 2)),7)) s +
          2 EXP 56 *
          (val(read (memory :> bytes32
                  (word_add a (word ((1 * l + 2) + 7)))) s) +
           2 EXP 32 *
           read (memory :> bytes(word_add a (word (1 * l + 13)),n)) s)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES32_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[ARITH_RULE `2 + l + 11 + n = 2 + (l + (7 + (4 + n)))`] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; MULT_CLAUSES] THEN
  REWRITE_TAC[ADD_AC] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX_HASH_SPLIT0 = prove
 (`!a n (s:x86state).
        read (memory :> bytes(a,2 + 0 + 11 + n)) s =
        read (memory :> bytes(a,2)) s +
        2 EXP 16 *
        (read (memory :> bytes(word_add a (word 2),7)) s +
         2 EXP 56 *
         (val(read (memory :> bytes32 (word_add a (word 9))) s) +
          2 EXP 32 * read (memory :> bytes(word_add a (word 13),n)) s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES32_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[ARITH_RULE `2 + 0 + 11 + n = 2 + (7 + (4 + n))`] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

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
(* DISCHARGE_SAFETY_PROPERTY_TAC for the events after a split whose events   *)
(* before it are a composition of parts of the template (some of them        *)
(* conditionals): memaccess_inbounds is split over each APPEND of the        *)
(* events, in the goal and in a copy of the assumption on the events before  *)
(* the split (with e2 = ... used there), so that each part is discharged by  *)
(* the assumption on it (cf. MLD_H_DISCHARGE_TAC of                          *)
(* utils/mldsa_native_hash.ml), after tac (e.g. an abbreviation of a value   *)
(* in the addresses, as CONTAINED_TAC ignores the assumptions with val). The *)
(* variable e2 must stay in the assumptions, so that the meta-variable for   *)
(* the events of the postcondition gets another name.                        *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_DISCHARGE_TAC tac =
  let is_e2_def th =
    let c = concl th in
    is_eq c && is_var(lhs c) && name_of(lhs c) = "e2" in
  let is_e2_meminb th =
    let c = concl th in
    is_comb c &&
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> is_var e && name_of e = "e2"
     | _ -> false) in
  TRY(FIRST_ASSUM(fun dth ->
        if is_e2_def dth then
          FIRST_ASSUM(fun mth ->
            if is_e2_meminb mth then
              STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND]
                                (REWRITE_RULE[dth] mth))
            else NO_TAC)
        else NO_TAC)) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN tac THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

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
(* MLD_PREFIX_HCASES_TAC splits into the cases val(word_zx hashalg) = 1,     *)
(* ..., 12, for hashalg != 0 and ~(12 < val(word_zx hashalg));               *)
(* MLD_PREFIX_HWORD_TAC k rewrites word_zx hashalg to word k in the          *)
(* assumptions in case k, except in the case assumption itself, which        *)
(* MLD_PREFIX_BRANCH_TAC may need again.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX_HCASES_TAC =
  SUBGOAL_THEN
   (list_mk_disj(map (fun k -> mk_eq(`val(word_zx (hashalg:int64):int32)`,
                                     mk_small_numeral k)) (1--12)))
   MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(val(word_zx (hashalg:int64):int32) = 0)`;
      `~(12 < val(word_zx (hashalg:int64):int32))`] THEN ARITH_TAC;
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)];;

let MLD_PREFIX_HWORD_TAC k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  let wth = prove
   (mk_imp(hk,mk_eq(`word_zx (hashalg:int64):int32`,
                    mk_comb(`word:num->int32`,mk_small_numeral k))),
    DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) in
  RULE_ASSUM_TAC(fun th ->
    if concl th = hk then th
    else CONV_RULE WORD_REDUCE_CONV (REWRITE_RULE[UNDISCH wth] th));;
