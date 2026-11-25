(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas between the machine words of compiled snappy code and the *)
(* num-based models of common/snappy/snappy_compress.ml, independent of the  *)
(* instruction set: loads from a region holding a byte list (snappy_load32,  *)
(* snappy_load64, single bytes), the hash of the compressor as the code      *)
(* computes it in 32-bit words, and the hash tables of uint16_t entries as   *)
(* functions from indices to positions.                                      *)
(* ========================================================================= *)

needs "common/snappy/snappy_compress.ml";;

(* ------------------------------------------------------------------------- *)
(* Sublists of byte lists as numbers.                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_SUB_LIST_BYTELIST_OF_NUM = prove
 (`!L p k n. p + k <= L
             ==> SUB_LIST(p,k) (bytelist_of_num L n) =
                 bytelist_of_num k (n DIV 256 EXP p)`,
  INDUCT_TAC THEN REWRITE_TAC[bytelist_of_num] THENL
   [SIMP_TAC[ARITH_RULE `p + k <= 0 <=> p = 0 /\ k = 0`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; bytelist_of_num];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `p:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; bytelist_of_num; EXP; DIV_1] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n':num`; `n DIV 256`]) THEN
    REWRITE_TAC[EXP; DIV_1; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `SUC n''`; `n DIV 256`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[bytelist_of_num; DIV_DIV; MULT_AC]]);;

let SNAPPY_NUM_OF_SUB_LIST = prove
 (`!(l:byte list) p k.
        p + k <= LENGTH l
        ==> num_of_bytelist(SUB_LIST(p,k) l) =
            (num_of_bytelist l DIV 256 EXP p) MOD 256 EXP k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  ASM_SIMP_TAC[SNAPPY_SUB_LIST_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM]);;

let SNAPPY_EL_NUM_OF_BYTELIST = prove
 (`!(l:byte list) p.
        p < LENGTH l
        ==> EL p l = word((num_of_bytelist l DIV 256 EXP p) MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `p:num`; `1`] SNAPPY_NUM_OF_SUB_LIST) THEN
  ASM_SIMP_TAC[ARITH_RULE `p < l ==> p + 1 <= l`; EXP_1] THEN
  ASM_SIMP_TAC[SUB_LIST_1; num_of_bytelist] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* Loads from a region of memory holding the byte list l at a.               *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_EXP_256 = prove
 (`!p. 256 EXP p = 2 EXP (8 * p)`,
  REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_READ_BYTES_SUB = prove
 (`!(m:(S,int64->byte)component) a (l:byte list) p k s.
        read (m :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        p + k <= LENGTH l
        ==> read (m :> bytes(word_add a (word p),k)) s =
            num_of_bytelist(SUB_LIST(p,k) l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; SNAPPY_EXP_256] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let SNAPPY_READ_BYTES32 = prove
 (`!(m:(S,int64->byte)component) x s.
        read (m :> bytes32 x) s = word(read (m :> bytes(x,4)) s)`,
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES32_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`x:int64`; `4`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_READ_BYTES64 = prove
 (`!(m:(S,int64->byte)component) x s.
        read (m :> bytes64 x) s = word(read (m :> bytes(x,8)) s)`,
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES64_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_64; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`x:int64`; `8`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_READ_BYTES8 = prove
 (`!(m:(S,int64->byte)component) x s.
        read (m :> bytes8 x) s = word(read (m :> bytes(x,1)) s)`,
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES8_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_8; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`x:int64`; `1`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_READ_LOAD32 = prove
 (`!(m:(S,int64->byte)component) a (l:byte list) p s.
        read (m :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        p + 4 <= LENGTH l
        ==> read (m :> bytes32(word_add a (word p))) s =
            word(snappy_load32 l p)`,
  SIMP_TAC[SNAPPY_READ_BYTES32; SNAPPY_READ_BYTES_SUB; snappy_load32]);;

let SNAPPY_READ_LOAD64 = prove
 (`!(m:(S,int64->byte)component) a (l:byte list) p s.
        read (m :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        p + 8 <= LENGTH l
        ==> read (m :> bytes64(word_add a (word p))) s =
            word(snappy_load64 l p)`,
  SIMP_TAC[SNAPPY_READ_BYTES64; SNAPPY_READ_BYTES_SUB; snappy_load64]);;

let SNAPPY_READ_EL = prove
 (`!(m:(S,int64->byte)component) a (l:byte list) p s.
        read (m :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        p < LENGTH l
        ==> read (m :> bytes8(word_add a (word p))) s = EL p l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNAPPY_READ_BYTES8] THEN
  MP_TAC(SPECL [`m:(S,int64->byte)component`; `a:int64`; `l:byte list`;
                `p:num`; `1`; `s:S`] SNAPPY_READ_BYTES_SUB) THEN
  ASM_SIMP_TAC[ARITH_RULE `p < l ==> p + 1 <= l`] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[SUB_LIST_1; num_of_bytelist] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* The table sizes are the powers 2^k, 8 <= k <= 15.                         *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TABLE_SIZE_CASES = prove
 (`!n. snappy_table_size n = 256 \/ snappy_table_size n = 512 \/
       snappy_table_size n = 1024 \/ snappy_table_size n = 2048 \/
       snappy_table_size n = 4096 \/ snappy_table_size n = 8192 \/
       snappy_table_size n = 16384 \/ snappy_table_size n = 32768`,
  GEN_TAC THEN REWRITE_TAC[snappy_table_size] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[]);;

let SNAPPY_TABLE_SIZE_BOUNDS = prove
 (`!n. 256 <= snappy_table_size n /\ snappy_table_size n <= 32768`,
  GEN_TAC THEN
  STRIP_ASSUME_TAC(SPEC `n:num` SNAPPY_TABLE_SIZE_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The hash of CompressFragment: (kMagic * v) >> 16 & mask, mask = 2(ts-1),  *)
(* in 32-bit words, is twice snappy_hash1.                                    *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_HASH1_LT = prove
 (`!ts v. ~(ts = 0) ==> snappy_hash1 ts v < ts`,
  SIMP_TAC[snappy_hash1; MOD_LT_EQ]);;
let SNAPPY_LOAD32_BOUND = prove
 (`!(l:byte list) p. snappy_load32 l p < 2 EXP 32`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_load32] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `256 EXP LENGTH(SUB_LIST(p,4) (l:byte list))` THEN
  REWRITE_TAC[NUM_OF_BYTELIST_BOUND; LENGTH_SUB_LIST; LE_EXP;
              ARITH_RULE `2 EXP 32 = 256 EXP 4`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_LOAD64_BOUND = prove
 (`!(l:byte list) p. snappy_load64 l p < 2 EXP 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_load64] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `256 EXP LENGTH(SUB_LIST(p,8) (l:byte list))` THEN
  REWRITE_TAC[NUM_OF_BYTELIST_BOUND; LENGTH_SUB_LIST; LE_EXP;
              ARITH_RULE `2 EXP 64 = 256 EXP 8`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_WORD32_SUB_EQ_0 = prove
 (`!a b. a < 2 EXP 32 /\ b < 2 EXP 32
         ==> (val(word_sub (word a:int32) (word_zx (word b:int64))) = 0 <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `b < 2 EXP 32 ==> b < 2 EXP 64`]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on the values of words: eliminate a MOD n and a DIV n (n a     *)
(* numeral) whose argument is below n by the arithmetic assumptions.         *)
(* ------------------------------------------------------------------------- *)

let rec snappy_term_size tm =
  match tm with
    Comb(a,b) -> snappy_term_size a + snappy_term_size b
  | Abs(_,b) -> 1 + snappy_term_size b
  | _ -> 1;;

(* Eliminate a MOD n (and a DIV n) for a numeral n where a < n follows from *)
(* the arithmetic assumptions, innermost first, until none can be.          *)
let NUM_MOD_ELIM_TAC : tactic =
  let is_md op t = is_binary op t && is_numeral(rand t) in
  let rec go (asl,w) =
    let cands = setify(find_terms (fun t -> is_md "MOD" t || is_md "DIV" t) w) in
    let cands = sort (fun a b -> snappy_term_size a < snappy_term_size b) cands in
    let try_one t =
      let a = lhand t and n = rand t in
      let lt = mk_binary "<" (a,n) in
      let lth = TAC_PROOF((asl,lt), ASM_ARITH_TAC) in
      let eq = if is_md "MOD" t then MATCH_MP MOD_LT lth
               else MATCH_MP DIV_LT lth in
      SUBST1_TAC eq in
    let rec first l = match l with
        [] -> ALL_TAC
      | t::r -> (try let tac = try_one t in tac THEN go with Failure _ -> first r) in
    first cands (asl,w) in
  go;;
let WORD_NUM_TAC : tactic =
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_USHR;
              VAL_WORD_SHL; VAL_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN NUM_MOD_ELIM_TAC THEN
  REPEAT COND_CASES_TAC THEN NUM_MOD_ELIM_TAC THEN TRY ASM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The hash of CompressFragment as compiled: ((kMul * v) >> 16) & mask in     *)
(* 32-bit words, mask = 2 * (table_size - 1), is twice snappy_hash1.          *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_HASH1_MASK = prove
 (`!ts (y:int32).
        (ts = 256 \/ ts = 512 \/ ts = 1024 \/ ts = 2048 \/ ts = 4096 \/
         ts = 8192 \/ ts = 16384 \/ ts = 32768)
        ==> val(word_and (word (2 * (ts - 1))) y) = 2 * ((val y DIV 2) MOD ts)`,
  let one k =
    let m = 2 * (1 lsl k - 1) and t = 1 lsl k - 1 in
    let bth = BITBLAST_RULE (parse_term (Printf.sprintf
      "!y:int32. word_and (word %d) y = word_shl (word_and (word %d) (word_ushr y 1)) 1" m t)) in
    let mth = CONV_RULE NUM_REDUCE_CONV
      (ISPECL [`word_ushr (y:int32) 1`; mk_small_numeral k] (CONJUNCT2 WORD_AND_MASK_WORD)) in
    REWRITE_TAC[bth; mth; VAL_WORD_SHL; VAL_WORD; VAL_WORD_USHR; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN NUM_MOD_ELIM_TAC THEN REFL_TAC in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THENL (map one [8;9;10;11;12;13;14;15]));;

let SNAPPY_WORD_ZX_WORD_64_32 = prove
 (`!n. word_zx (word n:int64):int32 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_HASH1_WORD = prove
 (`!n ts (x:int32).
        snappy_table_size n = ts
        ==> word_zx (word_and (word_zx (word (2 * (ts - 1)):int64):int32)
                     (word_ushr (word (0 + val x * 506832829):int32) 16)):int64 =
            word (2 * snappy_hash1 ts (val x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SNAPPY_WORD_ZX_WORD_64_32; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  SIMP_TAC[SNAPPY_HASH1_MASK; SNAPPY_TABLE_SIZE_CASES] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32; DIMINDEX_64; snappy_hash1;
              DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `val(x:int32) * 506832829 = 506832829 * val x`]);;

let SNAPPY_VAL_WORD_LOAD32 = prove
 (`!(l:byte list) p. val(word(snappy_load32 l p):int32) = snappy_load32 l p`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_32; SNAPPY_LOAD32_BOUND]);;
let SNAPPY_LOAD64_SHIFT_LOW32 = prove
 (`!(l:byte list) p r.
        r <= 4 /\ p + 8 <= LENGTH l
        ==> word_zx (word (snappy_load64 l p DIV 2 EXP (8 * r)):int64):int32 =
            word (snappy_load32 l (p + r))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[snappy_load64; snappy_load32] THEN
  ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST; ARITH_RULE
   `r <= 4 /\ p + 8 <= l ==> (p + r) + 4 <= l`] THEN
  REWRITE_TAC[SNAPPY_EXP_256; MOD_MOD_EXP_MIN; DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `MIN (8 * (p + 8)) (8 * p + 8 * r + MIN 64 32) = 8 * (p + r) + 32 /\
                MIN (8 * ((p + r) + 4)) (8 * (p + r) + 32) = 8 * (p + r) + 32 /\
                8 * p + 8 * r = 8 * (p + r)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MIN] THEN ASM_ARITH_TAC);;

let SNAPPY_HASH1_WORD_ALT = prove
 (`!n ts (x:int32).
        snappy_table_size n = ts
        ==> word_zx (word_and (word_zx (word (2 * (ts - 1)):int64):int32)
                     (word_ushr (word (0 + 506832829 * val x):int32) 16)):int64 =
            word (2 * snappy_hash1 ts (val x))`,
  REWRITE_TAC[ARITH_RULE `506832829 * a = a * 506832829`] THEN
  REWRITE_TAC[SNAPPY_HASH1_WORD]);;

(* ------------------------------------------------------------------------- *)
(* Regions of memory holding byte lists: appending, and prefixes of stores.  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_NUM_OF_BYTELIST_APPEND = prove
 (`!(l1:byte list) l2.
        num_of_bytelist(APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 + 8 * n`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* Appending to a region of memory holding a byte list.                      *)

let SNAPPY_READ_BYTES_APPEND = prove
 (`!(m:(S,int64->byte)component) a (l1:byte list) l2 s.
        read (m :> bytes(a,LENGTH l1)) s = num_of_bytelist l1 /\
        read (m :> bytes(word_add a (word(LENGTH l1)),LENGTH l2)) s =
        num_of_bytelist l2
        ==> read (m :> bytes(a,LENGTH(APPEND l1 l2))) s =
            num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
                  SNAPPY_NUM_OF_BYTELIST_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN ASM_REWRITE_TAC[]);;

(* A region holding a prefix of the value of a word (a store of a word whose *)
(* first k bytes matter).                                                    *)

let SNAPPY_READ_BYTES_OF_WORD = prove
 (`!(m:(S,int64->byte)component) a (w:N word) k s.
        read (m :> wbytes a) s = w /\ 8 * k <= dimindex(:N)
        ==> read (m :> bytes(a,k)) s = num_of_bytelist(bytelist_of_num k (val w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[SNAPPY_EXP_256; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;
let SNAPPY_READ_STEP16 = prove
 (`!(m:(S,int64->byte)component) b e (l:byte list) a k s.
        read (m :> bytes(word_add b (word e),k)) s =
        num_of_bytelist(SUB_LIST(a,k) l) /\
        read (m :> bytes64 (word_add b (word(e + k)))) s =
        word(snappy_load64 l (a + k)) /\
        read (m :> bytes64 (word_add b (word((e + k) + 8)))) s =
        word(snappy_load64 l ((a + k) + 8)) /\
        a + k + 16 <= LENGTH l
        ==> read (m :> bytes(word_add b (word e),k + 16)) s =
            num_of_bytelist(SUB_LIST(a,k + 16) l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ARITH_RULE `16 = 8 + 8`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `(e + k) + 8 = e + k + 8`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(e + k) + 8 = e + k + 8`;
                              ARITH_RULE `(a + k) + 8 = a + k + 8`]) THEN
  SUBGOAL_THEN
   `!x. read (bytes(x,8)) (read (m:(S,int64->byte)component) (s:S)) =
        val(read (bytes64 x) (read m s))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BYTES64_WBYTES; VAL_READ_WBYTES; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; snappy_load64] THEN
  ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST; ARITH_RULE
    `a + k + 16 <= l ==> a + k <= l /\ (a + k) + 8 <= l /\ (a + k + 8) + 8 <= l /\
                         a + k + 8 + 8 <= l`] THEN
  REWRITE_TAC[GSYM SNAPPY_EXP_256; ARITH_RULE `2 EXP 64 = 256 EXP 8`;
              MOD_MOD_REFL] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  ABBREV_TAC `X = num_of_bytelist (l:byte list) DIV 256 EXP a` THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let SNAPPY_READ_PREFIX = prove
 (`!(m:(S,int64->byte)component) x (l:byte list) a j k s.
        read (m :> bytes(x,k)) s = num_of_bytelist(SUB_LIST(a,k) l) /\
        j <= k /\ a + k <= LENGTH l
        ==> read (m :> bytes(x,j)) s = num_of_bytelist(SUB_LIST(a,j) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MIN k j = j` (SUBST1_TAC o SYM) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM READ_BYTES_MOD] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= k ==> MIN k j = j`] THEN
  ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST; ARITH_RULE
   `j <= k /\ a + k <= l ==> a + j <= l`] THEN
  REWRITE_TAC[GSYM SNAPPY_EXP_256; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= k ==> MIN k j = j`]);;
let SNAPPY_WORD32_SLE = prove
 (`!L k. L < 2 EXP 31 /\ k < 2 EXP 31
   ==> ((~(~(val(word_sub (word L:int32) (word k)) = 0) /\
          (ival(word_sub (word L:int32) (word k)) < &0 <=>
           ~(ival(word L:int32) - &k = ival(word_sub (word L:int32) (word k)))))) <=>
        L <= k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word L:int32) (word k) = iword(&L - &k)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ; IVAL_WORD_0] THEN
  REWRITE_TAC[WORD_IWORD] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `ival(iword(&L - &k):int32) = &L - &k /\ ival(iword(&L):int32) = &L`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let SNAPPY_WORD_SUB_ADD_ADD = prove
 (`!(x:N word) a b. b <= a
         ==> word_sub (word_add x (word a)) (word_add x (word b)) = word(a - b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add x a) (word_add x b) = word_sub a b`] THEN
  ASM_SIMP_TAC[WORD_SUB]);;
let SNAPPY_WORD_SX_32_64 = prove
 (`!L. L < 2 EXP 31 ==> word_sx (word L:int32):int64 = word L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  SUBGOAL_THEN `ival(word L:int32) = &L` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_IWORD]]);;
let SNAPPY_READ_COPY16 = prove
 (`!(m:(S,int64->byte)component) b e (l:byte list) a j s.
        read (m :> bytes64 (word_add b (word e))) s = word(snappy_load64 l a) /\
        read (m :> bytes64 (word_add b (word(e + 8)))) s =
        word(snappy_load64 l (a + 8)) /\
        a + 16 <= LENGTH l /\ j <= 16
        ==> read (m :> bytes(word_add b (word e),j)) s =
            num_of_bytelist(SUB_LIST(a,j) l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNAPPY_READ_PREFIX THEN
  EXISTS_TAC `16` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:(S,int64->byte)component`; `b:int64`; `e:num`; `l:byte list`;
                `a:num`; `0`; `s:S`] SNAPPY_READ_STEP16) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; SUB_LIST_CLAUSES; num_of_bytelist] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; SIMP_TAC[]]);;

let SNAPPY_EMIT_LITERAL_SHORT = prove
 (`!d:byte list. 1 <= LENGTH d /\ LENGTH d <= 60
                 ==> snappy_emit_literal d = CONS (word(4 * (LENGTH d - 1))) d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_emit_literal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_READ_BYTES_BYTE = prove
 (`!(m:(S,int64->byte)component) a (b:byte) s.
        read (m :> bytes8 a) s = b
        ==> read (m :> bytes(a,LENGTH [b])) s = num_of_bytelist [b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH; num_of_bytelist; ONE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES8_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES]);;

let SNAPPY_READ_APPEND_TAG = prove
 (`!(m:(S,int64->byte)component) op out L (t:byte) lit k s.
        read (m :> bytes(op,L)) s = num_of_bytelist out /\ LENGTH out = L /\
        read (m :> bytes8 (word_add op (word L))) s = t /\
        read (m :> bytes(word_add op (word(L + 1)),k)) s = num_of_bytelist lit /\
        LENGTH lit = k
        ==> read (m :> bytes(op,LENGTH(APPEND out (CONS t lit)))) s =
            num_of_bytelist(APPEND out (CONS t lit))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; SNAPPY_NUM_OF_BYTELIST_APPEND;
              num_of_bytelist] THEN
  SUBST1_TAC(ASSUME `LENGTH(out:byte list) = L`) THEN
  SUBST1_TAC(ASSUME `LENGTH(lit:byte list) = k`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ARITH_RULE `SUC k = 1 + k`] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (bytes(word_add op (word L),1)) (read (m:(S,int64->byte)component) (s:S)) = val(t:byte)`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `t:byte`)) THEN
    REWRITE_TAC[BYTES8_WBYTES; VAL_READ_WBYTES; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ARITH_TAC]);;

let SNAPPY_READ_APPEND_TAG_HDR = prove
 (`!(m:(S,int64->byte)component) op out L (t:byte) hdr c lit e k s.
        read (m :> bytes(op,L)) s = num_of_bytelist out /\ LENGTH out = L /\
        read (m :> bytes8 (word_add op (word L))) s = t /\
        read (m :> bytes(word_add op (word(L + 1)),c)) s = num_of_bytelist hdr /\
        LENGTH hdr = c /\
        read (m :> bytes(word_add op (word e),k)) s = num_of_bytelist lit /\
        LENGTH lit = k /\ e = (L + 1) + c
        ==> read (m :> bytes(op,LENGTH(APPEND out (CONS t (APPEND hdr lit))))) s =
            num_of_bytelist(APPEND out (CONS t (APPEND hdr lit)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `read ((m:(S,int64->byte)component) :> bytes(word_add op (word(L + 1)),
                              LENGTH(APPEND hdr lit))) (s:S) =
    num_of_bytelist(APPEND hdr (lit:byte list))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    UNDISCH_TAC `e = (L + 1) + c` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `op:int64`; `out:byte list`; `L:num`;
                 `t:byte`; `APPEND hdr lit:byte list`;
                 `LENGTH(APPEND hdr lit:byte list)`; `s:S`]
                SNAPPY_READ_APPEND_TAG) THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_EMIT_LITERAL_LONG = prove
 (`!d:byte list.
        60 <= LENGTH d - 1 /\ LENGTH d - 1 < 65536
        ==> snappy_emit_literal d =
            if LENGTH d - 1 < 256
            then CONS (word 240) (APPEND (bytelist_of_num 1 (LENGTH d - 1)) d)
            else CONS (word 244) (APPEND (bytelist_of_num 2 (LENGTH d - 1)) d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_emit_literal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `60 <= n ==> ~(n < 60)`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;
