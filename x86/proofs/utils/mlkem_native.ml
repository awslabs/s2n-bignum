(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see x86/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/fips203/properties/mlkem_native.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit and 16-bit arithmetic in the registers.           *)
(* ------------------------------------------------------------------------- *)

(*** Zero extension then truncation, or the reverse ***)

let WORD_ZX_ZX_GEN = prove
 (`!x:M word.
        dimindex(:P) <= dimindex(:N)
        ==> (word_zx:N word->P word) ((word_zx:M word->N word) x) = word_zx x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** Reading the 8-bit or 16-bit part of a register ***)

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

let WORD_VAL_MOD_65536 = prove
 (`!x:N word. word (val x MOD 65536):int16 = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `65536 = 2 EXP 16`] THEN
  REWRITE_TAC[GSYM DIMINDEX_16; WORD_MOD_SIZE; word_zx]);;

(*** The 16-bit part of a register after writing it ***)

let WORD_ZX_JOIN_48_16 = prove
 (`!(h:48 word) (l:int16). word_zx(word_join h l:int64):int16 = l`,
  BITBLAST_TAC);;

(*** Simplify the results of such arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_WORD_SIMP_TAC =
  REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536; WORD_ADD; WORD_MUL;
              WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX_GEN; WORD_ZX_TRIVIAL; DIMINDEX_8; DIMINDEX_16;
           DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_ZX_JOIN_48_16];;

(* ------------------------------------------------------------------------- *)
(* The scalar Barrett reduction mlk_barrett_reduce, as compiled using a pair *)
(* of 32-bit multiply-adds, is exactly the "barred" function used for the    *)
(* vectorized code.                                                          *)
(* ------------------------------------------------------------------------- *)

(*** The Barrett reduction as compiled for x86, multiplying the bottom 16
 *** bits of the quotient by -3329 = 62207 in a 16-bit register
 ***)

let BARRED_GCC12_O2 = prove
 (`!x:int16.
     word_add x
      (word_mul (word_zx (word_ishr (word_add (word_mul (word_sx x)
                                                         (word 20159))
                                             (word 33554432)) 26:int32))
                (word 62207)):int16 =
     barred x`,
  GEN_TAC THEN REWRITE_TAC[GSYM BARRED_SCALAR] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[ISPECL [`word_mul (word_sx (x:int16)) (word 20159):int32`;
                      `word 33554432:int32`] WORD_ADD_SYM] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reading arrays given as lists, and building byte arrays incrementally.    *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES16_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int16 list) n j s:x86state.
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int16 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `16 * j = 8 * (2 * j)`;
              ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:x86state.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

(* ------------------------------------------------------------------------- *)
(* The same Montgomery reduction in the form compiled for x86, multiplying   *)
(* the bottom 16 bits by 62209 = 3329^-1 in a 16-bit register.               *)
(* ------------------------------------------------------------------------- *)

let montred_x86 = define
 `montred_x86 (t:int32):int16 =
  word_zx(word_ishr
   (word_add
     (word_mul (word_sx (word_mul (word_zx t:int16) (word 62209)):int32)
               (word 4294963967))
     t)
   16)`;;

let MONTRED_X86_SCALAR = prove
 (`!t:int32. montred_x86 t = montred_scalar t`,
  GEN_TAC THEN
  REWRITE_TAC[montred_x86; montred_scalar; SXFROM_15_SUBWORD] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_SYM]);;

(*** Folding either order of the final addition into montred_scalar ***)

let MONTRED_X86_FOLD = prove
 (`(!t:int32.
      word_zx(word_ishr
       (word_add
         (word_mul (word_sx (word_mul (word_zx t:int16) (word 62209)):int32)
                   (word 4294963967))
         t)
       16):int16 =
      montred_scalar t) /\
   (!t:int32.
      word_zx(word_ishr
       (word_add t
         (word_mul (word_sx (word_mul (word_zx t:int16) (word 62209)):int32)
                   (word 4294963967)))
       16):int16 =
      montred_scalar t)`,
  REWRITE_TAC[GSYM MONTRED_X86_SCALAR; montred_x86] THEN
  REWRITE_TAC[WORD_ADD_SYM]);;

(*** A 32-bit product formed from the 16-bit high and low halves given by
 *** PMULHW and PMULLW
 ***)

let WORD_JOIN_MULHI_MULLO = prove
 (`!a b:int16.
     word_join (word_subword (word_mul (word_sx a) (word_sx b):int32)
                             (16,16):int16)
               (word_mul a b:int16):int32 =
     word_mul (word_sx a) (word_sx b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_mul a b:int16 = word_zx(word_mul (word_sx a) (word_sx b):int32)`
  SUBST1_TAC THENL
   [SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`];
    SPEC_TAC(`word_mul (word_sx a) (word_sx b):int32`,`p:int32`) THEN
    BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The table of zetas used by the C code, as the values in the source code   *)
(* and as the bytes of the read-only data in the compiled code. The latter   *)
(* is defined here so that it can be shared by several proofs; the proofs    *)
(* still check that it is the same as the data in their object files, since  *)
(* define_assert_relocs_from_elf can then only make a benign redefinition.   *)
(* ------------------------------------------------------------------------- *)

let MLK_ZETAS_LOADED = prove
 (`!z s. bytes_loaded s (word z) mlk_zetas_data
         ==> !k. k < 128
                 ==> read(memory :> bytes16(word_add (word z) (word(2 * k))))
                     s = iword(EL k mlk_zetas)`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLK_ZETAS_DATA;
              MLK_ZETAS_DATA] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word z:int64`; `MAP iword mlk_zetas:int16 list`; `128`;
                 `k:num`; `s:x86state`]
         READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLK_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLK_ZETAS]);;

(*** The table of zetas as a memory read, which simulation preserves
 *** across unrelated stores such as register saves
 ***)

let BYTES_LOADED_MLK_ZETAS_DATA = prove
 (`!s z. bytes_loaded s z mlk_zetas_data <=>
         read (memory :> bytes(z,256)) s = num_of_bytelist mlk_zetas_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLK_ZETAS_DATA]);;

(* ------------------------------------------------------------------------- *)
(* Instantiating a quantified fact about memory at the address that the      *)
(* simulation computes from the registers, which for indexed addressing is   *)
(* not in the same form as in the fact.                                      *)
(* ------------------------------------------------------------------------- *)

let READ_INSTANCE_TAC tm =
  let l,r = dest_eq tm in
  let tryth th =
    let avs,bod = strip_forall(concl th) in
    let eq = if is_imp bod then rand bod else bod in
    if not (is_eq eq) then failwith "READ_INSTANCE_TAC" else
    let i = term_match (frees(concl th)) (rhs eq) r in
    let th1 = INSTANTIATE i (SPECL avs th) in
    MP_TAC th1 THEN
    (if is_imp(concl th1) then
       ANTS_TAC THENL
        [ARITH_TAC ORELSE
         (FIRST_ASSUM(MP_TAC o check
            (can (term_match [] `(i:num) < n`) o concl)) THEN ARITH_TAC) ORELSE
         ASM_ARITH_TAC;
         ALL_TAC]
     else ALL_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
    (CONV_TAC WORD_RULE ORELSE
     (REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC) ORELSE
     (REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> tryth th); ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Reading a 128-bit vector of constants from loaded read-only data, and     *)
(* the XMM registers as parts of the YMM registers.                          *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_BYTES128 = prove
 (`!a l k s.
        bytes_loaded s a l /\ k + 16 <= LENGTH l
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((num_of_bytelist l DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bytes128; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`;
              READ_BYTES_MOD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let XMM_EXISTSTOP = prove
 (`!c s:S. read (c :> zerotop_128) s = l
           ==> ?h. read c s = (word_join:int128->int128->int256) h l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read c (s:S):int256) (128,128):int128` THEN
  REWRITE_TAC[READ_ZEROTOP_128] THEN CONV_TAC WORD_BLAST);;

let XMM_EXISTSTOP_RULE =
  REWRITE_RULE (map GSYM
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]) o
  C ISPEC XMM_EXISTSTOP;;

let XMM_EXISTSTOP_TAC top y =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (XMM_EXISTSTOP_RULE y)) THEN
  DISCH_THEN(X_CHOOSE_TAC(mk_var(top,`:int128`)));;

(* ------------------------------------------------------------------------- *)
(* Folding the address of a RIP-relative operand of the instruction ending   *)
(* at pc + ofs, given as data - (pc + c) in the relocated code, to data + k. *)
(* ------------------------------------------------------------------------- *)

let RIPREL_FOLD = prove
 (`!pc ofs data c k.
     riprel32_within_bounds (data + k) (pc + ofs) /\ &ofs - c = &k
     ==> word (val (word (pc + ofs):int64) +
               val (word_sx (iword (&data - (&pc + c)):int32):int64)):int64 =
         word (data + k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP WORD32_ADD_SUB_OF_LT) THEN
  REWRITE_TAC[word_add; modular] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN ASM_INT_ARITH_TAC);;

let RIPREL_FOLD_TAC data ofs c k =
  MP_TAC(SPECL [`pc:num`; ofs; data; c; k] RIPREL_FOLD) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The test of a 64-bit loop counter i in RAX against n after incrementing   *)
(* it, which the simulation gives as the sum with 2^64 + 1 - n.              *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_ADD_LOOP_TEST = prove
 (`!i n m:num. 1 < n /\ n <= 2 EXP 64 /\ i < n /\ m + n = 2 EXP 64 + 1
           ==> (~(val(word_add (word i) (word m):int64) = 0) <=> i + 1 < n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i MOD 18446744073709551616 = i /\
                m MOD 18446744073709551616 = m`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i + 1 = n` THEN ASM_REWRITE_TAC[LT_REFL] THENL
   [SUBGOAL_THEN `i + m = 18446744073709551616` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    SUBGOAL_THEN `(i + m) MOD 18446744073709551616 = i + m` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Reasoning about 32-bit operations on small numbers, which the compiled    *)
(* code uses for loop counters and indices, and about the flags set when     *)
(* they or pointers with the same base are compared.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_32 = INST_TYPE [`:32`,`:N`] (GSYM WORD_ADD);;

let W32_DECIDE_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64]) THEN
  W32_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_32]) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

(*** Replace 64-bit zero extensions of 32-bit views of small numbers ***)

let WORD_ZX_ZX_64_32_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word_zx(word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REFL_TAC);;

let WORD_ZX_32_64_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REFL_TAC);;

let W64_ZX_SMALL_TAC =
  let rule (pat,th,dest) =
    W(fun (asl,w) ->
      let tms = setify (find_terms (can (term_match [] pat))
        (list_mk_conj(w::map (concl o snd) asl))) in
      MAP_EVERY (fun t ->
        MP_TAC(SPEC (dest t) th) THEN
        ANTS_TAC THENL
         [SIMPLE_ARITH_TAC;
          DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                               REWRITE_TAC[th])]) tms) in
  rule (`word_zx(word_zx(word n:int64):int32):int64`,
        WORD_ZX_ZX_64_32_SMALL,rand o rand o rand) THEN
  rule (`word_zx(word n:int32):int64`,WORD_ZX_32_64_SMALL,rand o rand);;
