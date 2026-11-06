(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the NTT and inverse NTT of mldsa-native that do   *)
(* not depend on the build: the table of zetas as the bytes of the           *)
(* read-only data, and the Montgomery multiplication as the compiled code    *)
(* does it with scalar registers.                                            *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;

(* ------------------------------------------------------------------------- *)
(* The table mld_zetas as 1024 bytes, 4 for each entry, as the binary has it *)
(* in its read-only data. A proof about an image checks that the image has   *)
(* these bytes at the table's address.                                       *)
(* ------------------------------------------------------------------------- *)

let mld_zetas_data =
  let zs = map (fun t -> Num.int_of_num(dest_intconst t))
               (dest_list(rand(concl mld_zetas))) in
  let bs = Bytes.create (4 * length zs) in
  let _ = List.iteri (fun i z ->
    let m = if z < 0 then z + 4294967296 else z in
    for k = 0 to 3 do
      Bytes.set bs (4 * i + k) (Char.chr ((m lsr (8 * k)) land 255))
    done) zs in
  new_definition(mk_eq(mk_var("mld_zetas_data",`:byte list`),
                       term_of_bytes bs));;

let MLD_ZETAS_DATA = prove
 (`num_of_bytelist mld_zetas_data =
   num_of_wordlist (MAP iword mld_zetas:int32 list)`,
  REWRITE_TAC[mld_zetas_data; mld_zetas; MAP] THEN
  REWRITE_TAC[num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_MLD_ZETAS_DATA = CONV_RULE (RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mld_zetas_data);;

let LENGTH_MLD_ZETAS = CONV_RULE (RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:int list->num` mld_zetas);;

let READ_MEMORY_BYTES32_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int32 list) n j s:armstate.
        read (memory :> bytes(a,4 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes32(word_add a (word(4 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int32 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `32 * j = 8 * (4 * j)`;
              ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let MLD_ZETAS_LOADED = prove
 (`!z s. bytes_loaded s z mld_zetas_data
         ==> !k. k < 256
                 ==> read(memory :> bytes32(word_add z (word(4 * k)))) s =
                     mld_zeta k`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLD_ZETAS_DATA;
              MLD_ZETAS_DATA; mld_zeta] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:int64`; `MAP iword mld_zetas:int32 list`; `256`;
                 `k:num`; `s:armstate`]
         READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLD_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLD_ZETAS]);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery multiplication as the compiled code does it: with          *)
(* p = SMULL a b, t = MUL (low 32 bits of p) QINV and r = SMADDL t (-q) p,   *)
(* the result is the high 32 bits of r, i.e. word_zx(word_ishr r 32).       *)
(* ------------------------------------------------------------------------- *)

let WORD_MUL_SX_IWORD = prove
 (`!a b:int32.
     word_mul (word_sx a) (word_sx b):int64 = iword(ival a * ival b)`,
  REWRITE_TAC[word_sx; GSYM IWORD_INT_MUL]);;

let WORD_ZX_ISHR_32_SUBWORD = prove
 (`!w:int64. word_zx(word_ishr w 32):int32 = word_subword w (32,32)`,
  CONV_TAC WORD_BLAST);;

let MONTGOMERY_REDUCE_SCALAR = prove
 (`!p:int64.
     word_zx(word_ishr
      (iword(ival p + ival(word_mul (word_zx p) (word 58728449):int32) *
                      ival(word 4286586879:int32)):int64) 32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce; WORD_ZX_ISHR_32_SUBWORD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `t:int32 = word_mul (word_zx (p:int64)) (word 58728449)` THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM IWORD_IVAL] THEN
  REWRITE_TAC[word_sx; WORD_IWORD; GSYM IWORD_INT_MUL; GSYM IWORD_INT_SUB] THEN
  REWRITE_TAC[IWORD_EQ; DIMINDEX_64] THEN
  REWRITE_TAC[INTEGER_RULE `(a + b * --c:int == a - b * c) (mod n)`]);;

(*** The same with the constant -q reduced, and with the 64-bit product of ***)
(*** a and b as the code computes it with SMULL, giving mld_fqmul b a.     ***)

let MONTGOMERY_REDUCE_SCALAR_ALT = prove
 (`!p:int64.
     word_zx(word_ishr
      (iword(ival p + ival(word_mul (word_zx p) (word 58728449):int32) *
                      -- &8380417):int64) 32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM MONTGOMERY_REDUCE_SCALAR] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC);;

let WORD_MUL_QINV_32 = prove
 (`!x:int32. word(val x * 58728449):int32 = word_mul x (word 58728449)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let FQMUL_SCALAR = prove
 (`!a b:int32.
     word_zx(word_ishr
      (iword(ival(iword(ival a * ival b):int64) +
             ival(word_mul (word_zx (iword(ival a * ival b):int64))
                           (word 58728449):int32) *
             -- &8380417):int64) 32):int32 =
     mld_fqmul b a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MONTGOMERY_REDUCE_SCALAR_ALT; mld_fqmul;
              GSYM WORD_MUL_SX_IWORD] THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

(*** The simplifications that turn the code's result into mld_fqmul ***)

let FQMUL_SCALAR_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES; INT_ADD_LID;
              WORD_MUL_QINV_32; FQMUL_SCALAR];;

(*** The same with the operands of mld_fqmul the other way round, for     ***)
(*** the inverse NTT, whose code multiplies the difference by the zeta    ***)

let FQMUL_SCALAR_SWAP = prove
 (`!a b:int32.
     word_zx(word_ishr
      (iword(ival(iword(ival a * ival b):int64) +
             ival(word_mul (word_zx (iword(ival a * ival b):int64))
                           (word 58728449):int32) *
             -- &8380417):int64) 32):int32 =
     mld_fqmul a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MONTGOMERY_REDUCE_SCALAR_ALT; mld_fqmul;
              GSYM WORD_MUL_SX_IWORD]);;

let FQMUL_SCALAR_SWAP_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES; INT_ADD_LID;
              WORD_MUL_QINV_32; FQMUL_SCALAR_SWAP];;

(*** The address of the lower coefficient, relative to the upper one ***)

let WORD_4_VAL = prove
 (`!x:int64. word(4 * val x) = word_mul (word 4) x`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

(*** A Montgomery multiplication in a lane of a vectorized loop, from the ***)
(*** 64-bit product p, as SMULL, UZP1, MUL, SMLAL and UZP2 compute it     ***)

let MONTRED_VEC_LANE = prove
 (`!p:int64.
     word_subword
      (word_add (word_mul (word_sx (word_mul (word_subword p (0,32))
                                             (word 58728449):int32))
                          (word 18446744073701171199))
                p) (32,32) =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_subword (p:int64) (0,32):int32 = word_zx p`
  SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`word_sx(word_mul (word_zx (p:int64)) (word 58728449):int32)
            :int64`,`t:int64`) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub p (word_mul t c):N word =
    word_add (word_mul t (word_neg c)) p`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]);;

(*** The 4-fold zero extension of a 32-bit index for a UXTW offset ***)

let VAL_WORD_ZX4_UXTW = prove
 (`!n. n < 4294967296
       ==> val(word_zx(word_zx(word_zx(word_zx(word n:int64):int32):int64)
                       :int32):int64) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REWRITE_TAC[]);;

(*** A counter decremented in a W register ***)

let WORD_ZX_SUB_1_SMALL = prove
 (`!k. 1 <= k /\ k < 4294967296
       ==> word_zx(word_sub (word k:int32) (word 1)):int64 = word(k - 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
