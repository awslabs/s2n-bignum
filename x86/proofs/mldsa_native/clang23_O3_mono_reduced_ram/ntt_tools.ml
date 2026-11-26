(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of poly_ntt and poly_invntt_tomont of the clang 23   *)
(* build of mldsa-native (x86-64): vectorised and scalar Montgomery          *)
(* multiplication, the wrap-around of index registers, the blocks of a       *)
(* layer of the NTT.                                                         *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_ntt.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Steps of legacy SSE code, with the lanes of the 256-bit registers simplified after each step. *)
(* ------------------------------------------------------------------------- *)

let NTT_SUBWORD_JOIN_LO = prove
 (`!x y:int128. word_subword (word_join x y:int256) (0,128):int128 = y`,
  CONV_TAC WORD_BLAST);;
let NTT_SUBWORD_JOIN_HI = prove
 (`!x y:int128. word_subword (word_join x y:int256) (128,128):int128 = x`,
  CONV_TAC WORD_BLAST);;
let is_ymm_read c =
  match c with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(r,_)),_)),_) ->
      String.length r > 3 && String.sub r 0 3 = "YMM"
  | _ -> false;;
let NTT_SSE_STEPS_TAC execth ns =
  MAP_EVERY (fun n ->
    X86_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(fun th ->
      if is_ymm_read (concl th)
      then (try CONV_RULE(RAND_CONV(REWRITE_CONV[NTT_SUBWORD_JOIN_LO; NTT_SUBWORD_JOIN_HI] THENC SIMD_SIMPLIFY_CONV [])) th with Failure _ -> th)
      else th)) ns;;

(* ------------------------------------------------------------------------- *)
(* A region of n bytes inside a region that does not overlap another. *)
(* ------------------------------------------------------------------------- *)

(* a 16-byte region inside a region that does not overlap another, in the
   form after NONOVERLAPPING_CLAUSES *)
let NTT_NONOV16 = prove
 (`!op:int64 n pc sz len.
        n + 16 <= len /\ len < 2 EXP 64 /\
        nonoverlapping_modulo (2 EXP 64) (val op,len) (pc,sz)
        ==> nonoverlapping_modulo (2 EXP 64) (val(word_add op (word n):int64),16) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `pc:num`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `16`;
                `pc:num`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;

(* a region of c bytes inside a region of len bytes that does not overlap another *)
let NTT_NONOVC = prove
 (`!op:int64 n c pc sz len.
        n + c <= len /\ len < 2 EXP 64 /\
        nonoverlapping_modulo (2 EXP 64) (val op,len) (pc,sz)
        ==> nonoverlapping_modulo (2 EXP 64) (val(word_add op (word n):int64),c) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `pc:num`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `c:num`;
                `pc:num`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Offsets that wrap around 2^64 (the index of the vectorised loops counts up to 0 from a negative value). *)
(* ------------------------------------------------------------------------- *)

let NTT_W264B = prove(`word 18446744073709551616:int64 = word 0`, CONV_TAC WORD_REDUCE_CONV);;
let NTT_W264 = prove(`!n. word (18446744073709551616 + n):int64 = word n`,
  GEN_TAC THEN REWRITE_TAC[WORD_ADD; NTT_W264B; WORD_ADD_0] );;
let NTT_ADDRW1 = prove(`!i. word(1 * (18446744073709551104 + 16 * i) + 1024):int64 = word(512 + 16 * i)`,
  GEN_TAC THEN SUBGOAL_THEN `1 * (18446744073709551104 + 16 * i) + 1024 = 18446744073709551616 + (512 + 16 * i)` SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[NTT_W264]]);;
let NTT_ADDRW0 = prove(`!i. word(1 * (18446744073709551104 + 16 * i) + 512):int64 = word(16 * i)`,
  GEN_TAC THEN SUBGOAL_THEN `1 * (18446744073709551104 + 16 * i) + 512 = 18446744073709551616 + (16 * i)` SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[NTT_W264]]);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery multiplication by a constant that clang vectorises with PMULUDQ, and its scalar form. *)
(* ------------------------------------------------------------------------- *)

let NTT_L1 = prove(`!x:int64. word_subword (word_shl x 32) (32,32):int32 = word_subword x (0,32)`, CONV_TAC WORD_BLAST);;
let NTT_L2 = prove(`!x:int64. word_subword (word_shl x 32) (0,32):int32 = word 0`, CONV_TAC WORD_BLAST);;
let NTT_L3 = prove(`!y q:int32. word_subword (word_mul (word_zx y:int64) (word_zx q)) (0,32):int32 = word_mul y q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0,32):int32 = word_zx x`] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_BLAST `word_zx (word_zx (x:int32):int64):int32 = x`]);;
let NTT_L5 = prove(`!m:int32. word_subword (word_ushr (word_join m (word 0:int32):int64) 32) (0,32):int32 = m`, CONV_TAC WORD_BLAST);;
let NTT_L7 = prove(`!z:int32. word_subword (word_sx z:int64) (0,32):int32 = z`, CONV_TAC WORD_BLAST);;
let NTT_L8 = prove(`!y:int32. (if word_igt (word 0:int32) y then word 4294967295:int32 else word 0) = word_ishr y 31`, GEN_TAC THEN BITBLAST_TAC);;

let NTT_SXZX = prove(`!z:int32. &0 <= ival z ==> word_sx z:int64 = word_zx z`,
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT; GSYM MSB_IVAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;
let NTT_SXSPLIT = prove(`!y:int32. word_sx y:int64 = word_add (word_zx y) (word_shl (word_zx (word_ishr y 31)) 32)`, GEN_TAC THEN BITBLAST_TAC);;
let NTT_SHL32 = prove(`!x:int64. word_shl x 32 = word_mul x (word 4294967296)`, CONV_TAC WORD_BLAST);;

let NTT_KK = prove(`word_mul (word 4294967296) (word 4294967296):int64 = word 0`, CONV_TAC WORD_REDUCE_CONV);;
let NTT_KK0 = prove(`!x:int64. word_mul (word_mul x (word 4294967296)) (word 4294967296) = word 0`, REWRITE_TAC[GSYM WORD_MUL_ASSOC; NTT_KK; WORD_MUL_0]);;
let NTT_C3 = prove(`!(M:int64) (Tz:int64). word_add (word_mul M (word 4286586879)) (word_mul Tz (word 4294967295)) = word_sub (word_mul (word_add M Tz) (word 4294967296)) (word_add (word_mul M (word 8380417)) Tz)`, CONV_TAC WORD_RULE);;
let NTT_C4 = prove(`!(a:int64) (w:int64). word_mul (word_sub (word_mul a (word 4294967296)) w) (word 4294967296) = word_neg (word_mul w (word 4294967296))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_mul (word_sub (word_mul a (word 4294967296)) w) (word 4294967296) = word_sub (word_mul (word_mul a (word 4294967296)) (word 4294967296)) (word_mul w (word 4294967296)):int64` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[NTT_KK0] THEN CONV_TAC WORD_RULE);;
let NTT_TST = prove(`!(Tz:int64) (M:int64) (P1:int64) (P2:int64).
 word_add
 (word_mul
  (word_add (word_mul M (word 4286586879))
  (word_mul Tz (word 4294967295)))
 (word 4294967296))
 (word_add (word_mul Tz (word 4286586879))
 (word_add
  (word_mul P2
  (word 4294967296))
 P1)) =
 word_sub
 (word_add P1 (word_mul P2 (word 4294967296)))
 (word_mul
  (word_add Tz
  (word_mul M (word 4294967296)))
 (word 8380417))`,
 REPEAT GEN_TAC THEN REWRITE_TAC[NTT_C3; NTT_C4] THEN
 REWRITE_TAC[WORD_RULE `word_mul (word_add Tz (word_mul M (word 4294967296))) (word 8380417):int64 = word_add (word_mul Tz (word 8380417)) (word_mul (word_mul M (word 4294967296)) (word 8380417))`] THEN
 CONV_TAC WORD_RULE);;

let NTT_TST2 = prove(`!(Tz:int64) (M:int64) (yu:int64) (Sy:int64) (zl:int64).
 word_add
 (word_mul
  (word_add (word_mul M (word 4286586879))
  (word_mul Tz (word 4294967295)))
 (word 4294967296))
 (word_add (word_mul Tz (word 4286586879))
 (word_add
  (word_mul (word_mul Sy zl)
  (word 4294967296))
 (word_mul yu zl))) =
 word_sub
 (word_mul (word_add yu (word_mul Sy (word 4294967296))) zl)
 (word_mul
  (word_add Tz
  (word_mul M (word 4294967296)))
 (word 8380417))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`Tz:int64`;`M:int64`;`word_mul yu zl:int64`;`word_mul Sy zl:int64`] NTT_TST) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [ALL_TAC; AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE] THEN
  BINOP_TAC THEN TRY(CONV_TAC WORD_RULE) THEN REFL_TAC);;

let NTT_POSG = `!y z:int32. &0 <= ival z ==>
    (word_subword:int64->num#num->int32)
    (word_add
     (word_shl
      (word_add
       (word_mul
        ((word_zx:int32->int64)
        ((word_subword:int64->num#num->int32)
         (word_ushr
          ((word_join:int32->int32->int64)
           (word_ishr
            ((word_subword:int64->num#num->int32)
             (word_shl
              (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
             32)
            (32,32))
           31)
          (word_ishr
           ((word_subword:int64->num#num->int32)
            (word_shl
             (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
            32)
           (0,32))
          31))
         32)
        (0,32)))
       (word 4286586879))
      (word_mul
       ((word_zx:int32->int64)
       ((word_subword:int64->num#num->int32)
        (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
       (0,32)))
      (word 4294967295)))
     32)
    (word_add
     (word_mul
      ((word_zx:int32->int64)
      ((word_subword:int64->num#num->int32)
       (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
      (0,32)))
     (word 4286586879))
    (word_add
     (word_shl
      (word_mul
       ((word_zx:int32->int64) (if word_igt (word 0) y then word 4294967295 else word 0))
      ((word_zx:int32->int64) ((word_subword:int64->num#num->int32) ((word_sx:int32->int64) z) (0,32))))
     32)
    (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) ((word_subword:int64->num#num->int32) ((word_sx:int32->int64) z) (0,32)))))))
    (32,32) =
    mld_fqmul y z`;;

let NTT_LANE_POS = prove(NTT_POSG,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[NTT_L1; NTT_L2; NTT_L3; NTT_L7; NTT_L8; WORD_BLAST `word_ishr (word 0:int32) 31 = word 0`] THEN
  REWRITE_TAC[NTT_L5] THEN
  ABBREV_TAC `tl:int32 = word_mul y (word_mul z (word 58728449))` THEN
  REWRITE_TAC[mld_fqmul; mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_mul (word_zx (word_mul (word_sx (y:int32)) (word_sx (z:int32)):int64):int32) (word 58728449) = tl:int32` SUBST1_TAC THENL
   [EXPAND_TAC "tl" THEN
    SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
    REWRITE_TAC[WORD_BLAST `word_zx (word_sx (x:int32):int64):int32 = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NTT_SXZX] THEN
  REWRITE_TAC[NTT_SXSPLIT; NTT_SHL32] THEN
  MATCH_ACCEPT_TAC NTT_TST2);;

let NTT_SXZNEG = prove(`!z:int32. ival z < &0 ==> word_sx z:int64 = word_add (word_zx z) (word_mul (word 4294967295) (word 4294967296))`,
  GEN_TAC THEN REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;
let NTT_KK1 = prove(`!(Sy:int64) (Hi:int64). word_mul (word_mul Sy (word 4294967296)) (word_mul Hi (word 4294967296)) = word 0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_mul (word_mul Sy (word 4294967296)) (word_mul Hi (word 4294967296)) = word_mul (word_mul (word_mul Sy Hi) (word 4294967296)) (word 4294967296):int64` SUBST1_TAC THENL [CONV_TAC WORD_RULE; REWRITE_TAC[NTT_KK0]]);;
let NTT_PRODNEG = prove(`!(yu:int64) (Sy:int64) (zl:int64) (Hi:int64).
   word_mul (word_add yu (word_mul Sy (word 4294967296))) (word_add zl (word_mul Hi (word 4294967296))) =
   word_add (word_mul yu zl) (word_mul (word_add (word_mul Sy zl) (word_mul yu Hi)) (word 4294967296))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_mul (word_add yu (word_mul Sy (word 4294967296))) (word_add zl (word_mul Hi (word 4294967296))) =
     word_add (word_add (word_mul yu zl) (word_mul (word_add (word_mul Sy zl) (word_mul yu Hi)) (word 4294967296)))
              (word_mul (word_mul Sy (word 4294967296)) (word_mul Hi (word 4294967296))):int64` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; REWRITE_TAC[NTT_KK1; WORD_ADD_0]]);;
let NTT_TST3 = prove(`!(Tz:int64) (M:int64) (yu:int64) (Sy:int64) (zl:int64).
 word_add
 (word_mul
  (word_add (word_mul M (word 4286586879))
  (word_mul Tz (word 4294967295)))
 (word 4294967296))
 (word_add (word_mul Tz (word 4286586879))
 (word_add
  (word_mul (word_add (word_mul Sy zl) (word_mul yu (word 4294967295)))
  (word 4294967296))
 (word_mul yu zl))) =
 word_sub
 (word_mul (word_add yu (word_mul Sy (word 4294967296))) (word_add zl (word_mul (word 4294967295) (word 4294967296))))
 (word_mul
  (word_add Tz
  (word_mul M (word 4294967296)))
 (word 8380417))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NTT_PRODNEG] THEN
  MP_TAC(SPECL [`Tz:int64`;`M:int64`;`word_mul yu zl:int64`;`word_add (word_mul Sy zl) (word_mul yu (word 4294967295)):int64`] NTT_TST) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [ALL_TAC; AP_THM_TAC THEN AP_TERM_TAC THEN REFL_TAC] THEN
  REFL_TAC);;

let NTT_NEGG = `!y z:int32. ival z < &0 ==>
    (word_subword:int64->num#num->int32)
    (word_add
     (word_shl
      (word_add
       (word_mul
        ((word_zx:int32->int64)
        ((word_subword:int64->num#num->int32)
         (word_ushr
          ((word_join:int32->int32->int64)
           (word_ishr
            ((word_subword:int64->num#num->int32)
             (word_shl
              (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
             32)
            (32,32))
           31)
          (word_ishr
           ((word_subword:int64->num#num->int32)
            (word_shl
             (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
            32)
           (0,32))
          31))
         32)
        (0,32)))
       (word 4286586879))
      (word_mul
       ((word_zx:int32->int64)
       ((word_subword:int64->num#num->int32)
        (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
       (0,32)))
      (word 4294967295)))
     32)
    (word_add
     (word_mul
      ((word_zx:int32->int64)
      ((word_subword:int64->num#num->int32)
       (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) (word_mul z (word 58728449))))
      (0,32)))
     (word 4286586879))
    (word_add
     (word_shl
      (word_add
       (word_mul
        ((word_zx:int32->int64) (if word_igt (word 0) y then word 4294967295 else word 0))
        ((word_zx:int32->int64) ((word_subword:int64->num#num->int32) ((word_sx:int32->int64) z) (0,32))))
       (word_mul ((word_zx:int32->int64) y) (word 4294967295)))
     32)
    (word_mul ((word_zx:int32->int64) y) ((word_zx:int32->int64) ((word_subword:int64->num#num->int32) ((word_sx:int32->int64) z) (0,32)))))))
    (32,32) =
    mld_fqmul y z`;;

let NTT_LANE_NEG = prove(NTT_NEGG,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[NTT_L1; NTT_L2; NTT_L3; NTT_L7; NTT_L8; WORD_BLAST `word_ishr (word 0:int32) 31 = word 0`] THEN
  REWRITE_TAC[NTT_L5] THEN
  ABBREV_TAC `tl:int32 = word_mul y (word_mul z (word 58728449))` THEN
  REWRITE_TAC[mld_fqmul; mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_mul (word_zx (word_mul (word_sx (y:int32)) (word_sx (z:int32)):int64):int32) (word 58728449) = tl:int32` SUBST1_TAC THENL
   [EXPAND_TAC "tl" THEN
    SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
    REWRITE_TAC[WORD_BLAST `word_zx (word_sx (x:int32):int64):int32 = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NTT_SXZNEG] THEN
  REWRITE_TAC[NTT_SXSPLIT; NTT_SHL32] THEN
  MATCH_ACCEPT_TAC NTT_TST3);;

let NORM_R_RULES = [LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC; ADD_CLAUSES; MULT_CLAUSES];;
let NORM_R_CONV = REWRITE_CONV NORM_R_RULES THENC DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV NORM_R_RULES;;
let NORM_R_ASM_TAC = RULE_ASSUM_TAC(CONV_RULE NORM_R_CONV);;

let NTT_MONTRED_CLANG = prove
 (`!p:int64.
     word_zx(word_ushr
       (word_add (word_mul (word_ishr (word_mul p (word 252236767799803904)) 32)
                           (word 18446744073701171199)) p) 32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_ishr (word_mul p (word 252236767799803904)) 32:int64 =
    word_sx (word_mul (word_zx p:int32) (word 58728449))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `word_mul p (word 252236767799803904):int64 =
                  word_shl (word_mul p (word 58728449)) 32` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `word_mul (word_zx p:int32) (word 58728449) =
                  word_zx (word_mul p (word 58728449):int64)` SUBST1_TAC THENL
     [SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[WORD_BLAST `word_zx (word 58728449:int64):int32 = word 58728449`];
      ALL_TAC] THEN
    SPEC_TAC(`word_mul p (word 58728449):int64`,`u:int64`) THEN
    GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_ushr (v:int64) 32):int32 = word_subword v (32,32)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `word 18446744073701171199:int64 = word_neg(word 8380417)`] THEN
  CONV_TAC WORD_RULE);;


(* ------------------------------------------------------------------------- *)
(* The blocks of a layer. *)
(* ------------------------------------------------------------------------- *)

let has_c n tm = can (find_term (fun t -> is_const t && fst(dest_const t) = n)) tm;;
let NTT_BLK_ASM = prove
 (`!(G:num->int32) (m:num->int32) z start len.
     (!j. j < start ==> G j = m j) /\
     (!j. j < len ==> G (start + j) =
                      word_add (m (start + j)) (mld_fqmul (m ((start + len) + j)) z)) /\
     (!j. j < len ==> G ((start + len) + j) =
                      word_sub (m (start + j)) (mld_fqmul (m ((start + len) + j)) z)) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> G j = m j)
     ==> !j. j < 256 ==> G j = mld_ntt_block z start len m j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
   [h1;h2;h3;h4] ->
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_ntt_block] THEN
  ASM_CASES_TAC `j < start` THENL
   [ASM_SIMP_TAC[h1; ARITH_RULE `j < start ==> ~(start <= j /\ j < start + len)`;
                 ARITH_RULE `j < start ==> ~(start + len <= j /\ j < start + 2 * len)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `j < start + len` THENL
   [MP_TAC(SPEC `j - start` h2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `start + (j - start) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + len) + (j - start) = j + len` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < start) /\ j < start + len ==> start <= j /\ j < start + len`];
    ALL_TAC] THEN
  ASM_CASES_TAC `j < start + 2 * len` THENL
   [MP_TAC(SPEC `j - (start + len)` h3) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + len) + (j - (start + len)) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `start + (j - (start + len)) = j - len` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < start + len) /\ j < start + 2 * len ==> ~(start <= j /\ j < start + len) /\ start + len <= j /\ j < start + 2 * len`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j < start + 2 * len) ==> ~(start <= j /\ j < start + len) /\ ~(start + len <= j /\ j < start + 2 * len)`] THEN
  MATCH_MP_TAC h4 THEN ASM_ARITH_TAC
  | _ -> failwith "NTT_BLK_ASM"));;

let NTT_BLK_ASM2 = prove
 (`!(a:int64) (s:x86state) (m:num->int32) z start len.
     (!j. j < start ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s = m j) /\
     (!j. j < len ==> read (memory :> bytes32 (word_add a (word (4 * start + 4 * j)))) s =
                      word_add (m (start + j)) (mld_fqmul (m ((start + len) + j)) z)) /\
     (!j. j < len ==> read (memory :> bytes32 (word_add a (word (4 * (start + len) + 4 * j)))) s =
                      word_sub (m (start + j)) (mld_fqmul (m ((start + len) + j)) z)) /\
     (!j. j < 256 - (start + 2 * len)
          ==> read (memory :> bytes32 (word_add a (word (4 * (start + 2 * len) + 4 * j)))) s =
              m ((start + 2 * len) + j))
     ==> !j. j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s =
                         mld_ntt_block z start len m j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\j. read (memory :> bytes32 (word_add (a:int64) (word (4 * j)))) (s:x86state)`;
                `m:num->int32`; `z:int32`; `start:num`; `len:num`] NTT_BLK_ASM) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `4 * (start + j) = 4 * start + 4 * j` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> free_in `4 * start` (concl th) && not(has_c "word_sub" (concl th)))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `4 * ((start + len) + j) = 4 * (start + len) + 4 * j` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> has_c "word_sub" (concl th))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - (start + 2 * len)` o check (fun th -> free_in `4 * (start + 2 * len)` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + 2 * len) + (j - (start + 2 * len)) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `4 * (start + 2 * len) + 4 * (j - (start + 2 * len)) = 4 * j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[]]);;

let NTT_IBLK_ASM = prove
 (`!(G:num->int32) (m:num->int32) z start len.
     (!j. j < start ==> G j = m j) /\
     (!j. j < len ==> G (start + j) =
                      word_add (m (start + j)) (m ((start + len) + j))) /\
     (!j. j < len ==> G ((start + len) + j) =
                      mld_fqmul (word_sub (m (start + j)) (m ((start + len) + j))) z) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> G j = m j)
     ==> !j. j < 256 ==> G j = mld_invntt_block z start len m j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
   [h1;h2;h3;h4] ->
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_invntt_block] THEN
  ASM_CASES_TAC `j < start` THENL
   [ASM_SIMP_TAC[h1; ARITH_RULE `j < start ==> ~(start <= j /\ j < start + len)`;
                 ARITH_RULE `j < start ==> ~(start + len <= j /\ j < start + 2 * len)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `j < start + len` THENL
   [MP_TAC(SPEC `j - start` h2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `start + (j - start) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + len) + (j - start) = j + len` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < start) /\ j < start + len ==> start <= j /\ j < start + len`];
    ALL_TAC] THEN
  ASM_CASES_TAC `j < start + 2 * len` THENL
   [MP_TAC(SPEC `j - (start + len)` h3) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + len) + (j - (start + len)) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `start + (j - (start + len)) = j - len` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < start + len) /\ j < start + 2 * len ==> ~(start <= j /\ j < start + len) /\ start + len <= j /\ j < start + 2 * len`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j < start + 2 * len) ==> ~(start <= j /\ j < start + len) /\ ~(start + len <= j /\ j < start + 2 * len)`] THEN
  MATCH_MP_TAC h4 THEN ASM_ARITH_TAC
  | _ -> failwith "NTT_IBLK_ASM"));;

let NTT_IBLK_ASM2 = prove
 (`!(a:int64) (s:x86state) (m:num->int32) z start len.
     (!j. j < start ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s = m j) /\
     (!j. j < len ==> read (memory :> bytes32 (word_add a (word (4 * start + 4 * j)))) s =
                      word_add (m (start + j)) (m ((start + len) + j))) /\
     (!j. j < len ==> read (memory :> bytes32 (word_add a (word (4 * (start + len) + 4 * j)))) s =
                      mld_fqmul (word_sub (m (start + j)) (m ((start + len) + j))) z) /\
     (!j. j < 256 - (start + 2 * len)
          ==> read (memory :> bytes32 (word_add a (word (4 * (start + 2 * len) + 4 * j)))) s =
              m ((start + 2 * len) + j))
     ==> !j. j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s =
                         mld_invntt_block z start len m j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\j. read (memory :> bytes32 (word_add (a:int64) (word (4 * j)))) (s:x86state)`;
                `m:num->int32`; `z:int32`; `start:num`; `len:num`] NTT_IBLK_ASM) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `4 * (start + j) = 4 * start + 4 * j` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> free_in `4 * start` (concl th) && not(has_c "word_sub" (concl th)))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `4 * ((start + len) + j) = 4 * (start + len) + 4 * j` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> has_c "word_sub" (concl th))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - (start + 2 * len)` o check (fun th -> free_in `4 * (start + 2 * len)` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(start + 2 * len) + (j - (start + 2 * len)) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `4 * (start + 2 * len) + 4 * (j - (start + 2 * len)) = 4 * j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[]]);;

(* the blocks of a layer: what block i changes *)
let NTT_BLOCKS_UNCH = prove
 (`!l m i j. 2 * 2 EXP (7 - l) * i <= j ==> mld_ntt_blocks l i m j = m j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[mld_ntt_blocks];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_ntt_blocks; mld_ntt_block] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let NTT_BLOCKS_PREV = prove
 (`!l m i j. j < 2 * 2 EXP (7 - l) * i ==> mld_ntt_blocks l (SUC i) m j = mld_ntt_blocks l i m j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_ntt_blocks; mld_ntt_block] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let NTT_BLOCKS_LO = prove
 (`!l m i k. k < 2 EXP (7 - l)
     ==> mld_ntt_blocks l (SUC i) m (2 * 2 EXP (7 - l) * i + k) =
         word_add (m (2 * 2 EXP (7 - l) * i + k))
                  (mld_fqmul (m ((2 * 2 EXP (7 - l) * i + k) + 2 EXP (7 - l))) (mld_zeta (2 EXP l + i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_ntt_blocks; mld_ntt_block] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`l:num`; `m:num->int32`; `i:num`; `2 * 2 EXP (7 - l) * i + k`] NTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`l:num`; `m:num->int32`; `i:num`; `(2 * 2 EXP (7 - l) * i + k) + 2 EXP (7 - l)`] NTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let NTT_BLOCKS_HI = prove
 (`!l m i k. k < 2 EXP (7 - l)
     ==> mld_ntt_blocks l (SUC i) m ((2 * 2 EXP (7 - l) * i + 2 EXP (7 - l)) + k) =
         word_sub (m (2 * 2 EXP (7 - l) * i + k))
                  (mld_fqmul (m ((2 * 2 EXP (7 - l) * i + 2 EXP (7 - l)) + k)) (mld_zeta (2 EXP l + i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_ntt_blocks; mld_ntt_block] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`l:num`; `m:num->int32`; `i:num`; `2 * 2 EXP (7 - l) * i + k`] NTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`l:num`; `m:num->int32`; `i:num`; `(2 * 2 EXP (7 - l) * i + 2 EXP (7 - l)) + k`] NTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `((2 * 2 EXP (7 - l) * i + 2 EXP (7 - l)) + k) - 2 EXP (7 - l) = 2 * 2 EXP (7 - l) * i + k` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let NTT_CHUNK_OUTPUT_SPLIT = prove
 (`!n P x. (!j. j < x + n ==> P j) <=>
           (!j. j < x ==> P j) /\ (!k. k < n ==> P(x + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < x` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - x`) THEN
    SUBGOAL_THEN `x + (j - x) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;


(* the split of a todo range into the next chunk and the rest *)
let NTT_CHUNK_IN_L = prove
 (`!i n L. n * (i + 1) <= L
       ==> !P. ((!j. n * i <= j /\ j < L ==> P j) <=>
                (!j. n * (i + 1) <= j /\ j < L ==> P j) /\
                (!k. k < n ==> P (n * i + k)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `n * (i + 1) <= j` THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `j - n * i` o check (fun th -> free_in `k:num` (concl th) || true) o check (fun th -> can (term_match [] `!k. k < n ==> P (n * i + k)`) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `n * i + (j - n * i) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[]]]);;

