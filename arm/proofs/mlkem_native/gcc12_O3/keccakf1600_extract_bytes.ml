(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mlkem_keccakf1600_extract_bytes from mlkem-native's portable C            *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which copies len bytes of the 200-byte state starting at byte off. Unlike *)
(* at -O2, where it is a loop over the bytes, gcc has vectorized the copy:   *)
(* if len >= 8 and the output does not start within 15 bytes after byte      *)
(* off + 1 of the state, it copies blocks of 16 bytes with Q registers, then *)
(* possibly a block of 8 bytes with a D register, and then the last bytes    *)
(* one at a time; otherwise it copies one byte at a time as at -O2. The      *)
(* specifications are those for -O2. It is verified in the whole image (see  *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_extract_bytes:
       +0x0: mov     w2, w2
       +0x4: cbz     w3, <mlkem_keccakf1600_extract_bytes+0x4c>
       +0x8: sub     w5, w3, #0x1
       +0xc: cmp     w5, #0x6
      +0x10: b.ls    <mlkem_keccakf1600_extract_bytes+0x28>
      +0x14: add     x4, x2, #0x1
      +0x18: add     x4, x0, x4
      +0x1c: sub     x4, x1, x4
      +0x20: cmp     x4, #0xe
      +0x24: b.hi    <mlkem_keccakf1600_extract_bytes+0x50>
      +0x28: mov     w3, w3
      +0x2c: add     x2, x0, x2
      +0x30: mov     x0, #0x0
      +0x34: nop
      +0x38: ldrb    w4, [x2, x0]
      +0x3c: strb    w4, [x1, x0]
      +0x40: add     x0, x0, #0x1
      +0x44: cmp     x0, x3
      +0x48: b.ne    <mlkem_keccakf1600_extract_bytes+0x38>
      +0x4c: ret
      +0x50: add     x2, x0, x2
      +0x54: cmp     w5, #0xe
      +0x58: b.ls    <mlkem_keccakf1600_extract_bytes+0x134>
      +0x5c: and     x4, x3, #0xfffffff0
      +0x60: mov     x0, #0x0
      +0x64: nop
      +0x68: ldr     q0, [x2, x0]
      +0x6c: str     q0, [x1, x0]
      +0x70: add     x0, x0, #0x10
      +0x74: cmp     x0, x4
      +0x78: b.ne    <mlkem_keccakf1600_extract_bytes+0x68>
      +0x7c: and     w0, w3, #0xfffffff0
      +0x80: tst     x3, #0xf
      +0x84: b.eq    <mlkem_keccakf1600_extract_bytes+0x4c>
      +0x88: sub     w4, w3, w0
      +0x8c: sub     w5, w4, #0x1
      +0x90: cmp     w5, #0x6
      +0x94: b.ls    <mlkem_keccakf1600_extract_bytes+0xb0>
      +0x98: ldr     d0, [x2, w0, uxtw]
      +0x9c: and     w5, w4, #0xfffffff8
      +0xa0: str     d0, [x1, w0, uxtw]
      +0xa4: add     w0, w0, w5
      +0xa8: tst     x4, #0x7
      +0xac: b.eq    <mlkem_keccakf1600_extract_bytes+0x4c>
      +0xb0: ldrb    w5, [x2, w0, uxtw]
      +0xb4: add     w4, w0, #0x1
      +0xb8: strb    w5, [x1, w0, uxtw]
      +0xbc: cmp     w3, w4
      +0xc0: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
      +0xc4: ldrb    w6, [x2, w4, uxtw]
      +0xc8: add     w5, w0, #0x2
      +0xcc: strb    w6, [x1, w4, uxtw]
      +0xd0: cmp     w3, w5
      +0xd4: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
      +0xd8: ldrb    w6, [x2, w5, uxtw]
      +0xdc: add     w4, w0, #0x3
      +0xe0: strb    w6, [x1, w5, uxtw]
      +0xe4: cmp     w3, w4
      +0xe8: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
      +0xec: ldrb    w6, [x2, w4, uxtw]
      +0xf0: add     w5, w0, #0x4
      +0xf4: strb    w6, [x1, w4, uxtw]
      +0xf8: cmp     w3, w5
      +0xfc: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
     +0x100: ldrb    w6, [x2, w5, uxtw]
     +0x104: add     w4, w0, #0x5
     +0x108: strb    w6, [x1, w5, uxtw]
     +0x10c: cmp     w3, w4
     +0x110: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
     +0x114: ldrb    w5, [x2, w4, uxtw]
     +0x118: add     w0, w0, #0x6
     +0x11c: strb    w5, [x1, w4, uxtw]
     +0x120: cmp     w3, w0
     +0x124: b.ls    <mlkem_keccakf1600_extract_bytes+0x4c>
     +0x128: ldrb    w2, [x2, w0, uxtw]
     +0x12c: strb    w2, [x1, w0, uxtw]
     +0x130: ret
     +0x134: mov     w4, w3
     +0x138: mov     w0, #0x0
     +0x13c: b       <mlkem_keccakf1600_extract_bytes+0x98>
 ***)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_keccakf1600_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Reading 8 and 16 bytes of an array given as a number.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES128_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** A block of k bytes after the first j, both as numbers ***)

let READ_MEMORY_BYTES_EXTEND = prove
 (`!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

(*** The bytes of 8- and 16-byte words as numbers ***)

let READ_MEMORY_BYTES_OF_BYTES64 = prove
 (`!a:int64 v s:armstate.
        read (memory :> bytes64 a) s = word v
        ==> read (memory :> bytes(a,8)) s = v MOD 2 EXP (8 * 8)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_MEMORY_BYTES_OF_BYTES128 = prove
 (`!a:int64 v s:armstate.
        read (memory :> bytes128 a) s = word v
        ==> read (memory :> bytes(a,16)) s = v MOD 2 EXP (8 * 16)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_MEMORY_BYTES_OF_BYTES8_1 = prove
 (`!a:int64 v s:armstate.
        read (memory :> bytes8 a) s = word v
        ==> read (memory :> bytes(a,1)) s = v MOD 2 EXP (8 * 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics for the 32-bit arithmetic of the code on small         *)
(* numbers, and for the addresses with a 32-bit index register (UXTW).       *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:M)
       ==> (word_zx:M word->N word) (word n) = word n`,
  SIMP_TAC[WORD_ZX_WORD; MOD_LT]);;

let WORD_ZX_UXTW_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           word_zx(word_zx(word_zx(word n:int64):int32):int32):int64 = word n`,
  REWRITE_TAC[WORD_ZX_TRIVIAL] THEN SIMP_TAC[WORD_ZX_32_SMALL]);;

let WORD_ZX_BYTE_MOD = prove
 (`!y. 8 <= dimindex(:M)
       ==> (word_zx:M word->N word) (word (y MOD 256)) = word(y MOD 256)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ZX_WORD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP 8` THEN REWRITE_TAC[LE_EXP] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let WORD_ZX_BYTE_MOD_RULE =
  let pat = `read (memory :> bytes8 x) s = y` in
  let thms = map (fun ty ->
    REWRITE_RULE[] (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
                     (INST_TYPE [ty,`:M`] WORD_ZX_BYTE_MOD)))
    [`:8`; `:32`; `:64`] in
  fun th ->
    if can (term_match [] pat) (concl th) then REWRITE_RULE thms th
    else th;;

let WORD_AND_FFFFFFF0_32 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967280) = word(16 * n DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 4 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF8_32 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967288) = word(8 * n DIV 8)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 3 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF0_64 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967280) = word(16 * n DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word n:int64 = word_zx(word n:int32) /\
                word(16 * n DIV 16):int64 = word_zx(word(16 * n DIV 16):int32)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_AND_FFFFFFF0_32] THEN
  SPEC_TAC(`word n:int32`,`x:int32`) THEN BITBLAST_TAC);;

let VAL_WORD_AND_15 = prove
 (`!n. val(word_and (word n:int64) (word 15)) = (n MOD 2 EXP 64) MOD 16`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 4 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_AND_7 = prove
 (`!n. val(word_and (word n:int64) (word 7)) = (n MOD 2 EXP 64) MOD 8`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 3 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The test of the distance of the output from the state ***)

let EXT_NEAR_LEMMA = prove
 (`!x:int64. (14 <= val x /\ ~(val(word_sub x (word 14)) = 0)) <=> 14 < val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** Normalize word arithmetic on small numbers in the register values:  ***)
(*** word_zx (word n) = word n, word_sub (word x) (word y) = word(x - y) ***)
(*** and word_add (word x) (word y) = word(x + y), with the side          ***)
(*** conditions proved by arithmetic from the assumptions, then the       ***)
(*** masks of the length and simple quotients.                            ***)

let W_NORM_TAC =
  let zx_pat = `(word_zx:M word->N word) (word n)`
  and sub_pat = `word_sub (word x) (word y):N word`
  and add_pat = `word_add (word x) (word y):N word`
  and reg_pat = `read (r:(armstate,int64)component) s = x` in
  let is_reg th = can (term_match [] reg_pat) (concl th) in
  let cands (asl,w) =
    let tms = mapfilter (fun (_,th) -> if is_reg th then rand(concl th)
                                       else failwith "") asl in
    let fnd p = setify(itlist (fun t acc -> find_terms p t @ acc) tms []) in
    fnd (can (term_match [] add_pat)) @
    fnd (can (term_match [] sub_pat)) @
    fnd (can (term_match [] zx_pat)) in
  let side_tac =
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    SIMPLE_ARITH_TAC in
  let rule th = RULE_ASSUM_TAC(fun a -> if is_reg a then REWRITE_RULE[th] a
                                        else a) in
  let one_tac t =
    if can (term_match [] zx_pat) t then
      let n = rand(rand t) in
      let ity = type_of(rand t) and oty = type_of t in
      let th = SPEC n (INST_TYPE [hd(snd(dest_type ity)),`:M`;
                                  hd(snd(dest_type oty)),`:N`]
                       WORD_ZX_WORD_SMALL) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else if can (term_match [] sub_pat) t then
      let x = rand(lhand t) and y = rand(rand t) in
      let th = ISPECL [x; y] (INST_TYPE [hd(snd(dest_type(type_of t))),`:N`]
                              (GEN_ALL WORD_SUB2)) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else rule(GSYM WORD_ADD) in
  let pass = W(fun g -> MAP_EVERY (fun t -> TRY(one_tac t)) (cands g)) in
  pass THEN pass THEN pass THEN pass;;

let EXT_NORM_TAC =
  let mask_pats =
   [`word_and (word n:int32) (word 4294967280)`, WORD_AND_FFFFFFF0_32;
    `word_and (word n:int32) (word 4294967288)`, WORD_AND_FFFFFFF8_32;
    `word_and (word n:int64) (word 4294967280)`, WORD_AND_FFFFFFF0_64] in
  W_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> exists (fun (p,_) -> can (term_match [] p) t)
                                  mask_pats) (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let lth = snd(find (fun (p,_) -> can (term_match [] p) t) mask_pats) in
      let th = SPEC (rand(lhand t)) lth in
      TRY(SUBGOAL_THEN (lhand(concl th))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[MP th c])) THENL
          [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `(m * n + p) DIV m`) t &&
                           is_numeral(lhand(lhand(lhand t))))
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let eq = mk_eq(t,rand(lhand(lhand t))) in
      TRY(SUBGOAL_THEN eq (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
       [ARITH_TAC; ALL_TAC])) tms) THEN
  W_NORM_TAC;;

(*** The tests of the length with TST ***)

let EXT_TST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_AND_15; VAL_WORD_AND_7]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `n MOD 2 EXP 64`) t)
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      TRY(SUBGOAL_THEN (mk_eq(t,lhand t))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
          [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
           SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  DECIDE_FLAGS_TAC;;

(*** A branch on a comparison, decided by arithmetic ***)

let EXT_BRANCH_TAC =
  TRY(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("COND",_),c),_),_))
        when can (term_match [] `read PC s`) l ->
        (SUBGOAL_THEN c (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c)
          (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC])
    | _ -> NO_TAC));;

(*** The equations removing the extensions of 32-bit indices j ***)

let EXT_ZX_FACTS_TAC js =
  MAP_EVERY (fun j ->
    MP_TAC(SPEC j WORD_ZX_UXTW_SMALL) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                    STRIP_TAC]) js;;

(*** The bytes of the state at byte off + j of it, in the form of the ***)
(*** addresses that the code computes from a + off and j               ***)

let READ_MEMORY_BYTES8_OF_NUM_OFF = prove
 (`!a:int64 m n off j s:armstate.
        read (memory :> bytes(a,m)) s = n /\ off + j < m
        ==> read (memory :> bytes8(word_add (word_add a (word off))
                                            (word j))) s =
            word((n DIV 2 EXP (8 * (off + j))) MOD 256)`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; READ_MEMORY_BYTES8_OF_NUM]);;

let READ_MEMORY_BYTES64_OF_NUM_OFF = prove
 (`!a:int64 m n off j s:armstate.
        read (memory :> bytes(a,m)) s = n /\ off + j + 8 <= m
        ==> read (memory :> bytes64(word_add (word_add a (word off))
                                             (word j))) s =
            word((n DIV 2 EXP (8 * (off + j))) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let EXT_STATE_FACTS_TAC sname js8 js64 =
  let s = mk_var(sname,`:armstate`) in
  let one lth j =
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off:num`; j; s]
                 lth) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] in
  let one' lth j =
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`;
                  mk_binop `(+):num->num->num` `off:num` j; s] lth) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] in
  MAP_EVERY (one READ_MEMORY_BYTES8_OF_NUM_OFF) js8 THEN
  MAP_EVERY (one READ_MEMORY_BYTES64_OF_NUM_OFF) js64 THEN
  MAP_EVERY (one' READ_MEMORY_BYTES8_OF_NUM) js8 THEN
  MAP_EVERY (one' READ_MEMORY_BYTES64_OF_NUM) js64;;

(*** The stores to the output as byte arrays of the form needed below ***)

let EXT_CHUNK_LEMMA = prove
 (`!d:int64 J K v s:armstate off.
        read (memory :> bytes(word_add d (word J),K)) s =
        ((v DIV 2 EXP (8 * (off + J))) MOD 2 EXP (8 * K)) MOD 2 EXP (8 * K)
        ==> read (memory :> bytes(word_add d (word J),K)) s =
            ((v DIV 2 EXP (8 * off)) DIV 2 EXP (8 * J)) MOD 2 EXP (8 * K)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_DIV; GSYM EXP_ADD; LEFT_ADD_DISTRIB]);;

let EXT_STORES_TAC =
  let pats =
   [`read (memory :> bytes128 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES128;
    `read (memory :> bytes64 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES64;
    `read (memory :> bytes8 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES8_1] in
  let nums = REWRITE_RULE[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16) /\
    18446744073709551616 = 2 EXP (8 * 8) /\ 256 = 2 EXP (8 * 1) /\
    2 EXP 128 = 2 EXP (8 * 16) /\ 2 EXP 64 = 2 EXP (8 * 8)`] in
  RULE_ASSUM_TAC WORD_ZX_BYTE_MOD_RULE THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    match filter (fun (p,_) -> can (term_match [] p) c) pats with
      (_,lth)::_ ->
        (try MATCH_MP EXT_CHUNK_LEMMA (nums(MATCH_MP lth th))
         with Failure _ -> th)
    | [] -> th);;

(*** Fold sums of numerals in the register values ***)

let EXT_FOLD_TAC =
  let reg_pat = `read (r:(armstate,int64)component) s = x` in
  let conv t =
    match t with
      Comb(Comb(Const("+",_),Comb(Comb(Const("+",_),x),m)),n)
        when is_numeral m && is_numeral n ->
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) t
    | _ -> failwith "EXT_FOLD_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] reg_pat) (concl th)
    then CONV_RULE(RAND_CONV(DEPTH_CONV conv)) th else th);;

(*** W32_DECIDE_FLAGS_TAC, but rewriting only the flags, so that the ***)
(*** equations for the extended indices are kept                        ***)

let EXT_W32_DECIDE_TAC =
  let flag_pat = `read (f:(armstate,bool)component) s <=> p` in
  let is_flag th = can (term_match [] flag_pat) (concl th) in
  W(fun (asl,w) ->
    let tms = setify (itlist (fun (_,th) acc ->
      if is_flag th then
        find_terms (can (term_match [] `word_zx(word n:int64):int32`))
                   (concl th) @ acc
      else acc) asl []) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a ->
          if is_flag a then REWRITE_RULE[th] a else a))]) tms) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

let EXT_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC [n] THEN
  EXT_NORM_TAC THEN EXT_FOLD_TAC THEN
  TRY EXT_W32_DECIDE_TAC THEN EXT_BRANCH_TAC;;

(*** The events, by the path taken: nothing for len = 0; the byte loop,   ***)
(*** entered after one or two tests; for 8 <= len < 16 a straight line;   ***)
(*** otherwise the loop over blocks of 16 bytes and then the rest, by     ***)
(*** len MOD 16. The straight lines have len (or len DIV 16) as argument  ***)
(*** only through the number of whole blocks, so that len can be          ***)
(*** replaced by its value in them.                                       ***)

let EXT_EVENTS_TERM =
  let ev nm args = "f_ev_" ^ nm ^ " " ^ args in
  let full = "a d off len pc returnaddress"
  and short = "a d off pc returnaddress"
  and tailargs = "a d off (len DIV 16) pc returnaddress" in
  let rec cases var lo hi pfx args =
    if lo = hi then ev (pfx ^ string_of_int lo) args else
    "(if " ^ var ^ " = " ^ string_of_int lo ^ " then " ^
    ev (pfx ^ string_of_int lo) args ^ " else " ^
    cases var (lo + 1) hi pfx args ^ ")" in
  let byteloop k =
    "APPEND (" ^ ev ("be" ^ k) full ^ ") (APPEND (ENUMERATEL len (\\i. " ^
    ev ("bl" ^ k) full ^ " i)) (" ^ ev ("bp" ^ k) full ^ "))" in
  parse_term
   ("\\(a:int64) (d:int64) (off:num) (len:num) (pc:num) " ^
    "(returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" full ^
    " else if len <= 7 then " ^ byteloop "1" ^
    " else if ~(14 < val(word_sub d (word_add a (word (off + 1))):int64))" ^
    " then " ^ byteloop "2" ^
    " else if len < 16 then " ^ cases "len" 8 15 "s" short ^
    " else APPEND " ^ cases "len MOD 16" 0 15 "r" tailargs ^
    " (APPEND (" ^ ev "ve" full ^ ") (APPEND (ENUMERATEL (len DIV 16) (\\i. " ^
    ev "vl" full ^ " i)) (" ^ ev "vp" full ^ "))) :(uarch_event)list");;

(*** After a store of k bytes at d + j, the output up to j + k = n ***)

let EXT_PREFIX_TAC j k n =
  let ppat = subst [j,`j:num`] `read (memory :> bytes(d:int64,j)) s = y`
  and cpat = subst [j,`j:num`; k,`k:num`]
    `read (memory :> bytes(word_add (d:int64) (word j),k)) s = y` in
  let eth = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` j k,n)) in
  EXT_STORES_TAC THEN
  FIRST_ASSUM(fun pth ->
    if not(can (term_match [] ppat) (concl pth)) then NO_TAC else
    FIRST_ASSUM(fun cth ->
      if not(can (term_match [] cpat) (concl cth)) then NO_TAC else
      ASSUME_TAC(REWRITE_RULE[eth]
        (MATCH_MP READ_MEMORY_BYTES_EXTEND (CONJ pth cth)))));;

(*** The rest of the output after the blocks of 16 bytes, for ***)
(*** len = 16 * q + r, from the exit of the loop              ***)

let EXT_VTAIL_TAC r =
  let k = if r >= 8 then r - 8 else r and c0 = if r >= 8 then 8 else 0 in
  let ix c = if c = 0 then `16 * q` else
             mk_binop `(+):num->num->num` `16 * q` (mk_small_numeral c) in
  let byte_idxs = map (fun t -> ix (c0 + t)) (0--(k-1)) in
  let d_idxs = if r >= 8 then [ix 0] else [] in
  let blocks =
    (if r >= 8 then [ix 0,`8`] else []) @
    map (fun t -> (ix(c0 + t),`1`)) (0--(k-1)) in
  (*** the steps, with the stores and the blocks they write ***)
  let byte_steps s =
    if k = 0 then [] else
    let rec go t s =
      if t = k then [] else
      if t = 6 then [s+1,None; s+2,Some(ix(c0 + 6)); s+3,None] else
      [s+1,None; s+2,None; s+3,Some(ix(c0 + t)); s+4,None; s+5,None] @
      go (t + 1) (s + 5) in
    let l = go 0 s in
    if k <= 6 then l @ [s+5*k+1,None] else l in
  let dsteps = map (fun n -> n,if n = 10 then Some(ix 0) else None) in
  let steps =
    if r = 0 then dsteps(1--4) else
    if r <= 7 then dsteps(1--7) @ byte_steps 7 else
    if r = 8 then dsteps(1--14) else dsteps(1--13) @ byte_steps 13 in
  let size_of j = assoc j blocks in
  let next_of j =
    let c = if j = `16 * q` then 0 else dest_small_numeral(rand j) in
    ix(c + dest_small_numeral(size_of j)) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  EXT_ZX_FACTS_TAC (d_idxs @ byte_idxs) THEN
  EXT_STATE_FACTS_TAC "s0" byte_idxs d_idxs THEN
  MAP_EVERY (fun (j,k) ->
    SUBGOAL_THEN (subst [j,`j:num`; k,`k:num`]
      `nonoverlapping (word_add d (word j):int64,k) (word pc,libmlkem_size)`)
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC]) blocks THEN
  MAP_EVERY (fun (n,st) ->
    (if n = 2 then
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
       [n] THEN
      EXT_TST_TAC
     else EXT_STEP_TAC n) THEN
    (match st with
       None -> ALL_TAC
     | Some j -> EXT_PREFIX_TAC j (size_of j) (next_of j))) steps THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ((CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCHARGE_SAFETY_PROPERTY_TAC])
   ORELSE DISCHARGE_SAFETY_PROPERTY_TAC);;


(*** The prologue up to the test of the distance (steps 1 to 10) ***)

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

let EXT_PROLOGUE_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC (1--2) THEN
  TRY EXTRACT_BYTES_ARGS_TAC THEN TRY(ARGS_32_TAC [`off:num`]) THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC [i] THEN
    W_NORM_TAC THEN TRY EXT_W32_DECIDE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXT_NEAR_LEMMA]) THEN EXT_BRANCH_TAC)
   (3--n);;

(*** The invariant of the loop over the bytes ***)

let EXT_INV1 =
 `\i s. read X0 s = word i /\ read X1 s = d /\ read X3 s = word len /\
        read X2 s = word_add a (word off) /\
        read X30 s = returnaddress /\
        read (memory :> bytes(a,200)) s = val(S:1600 word) /\
        read (memory :> bytes(d,i)) s =
        (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)`;;

let EXT_BYTELOOP_TAC n =
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mlkem_keccakf1600_extract_bytes_loop1`
   `pc + mlkem_keccakf1600_extract_bytes_loop1_exit` EXT_INV1 THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The prologue to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    EXT_PROLOGUE_TAC n THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, copying one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    EXT_STATE_FACTS_TAC "s0" [`i:num`] [] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (1--3) THEN
    W_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (4--4) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (5--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i + 1 = len) <=> i + 1 < len` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i < len` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXT_STORES_TAC THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The blocks of 16 bytes, up to the exit of their loop ***)

let EXT_INV2 =
 `\i s. read X0 s = word(16 * i) /\ read X1 s = d /\
        read X2 s = word_add a (word off) /\ read X3 s = word len /\
        read X4 s = word(16 * len DIV 16) /\ read X30 s = returnaddress /\
        read (memory :> bytes(a,200)) s = val(S:1600 word) /\
        read (memory :> bytes(d,16 * i)) s =
        (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (16 * i))`;;

let EXT_MIDV =
 `\s. read X0 s = word(16 * len DIV 16) /\ read X1 s = d /\
      read X2 s = word_add a (word off) /\ read X3 s = word len /\
      read X30 s = returnaddress /\
      read (memory :> bytes(a,200)) s = val(S:1600 word) /\
      read (memory :> bytes(d,16 * len DIV 16)) s =
      (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (16 * len DIV 16))`;;

let EXT_LOOP2_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 16`
   `pc + mlkem_keccakf1600_extract_bytes_loop2`
   `pc + mlkem_keccakf1600_extract_bytes_loop2_exit` EXT_INV2 THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** The prologue to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    EXT_PROLOGUE_TAC 13 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (14--14) THEN
    EXT_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (15--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, copying 16 bytes, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `16 * i + 16 <= len` ASSUME_TAC THENL
     [UNDISCH_TAC `i < len DIV 16` THEN
      REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
      SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + 16 * i`;
                  `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (1--3) THEN
    W_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (4--4) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC
     (5--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(16 * i + 16 = 16 * len DIV 16) <=> i + 1 < len DIV 16`
     SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i < len DIV 16` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      EXT_STORES_TAC THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit of the loop ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The case len MOD 16 = r after the blocks of 16 bytes ***)

let EXT_RCASE_TAC r =
  let rt = mk_small_numeral r in
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = len DIV 16` THEN
  SUBGOAL_THEN (mk_eq(`len:num`,
     if r = 0 then `16 * q` else mk_binop `(+):num->num->num` `16 * q` rt))
    SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN
    FIRST_X_ASSUM(MP_TAC o check
      (fun th -> concl th = mk_eq(`len MOD 16`,rt))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  EXT_VTAIL_TAC r;;

(*** Case splits on the value of a numeric term x < n ***)

let NUM_CASES_TAC x n ttac =
  let disj = list_mk_disj(map (fun i -> mk_eq(x,mk_small_numeral i))
                              (0--(n-1))) in
  MP_TAC(ARITH_RULE(mk_imp(mk_binop `(<):num->num->bool` x (mk_small_numeral n),
                           disj))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ttac);;

let EXT_RCASES_TAC =
  NUM_CASES_TAC `len MOD 16` 16 (fun th ->
    ASSUME_TAC th THEN EXT_RCASE_TAC (dest_small_numeral(rand(concl th))));;

(*** The cases 8 <= len < 16 with the copying of 8 bytes, as straight-line ***)
(*** code with len known                                                    ***)

let EXT_D0_LEMMA = prove
 (`!d:int64 v off s:armstate.
        read (memory :> bytes64 d) s =
        word((v DIV 2 EXP (8 * off)) MOD 2 EXP 64)
        ==> read (memory :> bytes(d,8)) s =
            (v DIV 2 EXP (8 * off)) MOD 2 EXP (8 * 8)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_BYTES64) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (8 * 8)`; MOD_MOD_REFL]);;

let EXT_SHORT_CASE_TAC l =
  let k = l - 8 in
  let ix c = mk_small_numeral c in
  let byte_idxs = map (fun t -> ix (8 + t)) (0--(k-1)) in
  let blocks = map (fun t -> (ix(8 + t),`1`)) (0--(k-1)) in
  let byte_steps s =
    if k = 0 then [] else
    let rec go t s =
      if t = k then [] else
      if t = 6 then [s+1,None; s+2,Some(ix(8 + 6)); s+3,None] else
      [s+1,None; s+2,None; s+3,Some(ix(8 + t)); s+4,None; s+5,None] @
      go (t + 1) (s + 5) in
    let l = go 0 s in
    if k <= 6 then l @ [s+5*k+1,None] else l in
  let steps =
    map (fun n -> n,None) (14--22) @
    (if k = 0 then [23,None] else byte_steps 22) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  EXT_STATE_FACTS_TAC "s0" byte_idxs [] THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off:num`;
                `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MAP_EVERY (fun (j,k) ->
    SUBGOAL_THEN (subst [j,`j:num`; k,`k:num`]
      `nonoverlapping (word_add d (word j):int64,k) (word pc,libmlkem_size)`)
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC]) blocks THEN
  SUBGOAL_THEN `nonoverlapping (d:int64,8) (word pc,libmlkem_size)`
   ASSUME_TAC THENL
   [NONOVERLAPPING_TAC; ALL_TAC] THEN
  EXT_PROLOGUE_TAC 13 THEN
  MAP_EVERY (fun (n,st) ->
    EXT_STEP_TAC n THEN
    (if n = 19 then
       RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0]) THEN
       FIRST_ASSUM(fun th ->
         if can (term_match [] `read (memory :> bytes64 (d:int64)) s = x`)
                (concl th)
         then ASSUME_TAC(MATCH_MP EXT_D0_LEMMA th) else NO_TAC)
     else ALL_TAC) THEN
    (match st with
       None -> ALL_TAC
     | Some j ->
         EXT_PREFIX_TAC j `1` (ix(dest_small_numeral j + 1)))) steps THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ((CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCHARGE_SAFETY_PROPERTY_TAC])
   ORELSE DISCHARGE_SAFETY_PROPERTY_TAC);;

let EXT_SHORT_TAC =
  SUBGOAL_THEN `len - 8 < 8` ASSUME_TAC THENL
   [UNDISCH_TAC `len < 16` THEN ARITH_TAC; ALL_TAC] THEN
  NUM_CASES_TAC `len - 8` 8 (fun th ->
    let l = dest_small_numeral(rand(concl th)) + 8 in
    SUBGOAL_THEN (mk_eq(`len:num`,mk_small_numeral l)) SUBST_ALL_TAC THENL
     [MP_TAC th THEN UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_EQ] THEN EXT_SHORT_CASE_TAC l);;

(*** The case len = 0 ***)

let EXT_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;


(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for callers  *)
(* whose events depend on the result, such as the rejection sampling in      *)
(* mlkem_poly_rej_uniform. As in common/fips202.ml, the state is a 1600-bit  *)
(* word S, and the bytes extracted are bytes off to off + len - 1 of it,     *)
(* which as a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).    *)
(* The output is built up from the start as a number in all the paths. The  *)
(* events are given by the path: the byte loop (entered after one or two     *)
(* tests), a straight line for 8 <= len < 16, or the loop over the blocks of *)
(* 16 bytes and a straight line depending on len MOD 16. The theorems of     *)
(* correctness and of constant time and memory safety are derived from this  *)
(* one.                                                                      *)
(* ------------------------------------------------------------------------- *)

let EXT_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC EXT_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
       forall e a d off len (S:1600 word) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`,
  EXT_INTRO_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT_LEN0_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len <= 7` THEN ASM_REWRITE_TAC[] THENL
   [EXT_BYTELOOP_TAC 9; ALL_TAC] THEN
  ASM_CASES_TAC `14 < val(word_sub d (word_add a (word (off + 1))):int64)` THEN
  ASM_REWRITE_TAC[] THENL [ALL_TAC; EXT_BYTELOOP_TAC 14] THEN
  ASM_CASES_TAC `len < 16` THEN ASM_REWRITE_TAC[] THENL
   [EXT_SHORT_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_keccakf1600_extract_bytes_loop2_exit` EXT_MIDV THEN
  CONJ_TAC THENL [EXT_LOOP2_TAC; EXT_RCASES_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d off len (S:1600 word) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len)) [(word pc,libmlkem_size); (a,200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->num->num->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d:int64`; `off:num`; `len:num`;
    `S:1600 word`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`,
  MP_TAC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S:1600 word`
   `read (memory :> wbytes a):armstate->1600 word` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d:int64`; `off:num`; `len:num`;
    `S:1600 word`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
