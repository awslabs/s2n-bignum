(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from mlkem-       *)
(* native's portable C implementation compiled by clang 17 with -O3 (see    *)
(* mlkem_native/README.md), which is used by its SHA-3 and SHAKE functions.  *)
(* Unlike gcc at -O3, clang has not specialized it to a rate: it takes the   *)
(* rate r as an argument, so that the specifications are those of gcc12_O2.  *)
(* It zeroes the state, XORs in each whole block of r bytes of the message   *)
(* and permutes the state, and then XORs in the rest of the message and the  *)
(* padding, but does not permute the state again. Unlike gcc12_O2, it has a  *)
(* stack guard, whose address it reads from the GOT: as for the functions    *)
(* of gcc12_O3 with a guard, the specifications have the GOT entry as a      *)
(* precondition and require that neither it nor the guard overlaps the state *)
(* or the stack. The stack is the 80 bytes of the function and the 208 used  *)
(* by mlkem_keccakf1600_permute below them. It is verified in the whole      *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem_keccakf1600_xor_bytes and mlkem_keccakf1600_permute in the image.   *)
(* ========================================================================= *)


needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_permute_proof.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_xor_bytes_proof.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;


(*** The code in the image:

    mlk_keccak_absorb_once:
      +0x0: sub     sp, sp, #0x50
      +0x4: str     x30, [sp, #16]
      +0x8: stp     x24, x23, [sp, #32]
      +0xc: stp     x22, x21, [sp, #48]
     +0x10: stp     x20, x19, [sp, #64]
     +0x14: adrp    x8, <page>
     +0x18: mov     w21, w4
     +0x1c: movi    v0.2d, #0x0
     +0x20: mov     x20, x3
     +0x24: mov     x23, x2
     +0x28: mov     w22, w1
     +0x2c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x30: mov     x19, x0
     +0x34: mov     w24, w1
     +0x38: cmp     x24, x3
     +0x3c: ldr     x8, [x8]
     +0x40: str     x8, [sp, #8]
     +0x44: strb    w4, [sp, #4]
     +0x48: stp     q0, q0, [x0]
     +0x4c: stp     q0, q0, [x0, #32]
     +0x50: stp     q0, q0, [x0, #64]
     +0x54: stp     q0, q0, [x0, #96]
     +0x58: stp     q0, q0, [x0, #128]
     +0x5c: stp     q0, q0, [x0, #160]
     +0x60: str     xzr, [x0, #192]
     +0x64: b.hi    join1
     loop1:
     +0x68: mov     x0, x19
     +0x6c: mov     x1, x23
     +0x70: mov     w2, wzr
     +0x74: mov     w3, w22
     +0x78: bl      mlkem_keccakf1600_xor_bytes
     +0x7c: mov     x0, x19
     +0x80: bl      mlkem_keccakf1600_permute
     +0x84: sub     x20, x20, x24
     +0x88: add     x23, x23, x24
     +0x8c: cmp     x20, x24
     +0x90: b.cs    loop1
     join1:
     +0x94: cbz     x20, join2
     +0x98: mov     x0, x19
     +0x9c: mov     x1, x23
     +0xa0: mov     w2, wzr
     +0xa4: mov     w3, w20
     +0xa8: bl      mlkem_keccakf1600_xor_bytes
     join2:
     +0xac: sub     w22, w22, #0x1
     +0xb0: cmp     x20, x22
     +0xb4: b.ne    +0xc0
     +0xb8: orr     w8, w21, #0x80
     +0xbc: b       join3
     +0xc0: add     x1, sp, #0x4
     +0xc4: mov     x0, x19
     +0xc8: mov     w2, w20
     +0xcc: mov     w3, #0x1
     +0xd0: bl      mlkem_keccakf1600_xor_bytes
     +0xd4: mov     w8, #0x80
     +0xd8: mov     w20, w22
     join3:
     +0xdc: add     x1, sp, #0x4
     +0xe0: mov     x0, x19
     +0xe4: mov     w2, w20
     +0xe8: mov     w3, #0x1
     +0xec: strb    w8, [sp, #4]
     +0xf0: bl      mlkem_keccakf1600_xor_bytes
     +0xf4: adrp    x8, <page>
     +0xf8: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0xfc: ldr     x9, [sp, #8]
    +0x100: ldr     x8, [x8]
    +0x104: cmp     x8, x9
    +0x108: b.ne    +0x124
    +0x10c: ldp     x20, x19, [sp, #64]
    +0x110: ldp     x22, x21, [sp, #48]
    +0x114: ldp     x24, x23, [sp, #32]
    +0x118: ldr     x30, [sp, #16]
    +0x11c: add     sp, sp, #0x50
    +0x120: ret
    +0x124: bl      __stack_chk_fail
 ***)


let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlk_keccak_absorb_once"];;


(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments, the bytes of the message and the blocks.      *)
(* ------------------------------------------------------------------------- *)


let READ_MEMORY_BYTES_SUB = prove
 (`!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WORD_ZX_BYTE_SMALL = prove
 (`!p. p < 256 ==> word_zx(word_zx(word p:int64):int32):byte = word p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `p < 256 ==> p < 4294967296 /\ p < 18446744073709551616`]);;

let WORD_ZX_SUB1_SMALL = prove
 (`!r. 0 < r /\ r < 2 EXP 32
       ==> word_zx (word_sub (word_zx (word r:int64):int32) (word 1)):int64 =
           word(r - 1)`,
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `r < 4294967296 ==> r < 18446744073709551616`;
   ARITH_RULE `0 < r ==> 1 <= r`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 4294967296`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 18446744073709551616`]);;

let BIT7_SMALL = prove
 (`!p. p < 128 ==> ~bit 7 (word p:byte)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[DIV_LT; ARITH_ODD]);;

let ABSORB_BLOCK_BOUND = prove
 (`!mlen r i. 0 < r /\ i < mlen DIV r ==> r * i + r <= mlen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN
  REWRITE_TAC[ARITH_RULE `r * i + r = (i + 1) * r`; LE_MULT_RCANCEL] THEN
  ASM_ARITH_TAC);;

let ABSORB_MOD_EQ = prove
 (`!mlen r. mlen - r * mlen DIV r = mlen MOD r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] (CONJUNCT2 DIVISION_SIMP)) THEN
  ARITH_TAC);;

let ABSORB_LOOP_TEST = prove
 (`!mlen r i. 0 < r /\ r * i + r <= mlen
              ==> (r <= mlen - r * (i + 1) <=> i + 1 < mlen DIV r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`; LE_RDIV_EQ;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, with the state as bytes between them, and for the  *)
(* arguments and the byte of padding on the stack.                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Tactics for the state as bytes between the calls, and for the arguments   *)
(* and the byte of padding on the stack.                                     *)
(* ------------------------------------------------------------------------- *)


(*** The state set to zero by the 13 stores, as bytes ***)

let KECCAK_ZERO_STATE_TAC =
  let zl = mk_list(replicate `word 0:int64` 25,`:int64`) in
  let zth = prove
   (mk_eq(`0`,mk_comb(`num_of_wordlist:int64 list->num`,zl)),
    REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC) in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes128 a) s = word 0`) (concl th)
    then CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                   ONCE_DEPTH_CONV WORD_REDUCE_CONV) th
    else th) THEN
  GEN_REWRITE_TAC RAND_CONV [zth] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN ASM_REWRITE_TAC[];;

(*** The values of the 64-bit words for r and mlen ***)

let ABSORB_VAL_TAC =
  MAP_EVERY (fun t ->
    SUBGOAL_THEN (subst [t,`n:num`] `val(word n:int64) = n`)
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC])
   [`r:num`; `mlen:num`];;

(*** The byte p stored on the stack ***)

let ABSORB_BYTE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
     `read (memory :> bytes8 a) s = word_zx(word_zx(word p:int64):int32)`)
     (concl th)
    then CONV_RULE(RAND_CONV(REWR_CONV(MP (SPEC `p:num` WORD_ZX_BYTE_SMALL)
           (MP (ARITH_RULE `p < 128 ==> p < 256`) (ASSUME `p < 128`))))) th
    else th);;

(*** The padding after t bytes of the message in the last block ***)

let ABSORB_TAIL_ARITH_TAC =
  SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN REWRITE_TAC[MULT_CLAUSES; EXP];;

(*** Case split on tm, deciding the flags of the comparison with it ***)

let ABSORB_CASE_FLAG_TAC tm =
  ASM_CASES_TAC tm THEN
  FIRST_ASSUM(fun cth ->
    if concl cth = tm || concl cth = mk_neg tm then
      RULE_ASSUM_TAC(fun th ->
        if is_iff(concl th) && free_in `ZF` (concl th)
        then REWRITE_RULE[cth] th else th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in keccak_sponge in common/fips202.ml, the message  *)
(* of mlen bytes is a number M, and the padded message is the number         *)
(* P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen), with     *)
(* mlen DIV r + 1 blocks of r bytes, where p < 128 is the first byte of the  *)
(* padding (0x1F for SHAKE and 0x06 for SHA-3). The result is the state      *)
(* keccak_absorb r P (mlen DIV r) after absorbing the whole blocks of the    *)
(* message, XORed with the last block of P, so that keccak_f1600 of it is    *)
(* keccak_absorb r P (mlen DIV r + 1), the state in keccak_sponge. In        *)
(* mlkem-native, that last permutation is the first step of squeezing. The   *)
(* stack is the 64 bytes of the function and the 192 used by the             *)
(* permutation below them.                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The byte n on the stack (at 4 bytes above the stack pointer of the    ***)
(*** function) in state sname, as a 1-byte array                          ***)

let ABSORB_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 212),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);
    ALL_TAC];;

(*** The byte p OR 128 for p < 128 is p + 128 ***)

let ORR_BYTE_LEMMA = prove
 (`!p. p < 128
       ==> word_zx(word_zx(word_zx(word_zx (word p:int64):int32 || word 128:int32):int64):int32):byte = word (p + 128)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(BITBLAST_RULE `!x:int64. word_ult x (word 128) ==> word_zx(word_zx(word_zx(word_zx x:int32 || word 128:int32):int64):int32):byte = word_zx (word_add x (word 128))`) THEN
  DISCH_THEN(MP_TAC o SPEC `word p:int64`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[word_ult; relational2; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `p MOD 18446744073709551616 = p` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ZX_WORD] THEN
  SUBGOAL_THEN `(p + 128) MOD 2 EXP dimindex(:64) = p + 128` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    REFL_TAC]);;

let ABSORB_ORR_BYTE_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes8 a) s = x:byte`) c &&
       can (find_term (fun u -> is_const u && fst(dest_const u) = "word_or")) c
    then
      ASSUME_TAC(REWRITE_RULE[MP (SPEC `p:num` ORR_BYTE_LEMMA) (ASSUME `p < 128`)] th)
    else NO_TAC);;

(*** The test of t against r - 1 after the subtraction of 1 from the 32-bit r ***)

let ABSORB_PAD_TEST_TAC =
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word(r - 1):int64) = r - 1`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th; VAL_WORD_0;
                                          ASSUME `val(word t:int64) = t`])
              THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  XOR_BRANCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, with the     *)
(* facts of the correctness proof and the events of the safety proof in the  *)
(* same intermediate condition and loop invariant, using the combined        *)
(* theorems for the callees. The stack is the 80 bytes of the function and   *)
(* the 208 used by mlkem_keccakf1600_permute below them; the function reads  *)
(* the address of the stack guard from the GOT and the guard (the canary)    *)
(* from there, and checks it again at the end. In the last block the         *)
(* equation for mlen in terms of q and t is kept as r * q + t = mlen, so     *)
(* that it does not rewrite mlen in the events, and only the goal for the    *)
(* state is rewritten with it.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;


(*** The abbreviations q and t in the last block expanded ***)

let ABSORB_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV r = q` || c = `mlen MOD r = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

(*** EXISTS_E2_TAC, also allowing the event functions f_ev_... ***)

let ABSORB_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  ABSORB_UNABBREV_TAC THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC;
    SAFE_UNIFY_REFL_TAC allowed_vars_e pfx
  ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx));;

(*** The memory accesses of the events, split along the APPENDs into the ***)
(*** concrete pieces, the traces of the callees and the earlier events ***)

let ABSORB_MEMACC_TAC =
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN
  FIRST [DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC;
         DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC];;

let ABSORB_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
         ALL_TAC])
     else ALL_TAC) THEN
    (ABSORB_MEMACC_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC));;

let ABSORB_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let ABSORB_CS_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `r * q + t = mlen`));;

let ABSORB_SAFE_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `r:num`; `mlen:num`; `guard:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let ABSORB_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (r:num) (mlen:num) (guard:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then (if mlen MOD r = r - 1
              then f_ev_ta m st r mlen guard pc stackpointer returnaddress
              else f_ev_tb m st r mlen guard pc stackpointer returnaddress)
        else (if mlen MOD r = r - 1
              then f_ev_tc m st r mlen guard pc stackpointer returnaddress
              else f_ev_td m st r mlen guard pc stackpointer returnaddress))
       (if mlen < r
        then f_ev_short m st r mlen guard pc stackpointer returnaddress
        else APPEND (f_ev_epil m st r mlen guard pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m st r mlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m st r mlen guard pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24`;;

(*** The frame of 80 bytes below the stack pointer, the byte p, the canary, ***)
(*** and the address of the stack guard, as the part of the invariant       ***)

let ABSORB_FRAME =
 `read SP s = word_add stackpointer (word 208) /\
  read (memory :> bytes64 (word_add stackpointer (word 224))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x19_init /\
  read (memory :> bytes8 (word_add stackpointer (word 212))) s = word p /\
  read (memory :> bytes64 (word_add stackpointer (word 216))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary`;;

let ABSORB_CS_MID =
  let frame = ABSORB_FRAME in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs
     `\s. read X19 s = st /\ read X20 s = word(mlen MOD r) /\
          read X21 s = word p /\ read X22 s = word r /\
          read X23 s = word_add m (word(r * mlen DIV r)) /\
          read X24 s = word r /\
          read (memory :> bytes(m,mlen)) s = M /\
          read (memory :> bytes(st,200)) s =
          val(keccak_absorb r P (mlen DIV r))`),
    frame));;

let ABSORB_CS_INV =
  mk_abs(`k:num`, mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs
     `\s. read X19 s = st /\ read X20 s = word(mlen - r * k) /\
          read X21 s = word p /\ read X22 s = word r /\
          read X23 s = word_add m (word(r * k)) /\
          read X24 s = word r /\
          read (memory :> bytes(m,mlen)) s = M /\
          read (memory :> bytes(st,200)) s = val(keccak_absorb r P k)`),
    ABSORB_FRAME)));;

let ABSORB_CS_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSORB_CS_XOR_TAC vars off len data n =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    ABSORB_CS_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len; v; data;
      `pc:num`; `read X30 s`] vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(* ------------------------------------------------------------------------- *)
(* The last block: the rest of the message, if any, and the padding. The     *)
(* code first XORs in the t = mlen MOD r bytes of the message left (unless   *)
(* t = 0), and then either the single byte p + 128 at byte t if t = r - 1,   *)
(* or the byte p at byte t and the byte 128 at byte r - 1. Four cases:       *)
(* t = 0 = r - 1 (B), t = 0 < r - 1 (A), 0 < t = r - 1 (D) and               *)
(* 0 < t < r - 1 (C).                                                        *)
(* ------------------------------------------------------------------------- *)

let ABSORB_EXEC = MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC;;

(*** The epilogue after the last call at state number n: the check of the ***)
(*** stack guard and the return, then the final state                     ***)

let ABSORB_EPILOGUE_TAC n =
  ARM_STEPS_TAC ABSORB_EXEC (n--n) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ABSORB_EXEC ((n+1)--(n+11)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The padding is the single byte p + 128 at byte r - 1, and nothing of ***)
(*** the message is left (r = 1)                                          ***)

let ABSORB_TAIL_B =
  ABSORB_PAD_TEST_TAC THEN
  ARM_STEPS_TAC ABSORB_EXEC (5--11) THEN
  ARGS_32_TAC [`t:num`] THEN
  ARM_STEPS_TAC ABSORB_EXEC (12--12) THEN
  ABSORB_ORR_BYTE_TAC THEN
  ABSORB_BYTE_FACT_TAC "s12" `p + 128` THEN
  SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `0` `1` `p + 128` 13 THEN
  ABSORB_EPILOGUE_TAC 14 THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `mlen MOD r = r - 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M DIV 2 EXP (8 * r * q) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      SUBGOAL_THEN `8 * r * q = 8 * mlen` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
    COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC];
    SUBGOAL_THEN `r - 1 = 0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_EVENTS_TAC];;

(*** Nothing of the message is left (t = 0): the byte p at byte 0 and the ***)
(*** byte 128 at byte r - 1, which is a different byte                    ***)

let ABSORB_TAIL_A =
  ABSORB_PAD_TEST_TAC THEN
  ARM_STEPS_TAC ABSORB_EXEC (5--9) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_BYTE_FACT_TAC "s9" `p:num` THEN
  SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `0` `1` `p:num` 10 THEN
  ARM_STEPS_TAC ABSORB_EXEC (11--18) THEN
  ARGS_32_TAC [`r - 1`] THEN
  ABSORB_BYTE_FACT_TAC "s18" `128` THEN
  SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `r - 1` `1` `128` 19 THEN
  ABSORB_EPILOGUE_TAC 20 THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `M DIV 2 EXP (8 * r * q) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      SUBGOAL_THEN `8 * r * q = 8 * mlen` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(mlen MOD r = r - 1)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `~(0 = r - 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_EVENTS_TAC];;

(*** The part of the message left is XORed in, and the padding is the ***)
(*** single byte p + 128 at byte t = r - 1                            ***)

let ABSORB_TAIL_D =
  ARM_STEPS_TAC ABSORB_EXEC (11--18) THEN
  ARGS_32_TAC [`r - 1`] THEN
  ABSORB_ORR_BYTE_TAC THEN
  ABSORB_BYTE_FACT_TAC "s18" `p + 128` THEN
  SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `r - 1` `1` `p + 128` 19 THEN
  ABSORB_EPILOGUE_TAC 20 THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `mlen MOD r = r - 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    UNDISCH_TAC `M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)` THEN
    ASM_REWRITE_TAC[];
    ABSORB_CS_EVENTS_TAC];;


let ABSORB_CS_SHORT_TAC =
REWRITE_TAC(!simulation_precanon_thms) THEN
ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (1--6) THEN
MLKEM_NATIVE_ADRP_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (7--26) THEN
ARGS_32_TAC [`r:num`; `p:num`] THEN ABSORB_BYTE_TAC THEN
RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN ABSORB_VAL_TAC THEN
XOR_BRANCH_TAC THEN
SUBGOAL_THEN `mlen <= r /\ ~(r = mlen)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
CONJ_TAC THENL
 [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
  DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_loop1`
   `pc + mlk_keccak_absorb_once_loop1_exit` ABSORB_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** Initialization of the loop, with the state zeroed ***)

REWRITE_TAC(!simulation_precanon_thms) THEN
ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (1--6) THEN
MLKEM_NATIVE_ADRP_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (7--26) THEN
ARGS_32_TAC [`r:num`; `p:num`] THEN ABSORB_BYTE_TAC THEN
RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN ABSORB_VAL_TAC THEN
SUBGOAL_THEN `~(mlen <= r /\ ~(r = mlen))` ASSUME_TAC THENL
 [ASM_ARITH_TAC; ALL_TAC] THEN
XOR_BRANCH_TAC THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
CONJ_TAC THENL
 [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
  DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body: XOR in a block, permute, and the loop test ***)

X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
REWRITE_TAC(!simulation_precanon_thms) THEN
ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
 [SIMPLE_ARITH_TAC; ALL_TAC] THEN
MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * i`; `r:num`;
              `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (1--5) THEN
ARGS_32_TAC [`r:num`] THEN
ABSORB_CS_XOR_TAC (ABSORB_SAFE_VARS @ [`i:num`]) `0` `r:num`
  `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)` 6 THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (7--8) THEN
KECCAK_STATE_AT_TAC `st:int64` THEN
KECCAK_STATE_THEN `st:int64` (fun v ->
  ABSORB_CS_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
    `read X30 s`] (ABSORB_SAFE_VARS @ [`i:num`]) 9) THEN
RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (10--13) THEN
SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
              word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
 [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
  ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC;
  ALL_TAC] THEN
SUBGOAL_THEN
 `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
  val(word r:int64) = r`
 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
 [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
  ALL_TAC] THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
CONJ_TAC THENL
 [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
  ALL_TAC] THEN
CONJ_TAC THENL
 [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
  CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
  MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
  UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
  ALL_TAC] THEN
DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** 0 < t < r - 1: the byte p at byte t and the byte 128 at byte r - 1 ***)

let ABSORB_TAIL_C =
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (11--15) THEN
ARGS_32_TAC [`t:num`] THEN
ABSORB_BYTE_FACT_TAC "s15" `p:num` THEN
SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
 [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `t:num` `1` `p:num` 16 THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (17--24) THEN
ARGS_32_TAC [`r - 1`] THEN
ABSORB_BYTE_FACT_TAC "s24" `128` THEN
ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `r - 1` `1` `128` 25 THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (26--26) THEN
MLKEM_NATIVE_ADRP_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (27--37) THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
CONJ_TAC THENL
 [ABSORB_CS_MLEN_TAC THEN ABSORB_TAIL_ARITH_TAC THEN
  SUBGOAL_THEN
   `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * p`; `128`; `8 * t + 8 * (r - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
  ABSORB_CS_EVENTS_TAC];;

let ABSORB_CS_TAIL_TAC =
ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
 [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
  ALL_TAC] THEN
REWRITE_TAC(!simulation_precanon_thms) THEN
ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
 [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
  ALL_TAC] THEN
SUBGOAL_THEN
 `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
  M DIV 2 EXP (8 * r * q) +
  2 EXP (8 * t) * num_of_bytelist(keccak_pad r p mlen)`
SUBST1_TAC THENL
 [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
  MATCH_MP_TAC KECCAK_BLOCK_LAST THEN ASM_SIMP_TAC[KECCAK_PAD_BOUND];
  ALL_TAC] THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (1--1) THEN
  SUBGOAL_THEN `val(word t:int64) = t`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_BRANCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (2--4) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSORB_TAIL_B; ABSORB_TAIL_A];
    XOR_BRANCH_TAC THEN
SUBGOAL_THEN `0 + t <= 200 /\ M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`
STRIP_ASSUME_TAC THENL
 [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN ASM_REWRITE_TAC[];
  ALL_TAC] THEN
MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * q`; `t:num`;
              `s1:armstate`] READ_MEMORY_BYTES_SUB) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (2--6) THEN
ARGS_32_TAC [`t:num`] THEN
ABSORB_CS_XOR_TAC ABSORB_SAFE_VARS `0` `t:num` `M DIV 2 EXP (8 * r * q)` 7 THEN
ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_EXEC (8--10) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSORB_PAD_TEST_TAC THEN ABSORB_TAIL_D;
      ABSORB_PAD_TEST_TAC THEN ABSORB_TAIL_C]];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st r m mlen p M guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 288),288] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 288),288] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 288),288]
        [word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb r
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad r p mlen))
                    (mlen DIV r))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad r p mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen guard pc
                           (word_sub stackpointer (word 288)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 288),288;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 288),288]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 288),288)])`,
  ABSORB_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_keccak_absorb_once_loop1_exit` ABSORB_CS_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSORB_CS_SHORT_TAC; ABSORB_CS_LOOP_TAC];
    ABSORB_CS_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st r m mlen p M guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        0 < r /\ r <= 200 /\ p < 128 /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 288),288)] /\
        ALLPAIRS nonoverlapping
         [(st,200); (word_sub stackpointer (word 288),288)]
         [(word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r p mlen))
                     (mlen DIV r))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r p mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->num->num->int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m:int64`; `mlen:num`;
    `p:num`; `M:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e st r m mlen p guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 288),288] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 288),288] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 288),288]
        [word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen guard pc
                           (word_sub stackpointer (word 288)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 288),288;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 288),288]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 288),288)])`,
  MP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `M:num` `read (memory :> bytes(m,mlen))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m:int64`; `mlen:num`;
    `p:num`; `M:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
