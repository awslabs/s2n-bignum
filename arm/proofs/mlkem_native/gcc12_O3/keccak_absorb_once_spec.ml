(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from mlkem-       *)
(* native's portable C implementation compiled by gcc 12 with -O3 (see       *)
(* mlkem_native/README.md), which is used by its SHA3-256 and SHAKE256       *)
(* functions. At -O3, gcc has replaced it by a specialized copy              *)
(* mlk_keccak_absorb_once.constprop.1 with the rate r fixed at 136, the rate *)
(* of SHA3-256 and SHAKE256, so that it takes the arguments st, m, mlen and  *)
(* p, and the specifications are those for -O2 with r = 136. (The other      *)
(* callers at -O2, mlkem_shake128_absorb_once and mlkem_sha3_512, have their *)
(* own copies of the code inlined at -O3.) It zeroes the state, XORs in each *)
(* whole block of 136 bytes of the message and permutes the state, and then  *)
(* XORs in the rest of the message and the padding, but does not permute the *)
(* state again. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlkem_keccakf1600_xor_bytes and                          *)
(* mlkem_keccakf1600_permute in the image.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlk_keccak_absorb_once:
       +0x0: movi    v0.4s, #0x0
       +0x4: stp     x19, x20, [sp, #-64]!
       +0x8: mov     x19, x0
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x20, x2
      +0x14: mov     x21, x1
      +0x18: str     x30, [sp, #32]
      +0x1c: strb    w3, [sp, #63]
      +0x20: stp     q0, q0, [x0]
      +0x24: stp     q0, q0, [x0, #32]
      +0x28: stp     q0, q0, [x0, #64]
      +0x2c: stp     q0, q0, [x0, #96]
      +0x30: stp     q0, q0, [x0, #128]
      +0x34: stp     q0, q0, [x0, #160]
      +0x38: str     xzr, [x0, #192]
      +0x3c: cmp     x2, #0x87
      +0x40: b.ls    <mlk_keccak_absorb_once+0x74>
      +0x44: nop
      +0x48: mov     x1, x21
      +0x4c: mov     w3, #0x88
      +0x50: mov     w2, #0x0
      +0x54: mov     x0, x19
      +0x58: bl      <mlkem_keccakf1600_xor_bytes>
      +0x5c: sub     x20, x20, #0x88
      +0x60: mov     x0, x19
      +0x64: bl      <mlkem_keccakf1600_permute>
      +0x68: add     x21, x21, #0x88
      +0x6c: cmp     x20, #0x87
      +0x70: b.hi    <mlk_keccak_absorb_once+0x48>
      +0x74: mov     w22, w20
      +0x78: cbnz    x20, <mlk_keccak_absorb_once+0xc0>
      +0x7c: add     x20, sp, #0x3f
      +0x80: mov     w2, w22
      +0x84: mov     x1, x20
      +0x88: mov     x0, x19
      +0x8c: mov     w3, #0x1
      +0x90: bl      <mlkem_keccakf1600_xor_bytes>
      +0x94: mov     w4, #0xffffff80
      +0x98: mov     x1, x20
      +0x9c: mov     x0, x19
      +0xa0: mov     w3, #0x1
      +0xa4: mov     w2, #0x87
      +0xa8: strb    w4, [sp, #63]
      +0xac: bl      <mlkem_keccakf1600_xor_bytes>
      +0xb0: ldp     x21, x22, [sp, #16]
      +0xb4: ldr     x30, [sp, #32]
      +0xb8: ldp     x19, x20, [sp], #64
      +0xbc: ret
      +0xc0: mov     x1, x21
      +0xc4: mov     w3, w20
      +0xc8: mov     x0, x19
      +0xcc: mov     w2, #0x0
      +0xd0: bl      <mlkem_keccakf1600_xor_bytes>
      +0xd4: cmp     x20, #0x87
      +0xd8: b.ne    <mlk_keccak_absorb_once+0x7c>
      +0xdc: ldrb    w4, [sp, #63]
      +0xe0: mov     w2, w20
      +0xe4: mov     x0, x19
      +0xe8: add     x1, sp, #0x3f
      +0xec: orr     w4, w4, #0xffffff80
      +0xf0: mov     w3, #0x1
      +0xf4: strb    w4, [sp, #63]
      +0xf8: bl      <mlkem_keccakf1600_xor_bytes>
      +0xfc: ldp     x21, x22, [sp, #16]
     +0x100: ldr     x30, [sp, #32]
     +0x104: ldp     x19, x20, [sp], #64
     +0x108: ret
     +0x10c: nop
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlk_keccak_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments, the bytes of the message and the blocks.      *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_SUB_STMT =
  `!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`;;

let READ_MEMORY_BYTES_SUB = assume_spec READ_MEMORY_BYTES_SUB_STMT;;

let WORD_ZX_BYTE_SMALL_STMT =
  `!p. p < 256 ==> word_zx(word_zx(word p:int64):int32):byte = word p`;;

let WORD_ZX_BYTE_SMALL = assume_spec WORD_ZX_BYTE_SMALL_STMT;;

let BIT7_SMALL_STMT =
  `!p. p < 128 ==> ~bit 7 (word p:byte)`;;

let BIT7_SMALL = assume_spec BIT7_SMALL_STMT;;

let ABSORB_BLOCK_BOUND_STMT =
  `!mlen r i. 0 < r /\ i < mlen DIV r ==> r * i + r <= mlen`;;

let ABSORB_BLOCK_BOUND = assume_spec ABSORB_BLOCK_BOUND_STMT;;

let ABSORB_MOD_EQ_STMT =
  `!mlen r. mlen - r * mlen DIV r = mlen MOD r`;;

let ABSORB_MOD_EQ = assume_spec ABSORB_MOD_EQ_STMT;;

let ABSORB_LOOP_TEST_STMT =
  `!mlen r i. 0 < r /\ r * i + r <= mlen
              ==> (r <= mlen - r * (i + 1) <=> i + 1 < mlen DIV r)`;;

let ABSORB_LOOP_TEST = assume_spec ABSORB_LOOP_TEST_STMT;;

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

(*** The value of the 64-bit word for mlen ***)

let ABSORB_VAL_TAC =
  SUBGOAL_THEN `val(word mlen:int64) = mlen`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The byte p stored on the stack ***)

let ABSORB_BYTE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
     `read (memory :> bytes8 a) s = word_zx(word_zx(word p:int64):int32)`)
     (concl th)
    then CONV_RULE(RAND_CONV(REWR_CONV(MP (SPEC `p:num` WORD_ZX_BYTE_SMALL)
           (MP (ARITH_RULE `p < 128 ==> p < 256`) (ASSUME `p < 128`))))) th
    else th);;

(*** The byte n on the stack in state sname, as a 1-byte array ***)

let ABSORB_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 255),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);
    ALL_TAC];;

(*** The byte p OR 128, which is p + 128 since p < 128 ***)

let ABSORB_ORR_BYTE_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes8 a) s = x:byte`) c &&
       free_in `word p:byte` (rand c) &&
       free_in `word 4294967168:int32` (rand c)
    then
      let rhs = rand c in
      let bv = genvar `:byte` in
      let eq = mk_imp(mk_neg(mk_comb(`bit 7:byte->bool`,bv)),
                      mk_eq(subst [bv,`word p:byte`] rhs,
                            mk_comb(mk_comb(`word_add:byte->byte->byte`,bv),
                                    `word 128:byte`))) in
      let bth = INST [`word p:byte`,bv] (BITBLAST_RULE eq) in
      let pth = MP bth (MP (SPEC `p:num` BIT7_SMALL) (ASSUME `p < 128`)) in
      ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] (TRANS th pth))
    else NO_TAC);;

(*** The padding after t bytes of the message in the last block ***)

let ABSORB_TAIL_ARITH_TAC =
  SUBGOAL_THEN `(136 * q + t) MOD 136 = t` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP];;

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
(* Combined correctness, constant-time and memory safety proof, as for -O2,  *)
(* with r = 136. As in keccak_sponge in common/fips202.ml, the message of    *)
(* mlen bytes is a number M, and the padded message is the number            *)
(* P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 136 p mlen), with   *)
(* mlen DIV 136 + 1 blocks of 136 bytes, where p < 128 is the first byte of  *)
(* the padding (0x1F for SHAKE256 and 0x06 for SHA3-256). The result is the  *)
(* state keccak_absorb 136 P (mlen DIV 136) after absorbing the whole blocks *)
(* of the message, XORed with the last block of P, so that keccak_f1600 of   *)
(* it is keccak_absorb 136 P (mlen DIV 136 + 1), the state in keccak_sponge. *)
(* In mlkem-native, that last permutation is the first step of squeezing.    *)
(* The stack is the 64 bytes of the function and the 192 used by the         *)
(* permutation below them. The events depend on the length mlen, which is    *)
(* public, and are given in parts: for the last block, depending on which of *)
(* the three cases it is, for a message shorter than a block, and otherwise  *)
(* for the loop over the whole blocks. The facts of the correctness proof    *)
(* and the events are in the same intermediate condition and loop            *)
(* invariant, using the combined theorems for the callees. In the last block *)
(* the equation for mlen in terms of q and t is kept as 136 * q + t = mlen,  *)
(* so that it does not rewrite mlen in the events, and only the goal for the *)
(* state is rewritten with it. The theorems of correctness and of constant   *)
(* time and memory safety are derived from this one.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The abbreviations q and t in the last block expanded ***)

let ABSORB_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV 136 = q` || c = `mlen MOD 136 = t` then SYM th
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

let ABSORB_SAFE_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `mlen:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, also when the events for the last  ***)
(*** block are already known from the case of a short message          ***)

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
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABSORB_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (mlen:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD 136 = 0
        then f_ev_t0 m st mlen pc stackpointer returnaddress
        else if mlen MOD 136 = 135
        then f_ev_t1 m st mlen pc stackpointer returnaddress
        else f_ev_t2 m st mlen pc stackpointer returnaddress)
       (if mlen < 136
        then f_ev_short m st mlen pc stackpointer returnaddress
        else APPEND (f_ev_epil m st mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV 136)
                  (\i. f_ev_loop m st mlen pc stackpointer returnaddress i))
                (f_ev_prol m st mlen pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 136 p mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22`;;

let ABSORB_CS_MID =
 `\s. read X19 s = st /\ read X20 s = word(mlen MOD 136) /\
      read X21 s = word_add m (word(136 * mlen DIV 136)) /\
      read SP s = word_add stackpointer (word 192) /\
      read (memory :> bytes64 (word_add stackpointer (word 192))) s =
      x19_init /\
      read (memory :> bytes64 (word_add stackpointer (word 200))) s =
      x20_init /\
      read (memory :> bytes64 (word_add stackpointer (word 208))) s =
      x21_init /\
      read (memory :> bytes64 (word_add stackpointer (word 216))) s =
      x22_init /\
      read (memory :> bytes64 (word_add stackpointer (word 224))) s =
      returnaddress /\
      read (memory :> bytes8 (word_add stackpointer (word 255))) s =
      word p /\
      read (memory :> bytes(m,mlen)) s = M /\
      read (memory :> bytes(st,200)) s =
      val(keccak_absorb 136 P (mlen DIV 136))`;;

let ABSORB_CS_INV =
 `\k s. read X19 s = st /\ read X20 s = word(mlen - 136 * k) /\
        read X21 s = word_add m (word(136 * k)) /\
        read SP s = word_add stackpointer (word 192) /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 200))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        returnaddress /\
        read (memory :> bytes8 (word_add stackpointer (word 255))) s =
        word p /\
        read (memory :> bytes(m,mlen)) s = M /\
        read (memory :> bytes(st,200)) s = val(keccak_absorb 136 P k)`;;

(*** A branch on a comparison with a constant, decided by arithmetic ***)

let ABSORB_BRANCH_TAC =
  TRY(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("COND",_),c),_),_))
        when can (term_match [] `read PC s`) l ->
        (SUBGOAL_THEN c (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c)
          (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [SIMPLE_ARITH_TAC; ALL_TAC])
    | _ -> NO_TAC));;

(*** The prologue: zeroing the state and the comparison of mlen with 135 ***)

let ABSORB_CS_PROLOGUE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (1--16) THEN
  ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (17--17) THEN
  ABSORB_BRANCH_TAC;;

let ABSORB_CS_SHORT_TAC =
  ABSORB_CS_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSORB_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV 136`
   `pc + mlk_keccak_absorb_once_loop1`
   `pc + mlk_keccak_absorb_once_loop1_exit`
    ABSORB_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop, with the state zeroed ***)

    ABSORB_CS_PROLOGUE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (18--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body: XOR in a block, permute, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + 136 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `136 * i`; `136`;
                  `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (1--5) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    ABSORB_CS_CALL_TAC "H_XOR"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `136`;
       `keccak_absorb 136 P i`;
       `(M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`;
       `pc:num`; `read X30 s`]
      (ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (7--9) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      ABSORB_CS_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (11--12) THEN
    SUBGOAL_THEN `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                  word(mlen - 136 * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `136 * i + 136 <= mlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `val(word(mlen - 136 * (i + 1)):int64) = mlen - 136 * (i + 1)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (13--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `135 <= x /\ ~(x = 135) <=> 136 <= x`] THEN
    MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `136 * i + 136 <= mlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_XOR_TAC off len data n =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    ABSORB_CS_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len; v; data;
      `pc:num`; `read X30 s`] ABSORB_SAFE_VARS n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSORB_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV 136 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD 136 = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let ABSORB_CS_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `136 * q + t = mlen`));;

let ABSORB_CS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV 136` THEN ABBREV_TAC `t = mlen MOD 136` THEN
  SUBGOAL_THEN `136 * q + t = mlen /\ t < 136` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * 136) =
    M DIV 2 EXP (8 * 136 * q) +
    2 EXP (8 * t) * num_of_bytelist(keccak_pad 136 p mlen)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
    MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
    ASM_SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `0 < 136`];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (1--1) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: p at byte 0 and 128 at byte 135 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (2--8) THEN
    ABSORB_BYTE_FACT_TAC "s8" `p:num` THEN
    ABSORB_CS_XOR_TAC `0` `1` `p:num` 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (10--16) THEN
    ABSORB_BYTE_FACT_TAC "s16" `128` THEN
    SUBGOAL_THEN `135 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `135` `1` `128` 17 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (18--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ABSORB_CS_MLEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136`] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `M DIV 2 EXP (8 * 136 * q) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (136 * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `~(0 = 136 - 1) /\ 136 - 0 - 1 = 135`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
      ABSORB_CS_EVENTS_TAC];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * 136 * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `136 * q + t = mlen`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `136 * q`; `t:num`;
                `s1:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (2--7) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_CS_XOR_TAC `0` `t:num` `M DIV 2 EXP (8 * 136 * q)` 8 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (9--9) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = 135` THENL
   [(*** The padding is just the single byte p + 128 at byte 135 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = 135`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (10--17) THEN
    ABSORB_ORR_BYTE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (18--18) THEN
    ARGS_32_TAC [`135`] THEN
    ABSORB_BYTE_FACT_TAC "s18" `p + 128` THEN
    SUBGOAL_THEN `135 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `135` `1` `p + 128` 19 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (20--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `136 * q + 135 = mlen`)) THEN
      SUBGOAL_THEN `(136 * q + 135) MOD 136 = 135` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN
        REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136`] THEN
      REWRITE_TAC[ARITH_RULE `136 - 1 = 135`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      ABSORB_CS_EVENTS_TAC];

    (*** Otherwise p at byte t and 128 at byte 135 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (10--16) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSORB_BYTE_FACT_TAC "s16" `p:num` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 135 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `t:num` `1` `p:num` 17 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (18--24) THEN
    ABSORB_BYTE_FACT_TAC "s24" `128` THEN
    ABSORB_CS_XOR_TAC `135` `1` `128` 25 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_EXEC (26--29) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ABSORB_CS_MLEN_TAC THEN ABSORB_TAIL_ARITH_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `136 - 1 = 135`] THEN
      SUBGOAL_THEN
       `2 EXP (8 * 135) = 2 EXP (8 * t) * 2 EXP (8 * (136 - t - 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      W(fun (_,w) -> MP_TAC(ISPECL
        [`2 EXP (8 * t) * p`; `128`; `8 * t + 8 * (136 - t - 1)`]
        (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
      REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
       [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
          REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
        REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      ABSORB_CS_EVENTS_TAC]];;


let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e st m mlen p M pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen; word p] s /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb 136
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 136 p mlen))
                    (mlen DIV 136))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 136 p mlen)) DIV
                        2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one. Unlike at -O2, the latter also has the hypothesis       *)
(* p < 128, which holds for all the callers.                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st m mlen p M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ p < 128 /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m; word mlen; word p] s /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 136
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 136 p mlen))
                     (mlen DIV 136))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 136 p mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e st m mlen p pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen; word p] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
