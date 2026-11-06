(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a SHAKE128 state. This is the code for     *)
(* mlkem_shake128_absorb_once from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md). At -O2 it calls *)
(* mlk_keccak_absorb_once with the rate 168 of SHAKE128 and the first byte   *)
(* 0x1F of its padding, but at -O3 gcc has inlined that code, with r = 168   *)
(* and p = 0x1F. So it zeroes the state, XORs in each whole block of 168     *)
(* bytes of the message and permutes the state, and then XORs in the rest of *)
(* the message and the padding, but does not permute the state again. The    *)
(* byte of padding is on its stack, which gcc protects with a stack guard,   *)
(* as for mlkem_sha3_256: so unlike at -O2, the specifications have the GOT  *)
(* entry for the guard as a precondition, and require that neither it nor   *)
(* the guard overlaps the state or the stack. It is verified in the whole    *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem_keccakf1600_xor_bytes and mlkem_keccakf1600_permute in the image,   *)
(* and the lemmas and tactics for mlk_keccak_absorb_once.                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/keccak_absorb_once_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128_absorb_once:
       +0x0: movi    v0.4s, #0x0
       +0x4: stp     x19, x20, [sp, #-64]!
       +0x8: mov     x19, x0
       +0xc: adrp    x0, <page>
      +0x10: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x20, x2
      +0x1c: str     x30, [sp, #32]
      +0x20: mov     w2, #0x1f
      +0x24: mov     x21, x1
      +0x28: ldr     x3, [x0]
      +0x2c: str     x3, [sp, #56]
      +0x30: mov     x3, #0x0
      +0x34: stp     q0, q0, [x19]
      +0x38: stp     q0, q0, [x19, #32]
      +0x3c: strb    w2, [sp, #55]
      +0x40: stp     q0, q0, [x19, #64]
      +0x44: stp     q0, q0, [x19, #96]
      +0x48: stp     q0, q0, [x19, #128]
      +0x4c: stp     q0, q0, [x19, #160]
      +0x50: str     xzr, [x19, #192]
      +0x54: cmp     x20, #0xa7
      +0x58: b.ls    <mlkem_shake128_absorb_once+0x8c>
      +0x5c: nop
      +0x60: mov     x1, x21
      +0x64: mov     w3, #0xa8
      +0x68: mov     w2, #0x0
      +0x6c: mov     x0, x19
      +0x70: bl      <mlkem_keccakf1600_xor_bytes>
      +0x74: sub     x20, x20, #0xa8
      +0x78: mov     x0, x19
      +0x7c: bl      <mlkem_keccakf1600_permute>
      +0x80: add     x21, x21, #0xa8
      +0x84: cmp     x20, #0xa7
      +0x88: b.hi    <mlkem_shake128_absorb_once+0x60>
      +0x8c: mov     w22, w20
      +0x90: cbnz    x20, <mlkem_shake128_absorb_once+0xf4>
      +0x94: add     x20, sp, #0x37
      +0x98: mov     w2, w22
      +0x9c: mov     x1, x20
      +0xa0: mov     x0, x19
      +0xa4: mov     w3, #0x1
      +0xa8: bl      <mlkem_keccakf1600_xor_bytes>
      +0xac: mov     w4, #0xffffff80
      +0xb0: mov     x1, x20
      +0xb4: mov     x0, x19
      +0xb8: mov     w3, #0x1
      +0xbc: mov     w2, #0xa7
      +0xc0: strb    w4, [sp, #55]
      +0xc4: bl      <mlkem_keccakf1600_xor_bytes>
      +0xc8: adrp    x0, <page>
      +0xcc: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xd0: ldr     x2, [sp, #56]
      +0xd4: ldr     x1, [x0]
      +0xd8: subs    x2, x2, x1
      +0xdc: mov     x1, #0x0
      +0xe0: b.ne    <mlkem_shake128_absorb_once+0x134>
      +0xe4: ldp     x21, x22, [sp, #16]
      +0xe8: ldr     x30, [sp, #32]
      +0xec: ldp     x19, x20, [sp], #64
      +0xf0: ret
      +0xf4: mov     x1, x21
      +0xf8: mov     w3, w20
      +0xfc: mov     x0, x19
     +0x100: mov     w2, #0x0
     +0x104: bl      <mlkem_keccakf1600_xor_bytes>
     +0x108: cmp     x20, #0xa7
     +0x10c: b.ne    <mlkem_shake128_absorb_once+0x94>
     +0x110: ldrb    w4, [sp, #55]
     +0x114: mov     w2, w20
     +0x118: mov     x0, x19
     +0x11c: add     x1, sp, #0x37
     +0x120: orr     w4, w4, #0xffffff80
     +0x124: mov     w3, #0x1
     +0x128: strb    w4, [sp, #55]
     +0x12c: bl      <mlkem_keccakf1600_xor_bytes>
     +0x130: b       <mlkem_shake128_absorb_once+0xc8>
     +0x134: bl      <__stack_chk_fail@plt>
     +0x138: nop
     +0x13c: nop
 ***)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_shake128_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlk_keccak_absorb_once with r = 168 and p = 0x1F as in shake128 in        *)
(* common/fips202.ml, and the copy of the stack guard, which is checked at   *)
(* the end. The state is the first 200 bytes of the context. The stack is    *)
(* the 64 bytes of the function and the 192 used by the permutation below    *)
(* them. The theorems of correctness and of constant time and memory safety  *)
(* are derived from this one.                                                *)
(* ------------------------------------------------------------------------- *)

let S128_ABSORB_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV 168 = q` || c = `mlen MOD 168 = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

let S128_ABSORB_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  S128_ABSORB_UNABBREV_TAC THEN
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

let S128_ABSORB_SAFE_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `mlen:num`; `guard:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let S128_ABSORB_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (mlen:num) (guard:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD 168 = 0
        then f_ev_t0 m st mlen guard pc stackpointer returnaddress
        else if mlen MOD 168 = 167
        then f_ev_t1 m st mlen guard pc stackpointer returnaddress
        else f_ev_t2 m st mlen guard pc stackpointer returnaddress)
       (if mlen < 168
        then f_ev_short m st mlen guard pc stackpointer returnaddress
        else APPEND (f_ev_epil m st mlen guard pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV 168)
                  (\i. f_ev_loop m st mlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m st mlen guard pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 168 0x1F mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22`;;

let S128_ABSORB_FRAME =
 "read SP s = word_add stackpointer (word 192) /\\
  read (memory :> bytes64 (word_add stackpointer (word 192))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 200))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 208))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 216))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 224))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = canary /\\
  read (memory :> bytes64
         (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes8 (word_add stackpointer (word 247))) s = word 31 /\\
  read (memory :> bytes(m,mlen)) s = M";;

let S128_ABSORB_MID = parse_term
 ("\\s. read X19 s = st /\\ read X20 s = word(mlen MOD 168) /\\
       read X21 s = word_add m (word(168 * mlen DIV 168)) /\\ " ^
  S128_ABSORB_FRAME ^ " /\\
       read (memory :> bytes(st,200)) s =
       val(keccak_absorb 168 P (mlen DIV 168))");;

let S128_ABSORB_INV = parse_term
 ("\\k s. read X19 s = st /\\ read X20 s = word(mlen - 168 * k) /\\
         read X21 s = word_add m (word(168 * k)) /\\ " ^
  S128_ABSORB_FRAME ^ " /\\
         read (memory :> bytes(st,200)) s = val(keccak_absorb 168 P k)");;

(*** The prologue: the stack guard, zeroing the state, and the ***)
(*** comparison of mlen with 167                                ***)

let S128_ABSORB_PROLOGUE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (5--22) THEN
  ABSORB_VAL_TAC THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (23--23) THEN
  ABSORB_BRANCH_TAC;;

let S128_ABSORB_SHORT_TAC =
  S128_ABSORB_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let S128_ABSORB_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [S128_ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let S128_ABSORB_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV 168`
   `pc + mlkem_shake128_absorb_once_loop1`
   `pc + mlkem_shake128_absorb_once_loop1_exit`
    S128_ABSORB_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop, with the state zeroed ***)

    S128_ABSORB_PROLOGUE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (24--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body: XOR in a block, permute, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `168`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 168`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + 168 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `168 * i`; `168`;
                  `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (1--5) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    S128_ABSORB_CALL_TAC "H_XOR"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `168`;
       `keccak_absorb 168 P i`;
       `(M DIV 2 EXP (8 * 168 * i)) MOD 2 EXP (8 * 168)`;
       `pc:num`; `read X30 s`]
      (S128_ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (7--9) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      S128_ABSORB_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`]
        (S128_ABSORB_SAFE_VARS @ [`i:num`]) 10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (11--12) THEN
    SUBGOAL_THEN `word_sub (word (mlen - 168 * i)) (word 168):int64 =
                  word(mlen - 168 * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `168 * i + 168 <= mlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `val(word(mlen - 168 * (i + 1)):int64) = mlen - 168 * (i + 1)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (13--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `167 <= x /\ ~(x = 167) <=> 168 <= x`] THEN
    MP_TAC(SPECL [`mlen:num`; `168`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 168`] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `168 * i + 168 <= mlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;


(*** The byte n at byte 55 of the frame in state sname, as a 1-byte array ***)

let S128_ABSORB_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 247),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let S128_ABSORB_XOR_TAC off len data n =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    S128_ABSORB_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len; v; data;
      `pc:num`; `read X30 s`] S128_ABSORB_SAFE_VARS n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let S128_ABSORB_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV 168 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD 168 = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let S128_ABSORB_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `168 * q + t = mlen`));;

(*** The check of the stack guard and the return, from the ADRP at n ***)

let S128_ABSORB_GUARD_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (n--n) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC
   ((n+1)--(n+10)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC;;

let S128_ABSORB_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV 168` THEN ABBREV_TAC `t = mlen MOD 168` THEN
  SUBGOAL_THEN `168 * q + t = mlen /\ t < 168` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `168`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P DIV 2 EXP (8 * 168 * q)) MOD 2 EXP (8 * 168) =
    M DIV 2 EXP (8 * 168 * q) +
    2 EXP (8 * t) * num_of_bytelist(keccak_pad 168 31 mlen)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
    MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
    SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (1--1) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: 0x1F at byte 0 and 128 at byte 167 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (2--8) THEN
    S128_ABSORB_BYTE_FACT_TAC "s8" `31` THEN
    S128_ABSORB_XOR_TAC `0` `1` `31` 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (10--16) THEN
    S128_ABSORB_BYTE_FACT_TAC "s16" `128` THEN
    SUBGOAL_THEN `167 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S128_ABSORB_XOR_TAC `167` `1` `128` 17 THEN
    S128_ABSORB_GUARD_TAC 18 THENL
     [S128_ABSORB_MLEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `M DIV 2 EXP (8 * 168 * q) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (168 * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT; ARITH_RULE `~(168 = 0)`] THEN
      REWRITE_TAC[ARITH_RULE `~(0 = 168 - 1) /\ 168 - 0 - 1 = 167`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
      S128_ABSORB_EVENTS_TAC];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * 168 * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `168 * q + t = mlen`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `168 * q`; `t:num`;
                `s1:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (2--7) THEN
  ARGS_32_TAC [`t:num`] THEN
  S128_ABSORB_XOR_TAC `0` `t:num` `M DIV 2 EXP (8 * 168 * q)` 8 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (9--9) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = 167` THENL
   [(*** The padding is just the single byte 0x1F + 128 at byte 167 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = 167`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (10--18) THEN
    S128_ABSORB_BYTE_FACT_TAC "s18" `159` THEN
    SUBGOAL_THEN `167 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S128_ABSORB_XOR_TAC `167` `1` `159` 19 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (20--20) THEN
    S128_ABSORB_GUARD_TAC 21 THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `168 * q + 167 = mlen`)) THEN
      SUBGOAL_THEN `(168 * q + 167) MOD 168 = 167` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN
        REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 - 1 = 167`; ARITH_RULE `31 + 128 = 159`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      S128_ABSORB_EVENTS_TAC];

    (*** Otherwise 0x1F at byte t and 128 at byte 167 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (10--16) THEN
    ARGS_32_TAC [`t:num`] THEN
    S128_ABSORB_BYTE_FACT_TAC "s16" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 167 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    S128_ABSORB_XOR_TAC `t:num` `1` `31` 17 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_EXEC (18--24) THEN
    S128_ABSORB_BYTE_FACT_TAC "s24" `128` THEN
    S128_ABSORB_XOR_TAC `167` `1` `128` 25 THEN
    S128_ABSORB_GUARD_TAC 26 THENL
     [S128_ABSORB_MLEN_TAC THEN
      SUBGOAL_THEN `(168 * q + t) MOD 168 = t` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 - 1 = 167`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      SUBGOAL_THEN
       `2 EXP (8 * 167) = 2 EXP (8 * t) * 2 EXP (8 * (168 - t - 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      W(fun (_,w) -> MP_TAC(ISPECL
        [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (168 - t - 1)`]
        (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
      REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
       [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV;
          REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
        REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      S128_ABSORB_EVENTS_TAC]];;


let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st m mlen M guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 256),256]
        [word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_shake128_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb 168
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen guard pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  S128_ABSORB_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_shake128_absorb_once_loop1_exit` S128_ABSORB_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < 168` THEN ASM_REWRITE_TAC[] THENL
     [S128_ABSORB_SHORT_TAC; S128_ABSORB_LOOP_TAC];
    ASM_CASES_TAC `mlen < 168` THEN ASM_REWRITE_TAC[] THEN
    S128_ABSORB_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st m mlen M guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 256),256)] /\
        ALLPAIRS nonoverlapping
         [(st,200); (word_sub stackpointer (word 256),256)]
         [(word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_shake128_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 168
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 256),256)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m:int64`; `mlen:num`; `M:num`;
    `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e st m mlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 256),256]
        [word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_shake128_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen guard pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  MP_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `M:num` `read (memory :> bytes(m,mlen))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m:int64`; `mlen:num`; `M:num`;
    `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
