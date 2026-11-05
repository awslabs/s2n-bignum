(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-512. This is the code for mlkem_sha3_512 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack, permutes it and extracts the 64 bytes of the hash, and then zeroes *)
(* the state. At -O2 the absorption is a call of mlk_keccak_absorb_once, but *)
(* at -O3 gcc has inlined that code, with the rate r = 72 of SHA3-512 and    *)
(* the first byte 0x06 of its padding, as for mlkem_shake128_absorb_once.    *)
(* It is verified in the whole image (see libmlkem.ml), using the theorems   *)
(* for mlkem_keccakf1600_xor_bytes, mlkem_keccakf1600_permute and            *)
(* mlkem_keccakf1600_extract_bytes in the image, and the lemmas and tactics  *)
(* for mlk_keccak_absorb_once. The result is sha3_512 of common/fips202.ml.  *)
(* The specifications are those for -O2, with the stack of 496 bytes, of     *)
(* which the code uses the 272 of its own frame and the 192 of the           *)
(* permutation below them.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/keccak_absorb_once.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_extract_bytes.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_512:
       +0x0: movi    v0.4s, #0x0
       +0x4: stp     x19, x20, [sp, #-272]!
       +0x8: mov     x20, x2
       +0xc: adrp    x3, <page>
      +0x10: ldr     x3, [x3, #4088]  // got_stack_chk_guard
      +0x14: add     x19, sp, #0x40
      +0x18: stp     x21, x22, [sp, #16]
      +0x1c: mov     x22, x0
      +0x20: mov     x21, x1
      +0x24: stp     x23, x30, [sp, #32]
      +0x28: ldr     x2, [x3]
      +0x2c: str     x2, [sp, #264]
      +0x30: mov     x2, #0x0
      +0x34: stp     q0, q0, [x19]
      +0x38: mov     w2, #0x6
      +0x3c: stp     q0, q0, [x19, #32]
      +0x40: strb    w2, [sp, #63]
      +0x44: stp     q0, q0, [x19, #64]
      +0x48: stp     q0, q0, [x19, #96]
      +0x4c: stp     q0, q0, [x19, #128]
      +0x50: stp     q0, q0, [x19, #160]
      +0x54: str     xzr, [x19, #192]
      +0x58: cmp     x20, #0x47
      +0x5c: b.ls    <mlkem_sha3_512+0x8c>
      +0x60: mov     x1, x21
      +0x64: mov     w3, #0x48
      +0x68: mov     w2, #0x0
      +0x6c: mov     x0, x19
      +0x70: bl      <mlkem_keccakf1600_xor_bytes>
      +0x74: sub     x20, x20, #0x48
      +0x78: mov     x0, x19
      +0x7c: bl      <mlkem_keccakf1600_permute>
      +0x80: add     x21, x21, #0x48
      +0x84: cmp     x20, #0x47
      +0x88: b.hi    <mlkem_sha3_512+0x60>
      +0x8c: mov     w23, w20
      +0x90: cbnz    x20, <mlkem_sha3_512+0x130>
      +0x94: add     x20, sp, #0x3f
      +0x98: mov     w2, w23
      +0x9c: mov     x1, x20
      +0xa0: mov     x0, x19
      +0xa4: mov     w3, #0x1
      +0xa8: bl      <mlkem_keccakf1600_xor_bytes>
      +0xac: mov     w4, #0xffffff80
      +0xb0: mov     x1, x20
      +0xb4: mov     x0, x19
      +0xb8: mov     w3, #0x1
      +0xbc: mov     w2, #0x47
      +0xc0: strb    w4, [sp, #63]
      +0xc4: bl      <mlkem_keccakf1600_xor_bytes>
      +0xc8: mov     x0, x19
      +0xcc: bl      <mlkem_keccakf1600_permute>
      +0xd0: mov     x1, x22
      +0xd4: mov     x0, x19
      +0xd8: mov     w3, #0x40
      +0xdc: mov     w2, #0x0
      +0xe0: bl      <mlkem_keccakf1600_extract_bytes>
      +0xe4: str     xzr, [x19, #192]
      +0xe8: movi    v0.4s, #0x0
      +0xec: stp     q0, q0, [x19]
      +0xf0: stp     q0, q0, [x19, #32]
      +0xf4: stp     q0, q0, [x19, #64]
      +0xf8: stp     q0, q0, [x19, #96]
      +0xfc: stp     q0, q0, [x19, #128]
     +0x100: stp     q0, q0, [x19, #160]
     +0x104: adrp    x0, <page>
     +0x108: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x10c: ldr     x2, [sp, #264]
     +0x110: ldr     x1, [x0]
     +0x114: subs    x2, x2, x1
     +0x118: mov     x1, #0x0
     +0x11c: b.ne    <mlkem_sha3_512+0x170>
     +0x120: ldp     x21, x22, [sp, #16]
     +0x124: ldp     x23, x30, [sp, #32]
     +0x128: ldp     x19, x20, [sp], #272
     +0x12c: ret
     +0x130: mov     x1, x21
     +0x134: mov     w3, w20
     +0x138: mov     x0, x19
     +0x13c: mov     w2, #0x0
     +0x140: bl      <mlkem_keccakf1600_xor_bytes>
     +0x144: cmp     x20, #0x47
     +0x148: b.ne    <mlkem_sha3_512+0x94>
     +0x14c: ldrb    w4, [sp, #63]
     +0x150: mov     w2, w20
     +0x154: add     x1, sp, #0x3f
     +0x158: mov     x0, x19
     +0x15c: orr     w4, w4, #0xffffff80
     +0x160: mov     w3, #0x1
     +0x164: strb    w4, [sp, #63]
     +0x168: bl      <mlkem_keccakf1600_xor_bytes>
     +0x16c: b       <mlkem_sha3_512+0xc8>
     +0x170: bl      <__stack_chk_fail@plt>
     +0x174: nop
     +0x178: nop
     +0x17c: nop
 ***)

let MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_sha3_512"];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the hash *)
(* of the public key in the key generation, whose result the K-PKE key       *)
(* generation needs with its events. The absorption is as for                *)
(* mlk_keccak_absorb_once with r = 72 and p = 0x06, into the state at byte   *)
(* 64 of the frame, until join3, where the state is that after absorbing     *)
(* with the last block XORed in, as in keccak_sponge in common/fips202.ml;   *)
(* after it, the code permutes the state, extracts the hash, zeroes the      *)
(* state and checks the stack guard. The theorems of correctness and of      *)
(* constant time and memory safety are derived from this one.                *)
(* ------------------------------------------------------------------------- *)

let S512_ST = `word_add (stackpointer:int64) (word 288)`;;

let S512_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `inlen DIV 72 = q` || c = `inlen MOD 72 = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

let S512_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  S512_UNABBREV_TAC THEN
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

let S512_SAFE_VARS =
  [`pc:num`; `m:int64`; `out:int64`; `inlen:num`; `guard:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let S512_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (out:int64) (inlen:num) (guard:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_fin m out inlen guard pc stackpointer returnaddress)
      (APPEND
       (if inlen MOD 72 = 0
        then f_ev_t0 m out inlen guard pc stackpointer returnaddress
        else if inlen MOD 72 = 71
        then f_ev_t1 m out inlen guard pc stackpointer returnaddress
        else f_ev_t2 m out inlen guard pc stackpointer returnaddress)
       (if inlen < 72
        then f_ev_short m out inlen guard pc stackpointer returnaddress
        else APPEND (f_ev_epil m out inlen guard pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (inlen DIV 72)
                  (\i. f_ev_loop m out inlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m out inlen guard pc stackpointer returnaddress))))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  SUBGOAL_THEN `496 + inlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping (word_add stackpointer (word 288):int64,200) (m,inlen)`
  ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ABBREV_TAC `M = num_of_bytelist(inp:byte list)` THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad 72 6 inlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

let S512_FRAME =
 "read X22 s = out /\\
  read SP s = word_add stackpointer (word 224) /\\
  read (memory :> bytes64 (word_add stackpointer (word 224))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 232))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 488))) s = canary /\\
  read (memory :> bytes64
         (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64 guard) s = canary";;

let S512_MID1 = parse_term
 ("\\s. read X19 s = word_add stackpointer (word 288) /\\
       read X20 s = word(inlen MOD 72) /\\
       read X21 s = word_add m (word(72 * inlen DIV 72)) /\\ " ^
  S512_FRAME ^ " /\\
       read (memory :> bytes8 (word_add stackpointer (word 287))) s =
       word 6 /\\
       read (memory :> bytes(m,inlen)) s = M /\\
       read (memory :> bytes(word_add stackpointer (word 288),200)) s =
       val(keccak_absorb 72 P (inlen DIV 72))");;

let S512_INV = parse_term
 ("\\k s. read X19 s = word_add stackpointer (word 288) /\\
         read X20 s = word(inlen - 72 * k) /\\
         read X21 s = word_add m (word(72 * k)) /\\ " ^
  S512_FRAME ^ " /\\
         read (memory :> bytes8 (word_add stackpointer (word 287))) s =
         word 6 /\\
         read (memory :> bytes(m,inlen)) s = M /\\
         read (memory :> bytes(word_add stackpointer (word 288),200)) s =
         val(keccak_absorb 72 P k)");;

let S512_MID3 = parse_term
 ("\\s. read X19 s = word_add stackpointer (word 288) /\\ " ^
  S512_FRAME ^ " /\\
       read (memory :> bytes(word_add stackpointer (word 288),200)) s =
       val(word_xor (keccak_absorb 72 P (inlen DIV 72))
                    (word((P DIV 2 EXP (8 * 72 * inlen DIV 72)) MOD
                          2 EXP (8 * 72))))");;

(*** The prologue: the stack guard, zeroing the state, and the ***)
(*** comparison of inlen with 71                                ***)

let S512_PROLOGUE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (5--23) THEN
  SUBGOAL_THEN `val(word inlen:int64) = inlen`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (24--24) THEN
  ABSORB_BRANCH_TAC;;

let S512_SHORT_TAC =
  S512_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let S512_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [S512_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let S512_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `inlen DIV 72`
   `pc + mlkem_sha3_512_loop1`
   `pc + mlkem_sha3_512_loop1_exit`
    S512_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop, with the state zeroed ***)

    S512_PROLOGUE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body: XOR in a block, permute, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`inlen:num`; `72`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 72`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + 72 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`m:int64`; `inlen:num`; `M:num`; `72 * i`; `72`;
                  `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (1--5) THEN
    KECCAK_STATE_AT_TAC S512_ST THEN
    S512_CALL_TAC "H_XOR"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `72`;
       `keccak_absorb 72 P i`;
       `(M DIV 2 EXP (8 * 72 * i)) MOD 2 EXP (8 * 72)`;
       `pc:num`; `read X30 s`]
      (S512_SAFE_VARS @ [`i:num`]) 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (7--9) THEN
    KECCAK_STATE_AT_TAC S512_ST THEN
    KECCAK_STATE_THEN S512_ST (fun v ->
      S512_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`]
        (S512_SAFE_VARS @ [`i:num`]) 10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (11--12) THEN
    SUBGOAL_THEN `word_sub (word (inlen - 72 * i)) (word 72):int64 =
                  word(inlen - 72 * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `72 * i + 72 <= inlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `val(word(inlen - 72 * (i + 1)):int64) = inlen - 72 * (i + 1)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (13--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `71 <= x /\ ~(x = 71) <=> 72 <= x`] THEN
    MP_TAC(SPECL [`inlen:num`; `72`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 72`] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `72 * (i + 1) = 72 * i + 72`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `72 * i + 72 <= inlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The byte n at byte 287 of the stack in state sname, as a 1-byte array ***)

let S512_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 287),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let S512_XOR_TAC off len data n =
  KECCAK_STATE_AT_TAC S512_ST THEN
  KECCAK_STATE_THEN S512_ST (fun v ->
    S512_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len; v; data;
      `pc:num`; `read X30 s`] S512_SAFE_VARS n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let S512_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `inlen DIV 72 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `inlen MOD 72 = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let S512_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `72 * q + t = inlen`));;

(*** The rest of the message and the padding, up to join3 ***)

let S512_TAIL_TAC =
  ABBREV_TAC `q = inlen DIV 72` THEN ABBREV_TAC `t = inlen MOD 72` THEN
  SUBGOAL_THEN `72 * q + t = inlen /\ t < 72` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`inlen:num`; `72`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * inlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,inlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P DIV 2 EXP (8 * 72 * q)) MOD 2 EXP (8 * 72) =
    M DIV 2 EXP (8 * 72 * q) +
    2 EXP (8 * t) * num_of_bytelist(keccak_pad 72 6 inlen)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
    MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
    SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (1--1) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: 0x06 at byte 0 and 128 at byte 71 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (2--8) THEN
    S512_BYTE_FACT_TAC "s8" `6` THEN
    S512_XOR_TAC `0` `1` `6` 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (10--16) THEN
    S512_BYTE_FACT_TAC "s16" `128` THEN
    SUBGOAL_THEN `71 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S512_XOR_TAC `71` `1` `128` 17 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [S512_MLEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `M DIV 2 EXP (8 * 72 * q) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (72 * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT; ARITH_RULE `~(72 = 0)`] THEN
      REWRITE_TAC[ARITH_RULE `~(0 = 72 - 1) /\ 72 - 0 - 1 = 71`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
      S512_EVENTS_TAC];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * 72 * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * inlen)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `72 * q + t = inlen`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `inlen:num`; `M:num`; `72 * q`; `t:num`;
                `s1:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (2--7) THEN
  ARGS_32_TAC [`t:num`] THEN
  S512_XOR_TAC `0` `t:num` `M DIV 2 EXP (8 * 72 * q)` 8 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (9--9) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = 71` THENL
   [(*** The padding is just the single byte 0x06 + 128 at byte 71 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = 71`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (10--18) THEN
    S512_BYTE_FACT_TAC "s18" `134` THEN
    SUBGOAL_THEN `71 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S512_XOR_TAC `71` `1` `134` 19 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (20--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `72 * q + 71 = inlen`)) THEN
      SUBGOAL_THEN `(72 * q + 71) MOD 72 = 71` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN
        REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `72 - 1 = 71`; ARITH_RULE `6 + 128 = 134`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      S512_EVENTS_TAC];

    (*** Otherwise 0x06 at byte t and 128 at byte 71 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (10--16) THEN
    ARGS_32_TAC [`t:num`] THEN
    S512_BYTE_FACT_TAC "s16" `6` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 71 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    S512_XOR_TAC `t:num` `1` `6` 17 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (18--24) THEN
    S512_BYTE_FACT_TAC "s24" `128` THEN
    S512_XOR_TAC `71` `1` `128` 25 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [S512_MLEN_TAC THEN
      SUBGOAL_THEN `(72 * q + t) MOD 72 = t` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `72 - 1 = 71`] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      SUBGOAL_THEN
       `2 EXP (8 * 71) = 2 EXP (8 * t) * 2 EXP (8 * (72 - t - 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      W(fun (_,w) -> MP_TAC(ISPECL
        [`2 EXP (8 * t) * 6`; `128`; `8 * t + 8 * (72 - t - 1)`]
        (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
      REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
       [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV;
          REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
        REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      S512_EVENTS_TAC]];;

(*** From join3: the permutation, the extraction of the hash, zeroing ***)
(*** the state, the check of the stack guard and the return          ***)

(*** The events up to join3 as a variable ef, so that they are kept as  ***)
(*** one block when the events of the calls below are matched            ***)

let S512_FRONT_ABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2")
    then NO_TAC else
    let front = rhs c in
    let eq = mk_eq(front,`ef:(uarch_event)list`) in
    SUBST_ALL_TAC th THEN
    ABBREV_TAC (mk_eq(`ef:(uarch_event)list`,front)) THEN
    FIRST_ASSUM(fun ath ->
      if concl ath <> eq then NO_TAC else
      RULE_ASSUM_TAC(fun th' ->
        if concl th' = eq then th' else REWRITE_RULE[ath] th')));;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, with the events made right-associated ***)
(*** before the memory accesses are checked, so that the events of the     ***)
(*** calls and the new events are taken one block at a time down to ef    ***)

let S512_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let S512_FINAL_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  S512_FRONT_ABBREV_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (1--2) THEN
  KECCAK_STATE_AT_TAC S512_ST THEN
  KECCAK_STATE_THEN S512_ST (fun v ->
    S512_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
       `read X30 s`] (S512_SAFE_VARS @ [`ef:(uarch_event)list`]) 3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (4--8) THEN
  KECCAK_STATE_THEN S512_ST (fun v ->
    S512_CALL_TAC "H_EXTRACT"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `64`; v;
       `pc:num`; `read X30 s`]
      (S512_SAFE_VARS @ [`ef:(uarch_event)list`]) 9) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (10--18) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_EXEC (19--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_THEN `LENGTH(inp:byte list) = inlen` (SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[sha3_512] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    MATCH_MP_TAC KECCAK_SPONGE_BYTES THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["P"; "M"] THEN REFL_TAC;
    S512_DISCHARGE_TAC];;


let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e out m (inp:byte list) inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,64; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_sha3_512) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 496),496)])`,
  S512_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_sha3_512_join3` S512_MID3 THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_sha3_512_loop1_exit` S512_MID1 THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `inlen < 72` THEN ASM_REWRITE_TAC[] THENL
       [S512_SHORT_TAC; S512_LOOP_TAC];
      ASM_CASES_TAC `inlen < 72` THEN ASM_REWRITE_TAC[] THEN
      S512_TAIL_TAC];
    S512_FINAL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one. For the latter, the input is the list of bytes read     *)
(* from memory, which has the length inlen.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,64); (m,LENGTH inp); (word_sub stackpointer (word 496),496)] /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 496),496)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_sha3_512) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist(sha3_512 inp))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 496),496)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
    `LENGTH(inp:byte list)`; `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,64; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_sha3_512) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 496),496)])`,
  MP_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `inp:byte list`
   `read (memory :> bytelist(m,inlen)):armstate->byte list` THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  ASM_CASES_TAC `LENGTH(inp:byte list) = inlen` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
      `inlen:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
    SIMP_TAC[];
    REWRITE_TAC[ensures]]);;
