(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding. This is the code for the static function                     *)
(* mlk_keccak_absorb_once_x4 from mlkem-native's portable C implementation   *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), with the      *)
(* first byte 0x1F of the padding as a constant. It works as                 *)
(* mlk_keccak_absorb_once does on one state, with the same control flow in  *)
(* clang, using mlkem_keccakf1600x4_xor_bytes and                            *)
(* mlkem_keccakf1600x4_permute, except that the states are not zeroed first: *)
(* that is done by its callers. The statements are those for gcc 12 -O2;     *)
(* the proof combines that of mlk_keccak_absorb_once in this image (the      *)
(* paths and the four cases of the last block) with the handling of the four *)
(* states of the gcc 12 -O2 proof. It is verified in the whole image (see    *)
(* libmlkem.ml), using the theorems for those functions in the image.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/keccak_absorb_once_proof.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600x4_permute_proof.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600x4_xor_bytes_proof.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlk_keccak_absorb_once_x4:
      +0x0: sub     sp, sp, #0x60
      +0x4: stp     x30, x27, [sp, #16]
      +0x8: stp     x26, x25, [sp, #32]
      +0xc: stp     x24, x23, [sp, #48]
     +0x10: stp     x22, x21, [sp, #64]
     +0x14: stp     x20, x19, [sp, #80]
     +0x18: adrp    x8, <page>
     +0x1c: mov     x19, x6
     +0x20: mov     x22, x5
     +0x24: mov     x23, x4
     +0x28: mov     w21, w1
     +0x2c: mov     x24, x3
     +0x30: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x34: mov     x25, x2
     +0x38: mov     x20, x0
     +0x3c: mov     w9, #0x1f
     +0x40: mov     w27, w1
     +0x44: ldr     x8, [x8]
     +0x48: cmp     x27, x6
     +0x4c: str     x8, [sp, #8]
     +0x50: strb    w9, [sp, #4]
     +0x54: b.hi    join1
     +0x58: mov     x26, xzr
     +0x5c: add     x4, x22, x26
     +0x60: add     x3, x23, x26
     +0x64: add     x2, x24, x26
     +0x68: add     x1, x25, x26
     +0x6c: mov     x0, x20
     +0x70: mov     w5, wzr
     +0x74: mov     w6, w21
     +0x78: bl      mlkem_keccakf1600x4_xor_bytes
     +0x7c: mov     x0, x20
     +0x80: bl      mlkem_keccakf1600x4_permute
     +0x84: sub     x19, x19, x27
     +0x88: add     x26, x26, x27
     +0x8c: cmp     x19, x27
     +0x90: b.cs    loop1
     +0x94: add     x22, x22, x26
     +0x98: add     x23, x23, x26
     +0x9c: add     x24, x24, x26
     +0xa0: add     x25, x25, x26
     +0xa4: cbz     x19, join2
     +0xa8: mov     x0, x20
     +0xac: mov     x1, x25
     +0xb0: mov     x2, x24
     +0xb4: mov     x3, x23
     +0xb8: mov     x4, x22
     +0xbc: mov     w5, wzr
     +0xc0: mov     w6, w19
     +0xc4: bl      mlkem_keccakf1600x4_xor_bytes
     +0xc8: sub     w21, w21, #0x1
     +0xcc: cmp     x19, x21
     +0xd0: b.ne    +0xdc
     +0xd4: mov     w8, #0x9f
     +0xd8: b       join3
     +0xdc: add     x1, sp, #0x4
     +0xe0: add     x2, sp, #0x4
     +0xe4: add     x3, sp, #0x4
     +0xe8: add     x4, sp, #0x4
     +0xec: mov     x0, x20
     +0xf0: mov     w5, w19
     +0xf4: mov     w6, #0x1
     +0xf8: bl      mlkem_keccakf1600x4_xor_bytes
     +0xfc: mov     w8, #0x80
    +0x100: mov     w19, w21
    +0x104: add     x1, sp, #0x4
    +0x108: add     x2, sp, #0x4
    +0x10c: add     x3, sp, #0x4
    +0x110: add     x4, sp, #0x4
    +0x114: mov     x0, x20
    +0x118: mov     w5, w19
    +0x11c: mov     w6, #0x1
    +0x120: strb    w8, [sp, #4]
    +0x124: bl      mlkem_keccakf1600x4_xor_bytes
    +0x128: adrp    x8, <page>
    +0x12c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
    +0x130: ldr     x9, [sp, #8]
    +0x134: ldr     x8, [x8]
    +0x138: cmp     x8, x9
    +0x13c: b.ne    +0x15c
    +0x140: ldp     x20, x19, [sp, #80]
    +0x144: ldp     x22, x21, [sp, #64]
    +0x148: ldp     x24, x23, [sp, #48]
    +0x14c: ldp     x26, x25, [sp, #32]
    +0x150: ldp     x30, x27, [sp, #16]
    +0x154: add     sp, sp, #0x60
    +0x158: ret
    +0x15c: bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlk_keccak_absorb_once_x4"];;

let ABSX4_EXEC = MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The four states zero at the start, as 200 bytes each.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_ZERO_SPLIT = prove
 (`!a:int64 m n s:armstate.
        read (memory :> bytes(a,m + n)) s = 0 <=>
        read (memory :> bytes(a,m)) s = 0 /\
        read (memory :> bytes(word_add a (word m),n)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BYTES800_ZERO = prove
 (`!a:int64 s:armstate.
        read (memory :> bytes(a,800)) s = 0
        ==> read (memory :> bytes(a,200)) s = 0 /\
            read (memory :> bytes(word_add a (word 200),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 400),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 600),200)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `800 = 200 + 600`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `600 = 200 + 400`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, which act on all four states, and for the padding  *)
(* byte on the stack, which is used for all four.                            *)
(* ------------------------------------------------------------------------- *)

let ABSX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let ABSX4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let ABSX4_MBOUND_TAC =
  MAP_EVERY (fun mm ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC])
   [`M0:num`; `M1:num`; `M2:num`; `M3:num`];;

let ABSX4_LASTBLOCK_TAC =
  MAP_EVERY (fun (pp,mm,pn) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
        M DIV 2 EXP (8 * r * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad r 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [pn; "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      ASM_SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `31 < 128`];
      ALL_TAC])
   [`P0:num`,`M0:num`,"P0"; `P1:num`,`M1:num`,"P1";
    `P2:num`,`M2:num`,"P2"; `P3:num`,`M3:num`,"P3"];;

(*** The byte n on the stack, 4 bytes above the stack pointer of the ***)
(*** function, as a 1-byte array                                     ***)

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 228),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(*** The final state of a lane, for the four cases of the last block ***)

let ABSX4_T0_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]];;

(*** t = 0 = r - 1: the single byte 0x9F at byte 0 ***)

let ABSX4_R1_LANE_TAC =
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  COND_CASES_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC];;

let ABSX4_B_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

let ABSX4_C_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (r - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlk_keccak_absorb_once, with the combined theorems of the callees. The    *)
(* stack is the 96 bytes of the function and the 224 used by                 *)
(* mlkem_keccakf1600x4_permute below them.                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let ABSX4_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `r:num`; `mlen:num`; `guard:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ABSX4_SAFE_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,ABSX4_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSX4_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [REWRITE_TAC[VAL_WORD_SUB_EQ_0; ASSUME `val(word r:int64) = r`;
                     ASSUME `val(word mlen:int64) = mlen`] THEN
         (FULL_UNIFY_F_EVENTS_TAC ORELSE
          (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC));
         ALL_TAC])
     else ALL_TAC) THEN
    (ABSORB_MEMACC_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC));;

(*** The events, by the path in the last block (four cases of t and of ***)
(*** t = r - 1, as for mlk_keccak_absorb_once) and before it            ***)

let ABSX4_EVENTS_TERM =
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then (if mlen MOD r = r - 1
              then f_ev_ta m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress
              else f_ev_tb m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress)
        else (if mlen MOD r = r - 1
              then f_ev_tc m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress
              else f_ev_td m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress))
       (if mlen < r
        then f_ev_short m0 m1 m2 m3 st r mlen guard pc stackpointer
                        returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st r mlen guard pc stackpointer
                         returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m0 m1 m2 m3 st r mlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress)))
     :(uarch_event)list`;;

let ABSX4_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC ABSX4_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst ABSX4_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  MAP_EVERY (fun (p,m) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r 0x1F mlen)`))
   [`P0:num`,`M0:num`; `P1:num`,`M1:num`; `P2:num`,`M2:num`;
    `P3:num`,`M3:num`] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27`;;

(*** The frame of 96 bytes below the stack pointer, with the byte of the ***)
(*** padding at sp + 4 and the canary at sp + 8, the stack guard and the ***)
(*** messages, as the part of the invariants                            ***)

let ABSX4_CS_FRAME =
 `read SP s = word_add stackpointer (word 224) /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x19_init /\
  read (memory :> bytes8 (word_add stackpointer (word 228))) s = word 31 /\
  read (memory :> bytes64 (word_add stackpointer (word 232))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes(m0,mlen)) s = M0 /\
  read (memory :> bytes(m1,mlen)) s = M1 /\
  read (memory :> bytes(m2,mlen)) s = M2 /\
  read (memory :> bytes(m3,mlen)) s = M3`;;

let ABSX4_CS_MID = mk_abs(`s:armstate`,list_mk_conj
 [`read X19 s = word(mlen MOD r)`; `read X20 s = st`;
  `read X21 s = word r`;
  `read X22 s = word_add m3 (word(r * mlen DIV r))`;
  `read X23 s = word_add m2 (word(r * mlen DIV r))`;
  `read X24 s = word_add m1 (word(r * mlen DIV r))`;
  `read X25 s = word_add m0 (word(r * mlen DIV r))`;
  `read X27 s = word r`; ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 (mlen DIV r))`]);;

let ABSX4_CS_INV = list_mk_abs([`k:num`; `s:armstate`],list_mk_conj
 [`read X19 s = word(mlen - r * k)`; `read X20 s = st`;
  `read X21 s = word r`; `read X22 s = m3`; `read X23 s = m2`;
  `read X24 s = m1`; `read X25 s = m0`; `read X26 s = word(r * k)`;
  `read X27 s = word r`; ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 k)`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 k)`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 k)`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 k)`]);;

(*** The steps of the start, to the test of mlen against r ***)

let ABSX4_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match []
     `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  ARM_STEPS_TAC ABSX4_EXEC (1--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (8--22) THEN
  ARGS_32_TAC [`r:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN ABSORB_VAL_TAC;;

let ABSX4_CS_SHORT_TAC =
  ABSX4_START_TAC THEN
  SUBGOAL_THEN `mlen <= r /\ ~(r = mlen)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  XOR_BRANCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ABSX4_CS_XOR_TAC off len ms vars n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    ABSX4_SAFE_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read X30 s`]) vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSX4_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
   `pc + mlk_keccak_absorb_once_x4_loop1`
   `pc + mlk_keccak_absorb_once_x4_loop1_exit`
    ABSX4_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** The start, with the four states zero ***)

    ABSX4_START_TAC THEN
    SUBGOAL_THEN `~(mlen <= r /\ ~(r = mlen))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    XOR_BRANCH_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (23--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: XOR in a block of each, permute, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (m,mm) ->
      MP_TAC(SPECL [m; `mlen:num`; mm; `r * i`; `r:num`; `s0:armstate`]
                   READ_MEMORY_BYTES_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC)
     [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
      `m3:int64`,`M3:num`] THEN
    ARM_STEPS_TAC ABSX4_EXEC (1--8) THEN
    ARGS_32_TAC [`r:num`] THEN
    ABSX4_CS_XOR_TAC `0` `r:num`
     [`(M0 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M1 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M2 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M3 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`]
     (ABSX4_SAFE_VARS @ [`i:num`]) 9 THEN
    ARM_STEPS_TAC ABSX4_EXEC (10--11) THEN
    ABSX4_STATES_TAC THEN
    ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
      ABSX4_SAFE_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v0; v1; v2; v3; `pc:num`;
         `read SP s`; `read X30 s`] (ABSX4_SAFE_VARS @ [`i:num`]) 12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC ABSX4_EXEC (13--16) THEN
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
     [REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
      ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
      ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit: the four pointers advanced to the last block ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The last block, from join1: the rest of the messages, if any, and the     *)
(* padding, in the four cases of mlk_keccak_absorb_once: t = 0 = r - 1 (B),  *)
(* t = 0 < r - 1 (A), 0 < t = r - 1 (D) and 0 < t < r - 1 (C).              *)
(* ------------------------------------------------------------------------- *)

let ABSX4_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

(*** The four states with lane, after pre, then the events after evpre, ***)
(*** which decides the test of t = 0 against r - 1 in them if needed     ***)

let ABSX4_CS_LANES_TAC pre lane (evpre:tactic) =
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `mlen:num` &&
                       is_binary "+" (lhs(concl th)))) THEN
    pre THEN lane;
    ALL_TAC]) (1--4) THEN
  evpre THEN ABSX4_CS_EVENTS_TAC;;

(*** The epilogue after the last call at state n: the check of the stack ***)
(*** guard and the return, then the final state                          ***)

let ABSX4_EPILOGUE_TAC n =
  ARM_STEPS_TAC ABSX4_EXEC (n--n) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC ((n+1)--(n+12)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The test of t against r - 1 after the subtraction of 1 from r ***)

let ABSX4_PAD_TEST_TAC =
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

let ABSX4_ZERO_PRE =
  SUBGOAL_THEN
   `!M. M < 2 EXP (8 * (r * q + t)) ==> M DIV 2 EXP (8 * r * q) = 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
    UNDISCH_TAC `M < 2 EXP (8 * (r * q + t))` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC];;

(*** B: r = 1, the byte 0x9F at byte 0 ***)

let ABSX4_TAIL_B =
  ABSX4_PAD_TEST_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (5--15) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_BYTE_FACT_TAC "s15" `159` THEN
  SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABSX4_CS_XOR_TAC `0` `1` [`159`; `159`; `159`; `159`] ABSX4_SAFE_VARS 16 THEN
  ABSX4_EPILOGUE_TAC 17 THEN
  ABSX4_CS_LANES_TAC ABSX4_ZERO_PRE ABSX4_R1_LANE_TAC
   (SUBGOAL_THEN `r - 1 = 0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC]);;

(*** A: t = 0 < r - 1, the byte 0x1F at byte 0 and 0x80 at byte r - 1 ***)

let ABSX4_TAIL_A =
  ABSX4_PAD_TEST_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (5--12) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_BYTE_FACT_TAC "s12" `31` THEN
  SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABSX4_CS_XOR_TAC `0` `1` [`31`; `31`; `31`; `31`] ABSX4_SAFE_VARS 13 THEN
  ARM_STEPS_TAC ABSX4_EXEC (14--24) THEN
  ARGS_32_TAC [`r - 1`] THEN
  ABSX4_BYTE_FACT_TAC "s24" `128` THEN
  SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
    ABSX4_SAFE_VARS 25 THEN
  ABSX4_EPILOGUE_TAC 26 THEN
  ABSX4_CS_LANES_TAC ABSX4_ZERO_PRE ABSX4_T0_LANE_TAC
   (SUBGOAL_THEN `~(0 = r - 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC]);;

(*** D: 0 < t = r - 1, the byte 0x9F at byte t ***)

let ABSX4_TAIL_D =
  ARM_STEPS_TAC ABSX4_EXEC (14--24) THEN
  ARGS_32_TAC [`r - 1`] THEN
  ABSX4_BYTE_FACT_TAC "s24" `159` THEN
  SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABSX4_CS_XOR_TAC `r - 1` `1` [`159`; `159`; `159`; `159`]
    ABSX4_SAFE_VARS 25 THEN
  ABSX4_EPILOGUE_TAC 26 THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> concl th = `t = r - 1`)) THEN
  ABSX4_CS_LANES_TAC
   (SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
     [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
      ALL_TAC])
   ABSX4_B_LANE_TAC ALL_TAC;;

(*** C: 0 < t < r - 1, the byte 0x1F at byte t and 0x80 at byte r - 1 ***)

let ABSX4_TAIL_C =
  ARM_STEPS_TAC ABSX4_EXEC (14--21) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_BYTE_FACT_TAC "s21" `31` THEN
  SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABSX4_CS_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`] ABSX4_SAFE_VARS 22 THEN
  ARM_STEPS_TAC ABSX4_EXEC (23--33) THEN
  ARGS_32_TAC [`r - 1`] THEN
  ABSX4_BYTE_FACT_TAC "s33" `128` THEN
  ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
    ABSX4_SAFE_VARS 34 THEN
  ABSX4_EPILOGUE_TAC 35 THEN
  ABSX4_CS_LANES_TAC
   (SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
      ALL_TAC])
   ABSX4_C_LANE_TAC ALL_TAC;;

let ABSX4_CS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABSORB_VAL_TAC THEN
  ABSX4_MBOUND_TAC THEN ABSX4_LASTBLOCK_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (1--1) THEN
  SUBGOAL_THEN `val(word t:int64) = t`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_BRANCH_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (2--4) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_TAIL_B; ABSX4_TAIL_A];
    XOR_BRANCH_TAC THEN
    SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (m,mm) ->
      SUBGOAL_THEN
       (subst [mm,`M:num`] `M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`)
      ASSUME_TAC THENL
       [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
        REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
        FIRST_ASSUM(SUBST1_TAC o
          check (fun th -> concl th = `r * q + t = mlen`)) THEN
        FIRST_X_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
          `M < 2 EXP (8 * mlen)` then ACCEPT_TAC th else NO_TAC);
        ALL_TAC] THEN
      MP_TAC(SPECL [m; `mlen:num`; mm; `r * q`; `t:num`; `s1:armstate`]
                   READ_MEMORY_BYTES_SUB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC)
     [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
      `m3:int64`,`M3:num`] THEN
    ARM_STEPS_TAC ABSX4_EXEC (2--9) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_CS_XOR_TAC `0` `t:num`
     [`M0 DIV 2 EXP (8 * r * q)`; `M1 DIV 2 EXP (8 * r * q)`;
      `M2 DIV 2 EXP (8 * r * q)`; `M3 DIV 2 EXP (8 * r * q)`]
     ABSX4_SAFE_VARS 10 THEN
    ARM_STEPS_TAC ABSX4_EXEC (11--13) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_PAD_TEST_TAC THEN ABSX4_TAIL_D;
      ABSX4_PAD_TEST_TAC THEN ABSX4_TAIL_C]];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. The four     *)
(* states must be zero at the start, and each is then as for                 *)
(* mlk_keccak_absorb_once on the corresponding message, with the first byte  *)
(* 0x1F of the padding, as for SHAKE. The theorem of correctness is derived  *)
(* from this one.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
            returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 320),320]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
         word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(st,800)) s = 0 /\
                 read (memory :> bytes(m0,mlen)) s = M0 /\
                 read (memory :> bytes(m1,mlen)) s = M1 /\
                 read (memory :> bytes(m2,mlen)) s = M2 /\
                 read (memory :> bytes(m3,mlen)) s = M3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb r
                    (M0 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r 0x1F mlen))
                    (mlen DIV r))
                  (word((M0 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 word_xor
                  (keccak_absorb r
                    (M1 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r 0x1F mlen))
                    (mlen DIV r))
                  (word((M1 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 word_xor
                  (keccak_absorb r
                    (M2 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r 0x1F mlen))
                    (mlen DIV r))
                  (word((M2 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 word_xor
                  (keccak_absorb r
                    (M3 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r 0x1F mlen))
                    (mlen DIV r))
                  (word((M3 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st r mlen guard pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`,
  ABSX4_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_keccak_absorb_once_x4_join1` ABSX4_CS_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_CS_SHORT_TAC; ABSX4_CS_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_TAIL_TAC]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
    returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 320),320)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 320),320)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->int64->int64->int64->num->num->int64->num->int64->
      int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m0:int64`; `m1:int64`;
    `m2:int64`; `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`;
    `M3:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. It does not need the states to be  *)
(* zero at the start, so it is not derived from the combined theorem, but    *)
(* it follows the same paths with the same events, using the theorems of    *)
(* constant time and memory safety of the callees.                           *)
(* ------------------------------------------------------------------------- *)

let ABSX4_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC ABSX4_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst ABSX4_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27`;;

(*** The frame without the messages and the byte of the padding ***)

let ABSX4_SAFE_FRAME =
 `read SP s = word_add stackpointer (word 224) /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 232))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary`;;

let ABSX4_SAFE_MID = mk_abs(`s:armstate`,list_mk_conj
 [`read X19 s = word(mlen MOD r)`; `read X20 s = st`;
  `read X21 s = word r`;
  `read X22 s = word_add m3 (word(r * mlen DIV r))`;
  `read X23 s = word_add m2 (word(r * mlen DIV r))`;
  `read X24 s = word_add m1 (word(r * mlen DIV r))`;
  `read X25 s = word_add m0 (word(r * mlen DIV r))`;
  `read X27 s = word r`; ABSX4_SAFE_FRAME]);;

let ABSX4_SAFE_INV = list_mk_abs([`k:num`; `s:armstate`],list_mk_conj
 [`read X19 s = word(mlen - r * k)`; `read X20 s = st`;
  `read X21 s = word r`; `read X22 s = m3`; `read X23 s = m2`;
  `read X24 s = m1`; `read X25 s = m0`; `read X26 s = word(r * k)`;
  `read X27 s = word r`; ABSX4_SAFE_FRAME]);;

let ABSX4_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (1--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (8--22) THEN
  ARGS_32_TAC [`r:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN ABSORB_VAL_TAC;;

let ABSX4_SAFE_XOR_TAC off len vars n =
  ABSX4_SAFE_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
     `read X3 s`; `read X4 s`; off; len; `pc:num`; `read X30 s`] vars n;;

let ABSX4_SAFE_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
   `pc + mlk_keccak_absorb_once_x4_loop1`
   `pc + mlk_keccak_absorb_once_x4_loop1_exit`
    ABSX4_SAFE_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    ABSX4_SAFE_START_TAC THEN
    SUBGOAL_THEN `~(mlen <= r /\ ~(r = mlen))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    XOR_BRANCH_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (23--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC ABSX4_EXEC (1--8) THEN
    ARGS_32_TAC [`r:num`] THEN
    ABSX4_SAFE_XOR_TAC `0` `r:num` (ABSX4_SAFE_VARS @ [`i:num`]) 9 THEN
    ARM_STEPS_TAC ABSX4_EXEC (10--11) THEN
    ABSX4_SAFE_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] (ABSX4_SAFE_VARS @ [`i:num`]) 12 THEN
    ARM_STEPS_TAC ABSX4_EXEC (13--16) THEN
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
     [REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSX4_SAFE_SHORT_TAC =
  ABSX4_SAFE_START_TAC THEN
  SUBGOAL_THEN `mlen <= r /\ ~(r = mlen)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  XOR_BRANCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ABSX4_SAFE_END_TAC n (evpre:tactic) =
  ARM_STEPS_TAC ABSX4_EXEC (n--n) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC ((n+1)--(n+12)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  evpre THEN ABSX4_CS_EVENTS_TAC;;

let ABSX4_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABSORB_VAL_TAC THEN
  ARM_STEPS_TAC ABSX4_EXEC (1--1) THEN
  SUBGOAL_THEN `val(word t:int64) = t`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_BRANCH_TAC THEN
    ARM_STEPS_TAC ABSX4_EXEC (2--4) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_PAD_TEST_TAC THEN
      ARM_STEPS_TAC ABSX4_EXEC (5--15) THEN
      ARGS_32_TAC [`t:num`] THEN
      SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ABSX4_SAFE_XOR_TAC `0` `1` ABSX4_SAFE_VARS 16 THEN
      ABSX4_SAFE_END_TAC 17
       (SUBGOAL_THEN `r - 1 = 0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; ALL_TAC]);
      ABSX4_PAD_TEST_TAC THEN
      ARM_STEPS_TAC ABSX4_EXEC (5--12) THEN
      ARGS_32_TAC [`t:num`] THEN
      SUBGOAL_THEN `0 + 1 <= 200` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ABSX4_SAFE_XOR_TAC `0` `1` ABSX4_SAFE_VARS 13 THEN
      ARM_STEPS_TAC ABSX4_EXEC (14--24) THEN
      ARGS_32_TAC [`r - 1`] THEN
      SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 25 THEN
      ABSX4_SAFE_END_TAC 26
       (SUBGOAL_THEN `~(0 = r - 1)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; ALL_TAC])];
    XOR_BRANCH_TAC THEN
    SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC ABSX4_EXEC (2--9) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_SAFE_XOR_TAC `0` `t:num` ABSX4_SAFE_VARS 10 THEN
    ARM_STEPS_TAC ABSX4_EXEC (11--13) THEN
    ASM_CASES_TAC `t = r - 1` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_PAD_TEST_TAC THEN
      ARM_STEPS_TAC ABSX4_EXEC (14--24) THEN
      ARGS_32_TAC [`r - 1`] THEN
      SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 25 THEN
      ABSX4_SAFE_END_TAC 26 ALL_TAC;
      ABSX4_PAD_TEST_TAC THEN
      ARM_STEPS_TAC ABSX4_EXEC (14--21) THEN
      ARGS_32_TAC [`t:num`] THEN
      SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 22 THEN
      ARM_STEPS_TAC ABSX4_EXEC (23--33) THEN
      ARGS_32_TAC [`r - 1`] THEN
      ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 34 THEN
      ABSX4_SAFE_END_TAC 35 ALL_TAC]];;

let ABSX4_SAFE_MAIN_TAC =
  ABSX4_SAFE_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_keccak_absorb_once_x4_join1` ABSX4_SAFE_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_SAFE_SHORT_TAC; ABSX4_SAFE_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_SAFE_TAIL_TAC];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e st r m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 320),320]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
         word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st r mlen guard pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`,
  ABSX4_SAFE_MAIN_TAC);;
