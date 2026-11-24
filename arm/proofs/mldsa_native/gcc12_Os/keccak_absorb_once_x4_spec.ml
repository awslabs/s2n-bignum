(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding. This is the code for the static function                     *)
(* mld_keccak_absorb_once_x4 from mldsa-native's portable C implementation   *)
(* compiled by gcc 12 with -Os (see mldsa_native/README.md), specialized by  *)
(* the compiler to the first byte 0x1F of the padding. It works as           *)
(* mld_keccak_absorb_once does on one state, using                           *)
(* mldsa_keccakf1600x4_xor_bytes and mldsa_keccakf1600x4_permute, except     *)
(* that the states are not zeroed first: that is done by its callers. It     *)
(* uses a stack frame of 96 bytes and the 240 bytes of the callee            *)
(* mldsa_keccakf1600x4_permute below it. It is verified in the whole image   *)
(* (see libmldsa.ml), using the theorems for those functions in the image.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600x4_xor_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_keccak_absorb_once_x4:
       +0x0: stp     x19, x20, [sp, #-96]!
       +0x4: mov     x20, x0
       +0x8: mov     x19, x6
       +0xc: adrp    x0, <page>
      +0x10: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x22, #0x0
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     w23, w1
      +0x24: mov     x21, x23
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x24, x2
      +0x30: mov     x25, x3
      +0x34: stp     x27, x30, [sp, #64]
      +0x38: mov     x26, x4
      +0x3c: mov     x27, x5
      +0x40: ldr     x1, [x0]
      +0x44: str     x1, [sp, #88]
      +0x48: mov     x1, #0x0
      +0x4c: mov     w0, #0x1f
      +0x50: strb    w0, [sp, #87]
      +0x54: add     x4, x27, x22
      +0x58: add     x3, x26, x22
      +0x5c: add     x2, x25, x22
      +0x60: add     x1, x24, x22
      +0x64: add     x22, x22, x23
      +0x68: cmp     x19, x23
      +0x6c: b.cs    <mld_keccak_absorb_once_x4+0xe4>
      +0x70: mov     w23, w19
      +0x74: sub     w21, w21, #0x1
      +0x78: add     x22, sp, #0x57
      +0x7c: cbz     x19, <mld_keccak_absorb_once_x4+0x104>
      +0x80: mov     w6, w19
      +0x84: mov     x0, x20
      +0x88: mov     w5, #0x0
      +0x8c: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0x90: cmp     x19, w21, uxtw
      +0x94: b.ne    <mld_keccak_absorb_once_x4+0x104>
      +0x98: ldrb    w0, [sp, #87]
      +0x9c: mov     w5, w19
      +0xa0: mov     w6, #0x1
      +0xa4: orr     w0, w0, #0xffffff80
      +0xa8: strb    w0, [sp, #87]
      +0xac: mov     x2, x22
      +0xb0: mov     x1, x22
      +0xb4: mov     x0, x20
      +0xb8: mov     x4, x22
      +0xbc: mov     x3, x22
      +0xc0: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0xc4: adrp    x0, <page>
      +0xc8: ldr     x0, [x0, #4088]  // got_stack_chk_guard            | | | |
      +0xcc: ldr     x2, [sp, #88]
      +0xd0: ldr     x1, [x0]
      +0xd4: subs    x2, x2, x1
      +0xd8: mov     x1, #0x0
      +0xdc: b.eq    <mld_keccak_absorb_once_x4+0x138>
      +0xe0: bl      <__stack_chk_fail@plt>
      +0xe4: mov     w6, w21
      +0xe8: mov     w5, #0x0
      +0xec: mov     x0, x20
      +0xf0: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0xf4: mov     x0, x20
      +0xf8: sub     x19, x19, x23
      +0xfc: bl      <mldsa_keccakf1600x4_permute>
     +0x100: b       <mld_keccak_absorb_once_x4+0x54>
     +0x104: mov     w5, w23
     +0x108: mov     x0, x20
     +0x10c: mov     w6, #0x1
     +0x110: mov     x4, x22
     +0x114: mov     x3, x22
     +0x118: mov     x2, x22
     +0x11c: mov     x1, x22
     +0x120: bl      <mldsa_keccakf1600x4_xor_bytes>
     +0x124: mov     w0, #0xffffff80
     +0x128: mov     w5, w21
     +0x12c: mov     w6, #0x1
     +0x130: strb    w0, [sp, #87]
     +0x134: b       <mld_keccak_absorb_once_x4+0xac>
     +0x138: ldp     x21, x22, [sp, #16]
     +0x13c: ldp     x23, x24, [sp, #32]
     +0x140: ldp     x25, x26, [sp, #48]
     +0x144: ldp     x27, x30, [sp, #64]
     +0x148: ldp     x19, x20, [sp], #96
     +0x14c: ret
 ***)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_keccak_absorb_once_x4"];;

(* ------------------------------------------------------------------------- *)
(* The four states zero at the start, as 200 bytes each.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_ZERO_SPLIT_STMT =
  `!a:int64 m n s:armstate.
        read (memory :> bytes(a,m + n)) s = 0 <=>
        read (memory :> bytes(a,m)) s = 0 /\
        read (memory :> bytes(word_add a (word m),n)) s = 0`;;

let READ_MEMORY_BYTES_ZERO_SPLIT =
  assume_spec READ_MEMORY_BYTES_ZERO_SPLIT_STMT;;

let BYTES800_ZERO_STMT =
  `!a:int64 s:armstate.
        read (memory :> bytes(a,800)) s = 0
        ==> read (memory :> bytes(a,200)) s = 0 /\
            read (memory :> bytes(word_add a (word 200),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 400),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 600),200)) s = 0`;;

let BYTES800_ZERO = assume_spec BYTES800_ZERO_STMT;;

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

let LOCAL_XOR_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_X4_TAC ilist n =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_F1600)
   ilist n;;

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

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 327),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let ABSX4_XOR_CALL_TAC off len ms n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    LOCAL_XOR_X4_TAC
     ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
       off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read SP s`; `read X30 s`]) n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

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
(* Correctness proof. The four states must be zero at the start, and each    *)
(* is then as for mld_keccak_absorb_once on the corresponding message, with  *)
(* the first byte 0x1F of the padding, as for SHAKE. As for                  *)
(* mldsa_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 96 bytes of the function and the 208 used by    *)
(* mldsa_keccakf1600x4_permute below them.                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
    returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 336),336) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 336),336)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_keccak_absorb_once_x4) /\
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
                memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mld_keccak_absorb_once, the *)
(* events for the last block are given in three cases. The test of the       *)
(* message length against the rate at the start is normalized in the events  *)
(* before they are unified with the template.                                *)
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

let ABSX4_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `r:num`; `mlen:num`; `guard:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ABSX4_SAFE_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_Os_mc,
       MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_Os_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSX4_SAFE_XOR_TAC off len vars n =
  ABSX4_SAFE_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
     `read X3 s`; `read X4 s`; off; len; `pc:num`; `read SP s`;
     `read X30 s`] vars n;;

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
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABSX4_SAFE_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

let ABSX4_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (1--3) THEN
  ARGS_32_TAC [`t:num`] THEN ABSORB_VAL_TAC THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (4--12) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 13 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (14--24) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 25 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (26--26) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (27--38) THEN
    ABSX4_SAFE_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (4--8) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_SAFE_XOR_TAC `0` `t:num` ABSX4_SAFE_VARS 9 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (10--10) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (11--22) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 23 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (24--24) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (25--36) THEN
    ABSX4_SAFE_FINAL_TAC;
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (11--19) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 20 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (21--31) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 32 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (33--33) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (34--45) THEN
    ABSX4_SAFE_FINAL_TAC];;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e st r m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       nonoverlapping (st,800) (word_sub stackpointer (word 336),336) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 336),336]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
         word pc,libmldsa_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mldsa_native_libmldsa_gcc12_Os_mc /\
                 read PC s = word (pc + mld_keccak_absorb_once_x4) /\
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
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 336),336;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mld_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 336),336]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mld_keccak_absorb_once.                                                   *)
(* ------------------------------------------------------------------------- *)

let ABSX4_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress
        else f_ev_t2 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress)
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
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC] THEN
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

(*** The facts that hold throughout: the frame, the stack guard and the
     messages, with the byte p = 0x1F on the stack at the offset 87 of the
     frame of the function, which is 240 above the frame of the callees ***)

let ABSX4_CS_FRAME =
 `read SP s = word_add stackpointer (word 240) /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s =
  returnaddress /\
  read (memory :> bytes8 (word_add stackpointer (word 327))) s = word 31 /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes(m0,mlen)) s = M0 /\
  read (memory :> bytes(m1,mlen)) s = M1 /\
  read (memory :> bytes(m2,mlen)) s = M2 /\
  read (memory :> bytes(m3,mlen)) s = M3`;;

(*** At the end of the loop and the start of the last block, pc + 4768: the
     state is [r * q] bytes of each message in, with q = mlen DIV r ***)

let ABSX4_CS_MID = mk_abs(`s:armstate`,list_mk_conj
 [`read X19 s = word(mlen MOD r)`; `read X20 s = st`;
  `read X21 s = word r`; `read X23 s = word r`;
  `read X22 s = word(r * mlen DIV r + r)`;
  `read X24 s = m0`; `read X25 s = m1`; `read X26 s = m2`;
  `read X27 s = m3`;
  `read X1 s = word_add m0 (word(r * mlen DIV r))`;
  `read X2 s = word_add m1 (word(r * mlen DIV r))`;
  `read X3 s = word_add m2 (word(r * mlen DIV r))`;
  `read X4 s = word_add m3 (word(r * mlen DIV r))`;
  ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 (mlen DIV r))`]);;

(*** The loop invariant at pc + 4884, with k blocks done ***)

let ABSX4_CS_INV = list_mk_abs([`k:num`; `s:armstate`],list_mk_conj
 [`read X19 s = word(mlen - r * k)`; `read X20 s = st`;
  `read X21 s = word r`; `read X23 s = word r`;
  `read X22 s = word(r * k + r)`;
  `read X24 s = m0`; `read X25 s = m1`; `read X26 s = m2`;
  `read X27 s = m3`;
  `read X1 s = word_add m0 (word(r * k))`;
  `read X2 s = word_add m1 (word(r * k))`;
  `read X3 s = word_add m2 (word(r * k))`;
  `read X4 s = word_add m3 (word(r * k))`;
  ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 k)`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 k)`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 k)`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 k)`]);;

(*** The same without the facts about the messages and the states, for the
     proof of constant time and memory safety ***)

let ABSX4_SAFE_FRAME =
 `read SP s = word_add stackpointer (word 240) /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s =
  returnaddress /\
  read (memory :> bytes8 (word_add stackpointer (word 327))) s = word 31 /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary`;;

let ABSX4_SAFE_MID = mk_abs(`s:armstate`,list_mk_conj
 [`read X19 s = word(mlen MOD r)`; `read X20 s = st`;
  `read X21 s = word r`; `read X23 s = word r`;
  `read X22 s = word(r * mlen DIV r + r)`;
  `read X24 s = m0`; `read X25 s = m1`; `read X26 s = m2`;
  `read X27 s = m3`;
  `read X1 s = word_add m0 (word(r * mlen DIV r))`;
  `read X2 s = word_add m1 (word(r * mlen DIV r))`;
  `read X3 s = word_add m2 (word(r * mlen DIV r))`;
  `read X4 s = word_add m3 (word(r * mlen DIV r))`;
  ABSX4_SAFE_FRAME]);;

let ABSX4_SAFE_INV = list_mk_abs([`k:num`; `s:armstate`],list_mk_conj
 [`read X19 s = word(mlen - r * k)`; `read X20 s = st`;
  `read X21 s = word r`; `read X23 s = word r`;
  `read X22 s = word(r * k + r)`;
  `read X24 s = m0`; `read X25 s = m1`; `read X26 s = m2`;
  `read X27 s = m3`;
  `read X1 s = word_add m0 (word(r * k))`;
  `read X2 s = word_add m1 (word(r * k))`;
  `read X3 s = word_add m2 (word(r * k))`;
  `read X4 s = word_add m3 (word(r * k))`;
  ABSX4_SAFE_FRAME]);;

let ABSX4_CS_SHORT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match []
     `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (5--21) THEN
  ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (22--27) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (28--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0; ADD_CLAUSES] THEN
  REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let ABSX4_CS_XOR_TAC off len ms vars n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    ABSX4_SAFE_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read SP s`; `read X30 s`]) vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSX4_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
   `pc + 4884` `pc + 4768` ABSX4_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** The start of the function up to the first block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
     (can (term_match []
       `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (1--4) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (5--21) THEN
    ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (22--27) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (28--28) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: XOR in a block of each message and permute ***)

    (X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
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
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (1--4) THEN
    ARGS_32_TAC [`r:num`] THEN
    ABSX4_STATES_TAC THEN
    ABSX4_SAFE_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `r:num`;
      `keccak_absorb r P0 i`; `keccak_absorb r P1 i`;
      `keccak_absorb r P2 i`; `keccak_absorb r P3 i`;
      `(M0 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M1 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M2 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M3 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `pc:num`; `read SP s`; `read X30 s`]
     (ABSX4_SAFE_VARS @ [`i:num`]) 5 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (6--8) THEN
    ABSX4_STATES_TAC THEN
    ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
      ABSX4_SAFE_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v0; v1; v2; v3; `pc:num`;
         `read SP s`; `read X30 s`] (ABSX4_SAFE_VARS @ [`i:num`]) 9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (10--15) THEN
    SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                  word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (16--16) THEN
    SUBGOAL_THEN
     `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
      val(word r:int64) = r`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (17--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`]; ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
      ALL_TAC]) (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
      ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC);

    (*** The end of the loop ***)

    (REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC)];;

let ABSX4_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

let ABSX4_CS_LANES_TAC pre lane =
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `mlen:num` &&
                       is_binary "+" (lhs(concl th)))) THEN
    pre THEN lane;
    ALL_TAC]) (1--4) THEN
  ABSX4_CS_EVENTS_TAC;;


let ABSX4_CS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABSX4_MBOUND_TAC THEN ABSX4_LASTBLOCK_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (1--3) THEN
  ARGS_32_TAC [`t:num`] THEN ABSORB_VAL_TAC THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: p at byte 0 and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (4--12) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_BYTE_FACT_TAC "s12" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`]
      ABSX4_SAFE_VARS 13 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (14--24) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s24" `128` THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
      ABSX4_SAFE_VARS 25 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (26--26) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (27--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN
       `!M. M < 2 EXP (8 * (r * q + t)) ==> M DIV 2 EXP (8 * r * q) = 0`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (r * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC])
     ABSX4_T0_LANE_TAC;
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of each message after its blocks ***)

  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
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
    MP_TAC(SPECL [m; `mlen:num`; mm; `r * q`; `t:num`; `s3:armstate`]
                 READ_MEMORY_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC)
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (4--8) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_CS_XOR_TAC `0` `t:num`
   [`M0 DIV 2 EXP (8 * r * q)`; `M1 DIV 2 EXP (8 * r * q)`;
    `M2 DIV 2 EXP (8 * r * q)`; `M3 DIV 2 EXP (8 * r * q)`]
   ABSX4_SAFE_VARS 9 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC (10--10) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [(*** The padding is just the single byte p + 128 at byte r - 1 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (11--22) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s22" `159` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`159`; `159`; `159`; `159`]
      ABSX4_SAFE_VARS 23 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (24--24) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (25--36) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
       [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
        ALL_TAC])
     ABSX4_B_LANE_TAC;

    (*** Otherwise p at byte t and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (11--19) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_BYTE_FACT_TAC "s19" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`]
      ABSX4_SAFE_VARS 20 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (21--31) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s31" `128` THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
      ABSX4_SAFE_VARS 32 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (33--33) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_EXEC
     (34--45) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
        ALL_TAC])
     ABSX4_C_LANE_TAC];;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
            returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       nonoverlapping (st,800) (word_sub stackpointer (word 336),336) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 336),336]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
         word pc,libmldsa_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mldsa_native_libmldsa_gcc12_Os_mc /\
                 read PC s = word (pc + mld_keccak_absorb_once_x4) /\
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
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 336),336;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mld_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 336),336]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
