(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from mlkem-       *)
(* native's portable C implementation compiled by gcc 12 with -O2 (see       *)
(* mlkem_native/README.md), which is used by its SHA-3 and SHAKE functions.  *)
(* It zeroes the state, XORs in each whole block of r bytes of the message   *)
(* and permutes the state, and then XORs in the rest of the message and the  *)
(* padding, but does not permute the state again. It is verified in the      *)
(* whole image (see libmlkem.ml), using the theorems                         *)
(* for mlkem_keccakf1600_xor_bytes and mlkem_keccakf1600_permute in the      *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlk_keccak_absorb_once:
        +0x0: movi    v0.4s, #0x0
        +0x4: stp     x19, x20, [sp, #-64]!
        +0x8: mov     x19, x0
        +0xc: stp     x21, x22, [sp, #16]
       +0x10: mov     w22, w1
       +0x14: mov     x20, x3
       +0x18: stp     x23, x30, [sp, #32]
       +0x1c: mov     x21, x2
       +0x20: mov     x23, x22
       +0x24: stp     q0, q0, [x0]
       +0x28: stp     q0, q0, [x0, #32]
       +0x2c: strb    w4, [sp, #63]
       +0x30: stp     q0, q0, [x0, #64]
       +0x34: stp     q0, q0, [x0, #96]
       +0x38: stp     q0, q0, [x0, #128]
       +0x3c: stp     q0, q0, [x0, #160]
       +0x40: str     xzr, [x0, #192]
       +0x44: cmp     x3, x22
       +0x48: b.cc    <mlk_keccak_absorb_once+0x7c>
       +0x4c: nop
       +0x50: mov     x1, x21
       +0x54: mov     w3, w23
       +0x58: mov     w2, #0x0
       +0x5c: mov     x0, x19
       +0x60: bl      <mlkem_keccakf1600_xor_bytes>
       +0x64: sub     x20, x20, x22
       +0x68: mov     x0, x19
       +0x6c: bl      <mlkem_keccakf1600_permute>
       +0x70: add     x21, x21, x22
       +0x74: cmp     x20, x22
       +0x78: b.cs    <mlk_keccak_absorb_once+0x50>
       +0x7c: sub     w23, w23, #0x1
       +0x80: mov     w22, w20
       +0x84: cbnz    x20, <mlk_keccak_absorb_once+0xcc>
       +0x88: add     x20, sp, #0x3f
       +0x8c: mov     w2, w22
       +0x90: mov     x1, x20
       +0x94: mov     x0, x19
       +0x98: mov     w3, #0x1
       +0x9c: bl      <mlkem_keccakf1600_xor_bytes>
       +0xa0: mov     w4, #0xffffff80
       +0xa4: mov     x1, x20
       +0xa8: mov     w2, w23
       +0xac: mov     x0, x19
       +0xb0: mov     w3, #0x1
       +0xb4: strb    w4, [sp, #63]
       +0xb8: bl      <mlkem_keccakf1600_xor_bytes>
       +0xbc: ldp     x21, x22, [sp, #16]
       +0xc0: ldp     x23, x30, [sp, #32]
       +0xc4: ldp     x19, x20, [sp], #64
       +0xc8: ret
       +0xcc: mov     x1, x21
       +0xd0: mov     w3, w20
       +0xd4: mov     x0, x19
       +0xd8: mov     w2, #0x0
       +0xdc: bl      <mlkem_keccakf1600_xor_bytes>
       +0xe0: cmp     x20, w23, uxtw
       +0xe4: b.ne    <mlk_keccak_absorb_once+0x88>
       +0xe8: ldrb    w4, [sp, #63]
       +0xec: mov     w2, w20
       +0xf0: mov     x0, x19
       +0xf4: add     x1, sp, #0x3f
       +0xf8: orr     w4, w4, #0xffffff80
       +0xfc: mov     w3, #0x1
      +0x100: strb    w4, [sp, #63]
      +0x104: bl      <mlkem_keccakf1600_xor_bytes>
      +0x108: ldp     x21, x22, [sp, #16]
      +0x10c: ldp     x23, x30, [sp, #32]
      +0x110: ldp     x19, x20, [sp], #64
      +0x114: ret
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
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

let WORD_ZX_SUB1_SMALL_STMT =
  `!r. 0 < r /\ r < 2 EXP 32
       ==> word_zx (word_sub (word_zx (word r:int64):int32) (word 1)):int64 =
           word(r - 1)`;;

let WORD_ZX_SUB1_SMALL = assume_spec WORD_ZX_SUB1_SMALL_STMT;;

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
(* Tactics for the calls, with the state as bytes between them, and for the  *)
(* arguments and the byte of padding on the stack.                           *)
(* ------------------------------------------------------------------------- *)

let LOCAL_XOR_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

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

(*** A call of mlkem_keccakf1600_xor_bytes on the state at st ***)

let ABSORB_XOR_CALL_TAC off len data k =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    LOCAL_XOR_BYTES_TAC
     [`read X0 s`; `read X1 s`; off; len; v; data; `pc:num`; `read X30 s`]
     k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

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

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st r m mlen p M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        0 < r /\ r <= 200 /\ p < 128 /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
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
                memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on the lengths   *)
(* r and mlen, which are public, and are given in parts: for the last block, *)
(* depending on which of the three cases it is, for a message shorter than   *)
(* a block, and otherwise for the loop over the whole blocks.                *)
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

let ABSORB_SAFE_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `r:num`; `mlen:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

let ABSORB_SAFE_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSORB_SAFE_XOR_TAC off len n =
  ABSORB_SAFE_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len;
     `pc:num`; `read X30 s`] ABSORB_SAFE_VARS n;;

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

let ABSORB_SAFE_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

(*** The last block, the same for a short message and otherwise ***)

let ABSORB_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--2) THEN
  ARGS_32_TAC [`t:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--9) THEN
    ABSORB_SAFE_XOR_TAC `0` `1` 10 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--22) THEN
    ABSORB_SAFE_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--8) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_SAFE_XOR_TAC `0` `t:num` 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (10--10) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--19) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 20 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--24) THEN
    ABSORB_SAFE_FINAL_TAC;
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `t:num` `1` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--25) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 26 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (27--30) THEN
    ABSORB_SAFE_FINAL_TAC];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e st r m mlen p pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, with the     *)
(* facts of the correctness proof and the events of the safety proof in the  *)
(* same intermediate condition and loop invariant, using the combined        *)
(* theorems for the callees. In the last block the equation for mlen in      *)
(* terms of q and t is kept as r * q + t = mlen, so that it does not rewrite *)
(* mlen in the events, and only the goal for the state is rewritten with it. *)
(* ------------------------------------------------------------------------- *)

let ABSORB_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (r:num) (mlen:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m st r mlen pc stackpointer returnaddress
        else f_ev_t2 m st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m st r mlen pc stackpointer returnaddress
        else APPEND (f_ev_epil m st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m st r mlen pc stackpointer returnaddress i))
                (f_ev_prol m st r mlen pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

let ABSORB_CS_MID =
 `\s. read X19 s = st /\ read X20 s = word(mlen MOD r) /\
      read X21 s = word_add m (word(r * mlen DIV r)) /\
      read X23 s = word r /\
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
      x23_init /\
      read (memory :> bytes64 (word_add stackpointer (word 232))) s =
      returnaddress /\
      read (memory :> bytes8 (word_add stackpointer (word 255))) s =
      word p /\
      read (memory :> bytes(m,mlen)) s = M /\
      read (memory :> bytes(st,200)) s =
      val(keccak_absorb r P (mlen DIV r))`;;

let ABSORB_CS_INV =
 `\k s. read X19 s = st /\ read X20 s = word(mlen - r * k) /\
        read X21 s = word_add m (word(r * k)) /\
        read X22 s = word r /\ read X23 s = word r /\
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
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        returnaddress /\
        read (memory :> bytes8 (word_add stackpointer (word 255))) s =
        word p /\
        read (memory :> bytes(m,mlen)) s = M /\
        read (memory :> bytes(st,200)) s = val(keccak_absorb r P k)`;;

let ABSORB_CS_SHORT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
  ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSORB_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_loop1`
   `pc + mlk_keccak_absorb_once_loop1_exit`
    ABSORB_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** Initialization of the loop, with the state zeroed ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
    ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--20) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
    ARGS_32_TAC [`r:num`] THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    ABSORB_CS_CALL_TAC "H_XOR"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `r:num`;
       `keccak_absorb r P i`; `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
       `pc:num`; `read X30 s`]
      (ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (7--9) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      ABSORB_CS_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--12) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--13) THEN
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

let ABSORB_CS_XOR_TAC off len data n =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    ABSORB_CS_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; off; len; v; data;
      `pc:num`; `read X30 s`] ABSORB_SAFE_VARS n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSORB_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let ABSORB_CS_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `r * q + t = mlen`));;

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
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--2) THEN
  ARGS_32_TAC [`t:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: p at byte 0 and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--9) THEN
    ABSORB_BYTE_FACT_TAC "s9" `p:num` THEN
    ABSORB_CS_XOR_TAC `0` `1` `p:num` 10 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s17" `128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `128` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ABSORB_CS_MLEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
      SUBGOAL_THEN `M DIV 2 EXP (8 * r * q) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (r * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
      COND_CASES_TAC THENL
       [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MP_TAC(INST_TYPE [`:1600`,`:N`]
         (SPECL [`p:num`; `1`; `7`] WORD_XOR_DISJOINT_ADD)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
          REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC]];
      ABSORB_CS_EVENTS_TAC];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `r * q + t = mlen`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * q`; `t:num`;
                `s2:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--8) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_CS_XOR_TAC `0` `t:num` `M DIV 2 EXP (8 * r * q)` 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (10--10) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [(*** The padding is just the single byte p + 128 at byte r - 1 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--18) THEN
    ABSORB_ORR_BYTE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--19) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s19" `p + 128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `p + 128` 20 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `r * q + r - 1 = mlen`)) THEN
      SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
       [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      ABSORB_CS_EVENTS_TAC];

    (*** Otherwise p at byte t and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSORB_BYTE_FACT_TAC "s17" `p:num` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `t:num` `1` `p:num` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--25) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s25" `128` THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `128` 26 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (27--30) THEN
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
      ABSORB_CS_EVENTS_TAC]];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e st r m mlen p M pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 256),256]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
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
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
