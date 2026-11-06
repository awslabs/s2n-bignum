(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE128 states.     *)
(* This is the code for mlkem_shake128x4_absorb_once from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which zeroes the 800 bytes of the context with   *)
(* memset from the C library, called through the PLT of the image, and then  *)
(* absorbs the messages into the four states. At -O2 it calls                *)
(* mlk_keccak_absorb_once_x4 for that, but at -O3 gcc has inlined that code, *)
(* with r = 168 and p = 0x1F: it XORs in each whole block of 168 bytes of    *)
(* each message with mlkem_keccakf1600x4_xor_bytes and permutes the states   *)
(* with mlkem_keccakf1600x4_permute, and then XORs in the rest of each       *)
(* message and the padding, without permuting again. The byte of padding is  *)
(* on its stack, which gcc protects with a stack guard. It is verified in    *)
(* the whole image (see libmlkem.ml), using the theorems for those two       *)
(* functions in the image, the lemmas and tactics for mlk_keccak_absorb_once *)
(* and assuming the contracts for memset in utils/mlkem_native_libc.ml. The  *)
(* theorems have the statements of the -O2 ones, except that the stack used  *)
(* is 288 bytes rather than 304.                                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccak_absorb_once_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600x4_permute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600x4_xor_bytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem_shake128x4_absorb_once:
       +0x0: stp     x19, x20, [sp, #-80]!
       +0x4: mov     x20, x1
       +0x8: mov     x19, x5
       +0xc: adrp    x6, <page>
      +0x10: ldr     x6, [x6, #4088]  // got_stack_chk_guard
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x21, x2
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x22, x3
      +0x24: mov     x23, x4
      +0x28: stp     x25, x30, [sp, #48]
      +0x2c: mov     x24, x0
      +0x30: mov     x2, #0x320
      +0x34: ldr     x1, [x6]
      +0x38: str     x1, [sp, #72]
      +0x3c: mov     x1, #0x0
      +0x40: bl      <memset@plt>
      +0x44: mov     w0, #0x1f
      +0x48: strb    w0, [sp, #71]
      +0x4c: cmp     x19, #0xa7
      +0x50: b.ls    <mlkem_shake128x4_absorb_once+0x9c>
      +0x54: nop
      +0x58: mov     x4, x23
      +0x5c: mov     x3, x22
      +0x60: mov     x2, x21
      +0x64: mov     x1, x20
      +0x68: mov     w6, #0xa8
      +0x6c: mov     w5, #0x0
      +0x70: mov     x0, x24
      +0x74: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0x78: mov     x0, x24
      +0x7c: sub     x19, x19, #0xa8
      +0x80: bl      <mlkem_keccakf1600x4_permute>
      +0x84: add     x23, x23, #0xa8
      +0x88: add     x22, x22, #0xa8
      +0x8c: add     x21, x21, #0xa8
      +0x90: add     x20, x20, #0xa8
      +0x94: cmp     x19, #0xa7
      +0x98: b.hi    <mlkem_shake128x4_absorb_once+0x58>
      +0x9c: mov     w25, w19
      +0xa0: cbnz    x19, <mlkem_shake128x4_absorb_once+0x120>
      +0xa4: add     x19, sp, #0x47
      +0xa8: mov     w5, w25
      +0xac: mov     x4, x19
      +0xb0: mov     x3, x19
      +0xb4: mov     x2, x19
      +0xb8: mov     x1, x19
      +0xbc: mov     x0, x24
      +0xc0: mov     w6, #0x1
      +0xc4: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0xc8: mov     w7, #0xffffff80
      +0xcc: mov     x0, x24
      +0xd0: mov     x4, x19
      +0xd4: mov     x3, x19
      +0xd8: mov     x2, x19
      +0xdc: mov     x1, x19
      +0xe0: mov     w6, #0x1
      +0xe4: mov     w5, #0xa7
      +0xe8: strb    w7, [sp, #71]
      +0xec: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0xf0: adrp    x0, <page>
      +0xf4: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xf8: ldr     x2, [sp, #72]
      +0xfc: ldr     x1, [x0]
     +0x100: subs    x2, x2, x1
     +0x104: mov     x1, #0x0
     +0x108: b.ne    <mlkem_shake128x4_absorb_once+0x178>
     +0x10c: ldp     x21, x22, [sp, #16]
     +0x110: ldp     x23, x24, [sp, #32]
     +0x114: ldp     x25, x30, [sp, #48]
     +0x118: ldp     x19, x20, [sp], #80
     +0x11c: ret
     +0x120: mov     x4, x23
     +0x124: mov     x3, x22
     +0x128: mov     x2, x21
     +0x12c: mov     x1, x20
     +0x130: mov     w6, w19
     +0x134: mov     x0, x24
     +0x138: mov     w5, #0x0
     +0x13c: bl      <mlkem_keccakf1600x4_xor_bytes>
     +0x140: cmp     x19, #0xa7
     +0x144: b.ne    <mlkem_shake128x4_absorb_once+0xa4>
     +0x148: ldrb    w7, [sp, #71]
     +0x14c: add     x4, sp, #0x47
     +0x150: mov     w5, w19
     +0x154: mov     x0, x24
     +0x158: orr     w7, w7, #0xffffff80
     +0x15c: mov     x3, x4
     +0x160: mov     x2, x4
     +0x164: mov     x1, x4
     +0x168: mov     w6, #0x1
     +0x16c: strb    w7, [sp, #71]
     +0x170: bl      <mlkem_keccakf1600x4_xor_bytes>
     +0x174: b       <mlkem_shake128x4_absorb_once+0xf0>
     +0x178: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]  // got_memset
       +0x8: add     x16, x16, #0xfe8  // got_memset
       +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_shake128x4_absorb_once"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Absorbing from a given state rather than from zero, as keccak_absorb in   *)
(* common/fips202.ml does. The code after memset is verified for any initial *)
(* states, so that the same proof serves the theorems for the three          *)
(* contracts of memset: only with the combined and the correctness ones are  *)
(* the states known to be zero after it.                                     *)
(* ------------------------------------------------------------------------- *)

let keccak_absorb_from = define
 `keccak_absorb_from (s0:1600 word) r p 0 = s0 /\
  keccak_absorb_from s0 r p (SUC j) =
    keccak_f1600
     (word_xor (keccak_absorb_from s0 r p j)
               (word((p DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r))))`;;

let KECCAK_ABSORB_FROM_0 = prove
 (`!r p j. keccak_absorb_from (word 0) r p j = keccak_absorb r p j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[keccak_absorb_from; keccak_absorb]);;

(* ------------------------------------------------------------------------- *)
(* The four states zero after memset, as 200 bytes each (as at -O2).         *)
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
(* The code after memset, from after_memset to the return, for any initial   *)
(* states S0 to S3 (the states then are as for keccak_absorb_from), with the *)
(* events (constant time and memory safety). The frame of 80 bytes is set    *)
(* up, with the saved registers and the copy of the stack guard, and the     *)
(* stack below it is the 208 bytes used by mlkem_keccakf1600x4_permute. The  *)
(* events of the last block are given in three cases, as for                 *)
(* mlk_keccak_absorb_once, and so is the first test of mlen.                 *)
(* ------------------------------------------------------------------------- *)

let ABSX4_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `mlen:num`; `guard:int64`; `stackpointer:int64`; `returnaddress:int64`];;

let ABSX4_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV 168 = q` || c = `mlen MOD 168 = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

let ABSX4_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  ABSX4_UNABBREV_TAC THEN
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

let ABSX4_INPS =
  [`m0:int64`,`M0:num`,`P0:num`,`S0:1600 word`;
   `m1:int64`,`M1:num`,`P1:num`,`S1:1600 word`;
   `m2:int64`,`M2:num`,`P2:num`,`S2:1600 word`;
   `m3:int64`,`M3:num`,`P3:num`,`S3:1600 word`];;

(*** The events as in the -O2 template for mlk_keccak_absorb_once_x4: ***)
(*** the last block in three cases, after the test of mlen and the     ***)
(*** loop over the whole blocks                                         ***)

let ABSX4_TEMPLATE =
  let ord = [`m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
             `mlen:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
             `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) ord
                   `:(uarch_event)list` in
  let app n = list_mk_comb(mk_var(n,fty),ord) in
  let lty = itlist (fun a t -> mk_fun_ty (type_of a) t) ord
                   (mk_fun_ty `:num` `:(uarch_event)list`) in
  let loop = mk_abs(`i:num`,
               mk_comb(list_mk_comb(mk_var("f_ev_loop",lty),ord),`i:num`)) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,
                          [`mlen DIV 168`; loop]) in
  let tail = mk_cond(`mlen MOD 168 = 0`,app "f_ev_t0",
               mk_cond(`mlen MOD 168 = 167`,app "f_ev_t1",app "f_ev_t2")) in
  let head = mk_cond(`mlen < 168`,app "f_ev_short",
               list_mk_comb(ap,[app "f_ev_epil";
                 list_mk_comb(ap,[enum; app "f_ev_prol"])])) in
  list_mk_abs(ord,list_mk_comb(ap,[tail; head]));;

let ABSX4_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC ABSX4_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT(W(fun (asl,w) ->
    if name_of(fst(dest_forall w)) = "stackpointer" then NO_TAC
    else GEN_TAC)) THEN
  WORD_FORALL_OFFSET_TAC 208 THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (_,m,p,_) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 168 0x1F mlen)`))
   ABSX4_INPS;;

let ABSX4_FRAME =
 "read SP s = word_add stackpointer (word 208) /\\
  read (memory :> bytes64 (word_add stackpointer (word 208))) s = x19 /\\
  read (memory :> bytes64 (word_add stackpointer (word 216))) s = x20 /\\
  read (memory :> bytes64 (word_add stackpointer (word 224))) s = x21 /\\
  read (memory :> bytes64 (word_add stackpointer (word 232))) s = x22 /\\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s = x23 /\\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x24 /\\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x25 /\\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = canary /\\
  read (memory :> bytes64
         (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes8 (word_add stackpointer (word 279))) s = word 31 /\\
  read (memory :> bytes(m0,mlen)) s = M0 /\\
  read (memory :> bytes(m1,mlen)) s = M1 /\\
  read (memory :> bytes(m2,mlen)) s = M2 /\\
  read (memory :> bytes(m3,mlen)) s = M3";;

let ABSX4_STATES k =
 "read (memory :> bytes(st,200)) s =
  val(keccak_absorb_from S0 168 P0 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 200),200)) s =
  val(keccak_absorb_from S1 168 P1 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 400),200)) s =
  val(keccak_absorb_from S2 168 P2 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 600),200)) s =
  val(keccak_absorb_from S3 168 P3 " ^ k ^ ")";;

let ABSX4_MID = parse_term
 ("\\s. read X19 s = word(mlen MOD 168) /\\
       read X20 s = word_add m0 (word(168 * mlen DIV 168)) /\\
       read X21 s = word_add m1 (word(168 * mlen DIV 168)) /\\
       read X22 s = word_add m2 (word(168 * mlen DIV 168)) /\\
       read X23 s = word_add m3 (word(168 * mlen DIV 168)) /\\
       read X24 s = st /\\ " ^
  ABSX4_FRAME ^ " /\\ " ^ ABSX4_STATES "(mlen DIV 168)");;

let ABSX4_INV = parse_term
 ("\\k s. read X19 s = word(mlen - 168 * k) /\\
         read X20 s = word_add m0 (word(168 * k)) /\\
         read X21 s = word_add m1 (word(168 * k)) /\\
         read X22 s = word_add m2 (word(168 * k)) /\\
         read X23 s = word_add m3 (word(168 * k)) /\\
         read X24 s = st /\\ " ^
  ABSX4_FRAME ^ " /\\ " ^ ABSX4_STATES "k");;

let ABSX4_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [ABSX4_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSX4_XOR_TAC off len data vars n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    ABSX4_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; off; len; v0; v1; v2; v3] @ data @
      [`pc:num`; `read SP s`; `read X30 s`]) vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSX4_PERMUTE_TAC vars n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    ABSX4_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; v0; v1; v2; v3; `pc:num`;
      `read SP s`; `read X30 s`] vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(*** The start: the byte of padding and the comparison of mlen with 167 ***)

let ABSX4_PROLOGUE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (1--3) THEN
  ABSORB_VAL_TAC THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (4--4) THEN
  ABSORB_BRANCH_TAC;;

let ABSX4_SHORT_TAC =
  ABSX4_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb_from] THEN ABSORB_DISCHARGE_TAC;;

let ABSX4_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV 168`
   `pc + mlkem_shake128x4_absorb_once_loop1`
   `pc + mlkem_shake128x4_absorb_once_loop1_exit`
    ABSX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop ***)

    ABSX4_PROLOGUE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (5--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; keccak_absorb_from] THEN
    ABSORB_DISCHARGE_TAC;

    (*** The loop body: XOR in a block of each, permute, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `168`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 168`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + 168 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (m,mm,_,_) ->
      MP_TAC(SPECL [m; `mlen:num`; mm; `168 * i`; `168`; `s0:armstate`]
                   READ_MEMORY_BYTES_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) ABSX4_INPS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (1--8) THEN
    ABSX4_XOR_TAC `0` `168`
     (map (fun (_,mm,_,_) ->
        subst [mm,`M:num`] `(M DIV 2 EXP (8 * 168 * i)) MOD 2 EXP (8 * 168)`)
      ABSX4_INPS)
     (ABSX4_SAFE_VARS @ [`i:num`]) 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (10--12) THEN
    ABSX4_PERMUTE_TAC (ABSX4_SAFE_VARS @ [`i:num`]) 13 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (14--18) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (19--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `167 <= x /\ ~(x = 167) <=> 168 <= x`] THEN
    MP_TAC(SPECL [`mlen:num`; `168`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 168`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(AP_TERM_TAC THEN
        REWRITE_TAC[GSYM ADD1; keccak_absorb_from] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[MULT_CLAUSES; EXP] THEN
        MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
        CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
        MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
        UNDISCH_TAC `168 * i + 168 <= mlen` THEN ARITH_TAC) THEN
    ABSORB_DISCHARGE_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    ABSORB_DISCHARGE_TAC];;

(*** The bounds of the messages, and their last blocks with the padding ***)

let ABSX4_MBOUND_TAC =
  MAP_EVERY (fun (_,mm,_,_) ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC]) ABSX4_INPS;;

let ABSX4_LASTBLOCK_TAC =
  MAP_EVERY (fun (_,mm,pp,_) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * 168 * q)) MOD 2 EXP (8 * 168) =
        M DIV 2 EXP (8 * 168 * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad 168 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [fst(dest_var pp); "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]) ABSX4_INPS;;

(*** The byte n at byte 71 of the frame in state sname, as a 1-byte array ***)

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 279),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let ABSX4_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV 168 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD 168 = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let ABSX4_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `168 * q + t = mlen`));;

(*** The check of the stack guard and the return, from the ADRP at n ***)

let ABSX4_GUARD_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (n--n) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
   ((n+1)--(n+11)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The four states, from the tactic for one lane, and the events ***)

let ABSX4_LANES_TAC lane =
  REPEAT CONJ_TAC THENL
   (map (fun (_,mm,_,_) -> lane mm) ABSX4_INPS @ [ABSX4_EVENTS_TAC]);;

(*** A whole number of blocks: 0x1F at byte 0 and 128 at byte 167 ***)

let ABSX4_T0_LANE_TAC mm =
  ABSX4_MLEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN (subst [mm,`M:num`] `M DIV 2 EXP (8 * 168 * q) = 0`)
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    UNDISCH_TAC (subst [mm,`M:num`] `M < 2 EXP (8 * (168 * q + t))`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT; ARITH_RULE `~(168 = 0)`] THEN
  REWRITE_TAC[ARITH_RULE `~(0 = 168 - 1) /\ 168 - 0 - 1 = 167`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
  TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[LE_EXP] THEN ARITH_TAC];;

(*** The padding is just the single byte 0x1F + 128 at byte 167 ***)

let ABSX4_T1_LANE_TAC mm =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `168 * q + 167 = mlen`)) THEN
  SUBGOAL_THEN `(168 * q + 167) MOD 168 = 167` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 168 /\ 31 < 128`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `168 - 1 = 167`; ARITH_RULE `31 + 128 = 159`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(*** Otherwise 0x1F at byte t and 128 at byte 167 ***)

let ABSX4_T2_LANE_TAC mm =
  ABSX4_MLEN_TAC THEN
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
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

let ABSX4_REP4 t = [t; t; t; t];;

let ABSX4_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV 168` THEN ABBREV_TAC `t = mlen MOD 168` THEN
  SUBGOAL_THEN `168 * q + t = mlen /\ t < 168` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `168`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABSX4_MBOUND_TAC THEN ABSX4_LASTBLOCK_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (1--1) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (2--11) THEN
    ABSX4_BYTE_FACT_TAC "s11" `31` THEN
    ABSX4_XOR_TAC `0` `1` (ABSX4_REP4 `31`) ABSX4_SAFE_VARS 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (13--22) THEN
    ABSX4_BYTE_FACT_TAC "s22" `128` THEN
    SUBGOAL_THEN `167 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ABSX4_XOR_TAC `167` `1` (ABSX4_REP4 `128`) ABSX4_SAFE_VARS 23 THEN
    ABSX4_GUARD_TAC 24 THEN ABSX4_LANES_TAC ABSX4_T0_LANE_TAC;
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of each message after the blocks ***)

  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,mm,_,_) ->
    SUBGOAL_THEN
     (subst [mm,`M:num`] `M DIV 2 EXP (8 * 168 * q) < 2 EXP (8 * t)`)
    ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      FIRST_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
        `M < 2 EXP (8 * mlen)` then MP_TAC th else NO_TAC) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `168 * q + t = mlen`)) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [m; `mlen:num`; mm; `168 * q`; `t:num`; `s1:armstate`]
                 READ_MEMORY_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC) ABSX4_INPS THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (2--10) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_XOR_TAC `0` `t:num`
   (map (fun (_,mm,_,_) -> subst [mm,`M:num`] `M DIV 2 EXP (8 * 168 * q)`)
        ABSX4_INPS)
   ABSX4_SAFE_VARS 11 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (12--12) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = 167` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = 167`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (13--24) THEN
    ABSX4_BYTE_FACT_TAC "s24" `159` THEN
    SUBGOAL_THEN `167 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ABSX4_XOR_TAC `167` `1` (ABSX4_REP4 `159`) ABSX4_SAFE_VARS 25 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (26--26) THEN
    ABSX4_GUARD_TAC 27 THEN ABSX4_LANES_TAC ABSX4_T1_LANE_TAC;

    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (13--22) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_BYTE_FACT_TAC "s22" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 167 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_XOR_TAC `t:num` `1` (ABSX4_REP4 `31`) ABSX4_SAFE_VARS 23 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
     (24--33) THEN
    ABSX4_BYTE_FACT_TAC "s33" `128` THEN
    ABSX4_XOR_TAC `167` `1` (ABSX4_REP4 `128`) ABSX4_SAFE_VARS 34 THEN
    ABSX4_GUARD_TAC 35 THEN ABSX4_LANES_TAC ABSX4_T2_LANE_TAC];;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_BODY = prove
 (`exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 S0 S1 S2 S3 guard canary
            x19 x20 x21 x22 x23 x24 x25 pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (st,800) (word_sub stackpointer (word 208),288) /\
       ALLPAIRS nonoverlapping
        [(st,800); (word_sub stackpointer (word 208),288)]
        [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
         (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
         (guard,8)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s =
                 word (pc + mlkem_shake128x4_absorb_once_after_memset) /\
                 read SP s = stackpointer /\
                 read X19 s = word mlen /\
                 read X20 s = m0 /\ read X21 s = m1 /\
                 read X22 s = m2 /\ read X23 s = m3 /\ read X24 s = st /\
                 read (memory :> bytes64 stackpointer) s = x19 /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 x20 /\
                 read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                 x21 /\
                 read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                 x22 /\
                 read (memory :> bytes64 (word_add stackpointer (word 32))) s =
                 x23 /\
                 read (memory :> bytes64 (word_add stackpointer (word 40))) s =
                 x24 /\
                 read (memory :> bytes64 (word_add stackpointer (word 48))) s =
                 x25 /\
                 read (memory :> bytes64 (word_add stackpointer (word 56))) s =
                 returnaddress /\
                 read (memory :> bytes64 (word_add stackpointer (word 72))) s =
                 canary /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                 guard /\
                 read (memory :> bytes64 guard) s = canary /\
                 read (memory :> bytes(m0,mlen)) s = M0 /\
                 read (memory :> bytes(m1,mlen)) s = M1 /\
                 read (memory :> bytes(m2,mlen)) s = M2 /\
                 read (memory :> bytes(m3,mlen)) s = M3 /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read SP s = word_add stackpointer (word 80) /\
                 read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                 read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
                 read X25 s = x25 /\ read X30 s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb_from S0 168
                    (M0 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M0 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 word_xor
                  (keccak_absorb_from S1 168
                    (M1 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M1 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 word_xor
                  (keccak_absorb_from S2 168
                    (M2 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M2 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 word_xor
                  (keccak_absorb_from S3 168
                    (M3 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M3 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st mlen guard pc
                           (word_sub stackpointer (word 208)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 208),288;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 208),288]))
            (MAYCHANGE [SP; X19; X20; X21; X22; X23; X24; X25; X30] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 208),288)])`,
  ABSX4_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_shake128x4_absorb_once_loop1_exit` ABSX4_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < 168` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_SHORT_TAC; ABSX4_LOOP_TAC];
    ASM_CASES_TAC `mlen < 168` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The three theorems, for the three contracts of memset, from the theorem   *)
(* for the code after it. Up to memset the function saves the registers,     *)
(* copies the stack guard and calls memset to zero the 800 bytes of the      *)
(* context through the PLT. The stack is the 80 bytes of the function and    *)
(* the 208 used by mlkem_keccakf1600x4_permute below them, 288 in all (304   *)
(* at -O2, where mlk_keccak_absorb_once_x4 is a separate function with a     *)
(* frame of 96 bytes).                                                       *)
(* ------------------------------------------------------------------------- *)

let ABSX4_TOP_VARS =
  [`pc:num`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
   `mlen:num`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

(*** The stack guard and the registers, as for the theorem after memset ***)

let ABSX4_TOP_SETUP_TAC =
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--25);;

(*** Up to the call of memset through the PLT ***)

let ABSX4_TOP_START_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC (5--17) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC 17;;

(*** The states zero after memset, as 1600-bit words ***)

let ABSX4_WBYTES_ZERO = prove
 (`!a s. read (memory :> bytes(a,200)) s = 0
         ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0]);;

let ABSX4_ZERO_TAC =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEMSET_ZERO_BYTES o
    check (fun th -> is_forall(concl th) && free_in `st:int64` (concl th) &&
                     free_in `bytes8:int64->(int64->byte,byte)component`
                             (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match [] `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match [] `read (memory :> bytes(a,200)) s = 0`) (concl th)
      then ASSUME_TAC(MATCH_MP ABSX4_WBYTES_ZERO th) else ALL_TAC) asl);;

(*** The arguments of the theorem after memset, with the states given ***)

let ABSX4_MSGS = [`M0:num`; `M1:num`; `M2:num`; `M3:num`];;

let ABSX4_BODY_ARGS msgs states =
  [`read events s`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
   `m3:int64`; `mlen:num`] @ msgs @ states @
  [`guard:int64`; `canary:int64`; `x19_init:int64`; `x20_init:int64`;
   `x21_init:int64`; `x22_init:int64`; `x23_init:int64`; `x24_init:int64`;
   `x25_init:int64`; `pc:num`; `read SP s`; `returnaddress:int64`];;

let ABSX4_ZERO_STATES = [`word 0:1600 word`; `word 0:1600 word`;
                         `word 0:1600 word`; `word 0:1600 word`];;

let ABSX4_CURRENT_STATES =
  [`read (memory :> wbytes st) s:1600 word`;
   `read (memory :> wbytes (word_add st (word 200))) s:1600 word`;
   `read (memory :> wbytes (word_add st (word 400))) s:1600 word`;
   `read (memory :> wbytes (word_add st (word 600))) s:1600 word`];;

let ABSX4_CURRENT_MSGS =
  [`read (memory :> bytes(m0,mlen)) s`; `read (memory :> bytes(m1,mlen)) s`;
   `read (memory :> bytes(m2,mlen)) s`; `read (memory :> bytes(m3,mlen)) s`];;

(*** The theorem after memset as a callee, from the variable fb chosen ***)
(*** for its events (correctness) or tailed (the others)              ***)

let ABSX4_FB =
  `fb:int64->int64->int64->int64->int64->num->int64->num->int64->int64->
      (uarch_event)list`;;

let ABSX4_BODY_CALL_TAC ilist n =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in ABSX4_FB (concl th)
    then ARM_SUBROUTINE_SIM_TAC
          (mlkem_native_libmlkem_gcc12_O3_mc,
           MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC,
           0x0,mlkem_native_libmlkem_gcc12_O3_mc,th) ilist n
    else NO_TAC);;

let ABSX4_SAFE_BODY_CALL_TAC ilist n =
  REMOVE_THEN "H_BODY" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      (`e:(uarch_event)list` :: tl ilist) n THENL
     [EXISTS_E2_TAC (ref ABSX4_TOP_VARS);
      LABEL_TAC "H_BODY" safety_th]);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 288),288) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 288),288)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 168
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 168
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 168
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 168
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  X_CHOOSE_TAC ABSX4_FB MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_BODY THEN
  ABSX4_TOP_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ABSX4_TOP_START_TAC THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 22 THEN
  ABSX4_ZERO_TAC THEN
  ABSX4_BODY_CALL_TAC (ABSX4_BODY_ARGS ABSX4_MSGS ABSX4_ZERO_STATES) 23 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KECCAK_ABSORB_FROM_0]);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e st m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 288),288) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 288),288]
            [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O3_mc /\
                     read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m0 m1 m2 m3 st mlen guard mf pc
                               (word_sub stackpointer (word 288))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                          word_sub stackpointer (word 288),288;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          ea,el]
                         [st,800; word_sub stackpointer (word 288),288]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 288),288)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_safety_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_BODY "H_BODY" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABSX4_TOP_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ABSX4_TOP_START_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET"
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref ABSX4_TOP_VARS) 22 THEN
  ABSX4_SAFE_BODY_CALL_TAC
   (ABSX4_BODY_ARGS ABSX4_CURRENT_MSGS ABSX4_CURRENT_STATES) 23 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
                 returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 288),288) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 288),288]
            [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O3_mc /\
                     read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read (memory :> bytes(m0,mlen)) s = M0 /\
                     read (memory :> bytes(m1,mlen)) s = M1 /\
                     read (memory :> bytes(m2,mlen)) s = M2 /\
                     read (memory :> bytes(m3,mlen)) s = M3 /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     read (memory :> wbytes st) s =
                     word_xor
                      (keccak_absorb 168
                        (M0 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M0 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 200))) s =
                     word_xor
                      (keccak_absorb 168
                        (M1 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M1 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 400))) s =
                     word_xor
                      (keccak_absorb 168
                        (M2 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M2 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 600))) s =
                     word_xor
                      (keccak_absorb 168
                        (M3 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M3 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m0 m1 m2 m3 st mlen guard mf pc
                               (word_sub stackpointer (word 288))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                          word_sub stackpointer (word 288),288;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          ea,el]
                         [st,800; word_sub stackpointer (word 288),288]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 288),288)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_BODY "H_BODY" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABSX4_TOP_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ABSX4_TOP_START_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET"
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref ABSX4_TOP_VARS) 22 THEN
  ABSX4_ZERO_TAC THEN
  ABSX4_SAFE_BODY_CALL_TAC
   (ABSX4_BODY_ARGS ABSX4_MSGS ABSX4_ZERO_STATES) 23 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KECCAK_ABSORB_FROM_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
