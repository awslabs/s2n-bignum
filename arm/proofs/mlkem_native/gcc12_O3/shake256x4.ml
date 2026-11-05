(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which zeroes a context of four states on the     *)
(* stack with memset, absorbs the inputs into it, squeezes the whole blocks  *)
(* of 136 bytes, the rate of SHAKE256, directly into the outputs, and the    *)
(* rest of the outputs through four buffers on the stack with memcpy,        *)
(* before zeroing the context with memset and the buffers. At -O2 it calls   *)
(* mlk_keccak_absorb_once_x4 for the absorption, but at -O3 gcc has inlined  *)
(* that code, with r = 136 and p = 0x1F: it XORs in each whole block of 136  *)
(* bytes of each input with mlkem_keccakf1600x4_xor_bytes and permutes the   *)
(* states with mlkem_keccakf1600x4_permute, and then XORs in the rest of     *)
(* each input and the padding, without permuting again. The byte of padding  *)
(* is on the stack, which gcc protects with a stack guard. It is verified in *)
(* the whole image (see libmlkem.ml), using the theorems for those two       *)
(* functions and for mlkem_keccakf1600x4_extract_bytes in the image and      *)
(* assuming the contracts for memset and memcpy in                           *)
(* utils/mlkem_native_libc.ml. The result is shake256 of common/fips202.ml   *)
(* for each input.                                                           *)
(*                                                                           *)
(* The theorems have the statements of the -O2 ones, except that the stack   *)
(* used is 1728 bytes rather than 1792: the frame of the function is 1520    *)
(* bytes, and mlkem_keccakf1600x4_permute below it uses 208.                 *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccak_absorb_once.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600x4_permute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600x4_xor_bytes.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600x4_extract_bytes.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The code in the image, and the PLT stubs for memcpy and memset:

    mlkem_shake256x4:
        +0x0: sub     sp, sp, #0x5f0
        +0x4: adrp    x8, <page>
        +0x8: ldr     x8, [x8, #4088]  // got_stack_chk_guard
        +0xc: stp     x27, x28, [sp, #64]
       +0x10: mov     x27, #0xf0f0f0f0f0f0f0f0
       +0x14: movk    x27, #0xf0f1
       +0x18: str     x4, [sp, #104]
       +0x1c: mov     x28, x6
       +0x20: umulh   x4, x4, x27
       +0x24: stp     x19, x20, [sp]
       +0x28: add     x20, sp, #0xaf
       +0x2c: stp     x21, x22, [sp, #16]
       +0x30: and     x20, x20, #0xffffffffffffffe0
       +0x34: mov     x22, x3
       +0x38: stp     x23, x24, [sp, #32]
       +0x3c: mov     x21, x5
       +0x40: mov     x24, x1
       +0x44: stp     x25, x26, [sp, #48]
       +0x48: mov     x25, x0
       +0x4c: lsr     x0, x4, #7
       +0x50: str     x30, [sp, #80]
       +0x54: mov     x23, x2
       +0x58: str     x0, [sp, #112]
       +0x5c: mov     x27, x7
       +0x60: ldr     x19, [sp, #1528]
       +0x64: mov     x0, x20
       +0x68: ldr     x26, [sp, #1520]
       +0x6c: ldr     x1, [x8]
       +0x70: str     x1, [sp, #1512]
       +0x74: mov     x1, #0x0
       +0x78: mov     x2, #0x320
       +0x7c: bl      <memset@plt>
       +0x80: mov     w0, #0x1f
       +0x84: strb    w0, [sp, #143]
       +0x88: cmp     x19, #0x87
       +0x8c: b.ls    <mlkem_shake256x4+0xd4>
       +0x90: mov     x4, x26
       +0x94: mov     x3, x27
       +0x98: mov     x2, x28
       +0x9c: mov     x1, x21
       +0xa0: mov     w6, #0x88
       +0xa4: mov     w5, #0x0
       +0xa8: mov     x0, x20
       +0xac: bl      <mlkem_keccakf1600x4_xor_bytes>
       +0xb0: mov     x0, x20
       +0xb4: sub     x19, x19, #0x88
       +0xb8: bl      <mlkem_keccakf1600x4_permute>
       +0xbc: add     x26, x26, #0x88
       +0xc0: add     x27, x27, #0x88
       +0xc4: add     x28, x28, #0x88
       +0xc8: add     x21, x21, #0x88
       +0xcc: cmp     x19, #0x87
       +0xd0: b.hi    <mlkem_shake256x4+0x90>
       +0xd4: mov     w7, w19
       +0xd8: cbnz    x19, <mlkem_shake256x4+0x23c>
       +0xdc: add     x19, sp, #0x8f
       +0xe0: mov     w5, w7
       +0xe4: mov     x4, x19
       +0xe8: mov     x3, x19
       +0xec: mov     x2, x19
       +0xf0: mov     x1, x19
       +0xf4: mov     x0, x20
       +0xf8: mov     w6, #0x1
       +0xfc: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0x100: mov     w7, #0xffffff80
      +0x104: mov     x4, x19
      +0x108: mov     x3, x19
      +0x10c: mov     x2, x19
      +0x110: mov     x1, x19
      +0x114: mov     x0, x20
      +0x118: mov     w6, #0x1
      +0x11c: mov     w5, #0x87
      +0x120: strb    w7, [sp, #143]
      +0x124: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0x128: ldp     x0, x21, [sp, #104]
      +0x12c: mov     x19, #0x0
      +0x130: cmp     x0, #0x87
      +0x134: b.ls    <mlkem_shake256x4+0x16c>
      +0x138: mov     x0, x20
      +0x13c: bl      <mlkem_keccakf1600x4_permute>
      +0x140: add     x4, x22, x19
      +0x144: add     x3, x23, x19
      +0x148: add     x2, x24, x19
      +0x14c: add     x1, x25, x19
      +0x150: mov     x0, x20
      +0x154: mov     w6, #0x88
      +0x158: mov     w5, #0x0
      +0x15c: bl      <mlkem_keccakf1600x4_extract_bytes>
      +0x160: add     x19, x19, #0x88
      +0x164: subs    x21, x21, #0x1
      +0x168: b.ne    <mlkem_shake256x4+0x138>
      +0x16c: ldr     x0, [sp, #104]
      +0x170: mov     x19, #0xf0f0f0f0f0f0f0f0
      +0x174: movk    x19, #0xf0f1
      +0x178: umulh   x19, x0, x19
      +0x17c: lsr     x19, x19, #7
      +0x180: add     x19, x19, x19, lsl #4
      +0x184: subs    x19, x0, x19, lsl #3
      +0x188: b.ne    <mlkem_shake256x4+0x29c>
      +0x18c: add     x21, sp, #0x560
      +0x190: add     x26, sp, #0x4d8
      +0x194: add     x28, sp, #0x450
      +0x198: add     x27, sp, #0x3c8
      +0x19c: mov     x0, x20
      +0x1a0: mov     x2, #0x320
      +0x1a4: mov     w1, #0x0
      +0x1a8: bl      <memset@plt>
      +0x1ac: movi    v0.4s, #0x0
      +0x1b0: str     xzr, [x27, #128]
      +0x1b4: stp     q0, q0, [x27]
      +0x1b8: stp     q0, q0, [x27, #32]
      +0x1bc: stp     q0, q0, [x27, #64]
      +0x1c0: stp     q0, q0, [x27, #96]
      +0x1c4: stp     q0, q0, [x28]
      +0x1c8: stp     q0, q0, [x28, #32]
      +0x1cc: stp     q0, q0, [x28, #64]
      +0x1d0: stp     q0, q0, [x28, #96]
      +0x1d4: str     xzr, [x28, #128]
      +0x1d8: stp     q0, q0, [x26]
      +0x1dc: stp     q0, q0, [x26, #32]
      +0x1e0: stp     q0, q0, [x26, #64]
      +0x1e4: stp     q0, q0, [x26, #96]
      +0x1e8: str     xzr, [x26, #128]
      +0x1ec: stp     q0, q0, [x21]
      +0x1f0: stp     q0, q0, [x21, #32]
      +0x1f4: stp     q0, q0, [x21, #64]
      +0x1f8: stp     q0, q0, [x21, #96]
      +0x1fc: str     xzr, [x21, #128]
      +0x200: adrp    x0, <page>
      +0x204: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x208: ldr     x2, [sp, #1512]
      +0x20c: ldr     x1, [x0]
      +0x210: subs    x2, x2, x1
      +0x214: mov     x1, #0x0
      +0x218: b.ne    <mlkem_shake256x4+0x330>
      +0x21c: ldp     x19, x20, [sp]
      +0x220: ldp     x21, x22, [sp, #16]
      +0x224: ldp     x23, x24, [sp, #32]
      +0x228: ldp     x25, x26, [sp, #48]
      +0x22c: ldp     x27, x28, [sp, #64]
      +0x230: ldr     x30, [sp, #80]
      +0x234: add     sp, sp, #0x5f0
      +0x238: ret
      +0x23c: mov     x4, x26
      +0x240: mov     x3, x27
      +0x244: mov     x2, x28
      +0x248: mov     x1, x21
      +0x24c: mov     w6, w19
      +0x250: mov     x0, x20
      +0x254: mov     w5, #0x0
      +0x258: str     w19, [sp, #124]
      +0x25c: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0x260: ldr     w7, [sp, #124]
      +0x264: cmp     x19, #0x87
      +0x268: b.ne    <mlkem_shake256x4+0xdc>
      +0x26c: ldrb    w7, [sp, #143]
      +0x270: add     x4, sp, #0x8f
      +0x274: mov     w5, w19
      +0x278: mov     x3, x4
      +0x27c: orr     w7, w7, #0xffffff80
      +0x280: mov     x2, x4
      +0x284: mov     x1, x4
      +0x288: mov     x0, x20
      +0x28c: mov     w6, #0x1
      +0x290: strb    w7, [sp, #143]
      +0x294: bl      <mlkem_keccakf1600x4_xor_bytes>
      +0x298: b       <mlkem_shake256x4+0x128>
      +0x29c: ldr     x0, [sp, #112]
      +0x2a0: add     x21, sp, #0x560
      +0x2a4: add     x26, sp, #0x4d8
      +0x2a8: add     x28, sp, #0x450
      +0x2ac: add     x27, x0, x0, lsl #4
      +0x2b0: mov     x0, x20
      +0x2b4: lsl     x1, x27, #3
      +0x2b8: add     x27, sp, #0x3c8
      +0x2bc: str     x1, [sp, #104]
      +0x2c0: bl      <mlkem_keccakf1600x4_permute>
      +0x2c4: mov     x4, x21
      +0x2c8: mov     x3, x26
      +0x2cc: mov     w6, #0x88
      +0x2d0: mov     w5, #0x0
      +0x2d4: mov     x2, x28
      +0x2d8: mov     x1, x27
      +0x2dc: mov     x0, x20
      +0x2e0: bl      <mlkem_keccakf1600x4_extract_bytes>
      +0x2e4: ldr     x0, [sp, #104]
      +0x2e8: mov     x2, x19
      +0x2ec: mov     x1, x27
      +0x2f0: add     x0, x25, x0
      +0x2f4: bl      <memcpy@plt>
      +0x2f8: ldr     x25, [sp, #104]
      +0x2fc: mov     x2, x19
      +0x300: mov     x1, x28
      +0x304: add     x0, x24, x25
      +0x308: bl      <memcpy@plt>
      +0x30c: mov     x2, x19
      +0x310: mov     x1, x26
      +0x314: add     x0, x23, x25
      +0x318: bl      <memcpy@plt>
      +0x31c: mov     x2, x19
      +0x320: mov     x1, x21
      +0x324: add     x0, x22, x25
      +0x328: bl      <memcpy@plt>
      +0x32c: b       <mlkem_shake256x4+0x19c>
      +0x330: bl      <__stack_chk_fail@plt>

    memcpy@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4048]  // got_memcpy
      +0x8: add     x16, x16, #0xfd0  // got_memcpy
      +0xc: br      x17

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_shake256x4"; layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Absorbing from a given state rather than from zero, as keccak_absorb in   *)
(* common/fips202.ml does. The code of the absorption is verified for any    *)
(* initial states, so that the same proof serves the theorems for the        *)
(* contracts of memset, which give the states after it as zero or as         *)
(* unknown.                                                                  *)
(* ------------------------------------------------------------------------- *)

let keccak_absorb_from_gen = define
 `keccak_absorb_from_gen (s0:1600 word) r p 0 = s0 /\
  keccak_absorb_from_gen s0 r p (SUC j) =
    keccak_f1600
     (word_xor (keccak_absorb_from_gen s0 r p j)
               (word((p DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r))))`;;

let KECCAK_ABSORB_FROM_GEN_0 = prove
 (`!r p j. keccak_absorb_from_gen (word 0) r p j = keccak_absorb r p j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[keccak_absorb_from_gen; keccak_absorb]);;

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
(* The absorption, from after the first memset to the point where the        *)
(* squeezing starts, for any initial states S0 to S3 (the states then are as *)
(* for keccak_absorb_from_gen), with the events (constant time and memory    *)
(* safety). The inputs are in registers: X19 is the length and X21, X28, X27 *)
(* and X26 the four inputs; X20 is the context. The stack is the part of the *)
(* frame holding the registers saved and the byte of padding (at sp + 143),  *)
(* with the 208 bytes used by mlkem_keccakf1600x4_permute below them. The    *)
(* length is not a multiple of 136 in general, so the last block is padded,  *)
(* with the padding byte XORed in separately. The events of the last block   *)
(* are given in three cases, as for mlk_keccak_absorb_once, and so is the    *)
(* first test of the length.                                                 *)
(* ------------------------------------------------------------------------- *)

let S256_ABS_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `mlen:num`; `stackpointer:int64`];;

let S256_ABS_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV 136 = q` || c = `mlen MOD 136 = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

let S256_ABS_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  S256_ABS_UNABBREV_TAC THEN
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

let S256_ABS_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let S256_ABS_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let S256_ABS_INPS =
  [`m0:int64`,`M0:num`,`P0:num`,`S0:1600 word`;
   `m1:int64`,`M1:num`,`P1:num`,`S1:1600 word`;
   `m2:int64`,`M2:num`,`P2:num`,`S2:1600 word`;
   `m3:int64`,`M3:num`,`P3:num`,`S3:1600 word`];;

(*** The events as in the -O2 template for mlk_keccak_absorb_once_x4: ***)
(*** the last block in three cases, after the test of mlen and the     ***)
(*** loop over the whole blocks                                         ***)

let S256_ABS_TEMPLATE =
  let ord = [`m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
             `mlen:num`; `pc:num`; `stackpointer:int64`] in
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
                          [`mlen DIV 136`; loop]) in
  let tail = mk_cond(`mlen MOD 136 = 0`,app "f_ev_t0",
               mk_cond(`mlen MOD 136 = 135`,app "f_ev_t1",app "f_ev_t2")) in
  let head = mk_cond(`mlen < 136`,app "f_ev_short",
               list_mk_comb(ap,[app "f_ev_epil";
                 list_mk_comb(ap,[enum; app "f_ev_prol"])])) in
  list_mk_abs(ord,list_mk_comb(ap,[tail; head]));;

let S256_ABS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC S256_ABS_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT(W(fun (asl,w) ->
    if name_of(fst(dest_forall w)) = "stackpointer" then NO_TAC
    else GEN_TAC)) THEN
  WORD_FORALL_OFFSET_TAC 208 THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (_,m,p,_) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 136 0x1F mlen)`))
   S256_ABS_INPS;;

(*** The facts holding throughout: the stack pointer, the byte of padding ***)
(*** at sp + 143 and the inputs                                          ***)

let S256_ABS_FRAME =
 "read SP s = word_add stackpointer (word 208) /\\
  read (memory :> bytes8 (word_add stackpointer (word 351))) s = word 31 /\\
  read (memory :> bytes(m0,mlen)) s = M0 /\\
  read (memory :> bytes(m1,mlen)) s = M1 /\\
  read (memory :> bytes(m2,mlen)) s = M2 /\\
  read (memory :> bytes(m3,mlen)) s = M3";;

let S256_ABS_STATES k =
 "read (memory :> bytes(st,200)) s =
  val(keccak_absorb_from_gen S0 136 P0 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 200),200)) s =
  val(keccak_absorb_from_gen S1 136 P1 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 400),200)) s =
  val(keccak_absorb_from_gen S2 136 P2 " ^ k ^ ") /\\
  read (memory :> bytes(word_add st (word 600),200)) s =
  val(keccak_absorb_from_gen S3 136 P3 " ^ k ^ ")";;

let S256_ABS_MID = parse_term
 ("\\s. read X19 s = word(mlen MOD 136) /\\
       read X21 s = word_add m0 (word(136 * mlen DIV 136)) /\\
       read X28 s = word_add m1 (word(136 * mlen DIV 136)) /\\
       read X27 s = word_add m2 (word(136 * mlen DIV 136)) /\\
       read X26 s = word_add m3 (word(136 * mlen DIV 136)) /\\
       read X20 s = st /\\ " ^
  S256_ABS_FRAME ^ " /\\ " ^ S256_ABS_STATES "(mlen DIV 136)");;

let S256_ABS_INV = parse_term
 ("\\k s. read X19 s = word(mlen - 136 * k) /\\
         read X21 s = word_add m0 (word(136 * k)) /\\
         read X28 s = word_add m1 (word(136 * k)) /\\
         read X27 s = word_add m2 (word(136 * k)) /\\
         read X26 s = word_add m3 (word(136 * k)) /\\
         read X20 s = st /\\ " ^
  S256_ABS_FRAME ^ " /\\ " ^ S256_ABS_STATES "k");;

let S256_ABS_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [S256_ABS_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let S256_ABS_XOR_TAC off len data vars n =
  S256_ABS_STATES_TAC THEN
  S256_ABS_STATES_THEN (fun v0 v1 v2 v3 ->
    S256_ABS_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; off; len; v0; v1; v2; v3] @ data @
      [`pc:num`; `read SP s`; `read X30 s`]) vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let S256_ABS_PERMUTE_TAC vars n =
  S256_ABS_STATES_TAC THEN
  S256_ABS_STATES_THEN (fun v0 v1 v2 v3 ->
    S256_ABS_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; v0; v1; v2; v3; `pc:num`;
      `read SP s`; `read X30 s`] vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(*** The start: the byte of padding and the comparison of mlen with 135 ***)

let S256_ABS_PROLOGUE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--3) THEN
  ABSORB_VAL_TAC THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (4--4) THEN
  ABSORB_BRANCH_TAC;;

let S256_ABS_SHORT_TAC =
  S256_ABS_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb_from_gen] THEN ABSORB_DISCHARGE_TAC;;

let S256_ABS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV 136`
   `pc + mlkem_shake256x4_loop1`
   `pc + mlkem_shake256x4_loop1_exit`
    S256_ABS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop ***)

    S256_ABS_PROLOGUE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; keccak_absorb_from_gen] THEN
    ABSORB_DISCHARGE_TAC;

    (*** The loop body: XOR in a block of each, permute, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + 136 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (m,mm,_,_) ->
      MP_TAC(SPECL [m; `mlen:num`; mm; `136 * i`; `136`; `s0:armstate`]
                   READ_MEMORY_BYTES_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) S256_ABS_INPS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--8) THEN
    S256_ABS_XOR_TAC `0` `136`
     (map (fun (_,mm,_,_) ->
        subst [mm,`M:num`] `(M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`)
      S256_ABS_INPS)
     (S256_ABS_SAFE_VARS @ [`i:num`]) 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (10--12) THEN
    S256_ABS_PERMUTE_TAC (S256_ABS_SAFE_VARS @ [`i:num`]) 13 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (14--18) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (19--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `135 <= x /\ ~(x = 135) <=> 136 <= x`] THEN
    MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(AP_TERM_TAC THEN
        REWRITE_TAC[GSYM ADD1; keccak_absorb_from_gen] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[MULT_CLAUSES; EXP] THEN
        MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
        CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
        MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
        UNDISCH_TAC `136 * i + 136 <= mlen` THEN ARITH_TAC) THEN
    ABSORB_DISCHARGE_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    ABSORB_DISCHARGE_TAC];;

(*** The bounds of the messages, and their last blocks with the padding ***)

let S256_ABS_MBOUND_TAC =
  MAP_EVERY (fun (_,mm,_,_) ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC]) S256_ABS_INPS;;

let S256_ABS_LASTBLOCK_TAC =
  MAP_EVERY (fun (_,mm,pp,_) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * 136) =
        M DIV 2 EXP (8 * 136 * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad 136 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [fst(dest_var pp); "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `0 < 136 /\ 31 < 128`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]) S256_ABS_INPS;;

(*** The byte n at byte 143 of the frame in state sname, as a 1-byte array ***)

let S256_ABS_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 351),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let S256_ABS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV 136 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD 136 = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let S256_ABS_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `136 * q + t = mlen`));;

(*** The end of the absorption, the same for the three cases ***)

let S256_ABS_END_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The four states, from the tactic for one lane, and the events ***)

let S256_ABS_LANES_TAC lane =
  REPEAT CONJ_TAC THENL
   (map (fun (_,mm,_,_) -> lane mm) S256_ABS_INPS @ [S256_ABS_EVENTS_TAC]);;

(*** A whole number of blocks: 0x1F at byte 0 and 128 at byte 135 ***)

let S256_ABS_T0_LANE_TAC mm =
  S256_ABS_MLEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136 /\ 31 < 128`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN (subst [mm,`M:num`] `M DIV 2 EXP (8 * 136 * q) = 0`)
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    UNDISCH_TAC (subst [mm,`M:num`] `M < 2 EXP (8 * (136 * q + t))`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT; ARITH_RULE `~(136 = 0)`] THEN
  REWRITE_TAC[ARITH_RULE `~(0 = 136 - 1) /\ 136 - 0 - 1 = 135`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
  TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[LE_EXP] THEN ARITH_TAC];;

(*** The padding is just the single byte 0x1F + 128 at byte 135 ***)

let S256_ABS_T1_LANE_TAC mm =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `136 * q + 135 = mlen`)) THEN
  SUBGOAL_THEN `(136 * q + 135) MOD 136 = 135` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136 /\ 31 < 128`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `136 - 1 = 135`; ARITH_RULE `31 + 128 = 159`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(*** Otherwise 0x1F at byte t and 128 at byte 135 ***)

let S256_ABS_T2_LANE_TAC mm =
  S256_ABS_MLEN_TAC THEN
  SUBGOAL_THEN `(136 * q + t) MOD 136 = t` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `0 < 136 /\ 31 < 128`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `136 - 1 = 135`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `2 EXP (8 * 135) = 2 EXP (8 * t) * 2 EXP (8 * (136 - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (136 - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

let S256_ABS_REP4 t = [t; t; t; t];;

let S256_ABS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV 136` THEN ABBREV_TAC `t = mlen MOD 136` THEN
  SUBGOAL_THEN `136 * q + t = mlen /\ t < 136` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  S256_ABS_MBOUND_TAC THEN S256_ABS_LASTBLOCK_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--1) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (2--11) THEN
    S256_ABS_BYTE_FACT_TAC "s11" `31` THEN
    S256_ABS_XOR_TAC `0` `1` (S256_ABS_REP4 `31`) S256_ABS_SAFE_VARS 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (13--22) THEN
    S256_ABS_BYTE_FACT_TAC "s22" `128` THEN
    SUBGOAL_THEN `135 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S256_ABS_XOR_TAC `135` `1` (S256_ABS_REP4 `128`) S256_ABS_SAFE_VARS 23 THEN
    S256_ABS_END_TAC THEN S256_ABS_LANES_TAC S256_ABS_T0_LANE_TAC;
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of each message after the blocks ***)

  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,mm,_,_) ->
    SUBGOAL_THEN
     (subst [mm,`M:num`] `M DIV 2 EXP (8 * 136 * q) < 2 EXP (8 * t)`)
    ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      FIRST_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
        `M < 2 EXP (8 * mlen)` then MP_TAC th else NO_TAC) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `136 * q + t = mlen`)) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [m; `mlen:num`; mm; `136 * q`; `t:num`; `s1:armstate`]
                 READ_MEMORY_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC) S256_ABS_INPS THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (2--11) THEN
  ARGS_32_TAC [`t:num`] THEN
  S256_ABS_XOR_TAC `0` `t:num`
   (map (fun (_,mm,_,_) -> subst [mm,`M:num`] `M DIV 2 EXP (8 * 136 * q)`)
        S256_ABS_INPS)
   S256_ABS_SAFE_VARS 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (13--14) THEN
  PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = 135` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = 135`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (15--26) THEN
    S256_ABS_BYTE_FACT_TAC "s26" `159` THEN
    SUBGOAL_THEN `135 + 1 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    S256_ABS_XOR_TAC `135` `1` (S256_ABS_REP4 `159`) S256_ABS_SAFE_VARS 27 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (28--28) THEN
    S256_ABS_END_TAC THEN S256_ABS_LANES_TAC S256_ABS_T1_LANE_TAC;

    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (15--24) THEN
    ARGS_32_TAC [`t:num`] THEN
    S256_ABS_BYTE_FACT_TAC "s24" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 135 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    S256_ABS_XOR_TAC `t:num` `1` (S256_ABS_REP4 `31`) S256_ABS_SAFE_VARS 25 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     (26--35) THEN
    S256_ABS_BYTE_FACT_TAC "s35" `128` THEN
    S256_ABS_XOR_TAC `135` `1` (S256_ABS_REP4 `128`) S256_ABS_SAFE_VARS 36 THEN
    S256_ABS_END_TAC THEN S256_ABS_LANES_TAC S256_ABS_T2_LANE_TAC];;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O3_ABSORB = prove
 (`exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 S0 S1 S2 S3 pc stackpointer.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (st,800) (word_sub stackpointer (word 208),352) /\
       ALLPAIRS nonoverlapping
        [(st,800); (word_sub stackpointer (word 208),352)]
        [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
         (word pc,libmlkem_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s =
                 word (pc + mlkem_shake256x4_after_memset_1) /\
                 read SP s = stackpointer /\
                 read X19 s = word mlen /\
                 read X20 s = st /\
                 read X21 s = m0 /\ read X28 s = m1 /\
                 read X27 s = m2 /\ read X26 s = m3 /\
                 read (memory :> bytes(m0,mlen)) s = M0 /\
                 read (memory :> bytes(m1,mlen)) s = M1 /\
                 read (memory :> bytes(m2,mlen)) s = M2 /\
                 read (memory :> bytes(m3,mlen)) s = M3 /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read PC s = word (pc + mlkem_shake256x4_join3) /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb_from_gen S0 136
                    (M0 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 136 0x1F mlen))
                    (mlen DIV 136))
                  (word((M0 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                        2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))) /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 word_xor
                  (keccak_absorb_from_gen S1 136
                    (M1 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 136 0x1F mlen))
                    (mlen DIV 136))
                  (word((M1 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                        2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))) /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 word_xor
                  (keccak_absorb_from_gen S2 136
                    (M2 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 136 0x1F mlen))
                    (mlen DIV 136))
                  (word((M2 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                        2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))) /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 word_xor
                  (keccak_absorb_from_gen S3 136
                    (M3 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 136 0x1F mlen))
                    (mlen DIV 136))
                  (word((M3 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                        2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st mlen pc
                           (word_sub stackpointer (word 208)) /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 208),352;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 208),352]))
            (MAYCHANGE [X19; X21; X26; X27; X28; X30] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 208),208);
               memory :> bytes(word_add stackpointer (word 124),4);
               memory :> bytes(word_add stackpointer (word 143),1)])`,
  S256_ABS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_shake256x4_loop1_exit` S256_ABS_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < 136` THEN ASM_REWRITE_TAC[] THENL
     [S256_ABS_SHORT_TAC; S256_ABS_LOOP_TAC];
    ASM_CASES_TAC `mlen < 136` THEN ASM_REWRITE_TAC[] THEN
    S256_ABS_TAIL_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The context is aligned to 32 bytes within the stack frame, so its address *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* The four states in it are at offsets 0, 200, 400 and 600, in the form in  *)
(* which their addresses are normalized by the simulation.                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let SHAKE256X4_CTX_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 383)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 352 else 368))`,
  REWRITE_TAC[SHAKE256X4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256X4_CTX_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 383))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 352 else 368))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256X4_CTX_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256X4_ST =
  [`word_add stackpointer
     (word(if aligned 32 stackpointer then 352 else 368)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 352 else 368) + 200)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 352 else 368) + 400)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 352 else 368) + 600)):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_ST;;

(* ------------------------------------------------------------------------- *)
(* The number of whole blocks, outlen DIV 136, is computed by multiplying by *)
(* a constant (umulh and lsr), and multiplied back by 136 with shifts, to    *)
(* get the number of remaining bytes, outlen MOD 136. The loop is skipped    *)
(* if outlen <= 135, that is if there are no whole blocks.                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_NBLOCKS = prove
 (`!x. x < 2 EXP 64
       ==> (x * 17361641481138401521) DIV 2 EXP 64 DIV 2 EXP 7 = x DIV 136`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`x:num`; `136`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`x MOD 136`,`r:num`) THEN SPEC_TAC(`x DIV 136`,`q:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `8 * q + r * 17361641481138401521` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let SHAKE256X4_NBLOCKS_WORD = prove
 (`!n. n < 2 EXP 64
       ==> word_ushr (word((n * 17361641481138401521) DIV 2 EXP 64):int64) 7 =
           word(n DIV 136)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `val(word((n * 17361641481138401521) DIV 2 EXP 64):int64) =
    (n * 17361641481138401521) DIV 2 EXP 64`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 64 * 17361641481138401521` THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC SHAKE256X4_NBLOCKS THEN ASM_REWRITE_TAC[]]);;

let SHAKE256X4_MUL136 = prove
 (`!n. word_shl (word_add (word n) (word_shl (word n) 4)) 3:int64 =
       word(136 * n)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_64; GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SHAKE256X4_LS_LEMMA = prove
 (`!n. n < 2 EXP 64
       ==> (135 <= n /\ ~(val(word_sub (word n) (word 135):int64) = 0) <=>
            ~(n DIV 136 = 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word 135:int64) = 135`
   (fun th -> REWRITE_TAC[th])
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC]);;

(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1728 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN
   `136 * outlen DIV 136 + outlen MOD 136 = outlen /\ outlen MOD 136 < 136`
  MP_TAC THENL
   [MP_TAC(SPECL [`outlen:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `nb = outlen DIV 136` THEN ABBREV_TAC `rest = outlen MOD 136` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rest <= 136 /\ val(word rest:int64) = rest` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC VAL_WORD_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `rest < 136` THEN ARITH_TAC;
    ALL_TAC];;

(*** The number of blocks, the branch round the loop and the remainder ***)

let SHAKE256X4_NBLOCKS_TAC =
  let th = REWRITE_RULE[ASSUME `outlen DIV 136 = nb`]
            (MP (SPEC `outlen:num` SHAKE256X4_NBLOCKS_WORD)
                (ASSUME `outlen < 2 EXP 64`)) in
  RULE_ASSUM_TAC(REWRITE_RULE[th]);;

let SHAKE256X4_BRANCH_TAC th tm =
  RULE_ASSUM_TAC(fun th' ->
    if is_eq(concl th') && is_cond(rand(concl th'))
    then REWRITE_RULE[th; ASSUME tm] th' else th');;

let SHAKE256X4_LS_TAC tm =
  SHAKE256X4_BRANCH_TAC
   (REWRITE_RULE[ASSUME `outlen DIV 136 = nb`]
     (MP (SPEC `outlen:num` SHAKE256X4_LS_LEMMA)
         (ASSUME `outlen < 2 EXP 64`))) tm;;

let SHAKE256X4_REST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SUBGOAL_THEN `word_sub (word outlen) (word(136 * nb)):int64 = word rest`
   (fun th ->
      let t = `val(word rest:int64) = rest` in
      RULE_ASSUM_TAC(fun th' ->
        if concl th' = t then th' else REWRITE_RULE[th; ASSUME t] th')) THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `136 * nb + rest = outlen` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

(*** The loop counter, nb - i, after the subs ***)

let SHAKE256X4_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nb - i)) (word 1):int64 = word(nb - (i + 1))`
  SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nb` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nb - (i + 1)):int64) = nb - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`outlen < 2 EXP 64`; `136 * nb + rest = outlen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nb - (i + 1) = 0) <=> i + 1 < nb`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;


(* ------------------------------------------------------------------------- *)
(* The setup for both proofs, and the facts holding at all the intermediate  *)
(* points: the saved registers, the stack guard and the GOT entries.         *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1728):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `352 <= (if aligned 32 (stackpointer:int64) then 352 else 368) /\
    (if aligned 32 (stackpointer:int64) then 352 else 368) <= 368`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

let SHAKE256X4_FRAME =
 `read SP s = word_add stackpointer (word 208) /\
  read (memory :> bytes64 (word_add stackpointer (word 208))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 216))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 224))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 232))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 240))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 248))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1720))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME));;

(*** The subroutines ***)

let LOCAL_PERMUTE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
  MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
  MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The output of SHAKE256 in blocks, as in mlkem_shake256, in terms of the   *)
(* state after absorbing the input as by the absorption above, and the first *)
(* n bytes of one of the buffers holding a block.                            *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SPONGE = prove
 (`!(m:byte list) k n.
        n <= 136
        ==> num_of_bytelist(list_of_seq (\j. shake256 m (136 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 136
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 136 0x1F (LENGTH m)))
                     (LENGTH m DIV 136))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 136 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 136 * LENGTH m DIV 136) MOD
                         2 EXP (8 * 136))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake256] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SHAKE256X4_TMP_LEMMA = prove
 (`!a (S:1600 word) n s:armstate.
        read (memory :> bytes(a,136)) s =
        (val S DIV 2 EXP (8 * 0)) MOD 2 EXP (8 * 136) /\ n <= 136
        ==> read (memory :> bytes(a,n)) s = val S MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `136`; `n:num`; `read memory s`]
                READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `n <= 136 ==> MIN 136 n = n /\ MIN (8 * 136) (8 * n) = 8 * n`]);;

(*** The four absorbed states as S0, ..., S3, with their outputs ***)

let SHAKE256X4_ABSORBED =
 `\M. word_xor
       (keccak_absorb 136
         (M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad 136 0x1F inlen))
         (inlen DIV 136))
       (word((M + 2 EXP (8 * inlen) *
                  num_of_bytelist(keccak_pad 136 0x1F inlen)) DIV
             2 EXP (8 * 136 * inlen DIV 136) MOD 2 EXP (8 * 136))):1600 word`;;

let SHAKE256X4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = rhs(concl(BETA_CONV
             (mk_comb(SHAKE256X4_ABSORBED,
                      mk_comb(`num_of_bytelist:byte list->num`,inp))))) in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),
                           `inlen:num`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp SHAKE256X4_SPONGE)))
   (zip [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
         `inp3:byte list`]
        [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]);;

(*** The first rest bytes of the buffer at a, before the memcpy ***)

let SHAKE256X4_TMP_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`136`) ->
          ASSUME_TAC(MATCH_MP SHAKE256X4_TMP_LEMMA
                      (CONJ th (ASSUME `rest <= 136`)))
    | _ -> NO_TAC);;

(*** The intermediate points: after absorbing, after the whole blocks.  ***)
(*** The stack holds outlen at sp + 104 and the number of blocks at     ***)
(*** sp + 112, as stored by the prologue.                               ***)

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 352 else 368)) /\
      read X22 s = out3 /\ read X23 s = out2 /\
      read X24 s = out1 /\ read X25 s = out0 /\
      read (memory :> bytes64 (word_add stackpointer (word 312))) s =
      word outlen /\
      read (memory :> bytes64 (word_add stackpointer (word 320))) s =
      word nb /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 352 else 368)),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 200)),
              200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 400)),
              200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 600)),
              200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 352 else 368)) /\
      read X22 s = out3 /\ read X23 s = out2 /\
      read X24 s = out1 /\ read X25 s = out0 /\
      read (memory :> bytes64 (word_add stackpointer (word 312))) s =
      word outlen /\
      read (memory :> bytes64 (word_add stackpointer (word 320))) s =
      word nb /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 352 else 368)),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 200)),
              200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 400)),
              200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 352 else 368) + 600)),
              200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

(*** The loop invariant, with i blocks done ***)

let SHAKE256X4_INV = SHAKE256X4_AT
 `\i s. read X19 s = word(136 * i) /\ read X21 s = word(nb - i) /\
        read X20 s =
        word_add stackpointer
         (word(if aligned 32 stackpointer then 352 else 368)) /\
        read X22 s = out3 /\ read X23 s = out2 /\
        read X24 s = out1 /\ read X25 s = out0 /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        word outlen /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        word nb /\
        read (memory :> bytes(out0,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp0) (136 * i)) /\
        read (memory :> bytes(out1,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp1) (136 * i)) /\
        read (memory :> bytes(out2,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp2) (136 * i)) /\
        read (memory :> bytes(out3,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp3) (136 * i)) /\
        read (memory :> bytes(word_add stackpointer
                (word(if aligned 32 stackpointer then 352 else 368)),200)) s =
        val(keccak_squeeze i (S0:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 352 else 368) + 200)),
                200)) s =
        val(keccak_squeeze i (S1:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 352 else 368) + 400)),
                200)) s =
        val(keccak_squeeze i (S2:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 352 else 368) + 600)),
                200)) s =
        val(keccak_squeeze i (S3:1600 word))`;;

(*** After the remaining bytes, with the addresses of the buffers ***)

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 352 else 368)) /\
      read X27 s = word_add stackpointer (word 1176) /\
      read X28 s = word_add stackpointer (word 1312) /\
      read X26 s = word_add stackpointer (word 1448) /\
      read X21 s = word_add stackpointer (word 1584) /\
      read (memory :> bytes(out0,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
      read (memory :> bytes(out1,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
      read (memory :> bytes(out2,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
      read (memory :> bytes(out3,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) outlen)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy at the    *)
(* addresses mf and mc in the GOT entries, with their code and data in the   *)
(* region (ea,el). The inputs are four lists of bytes of the same length     *)
(* inlen, at in0, ..., in3, the last given on the stack with inlen, and the  *)
(* outlen bytes of each output, as a number, are the first outlen bytes of   *)
(* shake256 of the corresponding input. The stack is the 1520 bytes of the   *)
(* function and the 208 used by mlkem_keccakf1600x4_permute below them, and  *)
(* the two 8-byte stack arguments are just above it.                         *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_WBYTES_ZERO = prove
 (`!a s. read (memory :> bytes(a,200)) s = 0
         ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0]);;

let SHAKE256X4_ZERO_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o
    check (can (term_match [] `read (memory :> bytes(a,800)) s = 0`) o
           concl)) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
         `read (memory :> bytes(word_add (word_add a b) c,200)) s = 0`)
         (concl th)
    then REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th else th) THEN
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match [] `read (memory :> bytes(a,200)) s = 0`) (concl th)
      then ASSUME_TAC(MATCH_MP SHAKE256X4_WBYTES_ZERO th) else ALL_TAC) asl);;

let SHAKE256X4_ABSORB_ARGS msgs states =
  [`read events s`; `read X20 s`; `read X21 s`; `read X28 s`; `read X27 s`;
   `read X26 s`; `inlen:num`] @ msgs @ states @
  [`pc:num`; `read SP s`];;

let SHAKE256X4_ABSORB_CALL_TAC ilist n =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       free_in `fb:int64->int64->int64->int64->int64->num->num->int64->
                (uarch_event)list` (concl th)
    then ARM_SUBROUTINE_SIM_TAC
          (mlkem_native_libmlkem_gcc12_O3_mc,
           MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC,
           0x0,mlkem_native_libmlkem_gcc12_O3_mc,th) ilist n
    else NO_TAC);;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1728),1728)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1728),1728)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (stackpointer,16); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_shake256x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                  read (memory :> bytes64 stackpointer) s = in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word inlen /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in0,inlen)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(in1,inlen)) s = num_of_bytelist inp1 /\
                  read (memory :> bytes(in2,inlen)) s = num_of_bytelist inp2 /\
                  read (memory :> bytes(in3,inlen)) s = num_of_bytelist inp3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
                  read (memory :> bytes(out1,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
                  read (memory :> bytes(out2,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
                  read (memory :> bytes(out3,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp3) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                memory :> bytes(word_sub stackpointer (word 1728),1728)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1728 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMCPY" o REWRITE_RULE[memcpy_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  X_CHOOSE_TAC
   `fb:int64->int64->int64->int64->int64->num->num->int64->
       (uarch_event)list`
   MLKEM_NATIVE_SHAKE256X4_GCC12_O3_ABSORB THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  SHAKE256X4_ABSORBED_TAC THEN

  (*** Zeroing the context with memset, and the absorption ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_join3` SHAKE256X4_A1 THEN
    CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (3--13) THEN
    SHAKE256X4_CTX_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (14--32) THEN
    SHAKE256X4_NBLOCKS_TAC THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC 32 THEN
    LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 37 THEN
    MEMSET_ZERO_BYTES_TAC THEN SHAKE256X4_ZERO_TAC THEN
    SHAKE256X4_ABSORB_CALL_TAC
     (SHAKE256X4_ABSORB_ARGS
       [`num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
        `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`]
       [`word 0:1600 word`; `word 0:1600 word`; `word 0:1600 word`;
        `word 0:1600 word`]) 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KECCAK_ABSORB_FROM_GEN_0];
    ALL_TAC] THEN

  (*** The whole blocks, in a loop unless there are none ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_loop2_exit` SHAKE256X4_A2 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `nb = 0` THENL
     [ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
      SHAKE256X4_LS_TAC `nb = 0` THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL; list_of_seq;
                  num_of_bytelist; keccak_squeeze];
      ALL_TAC] THEN
    ENSURES_WHILE_UP2_TAC `nb:num` `pc + mlkem_shake256x4_loop2`
     `pc + mlkem_shake256x4_loop2_exit`
      SHAKE256X4_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];

      (*** Initialization ***)

      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
      SHAKE256X4_LS_TAC `~(nb = 0)` THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; READ_MEMORY_BYTES_TRIVIAL;
                  list_of_seq; num_of_bytelist; keccak_squeeze];

      (*** The loop body: permute, extract a block of each, the test ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--2) THEN
      SHAKE256X4_STATES_TAC THEN
      LOCAL_PERMUTE_X4_TAC
       [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
        `keccak_squeeze i (S1:1600 word)`;
        `keccak_squeeze i (S2:1600 word)`;
        `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
        `read X30 s`] 3 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (4--11) THEN
      SHAKE256X4_STATES_TAC THEN
      LOCAL_EXTRACT_X4_TAC
       [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
        `0`; `136`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
        `read SP s`; `read X30 s`] 12 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (13--15) THEN
      SHAKE256X4_COUNTER_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
          NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[LE_REFL] THEN
      REWRITE_TAC[GSYM ADD1; keccak_squeeze; MULT_CLAUSES; EXP; DIV_1];

      (*** The exit from the loop ***)

      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** The remaining bytes, if any, through the buffers on the stack ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_join5` SHAKE256X4_A3 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `rest = 0` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--5) THEN
    SHAKE256X4_NBLOCKS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (6--7) THEN
    SHAKE256X4_REST_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (8--8) THENL
     [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (9--12) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `outlen = 136 * nb` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`rest = 0`; `136 * nb + rest = outlen`] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN

    (*** Otherwise one more block into the buffers, and the memcpys ***)

    SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (9--18) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
    SHAKE256X4_STATES_TAC THEN
    LOCAL_PERMUTE_X4_TAC
     [`read X0 s`; `keccak_squeeze nb (S0:1600 word)`;
      `keccak_squeeze nb (S1:1600 word)`; `keccak_squeeze nb (S2:1600 word)`;
      `keccak_squeeze nb (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 19 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (20--27) THEN
    SHAKE256X4_STATES_TAC THEN
    LOCAL_EXTRACT_X4_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
      `136`; `keccak_f1600(keccak_squeeze nb (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S3:1600 word))`; `pc:num`;
      `read SP s`; `read X30 s`] 28 THEN
    MAP_EVERY (fun (a,sv,k0,k) ->
      SHAKE256X4_TMP_TAC a THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (k0--k) THEN
      LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC k THEN
      LIBC_CALL_TAC "H_MEMCPY" MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
       [`read X0 s`; `read X1 s`; `read X2 s`;
        vsubst [sv,`S:1600 word`]
         `val(keccak_f1600(keccak_squeeze nb (S:1600 word))) MOD
          2 EXP (8 * rest)`;
        `read X30 s`] (k + 5))
     [`word_add (stackpointer:int64) (word 1176)`,`S0:1600 word`,29,33;
      `word_add (stackpointer:int64) (word 1312)`,`S1:1600 word`,39,43;
      `word_add (stackpointer:int64) (word 1448)`,`S2:1600 word`,49,52;
      `word_add (stackpointer:int64) (word 1584)`,`S3:1600 word`,58,61] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (67--67) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `outlen = 136 * nb + rest` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
                NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; keccak_squeeze];
    ALL_TAC] THEN

  (*** Zeroing the context and the buffers, the stack guard, the return ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC 4 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (10--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (32--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events depend on the address of the  *)
(* stack guard and on the input in3 given on the stack, and the number of    *)
(* iterations of the loop and whether there is a remainder depend on outlen. *)
(* The events are split at the intermediate points of the correctness proof, *)
(* from the end, with the public parts of the same assertions, and when the  *)
(* events so far consist of several parts they are kept as a variable e2 in  *)
(* the simulation.                                                           *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_F_EVENTS =
 `\(in0:int64) (in1:int64) (in2:int64) (in3:int64)
   (out0:int64) (out1:int64) (out2:int64) (out3:int64) (outlen:num)
   (inlen:num) (guard:int64) (mf:int64) (mc:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_end in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard mf mc
              pc stackpointer returnaddress)
    (APPEND
      (if outlen MOD 136 = 0
       then f_ev_rest0 in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                       guard mf mc pc stackpointer returnaddress
       else f_ev_rest in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard
                      mf mc pc stackpointer returnaddress)
      (APPEND
        (if outlen DIV 136 = 0
         then f_ev_skip in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                        guard mf mc pc stackpointer returnaddress
         else APPEND
               (f_ev_epil in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                          guard mf mc pc stackpointer returnaddress)
               (APPEND
                 (ENUMERATEL (outlen DIV 136)
                   (\i. f_ev_loop in0 in1 in2 in3 out0 out1 out2 out3 outlen
                                  inlen guard mf mc pc stackpointer
                                  returnaddress i))
                 (f_ev_prol in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                            guard mf mc pc stackpointer returnaddress)))
        (f_ev_absorb in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard
                     mf mc pc stackpointer returnaddress)))
   :(uarch_event)list`;;

let SHAKE256X4_PUBLIC t =
  let vs,bod = strip_abs t
  and priv = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
              `S3:1600 word`; `inp0:byte list`; `inp1:byte list`;
              `inp2:byte list`; `inp3:byte list`] in
  list_mk_abs(vs,list_mk_conj
   (filter (fun c -> not(exists (fun v -> vfree_in v c) priv))
           (conjuncts bod)));;

let SHAKE256X4_ALLOWED =
  [`pc:num`; `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`;
   `out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
   `inlen:num`; `guard:int64`; `mf:int64`; `mc:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `e2:(uarch_event)list`];;

(*** EXISTS_E2_TAC with nb and rest expanded, allowing the f_ev_... ***)

let SHAKE256X4_EXISTS_E2_TAC =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  W(fun (asl,_) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `outlen DIV 136 = nb` || c = `outlen MOD 136 = rest`
      then SYM th else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths) THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
     [REFL_TAC; SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx]) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV CONS_TO_APPEND_CONV)) THEN
    TRY(GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx));;

let SHAKE256X4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name safety_th]);;

let SHAKE256X4_LIBC_SAFE_CALL_TAC name n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true
      MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC th
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name th]);;

(*** The start of a part, where the events e2 so far may be given ***)

let SHAKE256X4_SAFE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

(*** The same keeping e2 as a variable, when given in several parts ***)

let SHAKE256X4_SAFE_INIT_OPAQUE_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  TRY(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && name_of l = "e2" && not(is_var r)
    then ASSUME_TAC(SYM th) THEN PURE_REWRITE_TAC[SYM th]
    else NO_TAC));;

(*** The final step of a part, with nb and rest expanded in the events, ***)
(*** and if needed the events reassociated to the right                ***)

let SHAKE256X4_UNABBREV_TAC =
  MAP_EVERY (fun t ->
    TRY(FIRST_X_ASSUM(fun th ->
      if concl th = t then SUBST_ALL_TAC(SYM th) else NO_TAC)))
   [`outlen DIV 136 = nb`; `outlen MOD 136 = rest`];;

let SHAKE256X4_DISCHARGE_TAC =
  SHAKE256X4_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SHAKE256X4_DISCHARGE_ASSOC_TAC =
  SHAKE256X4_UNABBREV_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; APPEND_NIL] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** Zeroing the context and the absorption ***)

let SHAKE256X4_SAFE_ABSORB_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (3--13) THEN
  SHAKE256X4_CTX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (14--32) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC 32 THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 37 THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ABSORB"
   ([`e:(uarch_event)list`; `read X20 s`; `read X21 s`; `read X28 s`;
     `read X27 s`; `read X26 s`; `inlen:num`;
     `read (memory :> bytes(in0,inlen)) s`;
     `read (memory :> bytes(in1,inlen)) s`;
     `read (memory :> bytes(in2,inlen)) s`;
     `read (memory :> bytes(in3,inlen)) s`;
     `read (memory :> wbytes (read X20 s)) s:1600 word`;
     `read (memory :> wbytes (word_add (read X20 s) (word 200))) s:1600 word`;
     `read (memory :> wbytes (word_add (read X20 s) (word 400))) s:1600 word`;
     `read (memory :> wbytes (word_add (read X20 s) (word 600))) s:1600 word`;
     `pc:num`; `read SP s`]) 38 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

(*** The whole blocks ***)

let SHAKE256X4_SAFE_BLOCKS_TAC =
  ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
   [SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
    SHAKE256X4_LS_TAC `nb = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nb:num` `pc + mlkem_shake256x4_loop2`
   `pc + mlkem_shake256x4_loop2_exit`
    (SHAKE256X4_PUBLIC SHAKE256X4_INV) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
    SHAKE256X4_LS_TAC `~(nb = 0)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN
    SHAKE256X4_DISCHARGE_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SHAKE256X4_SAFE_INIT_TAC THEN
    SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--2) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (4--11) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read SP s`;
      `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (13--15) THEN
    SHAKE256X4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`];
      ALL_TAC] THEN
    SHAKE256X4_DISCHARGE_TAC;

    REWRITE_TAC[] THEN SHAKE256X4_SAFE_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC];;

(*** The remaining bytes ***)

let SHAKE256X4_SAFE_REST_TAC =
  ASM_CASES_TAC `rest = 0` THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--5) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (6--7) THEN
  SHAKE256X4_REST_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (8--8) THENL
   [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (9--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (9--18) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 19 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (20--27) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read SP s`;
    `read X30 s`] 28 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (k0--k) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC k THEN
    SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMCPY" (k + 5))
   [29,33; 39,43; 49,52; 58,61] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (67--67) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

(*** Zeroing, the stack guard and the return ***)

let SHAKE256X4_SAFE_END_TAC =
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (1--4) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC 4 THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (10--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC (32--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen guard
                 pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1728),1728] /\
           ALLPAIRS nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1728),1728]
            [in0,inlen; in1,inlen; in2,inlen; in3,inlen; stackpointer,16;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O3_mc /\
                     read PC s = word (pc + mlkem_shake256x4) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS
                      [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                     read (memory :> bytes64 stackpointer) s = in3 /\
                     read (memory :> bytes64(word_add stackpointer (word 8)))
                          s =
                     word inlen /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events in0 in1 in2 in3 out0 out1 out2 out3
                               outlen inlen guard mf mc pc
                               (word_sub stackpointer (word 1728))
                               returnaddress /\
                        memaccess_inbounds e2
                         [in0,inlen; in1,inlen; in2,inlen; in3,inlen;
                          out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          stackpointer,16;
                          word_sub stackpointer (word 1728),1728;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el]
                         [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          word_sub stackpointer (word 1728),1728]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                   memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                   memory :> bytes(word_sub stackpointer (word 1728),1728)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memset_safety_contract; memcpy_safety_contract] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET")
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY")) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256X4_GCC12_O3_ABSORB "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC SHAKE256X4_F_EVENTS THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256X4_GCC12_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_shake256x4_join5`
   (SHAKE256X4_PUBLIC SHAKE256X4_A3) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_END_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_shake256x4_loop2_exit`
   (SHAKE256X4_PUBLIC SHAKE256X4_A2) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_REST_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_shake256x4_join3`
   (SHAKE256X4_PUBLIC SHAKE256X4_A1) THEN
  CONJ_TAC THENL [SHAKE256X4_SAFE_ABSORB_TAC; SHAKE256X4_SAFE_BLOCKS_TAC]);;
