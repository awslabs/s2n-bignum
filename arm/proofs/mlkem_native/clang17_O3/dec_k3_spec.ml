(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-768 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem768_dec from mlkem-     *)
(* native's portable C implementation compiled by clang 17 with -O3 (see     *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem768_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem768_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem768_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time (a loop of 34 iterations of 32       *)
(* bytes), computes J of z (in the key) followed by the ciphertext with      *)
(* mlkem_shake256 into a buffer of 32 bytes on the stack, replaces it by K'  *)
(* if the ciphertexts are equal, again in constant time, and only then       *)
(* copies it to the shared secret, as two 16-byte loads and stores. In both  *)
(* cases it zeroes its buffers. The statements are those of the gcc 12 -O2   *)
(* image, except for the stack: the function saves its registers, aligns the *)
(* buffers to 32 bytes below them, and the frame also includes the 16656     *)
(* bytes of mlkem768_indcpa_enc below the buffers. It is verified in the     *)
(* whole image (see libmlkem.ml), using the theorems for mlkem768_check_sk,  *)
(* mlkem768_indcpa_dec, mlkem_sha3_512, mlkem768_indcpa_enc and              *)
(* mlkem_shake256 in the image and the contracts for memset and memcpy.      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/check_sk_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_dec_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_enc_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/shake256_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem768_dec:
       +0x0: stp     x29, x30, [sp, #-64]!
       +0x4: stp     x28, x23, [sp, #16]
       +0x8: stp     x22, x21, [sp, #32]
       +0xc: stp     x20, x19, [sp, #48]
      +0x10: mov     x29, sp
      +0x14: sub     x9, sp, #0x500
      +0x18: and     sp, x9, #0xffffffffffffffe0
      +0x1c: adrp    x8, <page>
      +0x20: mov     x19, x0
      +0x24: mov     x0, x2
      +0x28: mov     x21, x2
      +0x2c: mov     x20, x1
      +0x30: ldr     x8, [x8, #4088]
      +0x34: ldr     x8, [x8]
      +0x38: str     x8, [sp, #1272]
      +0x3c: bl      <mlkem768_check_sk>
      +0x40: mov     w22, w0
      +0x44: cbnz    w0, <mlkem768_dec+0x1c0>
      +0x48: add     x0, sp, #0x4a0
      +0x4c: mov     x1, x20
      +0x50: mov     x2, x21
      +0x54: bl      <mlkem768_indcpa_dec>
      +0x58: mov     w22, w0
      +0x5c: cbnz    w0, <mlkem768_dec+0x1c0>
      +0x60: ldr     q0, [x21, #2336]
      +0x64: add     x0, sp, #0x460
      +0x68: ldr     q1, [x21, #2352]
      +0x6c: add     x1, sp, #0x4a0
      +0x70: mov     w2, #0x40
      +0x74: add     x22, x21, #0x480
      +0x78: str     q0, [sp, #1216]
      +0x7c: add     x23, sp, #0x460
      +0x80: str     q1, [sp, #1232]
      +0x84: bl      <mlkem_sha3_512>
      +0x88: add     x3, x23, #0x20
      +0x8c: mov     x0, sp
      +0x90: add     x1, sp, #0x4a0
      +0x94: mov     x2, x22
      +0x98: mov     x23, sp
      +0x9c: bl      <mlkem768_indcpa_enc>
      +0xa0: mov     w22, w0
      +0xa4: cbnz    w0, <mlkem768_dec+0x1c0>
      +0xa8: movi    v0.2d, #0x0
      +0xac: mov     x8, xzr
      +0xb0: movi    v1.2d, #0x0
      +0xb4: movi    v2.2d, #0x0
      +0xb8: movi    v3.2d, #0x0
      +0xbc: add     x9, x20, x8
      +0xc0: add     x10, x23, x8
      +0xc4: add     x8, x8, #0x20
      +0xc8: cmp     x8, #0x440
      +0xcc: ldp     q4, q5, [x9]
      +0xd0: ldp     q6, q7, [x10]
      +0xd4: eor     v4.16b, v6.16b, v4.16b
      +0xd8: orr     v2.16b, v4.16b, v2.16b
      +0xdc: eor     v5.16b, v7.16b, v5.16b
      +0xe0: orr     v3.16b, v5.16b, v3.16b
      +0xe4: eor     v0.16b, v4.16b, v0.16b
      +0xe8: eor     v1.16b, v5.16b, v1.16b
      +0xec: b.ne    <mlkem768_dec+0xbc>
      +0xf0: orr     v2.16b, v3.16b, v2.16b
      +0xf4: mov     w22, wzr
      +0xf8: ext     v3.16b, v2.16b, v2.16b, #8
      +0xfc: mov     x8, sp
     +0x100: eor     v0.16b, v1.16b, v0.16b
     +0x104: add     x0, x8, #0x20
     +0x108: ext     v1.16b, v0.16b, v0.16b, #8
     +0x10c: mov     x1, x20
     +0x110: mov     w2, #0x440
     +0x114: orr     v2.8b, v2.8b, v3.8b
     +0x118: fmov    x9, d2
     +0x11c: eor     v0.8b, v0.8b, v1.8b
     +0x120: fmov    x11, d0
     +0x124: orr     x9, x9, x9, lsr #32
     +0x128: lsr     x10, x9, #16
     +0x12c: orr     w9, w9, w10
     +0x130: eor     x10, x11, x11, lsr #32
     +0x134: orr     w9, w9, w9, lsr #8
     +0x138: eor     x10, x10, x10, lsr #16
     +0x13c: sub     w9, w22, w9, uxtb
     +0x140: lsr     x11, x10, #8
     +0x144: eor     w10, w10, w11
     +0x148: eor     w9, w10, w9, lsr #16
     +0x14c: ldr     q0, [x21, #2368]
     +0x150: ldr     q1, [x21, #2384]
     +0x154: eor     w21, w9, w10
     +0x158: stp     q0, q1, [sp]
     +0x15c: bl      <memcpy>
     +0x160: add     x0, sp, #0x4a0
     +0x164: mov     x2, sp
     +0x168: mov     w1, #0x20
     +0x16c: mov     w3, #0x460
     +0x170: add     x20, sp, #0x4a0
     +0x174: bl      <mlkem_shake256>
     +0x178: mov     x8, xzr
     +0x17c: sub     w9, w22, w21, uxtb
     +0x180: add     x10, sp, #0x460
     +0x184: ldrb    w11, [x20, x8]
     +0x188: mov     w12, w9
     +0x18c: ldrb    w13, [x10, x8]
     +0x190: lsr     w12, w12, #16
     +0x194: and     w11, w11, w12
     +0x198: bic     w13, w13, w12
     +0x19c: orr     w11, w11, w13
     +0x1a0: strb    w11, [x20, x8]
     +0x1a4: add     x8, x8, #0x1
     +0x1a8: cmp     x8, #0x20
     +0x1ac: b.ne    <mlkem768_dec+0x184>
     +0x1b0: mov     w22, wzr
     +0x1b4: ldr     q0, [sp, #1184]
     +0x1b8: ldr     q1, [sp, #1200]
     +0x1bc: stp     q0, q1, [x19]
     +0x1c0: mov     x0, sp
     +0x1c4: mov     w1, wzr
     +0x1c8: mov     w2, #0x460
     +0x1cc: mov     x19, sp
     +0x1d0: bl      <memset>
     +0x1d4: movi    v0.2d, #0x0
     +0x1d8: add     x8, sp, #0x460
     +0x1dc: str     q0, [sp, #1168]
     +0x1e0: str     q0, [sp, #1152]
     +0x1e4: str     q0, [sp, #1136]
     +0x1e8: str     q0, [sp, #1120]
     +0x1ec: str     q0, [sp, #1232]
     +0x1f0: add     x8, sp, #0x4a0
     +0x1f4: str     q0, [sp, #1216]
     +0x1f8: str     q0, [sp, #1200]
     +0x1fc: str     q0, [sp, #1184]
     +0x200: adrp    x8, <page>
     +0x204: ldr     x8, [x8, #4088]
     +0x208: ldr     x9, [sp, #1272]
     +0x20c: ldr     x8, [x8]
     +0x210: cmp     x8, x9
     +0x214: b.ne    <mlkem768_dec+0x234>
     +0x218: mov     w0, w22
     +0x21c: mov     sp, x29
     +0x220: ldp     x20, x19, [sp, #48]
     +0x224: ldp     x22, x21, [sp, #32]
     +0x228: ldp     x28, x23, [sp, #16]
     +0x22c: ldp     x29, x30, [sp], #64
     +0x230: ret
     +0x234: bl      <stack_chk_fail>
 ***)

let MLKEM_NATIVE_DEC_K3_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "plt_memcpy"; layout_range "plt_memset";
    layout_range "mlkem768_dec"];;

let KD3_EXEC = MLKEM_NATIVE_DEC_K3_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-768, the input check of    *)
(* FIPS 203 in terms of the result of mlkem768_check_sk, and the address of  *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_768_STMT =
  `!ek m r. LENGTH(kpke_encrypt mlkem768 ek m r) = 1088`;;

let KPKE_ENCRYPT_LENGTH_768 = assume_spec KPKE_ENCRYPT_LENGTH_768_STMT;;

let KPKE_DECRYPT_LENGTH_768_STMT =
  `!dk c. LENGTH(kpke_decrypt mlkem768 dk c) = 32`;;

let KPKE_DECRYPT_LENGTH_768 = assume_spec KPKE_DECRYPT_LENGTH_768_STMT;;

let KD3_CHECK_STMT =
  `!dk c. LENGTH dk = 2400 /\ LENGTH c = 1088
          ==> (mlkem_decaps_check mlkem768 dk c <=>
               num_of_bytelist(mlkem_slice 2336 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk)))`;;

let KD3_CHECK = assume_spec KD3_CHECK_STMT;;

let KD3_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let KD3_ALIGNED_16_32 = assume_spec KD3_ALIGNED_16_32_STMT;;

let KD3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 16672)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 16672 else 16656))`;;

let KD3_BUFFER_ADDRESS = assume_spec KD3_BUFFER_ADDRESS_STMT;;

let KD3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD3_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_CHECK_SK_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_DEC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KD3_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,2400)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,1152; 1152,1184; 2336,32; 2368,32]
    else NO_TAC);;

let KD3_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 1152 1184 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list))`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 17;;

let KD3_FAIL_TAC =
  ARM_STEPS_TAC KD3_EXEC (18--24) THEN LIBC_PLT_TAC KD3_EXEC 24 THEN
  LIBC_CALL_TAC "H_MEMSET" KD3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC KD3_EXEC (30--41) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (42--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext. The invariant   *)
(* of the comparison loop at iteration i states that the OR accumulator Q3   *)
(* is zero if and only if the first 16 * i bytes of the ciphertext and of c' *)
(* are equal, and the invariant of the conditional move at iteration i that  *)
(* the first i bytes at ss are those of K' if the ciphertexts are equal and  *)
(* those of the result of J otherwise, and the others still those of the     *)
(* result of J. The frame has the facts needed after both loops.             *)
(* ------------------------------------------------------------------------- *)

let KD3_MP = `kpke_decrypt mlkem768 (mlkem_slice 0 1152 dk) c`;;

let KD3_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem768 (mlkem_slice 0 1152 dk) c)
                  (mlkem_slice 2336 32 dk))`;;

let KD3_KP = mk_comb(`mlkem_slice 0 32`,KD3_GG);;

let KD3_RR = mk_comb(`mlkem_slice 32 32`,KD3_GG);;

let KD3_CP = list_mk_comb(`kpke_encrypt mlkem768`,
  [`mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR]);;

let KD3_ZZ = `mlkem_slice 2368 32 (dk:byte list)`;;

let KD3_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 2368 32 dk) c)) 32`;;

let KD3_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD3_CP));;

let KD3_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD3_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD3_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD3_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD3_ZZ),`ZZ:num`;
         KD3_EQ,`EQ:bool`] tm;;

let KD3_FRAME b = KD3_SUBST(parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word %d) /\\
  read X29 s = word_add stackpointer (word 17952) /\\
  read X24 s = x24_init /\\ read X25 s = x25_init /\\
  read X26 s = x26_init /\\ read X27 s = x27_init /\\
  read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17952))) s =
  x29_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17960))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 17968))) s =
  x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17976))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17984))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17992))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 18000))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 18008))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196600))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196584))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word 196560))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  b (b + 1272) (b + 1120)));;

let KD3_INV b = KD3_SUBST(parse_term(Printf.sprintf
 "\\i s. read X8 s = word(32 * i) /\\
        read X19 s = ss /\\ read X20 s = ct /\\ read X21 s = sk /\\
        read X23 s = word_add stackpointer (word %d) /\\
        (read Q2 s = word 0 /\\ read Q3 s = word 0 <=>
         num_of_bytelist c MOD 2 EXP (256 * i) = CP MOD 2 EXP (256 * i)) /\\
        read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\\
        read (memory :> bytes(word_add stackpointer (word %d),1088)) s = CP /\\
        read (memory :> bytes128 (word_add sk (word 2368))) s =
        word(ZZ MOD 2 EXP 128) /\\
        read (memory :> bytes128 (word_add sk (word 2384))) s =
        word(ZZ DIV 2 EXP 128) /\\ FRAME"
  b b));;

let KD3_INV_FRAME b =
  let inv = KD3_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD3_FRAME b,`FRAME:bool`] bod);;

let KD3_CMOV_INV b = KD3_SUBST(parse_term(Printf.sprintf
 "\\i s. read X8 s = word i /\\
        read X9 s = (if EQ then word 0 else word 4294967041) /\\
        read X10 s = word_add stackpointer (word %d) /\\
        read X20 s = word_add stackpointer (word %d) /\\
        read X19 s = ss /\\
        read (memory :> bytes(word_add stackpointer (word %d),i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add (word_add stackpointer (word %d))
                                       (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"
  (b + 1120) (b + 1184) (b + 1184) (b + 1184)));;

let KD3_CMOV_INV_FRAME b =
  let inv = KD3_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD3_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption, G of m' and h, and the reencryption.                          *)
(* ------------------------------------------------------------------------- *)

let KD3_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 1184),`a:int64`;
           KD3_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 2336 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_768];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD3_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 2336 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_768] THEN ARITH_TAC;
    ALL_TAC];;

let KD3_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 1120) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD3_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD3_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD3_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 2336):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 2368):int64` THEN
  ARM_STEPS_TAC KD3_EXEC (1--7) THEN KD3_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (8--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (9--16) THEN KEM_GOT_TAC THEN
  KD3_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD3_EXEC (18--23) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `mlkem_slice 0 1152 (dk:byte list)`; `c:byte list`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 24 THEN
  ARM_STEPS_TAC KD3_EXEC (25--36) THEN
  KEM_JOIN_TAC (KEM_SP(b + 1216)) `mlkem_slice 2336 32 (dk:byte list)`
    (st 36) THEN
  KD3_G_INPUT_TAC b (st 36) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD3_MP),
            `mlkem_slice 2336 32 (dk:byte list)`);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  KD3_KR_TAC b (st 37) THEN
  ARM_STEPS_TAC KD3_EXEC (38--43) THEN KEM_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_768]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 44 THEN
  ARM_STEPS_TAC KD3_EXEC (45--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test.                      *)
(* ------------------------------------------------------------------------- *)

let KD3_TEST_STMT =
  `!i. i < 34
       ==> (val(word_add (word(32 * i)) (word 18446744073709550560):int64) = 0
            <=> ~(i + 1 < 34))`;;

let KD3_TEST = assume_spec KD3_TEST_STMT;;

let KD3_MOD_STEP2_STMT =
  `!n m i. n MOD 2 EXP (256 * (i + 1)) = m MOD 2 EXP (256 * (i + 1)) <=>
           n MOD 2 EXP (256 * i) = m MOD 2 EXP (256 * i) /\
           (n DIV 2 EXP (256 * i)) MOD 2 EXP 128 =
           (m DIV 2 EXP (256 * i)) MOD 2 EXP 128 /\
           (n DIV 2 EXP (256 * i + 128)) MOD 2 EXP 128 =
           (m DIV 2 EXP (256 * i + 128)) MOD 2 EXP 128`;;

let KD3_MOD_STEP2 = assume_spec KD3_MOD_STEP2_STMT;;

let KD3_OR_STEP2_STMT =
  `!q:int128 a b.
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ a MOD 2 EXP 128 = b MOD 2 EXP 128`;;

let KD3_OR_STEP2 = assume_spec KD3_OR_STEP2_STMT;;

let KD3_CHUNK_TAC norm a v k =
  let bth = MP (ARITH_RULE (subst [k,`k:num`]
                  `i < 34 ==> 16 * k + 16 <= 1088`))
               (ASSUME `i < 34`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1088`) && vv = v ->
          let lth = SPECL [a; `1088`; k; v; s] KEM_BYTES128 in
          let fth = REWRITE_RULE
                      [ARITH_RULE `16 * (2 * i) = 32 * i`;
                       ARITH_RULE `16 * (2 * i + 1) = 32 * i + 16`;
                       ARITH_RULE `128 * (2 * i) = 256 * i`;
                       ARITH_RULE `128 * (2 * i + 1) = 256 * i + 128`]
                      (MP lth (CONJ th bth)) in
          ASSUME_TAC(if norm then CONV_RULE(ONCE_DEPTH_CONV
                                    NORMALIZE_RELATIVE_ADDRESS_CONV) fth
                     else fth)
    | _ -> NO_TAC);;

let KD3_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD3_CHUNK_TAC true `ct:int64` `num_of_bytelist c` `2 * i` THEN
  KD3_CHUNK_TAC true `ct:int64` `num_of_bytelist c` `2 * i + 1` THEN
  KD3_CHUNK_TAC true (KEM_SP b) (mk_comb(`num_of_bytelist`,KD3_CP))
                `2 * i` THEN
  KD3_CHUNK_TAC false (KEM_SP b) (mk_comb(`num_of_bytelist`,KD3_CP))
                `2 * i + 1` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_TEST) (ASSUME `i < 34`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_iff(concl th) &&
      lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`)) THEN
    REWRITE_TAC[KD3_OR_STEP2; KD3_MOD_STEP2] THEN CONV_TAC TAUT;
    CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC];;

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 255, J of z and the ciphertext copied after  *)
(* z with memcpy, and the mask for the bytes.                                *)
(* ------------------------------------------------------------------------- *)

let KD3_DONE_TAC =
  SUBGOAL_THEN
   (mk_iff(`q2:int128 = word 0 /\ q3:int128 = word 0`,KD3_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) &&
         lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD3_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_768] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD3_MASK_TAC s =
  let x21 = mk_comb(`read X21`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      let e = rand c in
      let eth = BITBLAST_RULE
        (mk_eq(e,`if q2:int128 = word 0 /\ q3:int128 = word 0
                  then word 0:int64 else word 65535`)) in
      ASSUME_TAC(TRANS th eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') &&
           lhand(concl th') = `q2:int128 = word 0 /\ q3:int128 = word 0`
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD3_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP b,`a:int64`]
     `read (memory :> bytes(a,1120)) s =
      num_of_bytelist(APPEND (mlkem_slice 2368 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1120 = 32 + 1088`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 2368 32 (dk:byte list)) c) = 1120`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD3_EXIT_A_TAC b =
  let st n = "s"^string_of_int n in
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  ENSURES_INIT_TAC "s0" THEN KD3_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--26) THEN
  KD3_MASK_TAC (st 26) THEN
  ARM_STEPS_TAC KD3_EXEC (27--28) THEN
  KEM_JOIN_TAC (KEM_SP b) KD3_ZZ (st 28) THEN
  LIBC_PLT_TAC KD3_EXEC 28 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 33 THEN
  KD3_J_INPUT_TAC b (st 33) THEN
  ARM_STEPS_TAC KD3_EXEC (34--39) THEN KEM_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 2368 32 (dk:byte list)) c`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC KD3_EXEC (41--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD3_CMOV_TEST_STMT =
  `!i. i < 32
       ==> (val(word_add (word i) (word 18446744073709551585):int64) = 0 <=>
            ~(i + 1 < 32))`;;

let KD3_CMOV_TEST = assume_spec KD3_CMOV_TEST_STMT;;

let KD3_CMOV_BODY_TAC b =
  let nrm = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 1120); `32`; mk_comb(`num_of_bytelist`,KD3_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  SUBGOAL_THEN
   (KD3_SUBST(subst [KEM_SP(b + 1184),`ss:int64`]
     `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
      KB DIV 2 EXP (8 * i)`))
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC(nrm th1) THEN ASSUME_TAC(nrm th2))] THEN
  ARM_STEPS_TAC KD3_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
    SPEC_TAC(KD3_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD3_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; KEM_DIV_BYTE] THEN
    RULE_ASSUM_TAC(fun th ->
      if can (find_term (fun t -> t = `31 - i`)) (concl th)
      then nrm th else th) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[]];;

let KD3_FINAL_TAC =
  REWRITE_TAC[mlkem768; MLKEM_DECAPS_ALT] THEN REWRITE_TAC[GSYM mlkem768] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD3_CP,`c:byte list`),KD3_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_768];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(*** The 32 bytes at the shared secret after the copy from the buffer ***)

let KD3_COPY_TAC s =
  MP_TAC(SPECL [`ss:int64`;
                KD3_SUBST `(if EQ then KP else KB) MOD 2 EXP (8 * 32)`;
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

let KD3_EXIT_B_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  KEM_HALVES_TAC (KEM_SP(b + 1184)) THEN
  ARM_STEPS_TAC KD3_EXEC (1--4) THEN
  KD3_COPY_TAC "s4" THEN
  ARM_STEPS_TAC KD3_EXEC (5--9) THEN
  LIBC_PLT_TAC KD3_EXEC 9 THEN
  LIBC_CALL_TAC "H_MEMSET" KD3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 14 THEN
  ARM_STEPS_TAC KD3_EXEC (15--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (27--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD3_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy. The      *)
(* decapsulation key dk of 2400 bytes is at sk and the ciphertext c of 1088  *)
(* bytes at ct, and if they pass the check of FIPS 203, the shared secret of *)
(* 32 bytes written at ss is that of mlkem_decaps_internal mlkem768 dk c in  *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it    *)
(* returns -5. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix from the seed in the key and that the stack does not        *)
(* contain address 0, for mlkem768_indcpa_enc. The stack is the 64 bytes of  *)
(* saved registers, the buffers of 1280 bytes aligned to 32 bytes below them *)
(* (with up to 16 bytes of padding) and the 16656 used by                    *)
(* mlkem768_indcpa_enc below the buffers. The proof is by cases on whether   *)
(* the stack pointer is a multiple of 32, which gives the address b of the   *)
(* buffers, at offsets 0 (c' and then z and the ciphertext), 1120 (K' and    *)
(* r') and 1184 (m' and h), and on the check of the key.                     *)
(* ------------------------------------------------------------------------- *)

let KD3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 18016 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 18016):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD3_CHECK; ASSUME `LENGTH(dk:byte list) = 2400`;
           ASSUME `LENGTH(c:byte list) = 1088`] THEN
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
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1152 (dk:byte list)) = 1152 /\
    LENGTH(mlkem_slice 1152 1184 (dk:byte list)) = 1184 /\
    LENGTH(mlkem_slice 2336 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 2368 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1152`; `32`; `1152`; `1184`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1152 + 32 <= 1184`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD3_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `34` `pc + mlkem768_dec_loop1`
   `pc + mlkem768_dec_loop1_exit`
   (KD3_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD3_PART1_TAC b; KD3_BODY_TAC b;
    ENSURES_WHILE_UP2_TAC `32` `pc + mlkem768_dec_loop2`
     `pc + mlkem768_dec_loop2_exit`
     (KD3_CMOV_INV_FRAME b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD3_EXIT_A_TAC b; KD3_CMOV_BODY_TAC b; KD3_EXIT_B_TAC b]];;

let KD3_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--7) THEN KD3_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (8--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (9--16) THEN KEM_GOT_TAC THEN
  KD3_CHECK_TAC THEN KD3_FAIL_TAC;;

let KD3_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD3_OK_TAC b; KD3_BAD_TAC];;

let MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 2400 /\ LENGTH c = 1088 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 18016),18016) /\
        nonoverlapping (ct,1088) (word pc,libmlkem_size) /\
        nonoverlapping (sk,2400) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 18016),18016) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 18016),18016)]
         [(ct,1088); (sk,2400); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem768_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,2400)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem768 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist(mlkem_decaps_internal mlkem768 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem768 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 18016),18016)])`;;

let MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_indcpa_enc) and the safety contract for memcpy. The  *)
(* events depend only on the addresses and on the encapsulation key ek in    *)
(* the decapsulation key and the hash h stored with it, through the check of *)
(* the hash, given by the combined theorem for mlkem768_check_sk, and the    *)
(* reencryption, but not on the secret key, z or the ciphertext: the         *)
(* comparison of the ciphertexts and the selection of the shared secret are  *)
(* loops in constant time. The buffers are kept at their offset from the     *)
(* stack pointer as a conditional, and the invariants of the loops have only *)
(* the pointers and the frame.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD3_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if aligned 32 sp
   then (if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
      then APPEND
            (APPEND (f_ev_exitb_a ss ct sk guard mf mc pc sp ra)
              (APPEND (ENUMERATEL 32
                        (\i. f_ev_cmov_a ss ct sk guard mf mc pc sp ra i))
                      (f_ev_exita_a ss ct sk guard mf mc pc sp ra)))
            (APPEND (ENUMERATEL 34
                      (\i. f_ev_cmp_a ss ct sk guard mf mc pc sp ra i))
                    (f_ev_prol_a ss ct sk guard mf mc pc sp ra ek h))
      else f_ev_bad_a ss ct sk guard mf mc pc sp ra ek h)
   else (if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
      then APPEND
            (APPEND (f_ev_exitb_u ss ct sk guard mf mc pc sp ra)
              (APPEND (ENUMERATEL 32
                        (\i. f_ev_cmov_u ss ct sk guard mf mc pc sp ra i))
                      (f_ev_exita_u ss ct sk guard mf mc pc sp ra)))
            (APPEND (ENUMERATEL 34
                      (\i. f_ev_cmp_u ss ct sk guard mf mc pc sp ra i))
                    (f_ev_prol_u ss ct sk guard mf mc pc sp ra ek h))
      else f_ev_bad_u ss ct sk guard mf mc pc sp ra ek h)
   :(uarch_event)list`;;

let KD3_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`; `i:num`;
   `f_ev_cmp_a:int64->int64->int64->int64->int64->int64->num->int64->
                int64->num->(uarch_event)list`;
   `f_ev_cmov_a:int64->int64->int64->int64->int64->int64->num->int64->
                 int64->num->(uarch_event)list`;
   `f_ev_cmp_u:int64->int64->int64->int64->int64->int64->num->int64->
                int64->num->(uarch_event)list`;
   `f_ev_cmov_u:int64->int64->int64->int64->int64->int64->num->int64->
                 int64->num->(uarch_event)list`];;

let KD3_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let KD3_SAFE_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE KD3_EV_CONV th else th);;

(*** The events of the goal are normalized in the same way as those of the
     assumptions before the events of the loop are unified. ***)

let KD3_DISCHARGE_EXIT_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(RAND_CONV KD3_EV_CONV) THEN FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let KD3_SAFE_CALL_TAC name ilist n =
  KD3_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,KD3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD3_SAFE_FRAME b = parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word %d) /\\
  read X29 s = word_add stackpointer (word 17952) /\\
  read X24 s = x24_init /\\ read X25 s = x25_init /\\
  read X26 s = x26_init /\\ read X27 s = x27_init /\\
  read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17952))) s =
  x29_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17960))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 17968))) s =
  x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17976))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17984))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17992))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 18000))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 18008))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196600))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196584))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word 196560))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev"
  b (b + 1272));;

let KD3_SAFE_WITH_FRAME b inv =
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD3_SAFE_FRAME b,`FRAME:bool`] bod);;

let KD3_SAFE_INV b = KD3_SAFE_WITH_FRAME b (parse_term(Printf.sprintf
 "\\i s. read X8 s = word(32 * i) /\\
        read X19 s = ss /\\ read X20 s = ct /\\ read X21 s = sk /\\
        read X23 s = word_add stackpointer (word %d) /\\ FRAME" b));;

let KD3_SAFE_CMOV_INV b = KD3_SAFE_WITH_FRAME b (parse_term(Printf.sprintf
 "\\i s. read X8 s = word i /\\
        read X10 s = word_add stackpointer (word %d) /\\
        read X20 s = word_add stackpointer (word %d) /\\
        read X19 s = ss /\\ FRAME" (b + 1120) (b + 1184)));;

let KD3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP
         MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
         sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CHECK_SK_K3_CLANG17_O3_IMAGE_SUBROUTINE_FULL "H_CHECK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHAKE256" THEN
  CONCRETIZE_F_EVENTS_TAC KD3_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 18016):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
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
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1152 (dk:byte list)) = 1152 /\
    LENGTH(mlkem_slice 1152 1184 (dk:byte list)) = 1184 /\
    LENGTH(mlkem_slice 2336 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 2368 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1152`; `32`; `1152`; `1184`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1152 + 32 <= 1184`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th))) THEN
  ABBREV_TAC `ekk = mlkem_slice 1152 1184 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 2336 32 (dk:byte list)`;;

let KD3_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KD3_SK_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--7) THEN KD3_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (8--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (9--16) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 17;;

let KD3_SAFE_PART1_TAC =
  KD3_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD3_EXEC (18--23) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  ARM_STEPS_TAC KD3_EXEC (25--36) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  ARM_STEPS_TAC KD3_EXEC (38--43) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 44 THEN
  ARM_STEPS_TAC KD3_EXEC (45--51) THEN
  KD3_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_TEST) (ASSUME `i < 34`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_EXIT_A_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--28) THEN LIBC_PLT_TAC KD3_EXEC 28 THEN
  KD3_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD3_SAFE_ALLOWED) 33 THEN
  ARM_STEPS_TAC KD3_EXEC (34--39) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `1120`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC KD3_EXEC (41--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  KD3_DISCHARGE_EXIT_TAC;;

let KD3_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--9) THEN LIBC_PLT_TAC KD3_EXEC 9 THEN
  KD3_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD3_SAFE_ALLOWED) 14 THEN
  ARM_STEPS_TAC KD3_EXEC (15--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (27--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  KD3_DISCHARGE_EXIT_TAC;;

let KD3_SAFE_BAD_TAC =
  KD3_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD3_EXEC (18--24) THEN LIBC_PLT_TAC KD3_EXEC 24 THEN
  KD3_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD3_SAFE_ALLOWED) 29 THEN
  ARM_STEPS_TAC KD3_EXEC (30--41) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (42--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_CASE_TAC b =
  SUBGOAL_THEN (subst [mk_small_numeral b,`b:num`]
   `aligned 16 (word_add stackpointer (word b):int64)`)
  ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (stackpointer:int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(RAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `34` `pc + mlkem768_dec_loop1`
    `pc + mlkem768_dec_loop1_exit`
     (KD3_SAFE_INV b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD3_SAFE_PART1_TAC; KD3_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem768_dec_loop2`
       `pc + mlkem768_dec_loop2_exit`
       (KD3_SAFE_CMOV_INV b) THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD3_SAFE_EXIT_A_TAC; KD3_SAFE_CMOV_BODY_TAC;
        KD3_SAFE_EXIT_B_TAC]];
    KD3_SAFE_BAD_TAC];;

let MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ss ct sk (dk:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH dk = 2400 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 18016),18016) /\
          nonoverlapping (ct,1088) (word pc,libmlkem_size) /\
          nonoverlapping (sk,2400) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 18016),18016) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 18016),18016)]
           [(ct,1088); (sk,2400); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem768_dec) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ss; ct; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,2400)) s = num_of_bytelist dk /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ss ct sk guard mf mc pc
                              (word_sub stackpointer (word 18016))
                              returnaddress
                              (mlkem_slice 1152 1184 dk)
                              (mlkem_slice 2336 32 dk) /\
                       memaccess_inbounds e2
                        [ct,1088; sk,2400; ss,32;
                         word_sub stackpointer (word 18016),18016;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_ntt_consts),
                         mlkem_poly_ntt_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem_poly_invntt_tomont_consts),
                         mlkem_poly_invntt_tomont_consts_size;
                         word(pc + mlkem_poly_compress_d4_consts),
                         mlkem_poly_compress_d4_consts_size;
                         word(pc + mlkem_poly_decompress_d10_consts),
                         mlkem_poly_decompress_d10_consts_size;
                         word(pc + mlkem_poly_tomsg_consts),
                         mlkem_poly_tomsg_consts_size]
                        [ss,32; word_sub stackpointer (word 18016),18016]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 18016),18016)])`;;

let MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
