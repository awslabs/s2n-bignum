(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-768 (FIPS 203 Algorithm 17, with the input  *)
(* check of Algorithm 20). This is the code for mlkem768_enc_derand from   *)
(* mlkem-native's portable C implementation compiled by clang 17 with -O2  *)
(* (see mlkem_native/README.md). The compiler has inlined                  *)
(* mlkem768_check_pk: the function decodes the key with                    *)
(* mlkem768_polyvec_frombytes into a buffer on the stack, reduces it with  *)
(* mlkem768_polyvec_reduce, encodes it again with                          *)
(* mlkem768_polyvec_tobytes, compares the result with the key in a loop of *)
(* 32 bytes per iteration, and zeroes the two buffers with memset. If the  *)
(* comparison fails it returns -4. Otherwise it hashes the key with        *)
(* mlkem_sha3_256, computes K and r as G of the message m (the 32 bytes at *)
(* coins) followed by that hash with mlkem_sha3_512, encrypts m with r by  *)
(* mlkem768_indcpa_enc into the ciphertext, and writes K as the shared     *)
(* secret. In both cases it zeroes its buffers. The statements are those   *)
(* of the gcc 12 -O2 image, except for the stack: the function saves its   *)
(* registers, aligns the buffers to 32 bytes below them, and the frame     *)
(* also includes the 17024 bytes of mlkem768_indcpa_enc below the buffers. *)
(* It is verified in the whole image (see libmlkem.ml), using the theorems *)
(* for mlkem768_polyvec_frombytes, mlkem768_polyvec_reduce,                *)
(* mlkem768_polyvec_tobytes, mlkem_sha3_256, mlkem_sha3_512 and            *)
(* mlkem768_indcpa_enc in the image and the contracts for memset.          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/check_pk_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_reduce_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_tobytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/indcpa_enc_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

let CHECKPK_OR_STEP2_STMT =
  `!q:int128 a b.
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ a MOD 2 EXP 128 = b MOD 2 EXP 128`;;

let CHECKPK_OR_STEP2 = assume_spec CHECKPK_OR_STEP2_STMT;;

(*** The code in the image, and the PLT stub for memset:

    mlkem768_enc_derand:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: str     x28, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0xaa0
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: mov     x19, x1
      +0x2c: mov     x21, x0
      +0x30: add     x0, sp, #0x480
      +0x34: mov     x1, x2
      +0x38: mov     x22, x3
      +0x3c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x40: mov     x20, x2
      +0x44: ldr     x8, [x8]
      +0x48: str     x8, [sp, #2712]
      +0x4c: bl      <mlkem768_polyvec_frombytes>
      +0x50: add     x0, sp, #0x480
      +0x54: bl      <mlkem768_polyvec_reduce>
      +0x58: mov     x0, sp
      +0x5c: add     x1, sp, #0x480
      +0x60: mov     x23, sp
      +0x64: bl      <mlkem768_polyvec_tobytes>
      +0x68: movi    v0.2d, #0x0
      +0x6c: mov     x8, xzr
      +0x70: movi    v1.2d, #0x0
      +0x74: movi    v2.2d, #0x0
      +0x78: movi    v3.2d, #0x0
      +0x7c: add     x9, x20, x8
      +0x80: add     x10, x23, x8
      +0x84: add     x8, x8, #0x20
      +0x88: cmp     x8, #0x480
      +0x8c: ldp     q4, q5, [x9]
      +0x90: ldp     q6, q7, [x10]
      +0x94: eor     v4.16b, v6.16b, v4.16b
      +0x98: orr     v2.16b, v4.16b, v2.16b
      +0x9c: eor     v5.16b, v7.16b, v5.16b
      +0xa0: orr     v3.16b, v5.16b, v3.16b
      +0xa4: eor     v0.16b, v4.16b, v0.16b
      +0xa8: eor     v1.16b, v5.16b, v1.16b
      +0xac: b.ne    <mlkem768_enc_derand+0x7c>
      +0xb0: orr     v2.16b, v3.16b, v2.16b
      +0xb4: mov     w23, wzr
      +0xb8: ext     v3.16b, v2.16b, v2.16b, #8
      +0xbc: mov     x0, sp
      +0xc0: eor     v0.16b, v1.16b, v0.16b
      +0xc4: mov     w1, wzr
      +0xc8: mov     w2, #0x480
      +0xcc: mov     x24, sp
      +0xd0: orr     v1.8b, v2.8b, v3.8b
      +0xd4: ext     v2.16b, v0.16b, v0.16b, #8
      +0xd8: fmov    x8, d1
      +0xdc: orr     x8, x8, x8, lsr #32
      +0xe0: lsr     x9, x8, #16
      +0xe4: eor     v0.8b, v0.8b, v2.8b
      +0xe8: orr     w8, w8, w9
      +0xec: fmov    x9, d0
      +0xf0: orr     w8, w8, w8, lsr #8
      +0xf4: eor     x9, x9, x9, lsr #32
      +0xf8: sub     w8, w23, w8, uxtb
      +0xfc: eor     x9, x9, x9, lsr #16
     +0x100: lsr     x10, x9, #8
     +0x104: eor     w25, w9, w10
     +0x108: eor     w8, w25, w8, lsr #16
     +0x10c: and     w26, w8, #0xff
     +0x110: bl      <memset@plt>
     +0x114: add     x0, sp, #0x480
     +0x118: mov     w1, wzr
     +0x11c: mov     w2, #0x600
     +0x120: add     x23, sp, #0x480
     +0x124: bl      <memset@plt>
     +0x128: cmp     w26, w25, uxtb
     +0x12c: b.ne    <mlkem768_enc_derand+0x180>
     +0x130: ldp     q0, q1, [x22]
     +0x134: add     x0, x23, #0x20
     +0x138: mov     x1, x20
     +0x13c: mov     w2, #0x4a0
     +0x140: str     q0, [sp, #1152]
     +0x144: str     q1, [sp, #1168]
     +0x148: bl      <mlkem_sha3_256>
     +0x14c: mov     x0, sp
     +0x150: add     x1, sp, #0x480
     +0x154: mov     w2, #0x40
     +0x158: bl      <mlkem_sha3_512>
     +0x15c: add     x3, x24, #0x20
     +0x160: add     x1, sp, #0x480
     +0x164: mov     x0, x21
     +0x168: mov     x2, x20
     +0x16c: bl      <mlkem768_indcpa_enc>
     +0x170: cbnz    w0, <mlkem768_enc_derand+0x184>
     +0x174: ldp     q0, q1, [sp]
     +0x178: stp     q0, q1, [x19]
     +0x17c: b       <mlkem768_enc_derand+0x184>
     +0x180: mov     w0, #0xfffffffc
     +0x184: movi    v0.2d, #0x0
     +0x188: mov     x8, sp
     +0x18c: stp     q0, q0, [sp]
     +0x190: stp     q0, q0, [sp, #32]
     +0x194: str     q0, [sp, #1200]
     +0x198: add     x8, sp, #0x480
     +0x19c: str     q0, [sp, #1184]
     +0x1a0: str     q0, [sp, #1168]
     +0x1a4: str     q0, [sp, #1152]
     +0x1a8: adrp    x8, <page>
     +0x1ac: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x1b0: ldr     x9, [sp, #2712]
     +0x1b4: ldr     x8, [x8]
     +0x1b8: cmp     x8, x9
     +0x1bc: b.ne    <mlkem768_enc_derand+0x1e0>
     +0x1c0: mov     sp, x29
     +0x1c4: ldp     x20, x19, [sp, #80]
     +0x1c8: ldp     x22, x21, [sp, #64]
     +0x1cc: ldp     x24, x23, [sp, #48]
     +0x1d0: ldp     x26, x25, [sp, #32]
     +0x1d4: ldr     x28, [sp, #16]
     +0x1d8: ldp     x29, x30, [sp], #96
     +0x1dc: ret
     +0x1e0: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem768_enc_derand"; layout_range "plt_memset"];;

let KE3_EXEC = MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The input check of FIPS 203 for ML-KEM-768 in terms of the result of      *)
(* mlkem768_check_pk, and the address of the buffers, which are aligned to   *)
(* 32 bytes within the stack frame.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_EK_CHECK_768_STMT =
  `!ek. LENGTH ek = 1184
        ==> (mlkem_ek_check mlkem768 ek <=>
             !i. i < 768
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`;;

let MLKEM_EK_CHECK_768 = assume_spec MLKEM_EK_CHECK_768_STMT;;

let KE3_CHECK_EQ_STMT =
  `!n. (!i. i < 768
            ==> ((n MOD 2 EXP (8 * 1152)) DIV 2 EXP (12 * i)) MOD 2 EXP 12
                < 3329) <=>
       (!i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let KE3_CHECK_EQ = assume_spec KE3_CHECK_EQ_STMT;;

let KE3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 17040)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 17024 else 17040))`;;

let KE3_BUFFER_ADDRESS = assume_spec KE3_BUFFER_ADDRESS_STMT;;

let KE3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KE3_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the input of G (the message followed by H of the key), and   *)
(* its output as K and r.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHA3_256_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let KE3_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP b in
  let gt = `sha3_512 (APPEND (m:byte list) (sha3_256 ek))` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; gt; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; gt; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek))))
    = 32 /\
    LENGTH(mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek)))) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KE3_FINAL_TAC =
  REWRITE_TAC[mlkem768; MLKEM_ENCAPS_PAIR] THEN REWRITE_TAC[GSYM mlkem768] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (for    *)
(* the callees). The encapsulation key ek of 1184 bytes is at pk and the   *)
(* message m of 32 bytes at coins, and if ek passes the check of FIPS 203, *)
(* the shared secret of 32 bytes written at ss and the ciphertext of 1088  *)
(* bytes written at ct are those of mlkem_encaps_internal mlkem768 ek m in *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it  *)
(* returns -4. The theorem assumes that SampleNTT terminates for each      *)
(* entry of the matrix and that the stack does not contain address 0, as   *)
(* for mlkem768_indcpa_enc. The stack is the 96 bytes of the saved         *)
(* registers, the buffers of 2720 bytes aligned to 32 bytes below them     *)
(* (with up to 16 bytes of padding) and the 17024 used by                  *)
(* mlkem768_indcpa_enc below the buffers. The proof is by cases on whether *)
(* the stack pointer is a multiple of 32, which gives the offset b of the  *)
(* buffers. The first 1152 bytes of the buffers hold the re-encoded vector *)
(* and then G(m || H(ek)), that is K and r, at offset 0, and the vector    *)
(* with the reduced coefficients is at offset 1152, where m and H(ek) are  *)
(* written later. The comparison of the key with the re-encoded vector is  *)
(* a loop of 36 iterations of 32 bytes, with an invariant stating the      *)
(* value of the accumulators in terms of the prefixes.                     *)
(* ------------------------------------------------------------------------- *)

let KE3_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              768`;;

let KE3_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                768))`;;

let KE3_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let KE3_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `1152`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

(*** The loop body, comparing 32 more bytes as two 128-bit words ***)

let KE3_CHUNK_TAC norm a v k =
  let bth = MP (ARITH_RULE (subst [k,`k:num`]
                  `i < 36 ==> 16 * k + 16 <= 1152`))
               (ASSUME `i < 36`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1152`) && vv = v ->
          let lth = SPECL [a; `1152`; k; v; s] CHECKPK_BYTES128 in
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

let KE3_CHECK = `!i. i < 768 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`;;
(*** The tactics take the offset b of the buffers from the stack pointer as a
     numeral, which depends on whether the stack pointer is a multiple of 32 ***)

let ke3_bsub b tm = vsubst [mk_small_numeral b,`boff:num`] tm;;

let KE3_N = 19856;;

let ke3_frame b =
  let qs = Printf.sprintf
  "read SP s = word_add stackpointer (word %d) /\\
   read X29 s = word_add stackpointer (word 19760) /\\
   read (memory :> bytes64 (word_add stackpointer (word 19760))) s = x29_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19768))) s = returnaddress /\\
   read (memory :> bytes64 (word_add stackpointer (word 19776))) s = x28_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19792))) s = x26_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19800))) s = x25_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19808))) s = x24_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19816))) s = x23_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19824))) s = x22_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19832))) s = x21_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19840))) s = x20_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 19848))) s = x19_init /\\
   read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary /\\
   read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
   read (memory :> bytes64 guard) s = canary /\\
   read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
   read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
   read (memory :> bytes(ea,el)) s = ev /\\
   read X27 s = x27_init /\\
   read X19 s = ss /\\ read X20 s = pk /\\ read X21 s = ct /\\
   read X22 s = coins /\\
   read X23 s = word_add stackpointer (word %d) /\\
   read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\\
   read (memory :> bytes(coins,32)) s = num_of_bytelist m /\\
   read (memory :> bytes(pk,1152)) s = n /\\
   read (memory :> bytes(word_add stackpointer (word %d),1152)) s = M"
   b (b + 2712) b b in
  vsubst [KE3_M,`M:num`] (parse_term qs);;

let ke3_inv_frame b =
  let inv = `\i s. read X8 s = word(32 * i) /\
        (read Q2 s = word 0 /\ read Q3 s = word 0 <=>
         n MOD 2 EXP (256 * i) = M MOD 2 EXP (256 * i))` in
  let inv = vsubst [KE3_M,`M:num`] inv in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,mk_conj(bod,ke3_frame b));;

let KE3_CALL_TAC tac args n = tac args n;;
let KE3_N_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1184)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 1184 1152 = 1152`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 1152)`)))
    else NO_TAC);;

let KE3_FIX_N_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `n:num` &&
       not(is_var(lhand(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC);;


let KE3_HM_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 1152),`a:int64`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (m:byte list) (sha3_256 ek))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(APPEND (m:byte list) (sha3_256 ek)) = 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SHA3_256] THEN ARITH_TAC;
    ALL_TAC];;

let KE3_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;
let KE3_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;
let KE3_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let KE3_LIST_TAC b s =
  let p = string_of_int (b + 1152) in
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   (parse_term ("read (memory :> bytes(word_add stackpointer (word " ^ p ^ "),1536)) s =
    num_of_wordlist(list_of_seq (\\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 768)")))
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1536 = 2 * 768`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     (parse_term ("word_add (word_add stackpointer (word " ^ p ^ "))
               (word (2 * i)):int64 =
       word_add stackpointer (word (" ^ p ^ " + 2 * i))"))
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;



let KE3_PART1_TAC b =
  ENSURES_INIT_TAC "s0" THEN KE3_N_TAC THEN KE3_FIX_N_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (1--9) THEN KE3_BUFFER_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (11--20) THEN
  KE3_CALL_TAC KE3_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`;
                       `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  ARM_STEPS_TAC KE3_EXEC (22--23) THEN
  KE3_CALL_TAC KE3_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  KE3_LIST_TAC b `s24:armstate` THEN KE3_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (25--28) THEN
  KE3_CALL_TAC KE3_TOBYTES_TAC [`read X0 s`; `read X1 s`; KE3_L;
                     `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN
  ARM_STEPS_TAC KE3_EXEC (30--34) THEN
  KE3_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[];;

let KE3_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ABBREV_TAC(mk_eq(`mm:num`,KE3_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KE3_CHUNK_TAC true `pk:int64` `n:num` `2 * i` THEN
  KE3_CHUNK_TAC true `pk:int64` `n:num` `2 * i + 1` THEN
  KE3_CHUNK_TAC true (ke3_bsub b `word_add stackpointer (word boff):int64`)
                    `mm:num` `2 * i` THEN
  KE3_CHUNK_TAC false (ke3_bsub b `word_add stackpointer (word boff):int64`)
                    `mm:num` `2 * i + 1` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` CHECKPK3_TEST) (ASSUME `i < 36`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_iff(concl th) &&
      lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`)) THEN
    REWRITE_TAC[CHECKPK_OR_STEP2; CHECKPK_MOD_STEP2] THEN
    CONV_TAC TAUT];;

let KE3_DONE_TAC b =
  SUBGOAL_THEN
   `(q2:int128 = word 0 /\ q3:int128 = word 0) <=>
    !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q2:int128 = word 0 /\
                                                q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(KE3_BOUND `pk:int64` `s0:armstate`) THEN
    MP_TAC(KE3_BOUND (ke3_bsub b `word_add stackpointer (word boff):int64`)
                         `s0:armstate`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 1152 = 256 * 36`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(KE3_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECKPK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 768 = 256 * 36`];
    ALL_TAC];;

(*** After the loop: memsets, the check, the fail branch ***)

let KE3_EXIT_TAC b =
  ABBREV_TAC(mk_eq(`mm:num`,KE3_M)) THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN KEM_HALVES_TAC `coins:int64` THEN KE3_DONE_TAC b THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--25) THEN
  LIBC_PLT_TAC KE3_EXEC 25 THEN
  LIBC_CALL_TAC "H_MEMSET" KE3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC KE3_EXEC (31--35) THEN
  LIBC_PLT_TAC KE3_EXEC 35 THEN
  LIBC_CALL_TAC "H_MEMSET" KE3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC KE3_EXEC (41--42);;

let KE3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19856 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_contract mf ea el ev`) (concl th)
    then LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th)
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_768; ASSUME `LENGTH(ek:byte list) = 1184`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29);;


let KE3_JOIN_TAC a l s =
  MP_TAC(SPECL [a; mk_comb(`num_of_bytelist`,l);
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPEC l NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KE3_REST_PASS_TAC b =
  ARM_STEPS_TAC KE3_EXEC (43--49) THEN
  KE3_JOIN_TAC (KEM_SP(b + 1152)) `m:byte list` "s49" THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 50 THEN
  KE3_HM_TAC b "s50" THEN
  ARM_STEPS_TAC KE3_EXEC (51--54) THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND (m:byte list) (sha3_256 ek)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 55 THEN
  KE3_KR_TAC b "s55" THEN
  KEM_HALVES_TAC (KEM_SP b) THEN
  ARM_STEPS_TAC KE3_EXEC (56--60) THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
    `m:byte list`;
    `mlkem_slice 32 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 61 THEN
  ARM_STEPS_TAC KE3_EXEC (62--75) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (76--88) THEN
  KE3_JOIN_TAC `ss:int64`
   `mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`
   "s88" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KE3_FINAL_TAC;;

let KE3_REST_FAIL_TAC b =
  ARM_STEPS_TAC KE3_EXEC (43--53) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (54--66) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;


let KE3_IFF_FIND f =
  FIRST_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0` && rand(concl th) = KE3_CHECK then f th else NO_TAC);;

let KE3_PCFIX_TAC case =
  FIRST_X_ASSUM(fun th ->
    if (try lhand(concl th) = `read PC s42` with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[ASSUME case] th) else NO_TAC);;

let KE3_BRANCH2_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = try (fun (c,_) -> c) (dest_cond(rand(concl th)))
            with Failure _ -> failwith "no cond" in
    if lhand(concl th) <> `read PC s42` then failwith "not s42" else
    SUBGOAL_THEN
     (mk_eq(c,`~(q2:int128 = word 0 /\ q3:int128 = word 0)`))
     (fun eqth -> ASSUME_TAC(REWRITE_RULE[eqth] th)) THENL
     [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC]);;

let KE3_EXIT_FULL_TAC b =
  KE3_EXIT_TAC b THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `num_of_bytelist ek MOD 2 EXP (8 * 1152) = n`); KE3_CHECK_EQ]) THEN
  KE3_BRANCH2_TAC THEN
  ASM_CASES_TAC `q2:int128 = word 0 /\ q3:int128 = word 0` THENL
   [SUBGOAL_THEN KE3_CHECK ASSUME_TAC THENL
     [KE3_IFF_FIND (fun th -> ACCEPT_TAC(EQ_MP th (ASSUME `q2:int128 = word 0 /\ q3:int128 = word 0`)));
      ALL_TAC] THEN
    KE3_PCFIX_TAC `q2:int128 = word 0 /\ q3:int128 = word 0` THEN
    KE3_REST_PASS_TAC b;
    SUBGOAL_THEN (mk_neg KE3_CHECK) ASSUME_TAC THENL
     [KE3_IFF_FIND (fun th -> REWRITE_TAC[GSYM th] THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    KE3_PCFIX_TAC `~(q2:int128 = word 0 /\ q3:int128 = word 0)` THEN
    KE3_REST_FAIL_TAC b];;

let KE3_CASE_TAC b =
  SUBGOAL_THEN (ke3_bsub b `aligned 16 (word_add stackpointer (word boff):int64)`)
   ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (stackpointer:int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(RAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = num_of_bytelist ek MOD 2 EXP (8 * 1152)` THEN
  ENSURES_WHILE_UP2_TAC `36` `pc + mlkem768_enc_derand_loop1`
   `pc + mlkem768_enc_derand_loop1_exit` (ke3_inv_frame b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KE3_PART1_TAC b; KE3_BODY_TAC b; KE3_EXIT_FULL_TAC b];;

let MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct ss pk coins (ek:byte list) (m:byte list) guard mf mc ea el
    ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1184 /\ LENGTH m = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 19856),19856) /\
        nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
        PAIRWISE nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 19856),19856)] /\
        ALLPAIRS nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 19856),19856)]
         [(pk,1184); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem768_enc_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist m)
             (\s. read PC s = returnaddress /\
                  (mlkem_ek_check mlkem768 ek
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist
                        (FST(mlkem_encaps_internal mlkem768 ek m)) /\
                       read (memory :> bytes(ct,1088)) s =
                       num_of_bytelist
                        (SND(mlkem_encaps_internal mlkem768 ek m))) /\
                  C_RETURN s =
                  (if mlkem_ek_check mlkem768 ek then word 0
                   else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 19856),19856)])`;;

let MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract   *)
(* for memset (for mlkem768_indcpa_enc and the memset calls of this        *)
(* function) and the safety contract for memcpy. The events depend only on *)
(* the addresses and on the encapsulation key, which is public: the        *)
(* function branches on the result of the comparison of the key with its   *)
(* re-encoding, which is the check of the key, and the events of the       *)
(* encryption depend on rho. The events are given by a template with cases *)
(* on whether the stack pointer is a multiple of 32 and on whether the key *)
(* passes the check. Each case is of the form APPEND (events after the     *)
(* loop) (APPEND (ENUMERATEL 36 (events of one iteration)) (events before  *)
(* the loop)). The proof follows the correctness proof up to the branch on *)
(* the comparison: it uses the combined theorems of                        *)
(* mlkem768_polyvec_frombytes, mlkem768_polyvec_reduce and                 *)
(* mlkem768_polyvec_tobytes and the loop invariant of the correctness      *)
(* proof, because the branch and its jump event depend on the result of    *)
(* the comparison. The calls after the branch use the safety theorems of   *)
(* the callees.                                                            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KE_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (guard:int64)
   (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list).
   if aligned 32 stackpointer
   then APPEND
         (if mlkem_ek_check mlkem768 ek
          then f_ev_a1 ct ss pk coins guard mf mc pc stackpointer
                       returnaddress ek
          else f_ev_a0 ct ss pk coins guard mf mc pc stackpointer
                       returnaddress ek)
         (APPEND
           (ENUMERATEL 36
             (\i. f_ev_al ct ss pk coins guard mf mc pc stackpointer
                          returnaddress ek i))
           (f_ev_ap ct ss pk coins guard mf mc pc stackpointer
                    returnaddress ek))
   else APPEND
         (if mlkem_ek_check mlkem768 ek
          then f_ev_u1 ct ss pk coins guard mf mc pc stackpointer
                       returnaddress ek
          else f_ev_u0 ct ss pk coins guard mf mc pc stackpointer
                       returnaddress ek)
         (APPEND
           (ENUMERATEL 36
             (\i. f_ev_ul ct ss pk coins guard mf mc pc stackpointer
                          returnaddress ek i))
           (f_ev_up ct ss pk coins guard mf mc pc stackpointer
                    returnaddress ek))
   :(uarch_event)list`;;

let CHECKPK_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let CHECKPK_EV_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE CHECKPK_EV_CONV th else th);;

(*** The events of the loop in the assumptions have the addresses in the
     normalized form, as those in the goal after the loop invariant is
     normalized in the same way. At the exit, the events of the goal are
     normalized before f_ev_epil is unified ***)

let CHECKPK_DISCHARGE_EXIT_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(RAND_CONV CHECKPK_EV_CONV) THEN FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let KE_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ek:byte list`; `i:num`;
   `f_ev_al:int64->int64->int64->int64->int64->int64->int64->num->int64->int64->(byte)list->num->(uarch_event)list`;
   `f_ev_ul:int64->int64->int64->int64->int64->int64->int64->num->int64->int64->(byte)list->num->(uarch_event)list`];;

let KE3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_INDCPA" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract]
         (CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1))) "H_MEMSET")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_TOBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_256_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_SHA3_256" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  CONCRETIZE_F_EVENTS_TAC KE_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_768; ASSUME `LENGTH(ek:byte list) = 1184`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29);;

let ke3s_frame b =
  list_mk_conj
   (filter (fun c -> not(can (term_match []
       `read (memory :> bytes(coins,32)) s = x`) c))
     (conjuncts (ke3_frame b)));;

let ke3s_inv_frame b =
  let inv = `\i s. read X8 s = word(32 * i) /\
        (read Q2 s = word 0 /\ read Q3 s = word 0 <=>
         n MOD 2 EXP (256 * i) = M MOD 2 EXP (256 * i))` in
  let inv = vsubst [KE3_M,`M:num`] inv in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,mk_conj(bod,ke3s_frame b));;

let KE3_SAFE_CALL_TAC name ilist n =
  KE3_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,KE3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KE_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KE3_SAFE_PART1_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KE3_N_TAC THEN KE3_FIX_N_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (1--9) THEN KE3_BUFFER_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (11--20) THEN
  KE3_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `n:num`;
    `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  ARM_STEPS_TAC KE3_EXEC (22--23) THEN
  KE3_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  KE3_LIST_TAC b `s24:armstate` THEN KE3_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (25--28) THEN
  KE3_SAFE_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; KE3_L;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN
  ARM_STEPS_TAC KE3_EXEC (30--34) THEN
  KE3_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KE3_SAFE_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`mm:num`,KE3_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KE3_CHUNK_TAC true `pk:int64` `n:num` `2 * i` THEN
  KE3_CHUNK_TAC true `pk:int64` `n:num` `2 * i + 1` THEN
  KE3_CHUNK_TAC true (ke3_bsub b `word_add stackpointer (word boff):int64`)
                    `mm:num` `2 * i` THEN
  KE3_CHUNK_TAC false (ke3_bsub b `word_add stackpointer (word boff):int64`)
                    `mm:num` `2 * i + 1` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` CHECKPK3_TEST) (ASSUME `i < 36`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_iff(concl th) &&
      lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`)) THEN
    REWRITE_TAC[CHECKPK_OR_STEP2; CHECKPK_MOD_STEP2] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KE3_SAFE_EXIT_TAC b =
  ABBREV_TAC(mk_eq(`mm:num`,KE3_M)) THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KE3_DONE_TAC b THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--25) THEN
  LIBC_PLT_TAC KE3_EXEC 25 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KE3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KE_SAFE_ALLOWED) 30 THEN
  ARM_STEPS_TAC KE3_EXEC (31--35) THEN
  LIBC_PLT_TAC KE3_EXEC 35 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KE3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KE_SAFE_ALLOWED) 40 THEN
  ARM_STEPS_TAC KE3_EXEC (41--42);;

let KE3_SAFE_PASS_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`] in
  ARM_STEPS_TAC KE3_EXEC (43--49) THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE3_SAFE_CALL_TAC "H_SHA3_256" ([e; x 0; x 1; `1184`] @ rest) 50 THEN
  ARM_STEPS_TAC KE3_EXEC (51--54) THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE3_SAFE_CALL_TAC "H_SHA3_512" ([e; x 0; x 1; `64`] @ rest) 55 THEN
  ARM_STEPS_TAC KE3_EXEC (56--60) THEN
  KE3_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE3_SAFE_CALL_TAC "H_INDCPA"
   ([e; x 0; x 1; x 2; x 3; `ek:byte list`] @ rest) 61 THEN
  ARM_STEPS_TAC KE3_EXEC (62--75) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (76--88) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECKPK_DISCHARGE_EXIT_TAC;;

let KE3_SAFE_FAIL_TAC b =
  ARM_STEPS_TAC KE3_EXEC (43--53) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (54--66) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECKPK_DISCHARGE_EXIT_TAC;;

(*** The branch on the comparison is in the PC and in the events ***)

let KE3_SAFE_BRANCH_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = try (fun (c,_) -> c) (dest_cond(rand(concl th)))
            with Failure _ -> failwith "no cond" in
    if lhand(concl th) <> `read PC s42` then failwith "not s42" else
    SUBGOAL_THEN
     (mk_eq(c,`~(q2:int128 = word 0 /\ q3:int128 = word 0)`))
     (fun eqth ->
        ASSUME_TAC(REWRITE_RULE[eqth] th) THEN
        RULE_ASSUM_TAC(fun th2 ->
          if (try lhand(concl th2) = `read events s42` with Failure _ -> false)
          then REWRITE_RULE[eqth] th2 else th2)) THENL
     [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC]);;

let KE3_SAFE_PCFIX_TAC case =
  KE3_PCFIX_TAC case THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhand(concl th) = `read events s42` with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[ASSUME case] th) else NO_TAC);;

let KE3_SAFE_EXIT_FULL_TAC b =
  KE3_SAFE_EXIT_TAC b THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `num_of_bytelist ek MOD 2 EXP (8 * 1152) = n`); KE3_CHECK_EQ]) THEN
  KE3_SAFE_BRANCH_TAC THEN
  ASM_CASES_TAC `q2:int128 = word 0 /\ q3:int128 = word 0` THENL
   [SUBGOAL_THEN KE3_CHECK ASSUME_TAC THENL
     [KE3_IFF_FIND (fun th -> ACCEPT_TAC(EQ_MP th (ASSUME `q2:int128 = word 0 /\ q3:int128 = word 0`)));
      ALL_TAC] THEN
    KE3_SAFE_PCFIX_TAC `q2:int128 = word 0 /\ q3:int128 = word 0` THEN
    KE3_SAFE_PASS_TAC b;
    SUBGOAL_THEN (mk_neg KE3_CHECK) ASSUME_TAC THENL
     [KE3_IFF_FIND (fun th -> REWRITE_TAC[GSYM th] THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    KE3_SAFE_PCFIX_TAC `~(q2:int128 = word 0 /\ q3:int128 = word 0)` THEN
    KE3_SAFE_FAIL_TAC b];;

let KE3_SAFE_CASE_TAC b =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then REWRITE_TAC[th] else NO_TAC) THEN
  SUBGOAL_THEN (ke3_bsub b `aligned 16 (word_add stackpointer (word boff):int64)`)
   ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (stackpointer:int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(RAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = num_of_bytelist ek MOD 2 EXP (8 * 1152)` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `36` `pc + mlkem768_enc_derand_loop1`
   `pc + mlkem768_enc_derand_loop1_exit` (ke3s_inv_frame b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KE3_SAFE_PART1_TAC b; KE3_SAFE_BODY_TAC b;
    KE3_SAFE_EXIT_FULL_TAC b];;


let MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ct ss pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1184 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 19856),19856) /\
          nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
          PAIRWISE nonoverlapping
           [(ct,1088); (ss,32); (word_sub stackpointer (word 19856),19856)] /\
          ALLPAIRS nonoverlapping
           [(ct,1088); (ss,32); (word_sub stackpointer (word 19856),19856)]
           [(pk,1184); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem768_enc_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ct; ss; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mlkem_ek_check mlkem768 ek then word 0
                     else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ct ss pk coins guard mf mc pc
                              (word_sub stackpointer (word 19856))
                              returnaddress ek /\
                       memaccess_inbounds e2
                        [pk,1184; coins,32; ct,1088; ss,32;
                         word_sub stackpointer (word 19856),19856;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem_poly_compress_d4_consts),
                         mlkem_poly_compress_d4_consts_size]
                        [ct,1088; ss,32;
                         word_sub stackpointer (word 19856),19856]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 19856),19856)])`;;

let MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
