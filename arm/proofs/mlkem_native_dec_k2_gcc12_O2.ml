(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-512 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem512_dec from            *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem512_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem512_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem512_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time, computes J of z (in the key)        *)
(* followed by the ciphertext into the shared secret with mlkem_shake256,    *)
(* and replaces it by K' if the ciphertexts are equal, again in constant     *)
(* time. In both cases it zeroes its buffers. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x3f30, using the theorems for mlkem512_check_sk, mlkem512_indcpa_dec,    *)
(* mlkem_sha3_512, mlkem512_indcpa_enc and mlkem_shake256 in the image and   *)
(* the contracts for memset and memcpy.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_check_sk_k2_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_indcpa_dec_k2_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_indcpa_enc_k2_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake256_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    3f30: sub     sp, sp, #0x400
    3f34: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    3f38: ldr     x3, [x3, #4088]
    3f3c: stp     x19, x20, [sp]
    3f40: add     x19, sp, #0x5f
    3f44: and     x19, x19, #0xffffffffffffffe0
    3f48: stp     x21, x22, [sp, #16]
    3f4c: stp     x23, x24, [sp, #32]
    3f50: mov     x24, x0
    3f54: mov     x23, x2
    3f58: stp     x25, x30, [sp, #48]
    3f5c: mov     x25, x1
    3f60: mov     x0, x2
    3f64: ldr     x1, [x3]
    3f68: str     x1, [sp, #1016]
    3f6c: mov     x1, #0x0
    3f70: bl      3ba0 <mlkem512_check_sk>
    3f74: cbz     w0, 3fe0 <mlkem512_dec+0xb0>
    3f78: mov     w20, w0
    3f7c: add     x22, x19, #0x360
    3f80: add     x21, x19, #0x320
    3f84: mov     x0, x19
    3f88: mov     x2, #0x320
    3f8c: mov     w1, #0x0
    3f90: bl      840 <memset@plt>
    3f94: movi    v0.4s, #0x0
    3f98: stp     q0, q0, [x21]
    3f9c: stp     q0, q0, [x21, #32]
    3fa0: stp     q0, q0, [x22]
    3fa4: stp     q0, q0, [x22, #32]
    3fa8: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    3fac: ldr     x0, [x0, #4088]
    3fb0: ldr     x2, [sp, #1016]
    3fb4: ldr     x1, [x0]
    3fb8: subs    x2, x2, x1
    3fbc: mov     x1, #0x0
    3fc0: b.ne    4138 <mlkem512_dec+0x208>
    3fc4: ldp     x21, x22, [sp, #16]
    3fc8: mov     w0, w20
    3fcc: ldp     x19, x20, [sp]
    3fd0: ldp     x23, x24, [sp, #32]
    3fd4: ldp     x25, x30, [sp, #48]
    3fd8: add     sp, sp, #0x400
    3fdc: ret
    3fe0: add     x22, x19, #0x360
    3fe4: mov     x2, x23
    3fe8: mov     x0, x22
    3fec: mov     x1, x25
    3ff0: add     x21, x19, #0x320
    3ff4: bl      3910 <mlkem512_indcpa_dec>
    3ff8: mov     w20, w0
    3ffc: cbnz    w0, 3f84 <mlkem512_dec+0x54>
    4000: ldr     q0, [x23, #1568]
    4004: mov     x1, x22
    4008: ldr     q1, [x23, #1584]
    400c: mov     x0, x21
    4010: mov     x2, #0x40
    4014: stp     q0, q1, [x19, #896]
    4018: bl      26f4 <mlkem_sha3_512>
    401c: add     x3, x19, #0x340
    4020: add     x2, x23, #0x300
    4024: mov     x1, x22
    4028: mov     x0, x19
    402c: bl      3690 <mlkem512_indcpa_enc>
    4030: mov     w20, w0
    4034: cbnz    w0, 3f84 <mlkem512_dec+0x54>
    4038: movi    v2.4s, #0x0
    403c: mov     x0, x19
    4040: mov     x1, x25
    4044: add     x2, x19, #0x300
    4048: mov     v3.16b, v2.16b
    404c: nop
    4050: ldr     q0, [x1], #16
    4054: ldr     q1, [x0], #16
    4058: eor     v0.16b, v0.16b, v1.16b
    405c: orr     v3.16b, v3.16b, v0.16b
    4060: eor     v2.16b, v2.16b, v0.16b
    4064: cmp     x0, x2
    4068: b.ne    4050 <mlkem512_dec+0x120>
    406c: movi    v1.4s, #0x0
    4070: ext     v4.16b, v3.16b, v1.16b, #8
    4074: ext     v0.16b, v2.16b, v1.16b, #8
    4078: orr     v3.16b, v4.16b, v3.16b
    407c: eor     v2.16b, v0.16b, v2.16b
    4080: ext     v4.16b, v3.16b, v1.16b, #4
    4084: ext     v0.16b, v2.16b, v1.16b, #4
    4088: orr     v4.16b, v4.16b, v3.16b
    408c: eor     v0.16b, v0.16b, v2.16b
    4090: ext     v3.16b, v4.16b, v1.16b, #2
    4094: ext     v2.16b, v0.16b, v1.16b, #2
    4098: orr     v3.16b, v3.16b, v4.16b
    409c: eor     v2.16b, v2.16b, v0.16b
    40a0: ext     v0.16b, v3.16b, v1.16b, #1
    40a4: ext     v1.16b, v2.16b, v1.16b, #1
    40a8: orr     v0.16b, v0.16b, v3.16b
    40ac: eor     v1.16b, v1.16b, v2.16b
    40b0: umov    w0, v0.b[0]
    40b4: umov    w1, v1.b[0]
    40b8: neg     w0, w0
    40bc: eor     w0, w1, w0, asr #16
    40c0: ldr     q0, [x23, #1600]
    40c4: and     w0, w0, #0xff
    40c8: ldr     q1, [x23, #1616]
    40cc: mov     x2, #0x300
    40d0: eor     w23, w0, w1
    40d4: mov     x1, x25
    40d8: add     x0, x19, #0x20
    40dc: stp     q0, q1, [x19]
    40e0: bl      810 <memcpy@plt>
    40e4: mov     x0, x24
    40e8: mov     x2, x19
    40ec: mov     x3, #0x320
    40f0: mov     x1, #0x20
    40f4: bl      2570 <mlkem_shake256>
    40f8: neg     w4, w23
    40fc: sub     x24, x24, #0x1
    4100: mov     x0, #0x1
    4104: nop
    4108: add     x2, x21, x0
    410c: mov     w1, w4
    4110: ldurb   w2, [x2, #-1]
    4114: ldrb    w3, [x24, x0]
    4118: eor     w3, w2, w3
    411c: and     w1, w3, w1, asr #16
    4120: eor     w2, w2, w1
    4124: strb    w2, [x24, x0]
    4128: add     x0, x0, #0x1
    412c: cmp     x0, #0x21
    4130: b.ne    4108 <mlkem512_dec+0x1d8>
    4134: b       3f84 <mlkem512_dec+0x54>
    4138: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_DEC_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x810,0x820; 0x840,0x850; 0x3f30,0x413c];;

let KD2_EXEC = MLKEM_NATIVE_DEC_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-512, the input check of    *)
(* FIPS 203 in terms of the result of mlkem512_check_sk, and the address of  *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_512 = prove
 (`!ek m r. LENGTH(kpke_encrypt mlkem512 ek m r) = 768`,
  REWRITE_TAC[mlkem512; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_512 = prove
 (`!dk c. LENGTH(kpke_decrypt mlkem512 dk c) = 32`,
  REWRITE_TAC[mlkem512; KPKE_DECRYPT_LENGTH]);;

let KD2_CHECK = prove
 (`!dk c. LENGTH dk = 1632 /\ LENGTH c = 768
          ==> (mlkem_decaps_check mlkem512 dk c <=>
               num_of_bytelist(mlkem_slice 1568 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 768 800 dk)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem512; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

let KD2_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 12095)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 12064 else 12080))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KD2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD2_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_DEC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KD2_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,1632)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,768; 768,800; 1568,32; 1600,32]
    else NO_TAC);;

let KD2_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 768 800 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list))`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 18;;

let KD2_FAIL_TAC =
  ARM_STEPS_TAC KD2_EXEC (19--26) THEN
  LIBC_PLT_TAC KD2_EXEC 26 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 31 THEN
  ARM_STEPS_TAC KD2_EXEC (32--37) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (38--50) THEN
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

let KD2_MP = `kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c`;;

let KD2_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c)
                  (mlkem_slice 1568 32 dk))`;;

let KD2_KP = mk_comb(`mlkem_slice 0 32`,KD2_GG);;

let KD2_RR = mk_comb(`mlkem_slice 32 32`,KD2_GG);;

let KD2_CP = list_mk_comb(`kpke_encrypt mlkem512`,
  [`mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR]);;

let KD2_ZZ = `mlkem_slice 1600 32 (dk:byte list)`;;

let KD2_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 1600 32 dk) c)) 32`;;

let KD2_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD2_CP));;

let KD2_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD2_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD2_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD2_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD2_ZZ),`ZZ:num`;
         KD2_EQ,`EQ:bool`] tm;;

let KD2_FRAME b = KD2_SUBST(parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word 12000) /\\
  read X19 s = word_add stackpointer (word %d) /\\
  read X20 s = word 0 /\\
  read X21 s = word_add stackpointer (word %d) /\\
  read X22 s = word_add stackpointer (word %d) /\\
  read X25 s = ct /\\
  read X26 s = x26_init /\\ read X27 s = x27_init /\\ read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12000))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12008))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12016))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12024))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12032))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12040))) s =
  x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12048))) s =
  x25_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12056))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 13016))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word 131024))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  b (b + 800) (b + 864) (b + 800)));;

let KD2_INV b = KD2_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word_add stackpointer (word(%d + 16 * i)) /\\
        read X1 s = word_add ct (word(16 * i)) /\\
        read X2 s = word_add stackpointer (word %d) /\\
        read X23 s = sk /\\ read X24 s = ss /\\
        (read Q3 s = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\\
        read (memory :> bytes(ct,768)) s = num_of_bytelist c /\\
        read (memory :> bytes(word_add stackpointer (word %d),768)) s = CP /\\
        read (memory :> bytes128 (word_add sk (word 1600))) s =
        word(ZZ MOD 2 EXP 128) /\\
        read (memory :> bytes128 (word_add sk (word 1616))) s =
        word(ZZ DIV 2 EXP 128) /\\ FRAME"
  b (b + 768) b));;

let KD2_INV_FRAME b =
  let inv = KD2_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_FRAME b,`FRAME:bool`] bod);;

let KD2_CMOV_INV b = KD2_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word(i + 1) /\\
        read X24 s = word_sub ss (word 1) /\\
        read X4 s = (if EQ then word 0 else word 4294967041) /\\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"));;

let KD2_CMOV_INV_FRAME b =
  let inv = KD2_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption, G of m' and h, and the reencryption.                          *)
(* ------------------------------------------------------------------------- *)

let KD2_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 864),`a:int64`;
           KD2_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 1568 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_512];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD2_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 1568 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_512] THEN ARITH_TAC;
    ALL_TAC];;

let KD2_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 800) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD2_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD2_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD2_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 1568):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 1600):int64` THEN
  ARM_STEPS_TAC KD2_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (3--6) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (7--17) THEN KEM_GOT_TAC THEN
  KD2_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD2_EXEC (19--25) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `mlkem_slice 0 768 (dk:byte list)`; `c:byte list`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 26 THEN
  ARM_STEPS_TAC KD2_EXEC (27--35) THEN
  KEM_JOIN_TAC (KEM_SP(b + 896)) `mlkem_slice 1568 32 (dk:byte list)`
    (st 35) THEN
  KD2_G_INPUT_TAC b (st 35) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD2_MP),
            `mlkem_slice 1568 32 (dk:byte list)`);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 36 THEN
  KD2_KR_TAC b (st 36) THEN
  ARM_STEPS_TAC KD2_EXEC (37--41) THEN KEM_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_512]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC KD2_EXEC (43--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test.                      *)
(* ------------------------------------------------------------------------- *)

let KD2_TEST = prove
 (`!sp:int64 b i.
        b <= 12080 /\ i < 48
        ==> (val(word_sub (word_add (word_add sp (word(b + 16 * i))) (word 16))
                          (word_add sp (word(b + 768)))) = 0 <=>
             ~(i + 1 < 48))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_sub (word_add a x) (word_add a y):int64 =
                         word_sub x y`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `b + 768 < 2 EXP 64 /\ (b + 16 * i) + 16 < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let KD2_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 48 ==> 16 * i + 16 <= 768`)
               (ASSUME `i < 48`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let lth = SPECL [a; `768`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD2_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD2_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD2_CHUNK_TAC (KEM_SP b) (mk_comb(`num_of_bytelist`,KD2_CP)) THEN
  ARM_STEPS_TAC KD2_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MP (SPECL [`stackpointer:int64`; mk_small_numeral b; `i:num`] KD2_TEST)
         (CONJ (ARITH_RULE(mk_binop `(<=):num->num->bool`
                            (mk_small_numeral b) `12080`))
               (ASSUME `i < 48`)))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 48` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[KEM_OR_STEP; KEM_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]];;

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 255, J of z and the ciphertext copied after  *)
(* z with memcpy, and the mask for the bytes.                                *)
(* ------------------------------------------------------------------------- *)

let KD2_DONE_TAC =
  SUBGOAL_THEN (mk_iff(`q3:int128 = word 0`,KD2_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD2_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD2_MASK_TAC s =
  let x23 = mk_comb(`read X23`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x23 then
      let e = rand c in
      let eth = BITBLAST_RULE
        (mk_eq(e,`if q3:int128 = word 0 then word 0:int64 else word 255`)) in
      ASSUME_TAC(TRANS th eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x23 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') && lhand(concl th') = `q3:int128 = word 0`
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD2_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP b,`a:int64`]
     `read (memory :> bytes(a,800)) s =
      num_of_bytelist(APPEND (mlkem_slice 1600 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `800 = 32 + 768`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 1600 32 (dk:byte list)) c) = 800`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD2_EXIT_A_TAC b =
  let st n = "s"^string_of_int n in
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN KD2_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--26) THEN
  KD2_MASK_TAC (st 26) THEN
  ARM_STEPS_TAC KD2_EXEC (27--30) THEN
  KEM_JOIN_TAC (KEM_SP b) KD2_ZZ (st 30) THEN
  LIBC_PLT_TAC KD2_EXEC 30 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 35 THEN
  KD2_J_INPUT_TAC b (st 35) THEN
  ARM_STEPS_TAC KD2_EXEC (36--40) THEN KEM_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 1600 32 (dk:byte list)) c`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC KD2_EXEC (42--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD2_CMOV_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 800); `32`; mk_comb(`num_of_bytelist`,KD2_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[KEM_KP_ADDR] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (KD2_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC(ONCE_REWRITE_RULE
       [GSYM(SPECL [`ss:int64`; `i:num`] KEM_SS_ADDR)] th1) THEN
      ASSUME_TAC th2)] THEN
  ARM_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [KEM_SS_ADDR; MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
    SPEC_TAC(KD2_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD2_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_DECAPS_ALT] THEN REWRITE_TAC[GSYM mlkem512] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD2_CP,`c:byte list`),KD2_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD2_EXIT_B_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD2_EXEC (1--5) THEN
  LIBC_PLT_TAC KD2_EXEC 5 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC KD2_EXEC (11--16) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (17--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD2_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy. The      *)
(* decapsulation key dk of 1632 bytes is at sk and the ciphertext c of 768   *)
(* bytes at ct, and if they pass the check of FIPS 203, the shared secret of *)
(* 32 bytes written at ss is that of mlkem_decaps_internal mlkem512 dk c in  *)
(* common/fips203.ml and the function returns 0, and otherwise it returns    *)
(* -5. The theorem assumes that SampleNTT terminates for each entry of the   *)
(* matrix from the seed in the key. The stack is the 1024 bytes of the       *)
(* function and the 12000 used by mlkem512_indcpa_enc below them. The proof  *)
(* is by cases on whether the stack pointer is a multiple of 32, which gives *)
(* the address b of the buffers, at offsets 0 (c' and then z and the         *)
(* ciphertext), 800 (K' and r') and 864 (m' and h), and on the check of the  *)
(* key.                                                                      *)
(* ------------------------------------------------------------------------- *)

let KD2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13024 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13024):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD2_CHECK; ASSUME `LENGTH(dk:byte list) = 1632`;
           ASSUME `LENGTH(c:byte list) = 768`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffd0`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffd0`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD2_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `48` `pc + 0x4050` `pc + 0x406c`
   (KD2_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD2_PART1_TAC b; KD2_BODY_TAC b;
    ENSURES_WHILE_UP2_TAC `32` `pc + 0x4108` `pc + 0x4134`
     (KD2_CMOV_INV_FRAME b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD2_EXIT_A_TAC b; KD2_CMOV_BODY_TAC b; KD2_EXIT_B_TAC]];;

let KD2_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (3--6) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (7--17) THEN KEM_GOT_TAC THEN
  KD2_CHECK_TAC THEN KD2_FAIL_TAC;;

let KD2_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 768 800 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD2_OK_TAC b; KD2_BAD_TAC];;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
        nonoverlapping (ct,768) (word pc,0x6480) /\
        nonoverlapping (sk,1632) (word pc,0x6480) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 13024),13024) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 13024),13024)]
         [(ct,768); (sk,1632); (word pc,0x6480); (word(pc + 0x1fff8),8);
          (guard,8); (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x3f30) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem512 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem512 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 13024),13024)])`,
  KD2_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KD2_CASE_TAC 12064; KD2_CASE_TAC 12080]);;
