(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-1024 (FIPS 203 Algorithm 18, with the input *)
(* check of Algorithm 21). This is the code for mlkem1024_dec from mlkem-  *)
(* native's portable C implementation compiled by gcc 12 with -Os (see     *)
(* mlkem_native/README.md). It checks the decapsulation key with           *)
(* mlkem1024_check_sk, and returns -5 if the check fails. Otherwise it     *)
(* decrypts the ciphertext into m' with mlkem1024_indcpa_dec, computes K'  *)
(* and r' as G of m' followed by the hash h in the key with                *)
(* mlkem_sha3_512, encrypts m' with r' again by mlkem1024_indcpa_enc,      *)
(* compares the result with the ciphertext in constant time with           *)
(* mlk_ct_memcmp_1, computes J of z (in the key) followed by the           *)
(* ciphertext into a buffer on the stack with mlkem_shake256, and replaces *)
(* it by K' if the ciphertexts are equal, again in constant time, by a     *)
(* loop over the 32 bytes, and copies it to ss, which it writes only       *)
(* there. In both cases it zeroes its buffers by mlk_zeroize_2, which      *)
(* calls memset. It is verified in the whole image (see libmlkem.ml),      *)
(* using the theorems for mlkem1024_check_sk, mlkem1024_indcpa_dec,        *)
(* mlkem_sha3_512, mlkem1024_indcpa_enc, mlk_ct_memcmp_1, mlkem_shake256   *)
(* and mlk_zeroize_2 in the image and the contract for memcpy.             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/check_sk_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/indcpa_dec_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/indcpa_enc_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_1_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_2_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem1024_dec:
        +0x0: sub     sp, sp, #0x730
        +0x4: stp     x23, x24, [sp, #32]
        +0x8: mov     x23, x0
        +0xc: adrp    x0, <page>
       +0x10: ldr     x0, [x0, #4088]  // got_stack_chk_guard
       +0x14: stp     x19, x20, [sp]
       +0x18: add     x19, sp, #0x6f
       +0x1c: stp     x21, x22, [sp, #16]
       +0x20: and     x19, x19, #0xffffffffffffffe0
       +0x24: mov     x21, x2
       +0x28: stp     x25, x26, [sp, #48]
       +0x2c: mov     x25, x1
       +0x30: add     x22, x19, #0x680
       +0x34: str     x30, [sp, #64]
       +0x38: add     x24, x19, #0x640
       +0x3c: ldr     x1, [x0]
       +0x40: str     x1, [sp, #1832]
       +0x44: mov     x1, #0x0
       +0x48: mov     x0, x2
       +0x4c: bl      <mlkem1024_check_sk>
       +0x50: mov     w20, w0
       +0x54: cbnz    w0, <mlkem1024_dec+0x128>
       +0x58: mov     x2, x21
       +0x5c: mov     x1, x25
       +0x60: mov     x0, x22
       +0x64: bl      <mlkem1024_indcpa_dec>
       +0x68: mov     w20, w0
       +0x6c: cbnz    w0, <mlkem1024_dec+0x128>
       +0x70: ldr     q0, [x21, #3104]
       +0x74: add     x0, x19, #0x6a0
       +0x78: ldr     q1, [x21, #3120]
       +0x7c: mov     x1, x22
       +0x80: mov     x2, #0x40
       +0x84: stp     q0, q1, [x0]
       +0x88: mov     x0, x24
       +0x8c: bl      <mlkem_sha3_512>
       +0x90: add     x3, x19, #0x660
       +0x94: add     x2, x21, #0x600
       +0x98: mov     x1, x22
       +0x9c: mov     x0, x19
       +0xa0: bl      <mlkem1024_indcpa_enc>
       +0xa4: mov     w20, w0
       +0xa8: cbnz    w0, <mlkem1024_dec+0x128>
       +0xac: mov     x2, #0x620
       +0xb0: mov     x1, x19
       +0xb4: mov     x0, x25
       +0xb8: bl      <mlk_ct_memcmp_1>
       +0xbc: ldr     q0, [x21, #3136]
       +0xc0: and     w26, w0, #0xff
       +0xc4: ldr     q1, [x21, #3152]
       +0xc8: mov     x1, x25
       +0xcc: add     x0, x19, #0x20
       +0xd0: neg     w26, w26
       +0xd4: stp     q0, q1, [x19]
       +0xd8: bl      <memcpy@plt>
       +0xdc: mov     x0, x22
       +0xe0: mov     x3, #0x640
       +0xe4: mov     x2, x19
       +0xe8: mov     x1, #0x20
       +0xec: bl      <mlkem_shake256>
       +0xf0: mov     x3, x22
       +0xf4: mov     x0, #0x0
       +0xf8: ldrb    w2, [x24, x0]
       +0xfc: mov     w1, w26
      +0x100: ldrb    w4, [x3]
      +0x104: add     x0, x0, #0x1
      +0x108: eor     w4, w2, w4
      +0x10c: and     w1, w4, w1, asr #16
      +0x110: eor     w2, w2, w1
      +0x114: strb    w2, [x3], #1
      +0x118: cmp     x0, #0x20
      +0x11c: b.ne    <mlkem1024_dec+0xf8>
      +0x120: ldp     q0, q1, [x22]
      +0x124: stp     q0, q1, [x23]
      +0x128: mov     x0, x19
      +0x12c: mov     x1, #0x640
      +0x130: bl      <mlk_zeroize_2>
      +0x134: mov     x0, x24
      +0x138: mov     x1, #0x40
      +0x13c: bl      <mlk_zeroize_2>
      +0x140: mov     x0, x22
      +0x144: mov     x1, #0x40
      +0x148: bl      <mlk_zeroize_2>
      +0x14c: adrp    x0, <page>
      +0x150: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x154: ldr     x2, [sp, #1832]
      +0x158: ldr     x1, [x0]
      +0x15c: subs    x2, x2, x1
      +0x160: mov     x1, #0x0
      +0x164: b.eq    <join2>
      +0x168: bl      <__stack_chk_fail@plt>
      +0x16c: ldp     x21, x22, [sp, #16]
      +0x170: mov     w0, w20
      +0x174: ldp     x19, x20, [sp]
      +0x178: ldp     x23, x24, [sp, #32]
      +0x17c: ldp     x25, x26, [sp, #48]
      +0x180: ldr     x30, [sp, #64]
      +0x184: add     sp, sp, #0x730
      +0x188: ret
 ***)

let MLKEM_NATIVE_DEC_K4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "plt_memcpy"; layout_range "mlkem1024_dec"];;

let KD4_EXEC = MLKEM_NATIVE_DEC_K4_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-1024, the input check of    *)
(* FIPS 203 in terms of the result of mlkem1024_check_sk, and the address of  *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_1024_STMT =
  `!ek m r. LENGTH(kpke_encrypt mlkem1024 ek m r) = 1568`;;

let KPKE_ENCRYPT_LENGTH_1024 = assume_spec KPKE_ENCRYPT_LENGTH_1024_STMT;;

let KPKE_DECRYPT_LENGTH_1024_STMT =
  `!dk c. LENGTH(kpke_decrypt mlkem1024 dk c) = 32`;;

let KPKE_DECRYPT_LENGTH_1024 = assume_spec KPKE_DECRYPT_LENGTH_1024_STMT;;

let KD4_CHECK_STMT =
  `!dk c. LENGTH dk = 3168 /\ LENGTH c = 1568
          ==> (mlkem_decaps_check mlkem1024 dk c <=>
               num_of_bytelist(mlkem_slice 3104 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk)))`;;

let KD4_CHECK = assume_spec KD4_CHECK_STMT;;

let KD4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 22975)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 22944 else 22960))`;;

let KD4_BUFFER_ADDRESS = assume_spec KD4_BUFFER_ADDRESS_STMT;;

let KD4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD4_BUFFER_ADDRESS))
    else NO_TAC);;

(*** The test of the loop exit in the form that the simulation gives ***)

let KD4_CMOV_TEST_STMT =
  `!i. i < 32
       ==> (val(word (i + 18446744073709551585):int64) = 0 <=>
            ~(i + 1 < 32))`;;

let KD4_CMOV_TEST = assume_spec KD4_CMOV_TEST_STMT;;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_DEC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_MEMCMP_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let KD4_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,3168)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,1536; 1536,1568; 3104,32; 3136,32]
    else NO_TAC);;

let KD4_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 1536 1568 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list))`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 21;;

let KD4_ZEROIZE_TAC n k =
  LOCAL_ZEROIZE_TAC
   [`read X0 s`; mk_small_numeral n; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`; `read SP s`; `read X30 s`] k;;

let KD4_FAIL_TAC =
  ARM_STEPS_TAC KD4_EXEC (22--26) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 1600 27 THEN
  ARM_STEPS_TAC KD4_EXEC (28--30) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 64 31 THEN
  ARM_STEPS_TAC KD4_EXEC (32--34) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 64 35 THEN
  ARM_STEPS_TAC KD4_EXEC [36] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (37--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext. The invariant   *)
(* of the conditional move at iteration i states that the first i bytes at   *)
(* ss are those of K' if the ciphertexts are equal and those of the result   *)
(* of J otherwise, and the others still those of the result of J. The frame  *)
(* has the facts needed after the loop.                                      *)
(* ------------------------------------------------------------------------- *)

let KD4_MP = `kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c`;;

let KD4_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c)
                  (mlkem_slice 3104 32 dk))`;;

let KD4_KP = mk_comb(`mlkem_slice 0 32`,KD4_GG);;

let KD4_RR = mk_comb(`mlkem_slice 32 32`,KD4_GG);;

let KD4_CP = list_mk_comb(`kpke_encrypt mlkem1024`,
  [`mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR]);;

let KD4_ZZ = `mlkem_slice 3136 32 (dk:byte list)`;;

let KD4_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 3136 32 dk) c)) 32`;;

let KD4_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD4_CP));;

let KD4_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD4_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD4_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD4_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD4_ZZ),`ZZ:num`;
         KD4_EQ,`EQ:bool`] tm;;

let KD4_FRAME b = KD4_SUBST(parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word 22864) /\\
  read X19 s = word_add stackpointer (word %d) /\\
  read X20 s = word 0 /\\
  read X22 s = word_add stackpointer (word %d) /\\
  read X24 s = word_add stackpointer (word %d) /\\
  read X27 s = x27_init /\\ read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22864))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22872))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22880))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22888))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22896))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22904))) s =
  x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22912))) s =
  x25_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22920))) s =
  x26_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22928))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 24696))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  b (b + 1664) (b + 1600) (b + 1600)));;

let KD4_CMOV_INV b = KD4_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word i /\\
        read X3 s = word_add (word_add stackpointer (word %d)) (word i) /\\
        read X23 s = ss /\\
        read X26 s = (if EQ then word 0 else word 4294967041) /\\
        read (memory :> bytes(word_add stackpointer (word %d),i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add (word_add stackpointer (word %d))
                                       (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"
  (b + 1664) (b + 1664) (b + 1664)));;

let KD4_CMOV_INV_FRAME b =
  let inv = KD4_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD4_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the conditional move: the check of the key, the         *)
(* decryption, G of m' and h, the reencryption, the comparison of the        *)
(* ciphertexts and its result as a mask, J of z and the ciphertext copied    *)
(* after z with memcpy.                                                      *)
(* ------------------------------------------------------------------------- *)

let KD4_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 1664),`a:int64`;
           KD4_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 3104 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_1024];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD4_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 3104 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_1024] THEN ARITH_TAC;
    ALL_TAC];;

let KD4_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 1600) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD4_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD4_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

(*** The mask in x26 from the result of the comparison ***)

let KD4_MASK_TAC s =
  let x26 = mk_comb(`read X26`,mk_var(s,`:armstate`)) in
  SUBGOAL_THEN
   (mk_eq(x26,`if EQ then word 0 else word 4294967041:int64`) |>
    KD4_SUBST)
  ASSUME_TAC THENL
   [ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

let KD4_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP b,`a:int64`]
     `read (memory :> bytes(a,1600)) s =
      num_of_bytelist(APPEND (mlkem_slice 3136 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1600 = 32 + 1568`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 3136 32 (dk:byte list)) c) = 1600`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD4_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 3104):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 3136):int64` THEN
  ARM_STEPS_TAC KD4_EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (5--10) THEN KD4_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD4_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD4_EXEC (22--27) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `mlkem_slice 0 1536 (dk:byte list)`; `c:byte list`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 28 THEN
  ARM_STEPS_TAC KD4_EXEC (29--38) THEN
  KEM_JOIN_TAC (KEM_SP(b + 1696)) `mlkem_slice 3104 32 (dk:byte list)`
    (st 38) THEN
  KD4_G_INPUT_TAC b (st 38) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD4_MP),
            `mlkem_slice 3104 32 (dk:byte list)`);
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 39 THEN
  KD4_KR_TAC b (st 39) THEN
  ARM_STEPS_TAC KD4_EXEC (40--44) THEN KEM_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_1024]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 45 THEN

  (*** The comparison, the mask and J of z and the ciphertext ***)

  ARM_STEPS_TAC KD4_EXEC (46--51) THEN
  LOCAL_MEMCMP_TAC
   [`read X0 s`; `read X1 s`; `1568`; `num_of_bytelist(c:byte list)`;
    mk_comb(`num_of_bytelist`,KD4_CP); `pc:num`; `read X30 s`] 52 THEN
  ARM_STEPS_TAC KD4_EXEC (53--58) THEN KD4_MASK_TAC (st 58) THEN
  ARM_STEPS_TAC KD4_EXEC (59--60) THEN
  KEM_JOIN_TAC (KEM_SP b) KD4_ZZ (st 60) THEN
  LIBC_PLT_TAC KD4_EXEC 60 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD4_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 65 THEN
  KD4_J_INPUT_TAC b (st 65) THEN
  ARM_STEPS_TAC KD4_EXEC (66--70) THEN KEM_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 3136 32 (dk:byte list)) c`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 71 THEN
  ARM_STEPS_TAC KD4_EXEC (72--73) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD4_CMOV_BODY_TAC b =
  let buf = KEM_SP(b + 1664) in
  let nrm = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 1600); `32`; mk_comb(`num_of_bytelist`,KD4_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(nrm th)) THEN
  SUBGOAL_THEN
   (KD4_SUBST(subst [buf,`bf:int64`]
     `read (memory :> bytes(word_add bf (word i),(31 - i) + 1)) s0 =
      KB DIV 2 EXP (8 * i)`))
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC th1 THEN ASSUME_TAC(nrm th1) THEN
      ASSUME_TAC th2 THEN ASSUME_TAC(nrm th2))] THEN
  ARM_STEPS_TAC KD4_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_ADD; MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`);
    MP (SPEC `i:num` KD4_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [(ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
    (REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
    (REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE) THEN NO_TAC;
    (REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
     REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN
     ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
     GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
     SPEC_TAC(KD4_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
              `x:byte`) THEN
     SPEC_TAC(KD4_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
              `y:byte`) THEN
     REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC) THEN NO_TAC;
    (REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; KEM_DIV_BYTE] THEN
     RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     ASM_REWRITE_TAC[]) THEN NO_TAC];;

let KD4_FINAL_TAC =
  REWRITE_TAC[mlkem1024; MLKEM_DECAPS_ALT] THEN REWRITE_TAC[GSYM mlkem1024] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD4_CP,`c:byte list`),KD4_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_1024];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD4_EXIT_B_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  KEM_HALVES_TAC (KEM_SP(b + 1664)) THEN
  ARM_STEPS_TAC KD4_EXEC (1--2) THEN
  MP_TAC(SPECL [`ss:int64`;
                KD4_SUBST `(if EQ then KP else KB) MOD 2 EXP (8 * 32)`;
                `s2:armstate`] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ARM_STEPS_TAC KD4_EXEC (3--5) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 1600 6 THEN
  ARM_STEPS_TAC KD4_EXEC (7--9) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 64 10 THEN
  ARM_STEPS_TAC KD4_EXEC (11--13) THEN KEM_GOT_TAC THEN
  KD4_ZEROIZE_TAC 64 14 THEN
  ARM_STEPS_TAC KD4_EXEC [15] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (16--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD4_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy. The      *)
(* decapsulation key dk of 3168 bytes is at sk and the ciphertext c of 1568  *)
(* bytes at ct, and if they pass the check of FIPS 203, the shared secret of *)
(* 32 bytes written at ss is that of mlkem_decaps_internal mlkem1024 dk c in  *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it    *)
(* returns -5. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix from the seed in the key and that the stack does not        *)
(* contain address 0, for mlkem1024_indcpa_enc. The stack is the 1360 bytes   *)
(* of the function and the 22864 used by mlkem1024_indcpa_enc below them. The  *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (c' and then z and the   *)
(* ciphertext), 1600 (K' and r') and 1664 (m' and h), and on the check of the *)
(* key.                                                                      *)
(* ------------------------------------------------------------------------- *)

let KD4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24704 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 24704):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD4_CHECK; ASSUME `LENGTH(dk:byte list) = 3168`;
           ASSUME `LENGTH(c:byte list) = 1568`] THEN
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
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD4_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop1`
   `pc + mlkem1024_dec_loop1_exit`
   (KD4_CMOV_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD4_PART1_TAC b; KD4_CMOV_BODY_TAC b; KD4_EXIT_B_TAC b];;

let KD4_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (5--10) THEN KD4_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD4_CHECK_TAC THEN KD4_FAIL_TAC;;

let KD4_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD4_OK_TAC b; KD4_BAD_TAC];;

let MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 3168 /\ LENGTH c = 1568 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 24704),24704) /\
        nonoverlapping (ct,1568) (word pc,libmlkem_size) /\
        nonoverlapping (sk,3168) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 24704),24704) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 24704),24704)]
         [(ct,1568); (sk,3168); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem1024_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,3168)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem1024 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist(mlkem_decaps_internal mlkem1024 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem1024 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 24704),24704)])`;;

let MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem1024_indcpa_enc and mlk_zeroize_2) and the safety     *)
(* contract for memcpy. The events depend only on the addresses and on the   *)
(* encapsulation key ek in the decapsulation key and the hash h stored with  *)
(* it, through the check of the hash, given by the combined theorem for      *)
(* mlkem1024_check_sk, and the reencryption, but not on the secret key, z or  *)
(* the ciphertext: the comparison of the ciphertexts is mlk_ct_memcmp_1    *)
(* and the selection of the shared secret is a loop in constant time. The    *)
(* buffers are kept at their offset from the stack pointer as a conditional, *)
(* and the invariant of the loop has only the pointers and the frame.        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD4_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then f_ev_ok ss ct sk guard mf mc pc sp ra ek h
   else f_ev_bad ss ct sk guard mf mc pc sp ra ek h
   :(uarch_event)list`;;

let KD4_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`];;

let KD4_SAFE_B =
 `if aligned 32 (stackpointer:int64) then 22944 else 22960`;;

let KD4_SAFE_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let KD4_SAFE_BUFFER_TAC =
  SUBGOAL_THEN (subst [KD4_SAFE_B,`b:num`]
   `word_and (word_add stackpointer (word 22975))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word b)`)
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KD4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let KD4_SAFE_CALL_TAC name ilist n =
  KD4_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,KD4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD4_SAFE_ZEROIZE_TAC n k =
  KD4_SAFE_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; mk_small_numeral n; `pc:num`;
    `read SP s`; `read X30 s`] k;;

let KD4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP
         MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_ZEROIZE" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL
         th1) "H_CHECK" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_SHA3_512" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_SHAKE256" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_MEMCMP" THEN
  CONCRETIZE_F_EVENTS_TAC KD4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 24704):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `22944 <= (if aligned 32 (stackpointer:int64) then 22944 else 22960) /\
    (if aligned 32 (stackpointer:int64) then 22944 else 22960) <= 22960`
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
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th))) THEN
  ABBREV_TAC `ekk = mlkem_slice 1536 1568 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 3104 32 (dk:byte list)`;;

let KD4_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KD4_SK_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (5--10) THEN KD4_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 21;;

(*** The selection loop is run through instruction by instruction: the ***)
(*** events do not depend on the data, and each iteration is the same. ***)

let KD4_SAFE_OK_TAC =
  KD4_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD4_EXEC (22--27) THEN KEM_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC KD4_EXEC (29--38) THEN KEM_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD4_EXEC (40--44) THEN KEM_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 45 THEN
  ARM_STEPS_TAC KD4_EXEC (46--51) THEN
  KD4_SAFE_CALL_TAC "H_MEMCMP"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `1568`; `pc:num`;
    `read X30 s`] 52 THEN
  ARM_STEPS_TAC KD4_EXEC (53--60) THEN LIBC_PLT_TAC KD4_EXEC 60 THEN
  KD4_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD4_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD4_SAFE_ALLOWED) 65 THEN
  ARM_STEPS_TAC KD4_EXEC (66--70) THEN KEM_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `1600`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 71 THEN
  ARM_STEPS_TAC KD4_EXEC (72--73) THEN
  ARM_STEPS_TAC KD4_EXEC (74--393) THEN
  ARM_STEPS_TAC KD4_EXEC (394--395) THEN
  ARM_STEPS_TAC KD4_EXEC (396--398) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 1600 399 THEN
  ARM_STEPS_TAC KD4_EXEC (400--402) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 64 403 THEN
  ARM_STEPS_TAC KD4_EXEC (404--406) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 64 407 THEN
  ARM_STEPS_TAC KD4_EXEC [408] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (409--422) THEN
  KD4_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_BAD_TAC =
  KD4_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD4_EXEC (22--26) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 1600 27 THEN
  ARM_STEPS_TAC KD4_EXEC (28--30) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 64 31 THEN
  ARM_STEPS_TAC KD4_EXEC (32--34) THEN KEM_GOT_TAC THEN
  KD4_SAFE_ZEROIZE_TAC 64 35 THEN
  ARM_STEPS_TAC KD4_EXEC [36] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (37--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ss ct sk (dk:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH dk = 3168 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 24704),24704) /\
          nonoverlapping (ct,1568) (word pc,libmlkem_size) /\
          nonoverlapping (sk,3168) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 24704),24704) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 24704),24704)]
           [(ct,1568); (sk,3168); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem1024_dec) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ss; ct; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,3168)) s = num_of_bytelist dk /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ss ct sk guard mf mc pc
                              (word_sub stackpointer (word 24704))
                              returnaddress
                              (mlkem_slice 1536 1568 dk)
                              (mlkem_slice 3104 32 dk) /\
                       memaccess_inbounds e2
                        [ct,1568; sk,3168; ss,32;
                         word_sub stackpointer (word 24704),24704;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256]
                        [ss,32; word_sub stackpointer (word 24704),24704]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 24704),24704)])`;;

let MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
