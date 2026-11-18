(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-768 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem768_dec from mlkem-     *)
(* native's portable C implementation compiled by gcc 12 with -Os (see       *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem768_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem768_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem768_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time with mlk_ct_memcmp_3, computes J of  *)
(* z (in the key) followed by the ciphertext into the shared secret with     *)
(* mlkem_shake256, and replaces it by K' if the ciphertexts are equal, again *)
(* in constant time, by a loop over the 32 bytes. In both cases it zeroes    *)
(* its buffers by mlk_zeroize_8, which calls memset. It is verified in the   *)
(* whole image (see libmlkem.ml), using the theorems for mlkem768_check_sk,  *)
(* mlkem768_indcpa_dec, mlkem_sha3_512, mlkem768_indcpa_enc,                 *)
(* mlk_ct_memcmp_3, mlkem_shake256 and mlk_zeroize_8 in the image and the    *)
(* contract for memcpy.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/check_sk_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/indcpa_dec_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/indcpa_enc_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_8_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem768_dec:
       +0x0: sub     sp, sp, #0x550
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x22, x0
       +0xc: mov     x21, x2
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x18: stp     x19, x20, [sp]
      +0x1c: add     x19, sp, #0x6f
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: and     x19, x19, #0xffffffffffffffe0
      +0x28: add     x23, x19, #0x4a0
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: mov     x25, x1
      +0x34: add     x24, x19, #0x460
      +0x38: str     x30, [sp, #64]
      +0x3c: ldr     x1, [x0]
      +0x40: str     x1, [sp, #1352]
      +0x44: mov     x1, #0x0
      +0x48: mov     x0, x2
      +0x4c: bl      <mlkem768_check_sk>
      +0x50: mov     w20, w0
      +0x54: cbnz    w0, <mlkem768_dec+0x11c>
      +0x58: mov     x2, x21
      +0x5c: mov     x1, x25
      +0x60: mov     x0, x23
      +0x64: bl      <mlkem768_indcpa_dec>
      +0x68: mov     w20, w0
      +0x6c: cbnz    w0, <mlkem768_dec+0x11c>
      +0x70: ldr     q0, [x21, #2336]
      +0x74: add     x0, x19, #0x4c0
      +0x78: ldr     q1, [x21, #2352]
      +0x7c: mov     x1, x23
      +0x80: mov     x2, #0x40
      +0x84: stp     q0, q1, [x0]
      +0x88: mov     x0, x24
      +0x8c: bl      <mlkem_sha3_512>
      +0x90: add     x3, x19, #0x480
      +0x94: add     x2, x21, #0x480
      +0x98: mov     x1, x23
      +0x9c: mov     x0, x19
      +0xa0: bl      <mlkem768_indcpa_enc>
      +0xa4: mov     w20, w0
      +0xa8: cbnz    w0, <mlkem768_dec+0x11c>
      +0xac: mov     x2, #0x440
      +0xb0: mov     x1, x19
      +0xb4: mov     x0, x25
      +0xb8: bl      <mlk_ct_memcmp_3>
      +0xbc: ldr     q0, [x21, #2368]
      +0xc0: and     w26, w0, #0xff
      +0xc4: ldr     q1, [x21, #2384]
      +0xc8: mov     x1, x25
      +0xcc: add     x0, x19, #0x20
      +0xd0: neg     w26, w26
      +0xd4: stp     q0, q1, [x19]
      +0xd8: bl      <memcpy@plt>
      +0xdc: mov     x1, #0x20
      +0xe0: mov     x2, x19
      +0xe4: mov     x0, x22
      +0xe8: mov     x3, #0x460
      +0xec: bl      <mlkem_shake256>
      +0xf0: mov     x1, #0x0
      +0xf4: ldrb    w0, [x24, x1]
      +0xf8: mov     w2, w26
      +0xfc: ldrb    w3, [x22, x1]
     +0x100: eor     w3, w0, w3
     +0x104: and     w2, w3, w2, asr #16
     +0x108: eor     w0, w0, w2
     +0x10c: strb    w0, [x22, x1]
     +0x110: add     x1, x1, #0x1
     +0x114: cmp     x1, #0x20
     +0x118: b.ne    <mlkem768_dec+0xf4>
     +0x11c: mov     x0, x19
     +0x120: mov     x1, #0x460
     +0x124: bl      <mlk_zeroize_8>
     +0x128: mov     x0, x24
     +0x12c: mov     x1, #0x40
     +0x130: bl      <mlk_zeroize_8>
     +0x134: mov     x0, x23
     +0x138: mov     x1, #0x40
     +0x13c: bl      <mlk_zeroize_8>
     +0x140: adrp    x0, <page>
     +0x144: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x148: ldr     x2, [sp, #1352]
     +0x14c: ldr     x1, [x0]
     +0x150: subs    x2, x2, x1
     +0x154: mov     x1, #0x0
     +0x158: b.eq    <mlkem768_dec+0x160>
     +0x15c: bl      <__stack_chk_fail@plt>
     +0x160: ldp     x21, x22, [sp, #16]
     +0x164: mov     w0, w20
     +0x168: ldp     x19, x20, [sp]
     +0x16c: ldp     x23, x24, [sp, #32]
     +0x170: ldp     x25, x26, [sp, #48]
     +0x174: ldr     x30, [sp, #64]
     +0x178: add     sp, sp, #0x550
     +0x17c: ret
 ***)

let MLKEM_NATIVE_DEC_K3_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "plt_memcpy"; layout_range "mlkem768_dec"];;

let KD3_EXEC = MLKEM_NATIVE_DEC_K3_GCC12_OS_EXEC;;

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

let KD3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 17055)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 17024 else 17040))`;;

let KD3_BUFFER_ADDRESS = assume_spec KD3_BUFFER_ADDRESS_STMT;;

let KD3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD3_BUFFER_ADDRESS))
    else NO_TAC);;

(*** The test of the loop exit in the form that the simulation gives ***)

let KD3_CMOV_TEST_STMT =
  `!i. i < 32
       ==> (val(word (i + 18446744073709551585):int64) = 0 <=>
            ~(i + 1 < 32))`;;

let KD3_CMOV_TEST = assume_spec KD3_CMOV_TEST_STMT;;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_SK_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_DEC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_MEMCMP_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CT_MEMCMP_3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_8_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

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
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 21;;

let KD3_ZEROIZE_TAC n k =
  LOCAL_ZEROIZE_TAC
   [`read X0 s`; mk_small_numeral n; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`; `read SP s`; `read X30 s`] k;;

let KD3_FAIL_TAC =
  ARM_STEPS_TAC KD3_EXEC (22--26) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 1120 27 THEN
  ARM_STEPS_TAC KD3_EXEC (28--30) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 64 31 THEN
  ARM_STEPS_TAC KD3_EXEC (32--34) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 64 35 THEN
  ARM_STEPS_TAC KD3_EXEC [36] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (37--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext. The invariant   *)
(* of the conditional move at iteration i states that the first i bytes at   *)
(* ss are those of K' if the ciphertexts are equal and those of the result   *)
(* of J otherwise, and the others still those of the result of J. The frame  *)
(* has the facts needed after the loop.                                      *)
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
 "read SP s = word_add stackpointer (word 16944) /\\
  read X19 s = word_add stackpointer (word %d) /\\
  read X20 s = word 0 /\\
  read X23 s = word_add stackpointer (word %d) /\\
  read X24 s = word_add stackpointer (word %d) /\\
  read X27 s = x27_init /\\ read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16944))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16952))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16960))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16968))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16976))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16984))) s =
  x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 16992))) s =
  x25_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17000))) s =
  x26_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 17008))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 18296))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  b (b + 1184) (b + 1120) (b + 1120)));;

let KD3_CMOV_INV b = KD3_SUBST(parse_term(Printf.sprintf
 "\\i s. read X1 s = word i /\\
        read X22 s = ss /\\
        read X26 s = (if EQ then word 0 else word 4294967041) /\\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"));;

let KD3_CMOV_INV_FRAME b =
  let inv = KD3_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD3_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the conditional move: the check of the key, the         *)
(* decryption, G of m' and h, the reencryption, the comparison of the        *)
(* ciphertexts and its result as a mask, J of z and the ciphertext copied    *)
(* after z with memcpy.                                                      *)
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

(*** The mask in x26 from the result of the comparison ***)

let KD3_MASK_TAC s =
  let x26 = mk_comb(`read X26`,mk_var(s,`:armstate`)) in
  SUBGOAL_THEN
   (mk_eq(x26,`if EQ then word 0 else word 4294967041:int64`) |>
    KD3_SUBST)
  ASSUME_TAC THENL
   [ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

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

let KD3_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 2336):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 2368):int64` THEN
  ARM_STEPS_TAC KD3_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (6--10) THEN KD3_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD3_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD3_EXEC (22--27) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `mlkem_slice 0 1152 (dk:byte list)`; `c:byte list`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 28 THEN
  ARM_STEPS_TAC KD3_EXEC (29--38) THEN
  KEM_JOIN_TAC (KEM_SP(b + 1216)) `mlkem_slice 2336 32 (dk:byte list)`
    (st 38) THEN
  KD3_G_INPUT_TAC b (st 38) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD3_MP),
            `mlkem_slice 2336 32 (dk:byte list)`);
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 39 THEN
  KD3_KR_TAC b (st 39) THEN
  ARM_STEPS_TAC KD3_EXEC (40--44) THEN KEM_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_768]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 45 THEN

  (*** The comparison, the mask and J of z and the ciphertext ***)

  ARM_STEPS_TAC KD3_EXEC (46--51) THEN
  LOCAL_MEMCMP_TAC
   [`read X0 s`; `read X1 s`; `1088`; `num_of_bytelist(c:byte list)`;
    mk_comb(`num_of_bytelist`,KD3_CP); `pc:num`; `read X30 s`] 52 THEN
  ARM_STEPS_TAC KD3_EXEC (53--58) THEN KD3_MASK_TAC (st 58) THEN
  ARM_STEPS_TAC KD3_EXEC (59--60) THEN
  KEM_JOIN_TAC (KEM_SP b) KD3_ZZ (st 60) THEN
  LIBC_PLT_TAC KD3_EXEC 60 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 65 THEN
  KD3_J_INPUT_TAC b (st 65) THEN
  ARM_STEPS_TAC KD3_EXEC (66--70) THEN KEM_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 2368 32 (dk:byte list)) c`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 71 THEN
  ARM_STEPS_TAC KD3_EXEC [72] THEN
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

let KD3_CMOV_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 1120); `32`; mk_comb(`num_of_bytelist`,KD3_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN
    ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th)) THEN
  SUBGOAL_THEN
   (KD3_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
    ASSUME_TAC th1 THEN ASSUME_TAC th2 THEN
    ARM_STEPS_TAC KD3_EXEC (1--10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [GSYM WORD_ADD; MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`);
      MP (SPEC `i:num` KD3_CMOV_TEST) (ASSUME `i < 32`)]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
      SPEC_TAC(KD3_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
               `x:byte`) THEN
      SPEC_TAC(KD3_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
               `y:byte`) THEN
      REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
      REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                  KEM_DIV_BYTE] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[]]);;

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

let KD3_EXIT_B_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD3_EXEC (1--3) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 1120 4 THEN
  ARM_STEPS_TAC KD3_EXEC (5--7) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 64 8 THEN
  ARM_STEPS_TAC KD3_EXEC (9--11) THEN KEM_GOT_TAC THEN
  KD3_ZEROIZE_TAC 64 12 THEN
  ARM_STEPS_TAC KD3_EXEC [13] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (14--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD3_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy. The      *)
(* decapsulation key dk of 2400 bytes is at sk and the ciphertext c of 1088  *)
(* bytes at ct, and if they pass the check of FIPS 203, the shared secret of *)
(* 32 bytes written at ss is that of mlkem_decaps_internal mlkem768 dk c in  *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it    *)
(* returns -5. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix from the seed in the key and that the stack does not        *)
(* contain address 0, for mlkem768_indcpa_enc. The stack is the 1360 bytes   *)
(* of the function and the 16944 used by mlkem768_indcpa_enc below them. The  *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (c' and then z and the   *)
(* ciphertext), 1120 (K' and r') and 1184 (m' and h), and on the check of the *)
(* key.                                                                      *)
(* ------------------------------------------------------------------------- *)

let KD3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 18304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 18304):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--28) THEN
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
  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem768_dec_loop1`
   `pc + mlkem768_dec_loop1_exit`
   (KD3_CMOV_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD3_PART1_TAC b; KD3_CMOV_BODY_TAC b; KD3_EXIT_B_TAC];;

let KD3_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (6--10) THEN KD3_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD3_CHECK_TAC THEN KD3_FAIL_TAC;;

let KD3_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD3_OK_TAC b; KD3_BAD_TAC];;

let MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 2400 /\ LENGTH c = 1088 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 18304),18304) /\
        nonoverlapping (ct,1088) (word pc,libmlkem_size) /\
        nonoverlapping (sk,2400) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 18304),18304) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 18304),18304)]
         [(ct,1088); (sk,2400); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
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
                memory :> bytes(word_sub stackpointer (word 18304),18304)])`;;

let MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_indcpa_enc and mlk_zeroize_8) and the safety     *)
(* contract for memcpy. The events depend only on the addresses and on the   *)
(* encapsulation key ek in the decapsulation key and the hash h stored with  *)
(* it, through the check of the hash, given by the combined theorem for      *)
(* mlkem768_check_sk, and the reencryption, but not on the secret key, z or  *)
(* the ciphertext: the comparison of the ciphertexts is mlk_ct_memcmp_3    *)
(* and the selection of the shared secret is a loop in constant time. The    *)
(* buffers are kept at their offset from the stack pointer as a conditional, *)
(* and the invariant of the loop has only the pointers and the frame.        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD3_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then f_ev_ok ss ct sk guard mf mc pc sp ra ek h
   else f_ev_bad ss ct sk guard mf mc pc sp ra ek h
   :(uarch_event)list`;;

let KD3_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`];;

let KD3_SAFE_B =
 `if aligned 32 (stackpointer:int64) then 17024 else 17040`;;

let KD3_SAFE_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let KD3_SAFE_BUFFER_TAC =
  SUBGOAL_THEN (subst [KD3_SAFE_B,`b:num`]
   `word_and (word_add stackpointer (word 17055))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word b)`)
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KD3_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let KD3_SAFE_CALL_TAC name ilist n =
  KD3_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,KD3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD3_SAFE_ZEROIZE_TAC n k =
  KD3_SAFE_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; mk_small_numeral n; `pc:num`;
    `read SP s`; `read X30 s`] k;;

let KD3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP
         MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_ZEROIZE_8_GCC12_OS_IMAGE_SUBROUTINE_SAFE
         sth) "H_ZEROIZE" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_CHECK_SK_K3_GCC12_OS_IMAGE_SUBROUTINE_FULL
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
    MLKEM_NATIVE_CT_MEMCMP_3_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_MEMCMP" THEN
  CONCRETIZE_F_EVENTS_TAC KD3_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 18304):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `17024 <= (if aligned 32 (stackpointer:int64) then 17024 else 17040) /\
    (if aligned 32 (stackpointer:int64) then 17024 else 17040) <= 17040`
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
  ARM_STEPS_TAC KD3_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (6--10) THEN KD3_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (11--20) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 21;;

(*** The selection loop is run through instruction by instruction: the ***)
(*** events do not depend on the data, and each iteration is the same. ***)

let KD3_SAFE_OK_TAC =
  KD3_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD3_EXEC (22--27) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC KD3_EXEC (29--38) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD3_EXEC (40--44) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 45 THEN
  ARM_STEPS_TAC KD3_EXEC (46--51) THEN
  KD3_SAFE_CALL_TAC "H_MEMCMP"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `1088`; `pc:num`;
    `read X30 s`] 52 THEN
  ARM_STEPS_TAC KD3_EXEC (53--60) THEN LIBC_PLT_TAC KD3_EXEC 60 THEN
  KD3_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD3_SAFE_ALLOWED) 65 THEN
  ARM_STEPS_TAC KD3_EXEC (66--70) THEN KEM_GOT_TAC THEN
  KD3_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `1120`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 71 THEN
  ARM_STEPS_TAC KD3_EXEC [72] THEN
  ARM_STEPS_TAC KD3_EXEC (73--392) THEN
  ARM_STEPS_TAC KD3_EXEC (393--395) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 1120 396 THEN
  ARM_STEPS_TAC KD3_EXEC (397--399) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 64 400 THEN
  ARM_STEPS_TAC KD3_EXEC (401--403) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 64 404 THEN
  ARM_STEPS_TAC KD3_EXEC [405] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (406--419) THEN
  KD3_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BAD_TAC =
  KD3_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD3_EXEC (22--26) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 1120 27 THEN
  ARM_STEPS_TAC KD3_EXEC (28--30) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 64 31 THEN
  ARM_STEPS_TAC KD3_EXEC (32--34) THEN KEM_GOT_TAC THEN
  KD3_SAFE_ZEROIZE_TAC 64 35 THEN
  ARM_STEPS_TAC KD3_EXEC [36] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD3_EXEC (37--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
           (word_sub stackpointer (word 18304),18304) /\
          nonoverlapping (ct,1088) (word pc,libmlkem_size) /\
          nonoverlapping (sk,2400) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 18304),18304) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 18304),18304)]
           [(ct,1088); (sk,2400); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 18304))
                              returnaddress
                              (mlkem_slice 1152 1184 dk)
                              (mlkem_slice 2336 32 dk) /\
                       memaccess_inbounds e2
                        [ct,1088; sk,2400; ss,32;
                         word_sub stackpointer (word 18304),18304;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256]
                        [ss,32; word_sub stackpointer (word 18304),18304]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 18304),18304)])`;;

let MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
