(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four noise polynomials with eta = 3 from a seed and nonces.   *)
(* This is the code for mlkem512_poly_getnoise_eta1_4x from mlkem-native's   *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which computes 192 bytes of SHAKE256 of the seed *)
(* and each of the four nonces into buffers on the stack with                *)
(* mlkem_shake256x4, applies mlkem_poly_cbd3 to them, skipping the fourth    *)
(* polynomial if its pointer is null, and zeroes the buffers, the first ones *)
(* with memset. It is verified in the whole image (see                       *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x4730, using  *)
(* the theorems for mlkem_shake256x4 at 0x2a20 and mlkem_poly_cbd3 at 0x4ec4 *)
(* in the image and assuming the contracts for memset and memcpy in          *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native_shake256x4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_cbd3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image, and the PLT stub for memset:

    4730: sub     sp, sp, #0x480
    4734: stp     x19, x20, [sp, #16]
    4738: add     x20, sp, #0x7f
    473c: and     x20, x20, #0xffffffffffffffe0
    4740: stp     x21, x22, [sp, #32]
    4744: add     x10, x20, #0x340
    4748: add     x9, x20, #0x380
    474c: stp     x23, x24, [sp, #48]
    4750: add     x19, x20, #0x300
    4754: mov     x22, x2
    4758: stp     x25, x26, [sp, #64]
    475c: add     x8, x20, #0x3c0
    4760: add     x25, x20, #0x180
    4764: stp     x27, x30, [sp, #80]
    4768: add     x27, x20, #0x240
    476c: mov     x21, x3
    4770: ldp     q0, q1, [x4]
    4774: mov     x3, x27
    4778: adrp    x4, 1f000 <mlk_zetas+0x18c80>
    477c: ldr     x4, [x4, #4088]
    4780: mov     x24, x0
    4784: mov     x23, x1
    4788: mov     x0, x20
    478c: ldr     x2, [x4]
    4790: str     x2, [sp, #1144]
    4794: mov     x2, #0x0
    4798: stp     q0, q1, [x9]
    479c: mov     x2, x25
    47a0: stp     q0, q1, [x10]
    47a4: mov     x4, #0xc0
    47a8: add     x26, x20, x4
    47ac: strb    w5, [x19, #32]
    47b0: mov     x5, x19
    47b4: strb    w6, [x19, #96]
    47b8: mov     x6, x10
    47bc: strb    w7, [x19, #160]
    47c0: mov     x7, x9
    47c4: mov     x9, #0x21
    47c8: stp     x8, x9, [sp]
    47cc: ldrb    w9, [sp, #1152]
    47d0: stp     q0, q1, [x8]
    47d4: mov     x1, x26
    47d8: strb    w9, [x19, #224]
    47dc: stp     q0, q1, [x19]
    47e0: bl      2a20 <mlkem_shake256x4>
    47e4: mov     x1, x20
    47e8: mov     x0, x24
    47ec: bl      4ec4 <mlkem_poly_cbd3>
    47f0: mov     x1, x26
    47f4: mov     x0, x23
    47f8: bl      4ec4 <mlkem_poly_cbd3>
    47fc: mov     x1, x25
    4800: mov     x0, x22
    4804: bl      4ec4 <mlkem_poly_cbd3>
    4808: cbz     x21, 4818 <mlkem512_poly_getnoise_eta1_4x+0xe8>
    480c: mov     x1, x27
    4810: mov     x0, x21
    4814: bl      4ec4 <mlkem_poly_cbd3>
    4818: mov     x0, x20
    481c: mov     x2, #0x300
    4820: mov     w1, #0x0
    4824: bl      840 <memset@plt>
    4828: movi    v0.4s, #0x0
    482c: stp     q0, q0, [x19]
    4830: stp     q0, q0, [x19, #32]
    4834: stp     q0, q0, [x19, #64]
    4838: stp     q0, q0, [x19, #96]
    483c: stp     q0, q0, [x19, #128]
    4840: stp     q0, q0, [x19, #160]
    4844: stp     q0, q0, [x19, #192]
    4848: stp     q0, q0, [x19, #224]
    484c: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    4850: ldr     x0, [x0, #4088]
    4854: ldr     x2, [sp, #1144]
    4858: ldr     x1, [x0]
    485c: subs    x2, x2, x1
    4860: mov     x1, #0x0
    4864: b.ne    4884 <mlkem512_poly_getnoise_eta1_4x+0x154>
    4868: ldp     x19, x20, [sp, #16]
    486c: ldp     x21, x22, [sp, #32]
    4870: ldp     x23, x24, [sp, #48]
    4874: ldp     x25, x26, [sp, #64]
    4878: ldp     x27, x30, [sp, #80]
    487c: add     sp, sp, #0x480
    4880: ret
    4884: bl      830 <__stack_chk_fail@plt>

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x4730,0x4888; 0x840,0x850];;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16: the four outputs of SHAKE256, of 192 bytes each, and then its four *)
(* inputs, the seed and a nonce, at intervals of 64 bytes. The seed is       *)
(* copied to the inputs as two 128-bit words.                                *)
(* ------------------------------------------------------------------------- *)

let GETNOISE4_ALIGNED_16_32 = prove
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

let GETNOISE4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 1919)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 1888 else 1904))`,
  REWRITE_TAC[GETNOISE4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let GETNOISE4_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1919))
             (word 18446744073709551584):int64 =
    word_add stackpointer
     (word(if aligned 32 stackpointer then 1888 else 1904))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** Offset k of the buffer, as normalized by the simulation ***)

let GETNOISE4_AT k =
  let off = `if aligned 32 (stackpointer:int64) then 1888 else 1904` in
  let t = if k = 0 then off
          else mk_binop `(+):num->num->num` off (mk_small_numeral k) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,t));;

let GETNOISE4_READ_MEMORY_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The 33 bytes of one input to SHAKE256 from the seed and a nonce ***)

let GETNOISE4_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

let GETNOISE4_INPUT = prove
 (`!a:int64 (sd:byte list) b s:armstate.
        LENGTH sd = 32 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist sd MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist sd DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist sd`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GETNOISE4_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sd:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_MEMORY_BYTES_SNOC] THEN
  ASM_REWRITE_TAC[num_of_bytelist] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(*** Offsets in the buffers as single numbers ***)

let GETNOISE4_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let GETNOISE4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE GETNOISE4_ADDRESS_CONV th else th);;

(*** The input k in the buffer, at state s44, with the nonce byte b ***)

let GETNOISE4_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV GETNOISE4_INPUT in
  fun k b ->
    let a = GETNOISE4_AT (768 + 64 * k) in
    MP_TAC(SPECL [a; `sd:byte list`; b; `s44:armstate`] th) THEN
    ANTS_TAC THENL
     [CONV_TAC GETNOISE4_ADDRESS_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST;
      STRIP_TAC];;

(*** The GOT entries in the form in the precondition of the callee ***)

let GETNOISE4_GOT_TAC =
  MAP_EVERY (fun t ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] t) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [`read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
     g:int64`;
    `read (memory :> bytes64 (word_add (word pc) (word 131048))) s =
     g:int64`;
    `read (memory :> bytes64 (word_add (word pc) (word 131024))) s =
     g:int64`];;

(*** The test of whether the fourth pointer is null ***)

let GETNOISE4_BRANCH_TAC tm =
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && is_cond(rand(concl th))
    then REWRITE_RULE[VAL_EQ_0; ASSUME tm] th else th);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2944):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1888 <= (if aligned 32 (stackpointer:int64) then 1888 else 1904) /\
    (if aligned 32 (stackpointer:int64) then 1888 else 1904) <= 1904`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
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
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--27);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy as for    *)
(* mlkem_shake256x4. The seed is 32 bytes at seed, given as a list of bytes  *)
(* sd, and the nonces are the low bytes of the sixth to eighth arguments and *)
(* of the ninth, on the stack. For each polynomial, as for                   *)
(* mlkem512_poly_getnoise_eta2 but with eta = 3, the result is               *)
(* mlkem_poly_cbd3 applied to the first 192 bytes of shake256 of the seed    *)
(* followed by the nonce, except that if the fourth pointer is null there is *)
(* no fourth result. The stack is the 1152 bytes of the function and the     *)
(* 1792 used by mlkem_shake256x4 below them.                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let GETNOISE4_N nonce =
  vsubst [nonce,`nonce:int64`]
   `num_of_bytelist(list_of_seq
     (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) 192)`;;

(*** Up to the test of the fourth pointer: the inputs, SHAKE256, cbd3 ***)

let GETNOISE4_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GETNOISE4_READ_MEMORY_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (1--4) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (5--19) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (20--44) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  GETNOISE4_INPUT_TAC 0 `word_zx(nonce0:int64):byte` THEN
  GETNOISE4_INPUT_TAC 1 `word_zx(nonce1:int64):byte` THEN
  GETNOISE4_INPUT_TAC 2 `word_zx(nonce2:int64):byte` THEN
  GETNOISE4_INPUT_TAC 3 `word_zx(nonce3:int64):byte` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (45--45) THEN
  GETNOISE4_GOT_TAC THEN
  LOCAL_SHAKE256X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `192`;
    `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1888 else 1904) + 960))`;
    `33`; `APPEND (sd:byte list) [word_zx(nonce0:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce1:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce2:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce3:int64)]`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  MAP_EVERY (fun (k,nonce) ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
     ((k-3)--(k-1)) THEN
    LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; GETNOISE4_N nonce;
                    `pc:num`; `read X30 s`] k)
   [50,`nonce0:int64`; 54,`nonce1:int64`; 58,`nonce2:int64`] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (59--59);;

(*** From step k: zeroing the buffers, the stack guard, the return ***)

let GETNOISE4_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (k--(k+3)) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (k+3) THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (k+8) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   ((k+9)--(k+18)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   ((k+19)--(k+31)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2944),2944)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2944),2944)]
         [(seed,32); (stackpointer,1); (word pc,0x6480);
          (word(pc + 0x1fff8),8); (guard,8); (word(pc + 0x1ffe8),8);
          (word(pc + 0x1ffd0),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x4730) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [r0; r1; r2; r3; seed; nonce0; nonce1; nonce2] s /\
                  read (memory :> bytes8 stackpointer) s =
                  word_zx(nonce3:int64) /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read PC s = returnaddress /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce0])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce2])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (~(r3 = word 0) ==>
                   (let n = num_of_bytelist
                            (list_of_seq
                              (shake256 (APPEND sd [word_zx nonce3])) 192) in
                    !i. i < 256
                        ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                 s =
                            iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                  &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 5)) MOD 2)))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2944),2944)])`,
  MAP_EVERY X_GEN_TAC
   [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
    `sd:byte list`; `nonce0:int64`; `nonce1:int64`; `nonce2:int64`;
    `nonce3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2944 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  GETNOISE4_SETUP_TAC THEN
  ASM_CASES_TAC `r3:int64 = word 0` THENL
   [(*** The fourth pointer null, with no output for it ***)

    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    GETNOISE4_START_TAC THEN GETNOISE4_END_TAC 60;

    (*** Otherwise the fourth polynomial too ***)

    RULE_ASSUM_TAC(fun th ->
      if concl th = `~(r3:int64 = word 0)` then th
      else REWRITE_RULE[ASSUME `~(r3:int64 = word 0)`] th) THEN
    ASM_REWRITE_TAC[] THEN GETNOISE4_START_TAC THEN
    GETNOISE4_BRANCH_TAC `~(r3:int64 = word 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
     (60--62) THEN
    LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; GETNOISE4_N `nonce3:int64`;
                    `pc:num`; `read X30 s`] 63 THEN
    GETNOISE4_END_TAC 64]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events do not depend on the seed or  *)
(* the nonces, but on whether the fourth pointer is null.                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE4_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let GETNOISE4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GETNOISE4_ALLOWED); LABEL_TAC name safety_th]);;

(*** Up to the test of the fourth pointer ***)

let GETNOISE4_SAFE_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (1--4) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (5--19) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (20--44) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (45--45) THEN
  GETNOISE4_GOT_TAC THEN
  GETNOISE4_SAFE_CALL_TAC "H_SHAKE256X4"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `192`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1888 else 1904) + 960))`;
    `33`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
     ((k-3)--(k-1)) THEN
    GETNOISE4_SAFE_CALL_TAC "H_CBD3"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
      `read X30 s`] k)
   [50; 54; 58] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (59--59);;

(*** From step k ***)

let GETNOISE4_SAFE_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   (k--(k+3)) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC (k+3) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET"
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref GETNOISE4_ALLOWED) (k+8) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   ((k+9)--(k+18)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
   ((k+19)--(k+31)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2944),2944] /\
           ALLPAIRS nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2944),2944]
            [seed,32; stackpointer,1; word pc,0x6480; word(pc + 0x1fff8),8;
             guard,8; word(pc + 0x1ffe8),8; word(pc + 0x1ffd0),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O2_mc /\
                     read PC s = word (pc + 0x4730) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [r0; r1; r2; r3; seed] s /\
                     read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                     read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                     read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events r0 r1 r2 r3 seed guard mf mc pc
                               (word_sub stackpointer (word 2944))
                               returnaddress /\
                        memaccess_inbounds e2
                         [seed,32; stackpointer,1; r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2944),2944;
                          word(pc + 0x1fff8),8; guard,8;
                          word(pc + 0x62b0),192; word(pc + 0x6290),32;
                          word(pc + 0x1ffe8),8; word(pc + 0x1ffd0),8; ea,el]
                         [r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2944),2944]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(r0,512); memory :> bytes(r1,512);
                   memory :> bytes(r2,512);
                   memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                   memory :> bytes(word_sub stackpointer (word 2944),2944)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE th)
     "H_SHAKE256X4") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] (CONJUNCT1 th)) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_CBD3" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(r0:int64) (r1:int64) (r2:int64) (r3:int64) (seed:int64) (guard:int64)
     (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if r3 = word 0
     then f_ev_null r0 r1 r2 r3 seed guard mf mc pc stackpointer
                    returnaddress
     else f_ev_full r0 r1 r2 r3 seed guard mf mc pc stackpointer
                    returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GETNOISE4_SETUP_TAC THEN
  ASM_CASES_TAC `r3:int64 = word 0` THEN
  FIRST_ASSUM(fun th ->
    let th' = if is_neg(concl th) then EQF_INTRO th else EQT_INTRO th in
    REWRITE_TAC[th'] THEN
    RULE_ASSUM_TAC(fun th'' ->
      if concl th'' = concl th then th'' else REWRITE_RULE[th'] th'')) THEN
  GETNOISE4_SAFE_START_TAC THENL
   [GETNOISE4_BRANCH_TAC `r3:int64 = word 0` THEN GETNOISE4_SAFE_END_TAC 60;
    GETNOISE4_BRANCH_TAC `~(r3:int64 = word 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_EXEC
     (60--62) THEN
    GETNOISE4_SAFE_CALL_TAC "H_CBD3"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
      `read X30 s`] 63 THEN
    GETNOISE4_SAFE_END_TAC 64]);;
