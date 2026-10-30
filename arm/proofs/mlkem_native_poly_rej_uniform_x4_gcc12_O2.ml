(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials from four seeds by rejection. This   *)
(* is the code for mlkem_poly_rej_uniform_x4 from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which absorbs the four seeds of 34 bytes, 64 bytes apart, into a fourfold *)
(* SHAKE128 state, squeezes three blocks of 168 bytes of each and samples    *)
(* the coefficients below 3329 from them with mlk_rej_uniform_c, and then    *)
(* squeezes one more block of each and samples from all four until each      *)
(* polynomial has 256 coefficients, before zeroing the state and the         *)
(* buffers. It is verified in the whole image (see                           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x4b30, using  *)
(* the theorems for mlkem_shake128x4_init at 0x2a00,                         *)
(* mlkem_shake128x4_absorb_once at 0x2910, mlkem_shake128x4_squeezeblocks at *)
(* 0x2974, mlkem_shake128x4_release at 0x2a04 and mlk_rej_uniform_c at       *)
(* 0x4a90 in the image, assuming the contract for memset in                  *)
(* utils/mlkem_native_libc.ml, and the lemmas about the samples for          *)
(* mlkem_poly_rej_uniform. There is no constant-time and memory safety proof *)
(* yet (see mlkem_native/README.md).                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_rej_uniform_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128x4_init_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128x4_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128x4_squeezeblocks_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_shake128x4_release_gcc12_O2.ml";;

(*** The code in the image, and the PLT stub for memset:

    4b30: sub     sp, sp, #0xbc0
    4b34: adrp    x5, 1f000 <mlk_zetas+0x18c80>
    4b38: ldr     x5, [x5, #4088]
    4b3c: stp     x19, x20, [sp]
    4b40: mov     x20, x1
    4b44: mov     x19, x4
    4b48: stp     x21, x22, [sp, #16]
    4b4c: add     x22, sp, #0x9f
    4b50: and     x22, x22, #0xffffffffffffffe0
    4b54: stp     x23, x24, [sp, #32]
    4b58: mov     x21, x2
    4b5c: add     x23, x22, #0x600
    4b60: stp     x25, x26, [sp, #48]
    4b64: add     x26, x22, #0x800
    4b68: add     x24, x22, #0x400
    4b6c: stp     x27, x28, [sp, #64]
    4b70: mov     x27, x3
    4b74: mov     x28, x0
    4b78: str     x30, [sp, #80]
    4b7c: add     x25, x22, #0x200
    4b80: stp     x0, x1, [sp, #96]
    4b84: mov     x0, x26
    4b88: stp     x2, x3, [sp, #112]
    4b8c: ldr     x1, [x5]
    4b90: str     x1, [sp, #3000]
    4b94: mov     x1, #0x0
    4b98: bl      2a00 <mlkem_shake128x4_init>
    4b9c: add     x4, x19, #0xc0
    4ba0: add     x3, x19, #0x80
    4ba4: add     x2, x19, #0x40
    4ba8: mov     x1, x19
    4bac: mov     x0, x26
    4bb0: mov     x5, #0x22
    4bb4: bl      2910 <mlkem_shake128x4_absorb_once>
    4bb8: mov     x5, x26
    4bbc: mov     x4, #0x3
    4bc0: mov     x3, x23
    4bc4: mov     x2, x24
    4bc8: mov     x1, x25
    4bcc: mov     x0, x22
    4bd0: bl      2974 <mlkem_shake128x4_squeezeblocks>
    4bd4: mov     w3, #0x1f8
    4bd8: mov     x2, x22
    4bdc: mov     x0, x28
    4be0: mov     w1, #0x0
    4be4: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4be8: mov     w19, w0
    4bec: mov     x2, x25
    4bf0: mov     x0, x20
    4bf4: mov     w1, #0x0
    4bf8: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4bfc: mov     x2, x24
    4c00: mov     w20, w0
    4c04: mov     w1, #0x0
    4c08: mov     x0, x21
    4c0c: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4c10: mov     w21, w0
    4c14: mov     w1, #0x0
    4c18: mov     x0, x27
    4c1c: mov     x2, x23
    4c20: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4c24: cmp     w21, #0xff
    4c28: mov     w27, #0xff
    4c2c: ccmp    w0, w27, #0x0, hi
    4c30: mov     w28, w0
    4c34: cset    w0, ls
    4c38: cmp     w20, w27
    4c3c: ccmp    w19, w27, #0x0, hi
    4c40: cset    w1, ls
    4c44: orr     w0, w0, w1
    4c48: cbz     w0, 4ce0 <mlkem_poly_rej_uniform_x4+0x1b0>
    4c4c: nop
    4c50: mov     x5, x26
    4c54: mov     x4, #0x1
    4c58: mov     x3, x23
    4c5c: mov     x2, x24
    4c60: mov     x1, x25
    4c64: mov     x0, x22
    4c68: bl      2974 <mlkem_shake128x4_squeezeblocks>
    4c6c: ldr     x0, [sp, #96]
    4c70: mov     w3, #0xa8
    4c74: mov     w1, w19
    4c78: mov     x2, x22
    4c7c: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4c80: mov     w19, w0
    4c84: ldr     x0, [sp, #104]
    4c88: mov     w1, w20
    4c8c: mov     x2, x25
    4c90: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4c94: mov     w20, w0
    4c98: ldr     x0, [sp, #112]
    4c9c: mov     w1, w21
    4ca0: mov     x2, x24
    4ca4: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4ca8: mov     w21, w0
    4cac: ldr     x0, [sp, #120]
    4cb0: mov     w1, w28
    4cb4: mov     x2, x23
    4cb8: bl      4a90 <mlk_rej_uniform_c.constprop.0>
    4cbc: cmp     w0, #0xff
    4cc0: ccmp    w21, w27, #0x0, hi
    4cc4: mov     w28, w0
    4cc8: cset    w0, ls
    4ccc: cmp     w19, #0xff
    4cd0: ccmp    w20, w27, #0x0, hi
    4cd4: cset    w1, ls
    4cd8: orr     w0, w0, w1
    4cdc: cbnz    w0, 4c50 <mlkem_poly_rej_uniform_x4+0x120>
    4ce0: mov     x0, x26
    4ce4: bl      2a04 <mlkem_shake128x4_release>
    4ce8: mov     x0, x22
    4cec: mov     x2, #0x800
    4cf0: mov     w1, #0x0
    4cf4: bl      840 <memset@plt>
    4cf8: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    4cfc: ldr     x0, [x0, #4088]
    4d00: ldr     x2, [sp, #3000]
    4d04: ldr     x1, [x0]
    4d08: subs    x2, x2, x1
    4d0c: mov     x1, #0x0
    4d10: b.ne    4d34 <mlkem_poly_rej_uniform_x4+0x204>
    4d14: ldp     x19, x20, [sp]
    4d18: ldp     x21, x22, [sp, #16]
    4d1c: ldp     x23, x24, [sp, #32]
    4d20: ldp     x25, x26, [sp, #48]
    4d24: ldp     x27, x28, [sp, #64]
    4d28: ldr     x30, [sp, #80]
    4d2c: add     sp, sp, #0xbc0
    4d30: ret
    4d34: bl      830 <__stack_chk_fail@plt>

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x4b30,0x4d38; 0x840,0x850];;

(* ------------------------------------------------------------------------- *)
(* The samples from one more block, whatever the number of samples so far:   *)
(* if there are already 256, mlk_rej_uniform_c adds none, as there is no     *)
(* room for more. The loop test compares the numbers of samples with 255 as  *)
(* 32-bit words, using conditional comparisons (ccmp) to combine the four    *)
(* tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

let REJX4_SAMPLE_SUC = prove
 (`!(f:num->byte) j.
        SUB_LIST(0,256)
         (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
            (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
        APPEND
         (SUB_LIST(0,256)
           (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
              (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
         (SUB_LIST(0,256 -
                   MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j)))))))
           (REJ_SAMPLE(wordlist_of_num 112
              (num_of_bytelist
                (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v))
   [`REJ_SAMPLE(wordlist_of_num 112 (num_of_bytelist
      (list_of_seq (\i. (f:num->byte)((504 + 168 * j) + i)) 168)))`,
    `l2:int16 list`;
    `REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
      (num_of_bytelist(list_of_seq (f:num->byte) (504 + 168 * j))))`,
    `l1:int16 list`] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LENGTH(l1:int16 list) <= 256` THENL
   [ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL;
                 ARITH_RULE `x <= 256 ==> MIN 256 x = x`];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LT_IMP_LE; SUB_REFL;
                 ARITH_RULE `256 < x ==> MIN 256 x = 256`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; APPEND_NIL]]);;

let REJX4_CMP = prove
 (`!c. c < 2 EXP 32
       ==> val(word_zx(word c:int64):int32) = c /\
           (&c - &255:int =
            &(val(word_sub (word_zx (word c:int64):int32) (word 255))) <=>
            255 <= c) /\
           (val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0 <=>
            c = 255)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      MATCH_MP_TAC(INT_ARITH
       `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
      REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

(*** The loop test, as a condition on four numbers of samples at most 256 ***)

let REJX4_TEST_PROVE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `n0 < 2 EXP 32 /\ n1 < 2 EXP 32 /\ n2 < 2 EXP 32 /\ n3 < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REJX4_CMP] THEN
  REWRITE_TAC[TAUT `(if a then b else F) <=> a /\ b`;
              ARITH_RULE `255 <= n /\ ~(n = 255) <=> 255 < n`] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_ARITH_TAC;;

let REJX4_TEST_TAC cs =
  let vs = map (fun i -> mk_var("n"^string_of_int i,`:num`)) (0--3) in
  let ant = list_mk_conj
             (map (fun v -> mk_binop `(<=):num->num->bool` v `256`) vs)
  and res = list_mk_conj
             (map (fun v -> mk_binop `(<):num->num->bool` `255` v) vs) in
  let bth = end_itlist CONJ
             (map (fun c -> SPECL [`256`; rand c]
                    (ARITH_RULE `!a b. MIN a b <= a`)) cs) in
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),
           Comb(Comb(Comb(Const("COND",_),c),_),_)) when free_in (hd cs) c ->
        let res' = if is_neg c then mk_neg res else res in
        let lth = prove(list_mk_forall(vs,mk_imp(ant,mk_eq(subst(zip vs cs) c,
                                                          res'))),
                        REJX4_TEST_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[MP (SPECL cs lth) bth;
                                ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] th)
    | _ -> NO_TAC);;

let REJX4_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if (is_binary "<" (concl th) || is_binary "<=" (concl th)) &&
         lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

(* ------------------------------------------------------------------------- *)
(* The four buffers of 512 bytes for three blocks each, followed by the four *)
(* states, are aligned to 32 bytes within the stack frame, so their          *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. They are in the form given by NORMALIZE_RELATIVE_ADDRESS_CONV, as  *)
(* in the preconditions of the calls.                                        *)
(* ------------------------------------------------------------------------- *)

let REJX4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 463)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 448 else 432))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let REJX4_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 463))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REJX4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let REJX4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let REJX4_SP n =
  let b = `if aligned 32 (stackpointer:int64) then 448 else 432` in
  let off = if n = 0 then b
            else mk_binop `(+):num->num->num` b (mk_small_numeral n) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,off));;

let REJX4_BUF m = REJX4_SP(512 * m);;

let REJX4_ST m =
  let st = REJX4_SP 2048 in
  if m = 0 then st
  else rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV
    (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),
             mk_comb(`word:num->int64`,mk_small_numeral(200 * m))))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_poly_rej_uniform. The seeds are 34 bytes at seed, seed + 64, seed + *)
(* 128 and seed + 192, given as lists of bytes inp0, ..., inp3. As for       *)
(* mlkem_poly_rej_uniform, the theorem has the hypothesis that for some k    *)
(* there are at least 256 samples among the 12-bit fields of the first 504 + *)
(* 168 * k bytes of shake128 of each seed, and the results are the first 256 *)
(* samples for each. The loop sampling from one more block of each at a time *)
(* stops when there are 256 samples for all four, so the proof uses the      *)
(* minimal such k, k0, as the number of iterations, and the numbers of       *)
(* samples in the invariant are at most 256. The stack is the 3008 bytes of  *)
(* the function and the 304 used by mlkem_shake128x4_absorb_once below them. *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_RELEASE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with bounds on the offset of the buffers ***)

let REJX4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3312):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `432 <= (if aligned 32 (stackpointer:int64) then 448 else 432) /\
    (if aligned 32 (stackpointer:int64) then 448 else 432) <= 448`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

(*** The GOT entries in the form in the preconditions of the callees ***)

let REJX4_GOT_TAC =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [mk_small_numeral n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [131064; 131048];;

(*** The fields, samples and blocks for each seed ***)

let REJX4_INPS =
  [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`]
and REJX4_VECS = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`]
and REJX4_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let rejx4_fields inp j =
  vsubst [inp,`inp:byte list`; j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rejx4_fields0 inp =
  vsubst [inp,`inp:byte list`]
   `wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;;

let rejx4_count inp j =
  mk_comb(`LENGTH:(16 word)list->num`,
          mk_comb(`REJ_SAMPLE`,rejx4_fields inp j));;

let rejx4_block inp i =
  vsubst [inp,`inp:byte list`; i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rejx4_cs0 =
  map (fun inp -> mk_comb(`MIN 256`,
                   rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                         (rejx4_count inp `0`)))))
      REJX4_INPS
and rejx4_cs1 =
  map (fun inp -> mk_comb(`MIN 256`,rejx4_count inp `i + 1`)) REJX4_INPS;;

(*** The absorbed states as S0, ..., S3, and the minimal number of blocks ***)

let REJX4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = vsubst [inp,`inp:byte list`] REJ_ABSORBED in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),`34`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SPONGE)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SHAKE128_BLOCKS)))
   (zip REJX4_INPS REJX4_SVS);;

let REJX4_DONE n =
  list_mk_conj
   (map (fun inp -> mk_binop `(<=):num->num->bool` `256` (rejx4_count inp n))
        REJX4_INPS);;

let REJX4_MINIMAL_TAC =
  let p = mk_abs(`n:num`,REJX4_DONE `n:num`) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The minimality of k0, at j, without rewriting with it, which turns ***)
(*** its own instances into T                                           ***)

let REJX4_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(*** The facts at the intermediate points, with the saved registers ***)

let REJX4_FRAME =
 `read SP s = word_add stackpointer (word 304) /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 320))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 400))) s = vec0 /\
  read (memory :> bytes64 (word_add stackpointer (word 408))) s = vec1 /\
  read (memory :> bytes64 (word_add stackpointer (word 416))) s = vec2 /\
  read (memory :> bytes64 (word_add stackpointer (word 424))) s = vec3 /\
  read (memory :> bytes64 (word_add stackpointer (word 3304))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X22 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432)) /\
  read X25 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 512)) /\
  read X24 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 1024)) /\
  read X23 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 1536)) /\
  read X26 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 2048))`;;

let REJX4_POLY =
 `read (R:(armstate,int64)component) s =
  word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
  read (memory :> bytes(vec,2 * MIN 256 (LENGTH(REJ_SAMPLE
    (wordlist_of_num (336 + 112 * i)
      (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))))) s =
  num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
    (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (3 + i) (S:1600 word))`;;

let REJX4_POLYS regs =
  flat
   (map (fun (r,(vec,(inp,(st,sv)))) ->
          conjuncts
           (vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
                    inp,`inp:byte list`; st,`st:int64`; sv,`S:1600 word`]
                   REJX4_POLY))
        (zip regs (zip REJX4_VECS (zip REJX4_INPS
           (zip (map REJX4_ST (0--3)) REJX4_SVS)))));;

let REJX4_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(REJX4_POLYS [`X19`; `X20`; `X21`; `X0`])) in
  let t' = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] t)) in
  mk_abs(`s:armstate`,list_mk_conj(conjuncts t' @ conjuncts REJX4_FRAME));;

let REJX4_INV =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(REJX4_POLYS [`X19`; `X20`; `X21`; `X28`] @
                 [`read X27 s = word 255`] @ conjuncts REJX4_FRAME));;

let REJX4_A2 =
  let res inp vec =
    vsubst [inp,`inp:byte list`; vec,`vec:int64`]
     `read (memory :> bytes(vec,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))` in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res REJX4_INPS REJX4_VECS @ conjuncts REJX4_FRAME));;

(*** Calls of mlk_rej_uniform_c on the first three blocks ***)

let REJX4_INPUT0_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`336`); s]),
          rejx4_fields0 inp))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`336`; rand(rejx4_fields0 inp)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_CALL0_TAC m n =
  let inp = el m REJX4_INPS in
  REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(n-1),`:armstate`)) THEN
  LOCAL_REJ_X4_TAC [`read X0 s`; `0`; `read X2 s`; `504`; rejx4_fields0 inp;
                    `pc:num`; `read X30 s`] n THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl));;

(*** The numbers of samples so far in the loop body as ci0, ..., ci3, and ***)
(*** their definitions packed into a conjunction, which keeps them from   ***)
(*** the arithmetic of NONOVERLAPPING_TAC, much slower with them          ***)

let REJX4_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 3 && String.sub n 0 2 = "ci"
  | _ -> false;;

let REJX4_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`) in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("ci"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> REJX4_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let REJX4_ABBREV m =
  let eq = mk_eq(mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`),
                 mk_var("ci"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

(*** Calls of mlk_rej_uniform_c on one more block, and their results ***)

let REJX4_BLOCK_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`112`); s]),
          rejx4_block inp `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) &&
         free_in inp (concl th)
      then MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rejx4_block inp `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_COMBINE_TAC m n =
  let inp = el m REJX4_INPS and vec = el m REJX4_VECS in
  let c = mk_var("ci"^string_of_int m,`:num`)
  and s = mk_var("s"^string_of_int n,`:armstate`) in
  let l1 = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                   mk_comb(`REJ_SAMPLE`,rejx4_fields inp `i:num`))
  and l2 = mk_comb(mk_comb(`SUB_LIST:num#num->(16 word)list->(16 word)list`,
                           mk_pair(`0`,mk_binop `(-):num->num->num` `256` c)),
                   mk_comb(`REJ_SAMPLE`,rejx4_block inp `i:num`)) in
  let lenl1 = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l1),c) in
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN lenl1 ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [vec; c; l1; l2; s] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(fun gl ->
    let th = REWRITE_RULE [REJX4_ABBREV m gl]
             (ISPECL [mk_comb(`shake128`,inp); `i:num`] REJX4_SAMPLE_SUC) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
    MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND; ASSUME lenl1] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

let REJX4_CALL_TAC m n =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  REJX4_ARGS_32_TAC c THEN
  REJX4_BLOCK_TAC m (mk_var("s"^string_of_int(n-1),`:armstate`)) THEN
  LOCAL_REJ_X4_TAC [`read X0 s`; c; `read X2 s`; `168`;
                    rejx4_block inp `i:num`; `pc:num`; `read X30 s`] n THEN
  REJX4_COMBINE_TAC m n;;

(*** Whether there are 256 samples for all four after one more block ***)

let REJX4_LS_TAC =
  SUBGOAL_THEN (mk_eq(REJX4_DONE `i + 1`,`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        REJX4_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(*** The parts of the proof ***)

let REJX4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`; `seed:int64`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3312 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

let REJX4_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (3--9) THEN
  REJX4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (10--27) THEN
  REJX4_NORMALIZE_TAC THEN
  LOCAL_INIT_X4_TAC [`read X0 s`; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (29--35) THEN
  REJX4_GOT_TAC THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 36 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (37--43) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `3`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC
     ((45 + 6 * m)--(49 + 6 * m)) THEN
    REJX4_CALL0_TAC m (50 + 6 * m)) (0--3) THEN
  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** Branching round the loop when no more blocks are needed ***)

let REJX4_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) rejx4_cs0 THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

(*** The loop, if more blocks are needed, from the first samplings ***)

let REJX4_LOOP_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--10) THEN
  REJX4_TEST_TAC rejx4_cs0 THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (11--11) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

let REJX4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REJX4_ABBREV_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Squeezing one more block from each state ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--7) THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  REJX4_NORMALIZE_TAC THEN

  (*** Sampling from each block after the samples so far ***)

  MAP_EVERY (fun m ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC
     ((9 + 6 * m)--(13 + 6 * m)) THEN
    REJX4_CALL_TAC m (14 + 6 * m)) (0--3) THEN

  (*** The test of whether there are 256 samples for all four now ***)

  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs1) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (33--41) THEN
  REJX4_TEST_TAC rejx4_cs1 THEN REJX4_LS_TAC THEN
  REJX4_ARGS_32_TAC (last rejx4_cs1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[];;

let REJX4_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJX4_LOOP_TAC =
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + 0x4c50` `pc + 0x4ce0` REJX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REJX4_LOOP_INIT_TAC; REJX4_BODY_TAC; REJX4_EXIT_TAC];;

(*** Releasing the state, zeroing the buffers, the stack guard, return ***)

let REJX4_FINAL_TAC =
  let tac inp =
    let l = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                    mk_comb(`REJ_SAMPLE`,rejx4_fields inp `k:num`)) in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] in
  REPEAT CONJ_TAC THENL map tac REJX4_INPS;;

let REJX4_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN REJX4_GOT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--2) THEN
  LOCAL_RELEASE_X4_TAC
   [`read X0 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (4--7) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC 7 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (13--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (14--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJX4_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!vec0 vec1 vec2 vec3 seed (inp0:byte list) (inp1:byte list)
   (inp2:byte list) (inp3:byte list) k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = 34 /\ LENGTH inp1 = 34 /\
        LENGTH inp2 = 34 /\ LENGTH inp3 = 34 /\
        ALL (\inp. 256 <= LENGTH(FILTER (\x. val x < 3329)
                            (MAP (word_zx:12 word->16 word)
                              (wordlist_of_num (336 + 112 * k)
                                (num_of_bytelist
                                  (list_of_seq (shake128 inp)
                                               (504 + 168 * k)))))))
            [inp0; inp1; inp2; inp3] /\
        PAIRWISE nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3312),3312)] /\
        ALLPAIRS nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3312),3312)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x4b30) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s =
                  num_of_bytelist inp1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s =
                  num_of_bytelist inp2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s =
                  num_of_bytelist inp3)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(vec0,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp0) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec1,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp1) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec2,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp2) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec3,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp3) (504 + 168 * k)))))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(vec0,512); memory :> bytes(vec1,512);
                memory :> bytes(vec2,512); memory :> bytes(vec3,512);
                memory :> bytes(word_sub stackpointer (word 3312),3312)])`,
  REJX4_INTRO_TAC THEN REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN
  REJX4_MINIMAL_TAC THEN

  (*** The first three blocks of each and the samples from them ***)

  ENSURES_SEQUENCE_TAC `pc + 0x4ce0` REJX4_A2 THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x4c24` REJX4_A1 THEN CONJ_TAC THENL
     [REJX4_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL [REJX4_NOLOOP_TAC; REJX4_LOOP_TAC]];
    REJX4_PART3_TAC]);;
