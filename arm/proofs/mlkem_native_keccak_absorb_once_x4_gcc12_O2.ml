(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding. This is the code for the static function                     *)
(* mlk_keccak_absorb_once_x4 from mlkem-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), specialized by  *)
(* the compiler to the first byte 0x1F of the padding as                     *)
(* mlk_keccak_absorb_once_x4.constprop.0. It works as                        *)
(* mlk_keccak_absorb_once does on one state, using                           *)
(* mlkem_keccakf1600x4_xor_bytes and mlkem_keccakf1600x4_permute, except     *)
(* that the states are not zeroed first: that is done by its callers. It is  *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x27a0, using the theorems for those functions at  *)
(* 0x2d50 and 0x33a0 in the image.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600x4_permute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600x4_xor_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    27a0: stp     x19, x20, [sp, #-96]!
    27a4: mov     w19, w1
    27a8: mov     x20, x6
    27ac: adrp    x7, 1f000 <mlk_zetas+0x18c80>
    27b0: ldr     x7, [x7, #4088]
    27b4: stp     x21, x22, [sp, #16]
    27b8: mov     x21, x2
    27bc: stp     x23, x24, [sp, #32]
    27c0: mov     x22, x3
    27c4: mov     x24, x0
    27c8: stp     x25, x26, [sp, #48]
    27cc: mov     x23, x4
    27d0: mov     x25, x19
    27d4: stp     x27, x30, [sp, #64]
    27d8: mov     x26, x5
    27dc: ldr     x1, [x7]
    27e0: str     x1, [sp, #88]
    27e4: mov     x1, #0x0
    27e8: mov     w1, #0x1f
    27ec: strb    w1, [sp, #87]
    27f0: cmp     x19, x6
    27f4: b.hi    283c <mlk_keccak_absorb_once_x4.constprop.0+0x9c>
    27f8: mov     x4, x26
    27fc: mov     x3, x23
    2800: mov     x2, x22
    2804: mov     x1, x21
    2808: mov     w6, w25
    280c: mov     w5, #0x0
    2810: mov     x0, x24
    2814: bl      2d50 <mlkem_keccakf1600x4_xor_bytes>
    2818: mov     x0, x24
    281c: sub     x20, x20, x19
    2820: bl      33a0 <mlkem_keccakf1600x4_permute>
    2824: add     x26, x26, x19
    2828: add     x23, x23, x19
    282c: add     x22, x22, x19
    2830: add     x21, x21, x19
    2834: cmp     x20, x19
    2838: b.cs    27f8 <mlk_keccak_absorb_once_x4.constprop.0+0x58>
    283c: sub     w25, w25, #0x1
    2840: mov     w27, w20
    2844: cbnz    x20, 28c8 <mlk_keccak_absorb_once_x4.constprop.0+0x128>
    2848: add     x19, sp, #0x57
    284c: mov     w5, w27
    2850: mov     x4, x19
    2854: mov     x0, x24
    2858: mov     x3, x19
    285c: mov     x2, x19
    2860: mov     x1, x19
    2864: mov     w6, #0x1
    2868: bl      2d50 <mlkem_keccakf1600x4_xor_bytes>
    286c: mov     w5, w25
    2870: mov     x0, x24
    2874: mov     x4, x19
    2878: mov     w7, #0xffffff80
    287c: mov     x2, x4
    2880: mov     x1, x4
    2884: mov     x3, x4
    2888: mov     w6, #0x1
    288c: strb    w7, [sp, #87]
    2890: bl      2d50 <mlkem_keccakf1600x4_xor_bytes>
    2894: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    2898: ldr     x0, [x0, #4088]
    289c: ldr     x2, [sp, #88]
    28a0: ldr     x1, [x0]
    28a4: subs    x2, x2, x1
    28a8: mov     x1, #0x0
    28ac: b.ne    2908 <mlk_keccak_absorb_once_x4.constprop.0+0x168>
    28b0: ldp     x21, x22, [sp, #16]
    28b4: ldp     x23, x24, [sp, #32]
    28b8: ldp     x25, x26, [sp, #48]
    28bc: ldp     x27, x30, [sp, #64]
    28c0: ldp     x19, x20, [sp], #96
    28c4: ret
    28c8: mov     x4, x26
    28cc: mov     x3, x23
    28d0: mov     x2, x22
    28d4: mov     x1, x21
    28d8: mov     w6, w20
    28dc: mov     x0, x24
    28e0: mov     w5, #0x0
    28e4: bl      2d50 <mlkem_keccakf1600x4_xor_bytes>
    28e8: cmp     x20, w25, uxtw
    28ec: b.ne    2848 <mlk_keccak_absorb_once_x4.constprop.0+0xa8>
    28f0: ldrb    w7, [sp, #87]
    28f4: add     x4, sp, #0x57
    28f8: mov     w5, w20
    28fc: mov     x0, x24
    2900: orr     w7, w7, #0xffffff80
    2904: b       287c <mlk_keccak_absorb_once_x4.constprop.0+0xdc>
    2908: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x27a0,0x290c];;

(* ------------------------------------------------------------------------- *)
(* The four states zero at the start, as 200 bytes each.                     *)
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
(* Tactics for the calls, which act on all four states, and for the padding  *)
(* byte on the stack, which is used for all four.                            *)
(* ------------------------------------------------------------------------- *)

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

let LOCAL_XOR_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_X4_TAC ilist n =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
   ilist n;;

let ABSX4_MBOUND_TAC =
  MAP_EVERY (fun mm ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC])
   [`M0:num`; `M1:num`; `M2:num`; `M3:num`];;

let ABSX4_LASTBLOCK_TAC =
  MAP_EVERY (fun (pp,mm,pn) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
        M DIV 2 EXP (8 * r * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad r 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [pn; "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      ASM_SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `31 < 128`];
      ALL_TAC])
   [`P0:num`,`M0:num`,"P0"; `P1:num`,`M1:num`,"P1";
    `P2:num`,`M2:num`,"P2"; `P3:num`,`M3:num`,"P3"];;

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 295),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let ABSX4_XOR_CALL_TAC off len ms n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    LOCAL_XOR_X4_TAC
     ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
       off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read SP s`; `read X30 s`]) n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSX4_T0_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]];;

let ABSX4_B_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

let ABSX4_C_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (r - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states must be zero at the start, and each    *)
(* is then as for mlk_keccak_absorb_once on the corresponding message, with  *)
(* the first byte 0x1F of the padding, as for SHAKE. As for                  *)
(* mlkem_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 96 bytes of the function and the 208 used by    *)
(* mlkem_keccakf1600x4_permute below them.                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
    returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 304),304)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x27a0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 304),304)])`,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  MAP_EVERY (fun (p,m) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r 0x1F mlen)`))
   [`P0:num`,`M0:num`; `P1:num`,`M1:num`; `P2:num`,`M2:num`;
    `P3:num`,`M3:num`] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN

  (*** The states after the whole blocks, before the last block ***)

  ENSURES_SEQUENCE_TAC `pc + 0x283c`
   `\s. read X19 s = word r /\ read X20 s = word(mlen MOD r) /\
        read X21 s = word_add m0 (word(r * mlen DIV r)) /\
        read X22 s = word_add m1 (word(r * mlen DIV r)) /\
        read X23 s = word_add m2 (word(r * mlen DIV r)) /\
        read X26 s = word_add m3 (word(r * mlen DIV r)) /\
        read X24 s = st /\ read X25 s = word r /\
        read SP s = word_add stackpointer (word 208) /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s =
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s =
        x24_init /\
        read (memory :> bytes64 (word_add stackpointer (word 256))) s =
        x25_init /\
        read (memory :> bytes64 (word_add stackpointer (word 264))) s =
        x26_init /\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        x27_init /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        returnaddress /\
        read (memory :> bytes8 (word_add stackpointer (word 295))) s =
        word 31 /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        canary /\
        read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
        guard /\
        read (memory :> bytes64 guard) s = canary /\
        read (memory :> bytes(m0,mlen)) s = M0 /\
        read (memory :> bytes(m1,mlen)) s = M1 /\
        read (memory :> bytes(m2,mlen)) s = M2 /\
        read (memory :> bytes(m3,mlen)) s = M3 /\
        read (memory :> bytes(st,200)) s =
        val(keccak_absorb r P0 (mlen DIV r)) /\
        read (memory :> bytes(word_add st (word 200),200)) s =
        val(keccak_absorb r P1 (mlen DIV r)) /\
        read (memory :> bytes(word_add st (word 400),200)) s =
        val(keccak_absorb r P2 (mlen DIV r)) /\
        read (memory :> bytes(word_add st (word 600),200)) s =
        val(keccak_absorb r P3 (mlen DIV r))` THEN
  CONJ_TAC THENL
   [(*** A message shorter than a block, with no loop ***)

    ASM_CASES_TAC `mlen < r` THENL
       [ENSURES_INIT_TAC "s0" THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
         (can (term_match []
           `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (1--4) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (5--21) THEN
        ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (22--22) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
        REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
        REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[ARITH_RULE `mlen < r ==> mlen <= r /\ ~(r = mlen)`];
        ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_WHILE_UP_TAC `mlen DIV r` `pc + 0x27f8` `pc + 0x2834`
       `\k s. read X19 s = word r /\ read X20 s = word(mlen - r * k) /\
              read X21 s = word_add m0 (word(r * k)) /\
              read X22 s = word_add m1 (word(r * k)) /\
              read X23 s = word_add m2 (word(r * k)) /\
              read X26 s = word_add m3 (word(r * k)) /\
              read X24 s = st /\ read X25 s = word r /\
              read SP s = word_add stackpointer (word 208) /\
              read (memory :> bytes64 (word_add stackpointer (word 208))) s =
              x19_init /\
              read (memory :> bytes64 (word_add stackpointer (word 216))) s =
              x20_init /\
              read (memory :> bytes64 (word_add stackpointer (word 224))) s =
              x21_init /\
              read (memory :> bytes64 (word_add stackpointer (word 232))) s =
              x22_init /\
              read (memory :> bytes64 (word_add stackpointer (word 240))) s =
              x23_init /\
              read (memory :> bytes64 (word_add stackpointer (word 248))) s =
              x24_init /\
              read (memory :> bytes64 (word_add stackpointer (word 256))) s =
              x25_init /\
              read (memory :> bytes64 (word_add stackpointer (word 264))) s =
              x26_init /\
              read (memory :> bytes64 (word_add stackpointer (word 272))) s =
              x27_init /\
              read (memory :> bytes64 (word_add stackpointer (word 280))) s =
              returnaddress /\
              read (memory :> bytes8 (word_add stackpointer (word 295))) s =
              word 31 /\
              read (memory :> bytes64 (word_add stackpointer (word 296))) s =
              canary /\
              read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
              guard /\
              read (memory :> bytes64 guard) s = canary /\
              read (memory :> bytes(m0,mlen)) s = M0 /\
              read (memory :> bytes(m1,mlen)) s = M1 /\
              read (memory :> bytes(m2,mlen)) s = M2 /\
              read (memory :> bytes(m3,mlen)) s = M3 /\
              read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 k) /\
              read (memory :> bytes(word_add st (word 200),200)) s =
              val(keccak_absorb r P1 k) /\
              read (memory :> bytes(word_add st (word 400),200)) s =
              val(keccak_absorb r P2 k) /\
              read (memory :> bytes(word_add st (word 600),200)) s =
              val(keccak_absorb r P3 k)` THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];
        ENSURES_INIT_TAC "s0" THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
         (can (term_match []
           `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (1--4) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (5--21) THEN
        ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (22--22) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
        REWRITE_TAC[keccak_absorb; VAL_WORD_0; VAL_WORD_SUB_EQ_0] THEN
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(mlen < r) ==> ~(mlen <= r /\ ~(r = mlen))`];


        (*** The loop body: XOR in a block of each message and permute ***)

        (X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
          MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
           [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          MAP_EVERY (fun (m,mm) ->
            MP_TAC(SPECL [m; `mlen:num`; mm; `r * i`; `r:num`; `s0:armstate`]
                         READ_MEMORY_BYTES_SUB) THEN
            ASM_REWRITE_TAC[] THEN DISCH_TAC)
           [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
            `m3:int64`,`M3:num`] THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (1--8) THEN
          ARGS_32_TAC [`r:num`] THEN
          ABSX4_STATES_TAC THEN
          LOCAL_XOR_X4_TAC
           [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
            `0`; `r:num`; `keccak_absorb r P0 i`; `keccak_absorb r P1 i`;
            `keccak_absorb r P2 i`; `keccak_absorb r P3 i`;
            `(M0 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
            `(M1 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
            `(M2 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
            `(M3 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
            `pc:num`; `read SP s`; `read X30 s`] 9 THEN
          RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (10--12) THEN
          ABSX4_STATES_TAC THEN
          ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
            LOCAL_PERMUTE_X4_TAC
             [`read X0 s`; v0; v1; v2; v3; `pc:num`; `read SP s`;
              `read X30 s`] 13) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (14--17) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
           [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
            ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                            DISCH_THEN SUBST1_TAC] THEN
            AP_TERM_TAC THEN ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
            ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
          AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[MULT_CLAUSES; EXP] THEN
          MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
          CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
          MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
          UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC);

        (*** The loop-back branch ***)

        (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          ENSURES_INIT_TAC "s0" THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (1--1) THEN
          SUBGOAL_THEN `val(word(mlen - r * i):int64) = mlen - r * i /\
                        val(word r:int64) = r`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
            REWRITE_TAC[DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
            ALL_TAC] THEN
          DECIDE_FLAGS_TAC THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (2--2) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);

        (*** The loop exit ***)

        (ENSURES_INIT_TAC "s0" THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (1--1) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ABSORB_MOD_EQ]) THEN
          SUBGOAL_THEN `val(word(mlen MOD r):int64) = mlen MOD r /\
                        val(word r:int64) = r /\ mlen MOD r < r`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                      ASSUME_TAC th) THENL
           [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC VAL_WORD_EQ) THEN
            REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
            ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
            MP_TAC(SPECL [`mlen:num`; `r:num`] MOD_LT_EQ) THEN
            ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
            SIMPLE_ARITH_TAC;
            ALL_TAC] THEN
          DECIDE_FLAGS_TAC THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (2--2) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[])];

    (*** The last block: the rest of each message and the padding ***)

    ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
      SUBGOAL_THEN `mlen = r * q + t /\ t < r` STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
        MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN ABSX4_MBOUND_TAC THEN
    ABSX4_LASTBLOCK_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--2) THEN
      ARGS_32_TAC [`t:num`] THEN
      MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
      ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `t = 0` THENL
     [(*** A whole number of blocks: p at byte 0 and 128 at byte r - 1 ***)

      (ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
        (3--12) THEN
        ABSX4_BYTE_FACT_TAC "s12" `31` THEN
        ABSX4_XOR_CALL_TAC `t:num` `1` [`31`; `31`; `31`; `31`] 13 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (14--23) THEN
        ARGS_32_TAC [`r - 1`] THEN
        ABSX4_BYTE_FACT_TAC "s23" `128` THEN
        SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ABSX4_XOR_CALL_TAC `r - 1` `1` [`128`; `128`; `128`; `128`] 24 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (25--25) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (26--37) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `!M. M < 2 EXP (8 * mlen) ==> M DIV 2 EXP (8 * r * q) = 0`
         ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
          UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
          ALL_TAC] THEN
        REPEAT CONJ_TAC THEN ABSX4_T0_LANE_TAC);
      ALL_TAC] THEN

    (*** Otherwise, first the t bytes of each message after its blocks ***)

    SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY (fun (m,mm) ->
        SUBGOAL_THEN
         (subst [mm,`M:num`] `M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`)
        ASSUME_TAC THENL
         [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
          REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
          FIRST_X_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
            `M < 2 EXP (8 * mlen)` then MP_TAC th else NO_TAC) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(SPECL [m; `mlen:num`; mm; `r * q`; `t:num`; `s2:armstate`]
                     READ_MEMORY_BYTES_SUB) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC)
       [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
        `m3:int64`,`M3:num`] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (3--11) THEN
      ARGS_32_TAC [`t:num`] THEN
      ABSX4_XOR_CALL_TAC `0` `t:num`
       [`M0 DIV 2 EXP (8 * r * q)`; `M1 DIV 2 EXP (8 * r * q)`;
        `M2 DIV 2 EXP (8 * r * q)`; `M3 DIV 2 EXP (8 * r * q)`] 12 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (13--13) THEN
      ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
      ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
     [(*** The padding is just the single byte p + 128 at byte r - 1 ***)

      (FIRST_X_ASSUM(SUBST_ALL_TAC o
         check (fun th -> concl th = `t = r - 1`)) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (14--26) THEN
        ARGS_32_TAC [`r - 1`] THEN
      ABSX4_BYTE_FACT_TAC "s26" `159` THEN
        SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ABSX4_XOR_CALL_TAC `r - 1` `1` [`159`; `159`; `159`; `159`] 27 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (28--28) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (29--40) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
         [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
           [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
          ALL_TAC] THEN
        REPEAT CONJ_TAC THEN ABSX4_B_LANE_TAC);

      (*** Otherwise p at byte t and 128 at byte r - 1 ***)

      (ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
        (14--23) THEN
        ARGS_32_TAC [`t:num`] THEN
        ABSX4_BYTE_FACT_TAC "s23" `31` THEN
        SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ABSX4_XOR_CALL_TAC `t:num` `1` [`31`; `31`; `31`; `31`] 24 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (25--34) THEN
        ARGS_32_TAC [`r - 1`] THEN
        ABSX4_BYTE_FACT_TAC "s34" `128` THEN
        ABSX4_XOR_CALL_TAC `r - 1` `1` [`128`; `128`; `128`; `128`] 35 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (36--36) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (37--48) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
         [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
          ALL_TAC] THEN
        REPEAT CONJ_TAC THEN ABSX4_C_LANE_TAC)]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlk_keccak_absorb_once, the *)
(* events for the last block are given in three cases. The test of the       *)
(* message length against the rate at the start is normalized in the events  *)
(* before they are unified with the template.                                *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let ABSX4_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `r:num`; `mlen:num`; `guard:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ABSX4_SAFE_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSX4_SAFE_XOR_TAC off len vars n =
  ABSX4_SAFE_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
     `read X3 s`; `read X4 s`; off; len; `pc:num`; `read SP s`;
     `read X30 s`] vars n;;

let ABSX4_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [REWRITE_TAC[VAL_WORD_SUB_EQ_0; ASSUME `val(word r:int64) = r`;
                     ASSUME `val(word mlen:int64) = mlen`] THEN
         (FULL_UNIFY_F_EVENTS_TAC ORELSE
          (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC));
         ALL_TAC])
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABSX4_SAFE_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

let ABSX4_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (1--2) THEN
  ARGS_32_TAC [`t:num`] THEN ABSORB_VAL_TAC THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (3--12) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 13 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (14--23) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 24 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (25--25) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (26--37) THEN
    ABSX4_SAFE_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (3--11) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_SAFE_XOR_TAC `0` `t:num` ABSX4_SAFE_VARS 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (13--13) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (14--26) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 27 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (28--28) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (29--40) THEN
    ABSX4_SAFE_FINAL_TAC;
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (14--23) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 24 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (25--34) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 35 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (36--36) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (37--48) THEN
    ABSX4_SAFE_FINAL_TAC];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e st r m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 304),304]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
         word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x27a0) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st r mlen guard pc
                           (word_sub stackpointer (word 304)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 304),304;
                      word(pc + 0x1fff8),8; guard,8; word(pc + 0x62b0),192]
                     [st,800; word_sub stackpointer (word 304),304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 304),304)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress
        else f_ev_t2 m0 m1 m2 m3 st r mlen guard pc stackpointer
                     returnaddress)
       (if mlen < r
        then f_ev_short m0 m1 m2 m3 st r mlen guard pc stackpointer
                        returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st r mlen guard pc stackpointer
                         returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m0 m1 m2 m3 st r mlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st r mlen guard pc stackpointer
                           returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x283c`
   `\s. read X19 s = word r /\ read X20 s = word(mlen MOD r) /\
        read X21 s = word_add m0 (word(r * mlen DIV r)) /\
        read X22 s = word_add m1 (word(r * mlen DIV r)) /\
        read X23 s = word_add m2 (word(r * mlen DIV r)) /\
        read X26 s = word_add m3 (word(r * mlen DIV r)) /\
        read X24 s = st /\ read X25 s = word r /\
        read SP s = word_add stackpointer (word 208) /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s =
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s =
        x24_init /\
        read (memory :> bytes64 (word_add stackpointer (word 256))) s =
        x25_init /\
        read (memory :> bytes64 (word_add stackpointer (word 264))) s =
        x26_init /\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        x27_init /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        returnaddress /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        canary /\
        read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
        guard /\
        read (memory :> bytes64 guard) s = canary` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [(*** A message shorter than a block, with no loop ***)

      (REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (1--4) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (5--21) THEN
        ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
         (22--22) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      CONJ_TAC THENL
         [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
          ASM_SIMP_TAC[ARITH_RULE `mlen < r ==> mlen <= r /\ ~(r = mlen)`];
          DISCHARGE_SAFETY_PROPERTY_TAC]);

      (*** Otherwise the loop over the whole blocks ***)

      ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + 0x27f8` `pc + 0x283c`
         `\k s. read X19 s = word r /\ read X20 s = word(mlen - r * k) /\
                read X21 s = word_add m0 (word(r * k)) /\
                read X22 s = word_add m1 (word(r * k)) /\
                read X23 s = word_add m2 (word(r * k)) /\
                read X26 s = word_add m3 (word(r * k)) /\
                read X24 s = st /\ read X25 s = word r /\
                read SP s = word_add stackpointer (word 208) /\
                read (memory :> bytes64 (word_add stackpointer (word 208))) s =
                x19_init /\
                read (memory :> bytes64 (word_add stackpointer (word 216))) s =
                x20_init /\
                read (memory :> bytes64 (word_add stackpointer (word 224))) s =
                x21_init /\
                read (memory :> bytes64 (word_add stackpointer (word 232))) s =
                x22_init /\
                read (memory :> bytes64 (word_add stackpointer (word 240))) s =
                x23_init /\
                read (memory :> bytes64 (word_add stackpointer (word 248))) s =
                x24_init /\
                read (memory :> bytes64 (word_add stackpointer (word 256))) s =
                x25_init /\
                read (memory :> bytes64 (word_add stackpointer (word 264))) s =
                x26_init /\
                read (memory :> bytes64 (word_add stackpointer (word 272))) s =
                x27_init /\
                read (memory :> bytes64 (word_add stackpointer (word 280))) s =
                returnaddress /\
                read (memory :> bytes64 (word_add stackpointer (word 296))) s =
                canary /\
                read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
                guard /\
                read (memory :> bytes64 guard) s = canary` THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (1--4) THEN
          MLKEM_NATIVE_ADRP_TAC THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (5--21) THEN
          ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
          ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
           (22--22) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
          CONJ_TAC THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
            ASM_SIMP_TAC[ARITH_RULE
             `~(mlen < r) ==> ~(mlen <= r /\ ~(r = mlen))`];
            DISCHARGE_SAFETY_PROPERTY_TAC];

          (X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
            REWRITE_TAC(!simulation_precanon_thms) THEN
            ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
            MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`]
                         ABSORB_BLOCK_BOUND) THEN
            ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
            SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
             [SIMPLE_ARITH_TAC; ALL_TAC] THEN
            ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
             (1--8) THEN
            ARGS_32_TAC [`r:num`] THEN
            ABSX4_SAFE_XOR_TAC `0` `r:num` (ABSX4_SAFE_VARS @ [`i:num`]) 9 THEN
            ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
             (10--12) THEN
            ABSX4_SAFE_CALL_TAC "H_PERMUTE"
              [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
               `read X30 s`] (ABSX4_SAFE_VARS @ [`i:num`]) 13 THEN
            ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
             (14--18) THEN
            SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                          word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
             [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o
                lhand o snd) THEN
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
            ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
             (19--19) THEN
            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
            MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
            ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
            CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
            REPEAT(CONJ_TAC THENL
             [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
              REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
              ALL_TAC]) THEN
            DISCHARGE_SAFETY_PROPERTY_TAC);

          REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC]];

    (*** The last block ***)

    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_SAFE_TAIL_TAC]);;
