(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generation of the ML-KEM-1024 matrix from a seed. This is the code for    *)
(* mlkem1024_gen_matrix from mlkem-native's portable C implementation        *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which copies    *)
(* the seed of 32 bytes into four buffers of 64 bytes on the stack, and then *)
(* for each row of the matrix appends the two indices of each of its four    *)
(* entries to it in a loop and samples them with mlkem_poly_rej_uniform_x4,  *)
(* and zeroes the buffers. It is verified in the whole image (see            *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x850, using   *)
(* the theorem for mlkem_poly_rej_uniform_x4 at 0x4b30 in the image. There   *)
(* is no constant-time and memory safety proof yet (see                      *)
(* mlkem_native/README.md).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_rej_uniform_x4_gcc12_O2.ml";;

(*** The code in the image:

    850: stp     x19, x20, [sp, #-368]!
    854: adrp    x4, 1f000 <mlk_zetas+0x18c80>
    858: ldr     x4, [x4, #4088]
    85c: add     x20, sp, #0x6f
    860: stp     x21, x22, [sp, #16]
    864: and     x20, x20, #0xffffffffffffffe0
    868: mov     x3, x20
    86c: stp     x23, x24, [sp, #32]
    870: mov     x24, x0
    874: add     x0, x20, #0x100
    878: stp     x25, x26, [sp, #48]
    87c: mov     w25, w2
    880: str     x30, [sp, #64]
    884: ldr     x2, [x4]
    888: str     x2, [sp, #360]
    88c: mov     x2, #0x0
    890: ldp     q0, q1, [x1]
    894: stp     q0, q1, [x3]
    898: add     x3, x3, #0x40
    89c: cmp     x0, x3
    8a0: b.ne    890 <mlkem1024_gen_matrix+0x40>
    8a4: mov     w19, #0x4
    8a8: mov     w26, #0x800
    8ac: mov     x23, #0x600
    8b0: mov     x22, #0x400
    8b4: mov     x21, #0x200
    8b8: sub     w0, w19, #0x4
    8bc: mov     x6, x20
    8c0: mov     w1, w0
    8c4: and     w5, w1, #0x3
    8c8: ubfx    x3, x1, #2, #8
    8cc: cmp     w25, #0x0
    8d0: mov     w4, w5
    8d4: add     w1, w1, #0x1
    8d8: csel    w5, w5, w3, eq
    8dc: csel    w3, w3, w4, eq
    8e0: strb    w5, [x6, #32]
    8e4: strb    w3, [x6, #33]
    8e8: add     x6, x6, #0x40
    8ec: cmp     w19, w1
    8f0: b.ne    8c4 <mlkem1024_gen_matrix+0x74>
    8f4: sub     w3, w19, #0x1
    8f8: sub     w2, w19, #0x2
    8fc: sub     w1, w19, #0x3
    900: lsr     w0, w0, #2
    904: lsr     w3, w3, #2
    908: lsr     w2, w2, #2
    90c: lsr     w1, w1, #2
    910: add     w19, w19, #0x4
    914: add     x0, x24, x0, lsl #11
    918: mov     x4, x20
    91c: umaddl  x3, w3, w26, x23
    920: umaddl  x2, w2, w26, x22
    924: umaddl  x1, w1, w26, x21
    928: add     x3, x24, x3
    92c: add     x2, x24, x2
    930: add     x1, x24, x1
    934: bl      4b30 <mlkem_poly_rej_uniform_x4>
    938: cmp     w19, #0x14
    93c: b.ne    8b8 <mlkem1024_gen_matrix+0x68>
    940: movi    v0.4s, #0x0
    944: stp     q0, q0, [x20]
    948: stp     q0, q0, [x20, #32]
    94c: stp     q0, q0, [x20, #64]
    950: stp     q0, q0, [x20, #96]
    954: stp     q0, q0, [x20, #128]
    958: stp     q0, q0, [x20, #160]
    95c: stp     q0, q0, [x20, #192]
    960: stp     q0, q0, [x20, #224]
    964: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    968: ldr     x0, [x0, #4088]
    96c: ldr     x2, [sp, #360]
    970: ldr     x1, [x0]
    974: subs    x2, x2, x1
    978: mov     x1, #0x0
    97c: b.ne    998 <mlkem1024_gen_matrix+0x148>
    980: ldp     x21, x22, [sp, #16]
    984: ldp     x23, x24, [sp, #32]
    988: ldp     x25, x26, [sp, #48]
    98c: ldr     x30, [sp, #64]
    990: ldp     x19, x20, [sp], #368
    994: ret
    998: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x850,0x99c];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the two indices  *)
(* of an entry in a buffer of 64 bytes, as 34 bytes for SHAKE128. The four   *)
(* buffers are aligned to 32 bytes within the stack frame, so their address  *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let GENMAT_BYTES128_HALVES = prove
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

let GENMAT_BYTES_32_OF_HALVES = prove
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

let GENMAT_BYTES2 = prove
 (`(!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)) /\
   (!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8(word_add a (word 1))) s))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE; BYTES8_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let GENMAT_INPUT = prove
 (`!a:int64 (rho:byte list) x y s:armstate.
        LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist rho MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist rho DIV 2 EXP 128) /\
        read (memory :> bytes(word_add a (word 32),2)) s = x + 256 * y
        ==> LENGTH(APPEND rho [word x:byte; word y]) = 34 /\
            read (memory :> bytes(a,34)) s =
            num_of_bytelist(APPEND rho [word x; word y])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist rho`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GENMAT_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let GENMAT4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3423)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3392 else 3408))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let GENMAT4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` GENMAT4_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset (for the callees).    *)
(* The seed is 32 bytes at seed, given as a list of bytes rho. Entry (i,j)   *)
(* of the matrix, the polynomial at a + 512 * (4 * i + j), is sampled from   *)
(* shake128 of rho followed by the bytes j and i, as for the matrix in FIPS  *)
(* 203, or by i and j if transposed (as a 32-bit integer) is nonzero, which  *)
(* gives the transposed matrix. As for mlkem_poly_rej_uniform, the theorem   *)
(* has the hypothesis that for some k there are at least 256 samples within  *)
(* the first 504 + 168 * k bytes of shake128 for each entry. The proof is by *)
(* cases on whether the stack pointer is a multiple of 32, which gives the   *)
(* address of the buffers, and on whether transposed is zero. The stack is   *)
(* the 368 bytes of the function and the 3312 used by                        *)
(* mlkem_poly_rej_uniform_x4 below them.                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLY_REJ_UNIFORM_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the stack guard and the saved registers ***)

let GENMAT4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`; `k:num`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3680 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3680):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--26);;

(*** The buffers and the inputs to SHAKE128 in them ***)

let GENMAT_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let GENMAT_SEED x y =
  let b n = mk_comb(`word:num->byte`,mk_small_numeral n) in
  mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,`rho:byte list`),
          mk_list([b x; b y],`:byte`));;

let GENMAT_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV GENMAT_INPUT in
  fun off x y s ->
    let sl = GENMAT_SP off and a32 = GENMAT_SP(off + 32) in
    let n = mk_small_numeral(x + 256 * y) in
    SUBGOAL_THEN
     (mk_eq(list_mk_comb(`read:(armstate,num)component->armstate->num`,
                         [mk_comb(`(:>) memory:(int64->byte,num)component->
                                   (armstate,num)component`,
                                  mk_comb(`bytes:int64#num->
                                           (int64->byte,num)component`,
                                          mk_pair(a32,`2`)));
                          s]),n))
    ASSUME_TAC THENL
     [(REWRITE_TAC[CONJUNCT1 GENMAT_BYTES2] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) ORELSE
      (REWRITE_TAC[CONJUNCT2 GENMAT_BYTES2] THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
       CONV_TAC NUM_REDUCE_CONV);
      ALL_TAC] THEN
    MP_TAC(SPECL [sl; `rho:byte list`; mk_small_numeral x;
                  mk_small_numeral y; s] th) THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      STRIP_TAC];;

let GENMAT_HYP_TAC i j =
  W(fun (asl,_) ->
    let cth = find (fun th ->
      concl th = `word_zx(transposed:int64):int32 = word 0` ||
      concl th = `~(word_zx(transposed:int64):int32 = word 0)`)
      (map snd asl)
    and hth = find (fun th ->
      match concl th with
        Comb(Const("!",_),Abs(Var("i",_),_)) -> true | _ -> false)
      (map snd asl) in
    let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
    let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
    ASSUME_TAC(REWRITE_RULE[cth] th2));;

let GENMAT_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes64
                     (word_add (word (pc:num)) (word 131064):int64)) s =
              (g:int64)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;

(*** The results, in the form of the specification ***)

let GENMAT_TOBYTES_TAC =
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
    MATCH_MP REJ_BYTES16_OF_WORDLIST o check
     (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
      concl)));;

let GENMAT_FINAL1_TAC =
  W(fun (_,w) ->
    let l = rand w in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[]);;

let GENMAT_FINAL_TAC =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  GENMAT_FINAL1_TAC;;

(*** The simulation in each case, aligned or not, transposed or not ***)

let GENMAT4_CASE_TAC b tr =
  let st n = mk_var("s"^string_of_int n,`:armstate`) in
  let xy e = let i = e / 4 and j = e mod 4 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let rest = [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
              `ev:num`; `pc:num`; `read SP s`; `read X30 s`] in
  let args5 = [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
               `read X4 s`] in
  (if tr then
     SUBGOAL_THEN
      `~(val(word_sub (word_zx(word_zx(word_zx(transposed:int64):int32):
                                 int64):int32) (word 0)) = 0)`
     ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
       UNDISCH_TAC `~(word_zx(transposed:int64):int32 = word 0)` THEN
       CONV_TAC WORD_BLAST;
       ALL_TAC]
   else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The four copies of the seed ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (3--6) THEN
  GENMAT4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (7--16) THEN
  MAP_EVERY (fun m ->
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((17 + 5 * m)--(20 + 5 * m)) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [21 + 5 * m])
   (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (37--41) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  GENMAT_GOT_TAC THEN

  (*** Each row of four entries, the indices and the call ***)

  MAP_EVERY (fun g ->
    let s0 = 42 + 71 * g in
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     (s0--(s0 + 67)) THEN
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (b + 64 * m) x y (st(s0 + 67)))
     (0--3) THEN
    LOCAL_POLY_REJ_UNIFORM_X4_TAC
     (args5 @ map seed ((4 * g)--(4 * g + 3)) @ rest) (s0 + 68) THEN
    GENMAT_TOBYTES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 69)--(s0 + 70)))
   (0--3) THEN

  (*** Zeroing the seeds, the stack guard, the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (326--335) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (336--347) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN GENMAT_FINAL_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a seed (rho:byte list) transposed k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH rho = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                           (MAP (word_zx:12 word->16 word)
                             (wordlist_of_num (336 + 112 * k)
                               (num_of_bytelist
                                 (list_of_seq
                                   (shake128
                                     (APPEND rho
                                       (if word_zx transposed = (word 0:int32)
                                        then [word j; word i]
                                        else [word i; word j])))
                                   (504 + 168 * k))))))) /\
        nonoverlapping (a,8192) (word_sub stackpointer (word 3680),3680) /\
        ALLPAIRS nonoverlapping
         [(a,8192); (word_sub stackpointer (word 3680),3680)]
         [(seed,32); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x850) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist rho)
             (\s. read PC s = returnaddress /\
                  !i j. i < 4 /\ j < 4
                        ==> wordlist_from_memory
                             (word_add a (word(512 * (4 * i + j))),256) s =
                            SUB_LIST(0,256)
                             (FILTER (\x. val x < 3329)
                               (MAP (word_zx:12 word->16 word)
                                 (wordlist_of_num (336 + 112 * k)
                                   (num_of_bytelist
                                     (list_of_seq
                                       (shake128
                                         (APPEND rho
                                           (if word_zx transposed =
                                               (word 0:int32)
                                            then [word j; word i]
                                            else [word i; word j])))
                                       (504 + 168 * k)))))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,8192);
                memory :> bytes(word_sub stackpointer (word 3680),3680)])`,
  GENMAT4_INTRO_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THEN
  ASM_CASES_TAC `word_zx(transposed:int64):int32 = word 0` THENL
   [GENMAT4_CASE_TAC 3392 false; GENMAT4_CASE_TAC 3392 true;
    GENMAT4_CASE_TAC 3408 false; GENMAT4_CASE_TAC 3408 true]);;
