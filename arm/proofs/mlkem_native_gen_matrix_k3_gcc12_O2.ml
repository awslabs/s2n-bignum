(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generation of the ML-KEM-768 matrix from a seed. This is the code for     *)
(* mlkem768_gen_matrix from mlkem-native's portable C implementation         *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which copies    *)
(* the seed of 32 bytes into four buffers of 64 bytes on the stack, appends  *)
(* the two indices of each entry of the matrix to it, samples the first      *)
(* eight of the nine entries four at a time with mlkem_poly_rej_uniform_x4   *)
(* and the last one with mlkem_poly_rej_uniform, and zeroes the buffers. It  *)
(* is verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),   *)
(* where it is at address 0x4f50, using the theorems for                     *)
(* mlkem_poly_rej_uniform_x4 at 0x4b30 and mlkem_poly_rej_uniform at 0x4d40  *)
(* in the image. There is no constant-time and memory safety proof yet (see  *)
(* mlkem_native/README.md).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_poly_rej_uniform_x4_gcc12_O2.ml";;

(*** The code in the image:

    4f50: stp     x19, x20, [sp, #-320]!
    4f54: mov     x20, x0
    4f58: adrp    x4, 1f000 <mlk_zetas+0x18c80>
    4f5c: ldr     x4, [x4, #4088]
    4f60: add     x19, sp, #0x3f
    4f64: str     x30, [sp, #16]
    4f68: and     x19, x19, #0xffffffffffffffe0
    4f6c: mov     x3, x19
    4f70: add     x0, x19, #0x100
    4f74: ldr     x5, [x4]
    4f78: str     x5, [sp, #312]
    4f7c: mov     x5, #0x0
    4f80: ldp     q0, q1, [x1]
    4f84: stp     q0, q1, [x3]
    4f88: add     x3, x3, #0x40
    4f8c: cmp     x3, x0
    4f90: b.ne    4f80 <mlkem768_gen_matrix+0x30>
    4f94: strh    wzr, [x19, #32]
    4f98: cbnz    w2, 5074 <mlkem768_gen_matrix+0x124>
    4f9c: mov     w7, #0x1
    4fa0: mov     w6, #0x2
    4fa4: mov     w5, #0x100
    4fa8: mov     x4, x19
    4fac: add     x3, x20, #0x600
    4fb0: add     x2, x20, #0x400
    4fb4: add     x1, x20, #0x200
    4fb8: mov     x0, x20
    4fbc: strh    w7, [x19, #96]
    4fc0: strh    w6, [x19, #160]
    4fc4: strh    w5, [x19, #224]
    4fc8: bl      4b30 <mlkem_poly_rej_uniform_x4>
    4fcc: mov     w7, #0x2
    4fd0: mov     w5, w7
    4fd4: mov     w8, #0x0
    4fd8: mov     w6, #0x1
    4fdc: mov     w9, #0x101
    4fe0: mov     x4, x19
    4fe4: add     x3, x20, #0xe00
    4fe8: add     x2, x20, #0xc00
    4fec: add     x1, x20, #0xa00
    4ff0: add     x0, x20, #0x800
    4ff4: strh    w9, [x19, #32]
    4ff8: strb    w5, [x19, #96]
    4ffc: strb    w6, [x19, #97]
    5000: strb    w8, [x19, #160]
    5004: strb    w7, [x19, #161]
    5008: strb    w6, [x19, #224]
    500c: strb    w5, [x19, #225]
    5010: bl      4b30 <mlkem_poly_rej_uniform_x4>
    5014: mov     w2, #0x202
    5018: add     x0, x20, #0x1, lsl #12
    501c: mov     x1, x19
    5020: strh    w2, [x19, #32]
    5024: bl      4d40 <mlkem_poly_rej_uniform>
    5028: movi    v0.4s, #0x0
    502c: stp     q0, q0, [x19]
    5030: stp     q0, q0, [x19, #32]
    5034: stp     q0, q0, [x19, #64]
    5038: stp     q0, q0, [x19, #96]
    503c: stp     q0, q0, [x19, #128]
    5040: stp     q0, q0, [x19, #160]
    5044: stp     q0, q0, [x19, #192]
    5048: stp     q0, q0, [x19, #224]
    504c: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    5050: ldr     x0, [x0, #4088]
    5054: ldr     x2, [sp, #312]
    5058: ldr     x1, [x0]
    505c: subs    x2, x2, x1
    5060: mov     x1, #0x0
    5064: b.ne    50b8 <mlkem768_gen_matrix+0x168>
    5068: ldr     x30, [sp, #16]
    506c: ldp     x19, x20, [sp], #320
    5070: ret
    5074: mov     w7, #0x100
    5078: mov     w6, #0x200
    507c: mov     w5, #0x1
    5080: mov     x4, x19
    5084: add     x3, x20, #0x600
    5088: add     x2, x20, #0x400
    508c: add     x1, x20, #0x200
    5090: mov     x0, x20
    5094: strh    w7, [x19, #96]
    5098: strh    w6, [x19, #160]
    509c: strh    w5, [x19, #224]
    50a0: bl      4b30 <mlkem_poly_rej_uniform_x4>
    50a4: mov     w8, #0x2
    50a8: mov     w7, #0x0
    50ac: mov     w6, w8
    50b0: mov     w5, #0x1
    50b4: b       4fdc <mlkem768_gen_matrix+0x8c>
    50b8: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x4f50,0x50bc];;

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

let GENMAT3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3375)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3360 else 3344))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let GENMAT3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` GENMAT3_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset (for the callees).    *)
(* The seed is 32 bytes at seed, given as a list of bytes rho. Entry (i,j)   *)
(* of the matrix, the polynomial at a + 512 * (3 * i + j), is sampled from   *)
(* shake128 of rho followed by the bytes j and i, as for the matrix in FIPS  *)
(* 203, or by i and j if transposed (as a 32-bit integer) is nonzero, which  *)
(* gives the transposed matrix. As for mlkem_poly_rej_uniform, the theorem   *)
(* has the hypothesis that for some k there are at least 256 samples within  *)
(* the first 504 + 168 * k bytes of shake128 for each entry. The proof is by *)
(* cases on whether the stack pointer is a multiple of 32, which gives the   *)
(* address of the buffers, and on whether transposed is zero. The stack is   *)
(* the 320 bytes of the function and the 3312 used by                        *)
(* mlkem_poly_rej_uniform_x4 below them.                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLY_REJ_UNIFORM_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REJ_UNIFORM_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the stack guard and the saved registers ***)

let GENMAT3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`; `k:num`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3632 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3632):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20`;;

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

let GENMAT3_CASE_TAC b tr =
  let d = if tr then 1 else 0 in
  let st n = mk_var("s"^string_of_int n,`:armstate`) in
  let xy e = let i = e / 3 and j = e mod 3 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let inputs g s =
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (b + 64 * m) x y s) (0--3) in
  let rest = [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
              `ev:num`; `pc:num`; `read SP s`; `read X30 s`] in
  let args5 = [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
               `read X4 s`] in
  (if tr then
     SUBGOAL_THEN `~(val(word_zx(transposed:int64):int32) = 0)` ASSUME_TAC
     THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC]
   else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The four copies of the seed ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (4--7) THEN
  GENMAT3_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (8--12) THEN
  MAP_EVERY (fun m ->
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
     ((13 + 5 * m)--(16 + 5 * m)) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC [17 + 5 * m])
   (0--3) THEN

  (*** The first four entries ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (33--46) THEN
  inputs 0 (st 46) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 3) (e mod 3)) (0--8) THEN
  GENMAT_GOT_TAC THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (0--3) @ rest) 47 THEN
  GENMAT_TOBYTES_TAC THEN

  (*** The next four ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (48--(65 + d)) THEN
  inputs 1 (st(65 + d)) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (4--7) @ rest) (66 + d) THEN
  GENMAT_TOBYTES_TAC THEN

  (*** The last one ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((67 + d)--(71 + d)) THEN
  (let x,y = xy 8 in GENMAT_INPUT_TAC b x y (st(71 + d))) THEN
  LOCAL_POLY_REJ_UNIFORM_TAC ([`read X0 s`; `read X1 s`; seed 8] @ rest)
   (72 + d) THEN
  GENMAT_TOBYTES_TAC THEN

  (*** Zeroing the seeds, the stack guard, the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((73 + d)--(82 + d)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((83 + d)--(91 + d)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN GENMAT_FINAL_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a seed (rho:byte list) transposed k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH rho = 32 /\
        (!i j. i < 3 /\ j < 3
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
        nonoverlapping (a,4608) (word_sub stackpointer (word 3632),3632) /\
        ALLPAIRS nonoverlapping
         [(a,4608); (word_sub stackpointer (word 3632),3632)]
         [(seed,32); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x4f50) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist rho)
             (\s. read PC s = returnaddress /\
                  !i j. i < 3 /\ j < 3
                        ==> wordlist_from_memory
                             (word_add a (word(512 * (3 * i + j))),256) s =
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
               [memory :> bytes(a,4608);
                memory :> bytes(word_sub stackpointer (word 3632),3632)])`,
  GENMAT3_INTRO_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THEN
  ASM_CASES_TAC `word_zx(transposed:int64):int32 = word 0` THENL
   [GENMAT3_CASE_TAC 3360 false; GENMAT3_CASE_TAC 3360 true;
    GENMAT3_CASE_TAC 3344 false; GENMAT3_CASE_TAC 3344 true]);;
