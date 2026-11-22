(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generation of the ML-KEM-1024 matrix from a seed. This is the code for    *)
(* mlkem1024_gen_matrix from mlkem-native's portable C implementation        *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which copies  *)
(* the seed of 32 bytes into four buffers of 64 bytes on the stack, appends  *)
(* the two indices of each entry of the matrix to it, and samples the        *)
(* entries with mlkem_poly_rej_uniform_x4, four at a time, and zeroes the buffers. The code has the calls    *)
(* unrolled and computes the indices before the first call, keeping some of  *)
(* them in registers and in the stack frame across the calls. It is          *)
(* verified in the whole image (see libmlkem.ml), using the theorems for mlkem_poly_rej_uniform_x4     *)
(* in the image. The buffers are aligned to 32 bytes within the stack frame, *)
(* which the code makes by rounding the stack pointer down, so the proof is  *)
(* by cases on whether the incoming stack pointer is a multiple of 32.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_rej_uniform_x4_spec.ml";;

(*** The code in the image:

    mlkem1024_gen_matrix:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x160
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: add     x9, x0, #0x800
      +0x2c: cmp     w2, #0x0
      +0x30: add     x2, x0, #0x400
      +0x34: cset    w21, ne
      +0x38: cset    w22, eq
      +0x3c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x40: add     x3, x0, #0x600
      +0x44: lsl     w23, w22, #1
      +0x48: lsl     w25, w21, #1
      +0x4c: add     x4, sp, #0x40
      +0x50: mov     x19, x0
      +0x54: ldr     x8, [x8]
      +0x58: str     x8, [sp, #344]
      +0x5c: add     x8, x0, #0xa00
      +0x60: ldp     q0, q1, [x1]
      +0x64: add     x1, x0, #0x200
      +0x68: strh    wzr, [sp, #96]
      +0x6c: stp     x8, x9, [sp, #32]
      +0x70: add     x9, x0, #0xc00
      +0x74: add     x8, x0, #0xe00
      +0x78: strb    w22, [sp, #160]
      +0x7c: strb    w21, [sp, #161]
      +0x80: strb    w23, [sp, #224]
      +0x84: stp     x8, x9, [sp, #16]
      +0x88: mov     w8, #0x3
      +0x8c: csel    w10, w8, wzr, eq
      +0x90: mov     w9, #0x1
      +0x94: csel    w20, wzr, w8, eq
      +0x98: csinc   w28, w8, wzr, eq
      +0x9c: csinc   w24, w8, wzr, ne
      +0xa0: mov     w8, #0x2
      +0xa4: cinc    w26, w9, eq
      +0xa8: cinc    w27, w9, ne
      +0xac: cinc    w9, w8, eq
      +0xb0: cinc    w8, w8, ne
      +0xb4: stp     q0, q1, [sp, #64]
      +0xb8: stp     q0, q1, [sp, #128]
      +0xbc: stp     q0, q1, [sp, #192]
      +0xc0: stp     q0, q1, [sp, #256]
      +0xc4: stp     w9, w10, [sp, #56]
      +0xc8: str     w8, [sp, #52]
      +0xcc: strb    w25, [sp, #225]
      +0xd0: strb    w10, [sp, #288]
      +0xd4: strb    w20, [sp, #289]
      +0xd8: bl      <mlkem_poly_rej_uniform_x4>
      +0xdc: ldp     x1, x0, [sp, #32]
      +0xe0: mov     w8, #0x101
      +0xe4: add     x4, sp, #0x40
      +0xe8: ldp     x3, x2, [sp, #16]
      +0xec: strb    w21, [sp, #96]
      +0xf0: strb    w22, [sp, #97]
      +0xf4: strb    w26, [sp, #224]
      +0xf8: strh    w8, [sp, #160]
      +0xfc: strb    w27, [sp, #225]
     +0x100: strb    w28, [sp, #288]
     +0x104: strb    w24, [sp, #289]
     +0x108: bl      <mlkem_poly_rej_uniform_x4>
     +0x10c: mov     w8, #0x202
     +0x110: mov     w9, #0x1200
     +0x114: strb    w23, [sp, #97]
     +0x118: add     x1, x19, x9
     +0x11c: mov     w9, #0x1600
     +0x120: add     x0, x19, #0x1, lsl #12
     +0x124: strh    w8, [sp, #224]
     +0x128: mov     w8, #0x1400
     +0x12c: ldp     w23, w21, [sp, #52]
     +0x130: add     x2, x19, x8
     +0x134: add     x3, x19, x9
     +0x138: add     x4, sp, #0x40
     +0x13c: strb    w25, [sp, #96]
     +0x140: strb    w27, [sp, #160]
     +0x144: strb    w26, [sp, #161]
     +0x148: strb    w21, [sp, #288]
     +0x14c: strb    w23, [sp, #289]
     +0x150: bl      <mlkem_poly_rej_uniform_x4>
     +0x154: ldr     w9, [sp, #60]
     +0x158: mov     w10, #0x1e00
     +0x15c: mov     w8, #0x303
     +0x160: add     x3, x19, x10
     +0x164: add     x4, sp, #0x40
     +0x168: strb    w20, [sp, #96]
     +0x16c: strb    w9, [sp, #97]
     +0x170: mov     w9, #0x1800
     +0x174: add     x0, x19, x9
     +0x178: mov     w9, #0x1a00
     +0x17c: add     x1, x19, x9
     +0x180: mov     w9, #0x1c00
     +0x184: add     x2, x19, x9
     +0x188: strb    w24, [sp, #160]
     +0x18c: strb    w28, [sp, #161]
     +0x190: strb    w23, [sp, #224]
     +0x194: strb    w21, [sp, #225]
     +0x198: strh    w8, [sp, #288]
     +0x19c: bl      <mlkem_poly_rej_uniform_x4>
     +0x1a0: movi    v0.2d, #0x0
     +0x1a4: add     x8, sp, #0x40
     +0x1a8: stp     q0, q0, [sp, #64]
     +0x1ac: stp     q0, q0, [sp, #96]
     +0x1b0: stp     q0, q0, [sp, #128]
     +0x1b4: stp     q0, q0, [sp, #160]
     +0x1b8: stp     q0, q0, [sp, #192]
     +0x1bc: stp     q0, q0, [sp, #224]
     +0x1c0: stp     q0, q0, [sp, #256]
     +0x1c4: stp     q0, q0, [sp, #288]
     +0x1c8: adrp    x8, <page>
     +0x1cc: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x1d0: ldr     x9, [sp, #344]
     +0x1d4: ldr     x8, [x8]
     +0x1d8: cmp     x8, x9
     +0x1dc: b.ne    <mlkem1024_gen_matrix+0x200>
     +0x1e0: mov     sp, x29
     +0x1e4: ldp     x20, x19, [sp, #80]
     +0x1e8: ldp     x22, x21, [sp, #64]
     +0x1ec: ldp     x24, x23, [sp, #48]
     +0x1f0: ldp     x26, x25, [sp, #32]
     +0x1f4: ldp     x28, x27, [sp, #16]
     +0x1f8: ldp     x29, x30, [sp], #96
     +0x1fc: ret
     +0x200: bl      __stack_chk_fail
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_gen_matrix"];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the two indices  *)
(* of an entry in a buffer of 64 bytes, as 34 bytes for SHAKE128. The four   *)
(* buffers are aligned to 32 bytes within the stack frame, so their address  *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let GENMAT_BYTES128_HALVES_STMT =
  `!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let GENMAT_BYTES128_HALVES = assume_spec GENMAT_BYTES128_HALVES_STMT;;

let GENMAT_BYTES_32_OF_HALVES_STMT =
  `!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`;;

let GENMAT_BYTES_32_OF_HALVES = assume_spec GENMAT_BYTES_32_OF_HALVES_STMT;;

let GENMAT_BYTES2_STMT =
  `(!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)) /\
   (!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8(word_add a (word 1))) s))`;;

let GENMAT_BYTES2 = assume_spec GENMAT_BYTES2_STMT;;

let GENMAT_INPUT_STMT =
  `!a:int64 (rho:byte list) x y s:armstate.
        LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist rho MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist rho DIV 2 EXP 128) /\
        read (memory :> bytes(word_add a (word 32),2)) s = x + 256 * y
        ==> LENGTH(APPEND rho [word x:byte; word y]) = 34 /\
            read (memory :> bytes(a,34)) s =
            num_of_bytelist(APPEND rho [word x; word y])`;;

let GENMAT_INPUT = assume_spec GENMAT_INPUT_STMT;;

let GENMAT4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3408)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3392 else 3408))`;;

let GENMAT4_BUFFER_ADDRESS = assume_spec GENMAT4_BUFFER_ADDRESS_STMT;;

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
(* the 96 bytes of saved registers, 352 bytes of the buffers and the       *)
(* canary, up to 16 bytes of padding for the alignment, and the 3392 used  *)
(* by mlkem_poly_rej_uniform_x4 below them.                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLY_REJ_UNIFORM_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

(*** The addresses of the buffers are multiples of 16 in both cases ***)

let GENMAT_ALIGNED_TAC =
  MAP_EVERY (fun n ->
    SUBGOAL_THEN
     (subst [mk_small_numeral n,`n:num`]
       `aligned 16 (word_add (stackpointer:int64) (word n))`) ASSUME_TAC THENL
     [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC]) [3392; 3408];;

(*** The setup, with the stack guard and the saved registers ***)

let GENMAT4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`; `k:num`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3856 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

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
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

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
      `~(val(word_sub (word_zx(transposed:int64):int32) (word 0)) = 0)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0]; ALL_TAC]
   else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (1--9) THEN
  GENMAT4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (10--10) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (11--54) THEN
  MAP_EVERY (fun m -> let x,y = xy (0 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 54)) (0--3) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (55--55) THEN
  GENMAT_GOT_TAC THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (0--3) @ rest) 56 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (57--67) THEN
  MAP_EVERY (fun m -> let x,y = xy (4 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 67)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (68--68) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (4--7) @ rest) 69 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (70--86) THEN
  MAP_EVERY (fun m -> let x,y = xy (8 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 86)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (87--87) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (8--11) @ rest) 88 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (89--106) THEN
  MAP_EVERY (fun m -> let x,y = xy (12 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 106)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (107--107) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (12--15) @ rest) 108 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (109--119) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (120--132) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN GENMAT_FINAL_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a seed (rho:byte list) transposed k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
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
        nonoverlapping (a,8192) (word_sub stackpointer (word 3856),3856) /\
        ALLPAIRS nonoverlapping
         [(a,8192); (word_sub stackpointer (word 3856),3856)]
         [(seed,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_gen_matrix) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                memory :> bytes(word_sub stackpointer (word 3856),3856)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset as for mlkem_poly_rej_uniform_x4. The events depend only on the    *)
(* addresses, rho and the flag, through the samples of each entry, which are *)
(* public. They are given by cases on whether the stack pointer is a         *)
(* multiple of 32, which gives the address of the buffers, and on the flag,  *)
(* which gives the order of the indices and a branch.                        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GENMAT_SAFE_TEMPLATE =
 `\(a:int64) (seed:int64) (rho:byte list) (transposed:int64) (guard:int64)
   (mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   if aligned 32 stackpointer
   then (if word_zx transposed = (word 0:int32)
         then f_ev_an a seed rho transposed guard mf pc stackpointer
                      returnaddress
         else f_ev_at a seed rho transposed guard mf pc stackpointer
                      returnaddress)
   else (if word_zx transposed = (word 0:int32)
         then f_ev_un a seed rho transposed guard mf pc stackpointer
                      returnaddress
         else f_ev_ut a seed rho transposed guard mf pc stackpointer
                      returnaddress)
   :(uarch_event)list`;;

let GENMAT_SAFE_ALLOWED =
  [`pc:num`; `a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`;
   `guard:int64`; `mf:int64`; `stackpointer:int64`; `returnaddress:int64`];;

let GENMAT4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[ALL] (MATCH_MP
       MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE th))
     "H_X4") THEN
  CONCRETIZE_F_EVENTS_TAC GENMAT_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

let GENMAT4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GENMAT_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let GENMAT4_SAFE_CASE_TAC b tr =
  let st n = mk_var("s"^string_of_int n,`:armstate`) in
  let xy e = let i = e / 4 and j = e mod 4 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let rest = [`k:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] in
  let args5 = [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
               `read X3 s`; `read X4 s`] in
  (if tr then
     SUBGOAL_THEN
      `~(val(word_sub (word_zx(transposed:int64):int32) (word 0)) = 0)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0]; ALL_TAC]
   else ALL_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (1--9) THEN
  GENMAT4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (10--10) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (11--54) THEN
  MAP_EVERY (fun m -> let x,y = xy (0 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 54)) (0--3) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (55--55) THEN
  GENMAT_GOT_TAC THEN
  GENMAT4_SAFE_CALL_TAC "H_X4" (args5 @ map seed (0--3) @ rest) 56 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (57--67) THEN
  MAP_EVERY (fun m -> let x,y = xy (4 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 67)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (68--68) THEN
  GENMAT4_SAFE_CALL_TAC "H_X4" (args5 @ map seed (4--7) @ rest) 69 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (70--86) THEN
  MAP_EVERY (fun m -> let x,y = xy (8 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 86)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (87--87) THEN
  GENMAT4_SAFE_CALL_TAC "H_X4" (args5 @ map seed (8--11) @ rest) 88 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (89--106) THEN
  MAP_EVERY (fun m -> let x,y = xy (12 + m) in
                      GENMAT_INPUT_TAC (b + 64 + 64 * m) x y (st 106)) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (107--107) THEN
  GENMAT4_SAFE_CALL_TAC "H_X4" (args5 @ map seed (12--15) @ rest) 108 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (109--119) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_EXEC (120--132) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
        forall e a seed (rho:byte list) transposed k guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH rho = 32 /\
          (!i j. i < 4 /\ j < 4
                 ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
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
                                     (504 + 168 * k))))))) /\
          nonoverlapping (a,8192) (word_sub stackpointer (word 3856),3856) /\
          ALLPAIRS nonoverlapping
           [(a,8192); (word_sub stackpointer (word 3856),3856)]
           [(seed,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem1024_gen_matrix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed; transposed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = num_of_bytelist rho /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed rho transposed guard mf pc
                              (word_sub stackpointer (word 3856))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; a,8192;
                         word_sub stackpointer (word 3856),3856;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                        [a,8192; word_sub stackpointer (word 3856),3856]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,8192);
                  memory :> bytes(word_sub stackpointer (word 3856),3856)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
