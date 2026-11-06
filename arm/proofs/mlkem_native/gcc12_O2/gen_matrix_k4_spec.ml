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
(* libmlkem.ml), using the theorem for                                       *)
(* mlkem_poly_rej_uniform_x4 in the image.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_rej_uniform_x4_spec.ml";;

(*** The code in the image:

    mlkem1024_gen_matrix:
        +0x0: stp     x19, x20, [sp, #-368]!
        +0x4: adrp    x4, <page>
        +0x8: ldr     x4, [x4, #4088]  // got_stack_chk_guard
        +0xc: add     x20, sp, #0x6f
       +0x10: stp     x21, x22, [sp, #16]
       +0x14: and     x20, x20, #0xffffffffffffffe0
       +0x18: mov     x3, x20
       +0x1c: stp     x23, x24, [sp, #32]
       +0x20: mov     x24, x0
       +0x24: add     x0, x20, #0x100
       +0x28: stp     x25, x26, [sp, #48]
       +0x2c: mov     w25, w2
       +0x30: str     x30, [sp, #64]
       +0x34: ldr     x2, [x4]
       +0x38: str     x2, [sp, #360]
       +0x3c: mov     x2, #0x0
       +0x40: ldp     q0, q1, [x1]
       +0x44: stp     q0, q1, [x3]
       +0x48: add     x3, x3, #0x40
       +0x4c: cmp     x0, x3
       +0x50: b.ne    <mlkem1024_gen_matrix+0x40>
       +0x54: mov     w19, #0x4
       +0x58: mov     w26, #0x800
       +0x5c: mov     x23, #0x600
       +0x60: mov     x22, #0x400
       +0x64: mov     x21, #0x200
       +0x68: sub     w0, w19, #0x4
       +0x6c: mov     x6, x20
       +0x70: mov     w1, w0
       +0x74: and     w5, w1, #0x3
       +0x78: ubfx    x3, x1, #2, #8
       +0x7c: cmp     w25, #0x0
       +0x80: mov     w4, w5
       +0x84: add     w1, w1, #0x1
       +0x88: csel    w5, w5, w3, eq
       +0x8c: csel    w3, w3, w4, eq
       +0x90: strb    w5, [x6, #32]
       +0x94: strb    w3, [x6, #33]
       +0x98: add     x6, x6, #0x40
       +0x9c: cmp     w19, w1
       +0xa0: b.ne    <mlkem1024_gen_matrix+0x74>
       +0xa4: sub     w3, w19, #0x1
       +0xa8: sub     w2, w19, #0x2
       +0xac: sub     w1, w19, #0x3
       +0xb0: lsr     w0, w0, #2
       +0xb4: lsr     w3, w3, #2
       +0xb8: lsr     w2, w2, #2
       +0xbc: lsr     w1, w1, #2
       +0xc0: add     w19, w19, #0x4
       +0xc4: add     x0, x24, x0, lsl #11
       +0xc8: mov     x4, x20
       +0xcc: umaddl  x3, w3, w26, x23
       +0xd0: umaddl  x2, w2, w26, x22
       +0xd4: umaddl  x1, w1, w26, x21
       +0xd8: add     x3, x24, x3
       +0xdc: add     x2, x24, x2
       +0xe0: add     x1, x24, x1
       +0xe4: bl      <mlkem_poly_rej_uniform_x4>
       +0xe8: cmp     w19, #0x14
       +0xec: b.ne    <mlkem1024_gen_matrix+0x68>
       +0xf0: movi    v0.4s, #0x0
       +0xf4: stp     q0, q0, [x20]
       +0xf8: stp     q0, q0, [x20, #32]
       +0xfc: stp     q0, q0, [x20, #64]
      +0x100: stp     q0, q0, [x20, #96]
      +0x104: stp     q0, q0, [x20, #128]
      +0x108: stp     q0, q0, [x20, #160]
      +0x10c: stp     q0, q0, [x20, #192]
      +0x110: stp     q0, q0, [x20, #224]
      +0x114: adrp    x0, <page>
      +0x118: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x11c: ldr     x2, [sp, #360]
      +0x120: ldr     x1, [x0]
      +0x124: subs    x2, x2, x1
      +0x128: mov     x1, #0x0
      +0x12c: b.ne    <mlkem1024_gen_matrix+0x148>
      +0x130: ldp     x21, x22, [sp, #16]
      +0x134: ldp     x23, x24, [sp, #32]
      +0x138: ldp     x25, x26, [sp, #48]
      +0x13c: ldr     x30, [sp, #64]
      +0x140: ldp     x19, x20, [sp], #368
      +0x144: ret
      +0x148: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
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
        ==> word_and (word_add sp (word 3423)) (word 18446744073709551584) =
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
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
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

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
        nonoverlapping (a,8192) (word_sub stackpointer (word 3680),3680) /\
        ALLPAIRS nonoverlapping
         [(a,8192); (word_sub stackpointer (word 3680),3680)]
         [(seed,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
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
                memory :> bytes(word_sub stackpointer (word 3680),3680)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
       MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE th))
     "H_X4") THEN
  CONCRETIZE_F_EVENTS_TAC GENMAT_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3680):int64)` THEN
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
     (mk_const(r,[]))) (19--26);;

let GENMAT4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
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
      `~(val(word_sub (word_zx(word_zx(word_zx(transposed:int64):int32):
                                 int64):int32) (word 0)) = 0)`
     ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
       UNDISCH_TAC `~(word_zx(transposed:int64):int32 = word 0)` THEN
       CONV_TAC WORD_BLAST;
       ALL_TAC]
   else ALL_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
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
  MAP_EVERY (fun g ->
    let s0 = 42 + 71 * g in
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     (s0--(s0 + 67)) THEN
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (b + 64 * m) x y (st(s0 + 67)))
     (0--3) THEN
    GENMAT4_SAFE_CALL_TAC "H_X4"
     (args5 @ map seed ((4 * g)--(4 * g + 3)) @ rest) (s0 + 68) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 69)--(s0 + 70)))
   (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (326--335) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (336--347) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          nonoverlapping (a,8192) (word_sub stackpointer (word 3680),3680) /\
          ALLPAIRS nonoverlapping
           [(a,8192); (word_sub stackpointer (word 3680),3680)]
           [(seed,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
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
                              (word_sub stackpointer (word 3680))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; a,8192;
                         word_sub stackpointer (word 3680),3680;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                        [a,8192; word_sub stackpointer (word 3680),3680]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,8192);
                  memory :> bytes(word_sub stackpointer (word 3680),3680)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
