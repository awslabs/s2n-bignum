(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-512 encapsulation key. This is the code    *)
(* for mlkem512_check_pk from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 as one translation unit (see                  *)
(* mlkem_native/README.md), which decodes the vector of the key from its     *)
(* first 768 bytes into a buffer on the stack, reduces it, encodes it again  *)
(* into another buffer, compares the result in constant time with the key,   *)
(* and zeroes the buffers. It is verified in the whole image (see            *)
(* libmlkem.ml), using the theorems for mlk_poly_frombytes_c,                *)
(* mlk_poly_reduce_c and mlk_poly_tobytes_c in the image and assuming the    *)
(* contracts for memset in utils/mlkem_native_libc.ml.                       *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined                    *)
(* mlkem512_polyvec_frombytes, mlkem512_polyvec_reduce and                   *)
(* mlkem512_polyvec_tobytes, so the function calls each kernel twice itself, *)
(* once for each polynomial, and the proof does what the proofs of those     *)
(* wrappers do (the lemmas of mlkem_native/polyvec_inline.ml) between the    *)
(* calls. The inlined code does nothing but set up the calls, and its        *)
(* instructions are interleaved with the prologue and the setup of the       *)
(* comparison, so there is no lemma for each inlined call. The code relies   *)
(* on the kernels leaving X8, X9, Q2 and Q3 unchanged, which their theorems  *)
(* state. Since the kernels use no stack, the frame is the 1856 bytes of the *)
(* function itself, rather than 1888 with the 32 bytes of the polyvec        *)
(* callees, and the buffers are at 32 or 48 bytes from its base.             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/polyvec_inline.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tobytes_spec.ml";;

(*** The code in the image, as listed in layout.ml (without the comparison
     and the epilogue, which are as in the gcc 12 -O2 code), and the PLT
     stub for memset:

    mlkem512_check_pk:
        +0x0  sub     sp, sp, #0x740
        +0x4  mov     x8, x0
        +0x8  adrp    x2, <page>
        +0xc  ldr     x2, [x2, #4088]          // got_stack_chk_guard
       +0x10  mov     x1, x0                   // polyvec_frombytes
       +0x14  stp     x19, x20, [sp]
       +0x18  add     x19, sp, #0x3f
       +0x1c  and     x19, x19, #0xffffffffffffffe0
       +0x20  stp     x21, x30, [sp, #16]
       +0x24  mov     x0, x19                  // polyvec_frombytes
       +0x28  add     x9, x19, #0x200          // polyvec_frombytes
       +0x2c  ldr     x3, [x2]
       +0x30  str     x3, [sp, #1848]
       +0x34  mov     x3, #0x0
       +0x38  add     x20, x19, #0x400         // polyvec_tobytes
       +0x3c  movi    v2.4s, #0x0
       +0x40  bl      mlk_poly_frombytes_c
       +0x44  add     x1, x8, #0x180
       +0x48  mov     x0, x9
       +0x4c  mov     v3.16b, v2.16b
       +0x50  bl      mlk_poly_frombytes_c
       +0x54  mov     x0, x19                  // polyvec_reduce
       +0x58  bl      mlk_poly_reduce_c
       +0x5c  mov     x0, x9
       +0x60  bl      mlk_poly_reduce_c
       +0x64  mov     x0, x20                  // polyvec_tobytes
       +0x68  mov     x1, x19
       +0x6c  bl      mlk_poly_tobytes_c
       +0x70  mov     x1, x9
       +0x74  add     x0, x19, #0x580
       +0x78  bl      mlk_poly_tobytes_c
       +0x7c  mov     x0, x8
       +0x80  mov     x2, x20
       +0x84  add     x1, x19, #0x700
    loop1:
       +0x88  ldr     q0, [x0], #16
       +0x8c  ldr     q1, [x2], #16
       +0x90  eor     v0.16b, v0.16b, v1.16b
       +0x94  orr     v3.16b, v3.16b, v0.16b
       +0x98  eor     v2.16b, v2.16b, v0.16b
       +0x9c  cmp     x1, x2
       +0xa0  b.ne    loop1
    loop1_exit:
       +0xa4  movi    v1.4s, #0x0
       ...    (the reduction of the accumulators, as in gcc12_O2)
      +0x108  mov     w21, #0xfffffffc
      +0x10c  csel    w21, wzr, w21, eq
      +0x110  bl      memset                   // the encoding, 768 bytes
      +0x114  mov     x2, #0x400
      +0x118  mov     x0, x19
      +0x11c  mov     w1, #0x0
      +0x120  bl      memset                   // the vector, 1024 bytes
      +0x124  adrp    x0, <page>
      +0x128  ldr     x0, [x0, #4088]          // got_stack_chk_guard
      +0x12c  ldr     x2, [sp, #1848]
      +0x130  ldr     x1, [x0]
      +0x134  subs    x2, x2, x1
      +0x138  mov     x1, #0x0
      +0x13c  b.ne    +0x154
      +0x140  ldp     x19, x20, [sp]
      +0x144  mov     w0, w21
      +0x148  ldp     x21, x30, [sp, #16]
      +0x14c  add     sp, sp, #0x740
      +0x150  ret
      +0x154  bl      stack_chk_fail

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem512_check_pk"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES16_LIST_STMT =
  `!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`;;

let CHECKPK_BYTES16_LIST = assume_spec CHECKPK_BYTES16_LIST_STMT;;

let CHECKPK_IVAL_WORD_STMT =
  `!f. f < 32768 ==> ival(word f:int16) = &f`;;

let CHECKPK_IVAL_WORD = assume_spec CHECKPK_IVAL_WORD_STMT;;

let CHECKPK_REDUCED_STMT =
  `!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`;;

let CHECKPK_REDUCED = assume_spec CHECKPK_REDUCED_STMT;;

let CHECKPK_LIST_PROPS_STMT =
  `!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`;;

let CHECKPK_LIST_PROPS = assume_spec CHECKPK_LIST_PROPS_STMT;;

let CHECKPK_REENCODE_STMT =
  `!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let CHECKPK_REENCODE = assume_spec CHECKPK_REENCODE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time: the bytes of the key and of the       *)
(* encoding XORed together are ORed into one accumulator (and XORed into     *)
(* another), which is zero if and only if the prefixes so far are equal. The *)
(* loop test compares the pointers.                                          *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES128_STMT =
  `!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`;;

let CHECKPK_BYTES128 = assume_spec CHECKPK_BYTES128_STMT;;

let CHECKPK_MOD_STEP_STMT =
  `!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`;;

let CHECKPK_MOD_STEP = assume_spec CHECKPK_MOD_STEP_STMT;;

let CHECKPK_OR_STEP_STMT =
  `!q:int128 a b.
        word_or
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456)))
         q = word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`;;

let CHECKPK_OR_STEP = assume_spec CHECKPK_OR_STEP_STMT;;

let CHECKPK2_TEST_STMT =
  `!sp:int64 b i.
        b <= 48 /\ i < 48
        ==> (val(word_sub (word_add sp (word(b + 1792)))
                          (word_add (word_add sp (word((b + 1024) + 16 * i)))
                                    (word 16))) = 0 <=>
             ~(i + 1 < 48))`;;

let CHECKPK2_TEST = assume_spec CHECKPK2_TEST_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* address depends on whether the stack pointer is a multiple of 32 or just  *)
(* of 16. The proof uses a variable boff for the offset of the first one.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let CHECKPK_ALIGNED_16_32 = assume_spec CHECKPK_ALIGNED_16_32_STMT;;

let CHECKPK2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 63)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 32 else 48))`;;

let CHECKPK2_BUFFER_ADDRESS = assume_spec CHECKPK2_BUFFER_ADDRESS_STMT;;

let CHECKPK_BUFFER_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `word_and (word_add stackpointer (word n))
                                    (word m):int64`) (lhs(concl th))
    then SUBST_ALL_TAC th else NO_TAC);;

let CHECKPK_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_shake128x4_release. The first 768 bytes of the key at pk are a      *)
(* number n, and the result is 0 if all the 512 12-bit fields of n are below *)
(* 3329, which is the modulus check of FIPS 203, and -4 otherwise. The loop  *)
(* of the comparison has an invariant stating the value of the accumulator   *)
(* in terms of the prefixes of the key and of the encoding. The stack is the *)
(* 1856 bytes of the function: the kernels use none.                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the offset of the buffers as boff ***)

let CHECKPK2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `n:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1856 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK2_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`if aligned 32 (stackpointer:int64) then 32 else 48`,
           `boff:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

(*** The facts in the loop, with the saved registers and the stack guard ***)

let CHECKPK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              512`;;

let CHECKPK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                512))`;;

let CHECKPK2_FRAME = vsubst [CHECKPK_M,`M:num`]
 `read SP s = stackpointer /\
  read (memory :> bytes64 stackpointer) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 8))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 16))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1848))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
  s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
  mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X19 s = word_add stackpointer (word boff) /\
  read X20 s = word_add stackpointer (word(boff + 1024)) /\
  read (memory :> bytes(pk,768)) s = n /\
  read (memory :> bytes(word_add stackpointer (word(boff + 1024)),768)) s =
  M`;;

let CHECKPK2_INV = vsubst [CHECKPK_M,`M:num`]
 `\i s. read X0 s = word_add pk (word(16 * i)) /\
        read X2 s = word_add stackpointer (word((boff + 1024) + 16 * i)) /\
        read X1 s = word_add stackpointer (word(boff + 1792)) /\
        (read Q3 s = word 0 <=>
         n MOD 2 EXP (128 * i) = M MOD 2 EXP (128 * i))`;;

let CHECKPK2_INV_FRAME =
  let vs,bod = strip_abs CHECKPK2_INV in
  list_mk_abs(vs,mk_conj(bod,CHECKPK2_FRAME));;

(*** Decoding, reducing and encoding the vector, up to the loop. Between
     the calls of the kernels, the facts for the two polynomials are
     joined into those for the vector, as in the proofs of the polyvec
     functions of the gcc 12 -O2 build. ***)

let CHECKPK_ADDR_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let CHECKPK_JOIN_TAC k ths =
  POLYVEC_JOIN_TAC k THEN REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE CHECKPK_ADDR_CONV) THEN
  CONV_TAC CHECKPK_ADDR_CONV THEN
  ASM_SIMP_TAC(POLYVEC_FROMBYTES_FIELD_GEN::ADD_CLAUSES::ths);;

let CHECKPK2_REDUCED_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `!i. i < 512
        ==> ival(read (memory :> bytes16
                  (word_add (word_add stackpointer (word boff))
                            (word(2 * i)))) s) =
            ival(word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16) rem &3329`)
  ASSUME_TAC THENL [CHECKPK_JOIN_TAC 2 []; ALL_TAC];;

let CHECKPK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add stackpointer (word boff),1024)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The results of mlk_poly_tobytes_c, whose hypotheses on the list of
     coefficients hold for the parts of the reduced vector ***)

let CHECKPK_TOBYTES_POST_TAC =
  let is_sublist t = match t with Const("SUB_LIST",_) -> true | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("==>",_),ant),_)
        when can (find_term is_sublist) ant ->
        MP_TAC th THEN ANTS_TAC THENL
         [REWRITE_TAC[LENGTH_SUB_LIST; CHECKPK_LIST_PROPS] THEN
          CONV_TAC(DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_MIN_CONV) THEN
          REWRITE_TAC[] THEN
          MATCH_MP_TAC ALL_SUB_LIST_GEN THEN REWRITE_TAC[CHECKPK_LIST_PROPS];
          DISCH_TAC]
    | _ -> NO_TAC));;

let CHECKPK2_ENCODED_TAC s =
  CHECKPK_TOBYTES_POST_TAC THEN
  SUBGOAL_THEN (vsubst [s,`s:armstate`; CHECKPK_M,`M:num`]
   `read (memory :> bytes(word_add stackpointer (word(boff + 1024)),
                          384 * 2)) s = M`)
  (ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THENL
   [MATCH_MP_TAC POLYVEC_TOBYTES_JOIN_GEN THEN
    REWRITE_TAC[CHECKPK_LIST_PROPS] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    RULE_ASSUM_TAC(CONV_RULE CHECKPK_ADDR_CONV) THEN
    CONV_TAC CHECKPK_ADDR_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The calls are simulated with ARM_STEPS_TAC up to and including the BL,
     and the call tactic for the next step. The addresses in registers are
     normalized before each call, so that those of its results are. ***)

let CHECKPK2_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 2 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (4--8) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (9--17) THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (19--22) THEN
  CHECKPK_NORMALIZE_TAC THEN
  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`;
                       `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`;
                       `read X30 s`] 23 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (24--25) THEN
  LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word(((n DIV 2 EXP 0) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD
              2 EXP 12):int16`;
    `pc:num`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (27--28) THEN
  LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word(((n DIV 2 EXP 3072) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD
              2 EXP 12):int16`;
    `pc:num`; `read X30 s`] 29 THEN
  CHECKPK2_REDUCED_TAC `s29:armstate` THEN
  CHECKPK_LIST_TAC `s29:armstate` THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN
   `word_add stackpointer (word boff):int64` 2 THEN
  CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (30--32) THEN
  CHECKPK_NORMALIZE_TAC THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`;
                     mk_comb(`SUB_LIST(0,256):int16 list->int16 list`,
                             CHECKPK_L);
                     `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--36) THEN
  CHECKPK_NORMALIZE_TAC THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`;
                     mk_comb(`SUB_LIST(256,256):int16 list->int16 list`,
                             CHECKPK_L);
                     `pc:num`; `read X30 s`] 37 THEN
  CHECKPK2_ENCODED_TAC `s37:armstate` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (38--40) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[];;

(*** The loop body, comparing 16 more bytes ***)

let CHECKPK_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 48 ==> 16 * i + 16 <= 768`)
               (ASSUME `i < 48`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let lth = SPECL [a; `768`; `i:num`; v; s] CHECKPK_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let CHECKPK2_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  CHECKPK_CHUNK_TAC `pk:int64` `n:num` THEN
  CHECKPK_CHUNK_TAC `word_add stackpointer (word(boff + 1024)):int64`
                    `mm:num` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`; `boff:num`; `i:num`] CHECKPK2_TEST)
       (CONJ (ASSUME `boff <= 48`) (ASSUME `i < 48`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[CHECKPK_OR_STEP; CHECKPK_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]];;

(*** The final result from the accumulators, the zeroing, the return ***)

let CHECKPK_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `768`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECKPK2_DONE_TAC =
  SUBGOAL_THEN
   `(q3:int128 = word 0) <=>
    !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECKPK_BOUND `pk:int64` `s0:armstate`) THEN
    MP_TAC(CHECKPK_BOUND `word_add stackpointer (word(boff + 1024)):int64`
                         `s0:armstate`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 768 = 128 * 48`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECKPK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECKPK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 512 = 128 * 48`];
    ALL_TAC];;

let CHECKPK2_EXIT_TAC =
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN CHECKPK2_DONE_TAC THEN

  (*** The comparison of the hashes and the zeroing of the buffers ***)

  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--21) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (22--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 28 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--37) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 37 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 42 THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (43--43) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (44--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (pk,768) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 1856),1856)]
         [(pk,768); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem512_check_pk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,768)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 512
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 0 else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 1856),1856)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the address of the key,    *)
(* the stack and the image: the comparison is in constant time and the       *)
(* result is selected without a branch. The buffers are kept at their offset *)
(* from the stack pointer as a conditional (32 or 48), and the loop          *)
(* invariant has only the pointers and the frame.                            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let CHECKPK2_SAFE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 63))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 32 else 48))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECKPK2_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let CHECKPK_SAFE_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let CHECKPK_ALLOWED =
  [`pc:num`; `pk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `f_ev_loop:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`];;

let CHECKPK2_SAFE_CALL_TAC name ilist n =
  CHECKPK_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK_ALLOWED); LABEL_TAC name safety_th]);;

let CHECKPK2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil pk guard mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 48
          (\i. f_ev_loop pk guard mf pc stackpointer returnaddress i))
        (f_ev_prol pk guard mf pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

let CHECKPK2_SAFE_INV =
 `\i s. read X0 s = word_add pk (word(16 * i)) /\
        read X2 s =
        word_add stackpointer
         (word(((if aligned 32 stackpointer then 32 else 48) + 1024) +
               16 * i)) /\
        read X1 s =
        word_add stackpointer
         (word((if aligned 32 stackpointer then 32 else 48) + 1792)) /\
        read SP s = stackpointer /\
        read (memory :> bytes64 stackpointer) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 8))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 16))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 24))) s =
        returnaddress /\
        read (memory :> bytes64 (word_add stackpointer (word 1848))) s =
        canary /\
        read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
        s = guard /\
        read (memory :> bytes64 guard) s = canary /\
        read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
        mf /\
        read (memory :> bytes(ea,el)) s = ev /\
        read X19 s =
        word_add stackpointer
         (word(if aligned 32 stackpointer then 32 else 48)) /\
        read X20 s =
        word_add stackpointer
         (word((if aligned 32 stackpointer then 32 else 48) + 1024))`;;

let CHECKPK2_SAFE_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (4--8) THEN
  CHECKPK2_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (9--17) THEN
  CHECKPK2_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
    `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (19--22) THEN
  CHECKPK2_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
    `read X30 s`] 23 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (24--25) THEN
  CHECKPK2_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (27--28) THEN
  CHECKPK2_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (30--32) THEN
  CHECKPK2_SAFE_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
    `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--36) THEN
  CHECKPK2_SAFE_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
    `read X30 s`] 37 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (38--40) THEN
  CHECKPK_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK2_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--7) THEN
  SUBGOAL_THEN `(if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`;
               `if aligned 32 (stackpointer:int64) then 32 else 48`;
               `i:num`] CHECKPK2_TEST)
       (CONJ (ASSUME
         `(if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`)
             (ASSUME `i < 48`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK2_SAFE_EXIT_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 28 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_ALLOWED) 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--37) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 37 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_ALLOWED) 42 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (43--43) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (44--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 1856),1856)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 1856))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 1856),1856;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 1856),1856]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 1856),1856)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for          *)
(* mlkem512_enc_derand, which branches on the result. It uses the combined   *)
(* theorems for the callees and the invariant of the correctness proof with  *)
(* the events. The offset boff of the buffers is an abbreviation of the      *)
(* conditional, which is restored before the events are matched, so that     *)
(* they are a function of the stack pointer.                                 *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_FULL_ALLOWED = CHECKPK_ALLOWED @ [`boff:num`];;

let CHECKPK_UNABBREV_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `boff:num`));;

let CHECKPK2_FULL_CALL_TAC name ilist n =
  CHECKPK_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK_FULL_ALLOWED); LABEL_TAC name safety_th]);;

let CHECKPK2_FULL_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil pk guard mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 48
          (\i. f_ev_loop pk guard mf pc stackpointer returnaddress i))
        (f_ev_prol pk guard mf pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1856):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP CHECKPK2_BUFFER_ADDRESS
              (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `boff = if aligned 32 (stackpointer:int64) then 32 else 48` THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

let CHECKPK2_FULL_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 2 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (4--8) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (9--17) THEN
  CHECKPK2_FULL_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
    `(n DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (19--22) THEN
  CHECKPK2_FULL_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
    `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`; `read X30 s`] 23 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (24--25) THEN
  CHECKPK2_FULL_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word(((n DIV 2 EXP 0) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD
              2 EXP 12):int16`;
    `pc:num`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (27--28) THEN
  CHECKPK2_FULL_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word(((n DIV 2 EXP 3072) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD
              2 EXP 12):int16`;
    `pc:num`; `read X30 s`] 29 THEN
  CHECKPK2_REDUCED_TAC `s29:armstate` THEN
  CHECKPK_LIST_TAC `s29:armstate` THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN
   `word_add stackpointer (word boff):int64` 2 THEN
  CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (30--32) THEN
  CHECKPK2_FULL_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
    mk_comb(`SUB_LIST(0,256):int16 list->int16 list`,CHECKPK_L);
    `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--36) THEN
  CHECKPK2_FULL_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
    mk_comb(`SUB_LIST(256,256):int16 list->int16 list`,CHECKPK_L);
    `pc:num`; `read X30 s`] 37 THEN
  CHECKPK2_ENCODED_TAC `s37:armstate` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (38--40) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[] THEN
  CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK2_FULL_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CHECKPK_CHUNK_TAC `pk:int64` `n:num` THEN
  CHECKPK_CHUNK_TAC `word_add stackpointer (word(boff + 1024)):int64`
                    `mm:num` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`; `boff:num`; `i:num`] CHECKPK2_TEST)
       (CONJ (ASSUME `boff <= 48`) (ASSUME `i < 48`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[CHECKPK_OR_STEP; CHECKPK_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
  CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK2_FULL_EXIT_TAC =
  REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CHECKPK2_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--21) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (22--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 28 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_FULL_ALLOWED) 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (34--37) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC 37 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_FULL_ALLOWED) 42 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (43--43) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_EXEC (44--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q3:int128 = word 0`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
     (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
    CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk n guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 1856),1856)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,768)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if !i. i < 512
                            ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                     then word 0 else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 1856))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 1856),1856;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 1856),1856]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 1856),1856)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT;;
