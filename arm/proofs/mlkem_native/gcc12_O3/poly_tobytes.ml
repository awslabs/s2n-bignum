(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks to a byte array.      *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml); unlike at -O2 there  *)
(* is no separate transcription of it.                                       *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with LD2 and ST3, after  *)
(* a check that the input and the output do not overlap; if they do, the     *)
(* code falls back to the scalar loop of -O2. Since the specification        *)
(* requires them not to overlap, only the vector code runs. It saves X19 and *)
(* X30 in a 16-byte frame on the stack and uses X18 as a temporary, so       *)
(* unlike those of gcc12_O2 the specifications have the stack pointer and    *)
(* this frame, and X18 among the registers changed.                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/utils/mlkem_native_interleave.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tobytes:
       +0x0: add     x4, x0, #0x180
       +0x4: add     x2, x1, #0x200
       +0x8: cmp     x1, x4
       +0xc: ccmp    x0, x2, #0x2, cc
      +0x10: b.cc    <mlkem_poly_tobytes+0x1f4>
      +0x14: mov     x2, x1
      +0x18: stp     x19, x30, [sp, #-16]!
      +0x1c: add     x19, x1, #0x40
      +0x20: add     x30, x1, #0x60
      +0x24: add     x16, x0, #0x60
      +0x28: ld2     {v0.8h-v1.8h}, [x2], #32
      +0x2c: add     x13, x0, #0x90
      +0x30: add     x10, x0, #0xc0
      +0x34: add     x7, x0, #0xf0
      +0x38: add     x4, x0, #0x120
      +0x3c: add     x18, x1, #0x80
      +0x40: ld2     {v2.8h-v3.8h}, [x2]
      +0x44: add     x2, x0, #0x150
      +0x48: shrn    v16.8b, v1.8h, #4
      +0x4c: add     x17, x1, #0xa0
      +0x50: add     x15, x1, #0xc0
      +0x54: add     x14, x1, #0xe0
      +0x58: uzp1    v7.16b, v1.16b, v3.16b
      +0x5c: add     x12, x1, #0x100
      +0x60: uzp1    v4.16b, v0.16b, v2.16b
      +0x64: add     x11, x1, #0x120
      +0x68: uzp2    v0.16b, v0.16b, v2.16b
      +0x6c: add     x9, x1, #0x140
      +0x70: add     x8, x1, #0x160
      +0x74: add     x6, x1, #0x180
      +0x78: shl     v1.16b, v7.16b, #4
      +0x7c: add     x5, x1, #0x1a0
      +0x80: add     x3, x1, #0x1c0
      +0x84: add     x1, x1, #0x1e0
      +0x88: orr     v5.16b, v0.16b, v1.16b
      +0x8c: mov     v0.8b, v16.8b
      +0x90: shrn2   v0.16b, v3.8h, #4
      +0x94: mov     v6.16b, v0.16b
      +0x98: st3     {v4.16b-v6.16b}, [x0], #48
      +0x9c: ld2     {v0.8h-v1.8h}, [x19]
      +0xa0: ld2     {v2.8h-v3.8h}, [x30]
      +0xa4: shrn    v16.8b, v1.8h, #4
      +0xa8: uzp1    v7.16b, v1.16b, v3.16b
      +0xac: uzp1    v4.16b, v0.16b, v2.16b
      +0xb0: uzp2    v0.16b, v0.16b, v2.16b
      +0xb4: shl     v1.16b, v7.16b, #4
      +0xb8: orr     v5.16b, v0.16b, v1.16b
      +0xbc: mov     v0.8b, v16.8b
      +0xc0: shrn2   v0.16b, v3.8h, #4
      +0xc4: mov     v6.16b, v0.16b
      +0xc8: st3     {v4.16b-v6.16b}, [x0]
      +0xcc: ld2     {v0.8h-v1.8h}, [x18]
      +0xd0: ld2     {v2.8h-v3.8h}, [x17]
      +0xd4: shrn    v16.8b, v1.8h, #4
      +0xd8: uzp1    v7.16b, v1.16b, v3.16b
      +0xdc: uzp1    v4.16b, v0.16b, v2.16b
      +0xe0: uzp2    v0.16b, v0.16b, v2.16b
      +0xe4: shl     v1.16b, v7.16b, #4
      +0xe8: orr     v5.16b, v0.16b, v1.16b
      +0xec: mov     v0.8b, v16.8b
      +0xf0: shrn2   v0.16b, v3.8h, #4
      +0xf4: mov     v6.16b, v0.16b
      +0xf8: st3     {v4.16b-v6.16b}, [x16]
      +0xfc: ld2     {v0.8h-v1.8h}, [x15]
     +0x100: ld2     {v2.8h-v3.8h}, [x14]
     +0x104: shrn    v16.8b, v1.8h, #4
     +0x108: uzp1    v7.16b, v1.16b, v3.16b
     +0x10c: uzp1    v4.16b, v0.16b, v2.16b
     +0x110: uzp2    v0.16b, v0.16b, v2.16b
     +0x114: shl     v1.16b, v7.16b, #4
     +0x118: orr     v5.16b, v0.16b, v1.16b
     +0x11c: mov     v0.8b, v16.8b
     +0x120: shrn2   v0.16b, v3.8h, #4
     +0x124: mov     v6.16b, v0.16b
     +0x128: st3     {v4.16b-v6.16b}, [x13]
     +0x12c: ld2     {v0.8h-v1.8h}, [x12]
     +0x130: ld2     {v2.8h-v3.8h}, [x11]
     +0x134: shrn    v16.8b, v1.8h, #4
     +0x138: uzp1    v7.16b, v1.16b, v3.16b
     +0x13c: uzp1    v4.16b, v0.16b, v2.16b
     +0x140: uzp2    v0.16b, v0.16b, v2.16b
     +0x144: shl     v1.16b, v7.16b, #4
     +0x148: orr     v5.16b, v0.16b, v1.16b
     +0x14c: mov     v0.8b, v16.8b
     +0x150: shrn2   v0.16b, v3.8h, #4
     +0x154: mov     v6.16b, v0.16b
     +0x158: st3     {v4.16b-v6.16b}, [x10]
     +0x15c: ld2     {v0.8h-v1.8h}, [x9]
     +0x160: ld2     {v2.8h-v3.8h}, [x8]
     +0x164: shrn    v16.8b, v1.8h, #4
     +0x168: uzp1    v7.16b, v1.16b, v3.16b
     +0x16c: uzp1    v4.16b, v0.16b, v2.16b
     +0x170: uzp2    v0.16b, v0.16b, v2.16b
     +0x174: shl     v1.16b, v7.16b, #4
     +0x178: orr     v5.16b, v0.16b, v1.16b
     +0x17c: mov     v0.8b, v16.8b
     +0x180: shrn2   v0.16b, v3.8h, #4
     +0x184: mov     v6.16b, v0.16b
     +0x188: st3     {v4.16b-v6.16b}, [x7]
     +0x18c: ld2     {v0.8h-v1.8h}, [x6]
     +0x190: ld2     {v2.8h-v3.8h}, [x5]
     +0x194: shrn    v16.8b, v1.8h, #4
     +0x198: uzp1    v7.16b, v1.16b, v3.16b
     +0x19c: uzp1    v4.16b, v0.16b, v2.16b
     +0x1a0: uzp2    v0.16b, v0.16b, v2.16b
     +0x1a4: shl     v1.16b, v7.16b, #4
     +0x1a8: orr     v5.16b, v0.16b, v1.16b
     +0x1ac: mov     v0.8b, v16.8b
     +0x1b0: shrn2   v0.16b, v3.8h, #4
     +0x1b4: mov     v6.16b, v0.16b
     +0x1b8: st3     {v4.16b-v6.16b}, [x4]
     +0x1bc: ld2     {v0.8h-v1.8h}, [x3]
     +0x1c0: ld2     {v2.8h-v3.8h}, [x1]
     +0x1c4: shrn    v16.8b, v1.8h, #4
     +0x1c8: uzp1    v7.16b, v1.16b, v3.16b
     +0x1cc: uzp1    v4.16b, v0.16b, v2.16b
     +0x1d0: uzp2    v0.16b, v0.16b, v2.16b
     +0x1d4: shl     v1.16b, v7.16b, #4
     +0x1d8: orr     v5.16b, v0.16b, v1.16b
     +0x1dc: mov     v0.8b, v16.8b
     +0x1e0: shrn2   v0.16b, v3.8h, #4
     +0x1e4: mov     v6.16b, v0.16b
     +0x1e8: st3     {v4.16b-v6.16b}, [x2]
     +0x1ec: ldp     x19, x30, [sp], #16
     +0x1f0: ret
     +0x1f4: mov     x3, x1
     +0x1f8: mov     x1, x0
     +0x1fc: nop
     +0x200: ldrsh   w0, [x3]
     +0x204: add     x1, x1, #0x3
     +0x208: ldrh    w2, [x3, #2]
     +0x20c: add     x3, x3, #0x4
     +0x210: sturb   w0, [x1, #-3]
     +0x214: ubfx    x0, x0, #8, #8
     +0x218: orr     w0, w0, w2, lsl #4
     +0x21c: lsr     w2, w2, #4
     +0x220: sturb   w0, [x1, #-2]
     +0x224: sturb   w2, [x1, #-1]
     +0x228: cmp     x4, x1
     +0x22c: b.ne    <mlkem_poly_tobytes+0x200>
     +0x230: ret
 ***)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_tobytes"];;

(* ------------------------------------------------------------------------- *)
(* The packing of the coefficients in groups of two into three bytes, as in  *)
(* the gcc12_O2 proof, but for all the groups at once: if the bytes of each  *)
(* group are as the C code computes them, the 384 bytes are the 12-bit       *)
(* coefficients put together little-endian.                                  *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_PACK = prove
 (`!r s (l:int16 list).
     LENGTH l = 256 /\ ALL (\x. val x < 4096) l /\
     (!k. k < 128
          ==> read (memory :> bytes8 (word_add r (word(3 * k)))) s =
              word_zx (EL (2 * k) l) /\
              read (memory :> bytes8 (word_add r (word(3 * k + 1)))) s =
              word_or (word_shl (word_zx (EL (2 * k + 1) l)) 4)
                      (word_zx (word_ushr (EL (2 * k) l) 8)) /\
              read (memory :> bytes8 (word_add r (word(3 * k + 2)))) s =
              word_zx (word_ushr (EL (2 * k + 1) l) 4))
     ==> read (memory :> bytes(r,384)) s =
         num_of_wordlist (MAP word_zx l:(12 word)list)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 128
        ==> read (memory :> bytes(r,3 * k)) s =
            num_of_wordlist
             (MAP word_zx (SUB_LIST(0,2 * k) (l:int16 list)):(12 word)list)`
   (MP_TAC o SPEC `128`) THENL
   [ALL_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `LENGTH(l:int16 list) = 256`)) THEN
    REWRITE_TAC[SUB_LIST_LENGTH]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; MAP; num_of_wordlist;
                READ_MEMORY_BYTES_TRIVIAL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[ADD1; ARITH_RULE `3 * (k + 1) = ((3 * k + 1) + 1) + 1`;
              ARITH_RULE `2 * (k + 1) = 2 * k + 2`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE `(3 * k + 1) + 1 = 3 * k + 2`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SUB_LIST_0_SNOC2;
               ARITH_RULE `SUC k <= 128 ==> 2 * k + 2 <= 256`] THEN
  REWRITE_TAC[MAP_APPEND; MAP; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
              LENGTH_SUB_LIST; num_of_wordlist] THEN
  SUBGOAL_THEN `val(EL (2 * k) (l:int16 list)) < 4096` MP_TAC THENL
   [UNDISCH_TAC `ALL (\x. val x < 4096) (l:int16 list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `2 * k`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= 128 ==> MIN (2 * k) 256 = 2 * k`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 3 * k = 24 * k`;
              ARITH_RULE `12 * 2 * k = 24 * k`;
              ARITH_RULE `8 * (3 * k + 1) = 24 * k + 8`;
              ARITH_RULE `8 * (3 * k + 2) = 24 * k + 16`; EXP_ADD] THEN
  DISCH_TAC THEN MATCH_MP_TAC(NUM_RING
   `v0 + 2 EXP 8 * v1 + 2 EXP 16 * v2 = w0 + 2 EXP 12 * w1
    ==> ((n + a * v0) + (a * 2 EXP 8) * v1) + (a * 2 EXP 16) * v2 =
        n + a * (w0 + 2 EXP 12 * (w1 + 2 EXP 12 * 0))`) THEN
  UNDISCH_TAC `val(EL (2 * k) (l:int16 list)) < 4096` THEN
  SPEC_TAC(`EL (2 * k + 1) (l:int16 list)`, `t1:int16`) THEN
  SPEC_TAC(`EL (2 * k) (l:int16 list)`, `t0:int16`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The simulation: the input as the 16-bit coefficients EL j l, merged into  *)
(* the 256-bit loads of LD2, and after each step the registers loaded by     *)
(* LD2 and the 128-bit parts of the memory written by ST3 as joins.          *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(32 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes256 x) s0`)) (0--15);;

let TOBYTES_INPUT_TAC =
  SUBGOAL_THEN
   `!j. j < 256
        ==> read (memory :> bytes16 (word_add a (word(2 * j)))) s0 =
            EL j (l:int16 list)`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `j:num`; `s0:armstate`]
                 READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOBYTES_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

let TOBYTES_UNFOLD_CONV =
  REWRITE_CONV[word_deinterleave8_x; word_deinterleave4_x;
               word_deinterleave2_x; word_deinterleave8_y;
               word_deinterleave4_y; word_deinterleave2_y;
               word_split_lo; word_split_hi] THENC
  TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV DIMINDEX_CONV THENC
  TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV THENC
  SIMD_SIMPLIFY_CONV [];;

let TOBYTES_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_interleave"|"word_deinterleave8_x"|
                     "word_deinterleave8_y"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV TOBYTES_UNFOLD_CONV) th
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** The bytes of the 24 stores of 16 bytes ***)

let TOBYTES_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As at -O2, the C code relies on the coefficients being *)
(* < 2^12, as stated in its contract, so this is an assumption here.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,384)) [(word pc,libmlkem_size); (a,512)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,libmlkem_size); (a,512); (r,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_tobytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,384);
                         memory :> bytes(word_sub stackpointer
                                                 (word 16),16)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Without the conditions on l, only the control flow matters ***)

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256 /\ ALL (\x. val x < 4096) l`
  THENL
   [ALL_TAC;
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
    ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (6--125) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  TOBYTES_INPUT_TAC THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC [k] THEN
    TOBYTES_SIMD_TAC) (6--125) THEN
  TOBYTES_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The bytes of each group of two coefficients ***)

  MATCH_MP_TAC TOBYTES_PACK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 16),16))
               [word pc,libmlkem_size; a,512; r,384]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc (word_sub stackpointer (word 16))
                                      returnaddress /\
                        memaccess_inbounds e2
                         [a,512; r,384; word_sub stackpointer (word 16),16]
                         [r,384; word_sub stackpointer (word 16),16])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(r,384);
                           memory :> bytes(word_sub stackpointer
                                                   (word 16),16)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (6--125) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* gcc12_O2. Since the events must come from a single simulation, the input  *)
(* is named as w j for any contents of memory, with w j = EL j l when l has  *)
(* 256 elements, which is used only at the end.                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 16),16))
               [word pc,libmlkem_size; a,512; r,384]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc (word_sub stackpointer (word 16))
                                      returnaddress /\
                        memaccess_inbounds e2
                         [a,512; r,384; word_sub stackpointer (word 16),16]
                         [r,384; word_sub stackpointer (word 16),16]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(r,384);
                           memory :> bytes(word_sub stackpointer
                                                   (word 16),16)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN

  (*** The input as w j, whatever l is ***)

  SUBGOAL_THEN
   `?w:num->int16.
      !j. j < 256
          ==> read (memory :> bytes16 (word_add a (word(2 * j)))) s0 = w j`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\j. read (memory :> bytes16 (word_add a (word(2 * j)))) s0` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(l:int16 list) = 256 ==> !j. j < 256 ==> EL j l = (w:num->int16) j`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `read (memory :> bytes16 (word_add a (word(2 * j)))) s0` THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `j:num`; `s0:armstate`]
                   READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `w:num->int16` (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `w:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOBYTES_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC [k] THEN
    TOBYTES_SIMD_TAC) (6--125) THEN
  TOBYTES_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** Under the conditions on l, w j = EL j l, and the bytes as before ***)

  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) && free_in `EL:num->int16 list->int16` (concl th)
    then ASSUME_TAC(MP th (ASSUME `LENGTH(l:int16 list) = 256`))
    else NO_TAC) THEN
  MATCH_MP_TAC TOBYTES_PACK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `EL:num->int16 list->int16` (concl th)
    then REWRITE_TAC(map (fun j ->
           MP (SPEC (mk_small_numeral j) th)
              (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                                    (mk_small_numeral j) `256`)))) (0--255))
    else NO_TAC) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;
